# 020-07 Stored objects, format 2: the spec

Created 2026-11-08 by Frans Lundberg. Status: done, approved by Frans
under 018-01's rule on 2026-11-09, 07:33 (020-02, section 4.12; section
14); frozen at release 2026.4 (Q6). The bytes of a stored
object in BergDB, format 2, "DbObject's table with Binson's values"
(020-05's option (f)), as Frans decided them on 2026-11-08, 15:51 to 17:09
(020-02, section 4): the model, the grammar, the rules, what a writer must
do and a reader must refuse, the limits, the lookup, the format's version,
the conversion to and from Binson, and the conformance vectors. A reader
and a writer can be written in any language from this document and
BINSON-SPEC-1.1 alone. How the Java code gets there: 020-08.

Frans, 2026-11-08, 17:09, asked "Do you decide that the object format is
under 018-01's approval rule, with today's decisions as your approval of
the design and the spec as a subitem of 020 for your approval before
release?", answered "Yes" (020-02, section 4.12). At 17:12 he asked for
this spec and the implementation plan, with no code.

Where this document and 020-02, section 4, differ, section 4 wins. Each
rule names its decision. What the decisions leave open is in section 14,
as questions with a recommendation each; nothing here decides them, and
where the text needs an answer it states the recommended one and names
the question.

How each fact is known: the vectors (section 13) were made and checked by
two programs written apart, `F2.java` (adapted from 020-05's `Fmt.java`)
and `check.py` (written from this text, with another order of checks), in
`/Users/f/fl/bench/006-15/020-07/` (its `readme.txt` says how to run
them); BINSON-SPEC-1.1 read in the clone of binson.org at `46459bc`
(page version 2026-10-07); BergDB's code at `21936d3`.


## 1. In short

* A stored object is a header byte, 0x82, and an object. An object is a
  type byte (0x48, 0x49 or 0x4a) that gives the width w of its numbers
  (1, 2 or 4 bytes), the count of its fields in w bytes, the end of each
  field in w bytes, and the fields in the order of their names' unsigned
  bytes; a field is a 1-byte name length, the name, and a value in
  Binson's encoding. A nested object has the same framing and no header.
  An array is Binson's: 0x42, the elements, 0x43.
* Seven types, Binson's: boolean, integer (signed, 64 bits), double,
  string, bytes, array, object. No null: a field without a value is
  absent.
* One object, one byte string: a writer writes the canonical bytes, and a
  reader refuses any other byte string, naming the rule it breaks
  (sections 5 and 7).
* Limits: names of 1 to 255 bytes; at most 32,767 fields an object; depth
  16, objects and arrays counted alike, the top object level 1; a stored
  value of at most 2^31 − 1 bytes (section 11).
* A field is found by a binary search on the names, reading nothing but
  the table and the names it probes (section 8).
* Binson is one pass away, both ways: the values' bytes are copied, the
  objects framed again (section 10).
* The vectors: 33 valid stored values with 343 lookups, 85 invalid byte
  strings, each with the rules it breaks, and 8 Binson inputs, in
  `07-object-spec/vectors.txt` (section 13).
* Seven questions for Frans (section 14); one of them, whether a scalar
  is a level, before the code.


## 2. Scope, terms and conventions

### 2.1. Scope

In this spec: the bytes of a stored object, the value at a key that holds
an object, and of every object and array in it; what a writer writes; what
a reader accepts, refuses and finds; the limits; the format's version and
the old format; the conversion to and from Binson; the conformance
vectors.

Not in it (section 12): the API of any binding; the conversion between
stored objects and a language's classes; which keys hold objects; the
index definitions' fields, the index entries and their sort keys; Java's
wrapping of a top-level array or primitive.

### 2.2. Terms

* **Stored value**: the bytes of the value at a key, as the Core stores
  them.
* **Stored object**: a stored value that is the header and an object.
* **Container**: an object or an array. A **scalar**: a value of any
  other type.
* **Extent**: the bytes a value must fill exactly: the stored value after
  its header, for the top object; a field's bytes after its name, for the
  field's value. An array's element has no extent of its own: it lies in
  the array's.
* **Writer**: code that makes a stored value. **Reader**: code that reads
  one, by the **full check** (every rule over the whole value, section
  7.1) or by **lookups** (section 8).
* **Binding**: the code of one language that writes and reads stored
  objects.

### 2.3. Conventions

* Bytes are written in hexadecimal, `82 48 00`. Every multi-byte number is
  little-endian. Integers are two's complement where signed.
* The grammar is ABNF (RFC 5234). "Must", "must not" and "may" are rules;
  a section or paragraph marked *informative* is not.
* Names and strings compare as sequences of unsigned bytes (0 to 255),
  the first differing byte deciding, and a proper prefix before the
  longer sequence. This is Binson's order (BINSON-SPEC-1.1, section 3).
* BINSON-SPEC-1.1 (binson.org; "Copyright Frans Lundberg 2014-2026", CC
  BY-ND 4.0) is cited by section, not copied: this spec states what it
  takes from it and what it adds (020-05, section 9).


## 3. The model

What a stored object means, whatever the language.

* **An object** is a finite set of fields. A field is a name and a value.
  No two fields of an object have one name. The order of the fields is
  not part of the meaning; the bytes have one order (rule R7).
* **A name** is a string of 1 to 255 bytes (020-02, section 4.4).
* **A value** has one of seven types (020-02, sections 1, 4.2 and 4.7):
  * **boolean**: true or false;
  * **integer**: a whole number from −2^63 to 2^63 − 1; one type, whatever
    the width a writer's language gave it (4.7);
  * **double**: an IEEE 754 binary64 bit pattern. Every NaN is one value,
    whose pattern is `0x7ff8000000000000`; −0.0 and 0.0 are two values;
    the infinities and the subnormal numbers are values (4.8);
  * **string**: a sequence of Unicode scalar values (U+0000 to U+D7FF and
    U+E000 to U+10FFFF), held as its well-formed UTF-8 bytes (4.9, 021-04).
    No normalization: two strings are equal when their bytes are;
  * **bytes**: any sequence of bytes;
  * **array**: a finite sequence of values, of any types, mixed (4.6);
  * **object**: an object as above, nested.
* **No null** (4.1). No type has a null value. A field that has no value
  is absent. An array has no absent elements: every index from 0 to its
  length − 1 holds a value.
* **Equality.** Two objects are equal when they have the same names and,
  for each name, equal values. Two doubles are equal when their patterns
  are: NaN equals NaN, and −0.0 does not equal 0.0, unlike IEEE 754's
  comparison. Two arrays are equal when they have the same length and
  equal elements in order. Two stored objects are equal exactly when
  their bytes are (section 5.2).

**Absence**, for every binding: 020-04, section 3.3's text, which 020-04,
section 11, keeps for format 2, with its writer's paragraph made to leave
the put's rule open:

> A field that is present holds one value of its type. A field that the
> object does not hold is absent. Absence is the only way to say that a
> field has no value, and every reader meets it: in an object written
> before its class had the field, or by another language.
>
> A writer never stores its language's "no value" (Java's `null`,
> Python's `None`, JavaScript's `null` and `undefined`, Swift's `nil`,
> Rust's `None`, a nil pointer in Go): there is no encoding for it. It
> refuses one where nothing can be left out: an array's element, and the
> value at a key. In a field, it leaves the field out or refuses the
> value, by its binding's put rule (020-04, Q1: open, for the API,
> 020-02, section 5).
>
> A reader gives an absent field its language's value for a missing
> field: the class's initial value (Java, C#, Kotlin), `None` or `nil`
> for an optional (Rust, Swift), no key (Python, JavaScript), the zero
> value (Go). A present field is never "no value".


## 4. The bytes

### 4.1. The grammar

    stored     = header object            ; the value at a key
    header     = %x82                     ; format 2 (section 9)
    object     = %x48 count1 n*end1 fields    ; w = 1
               / %x49 count2 n*end2 fields    ; w = 2
               / %x4a count4 n*end4 fields    ; w = 4
    count1     = 1OCTET                   ; n, unsigned
    count2     = 2OCTET
    count4     = 4OCTET
    end1       = 1OCTET                   ; unsigned: where a field ends
    end2       = 2OCTET
    end4       = 4OCTET
    fields     = n*field                  ; n: the count
    field      = nameLen name value
    nameLen    = %x01-FF                  ; L, the name's length in bytes
    name       = L OCTET                  ; well-formed UTF-8
    value      = boolean / integer / double / string / bytes
               / array / object
    array      = %x42 *value %x43
    boolean    = %x44 / %x45              ; true / false
    double     = %x46 float64
    integer    = %x10 int8 / %x11 int16 / %x12 int32 / %x13 int64
    string     = stringLen utf
    bytes      = bytesLen raw
    stringLen  = %x14 int8 / %x15 int16 / %x16 int32
    bytesLen   = %x18 int8 / %x19 int16 / %x1a int32

`float64`, `int8` to `int64`, `utf` and `raw` are BINSON-SPEC-1.1's, its
section 2: a binary64 number in 8 bytes; signed integers of 1, 2, 4 and 8
bytes; the length's number of UTF-8 bytes; the length's number of any
bytes. Every value but the object is Binson's, byte for byte (020-02,
section 4.2). The grammar does not say how many bytes the fields take or
where each ends; the table does, by rules R4 and R5.

### 4.2. The table

In an object with type byte T, count n and width w = 1, 2 or 4 (T = 0x48,
0x49, 0x4a):

* The table is n numbers of w bytes, `end[0]` to `end[n−1]`, right after
  the count. The fields start at the first byte after the table: at
  offset `1 + w + n·w` from the type byte.
* `end[i]` is where field i ends, counted from the fields' first byte.
  Field i is the bytes from `end[i−1]` to `end[i]`, with `end[−1]` = 0.
  The fields take `end[n−1]` bytes, 0 when n = 0.
* So the object is `1 + w + n·w + end[n−1]` bytes, and a reader finds
  field i, and the object's end, without reading any field.

### 4.3. The type bytes

| Byte(s)          | What                                   |
|------------------|----------------------------------------|
| `10` to `13`     | integer of 1, 2, 4, 8 bytes            |
| `14` to `16`     | string, its length in 1, 2, 4 bytes    |
| `18` to `1a`     | bytes, the length in 1, 2, 4 bytes     |
| `42`, `43`       | an array's start and end               |
| `44`, `45`       | true, false                            |
| `46`             | double                                 |
| `48`, `49`, `4a` | object, w = 1, 2, 4                    |
| `82`             | the header, before the top object only |

No other byte starts a value. Binson's object bytes, `40` and `41`, are
not type bytes of format 2, and `48` to `4a` are not Binson's: a reader of
either refuses the other at its first object (020-05, section 12b.1).

### 4.4. Two examples

Each example gives an object's content in JSON5, JSON with its names
unquoted, then its bytes. JSON5 shows the fields and their values,
nothing more. It has one type of number, and format 2 has two, integer
and double: every number here is an integer, stored in the fewest bytes
(rule R9). JSON5 has no bytes type; neither example needs one. The order
of the fields in the JSON5 does not matter: the bytes hold them in the
order of their names (rule R7).

**A payment**, 36 bytes (020-05, section 12b.1; vector `payment`):

    {from: "1001", to: "1002", amount: 500}

Three fields: `from` and `to` are strings, and `amount` is the integer
500, an int16 (`11 f4 01`), as 500 is above 127. In the bytes the fields
come as `amount`, `from`, `to`. The field `amount` takes 10 bytes: its
name's length, 6 bytes of name and 3 of value; so its end is 10 (section
4.2). The last end, 30, fits in a byte, so w = 1 (rule R2):

    82                                 header, format 2
    48 03                              w = 1; 3 fields
    0a 15 1e                           the ends: 10, 21, 30
    06 61 6d 6f 75 6e 74  11 f4 01     amount: 500 (int16)
    04 66 72 6f 6d  14 04 31 30 30 31  from: "1001" (string, 4 bytes)
    02 74 6f  14 04 31 30 30 32        to: "1002" (string, 4 bytes)

**A dialog**, 37 bytes (vector `dialog`): one object with two fields,
`personA` and `personB`, whose values are objects. Each of them has one
field, `id`, the integer 1 or 2, an int8 (`10 01`, `10 02`):

    {personA: {id: 1}, personB: {id: 2}}

A nested object has the top object's framing, its own type byte, count
and table, and no header. Below, each is indented under its field's
name:

    82                                 header, format 2
    48 02                              w = 1; 2 fields
    10 20                              the ends: 16, 32
    07 70 65 72 73 6f 6e 41            personA: its value
       48 01                           w = 1; 1 field
       05                              the end: 5
       02 69 64  10 01                 id: 1 (int8)
    07 70 65 72 73 6f 6e 42            personB: its value
       48 01                           w = 1; 1 field
       05                              the end: 5
       02 69 64  10 02                 id: 2 (int8)

The empty object is `82 48 00` (`{}` in JSON5).

*Informative*: Java writes these objects from instances of classes with
public fields: `Payment` with `String from`, `String to` and `long
amount`; `Dialog` with `Person personA` and `Person personB`, and
`Person` with `long id`. The classes' names are not stored, only their
fields; and a `long` of 500 is an int16 all the same (rule R9).


## 5. The rules

A byte string is a stored object of format 2 if and only if it follows the
grammar and every rule below. Each rule names its decision in 020-02,
section 4, and the condition codes of section 7.2 that a reader gives
when the rule is broken.

* **R1. Header.** The first byte is `82`, and one object follows it, and
  nothing after that object. (4.5.) Codes: `header`, `format-1`, `type`,
  `trailing`, `past-end`.
* **R2. Width.** w is the smallest of 1, 2 and 4 that holds `end[n−1]`
  (0 for an empty object): 1 up to 255, 2 up to 65,535, 4 above. The
  count has w bytes too. (4.2; 020-05, section 12b.1, rule 2.) Code:
  `width`. *Informative*: a field takes at least 3 bytes, so the count
  always fits where the ends fit.
* **R3. Count.** The count n is at most 32,767. (4.10.) Code: `fields`.
* **R4. Ends.** The ends strictly increase: `end[i−1] < end[i]` for every
  i, with `end[−1]` = 0. The count, the table and the fields lie in the
  object's extent. Codes: `ends`, `past-end`.
* **R5. Fields.** Field i is exactly a name length L, L bytes of name,
  and one value that ends at `end[i]`. (4.2.) Codes: `name-length` (L =
  0), `past-end` (the name or the value reaches past the field),
  `field-size` (the value ends before the field).
* **R6. Names.** A name is 1 to 255 bytes of well-formed UTF-8 (rule
  R11). (4.4, 4.9.) Codes: `name-length`, `utf8`.
* **R7. Order.** The fields are in strictly increasing order of their
  names (section 2.3), so no two fields have one name. (4.4; Binson's
  section 3.) Codes: `order`, `duplicate`.
* **R8. Types.** A value starts with a type byte of section 4.3, and the
  top value is an object. Code: `type`.
* **R9. Integers.** An integer is stored in the fewest bytes that hold
  it: `10` for −128 to 127, `11` for −32,768 to 32,767 outside that, `12`
  for −2^31 to 2^31 − 1 outside that, `13` for the rest. (4.7; Binson's
  section 3, "Values must be stored using as few bytes as possible".)
  Code: `integer-size`.
* **R10. Lengths.** A string's or bytes' length is a signed integer, at
  least 0, in the fewest bytes by R9's ranges: `14` or `18` for 0 to 127,
  `15` or `19` for 128 to 32,767, `16` or `1a` above; and the string or
  bytes lie in their extent. (Binson's sections 2 and 3.) Codes:
  `length` (below 0), `integer-size`, `past-end`.
* **R11. Strings.** A string is well-formed UTF-8 (RFC 3629; the Unicode
  Standard, table 3-7): no surrogate (U+D800 to U+DFFF), no overlong
  form, nothing above U+10FFFF, no cut sequence; U+0000 and the
  noncharacters are allowed. (021-04, option 1; 4.9: stricter than
  Binson's section 4, where it is a recommendation.) Code: `utf8`.
* **R12. Doubles.** A double is its 8-byte pattern. A NaN is only
  `0x7ff8000000000000` (bytes `00 00 00 00 00 00 f8 7f`); −0.0 is
  `0x8000000000000000` and is kept. (4.8: Binson's section 4,
  recommendation 6, made a must.) Code: `nan`.
* **R13. Arrays.** An array is `42`, zero or more values, and `43`, all in
  its extent. (4.6.) Code: `past-end`.
* **R14. Depth.** Every container has a level: the top object 1, and a
  container that is a field's value or an array's element its parent's
  level + 1. No level is above 16. A scalar has no level (question Q1).
  (4.10.) Code: `depth`.
* **R15. Size.** A stored value is at most 2^31 − 1 bytes, its header
  included; so every end, length and object in it is below 2^31. (4.10,
  "an object under 2^31 bytes".) Code: `size`.

No rule is needed for null: the grammar has no encoding for it (4.1).

### 5.1. What the rules give

* **One object, one byte string** (P2; 020-05, section 12b.5). For every
  object of the model within the limits of section 11 there is exactly one
  byte string that follows the rules, and a reader that keeps the rules
  accepts no other. The writer's choices are all fixed: the fields' order
  (R7), each width (R2), each integer's and length's size (R9, R10), the
  NaN (R12), the header (R1). Checked: 38,579 changed byte strings (every
  byte of 28 valid vectors changed ten ways, and every cut) gave the same
  verdict in both programs of section 13.4, and each of the 20,251
  accepted ones was written again to the same bytes (020-05, section
  12b.5, F7: 13,417 of 32,867, in its sketch).
* **A field is found without a walk** (section 8): the table gives each
  field's place, and a nested object's table its fields'.
* **A stored object is never a string**: no well-formed UTF-8 starts with
  a byte from `80` to `bf` (4.5). A stored `byte[]` may start with `82`:
  the API's question (4.5; section 12).

### 5.2. Equality *(informative)*

Since the bytes are canonical, two stored objects are equal (section 3)
exactly when their bytes are; a binding may compare, hash or sign the
bytes. The doubles' equality is by pattern: a binding that compares
decoded doubles with its language's `==` treats NaN and −0.0 otherwise.


## 6. Writers

### 6.1. What a writer must do

* Write only stored objects that keep every rule of section 5: the fields
  sorted by their names' unsigned bytes, every width the smallest, every
  integer and length in the fewest bytes, the header before the top object
  and nowhere else.
* Write every NaN as `0x7ff8000000000000`, whatever its pattern in the
  writer's language; −0.0 as `0x8000000000000000` (4.8: a writer rewrites
  a NaN, it does not refuse it). In Java, `Double.doubleToLongBits`.
* Refuse, before anything is written (021-04), a value that has no stored
  form, and name its place from the top object, as `inner.names[3]`:
  * a name of 0 bytes or of more than 255 bytes (4.4);
  * a name or a string that is not a sequence of Unicode scalar values: a
    lone surrogate in Java, JavaScript, C# or Kotlin, ill-formed bytes in
    C or Go (021-04; R11);
  * an integer outside −2^63 to 2^63 − 1, such as a Python `int` or a
    JavaScript `BigInt` beyond it (4.7);
  * a container at a level above 16 (4.10; R14);
  * more than 32,767 fields in an object (4.10);
  * a stored value of more than 2^31 − 1 bytes (4.10; R15);
  * a "no value" as an array's element or as the value at a key; in a
    field, as its binding's put rule says (section 3).
* Never write two fields with one name. How an API that is given two
  resolves them is the API's (Java's `DbObject.Builder` keeps the last).
* In Java, each refusal is an `IllegalArgumentException` whose message
  names the place, as for 021-04's lone surrogates.

### 6.2. How *(informative)*

An object's table holds its fields' ends before the fields, and its width
depends on their total, so a writer knows each object's size before it
writes its table (020-05, section 12b.6):

1. **Bottom up**: each object's fields into a buffer, then its table in
   front of them; a nested object's bytes are copied once per level. The
   simplest; natural in Python and JavaScript.
2. **Back to front**: the last field first, each value before its name,
   then the table when every end is known; one pass, no copy (as
   FlatBuffers' builder). Needs each string's UTF-8 length first.
3. **Optimistic widths**: forward, with 1-byte entries reserved; an
   object whose fields pass 255 bytes moves them (as MySQL's binary JSON).

Both `F2.java`'s writers, 1 and 2, give the same bytes on every valid
vector. Sizes are computed in 64 bits, so that R15 is checked before any
number wraps.


## 7. Readers

### 7.1. The full check

A reader that reads a whole stored value (to decode it into a language's
objects, to convert it, or to take bytes that a conforming writer did not
make, such as a put of bytes) must check every rule of section 5 and
refuse a byte string that breaks one; it then gives nothing from it.

Every limit is checked before the reader recurses or allocates for it
(020-05, section 12b.9; 021-07, 021-08):

* the level (R14) before it enters an object or an array, so that a
  reader never recurses more than 16 levels deep, or keeps a stack of at
  most 16 entries;
* the count (R3), and that the table lies in the extent (R4), before it
  reads the table or allocates anything per field; the table's size `n·w`
  computed so that it cannot wrap (in 64 bits, or n checked first);
* every end and length against its extent (R4, R10) before it reads or
  allocates the bytes;
* the stored value's size (R15) before anything, where a binding can be
  given more bytes.

A reader never fails other than by its refusal: no index or bounds error,
no stack overflow, no out-of-memory from a count or a length it read
(021-07, 021-08; 020-01, N2).

### 7.2. The conditions

A reader that names why it refuses names one of these conditions. A byte
string may break more than one rule; which one a reader meets first
depends on its order of checks, and any of them is right. The vectors
list every condition that a reasonable order may meet (section 13).

| Code           | Rule                 | Condition                                             |
|----------------|----------------------|-------------------------------------------------------|
| `past-end`     | R1, R4, R5, R10, R13 | a number, a name or a value past its extent           |
| `header`       | R1                   | a first byte other than `82`, not format 1            |
| `format-1`     | R1                   | the bytes start with `bergo` (`62 65 72 67 6f`)       |
| `trailing`     | R1                   | bytes after the top object                            |
| `type`         | R8                   | not a type byte; or a top value that is not an object |
| `width`        | R2                   | an object's width is not the smallest                 |
| `fields`       | R3                   | a count above 32,767                                  |
| `ends`         | R4                   | the ends do not strictly increase                     |
| `field-size`   | R5                   | a value ends before its field                         |
| `name-length`  | R5, R6               | a name of 0 bytes                                     |
| `utf8`         | R6, R11              | a name or a string that is not well-formed UTF-8      |
| `order`        | R7                   | a name before the name before it                      |
| `duplicate`    | R7                   | a name equal to the name before it                    |
| `integer-size` | R9, R10              | an integer or a length not in the fewest bytes        |
| `length`       | R10                  | a length below 0                                      |
| `nan`          | R12                  | a NaN pattern other than `0x7ff8000000000000`         |
| `depth`        | R14                  | a container at a level above 16                       |
| `size`         | R15                  | a stored value of more than 2^31 − 1 bytes            |

A later format (`83` to `bf`) is `header`; a reader should name its
version, the first byte − `80` (section 9). A conversion from Binson has
one more condition, `binson`: its input is not a Binson object (section
10.2).

### 7.3. In Java *(informative)*

The reader throws `bergdb.pub.util.BadFormatException`, whose message
starts with the condition's code and says where, for example `past-end:
the value of field 2 ends past its field (bergdb 020-07, section 7.2)`.
Where it is read, as today (021-07): a get gives an
`ObjectCreationException` (`KvToObjectImp`), index maintenance a
`DataFormatException` (`RwEnvironmentImp.indexEntries`), and a start that
reads an index definition in format 1 is refused with a message (4.11;
020-08, section 5). Nothing else leaves a reader, and no `Error`.

### 7.4. Lookups without the full check

A binding may read single fields of a stored value that it has not fully
checked, by lookups (section 8) that check what they touch: the type byte,
the count against R3, the table against the object's extent, each end
they probe against R4, each name they compare against its field, and the
value they return by every rule, its nested values included. On bytes
that break a rule elsewhere, such a lookup may answer "absent" for a field
that is there, or the value of another field, but it never reads outside
the stored value and never fails but by a refusal (020-05, section 12b.5).
So a binding that reads by lookups must make the full check where bytes
enter that no conforming writer made: at a put of bytes, at a conversion.
Whether this freedom stays in the spec: question Q2.


## 8. Finding a field

### 8.1. The result

A **lookup** of a name in an object gives the value of the object's field
with that name, or **absent** when it has none. Names compare by their
bytes; a binding gives the wanted name as UTF-8 bytes. A **path** of names
`a.b.c` looks up `a` in the top object, then `b` in its value, then `c`:
it is absent when a step is absent, or when a step's value but the last is
not an object. A path does not enter arrays.

A reader may find a field by any method that gives this result on every
stored object.

### 8.2. The binary search *(informative)*

The method decided (4.3: "binary search with no hash list"), on the object
at offset p of the extent [p, limit):

    w = width from the type byte; n = count; f0 = p + 1 + w + n·w
    lo = 0, hi = n − 1
    while lo ≤ hi:
        m = (lo + hi) / 2, rounded down
        start = (m = 0 ? 0 : end[m−1]); stop = end[m]
        L = byte at f0 + start; name = the L bytes after it
        compare name with the wanted name, as unsigned bytes:
            equal: the value is the bytes from f0 + start + 1 + L to f0 + stop
            name before the wanted one: lo = m + 1
            after: hi = m − 1
    absent

It reads at most ⌈log2(n + 1)⌉ ends and names: 2 for `Payment`, 4 for
`Customer`, 7 at 100 fields; no other field, and no array is walked
(020-05, section 12b.4). A path is one search per step, each within the
extent of the step before; no recursion. A scan of the names in order that
stops at the first name past the wanted one reads the same bytes and gives
the same result (020-06's L). The lookup's cost against a hash scan was
measured in 020-06; the choice is 020-02, section 4.3.

### 8.3. The value found

A lookup gives the value's bytes, its type byte first. Its type and its
meaning are section 4.3's and section 3's; its end is the field's end. A
binding that converts it into its language's value checks it by every
rule (section 7.4).


## 9. Format versions and old objects

* **The header** is `80` + the format's version, before the top object of
  every stored object (4.5). `82` is format 2, this spec. `83` to `bf` are
  for later formats; a reader of format 2 refuses them (`header`), naming
  the version. `80` and `81` are not used.
* **A later format** is made with a new header (question Q5): a value
  that needs anything format 2 does not have, a new type byte such as a
  hashed object (4.3) or an array with a table (4.6), has a later header,
  so that a reader of format 2 refuses it at its first byte; a reader of a
  later format reads format 2 too.
* **Format 1**, BergDB 2026.3's and before, starts with `62 65 72 67 6f
  01`, `bergo` and the version 1 (`DbObject.Builder.buildInner` at
  `52f8ee5`; 020-05, section 3). A reader of format 2 refuses it
  (`format-1`), and says that the object was written by BergDB 2026.3 or
  before, which 2026.4 does not read (4.11). Format 1 is not described
  here, and no binding needs to read it.
* *Informative*: the header tells an object from a `String` value at its
  first byte, as no UTF-8 string starts with a byte from `80` to `bf`; a
  `byte[]` value may start with `82` (section 12).


## 10. Conversion with Binson

A binding that converts between stored objects and Binson
(BINSON-SPEC-1.1) must convert as this section says, so that every
binding gives the same bytes (question Q3); the method is informative.

### 10.1. Format 2 to Binson

Always possible, for every stored object. The header is left out. Each
object becomes `40`, then for each field in the stored order the name as
a Binson string (`14` L, or `15` and L in 2 bytes for L of 128 to 255) and
the value, then `41`. Each integer, double, boolean, string and bytes value
is copied byte for byte; an array is copied element by element, each
object in it framed again; a nested object is framed again the same way.
The result is canonical Binson: format 2's rules hold Binson's (section
5). For an object whose fields take at most 255 bytes and whose names are
under 128 bytes, the Binson bytes are as many as format 2's without the
header (020-05, section 12b.3).

### 10.2. Binson to format 2

The input must be a Binson object by BINSON-SPEC-1.1's sections 2 and 3
(code `binson` if not: its order, its fewest bytes, no two fields with one
name, nothing after it), and must fit format 2:

* every name of 1 to 255 bytes (`name-length`): Binson allows the empty
  name and longer ones (4.4);
* every name and string well-formed UTF-8 (`utf8`): a recommendation in
  Binson's section 4, a rule here (4.9);
* no container above level 16 (`depth`): Binson has no limit (4.10);
* at most 32,767 fields an object (`fields`), and a result of at most 2^31
  − 1 bytes (`size`).

Every NaN becomes `0x7ff8000000000000` (4.8: rewritten, not refused). The
values are copied, each object framed bottom up or back to front (section
6.2). A Binson object outside these rules is refused, naming the rule.

Both directions were checked on every valid vector, and the Binson bytes
against binson-java 3.5, which reads each and writes it again to the same
bytes (section 13.4; 020-05, section 12b.7, F2).


## 11. Limits

| Limit               | Value                       | Rule | A writer | A reader                  |
|---------------------|-----------------------------|------|----------|---------------------------|
| a name              | 1 to 255 bytes              | R6  | refuses  | refuses                   |
| fields of an object | at most 32,767              | R3  | refuses  | refuses, before the table |
| depth               | 16 levels, the top object 1 | R14 | refuses  | refuses, before entering  |
| a stored value      | at most 2^31 − 1 bytes      | R15 | refuses  | refuses                   |
| an integer          | −2^63 to 2^63 − 1           | R9  | refuses  | (by the encoding)         |
| a length            | 0 to 2^31 − 1               | R10 | (by R15) | refuses below 0           |
| an array's elements | no limit but R15            | R13 | -        | -                         |

*Informative*: in Java, the Core refuses a transaction whose values take
more than 7/8 of `Integer.MAX_VALUE − 8` bytes in the stream
(`StoredTrans.valueLimit`), so a Java database holds no stored value near
R15's limit. Binson recommends objects of under 100 fields and under 40
million bytes, and names of at most 50 characters (BINSON-SPEC-1.1,
section 4); format 2 does not make them rules.


## 12. Not in this spec

* **The API**: `DbObject`'s methods, what `getType` answers for an
  integer, whether a `DbObject` copies its bytes, whether it is public
  (020-02, section 5.1).
* **The conversion into a language's classes**: question 1 (exact or
  best effort; option (D) and its report), question 2 (the closed list of
  types a put takes), the put's rule for a null field (020-04, Q1)
  (020-02, sections 2, 3 and 5).
* **Which keys hold objects**, and what a build, an `Object.class` get or
  a primary scan does with a `byte[]` value that starts with `82` (4.5;
  020-01, section 14, decision 6).
* **The field `key`**: Java sets a field named `key` from the database
  key at a read, whatever is stored (020-02, question 5). To the format,
  `key` is a name like any other.
* **Java's wrapping at the top**: Java's `toDbObject` stores a top-level
  array in a field `array` and a primitive or a wrapper in a field `p`,
  as 2026.3 did (vectors `wrapped-array`, `wrapped-primitive`). To the
  format these are ordinary objects. Recommended: a convention of the
  API, not a rule of the format (question Q4; 020-02, section 5.2).
* **Index definitions, index entries, sort keys**: BergDB's index
  definitions are stored objects in this format (vector
  `index-definition`); their fields, and the index entries made from
  objects, are the index code's (4.12, "What it leaves open").


## 13. Conformance vectors

The file is `07-object-spec/vectors.txt`, beside this document: 38 KB of
plain ASCII text, written by `Vectors.java` and checked by `check.py`
(section 13.4). Every binding runs every record of it.

### 13.1. The file

* A line starting with `#` is a comment. A record starts with a line
  `KIND ID` at the start of a line; its attributes follow, one per line,
  each line starting with two spaces: `  KEY REST`. A blank line ends a
  record.
* **valid ID**: `bytes HEX`, a stored object; `value VN`, its meaning;
  `binson HEX`, the same object in Binson; any number of `lookup PATH
  RESULT`; an optional `note`.
* **invalid ID**: `bytes HEX`, a byte string that is not a stored object;
  `rules CODES`, the conditions of section 7.2 it breaks, separated by
  commas; an optional `note`.
* **generated ID**: `recipe TEXT`, how to make the bytes; `length N`;
  `sha256 HEX`, of the bytes; then a line `valid`, or `rules CODES`.
* **binson-in ID**: `binson HEX`, a Binson object; then `bytes HEX`, the
  stored object it converts to (section 10.2), or `rules CODES`, why it
  does not convert.
* **HEX**: pairs of hex digits; a group `(HH..*N)` is the bytes `HH..`
  repeated N times. No spaces.
* **VN**, the value notation: `{NAME:VALUE,...}` an object, its members
  in the stored order; `[VALUE,...]` an array; `true`, `false`;
  `iDECIMAL` an integer; `dHHHHHHHHHHHHHHHH` a double, its 64-bit pattern
  in 16 hex digits, the most significant first; `sTEXT` a string; `bTEXT`
  bytes. A NAME or TEXT is `"..."`, printable ASCII with `\"`, `\\` and
  `\xHH` for any byte, or `<HEX>`. No spaces outside `"..."`.
* **PATH RESULT**: NAMEs joined by `.`, from the top object; a space ends
  the path (a space inside `"..."` does not); RESULT is a VN value, or
  `absent`.

### 13.2. What a binding does with each record

* **valid**: the full check accepts `bytes`; decoded, they equal `value`;
  written from `value`, they are `bytes`; each `lookup` gives its result
  (by section 8's method or another); where the binding converts, `bytes`
  give `binson`, and `binson` gives `bytes`.
* **invalid**: the full check refuses `bytes`; a binding that names
  conditions names one of `rules`.
* **generated**: the recipe makes bytes of `length` and `sha256`; then as
  valid (without value and lookups) or invalid.
* **binson-in**: the conversion gives `bytes`, or refuses with one of
  `rules`.

### 13.3. What they cover

* **Valid, 32 records and 1 generated**: the samples of 020-05 (`payment`,
  `person`, `dialog`, `customer`, `index-definition`, `order` with w = 2
  and objects in an array); each type and its widths (`integers` at the
  boundaries of every width, `integer-fields`, `doubles` with −0.0, the
  infinities, NaN and subnormals, `strings` from U+0000 to U+10FFFF,
  lengths at 127/128 and 32,767/32,768, `bytes`); `arrays` (empty, nested,
  every type, objects); names (`names-order`, the unsigned order and
  prefixes; `names-odd`; `name-255`; `fields-85`, the most fields with w =
  1); the widths at 255/256 and 65,535/65,536 bytes of fields, and nested
  widths 4, 2, 1; depth 16 by objects, by arrays, mixed, and with a scalar
  below; Java's wrapping; and `fields-32767` (generated).
* **Lookups, 343**: every top-level name of each valid record, absent
  names before, between and after them (a name plus U+0000, a prefix,
  U+0001, `~~`, U+10FFFF), and paths through nested objects, through a
  scalar and through an array.
* **Invalid, 84 records and 1 generated**, by condition: `header` 5,
  `format-1` 2 (made by 2026.3's `DbObject`), `past-end` 13, `type` 13,
  `trailing` 2, `width` 4, `ends` 2 (also `past-end`), `field-size` 2,
  `name-length` 1, `utf8` 17 (names and strings: lone continuation bytes,
  overlong forms, surrogates, above U+10FFFF, cut sequences), `order` 3
  (one that a signed comparison would take), `duplicate` 1,
  `integer-size` 7, `length` 3, `nan` 4, `depth` 4, `fields` 1 (the
  generated `fields-32768`) and 1 more (`count-huge`, also `past-end`).
  `size` has no vector: it needs 2 GB.
* **Binson inputs, 8**: Payment and a NaN rewritten convert; an empty
  name, a 256-byte name, ill-formed UTF-8, 17 levels and two byte strings
  that are not Binson are refused.

### 13.4. How they were made and checked

`Vectors.java` builds each record and checks it with `F2.java` every way:
both writers give the bytes; the full check accepts them; the decoder
gives the value back; VN both ways; each lookup by the binary search
against the decoded value; Binson both ways, and binson-java 3.5 reads the
Binson bytes and writes them again unchanged; each invalid record is
refused with one of its codes. The format-1 records are made by
`bergdb.jar` at `52f8ee5`. `check.py`, a second implementation written
from this text, checks each record again, with its own writer, decoder,
lookup and conversions, and another order of checks (each table whole
before its fields; the top's trailing bytes before its fields). Then
38,579 changed byte strings (section 5.1) got the same verdict from both;
the 786 that the two refused for different conditions break at least the
two rules named, as each program names a rule only where it is broken.
Outputs: `out/run-vectors.txt` ("ALL VECTORS OK"),
`out/run-check.txt` ("ALL VECTORS OK (check.py)"), `out/run-diff.txt` (0
disagreements).

### 13.5. Where they live

In `java/src/bergdb/pubimp/doc-files/object-vectors.txt`, beside the code
that reads them (`ObjectFormatTester`), since 020-08's step 1
(2026-11-08). They were here, beside the spec, as
`07-object-spec/vectors.txt`, the place sections 1 and 13 name; a test
cannot read `items/` (items/readme.md, "Items and the current state"),
so the file moved into `java/` unchanged, byte for byte, and this section
points to it (question Q6's recommended answer, 020-08's default until
Frans says otherwise).


## 14. Questions for Frans

None changes a decision of 020-02, section 4; each makes a rule exact or
says where the spec stops. Q1 before the code (020-08, step 1); Q2 with
020-08's measurements (its step 4), as Java's first steps make the full
check at every read; the others before the release.

* **Q1. Is a scalar a level?** 4.10 decided "depth 16, counting every
  level, objects and arrays alike, the top object level 1". R14 counts the
  containers only: an object of 16 nested levels may hold scalars at its
  deepest level, as 021-08's reader and 020-05's sketch count. 4.10's
  example, `Customer`, `orders`, `Order`, `lines`, `Line`, `product`,
  `price`: 7, is 7 by R14 if `price` is an object, 6 if it is a number.
  *Recommended*: as R14, containers only; a scalar is a container's
  content, not a level. Else every limit moves down by one and the depth
  vectors change.
  *Decided* (Frans, 2026-11-08, 19:43: "As recommended"): containers
  only, as R14; a scalar is not a level.
* **Q2. Lookups without the full check.** Section 7.4 lets a binding read
  fields of a stored value it has not fully checked, by lookups that check
  what they touch (020-05, section 12b.5): fast for index maintenance and
  builds, and safe (no read outside, no failure but a refusal), but on
  damaged bytes a field may read as absent where the full check would
  refuse. *Recommended*: keep it, with the full check where bytes enter
  from outside (a put of bytes, a conversion) and for every whole read.
  The other choice, the full check before any read of a value, is one
  pass over its bytes (020-02, section 6, point 2: to be timed by 020-08).
  Java's first steps make the full check at every read either way (020-08,
  section 4.2).
  *Decided* (2026-11-09, under Frans's delegation of 22:17, as
  recommended): section 7.4 stays; Java 2026.4 makes the full check at
  every read (020-08, section 4.2), which 7.4 allows, and step 4's
  measurements (M2, M5) may later make its lookups the faster ones.
* **Q3. The Binson conversion: normative?** Section 10 makes the mapping
  a rule for a binding that converts, the method informative; Binson then
  is BergDB's interchange format with one result in every binding (4.2's
  consequences). *Recommended*: as written. The other choice: section 10
  informative, each binding free.
  *Decided* (2026-11-09, under the delegation, as recommended): section
  10 is normative for a binding that converts; Java converts only in its
  tests (`ObjectFormatTester`), as written.
* **Q4. Java's wrapping at the top** (`array`, `p`): a convention of the
  API, or a rule of the format that every binding keeps (a top-level
  array always read as an array)? *Recommended*: the API's (020-02,
  section 5.2 says "a rule of the API that the format keeps"), decided
  with question 5; section 12 says so. To the format they are objects.
  *Decided* (2026-11-09, under the delegation, as recommended): the API's
  convention, as Java's binding keeps it (020-09, section 5.9, and the
  package page); to the format they are objects.
* **Q5. Later formats.** Section 9 says that anything format 2 does not
  have comes with a new header byte, never as a new type byte inside a
  value of format 2, so that an old reader refuses a newer value at its
  first byte, with its version. *Recommended*: as written; it makes 4.3's
  "a hashed object type can come later under its own type byte, old
  values staying readable" exact.
  *Decided* (2026-11-09, under the delegation, as recommended): as
  written; Java's reader tells format 1 and format 2 by their first bytes
  and refuses any other.
* **Q6. The spec's home after the release, and the vectors'.** 4.12
  decided "a subitem of 020". *Recommended*: 020-07 stays the spec of
  format 2, frozen at the release (a later format gets a spec of its own,
  Q5), and the vectors move into `java/` with 020-08's step 1, beside the
  code that reads them, with this section pointing there; the Core's
  `doc-files/key-encoding.md` is the precedent for a format document in
  `java/`, if Frans wants the spec there too.
  *Decided* (020-08, section 2, item 5, its default; 2026-11-09 for the
  rest, under the delegation): the vectors are in
  `java/src/bergdb/pubimp/doc-files/object-vectors.txt` (41cb0ba); 020-07
  stays the spec of format 2, frozen at the release.
* **Q7. Names and index paths.** The format allows any name of 1 to 255
  bytes, `.` and `,` included (vector `names-odd`); an index definition
  names nested fields with `.` and separates names with `,` (`Data.Index`,
  "this will not handle DbObject fields that contain ',' or '.'").
  *Recommended*: the format stays as it is, and an index definition refuses
  a name it cannot hold (an index question, 020-01, section 6). Java's
  field names never contain either.
  *Settled* by 020-10 (sections 3.1 and 4.2): the format stays; an index
  definition stores a level's path as an array of names, any name of the
  format, '.' and ',' included (`nestedField(String[])`), so none is
  refused.

The approval of this spec's text under 018-01's rule stays with Frans: a
step of the release, not a blocker of the code (020-11). *Approved*
(Frans, 2026-11-09, 07:33): "I approve 020-07."


## 15. Sources

* [Binson]: BINSON-SPEC-1.1, https://binson.org/ (sections 1 to 6, the
  example, "Changes from BINSON-SPEC-1"), page version 2026-10-07, read in
  the clone `/Users/f/fl/repos/binson.org` at `46459bc`; CC BY-ND 4.0.
* RFC 3629 (UTF-8); the Unicode Standard, chapter 3, table 3-7
  (well-formed UTF-8 byte sequences); IEEE Std 754-2019 (binary64); RFC
  5234 (ABNF).
* BergDB: 020-02, sections 1, 4 and 5; 020-04, sections 3.3 and 11;
  020-05, sections 3, 5, 9 and 12b; 020-06, sections 3 and 14; 021-04,
  021-06, 021-07, 021-08; 018-01, section 2; 012-02 (a format written as
  a spec); `java/src/bergdb/pubimp/` at `21936d3`.
* The programs and outputs: `/Users/f/fl/bench/006-15/020-07/`;
  binson-java at `45346ad` (release 3.5), built by 020-05.


## 16. Log

2026-11-08. Drafted for coord-1108 at Frans's request (17:12), after his
twelve decisions of 15:51 to 17:09 (020-02, section 4), with the vectors
in `07-object-spec/vectors.txt` and the programs in
`/Users/f/fl/bench/006-15/020-07/`. No code changed. For Frans's approval
under 018-01's rule; questions Q1 to Q7 open.

2026-11-09. Q2 to Q5 decided under Frans's delegation of 22:17, as
recommended, and Q6 and Q7 recorded as settled (section 14), in night
006-15 (020-11); the spec's approval stays with Frans.

2026-11-09. Section 4.4's two examples rewritten at Frans's request: each
object's content in JSON, one notation for both, its numbers said to be
integers, and both dumps annotated alike (header, type byte and count,
ends, each field); Java's classes a side note, their names not stored.
No change of meaning; the bytes checked against the vectors `payment` and
`dialog`. Then, at Frans's request, in JSON5: the names unquoted, in the
annotations too, easier to read.

2026-11-09. Approved by Frans under 018-01's rule, 07:33: "I approve
020-07." Status: done.
