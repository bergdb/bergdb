# 020-02 Objects: the design, worked out with Frans

Created 2026-11-07 by Frans Lundberg. Status: open. The design of objects
(DbObject) for release 2026.4, decided by Frans one question at a time,
after 020-01's inventory: each question with its options in full, the
recommendation, and Frans's answer. The code follows when the questions
are answered.

The main study of objects' storage (Frans, 2026-11-08, 15:22): section 4
holds the decisions on object storage, from the studies 020-03 to 020-06,
ready for Frans one at a time; section 5 the API and the conversion
between `DbObject` and Java objects, not yet for decision; section 6
whether the studies are enough to decide.


## 1. The shape: decided

020-01, section 14, decision 2. Frans, 2026-11-07, 09:52: "Shape 1,
absolutely. Go slow here. I want to work out the details with you. I read
DbObject.java yesterday. I really like the concept. Read the comments of
it. At the very end too. The design is a limited supported set of types
that most (approximately "all") languages will support. It is meant like
a data storage format for objects in OO languages. Where the objects are
crafted for this purpose, for storage. We do not support serialization of
all types of Java objects. A real application will need to deal with
long-term stored db objects including type evolution. We need to discuss
thowing exceptions vs doing best-effort conversions."

So: objects stay, with a closed list of types (020-01, F1 b and F2 b),
and indexes are defined by data over their fields (F3 b). It is the
design of `DbObject`'s notes of 2013 (the comment at the end of
`DbObject.java`, "Types to support, notes"): "Serialization of existing
objects is not the goal; we assume specially crafted classes for data
storage. More important than supporting many types, is portability to
vast number of platforms and languages."

The stored types are `DbObject`'s eight: `n` boolean, `i` int (32 bits),
`l` long (64 bits), `d` double, `s` string (well-formed UTF-8, 021-04),
`b` bytes, `a` array (each element of any type), `o` object; and null for
`s`, `b`, `a` and `o`.

Note (2026-11-08): that is today's list. Under Frans's leans of section
4, no type has a null (4.1), and the values are Binson's (4.2), with one
integer type in place of `i` and `l` (4.7): Binson's seven types, which
are DbObject's eight with one integer and no null.


## 2. Question 1: a conversion on a get, exact or best effort? (decided: (C) for 2026.4)

**Decided**: (C), best effort, for 2026.4. Frans, 2026-11-08, 21:47: "This was a very hard decision for me. But for
2026.4, let's go with best-effort. This is how Java object are created
from DbObjects today. The interfaces stay the same or similar as today.
The Pub API is similar. We can iterator objects in the database easily.
This will problably need to evolve one more time, but let's get
something stable as a foundation. Something that works. Users who want
full control need to get object of type DbObject and from that convert
to Data Objects explicitely. Regarding puts and null fields. Allow it a
null-valued field in the Data Object. Such a field is not written, it is
not a field in the DbObject. Regarding gets. When a field name matches,
always make a conversion, best effort. There are many details for how to
do this. You can propose the exact rules."
So a get into a Data Object class converts every stored field whose
name matches a field of the class, best effort, and never throws for the
data; a caller who wants full control gets the `DbObject` and converts
by hand. (D)'s report (section 2.5) is not in 2026.4. The exact rules:
proposed by the coordinator (section 5.1b).

Frans, 10:03: "Will decide later today. Need to read and think."

A fourth option, (D), storage and conversion apart with a report, came
from Frans at 12:31 (section 2.5); not decided (14:26).

### 2.1. Where values are converted

1. **At a put**, from a Java value to a stored type. `byte`, `short`,
   `char` and `int` become `i`, `float` and `double` become `d`: no value
   changes. What is outside the closed list (`Date`, an enum, a `List`, a
   final field) is today sometimes stored as nothing, silently (020-01,
   S2-F9, F18, F19); under shape 1 the put refuses it, naming the field.
   This is assumed here; it is question 2's subject.
2. **At a get into the same class** that was put: an exact round trip,
   by the closed list. No question.
3. **At a get into a class that changed since the put**: type evolution.
   This is question 1. A database lives for years; the application's
   classes change; the old objects stay as they were written. And another
   language may have written the object (021-04, section 4): JavaScript
   has one number type, Python's `int` has no size, so another binding
   may store 5 as `l` or as `d`.

The cases of 3:

* a stored field that the class no longer has: ignored (the field was
  removed); today too;
* a field of the class that is not stored: keeps the value the
  constructor gave it (the field was added); today too;
* a number of another type: `i` into a `long`, `l` into an `int`, `l`
  into a `double`, `d` into a `long`;
* another kind: `s` into an `int`, a number into a `String`, `n` into an
  `int`;
* a null into a primitive field.

Today's faults of this part are best-effort conversions gone wrong
(020-01, section 5.3): a stored 1.5 read into a `String` field gives
"d:1.5" (S2-F4); a stored double of 2^63 read into a `long` gives
`Long.MAX_VALUE` (S2-F5); a null or another kind read into a primitive
gives 0, or throws `Bug` (S2-F6). And one exact-or-throw rule exists:
a stored number too large for its field throws `DataFormatException`
with the field's name (005-22).

### 2.2. The options

* **(A) Exact or throw, by the value** (recommended). A stored value is
  converted to the field's type only if the value read equals the value
  stored, as a number, a string or a boolean; else the get throws
  `DataFormatException` naming the field (its path), the stored type and
  the field's type. Whether it is exact is decided for each value: a
  stored `l` of 5 reads into an `int`; a stored `l` of 2^40 throws.
* **(B) Exact or throw, by the type.** Only the conversions that are
  exact for every value of the stored type: `i` into `long` or `double`;
  `l` into `long` only. A stored `l` into an `int` throws even when it
  is 5. The result does not depend on the data, but a value written by
  a binding with fewer number types (JavaScript, Python) is refused
  where it would fit.
* **(C) Best effort.** As Java's casts do: a `long` cut to an `int`'s 32
  bits, 1.5 into a `long` as 1, NaN as 0, a null into a primitive as 0, a
  number into a `String` as its text and back. A get never fails; the
  value read may differ from the one stored, silently.

The table of (A), stored type against the field's type (wrappers as
their primitives, with null allowed):

| Stored | Field's type | (A) gives |
|------|-------------------------|----------------------------------------------------------|
| `n`  | `boolean`               | the value                                                |
| `i`  | `int`, `long`, `double` | the value: exact for every `i`                           |
| `i`  | `byte`, `short`, `char` | the value if it fits; else throws                        |
| `i`  | `float`                 | the value if a `float` holds it exactly (all to 2^24 do) |
| `l`  | `long`                  | the value                                                |
| `l`  | `int` and smaller       | the value if it fits; else throws                        |
| `l`  | `double`, `float`       | the value if held exactly (all to 2^53, 2^24 do)         |
| `d`  | `double`                | the value                                                |
| `d`  | `float`                 | the value if a `float` holds it exactly                  |
| `d`  | `long`, `int`, ...      | the value if a whole number that fits; else throws       |
| `s`  | `String`                | the value                                                |
| `b`  | `byte[]`                | the value                                                |
| `a`  | an array type           | element by element, by this table                        |
| `o`  | a class                 | field by field, by this table                            |
| null | a reference type        | null                                                     |
| null | a primitive             | throws                                                   |
| any  | another kind            | throws (no number as text, no text as a number)          |

Two consequences of (A) to weigh:

* A `d` read into a `float` field throws unless the double is a float's
  value. A float put from Java always reads back (it was a float); a
  double such as 0.1 from another language, or from a field that was a
  `double`, does not. The application then uses a `double` field, or
  converts by hand.
* The failure depends on the data: an old object with a value that does
  not fit throws when it is read, maybe long after the class changed.
  The error names the field and the types.

Note (2026-11-08): under 020-05's option (f) (section 4.2) one integer
type replaces `i` and `l` (4.7), and the table's `i` and `l` rows become
one: "integer: into `long` always; into `int` and smaller if it fits;
into `double` and `float` if held exactly" (020-05, section 4). Option
(B) cannot be had then: the stored bytes no longer say whether the writer
had an `int` or a `long` (section 5.2). Under no stored null (4.1) the
two null rows become one, "absent: the constructor's value" (020-04,
section 7).

### 2.3. Why (A)

1. **No silent change of data**, the rule that 021-04 made for strings
   (Frans, 09:33: "option 1, absolutely"), here for numbers. Every value
   read equals the value stored, or the get says why not.
2. **A throw strands no data.** The application can always get the
   object as a `DbObject` (`get(key, DbObject.class)`) and convert its
   old forms itself. That is the way out for type evolution that (A) and
   (B) need and (C) hides.
3. **By the value, not the type, because of other languages.** A
   JavaScript or Python binding may write 5 as `l` or `d`; (B) would
   refuse it in a Java `int` field for no reason that the value shows.
4. **It is what 005-22 chose** for a number too large, and what the
   harness needs: a table that is the promise (020-01, F2 b), checked
   case by case.

### 2.4. Related questions, for later

* An application's own conversion: a way for a class to read its old
  forms (a constructor or a method that takes the `DbObject`), so that
  type evolution needs no second get. Or the `DbObject` get is enough.
* A field's type change that (A) refuses but the application wants, such
  as `int` to `String`: by hand, through the `DbObject` get, in (A).
* Renamed fields: not seen by name; by hand, as above.

### 2.5. Option (D): storage and conversion apart, with a report

Frans, 12:31: "Meanwhile, let's discuss conversion between Java object and
DbObject. I am not sure we can say what is best for the database user
here. I see throwing as problematic sometimes. Sometimes best effort is
better, but with feedback how the conversation went. There may be other
options then either best-effort or exact-or-throw. Feedback about how
conversation went together with best-effort. Sounds reasonable. Users
convert and can check what was done. One possibility is to work with a
ConversionResult object or similar. A possibility is to always retain the
DbObject so the database client can check exactly what was in the
database and how it was converted to Java object fields. Just thinking
out loud..."

Frans, 14:26: "About the Conversion design. Write it down. It sounds
pretty good. No decision yet. [...] I this is something I want to design
in detail. Important for usability, public API."

Not decided; a design to work out in detail with Frans.

**The idea: two steps.**

1. **The database** stores and returns a `DbObject`, exactly: what was
   put is what is read (`get(key, DbObject.class)`). Indexes are over
   its fields. This is the database's promise, the same in every
   language.
2. **The binding** converts a `DbObject` to an object of the
   application's class: a pure function of the `DbObject` and the class,
   outside the database, which never changes what is stored. It never
   throws for the data, and it reports how the conversion went.

So no one policy has to be the best for every user: the binding offers
the report, and the user decides what to do with it. And each language's
binding converts in its own way (Rust with a `Result`, Python setting
attributes), over one stored format.

**The put stays strict.** A best-effort conversion at a get cannot harm
the stored data; at a put it would store a changed value. So a put
refuses what it cannot store exactly (question 2, 021-04, question 1b),
and only the get side converts with a report.

**A sketch** (names to be chosen):

    DbObject o = c.get(key, DbObject.class);         // exactly what is stored
    Conversion<Person> r = Conversion.of(o, Person.class);  // never throws for the data
    Person p = r.value();      // the best-effort object
    r.isExact();               // true if every stored value was set exactly
    r.issues();                // per field: path, stored type, value, field type, what was done
    r.dbObject();              // the source, kept

    Person q = c.get(key, Person.class);  // convenience: exact, or throws an exception holding r

* Keeping the `DbObject` costs little: it is a view over the bytes that
  the get has read anyway.
* An exact conversion, the common case (the class did not change), can
  share one empty report: no cost beyond today's.
* The strict get's exception holds the `Conversion`: a caller that
  catches it has the best-effort object, the issues and the stored data.
  Throwing and best effort are then not two designs but one: the strict
  path is best effort that says so loudly.
* Question 1's table (section 2.2) still defines what is exact; (D)
  decides what happens when a value is not.

**What a report holds.** Each event of type evolution, by field path:

* a value set exactly (not listed; the report is about the rest);
* a value not set, because it cannot be converted exactly: the field
  keeps the constructor's value;
* a stored field that the class does not have: ignored;
* a field of the class that is not stored: keeps the constructor's
  value (under question 1b's (d), the one "no value").

**Questions for the detailed design:**

1. Best effort for a value that is not exact: leave the field at the
   constructor's value and report it (the coordinator's lean: it never
   invents a value), or set the nearest value (1.5 to 1, 2^40 to
   `Integer.MAX_VALUE`) and report it? A `d` into a `float` field may be
   the exception: the nearest float, since a float is approximate.
2. Which events make a conversion not exact: only a value not set, or
   also a missing or an ignored field (normal evolution)? Perhaps two
   levels: `isExact()` (no value lost) and `isComplete()` (the class and
   the stored object have the same fields).
3. The convenience `get(key, Class)`: strict (throws with the report) or
   lenient (returns the best-effort object)? Or both, as two methods, or
   a policy argument?
4. Unknown fields at a put back. An older version of the application
   reads an object that a newer version wrote, changes a field and puts
   it back: the fields its class does not know are lost. Protocol
   Buffers keeps "unknown fields" for this reason. Keeping the
   `DbObject` makes it possible: a put of the converted object with its
   source keeps the fields the class lacks. Wanted, and how?
5. An application's own conversion of old forms (section 2.4): a hook
   on the class that gets the `DbObject` and the report, or by hand
   through `Conversion.of`?
6. Scans and index reads: each result converted, with a report per
   result, or `DbObject`s only?
7. The names and the package: `Conversion`, `ConversionResult`,
   `ConversionIssue`; in `bergdb.pub` or a package of its own.


## 2b. Question 1b: should BergDB store null? (leaning: no null)

Frans, 12:15: "020-02. I would like to extend this by one more question:
should null be supported? Let's open up for the option of not supporting
storing null values. In general, null is a mistake. A billion dollar
historic mistake. However, many languages support it, so omitting the
possibility of storing null is not obvious. For binson (binson.org), I
chose to not support null values."

Frans, 14:31: "About null or not. Based on your investigation, I lean
towards: no null values. Make a note of this and prepare the required
changes. But don't code it yet. Might sleep on it or study it one more
time before I give it an ok-and-implement. Now it is ok to design and
document. Prepare for it."

So: leaning to no stored null; not yet decided, and no code until Frans's
"ok-and-implement". The design and the change plan are 020-04.

The study, with the languages, formats and databases, the programs run
and the sources, is 020-03; the labels below (BG3, JL3, ...) are its
program results.

### 2b.1. Null in BergDB today

020-03, section 5, from a probe of the jar at `b7fc20a`:

* Null is a value of four of the eight types: a null `String`, `byte[]`,
  array or object field is stored as a null `s`, `b`, `a` or `o`; a null
  `Integer` (any wrapper) as a null `o`, an object. An array element may
  be null, typed the same way.
* A null field and a missing field differ. A get leaves a missing field
  as the class's constructor set it, and sets a null field to null over
  that value: `String name = "dflt"` reads "dflt" from an object without
  `name`, and null from one with a null `name`.
* A null read into a primitive throws `Bug` (S2-F6), or reads as 0: a
  null `String` read into an `int` or an `Integer` field gives 0,
  silently (BG3, not known before; any `String` does, null or not:
  020-04, section 10).
* At the top there is no null already: `put(key, null)` is refused with
  `IllegalArgumentException`, and a key with no value reads as null.
* Indexes meet three kinds of "no value": a missing field and a null
  `Integer` give no entry; a null `String` in a string index makes the
  put throw `IllegalArgumentException` (019-42).

### 2b.2. What others do

020-03, sections 2 to 4:

* Most formats and document stores have both null and absence, and each
  draws its own line between them: MongoDB's `{x: null}` matches a null
  and a missing field, its `$type` and `$exists` split them; Firestore's
  `!=` skips both; SQL's `DEFAULT` applies to an absent column, not to a
  NULL given; Python's `d.get` merges them, JavaScript's `undefined` and
  `null` do not. Typed nulls, as BergDB's, are Amazon Ion's.
* No null: Binson; TOML ("just leave it out"); the Protocol Buffers wire
  format ("the serialization contains no information about not-present
  values"), whose JSON form reads a null as not set. proto3 had to add
  presence back (`optional`, release 3.15); it did not add null.
  Cassandra stores a null as a deleted cell.
* Serializers that write a null as absence: Gson by default,
  kotlinx.serialization with `explicitNulls = false`, Swift's `Codable`.
  kotlinx's documentation warns that "encoding and decoding can become
  asymmetrical": a null written reads back as the property's default
  (and Gson does so: JL3).
* Languages: null in every reference (Java, C#, JavaScript, Python), an
  explicit optional type (Rust's `Option`, Swift's and Kotlin's `T?`),
  or zero values (Go, C). Each has a rule for a missing field, as its
  JSON libraries show; absence must be handled in all of them anyway,
  since an object written before a field was added lacks it.

### 2b.3. The options

* **(a) Keep null** as a value, as today, for `s`, `b`, `a` and `o`, and
  fix its faults: a null into a primitive throws (question 1's table,
  its two null rows); a null in an indexed field gives no entry, as a
  missing field does; a null wrapper is stored as a null of its number
  type. A variant (a2): one untyped null, in a format version 2
  (question 3), for example `z`, which `DbObject`'s Javadoc reserves
  "for null-capability" (an array needs another byte, since `z` ends an
  array there). Consequences:
  * Every Java object reads back into its class exactly, with no rule
    about initial values and no constructor call at a put.
  * Two kinds of "no value" in every rule: question 1's table, the index
    function, the format's spec, the harness and every binding. A
    binding whose plain types have no null (Rust, Swift, Kotlin, Go, C)
    must make every `s`, `b`, `a` and `o` field optional, since any
    stored one may be null, besides handling absence. A binding with an
    untyped null (Python's `None`, JavaScript's `null` and `undefined`)
    must choose which typed null to write; (a2) removes that choice.
  * Three states can be stored: a value, "no value" (null), and "not
    written" (absent: an object older than the field), the distinction
    that SQL's `DEFAULT`, Cassandra's `UNSET` and MongoDB's `$exists`
    keep. A JSON document with null is stored as it is.
* **(b) No null: a null is refused** at a put, anywhere (a field, an
  array element, a nested object), with `IllegalArgumentException`
  naming its place, as for a lone surrogate (021-04). Binson's choice for
  its API: binson-java refuses a null at a put, and JSON with a null
  (BN1, BN3). Consequences:
  * The simplest format and reads: a field is present with a value of
    its type, or absent from an object older than the field.
  * A Java class has all its fields always, so it can never say "no
    value": an optional `String` must be "" or come with a flag, and an
    optional nested object cannot be said at all. An unset field, a
    `new String[n]` not filled, any object with a null, fails the put.
    proto3's lesson (presence was needed) applies. Binson's API avoids
    this by not adding the field; a put of a class cannot.
* **(c) Null is absence.** A null field at a put is left out of the
  stored object, as if the class had no such field; a null array
  element is refused, naming its index (an array has no absence, as in
  protobuf and Binson); a null at the top is refused, as today. A get
  of an absent field keeps the constructor's value, as today and in
  question 1. Consequences:
  * The format has no null: a present field always holds a value of its
    type. The null encodings (length −1, `Z`, field count −1) go with
    the format version 2 of question 3. Every binding maps its
    language's "no value" to absence and back, as its JSON libraries do
    for a missing field (020-03, section 6.2).
  * One rule for indexes: an object has an entry when each indexed field
    is present with an accepted type; today's three behaviours become
    one, and 019-42's refusal of a put goes.
  * Question 1's two null rows become one, "absent: the constructor's
    value", for every type, primitives included; the null cases of
    S2-F6 and BG3 go by construction (the rest is question 1's: 020-04,
    section 10).
  * Not a round trip in one case: a null put into a field that the
    constructor sets reads back as the constructor's value (`String
    name = "dflt"`, put with null, reads "dflt"). It is Gson's default
    (JL3) and kotlinx's documented asymmetry, and a silent change of data
    in the sense of 021-04 and of question 1's reason 1.
  * Two states only, a value or none. An application that needs "no
    value" apart from "not written" stores it explicitly (a flag, or a
    nested object).
  * A JSON null member converts to an absent field; a null in a JSON
    array is refused, as in protobuf's JSON form.
* **(d) Null is absence, exactly.** As (c), and a put is refused where
  its null would not read back: a null in a reference field to which
  the class's no-argument constructor gives a non-null value, with
  `IllegalArgumentException` naming the field and saying why (a get
  would read the constructor's value).
  Consequences:
  * As (c), and every put that BergDB takes reads back equal: the round
    trip is exact, and the constructor's value serves only the objects
    written before the field existed (type evolution).
  * The fields to check are found once per class and database, from one
    new instance (which reference fields are not null), as
    `BlankConstructorFactory` makes one for gets today; a put then costs
    a look-up per null field.
  * The class's constructor runs at a put, once per class and database,
    as it runs at a get today (a constructor that throws, S2-F21,
    becomes a put's question too). A class without a no-argument
    constructor cannot be read back into itself, so it is not checked,
    unless question 2 requires that constructor at a put.
  * Some puts that work today are refused, each with a message that
    names the field: the application sets the field, or drops its
    initial value.

### 2b.4. Recommendation: (d)

1. **One "no value", the one that cannot go.** Absence must be handled
   by every reader, in every language, for every field: an object older
   than its class's newest field, or one written in another language.
   Null adds a second "no value" to every `s`, `b`, `a` and `o` field,
   and every rule, binding and test doubles for it. Hoare's mistake is
   that every reference may be null; the languages that fixed it kept
   one explicit "no value" (`Option`, `T?`). (c) and (d) do the same in
   the format: a present string is always a string.
2. **Java's null maps to absence.** A class cannot leave a field out;
   null is how it says "not set". Under (d) a Java object says "no
   value" as a Binson object does, by the field's absence: Binson's
   choice, applied to classes. (b) leaves a class no way to say it.
3. **Faults go by construction**: a null into a primitive (S2-F6), the
   silent 0 of a null (BG3; a non-null `String` into an `int` gives 0
   too, which question 1 removes: 020-04, section 10), typed nulls of
   the wrong type (a null `Integer` stored as an object), three index
   behaviours (019-42); and question 1's table loses a row.
4. **(d) rather than (c): no silent change.** It is the rule of 021-04
   and of question 1's (A): every value read equals the value stored,
   or BergDB says why not, here at the put. (c) reads "dflt" where null
   was put, silently, as Gson does.
5. **Every language, one rule.** Under (d) a binding in any language
   writes and reads one kind of "no value", which every language has
   (`null`, `None`, `nil`, `undefined`, `Option`, a missing key). Under
   (a) a binding whose plain types have no null must make every string
   optional, and one with an untyped null must pick a type to write.

What (d) gives up and (a) keeps, for Frans to weigh: a third stored
state ("no value" apart from "not written"); JSON documents with null
stored as they are (a null array element is refused under (d)); and a
put of any Java object, with no rule about initial values and no
constructor call. If BergDB should store JSON documents as they are,
(a) is the better choice, with (a2)'s one untyped null. And (c) is the
fallback to (d) if running the class's constructor at a put is not
wanted: the same format, with the asymmetry documented.

### 2b.5. What (d) changes, if chosen

* Question 1's table (when both are decided): its rows "null, a
  reference type: null" and "null, a primitive: throws" become one,
  "absent, any type: the constructor's value".
* The put: a null field left out; a null array element, a null at the
  top, and a null over a non-null initial value refused with
  `IllegalArgumentException` naming the place (as 021-04's path).
* Indexes: no entry for an absent field, the one "no value".
* The format (questions 3 and 4): no null encodings; `z` stays
  `getType`'s answer for "no such field". (Corrected 2026-11-08: 020-04,
  section 3.2, keeps today's format at version 1, Q4; under 020-05's
  option (f) the format is a new one anyway, with a header 0x82: sections
  4.2 and 4.5.)
* `DbObject`, the stored object's view (`get(key, DbObject.class)`),
  has no null values; its `getString` of an absent field returns
  null, Java's way to say absent.
* Tests: 19 of `DbObjectTester`'s 72 tests at `b4cf896` set a null and
  4 more hold nulls by default (020-04, sections 5.1 and 10; 020-03,
  section 5.3, counted about a dozen); 13 of them are refused under (d)
  and 5 change their asserts. They become tests of the new rules, each
  failing on today's code.


## 3. The next questions

From 020-01, sections 4.5 and 5.5, one at a time after question 1:

* **Question 2: the closed list at a put.** Which Java types are stored
  and how (the primitives and their wrappers, `String`, `byte[]`, arrays
  of these, classes and records made of them, with a no-argument
  constructor); what a put of anything else does (refuse, naming the
  field); final fields, a field that hides another's (S2-F9, F19).
  And S2-F8, open: an `Object[]` that holds itself gives a
  `StackOverflowError` at the put, which fails the database inside
  `rw()` (021-08's Log); it goes if `Object[]` is not on the list, else
  the writer needs a cycle check for arrays, as 005-23 made for objects.
  A question of the conversion: section 5.
* **Question 3: the kind of a value.** Is it stored (a format version 2
  with the kind of a value; 020-01, N4), or told by the key's suffix and
  the `bergo` bytes, as today? Narrowed by 020-05 (2026-11-08): under its
  option (f) a 1-byte header, 0x82, before the object tells it from a
  `String` value and gives the format's version; a `byte[]` may still
  start with it (020-05, sections 7 and 12b.2). Section 4.5.
* **Question 4: the format and its spec** (020-01, section 14, decision
  7): under 018-01's rule that Frans approves format changes; a spec for
  other languages, with 021-06 (strings read that are not well-formed
  UTF-8). Binson as the format, a study: 020-05 (Frans, 20:42), which
  recommended (c1), Binson under a BergDB profile behind a short header,
  and since 2026-11-08 recommends (f), DbObject's table with Binson's
  values (020-05, sections 12b and 13); a field's lookup in (f) is
  measured in 020-06. Sections 4.2, 4.3 and 4.12.
* **Question 5: `put(Object)`, the field `key`, and `Object.class`
  gets.** The API's: section 5.


## 4. Object storage: the decisions

Frans, 2026-11-08, 15:22: "I lean towards: no nulls, binary search for
fields (no hash list), binson value format but not the whole Binson
format. The API and converting between DbObject and Java objects is not
yet decided, but there are good options that have been researched." And:
"I suppose we can use 020-02 is the main study here. We are getting
closer to a decision. I think we have the investigations needed to
proceed with decisions on object storage."

**All twelve decided** by Frans on 2026-11-08, 15:55 to 17:09, one at a
time, each with his words in its subsection: no null in the stored
format; (f); binary search; names of 1 to 255 bytes; the header 0x82;
arrays in Binson's framing; one 64-bit integer (question 1's (B)
dropped); Binson's NaN rule as a must, −0.0 kept; readers refuse
ill-formed UTF-8; depth 16, other limits as today; old objects refused;
the format under 018-01's rule, the spec a subitem of 020. Left for the
API (section 5): the put rule of 4.1 (020-04's Q1) and the `byte[]` case
of 4.5.

Object storage is what the bytes of a stored object are, and the rules
that every binding keeps when it writes and reads them: questions 1b, 3
and 4 of section 3, and the choices that come with a format. Each
subsection is one decision, for Frans to take one at a time: the
question, the options, the evidence by ID and section, the
recommendation, Frans's lean where he gave one, the consequences, and
what it leaves open. Nothing here is decided, but where a document
records Frans's decision in his words (021-04, in 4.9). The order: 4.1
to 4.3 first, as they shape the rest (4.7 comes with 4.2); then 4.4 to
4.12, each a few lines of the spec. The API and the conversion are
apart, in section 5; whether the studies are enough, in section 6.

| Decision            | Recommended                                   | Frans leans to |
|---------------------|-----------------------------------------------|-----------------|
| 4.1 Stored null     | (d): no null; null is absence, exactly        | decided: no null |
| 4.2 The byte format | (f): DbObject's table, Binson's values        | decided: (f)    |
| 4.3 Finding a field | B, binary search (020-06 measured: H16)       | decided: B      |
| 4.4 Names           | a 1-byte length, names of 1 to 255 bytes      | decided: (i)    |
| 4.5 Header, kind    | 0x82 before the top object                    | decided: (i)    |
| 4.6 Arrays          | Binson's framing (A1)                         | decided: (A1)   |
| 4.7 Integers        | one type, 64 bits, in the fewest bytes        | decided: (i)    |
| 4.8 Doubles         | one NaN pattern; −0.0 kept                    | decided: (i)    |
| 4.9 Strings         | well-formed UTF-8; a reader refuses others    | decided         |
| 4.10 Limits         | today's: depth 1,001 and 2,001; 32,767 fields | decided: depth 16 |
| 4.11 Old databases  | refused, with a message                       | decided: (i)    |
| 4.12 The spec       | under 018-01's rule; a subitem of 020         | decided         |

### 4.1. Stored null (question 1b)

* **The question**: does the format have a null value, or is a field
  without a value always absent?
* **The options** (section 2b.3; 020-04, section 2.6): (a) null kept, a
  typed null of `s`, `b`, `a` and `o` as today, or (a2) one untyped
  null; (b) no null, every null refused at a put; (c) no null, a null
  field left out, absent; (d) as (c), and a put refused where its null
  would not read back: a null over a non-null value that the class's
  no-argument constructor gives, and a null array element.
* **The evidence**: 020-03 (languages, formats, databases, and BergDB
  today, BG1 to BG6); section 2b.4; 020-04 (the rules, the format, the
  code sites, the tests).
* **Recommended**: (d) (section 2b.4; 020-04, section 8, Q1).
* **Frans leans to** no null: "Based on your investigation, I lean
  towards: no null values" (2026-11-07, 14:31), and "no nulls"
  (2026-11-08, 15:22). (b), (c) and (d) all store no null; which of the
  three is 020-04's Q1. Then his "ok-and-implement" (section 2b).
* **The consequences** (section 2b.5; 020-04, sections 1 and 7): one "no
  value", absence; a present field always holds a value of its type;
  question 1's null rows become one, "absent: the constructor's value";
  one index rule, and 019-42's refusal of a put goes; under (d) the
  class's constructor runs once per class at a put that meets a null
  field; some puts of today are refused, naming the field. Under (f)
  (4.2) there is no null encoding to remove: 020-04's step A goes, its
  rules stay (020-04, section 11).
* **Decided**, the format (Frans, 2026-11-08, 15:55): "Yes. Like Binson,
  no null values in the stored data." The stored bytes have no null
  value; a field without a value is absent. The put rule, (b), (c) or (d)
  (020-04's Q1), all three with the same bytes, is left for the API
  (section 5); (d) stays recommended.
* **What it leaves open**: 020-04's Q2 (a class without a no-argument
  constructor) and Q6 (`getString` of an absent field), both the API's
  (section 5). Its Q3 (an old object with a null) becomes 4.11 under
  (f); its Q4 (the version byte) goes with 4.2 and 4.5; its Q5 (the
  Builder refuses null) was done by 021-07, by that entry's default.

### 4.2. The byte format (question 4)

* **The question**: what are the bytes of a stored object?
* **The options** (020-05, section 12): (a) DbObject's version 1 kept,
  without null, its reader made strict and its reads through the table;
  (b) Binson under a BergDB profile; (c1) Binson behind a short header of
  kind and version; (c2) as (c1), with a table of the top-level fields;
  (d) DbObject's framing, its values moved towards Binson's types; (e)
  CBOR's deterministic encoding; (f) DbObject's table with Binson's
  values: a type byte that gives the offsets' width (1, 2 or 4 bytes),
  the field count, each field's end, then the fields in name order, each
  a name length, the name and a value in Binson's bytes (020-05, section
  12b.1).
* **The evidence**: 020-05: the types (section 4); the sizes (sections
  5.1 and 12b.3: (f) is Binson's size for an object whose fields take
  under 256 bytes, every sample among them, and n + 1 bytes more up to
  64 KB; today's format is 1.3 to 2.8 times larger); the reads (section
  6.2 and 12b.4; 020-06); one byte string per object and the reader's
  two levels (12b.5, F7); the writer (12b.6); the conversion to and from
  Binson by copying the values (12b.7, F2); other languages (sections 8
  and 12b.8); safety (12b.9, F6); governance (section 9); the cost, M, 3
  to 5 days (section 10); pros, cons and risks (section 11); prior art
  (12b.10).
* **Recommended**: (f) (020-05, section 13, since 2026-11-08; (c1)
  before).
* **Frans leans to** (f): "binson value format but not the whole Binson
  format" (2026-11-08, 15:22).
* **The consequences** (020-05, sections 11 and 13): about half today's
  bytes; a field found without a walk, at any position and depth; the
  values' bytes are Binson's, so a conversion to Binson copies them, and
  Binson can be the format of interchange; BergDB writes the whole spec
  (a page on objects, Binson's values by reference), a codec in each
  language (about 300 lines, 12b.8) and the conformance vectors; the
  writer must know each object's size before its table (12b.6); a new
  reader in the bug-free release; 2026.3's objects and index definitions
  are in the old format (4.11); 020-04's format part is replaced (020-04,
  section 11). What it gives up against (c1): a Binson library does not
  read the stored bytes as they are. Frans valued Binson's many
  implementations for a value read as raw bytes, through the Core API or
  by C reading a database that Java wrote (006-15, section 1, 09:01);
  under (f) such a reader goes through the converter, or (f)'s own
  reader.
* **Decided** (Frans, 2026-11-08, 16:08): (f), asked "Do you decide (f)
  as the format of stored objects?", answered "Yes."
* **What it leaves open**: 4.3 to 4.12.

### 4.3. Finding a field: binary search or a hash scan

* **The question**: does (f)'s table hold a hash of each name, scanned
  at a lookup (variant H), or only the ends, with a binary search on the
  names (variant B)?
* **The options** (020-05, section 12b.4; 020-06, section 3): B, no
  bytes added; H16, a 16-bit hash per field after the count (FNV-1a over
  the UTF-8 name, folded), 2 bytes a field, scanned one hash or four at
  a time (H16w); H8, 8-bit hashes; D, today's 6-byte entries. L, a scan
  of the names in order, reads B's bytes: a reader's choice, not the
  format's.
* **The evidence**: 020-06, measured in Java and C on F53: 1 to 100
  fields; hot, warm, cold and the index case; a `String` name; the cache
  lines read; the collisions of five hashes on 16,944 JDK names.
* **020-06's conclusion, as measured**: H16 is faster than B at the
  lookup, but in two corners (Java's hot misses from about 70 fields,
  and the index case from about 50): under 20 fields 1.1 to 1.5 times
  on hot hits, 2.3 to 3.1 on hot misses, 1.5 to 1.9 on cold misses from
  8 fields, 1.0 to 1.2 on cold hits (020-06, sections 1 and 13). It
  recommends H16 (section 14).
* **Frans leans to** B: "binary search for fields (no hash list)"
  (2026-11-08, 15:22).
* **Recommended** (here): B, as 020-05, section 12b.4, did before the
  measurement: no byte and no hash function in the format, for a
  difference that is small next to the work around a lookup.
* **Decided** (Frans, 2026-11-08, 16:17): B, asked "Do you decide B,
  binary search with no hash list?", answered "Yes!" A hashed object
  type can come later under its own type byte, old values staying
  readable.

The coordinator's summary, which Frans liked (2026-11-08): "The big gain
is reading fields through the table at all: a lookup is about 10 times
cheaper than today's full parse. Hash scan against binary search is a
second-order difference within that." Its numbers, checked against their
sources:

* **Today's read of one field** parses the whole object first: 340 to
  720 ns (020-05, section 6.2: 342 to 722 ns, one field of `Payment`,
  `Foobar`, an index definition and `Customer`, 3 to 12 fields).
* **A lookup in (f) by B**: 31 to 46 ns for a hit at 4 to 20 fields hot,
  43 to 65 warm (L2); 60 and 89 at 100 fields (020-06, section 6); 14 to
  22 ns hot in the index case, one field in every object of a class
  (section 9). So 5 to 23 times cheaper than today's read, about 10 for
  a typical object. The two benchmarks used other objects; 006-14's
  sketch of a lookup in today's table took 17 to 30 ns on 020-05's own
  objects (section 6.2).
* **B's extra over H16**, Java, ns a lookup, at 4 / 20 / 100 fields
  (020-06, sections 6, 7 and 9):

| State               | Hits            | Misses            |
|---------------------|-----------------|-------------------|
| hot (L1)            | +4 / +15 / +1   | +16 / +20 / −17   |
| warm (L2)           | +10 / +28 / +25 | +20 / +31 / +6    |
| cold, one at a time | +9 / +56 / +67  | +37 / +143 / +198 |
| index case, hot     | 0 / +6 / −5     | +3 / +6 / −56     |

Against the word scan H16w, which 020-06 recommends for Java, B's extra
is +16 ns on hot hits at 20 and at 100 fields, +25 and +16 on hot misses.

The hot and warm rows are the realistic ones, the coordinator said: a
value's bytes are copied before any field lookup, so they are in the
cache. Checked against the read paths at `72278e5`:

* **True today, on every path.** `DbObject`'s constructor copies the
  bytes (`b.clone()`, `DbObject.java`, line 155), walks them for
  021-08's depth check and parses every field, before any lookup; and
  every path that reads a field makes one: a get and a scan
  (`KvToObjectImp.entryToDbObject`), index maintenance (the previous
  value, `RwEnvironmentImp`, line 401), a build (`IndexBuilderImp`, line
  489) and the index definitions at a start (`IndexManager`, line 535).
* **Not from the stream, for a value in memory.** The Core's get then
  returns its own array (`Db.getOne`'s Javadoc), and so does the Pub
  API's get as `byte[]`, by Frans's choice of zero-copy gets (015-47,
  2026-11-05), which index maintenance uses for the previous value
  (`RwEnvironmentImp`, line 396). The copy is `DbObject`'s. A value not
  in memory is read from the stream into a new array.
* **Under (f), only if its reader copies or checks first.** 020-05,
  section 13, sketches `DbObject` as a view that reads its header at
  construction and each field by a lookup. A view that keeps today's
  copy keeps the warm rows; a view over the database's own array, in the
  spirit of 015-47's zero-copy gets, makes a lookup the first read of a
  value in memory, and the cold rows apply to index maintenance's
  previous value and to a build: B's extra up to +56 ns a hit and +143 a
  miss at 20 fields, +67 and +198 at 100. Whether `DbObject` copies is
  the API's (section 5).

A whole get and a commit, for scale: F53, one thread, release 2026.2
(016-10), the Core API's gets of a value's bytes:

* about 0.8 µs at 200,000 keys of 1 KB in memory (the quick suite's
  read-1k: `get_latest` 1.25 to 1.26 million a second, p50 0.67 µs in
  its result files);
* about 1.5 µs at 10M keys in memory, uniform (ScaleBench M, G1: 657,000
  a second, p50 1.46 µs);
* about 3.8 µs at 10M keys with a 665 MB cache and the rest from the OS
  cache (ScaleBench C, G1: 265,000 a second, p50 3.29 µs, p99 8.96 µs);
* a commit of one KV, 10 to 20 µs (50,000 to 100,000 a second: 99,000
  in w-uni-1k-inf, 64,000 in w-uni-1k-fin, 52,000 in r-1k-fin's mix).

So B's extra, at most 35 ns hot or warm from 1 to 100 fields (31 at 4,
20 and 100), is up to 4.4 % of a 0.8 µs get (2.5 % hot), up to 2.3 % of
a 1.5 µs get, under 1 % of a 3.8 µs get, and about 0.3 % of a commit:
the coordinator's "about 1 to 2 % of an in-memory get" holds at 10M keys
(at most 1.3 % hot, 2.3 % warm), and is up to 4.4 % at 200,000. Cold,
it is up to 5 % of a 1.5 µs get for a hit (73 ns at 32 fields) and up
to 13 % for a miss (198 ns at 100 fields). These are per lookup, and a Pub get of an object adds the
Pub layer and the decode to the Core's get (today 665 to 1,972 ns into a
class, 020-05, section 6.2). A get into a class or a scan needs no
lookup at all if its decoder walks the stored fields in name order beside
the class's fields in the same order (020-05, section 12b.5: they "read
every field anyway"); today's `toJavaObject` looks up each of the
class's fields. Lookups are in index maintenance (each indexed field of
the previous value and of the new one, inside a commit), in builds, in
`DbObject.getX` and in the index definitions read at a start.

What the hashes would cost, besides their speed:

* **Space**: 2 bytes a field, nested objects included: `Person` 15
  bytes, 17 with hashes; `Account` 13 and 15; `Dialog` 36 and 44;
  `Payment` 35 and 41; `Data.Index` (1 level) 95 and 105; `Foobar` 181
  and 195; `Customer` 225 and 249: 8 to 22 % more (020-05, section
  12b.3); 6.4 to 7.4 % on 020-06's objects (020-06, section 4). Under B,
  (f) is Binson's size.
* **A hash function in every binding's spec** (FNV-1a over the UTF-8
  bytes, or Java's `String.hashCode` folded: 020-06, section 14, point
  5), computed by a `get(String)` at each call (15 to 19 ns hot, section
  10).
* **A rule for a strict reader**: each stored hash is its name's. Without
  it a field is invisible to a lookup, as today (DB2, 020-05, section
  5.2); 020-06, section 14, sets no rule on equal hashes, and this one
  would join (f)'s full check (020-05, section 12b.1).
* **What a weak hash does**: today's takes 2,145 of the 65,536 values on
  16,944 JDK names, and half of the 20-field objects hold two names with
  one hash (020-06, section 11).
* **Room for later**: (f)'s objects are told by their type byte (0x48 to
  0x4a); a hashed object type, with type bytes of its own, can be added
  in a later format if ever needed, with old values staying readable.
  The spec would then say which type a writer uses for an object, to
  keep one byte string per object (P2).

And:

* **The consequences of B**: no bytes, no hash function and no hash rule
  in the format; a lookup reads at most ⌈log2(n + 1)⌉ names, 2 for
  `Payment`, 4 for `Customer`, 7 at 100 fields (020-05, section 12b.4);
  a hot miss takes 11 to 33 ns up to 20 fields, 2.3 to 3.1 times H16's;
  a `get(String)` compares by chars, 14 to 31 ns more a hot hit up to 20
  fields (B-S, 020-06, section 10), or makes the name's UTF-8 bytes
  first, while an index function holds its names as bytes.
* **What it leaves open**: the reader's way on B's bytes (a binary
  search, or a scan of the names for objects of a few fields); names kept
  apart from the values, as in PostgreSQL's JSONB, which would let B's
  probes read one area (020-05, section 12b.10; not measured, 020-06,
  section 15).

### 4.4. Names

* **The question**: how long may a field's name be, and how is its
  length stored?
* **The options** (020-05, section 12b.11, question 3): (i) a 1-byte
  length, names of 1 to 255 bytes; (ii) a length of w bytes, as the
  ends: no limit but the object's size, and n bytes more in objects of
  256 bytes to 64 KB. Today 1 to 32,767 bytes (005-21); Binson 0 to
  2^31 − 1, and it recommends at most 50 characters (020-05, section
  5.4).
* **Recommended**: (i) (020-05, section 12b.11).
* **The consequences**: a put of a class with a longer field name is
  refused, naming it; a Binson object with an empty or a longer name
  does not convert to (f) (12b.7). Fixed in every option: names of
  well-formed UTF-8, the fields in strictly increasing order of their
  names' unsigned bytes, so no two fields share a name (12b.1, rule 4;
  Binson's order and today's).
* **Decided** (Frans, 2026-11-08, 16:19): (i), asked "Do you decide (i),
  names of 1 to 255 UTF-8 bytes with a 1-byte length?", answered "Yes".
* **What it leaves open**: nothing.

### 4.5. The header byte and the kind of a value (question 3)

* **The question**: is the kind of a value (an object, a `String`,
  bytes) stored, and where?
* **The options** (020-05, sections 7 and 12b.2): (i) a header in the
  value, the byte 0x82 before the top object, which is also the
  format's version (format 2; a later one 0x83); (ii) the kind in the
  Core's entry, a change of the stream under 018-01's rule; (iii) a rule
  of keys or directories, no header (an object key or an indexed
  directory holds objects only: 020-01, section 14, decision 6), and
  `Payment` is 35 bytes. Today: no suffix (or `.obj`) and bytes that
  start with `bergo` (020-01, N4).
* **Recommended**: (i) (020-05, section 12b.11, question 4).
* **The consequences**: no well-formed UTF-8 starts with a byte from 0x80
  to 0xbf, so a `String` value is never taken for an object (N4's case
  for strings); 1 byte a stored object; the format's version is in every
  value, and a reader tells a 2026.3 object (`b`, 0x62) at its first
  byte (4.11).
* **What it leaves open**: a `byte[]` at an object key may start with
  0x82, as with `bergo` today, so a build, an `Object.class` get and a
  primary scan still guess for bytes: settled by (iii) beside (i), or
  left as a documented guess; with 020-01's decision 6 and 015-46.
* **Decided** (Frans, 2026-11-08, 16:22): (i), asked "Do you decide (i),
  the byte 0x82 before each stored object as its kind and format
  version?", answered "Yes". The `byte[]` case stays with the API
  (section 5; 020-01's decision 6).

### 4.6. Arrays

* **The question**: how is an array framed?
* **The options** (020-05, section 12b.1): (A1) Binson's, 0x42, the
  elements, 0x43, walked; (A2) a count in place of the end byte; (A3) a
  size; (A4) a table of the elements' ends.
* **Recommended**: (A1) (020-05, section 12b.11, question 5): no index
  reads an array, a get reads an array whole, a lookup skips an array
  field by the table without a walk (W's case), and the bytes are
  Binson's, so a conversion copies an array that holds no object.
* **The consequences**: element i needs a walk; an object in an array
  carries its own table and size, so it is skipped without a walk; the
  elements may be of any types, mixed, as in Binson and today.
* **Decided** (Frans, 2026-11-08, 16:24): (A1), asked "Do you decide
  (A1), Binson's framing for arrays?", answered "Yes, A1."
* **What it leaves open**: (A4), as a new type byte in a later format,
  if element reads or indexes over arrays come.

### 4.7. Integers: one type

* **The question**: one integer type, or `i` (32 bits) and `l` (64 bits)
  as today?
* **The options**: (i) one, Binson's: a signed 64-bit integer in the
  fewest bytes, 1, 2, 4 or 8 (020-05, section 3); (ii) two, as today and
  in (a). (f) has (i) with its values.
* **The evidence**: 020-05, section 4; question 1's (A), "by the value,
  not the type" (section 2.3, reason 3).
* **Recommended**: (i) (020-05, sections 4 and 13).
* **Frans leans to** it with 4.2, "binson value format".
* **The consequences**: a Java `byte`, `short`, `char`, `int` and `long`
  each become an integer, and 5 has the same bytes in each (2 bytes,
  0x10 05, against 5 for `i` and 9 for `l` today); the bytes no longer
  tell an `int` from a `long`, so a get decides by the value (section
  5.2); a long index reads the integer (`FieldIndexFunction` reads `i`
  and `l` today); a JavaScript or Python binding need not choose a
  width; a value beyond 64 bits (Python's `int`, a JavaScript `BigInt`)
  is refused at its put.
* **Decided** (Frans, 2026-11-08, 16:25): (i), asked "Do you decide (i),
  one signed 64-bit integer type, and with it drop question 1's option
  (B)?", answered "Yes". Question 1's (B), exact by the stored type, is
  dropped; (A), (C) and (D) remain (section 2). A value beyond the
  signed 64-bit range is refused at its put.
* **What it leaves open**: question 1's rules, and what
  `DbObject.getType` answers for an integer (section 5).

### 4.8. Doubles: NaN and −0.0

* **The question**: may a stored double be any 64-bit pattern, or one
  pattern per value?
* **The options**: (i) every NaN written as `0x7ff8000000000000`, and a
  reader refuses another NaN pattern (020-05, section 9, rule 4, and
  section 12b.1, rule 5); (ii) any pattern kept, as today (DB7,
  `doubleToRawLongBits`), so that one Java value (`Double.equals`) has
  several byte strings. In both, −0.0 is kept apart from 0.0, as in
  Binson and today (BJ13).
* **Recommended**: (i), with −0.0 kept: one byte string per object (P2;
  020-05, section 12b.5), and Java's `Double.equals` and
  `doubleToLongBits` already treat every NaN as one.
* **The consequences**: a Java writer writes `doubleToLongBits`; a NaN's
  payload, which Java's `==` and `equals` do not show, is not kept: a
  change that only `doubleToRawLongBits` sees, which Frans may or may not
  count under 021-04's "no silent change" (the alternative is to refuse
  such a NaN at the put); −0.0 reads back as −0.0; a `float` is stored as
  a double, as today.
* **Binson** (BINSON-SPEC-1.1, binson.org, read 2026-11-08): "A double is
  its 64-bit pattern, interpreted as an [IEEE-754] binary64 number";
  recommendation 6: "A writer should store NaN as the bit pattern
  0x7ff8000000000000 (a positive, quiet NaN)", because "different
  programming languages produce different NaN bit patterns by default";
  −0.0 is not named, so it is its own pattern and value; no rule for a
  reader (binson-java reads any NaN, 020-05, BJ12). (i) follows Binson:
  its "should" a must for a writer, which rewrites any NaN to the one
  pattern rather than refusing it (other patterns come from ordinary
  computation), and a BergDB reader refuses another pattern, as 021-07's
  strict reader; bytes from Binson come in through the converter, which
  rewrites NaN.
* **Decided** (Frans, 2026-11-08, 16:34): (i), asked "Do you decide that,
  Binson's NaN rule made a must for writers, readers refusing other NaN
  patterns, and −0.0 kept as Binson keeps it?", answered "Yes, and this
  was the recommendation from before my Binson question anyhow."
* **What it leaves open**: what a double index does with NaN and −0.0
  (020-01, section 6.5, question 1; 020-04, section 2.5), an index
  decision.

### 4.9. Strings: well-formed UTF-8, written and read

* **The question**: what is a stored string or name, and what does a
  reader do with bytes that are not one?
* **Decided for writers**: 021-04, option (1) (Frans, 2026-11-07, 09:33:
  "Yes, option 1, absolutely"): every string, keys and field names too,
  is a sequence of Unicode scalar values stored as well-formed UTF-8; a
  writer refuses others before anything is written. 021-05 did the
  Core's String puts.
* **Open for readers**: 021-06 (open), its question 1: report or
  repair. Under (f) the full check refuses ill-formed UTF-8 in names and
  strings (020-05, section 12b.1, rules 4 and 5), and a lookup checks
  the value it returns (12b.5). So (f)'s spec answers 021-06's question 1
  for objects, and its question 3: a `DbObject` put from bytes gets the
  full check (12b.5).
* **Recommended**: a reader refuses, with `BadFormatException` (at a
  get `ObjectCreationException`, in index maintenance
  `DataFormatException`), in every language: 021-06's default.
* **The consequences**: stricter than Binson 1.1, whose rule is a
  recommendation ("A Binson implementation need not check this"); a
  conversion from Binson checks it (12b.7).
* **Decided for readers** (Frans, 2026-11-08, 16:37): asked "Do you
  decide that readers refuse ill-formed UTF-8 in names and strings, with
  `BadFormatException`?", answered "Yes". For objects, 021-06's
  question 1 is answered: refuse, not repair.
* **What it leaves open**: 021-06's keys and `String` values, outside
  objects (its questions 1 and 2).

### 4.10. Limits: depth, fields, sizes

* **The question**: which limits does the spec name, so that every
  binding meets them?
* **The options and the evidence**: depth: today 1,001 objects, and 2,001
  objects and arrays, on a path (021-08; the writer's `MAX_DEPTH`, 1,000
  objects, 005-23), or lower so that small readers meet it:
  binson-c-light allows at most 255, binson-python stops at Python's
  recursion limit (020-05, sections 5.4 and 9, rule 2). Fields: today
  32,767 (12b.1, rule 6); Binson "should" be under 100, binson-java's
  reader refuses more than 1,000 by default; Frans: "Normally, we have
  fewer than 100 fields of an object" (2026-11-08, 09:32). Size: an
  object below 2^31 bytes, by its 4-byte ends (12b.1, rule 6); Binson
  recommends under 40 million bytes.
* **Recommended**: today's numbers, as 020-05's (f) keeps them (12b.1,
  rule 6): they refuse nothing that 2026.3's writer writes, and 021-08's
  tests hold them. A lower depth only if small readers (006-08's C
  target) should read every object without a deep stack. No study chose
  other numbers.
* **The consequences**: a reader checks each limit before it recurses or
  allocates (12b.9, F6).
* **Frans on depth** (2026-11-08, 16:43): "Yes by default. But depth
  should change. Not sure what is best here. I really see little need
  for above 5 or something. This is a storage format for single entries
  in a database. Databases can have depth = 1, like a typical SQL
  database. So, is there really a reason for depth 1000 or 100?" The
  coordinator's answer: no; today's 1,001 is the writer's `MAX_DEPTH`
  (005-23), a guard against a deep stack, not a need. Deep nesting
  elsewhere serves documents from outside (MongoDB 100 levels, serde_json
  128, Jackson about 1,000) and recursive structures, which in a database
  are entries linked by keys; a nested object is a copy, DbObject has no
  references. A limit can be raised later (stored values stay valid; the
  header's version can mark it) but not lowered. A deep but real value,
  arrays counted: `Customer`, `orders` [ ], `Order`, `lines` [ ], `Line`,
  `product`, `price`: 7.
* **Decided** (Frans, 2026-11-08, 16:52: "Yes, 16 is good"): one depth
  limit, 16, counting every level, objects and arrays alike, the top
  object level 1 (in place of today's 1,001 objects and 2,001 objects and
  arrays); a put of a deeper object is refused, naming its path, and so is
  a conversion of deeper Binson. The other limits as today: at most
  32,767 fields an object, an object under 2^31 bytes ("Yes by
  default").
* **What it leaves open**: nothing beyond the numbers.

### 4.11. Old databases

* **The question**: what does 2026.4 do with an object or an index
  definition written by 2026.3 or before (`bergo`, version 1)?
* **The options**: (i) refuse: a get of an old object throws
  `ObjectCreationException`, index maintenance `DataFormatException`,
  each naming the old format; a start that reads an old index definition
  is refused with a message, as 005-50 refused databases without the
  node size; (ii) keep today's reader of version 1, made strict by
  021-07 and 021-08, for reads only, every write in (f); (iii) a
  migration that rewrites the values, with (i) at a start.
* **The evidence**: Frans, 2026-11-06, 12:05: "No need for any
  backwards-compatibility"; 020-04, section 3.2 and Q3 (for version 1:
  an old object with a null refused, recommended); 020-05, section 10
  (every database with an object or an index stops opening unless a
  reader of version 1 is kept; the night tests' and benchmarks'
  databases made again, as after 005-50).
* **Recommended**: (i): the simplest code and spec, and the header tells
  an old value by its first byte (4.5).
* **The consequences**: databases with objects or indexes are made again;
  StreamDigest's workloads put no object, so no digest changes (020-04,
  section 3.2); the release notes say so.
* **Decided** (Frans, 2026-11-08, 17:06): (i), asked "Do you decide (i),
  refusing old objects and index definitions with a clear message?",
  answered "Yes, (i)." No database with objects needs (ii) or (iii).

### 4.12. The spec, its home, and 018-01's rule

* **The question** (question 4; 020-01, section 14, decision 7): is the
  object format under 018-01's rule that Frans approves every change of
  the stream's format, and where is its spec written?
* **The options**: under the rule, or not (objects are values to the
  Core, but the index definitions are objects that every start reads:
  020-04, section 3.2); the spec in a subitem of 020, as 012-02 wrote
  the stream's in an item, or beside the code, as the Core's
  `doc-files/key-encoding.md`; with conformance vectors shared by every
  binding (020-05, section 8.2).
* **Recommended**: under the rule (020-04, section 3.2; 020-05, section
  9): Frans's decision of 4.2 is then the approval, recorded in 020's
  log. The spec: no document recommends a home; a subitem of 020, written
  with the implementation, is the default: (f)'s rules (020-05, section
  12b.1), Binson's values by reference to BINSON-SPEC-1.1 (its licence,
  CC BY-ND 4.0, allows citing it: 020-05, section 9), 020-04, section
  3.3's text on absence, 4.4 to 4.10, and the vectors.
* **Decided** (Frans, 2026-11-08, 17:09): asked "Do you decide that the
  object format is under 018-01's approval rule, with today's decisions
  as your approval of the design and the spec as a subitem of 020 for
  your approval before release?", answered "Yes". The decisions of 4.1
  to 4.11 are the approval of the design (020's log, 2026-11-08); the
  spec and its vectors, a subitem of 020 written with the
  implementation, come to Frans for approval before the release.
* **What it leaves open**: the index keys' format (the sort keys, ICU:
  020-01, section 14, decision 3), outside objects.
* **The spec and the plan** (2026-11-08, at Frans's request, 17:12):
  020-07, the spec with its vectors, for his approval; 020-08, the
  implementation plan, for his "ok-and-implement".


## 5. Not yet for decision: the API and the conversion

Frans, 2026-11-08, 15:22: "The API and converting between DbObject and
Java objects is not yet decided, but there are good options that have
been researched." And 2026-11-07, 14:26, on (D): "I this is something I
want to design in detail. Important for usability, public API." Kept
apart from section 4, for later.

Frans, 2026-11-08, 17:26, reading `WebsiteCode.java` and `PayDemo.java`
(java/src-dev/frans/): "I like this. Everything is just plain Java,
including index creation and atomic payments. Nice to have such storage
garantees without the hassle of Java and SQL mixed. I like it. So the main
design is good as is. Let's keep it." The Pub API's shape stays: plain
Java objects put and got by key, indexes defined in Java, atomic
transactions as `rw()` actions; the questions below refine it.

### 5.1. What is open

* Question 1, a conversion on a get: (A) exact or throw, by the value;
  (B) by the type; (C) best effort; (D) storage and conversion apart,
  with a report (sections 2.2 to 2.5), and (D)'s seven questions for its
  detailed design (section 2.5).
* Question 2, the closed list at a put (section 3), with S2-F8; and
  020-04's Q2, a class without a no-argument constructor.
* Question 5, `put(Object)`, the field `key` and `Object.class` gets
  (section 3; 020-01, section 14, decision 6, recommends dropping
  `put(Object)` and the field `key`).
* `DbObject`'s API: what `getString` of an absent field gives (020-04,
  Q6); what `getType` answers for an integer; a key form for repeated
  lookups (020-06, section 14, point 4; under B, a name's UTF-8 bytes);
  whether a `DbObject` copies the bytes it is made from (section 4.3,
  where it decides between the warm and the cold costs); whether it is
  public.
* The decoder into a class: a walk of the stored fields beside the
  class's fields, both in name order, with no lookups, or a lookup per
  class field, as today (section 4.3).

### 5.1b. Decided for the API

* **A null field at a put: left out, (c)** (020-04's Q1; 4.1's put
  rule). See section 2's decision (Frans, 21:47): "Allow it a
  null-valued field in the Data Object. Such a field is not written, it
  is not a field in the DbObject." No put is refused for a null field;
  a get then leaves the field at the constructor's value (020-04,
  section 2.6, where (c) and (d) differ). 020-08's step 5, (d)'s
  constructor check, is not needed.
* **The rules of best effort at a get** (question 1, (C)). The
  coordinator proposed principles and a table (21:48); Frans, 21:56, on
  its principle 4 (a field kept at the constructor's value where no
  sensible conversion exists): "Not sure about principle 4. I was
  leaning towards always converstion for a matching field. If there is a
  field name match, the fields data always depends only on the database
  value, not of a Java default. Otherwise, matching fields mean either
  that depend on default values from a constructor (which can change
  over time) or the value in the database. Even field values will be
  "invented", I prefer to have them depent solely on the database value.
  How about this?" Revised: a matching field always gets a value that
  depends only on the stored value and the field's type; where no
  sensible conversion exists, the type's zero (`0`, `0.0`, `false`,
  `'\u0000'` for primitives and their wrappers; `null` for `String`,
  `byte[]`, arrays and Data Objects); only a field without a stored
  match keeps the constructor's value. Frans, 21:59: "Yes, do so." The
  rules in full, with a test for each: 020-09 (its sections 3 to 5, the
  tests in its section 8; what was left open, decided under Frans's
  delegation of 22:17, in its section 6).
* **Two layers** (question 1's architecture, (D)'s two steps of section
  2.5). Frans, 2026-11-08, 19:53: "Important, this should be completely
  separate from DbObject to database storage. So, DbObject to bytes
  stored. [...] Next layer is the Java object to DbObject conversion.
  This is separate. The user can choose to work with DbObjects directly,
  or even with byte[] directly." And, 20:23, to the coordinator's
  question whether to record it as decided: "About the two layers, yes.
  Internally, this is two separate layers. The top level API will allow
  Person a = c.get("/adam", Person.class), that is DbObject is often not
  used directly at that layer, but it can be. Up to the user. One example
  is for migration, it can be useful to use DbObject explicitely then."
  So: layer 1, a `DbObject` and its stored bytes, exact (section 4,
  020-07); layer 2, the conversion between Java objects and `DbObject`s,
  a binding apart from storage; the API offers both, and `byte[]`.
  What stays open is layer 2's policy: (D)'s questions (section 2.5), the
  put's closed list (question 2) and the put rule of 4.1.
* **Data Objects: public fields only** (question 2, in part). Frans,
  2026-11-08, 20:32, reading `DbObject.getEligibleFields()` (every field
  that is not final, static, transient or synthetic, at any access, made
  accessible by `setAccessible`): "To me it indicates that private fields
  are also read and written. Not sure we really want this. I was
  thinking this serialization is primarily designed with classes created
  for the purpose. Then fields can be made public. [...] Would be a
  clean rule to read/write public non-static fields only." The
  coordinator's case: shape 1's classes crafted for storage; no deep
  reflection (`setAccessible`), which a modular application must permit
  by `opens`; to reflection from another package, a package-private or
  protected field is as closed as a private one, so the line is public
  against the rest; `transient`, Java's keyword for a field outside an
  object's stored state, stays the way to leave a field out. Frans,
  20:44, to "Do you decide (i), public only, with other instance fields
  refused unless transient?": "Yes, let's go for public fields only. For
  2026.4." The rule: BergDB stores the public, non-static, non-transient
  fields of a public class with a public no-argument constructor,
  inherited public fields included; a put refuses a class with another
  instance field that is not transient, naming the field (nothing is
  stored as nothing). Left to question 2: a public final field (the
  coordinator's lean: refused, as a get cannot set it); records (their
  components are private final fields: a later addition, by their
  accessors and canonical constructor, the coordinator's lean).
* **The layers, in Frans's words** (2026-11-08, 20:44): "I think we can
  view this as layers: bytes stored in database -- DbObject -- Data
  Objects (public fields, designed for storage) -- App Objects (ordinary
  application objects). Converting from bytes stored to Data Objects is
  good. We can immediately get typed composite data structures from raw
  bytes. We can immediate use them in ordinary Java code. We allow
  creation of special Data Object classes, structures really. Instead of
  aiming for direct application object serialization /
  deserialization." So BergDB converts between its bytes, `DbObject`s
  and Data Objects; between Data Objects and an application's own
  objects is the application's.
* **No key field in the object: `put(Object)` goes** (question 5;
  020-01, section 14, decision 6, as it recommended). Frans first
  decided, 2026-11-08, 19:10: "Decision: use dbKey for the database key.
  Allow env.put(Object) when its dbKey field is ok. And as you say,
  env.put(key, obj) works for an obj with a dbKey field iff key ==
  dbKey." Then, 19:13: "I am about to change my mind. How about this. We
  remove this now. No special dbKey field. Main reason: it adds some
  complexity that is hard to remove. Adding it is easy. Compatible API.
  Easy to add, hard to remove. So, add if there is demand only.
  Correct?" And, final, 19:21: "OK, hard to decide. Might add it back in
  a future release, we will see. But for 2026.4, my final decision is:
  no dbKey field. Add the possibility of adding it back in
  017-07-to-consider." (017-07, section 6.) Confirmed by the coordinator, with one condition: a later
  key field must be opt-in (such as an annotation on the field), since a
  name rule added later would change the meaning of classes that
  already have a field of that name, stored as an ordinary field. The
  case for the field, kept for a later demand: read-modify-write without
  carrying the key, and "read from one key, put at another" refused;
  `key` was a field of 127 of the 12,700 JDK classes with fields,
  `dbKey` of none (020-06's name set, counted 2026-11-08). Without it, a
  scan or an index read gives the key with the object (`kvs()`), and a
  put names its key: `env.put(k, a)`.
  * What goes in the code: `put(Object)` in `WBuilder` and
    `RwEnvironment`, `MissingKeyFieldException`, the key field's
    handling in `DbObject` and `PubUtil` (a get answers `key` with the
    database key), their tests (`PubTester`), the Javadoc
    (`package.html`, `overview-pub.html`, `DataFormatException`), and
    `PayDemo`'s `env.put(a1)` (java/src-dev/frans/, which the
    implementer may change). A field named `key` is then an ordinary
    field. To be added to 020-08 as a step.

* **`createFast()` goes** (020-01, section 14, decision 6, as it
  recommended; 020-01, F4). Frans, 2026-11-08, 19:24: "Why was this
  added? What is the reason? Seems a bit strange. But knowing myself,
  there might be a good reason. Let's find this first." Found (19:25):
  the 2012-10 notes ("Create index") design an index over existing
  objects as a background job in many transactions, with a "creating"
  state: `start()`, returning a `Job`. `createFast()` is in the first Git
  commit (2013-06-06, before release 2013.1), with today's Javadoc
  ("Creates this index immediately and makes it active without adding
  index entries for existing database objects") and today's code (the
  index set active, no job); it served the setup case, indexes defined
  on a new, empty database (the `IndexBuilder` Javadoc's example,
  `PayDemo`'s `/payments/`, 38 tests). `Job.join()` existed in 2013 too,
  so `start().join()` did the same on empty directories. Frans, 19:43,
  to "Do you decide (a), drop createFast() in favour of start().join()?":
  "Yes." The tests that call it switch to `start().join()`; to be added
  to 020-08 as a step, with `put(Object)`'s removal.

### 5.2. What the storage decisions fix for it

* **One integer type** (4.7): a conversion decides by the value, as (A),
  (C) and (D) do; (B), exact by the stored type, is not possible, since
  the bytes do not say whether the writer had an `int` or a `long`.
  Question 1's table loses the `i` and `l` split (020-05, section 4).
* **No stored null** (4.1): question 1's two null rows become "absent:
  the constructor's value"; (D)'s report lists an absent field only
  where the constructor gives it a non-null value (020-04, section 7).
* **Names of 1 to 255 bytes** (4.4): question 2's list refuses a field
  with a longer name, naming it.
* **The header** (4.5): an `Object.class` get and a scan tell an object
  from a `String` by its first byte (question 5); a `byte[]` stays a
  guess unless 020-01's decision 6 makes a rule.
* **The types**: question 2's Java types map to Binson's seven:
  `boolean`; `byte`, `short`, `char`, `int` and `long` to the integer;
  `float` and `double` to the double; `String`; `byte[]`; arrays;
  classes (020-05, section 4).
* **The top level**: an array is wrapped in a field `array`, a primitive
  in a field `p`, as today (020-05, sections 5.4 and 12b.1): a rule of
  the API that the format keeps.


## 6. Are the studies enough to decide object storage?

Yes, as Frans thinks (15:22): each decision of section 4 has its options
worked out and its evidence. The null question in 020-03 and 020-04; the
format in 020-05 (sizes, reads, languages, governance, cost, and (f) in
detail with programs that check every rule and every conversion); the
lookup in 020-06 (both ways, two languages, every cache state); the
string rule in 021-04 to 021-06; the reader's safety in 021-07 and
021-08. Nothing missing blocks a decision. What is missing, and when it
can come:

1. **Old databases under (f)** (4.11): 020-04 planned them for version 1
   only. A choice between options, not a study; before the
   implementation.
2. **The cost of (f)'s writer and full check**: reasoned from the code,
   not timed (020-05, sections 12b.5, 12b.6 and 14). Can follow, with
   the implementation: against today's writer (670 to 2,523 ns, 020-05,
   section 6.2) and a strict Binson parse (322 to 886 ns).
3. **A read path end to end**: no BergDB get, index update or build with
   an (f) reader was measured (020-05, section 14; 020-06, section 15),
   and whether (f)'s `DbObject` copies its bytes decides whether its
   lookups run warm or cold (4.3). Can follow; it does not change the
   order of magnitude, a lookup of tens of nanoseconds against today's
   340 to 720 ns.
4. **Limits and NaN** (4.8, 4.10): no study chose numbers; choices, with
   today's values as defaults.
5. **x86, nested paths, names apart from the values**: not measured
   (020-06, section 15). They would move the lookups by some nanoseconds
   (x86's 64-byte lines favour the hashes a little; names apart would
   help B's cold probes), and would not change B's cost against a get or
   a commit.
6. **After the decisions, before code**: an implementation plan for (f)
   with 020-04's no-null rules (020-04, section 11: its step A replaced,
   its steps B to D kept, the order of the commits); the spec of (f) and
   its conformance vectors (4.12; 020-05, section 8.2); Frans's approval
   under 018-01's rule. Work, not studies.

What is not storage stays open: section 5.


## 7. Log

2026-11-07. Created by coord-1107 at Frans's decision of shape 1 (09:52),
with question 1 for Frans to read (10:03: "Where can I read about it
later?").

2026-11-07. Question 1b (section 2b), whether BergDB stores null, added
at Frans's request (12:15) by coord-1107's agent n02, with its study in
020-03; recommended (d), null as absence with an exact round trip.

2026-11-07. Option (D) of question 1 (section 2.5), storage and
conversion apart with a report, written by coord-1107 from Frans's
thinking (12:31) and the chat's sketch, at Frans's request (14:26: "Write
it down. It sounds pretty good. No decision yet.").

2026-11-07. Question 1b: Frans leans to no null values (14:31), not yet
decided; the design and the change plan, without code, go to 020-04.

2026-11-07. 020-04 written (agent p04): the rules, the format, the change
plan, the tests and the Javadoc for (d), with six questions for Frans
(020-04, section 8). Section 2b corrected where 020-04, section 10, found
that BG3's silent 0 is any `String`'s, not only a null's.

2026-11-08. Object storage made ready for decisions, at Frans's request
(15:22), by coord-1108's agent d02, from 020-03 to 020-06 checked
against their sources: section 4, the decisions one at a time (4.1 to
4.12), with Frans's leans (no null; (f); binary search, no hash list);
section 5, the API and the conversion, not yet for decision; section 6,
whether the studies are enough (yes, nothing missing blocks). Corrected:
section 2b.5's format version and test count (from 020-04); section 3's
questions 3 and 4 (narrowed by 020-05, (f) recommended since
2026-11-08). Notes in sections 1 and 2.2 on (f)'s one integer type. The
coordinator's numbers for the lookup checked (section 4.3): "about 1 to
2 % of an in-memory get" is up to 4.4 % at 200,000 keys; the hot and warm
rows hold today, and under (f) only if `DbObject` copies or checks its
bytes first (015-47's gets are zero-copy).

2026-11-08, 15:51 to 17:09. Frans decided the twelve storage decisions
of section 4 with the coordinator (coord-1108), one at a time: each
subsection's "Decided" line holds the question and his answer. Changed
from the recommendations: the depth limit, 16 levels of objects and
arrays (4.10, Frans's question); the put rule of 4.1 left for the API.

2026-11-08. Section 5.1b: a pointer to 020-09, the conversion rules
written with what was left open decided under Frans's delegation of
22:17, by coord-1108's agent.
