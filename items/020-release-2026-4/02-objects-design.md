# 020-02 Objects: the design, worked out with Frans

Created 2026-11-07 by Frans Lundberg. Status: open. The design of objects
(DbObject) for release 2026.4, decided by Frans one question at a time,
after 020-01's inventory: each question with its options in full, the
recommendation, and Frans's answer. The code follows when the questions
are answered.


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


## 2. Question 1: a conversion on a get, exact or best effort? (open)

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

020-03, section 5, from a probe of the jar at `c00e621`:

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
   too, which question 1 removes: 020-04, section 10), typed nulls of the wrong type (a null `Integer`
   stored as an object), three index behaviours (019-42); and question
   1's table loses a row.
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
* The format (questions 3 and 4): no null encodings in its version 2;
  `z` stays `getType`'s answer for "no such field".
* `DbObject`, the stored object's view (`get(key, DbObject.class)`),
  has no null values; its `getString` of an absent field returns
  null, Java's way to say absent.
* Tests: about a dozen of `DbObjectTester`'s 72 tests put nulls
  (020-03, section 5.3); they become tests of the new rules, each
  failing on today's code.


## 3. The next questions

From 020-01, sections 4.5 and 5.5, one at a time after question 1:

* **Question 2: the closed list at a put.** Which Java types are stored
  and how (the primitives and their wrappers, `String`, `byte[]`, arrays
  of these, classes and records made of them, with a no-argument
  constructor); what a put of anything else does (refuse, naming the
  field); final fields, a field that hides another's (S2-F9, F19).
* **Question 3: the kind of a value.** Is it stored (a format version 2
  with the kind of a value; 020-01, N4), or told by the key's suffix and
  the `bergo` bytes, as today?
* **Question 4: the format and its spec** (020-01, section 14, decision
  7): under 018-01's rule that Frans approves format changes; a spec for
  other languages, with 021-06 (strings read that are not well-formed
  UTF-8).
* **Question 5: `put(Object)`, the field `key`, and `Object.class`
  gets.**


## 4. Log

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
