# 020-03 Null: a study for question 1b

Created 2026-11-07 by Frans Lundberg. Status: done. The evidence for
020-02's question 1b, whether BergDB stores null: how languages,
serialization formats and databases model null and a missing value, what
BergDB does with null today, and what each option asks of a binding in
another language. The options, the recommendation and Frans's answer are
in 020-02, question 1b (its section 2b).

Frans, 2026-11-07, 12:15: "020-02. I would like to extend this by one
more question: should null be supported? Let's open up for the option of
not supporting storing null values. In general, null is a mistake. A
billion dollar historic mistake. However, many languages support it, so
omitting the possibility of storing null is not obvious. For binson
(binson.org), I chose to not support null values. Please analyse this in
a new XHigh subagent. Either add to 020-02 or a new separate subitem.
Consider how this is done in object storage engines, database (MongoDB,
prevayler, SQLite). In different languages and different serialization
formats (JSON, BSON, xml, Binson)."

How each fact is known: "run" with a label (BG1, SW2, ...) means a
program's output line, in section 7, from the programs in
`/Users/f/fl/bench/006-14/020-null/` (its `readme.txt` says how each
was run); "docs" means a document or source of section 8, read on
2026-11-07.


## 1. In short

* **Two things, often mixed**: a *null value* (the field is there and
  says "no value") and a *missing field* (absent: not written). JSON,
  BSON, CBOR, MessagePack, MongoDB, Firestore, DynamoDB, Python and
  JavaScript have both; their users and libraries then need rules to
  tell them apart, and the rules differ (sections 2 to 4).
* **A missing field cannot be avoided** in a store that keeps objects
  for years: an object written before a field was added lacks it, and
  so may an object written by another language. Every reader in every
  language handles absence already. Null is a second "no value" on top.
* **Those who chose no null** say "no value" by leaving the field out:
  Binson ("the best feature: Binson has no nulls"), TOML ("just leave it
  out"), Protocol Buffers' wire format ("the serialization contains no
  information about not-present values"). Cassandra stores a null as a
  deleted cell. Serializers that map null to absence: Gson by default
  (JL1), kotlinx.serialization with `explicitNulls = false`, Swift's
  Codable encoder (SW4).
* **The billion-dollar mistake** (Hoare, 1965; his talk of 2009) is the
  null reference that every reference type admits, so that every use
  must check. Rust, Swift and Kotlin fixed it by making "no value" an
  explicit, opt-in type (`Option`, `T?`), not by removing it. The
  counterpart in a format: a stored string is always a string, and "no
  value" is the one explicit state a reader must handle anyway, absence.
* **BergDB today** stores a typed null for `s`, `b`, `a` and `o`, and
  reads a null and a missing field differently; a null meets three
  different index behaviours, and a null `String` read into an `int` or
  `Integer` field gives 0 silently (BG3, found here; any `String` does,
  null or not: 020-04, section 10). At the top level
  BergDB has no null already: `put(key, null)` is refused, and a key
  with no value reads as null (BG5).
* **The trade-off**: keeping null keeps exact Java round trips with no
  rule, JSON documents with null as they are, and a third state
  ("asked, no value" against "not written"). Dropping it halves the
  "no value" cases in every rule, binding and test, and removes a class
  of faults (a null into a primitive, typed nulls, null in an index).
  020-02, question 1b, weighs the options and recommends (d): no null in
  the format, Java's null stored as absence, and a put refused where a
  null would not read back.


## 2. Languages

What a language has for "no value", what a typical JSON library of the
language does with a null and with a missing field read into a typed
field (or a dictionary), and how it is known.

| Language   | Its "no value"         | A null read             | A missing field read   | Known |
|---|---|---|---|---|
| Java       | `null`: references     | `null`; `int` unchanged | constructor's value    | run   |
| C#         | `null`; `int?`         | `null`; opt-in: throws  | constructor's value    | docs  |
| Kotlin     | `T?` only, checked     | `T`: throws             | the default, or throws | docs  |
| Swift      | `T?` only              | `T`: throws             | `nil`, or throws       | run   |
| Rust       | `Option<T>`; no null   | `T`: error              | `None`, or error       | docs  |
| Go         | `nil` pointers; zeros  | value type: no effect   | unchanged (zero)       | run   |
| Python     | `None`, anywhere       | `None`                  | no key                 | run   |
| JavaScript | `null`, `undefined`    | `null`                  | `undefined`            | run   |
| C          | `NULL` pointers only   | by hand                 | zero; a flag           | run   |
| Lua        | `nil`, also absence    | `nil`                   | `nil`                  | docs  |

Notes:

* **Java**: every reference may be null, a primitive cannot: unboxing a
  null `Integer` throws (J1); `new String[2]` holds nulls, `new int[2]`
  zeros (J4). `Optional` "is primarily intended for use as a method
  return type" ([Java Optional], API Note), and is not `Serializable`
  (J3): not a field type. Gson leaves null fields out when it writes
  (JL1, `serializeNulls()` keeps them), reads a missing field as the
  constructor's value (JL2), a null into a reference as null, and a
  null into an `int` leaves it (JL2); so its round trip of a null over
  a non-null initializer gives the initializer (JL3). Java serialization
  gives a field added since the write the type's default, 0 or null,
  not the initializer (JO1).
* **C#**: references are nullable at run time; `string?` is an
  annotation: "The runtime behavior of your program is unchanged.
  Nullable reference types are entirely a compile-time feature"
  ([C# NRT]). Value types need `Nullable<T>` (`int?`).
  System.Text.Json: "a missing property ... The serializer doesn't set
  the property, leaving it at its default value from the constructor";
  an explicit null into a non-nullable property throws only with the
  opt-in `RespectNullableAnnotations` of .NET 9, and ".NET doesn't have
  an `undefined` concept, so both cases deserialize to `null`" ([STJ
  nullable]). Not run.
* **Kotlin**: "a regular variable of type `String` cannot hold `null`";
  `String?` can ([Kotlin null safety]). kotlinx.serialization: "an
  object can be deserialized only when all its properties are present
  in the input", unless a property has a default value, which a
  missing one takes ([kotlinx options]); with `explicitNulls =
  false` null properties are left out when written, and "encoding and
  decoding can become asymmetrical ... the `version` property is `null`
  before encoding, but it decodes to `1.2.2`"; `coerceInputValues` reads
  a null for a non-nullable property as missing ([kotlinx JSON
  config]). Not run.
* **Swift**: an `Int` cannot be nil (SW1). The synthesized `Codable`:
  a null into a `String` throws `valueNotFound`, a missing `String`
  throws `keyNotFound` even when the property has a default value, and
  a missing `Int?` reads as `nil`, not its default 42 (SW2, SW3); the
  encoder leaves a nil property out (SW4) and writes `null` in an array
  (SW5).
* **Rust**: "there are no "null" references" ([Rust Option]); serde's
  derive: "If the missing field is of type `Option<T>` then treat is as
  `None`, otherwise it is an error" ([serde de.rs]); `#[serde(default)]`
  gives a default ([serde default]). Not run (no rustc).
* **Go**: value types have zero values, not null (GO1).
  `encoding/json`: null "into any other Go type has no effect on the
  value and produces no error" ([Go json]): a struct cannot tell null
  from missing (GO2, GO3), a map can (GO5); `[1, null, 3]` into `[]int`
  is `[1 0 3]` (GO6). `omitempty` and `omitzero` leave fields out (GO4).
* **Python**: `None` anywhere; `d.get("x")` is `None` for a null and
  for a missing key, `"x" in d` tells them apart (PY1); a dataclass does
  not check its hints (PY3).
* **JavaScript**: two "no values": a missing property reads as
  `undefined`, a JSON null as `null` (JS2); `JSON.stringify` drops
  `undefined` members and writes `null` for them in arrays (JS3);
  default parameters and destructuring defaults apply to `undefined`
  only, not `null` (JS4, JS5). TypeScript: with `strictNullChecks`,
  "`null` and `undefined` have their own distinct types";
  `exactOptionalPropertyTypes` separates an absent optional property
  from one set to `undefined` ([TS config]).
* **C**: `NULL` is a pointer; an `int` has no null: a flag (`has_x`)
  or a sentinel by hand; members a designated initializer does not name
  are zero (C1, C2).
* **Lua**: "Any key associated to the value nil is not considered part
  of the table" ([Lua], section 2.1): null and absence are one.

So the languages fall in three groups. Null in every reference (Java,
C#, JavaScript, Python, Lua, C pointers); an opt-in optional type checked
by the compiler (Rust, Swift, Kotlin, and C# for value types); and zero
values with no null for values (Go, C). In all three, the JSON libraries
have a rule for a missing field: the constructor's or declared default
(Java, C#, Kotlin, Go), `None` or `nil` for an optional (Rust, Swift), an
absent key (Python, JavaScript), or an error where the field's type has
neither a default nor an optional (Kotlin, Swift, Rust).


## 3. Serialization formats

| Format          | Null                                  | Absent field             | Known     |
|---|---|---|---|
| JSON            | `null`                                | yes                      | docs, run |
| BSON 1.1        | null 0x0A; undefined 0x06, deprecated | yes                      | docs, run |
| XML Schema      | `xsi:nil="true"`, where `nillable`    | `minOccurs="0"`          | docs      |
| CBOR            | null (22, f6); undefined (23, f7)     | yes                      | docs, run |
| MessagePack     | nil (0xc0)                            | yes                      | docs, run |
| Avro 1.12       | a `null` type; `["null", T]` unions   | no: the reader's default | docs      |
| Amazon Ion      | typed (`null.int`, ...) and `null`    | yes                      | docs      |
| Protobuf proto3 | none on the wire                      | yes: the only way        | docs, run |
| Binson 1.1      | none                                  | yes: the only way        | docs, run |
| TOML 1.0        | none                                  | yes: the only way        | docs      |

Notes:

* **JSON** ([RFC 8259], section 3): `null` is one of three literal
  names; the RFC gives it no meaning beyond that, and says nothing of
  null against a missing member. JSON Merge Patch gives null one:
  "Null values in the merge patch are given special meaning to indicate
  the removal of existing values in the target", so it suits documents
  that "do not make use of explicit null values" ([RFC 7396], section
  1).
* **BSON** ([BSON spec] 1.1): element type 0x0A "Null value", and 0x06
  "Undefined (value). Deprecated". pymongo reads 0x06 as `None` (PL3),
  js-bson as `undefined` (JSL1); js-bson 7.3.4 leaves an `undefined`
  member out when it writes (JSL1).
* **XML Schema** ([XSD 1], sections 2.6.2, 3.3.1): "An element may be
  valid without content if it has the attribute xsi:nil with the value
  true", allowed only where the declaration is `nillable`; an element
  with `minOccurs="0"` may be absent; an empty `<x/>` is the empty
  string for a string type. Three states, each opt-in by the schema.
* **CBOR** ([RFC 8949]): simple values 22 null and 23 undefined
  (section 3.3); generic decoders are expected to represent "false",
  "true", and "null" ("undefined" is intentionally omitted)" (section
  2.1); undefined "might be used by an encoder as a substitute for a
  data item with an encoding problem" (section 5.7). cbor2 and cbor-x
  write f6 and f7 (PL1, JSL2).
* **MessagePack** ([MessagePack spec]): one nil, 0xc0 (PL2).
  @msgpack/msgpack writes JavaScript's `undefined` as nil, which reads
  back as `null` (JSL3).
* **Avro** ([Avro spec], "Primitive Types", "Unions", "Schema
  Resolution"): `null` is a type of its own, "no value"; a field that
  may hold none is a union such as `["null", "string"]`, opt-in per
  field. Every record holds every field of its writer's schema; a field
  the reader has and the writer lacks takes "the default value from its
  field", else "an error is signalled".
* **Amazon Ion** ([Ion spec], "Null Values"): "Ion supports distinct
  null values for every core type, as well as a separate null type ...
  primarily for compatibility with JSON". BergDB's `s`, `b`, `a` and `o`
  nulls are typed nulls of this kind.
* **Protocol Buffers** ([PB presence], [ProtoJSON]): "the wire format
  represents a sequence of present values ... the serialization contains
  no information about not-present values". proto3 dropped presence for
  plain scalars: 0 and "" are not written and cannot be told from unset
  (PL4); presence came back as `optional` in release 3.15, and messages
  and the wrapper types have it (PL4). None of it is a null: `a = None`
  is a `TypeError` (PL4). In its JSON form a null "should remain unset,
  as though it was not present in the input at all" (PL5), and "`null`
  values are not allowed within repeated fields" (PL6 for the API).
* **Binson** ([Binson], BINSON-SPEC-1.1, published October 2026): seven
  types, "five primitive types (boolean, integer, double, string,
  bytes) and two composite types (array, object)", and "the best
  feature: Binson has no nulls :-)". The spec gives no reason; its
  answer to "no value" is the absent field: BINSON-SCHEMA marks a field
  `"optional": true`, with the example doc "time zone name, if not set
  UTC is used" ([Binson Schema]). binson-java (release 3.5) refuses a
  null at a put and in an array (`IllegalArgumentException`, BN1), throws
  `BinsonFormatException` for a missing field and offers `hasString`
  (BN2), and refuses a JSON text with null ("not a Binson value", BN3);
  its `JsonNull` is documented as "the ugly null value of JSON". The
  types are DbObject's eight with one integer and no null (section 5.3).
* **TOML** ([TOML 1.0]): no null. Asked for one in 2013 (issue #30),
  its author answered: "I'm not convinced of the usefulness of nil. TOML
  is intended for configuration, at which point [the commenter] is
  right: just leave it out"; in 2023 a maintainer: "we're not revisiting
  this design choice" ([TOML #30]).

Who chose no null, and how its users say "no value": Binson, TOML and
the protobuf wire format, all by leaving the field out; proto3 at first
also had no presence for scalars (a 0 meant unset) and had to add
`optional` back: presence was needed, null was not. Bencode, the
BitTorrent format, has no null either: strings, integers, lists and
dictionaries ([BEP 3], "bencoding"). The formats with null keep it
mostly for JSON (Ion says so); CBOR's and BSON's second "no value"
(undefined) is deprecated or left out of the generic model.


## 4. Databases and object stores

| Database    | Null and absence               | A query or index on "no value"      | Known     |
|---|---|---|---|
| SQL, SQLite | NULL; no absent column         | `= NULL` matches nothing; `IS NULL` | run       |
| MongoDB     | null, and missing fields       | `{x: null}` matches both            | docs      |
| Firestore   | null, and missing fields       | `!=`, `orderBy` skip missing fields | docs      |
| DynamoDB    | `NULL`, and missing attributes | an index skips an absent key        | docs      |
| Cassandra   | a null is a deleted cell       | null and never-set read alike       | docs      |
| Realm       | `T?`; no absent property       | the value null                      | docs      |
| Prevayler   | Java's null, in memory         | the application's code              | docs, run |

Notes:

* **SQL** (SQLite 3.54.0): three-valued logic: `NULL = NULL` and
  `NULL <> 1` are NULL, `NULL OR 1` is 1 (SQ1); `WHERE x <> 1` skips the
  NULL rows, and `NOT IN` a list with a NULL matches nothing (SQ3);
  `count(x)` and `sum(x)` skip NULLs (SQ4); NULLs sort first (SQ5), are
  one value to `DISTINCT` (SQ6) and many to `UNIQUE` (SQ2); a partial
  index `WHERE s IS NOT NULL` serves `s = 'a'` (SQ7). In JSON,
  `json_extract` gives NULL for a null and for a missing member alike,
  `json_type` tells them apart (SQ8). A column `DEFAULT 42` applies only
  when the column is absent from the `INSERT`; a NULL given is stored
  as NULL (SQ10): SQL's own "absent against null". SQLite's notes: "It
  seems that NULLs should be either distinct everywhere or nowhere. And
  the SQL standards documents suggest that NULLs should be distinct
  everywhere. Yet ... no SQL engine tested treats NULLs as distinct in a
  SELECT DISTINCT statement or in a UNION" ([SQLite nulls]).
* **MongoDB** ([Mongo null]): "The `{ item : null }` query matches
  documents that contain the `item` field with a `null` value **or** do
  not contain the `item` field"; `{ $type: 10 }` matches only the null,
  `{ $exists: false }` only the missing. Indexes ([Mongo sparse],
  [Mongo unique]): "non-sparse indexes contain all documents ...
  storing null values for those documents that do not contain the
  indexed field"; a unique index "can only contain one document that
  contains a `null` value in its index entry", a missing field
  included; a sparse index has "entries for documents that have the
  indexed field, even if the index field contains a null value". So
  MongoDB merges the two in equality and in a plain index, and splits
  them in `$type`, `$exists` and sparse indexes.
* **Firestore** ([Firestore queries], [Firestore order]): "A field
  exists when it's set to any value, including ... `null`"; "Not-equal
  (`!=`) and `not-in` queries exclude documents where the given field
  does not exist", and "`null` field values do not match `!=` clauses";
  "An orderBy() clause also filters for existence of the given field".
* **DynamoDB** ([DynamoDB types], [DynamoDB sparse]): "Null represents
  an attribute with an unknown or undefined state"; key attributes must
  be string, number or binary; "DynamoDB writes a corresponding index
  entry only if the index key attributes are present in the item", and
  the guide's pattern for a flag is to add an attribute and later delete
  it.
* **Cassandra** ([Cassandra JSON], "INSERT JSON"): "a column omitted
  from the JSON map will be set to NULL, meaning that any pre-existing
  value for that column will be removed (resulting in a tombstone being
  created)"; "DEFAULT UNSET" leaves it. A null is a delete; third-party
  guides add that a read shows a null and a never-written cell alike
  (not checked here).
* **Realm** ([Realm Kotlin types]; the Atlas Device SDKs "are
  deprecated"): an object database with a schema: a property is
  required or optional ("declare properties optional (nullable) using
  the built-in `?` Kotlin operator"); every object has every property,
  so there is no absent field, and null is the only "no value".
* **Prevayler** ([Prevayler]): "business objects are kept live in memory
  and transactions are journaled for system recovery", for "plain old
  Java objects" that "implement Serializable". Null is Java's. If its
  snapshots are Java serialization, as "implement Serializable" and its
  "freshly deserialized copy" suggest (the page names no format), a
  field added to a class since a snapshot reads as 0 or null, not as its
  initializer (JO1).

So the document stores keep both null and absence, and each draws the
line between them in its own place (MongoDB's equality merges them,
Firestore's does not); SQL has no absent column in a row but separates
"not given" from NULL at an `INSERT` (DEFAULT). Indexes over a field
without a value are sparse by choice (MongoDB), by design (DynamoDB,
BergDB today), or hold the NULLs (SQL, a plain MongoDB index).


## 5. BergDB today

From the code at `b7fc20a` and the probe `NullProbe` (BG1 to BG6), run
on the jar of that commit.

### 5.1. What is stored

* A null field of a reference type is stored as a null of a type: a
  `String` as `s` with length −1, a `byte[]` as `b` with length −1, an
  array as `a` with the byte `Z`, an object as `o` with field count −1
  (`DbString`, `DbByteArray`, `DbArray.Builder.buildNull`,
  `DbObject.Builder.buildNull`; BG1). A null wrapper (`Integer`,
  `Double`, ...) is stored as a null `o`, an object, not a number
  (`DbValue.toNullDbValue`; BG1).
* A null array element is stored the same way, typed: `s` null in a
  `String[]`, `o` null in an `Integer[]` or an `Object[]` (BG4).
* A null at the top is refused: `put(key, null)` throws
  `IllegalArgumentException` ("object == null not allowed", BG5;
  `Connection.put`'s Javadoc). A key without a value reads as null and
  `exists` is false (BG5). `DbObject.toDbObject(null)` builds a null
  object (field count −1), which a put of a class never reaches.
* A missing field is stored as nothing: the object has no such field.
  `DbObject.getType` answers `z` for it ("think 'zero', nothing");
  `getString` answers null for a missing and for a null field alike,
  `has` and `getType` tell them apart (BG1).

### 5.2. What a get does

* Into the class that was put: null reads back as null (BG4, and
  `DbObjectTester`'s null tests).
* A missing field keeps the value the constructor gave it; a null field
  is set to null over it (BG2): `New { String name = "dflt"; Integer
  count = 42; }` reads a stored object without the fields as "dflt" and
  42, and one with null fields as null and null.
* A null into a primitive: a null `Integer` (an `o` null) into an `int`
  throws `Bug` (S2-F6; BG3); a null `String` (an `s` null) into an `int`
  or an `Integer` field reads as 0, silently (BG3: `DbValue.toJavaObject`
  calls `toInt()`, which is 0 for a string; for any string, not only a
  null one: 020-04, section 10). An `Integer[]` with a null
  read into an `int[]` throws a bare `IllegalArgumentException` from
  `Array.set` (BG4). An `Object[]` of `{null, "x"}` reads back as
  `[null, null]` (S2-F7; BG4).

### 5.3. Indexes, the format and the history

* Indexes (`FieldIndexFunction.createIndexEntry`): an entry needs every
  indexed field present with an accepted type. A missing field gives no
  entry; a null `Integer` (an `o`) gives no entry in a `long` index; a
  null nested object gives no entry for `inner.name` (BG6, two entries
  of three each). A null `String` in a `string` index makes the put
  throw `IllegalArgumentException` ("A null String cannot be indexed",
  BG6), and a build over one ends as failed (019-42, which made the
  assertion a check); `eq(null)` is refused (BG6). Three behaviours for
  one "no value". 019-42's option (a), a null `String` giving no entry
  as a missing field does, was left for 2026.4; its option (b) was
  done.
* The format: `DbObject`'s Javadoc: "z - zero  Not a type, character
  'z' is reserved for null-capability". In `DbArray`'s bytes `z` ends an
  array and `Z` is a null array, so `z` cannot be an element's type. The
  null encodings are three: length −1 (`s`, `b`), `Z` (`a`), field count
  −1 (`o`); a null object is `626572676f01ffff` (BG5).
* The history: Frans's design note of 2013-05-22 ([F1-007],
  `2013/2013-05-db-object.txt`) lists the types "boolean, int, long,
  double, string, byteArray, object, array", with no null, under
  "Simple! As few types as possible to reduce komplexity"; it also asks
  for "Conversion JSON -> DbObject". The nulls of `s`, `b`, `a` and `o`
  follow Java's null references. Binson (2014 to 2026), Frans's later
  format, has the same field model (named, typed fields sorted by the
  bytes of their names) with one integer type and no null.
* Tests: about a dozen of `DbObjectTester`'s 72 tests put nulls
  (`testNullField0` and 1, `testStrings2`, `testStringArray0`,
  `testArray1`, `testStrings2D`, the 4-D and 5-D array tests and the
  null cases of the object tests); none covers a null into a primitive
  or another type, or null in an index but 019-42's. (020-04, section
  10, counted them at `b4cf896`: 19 of the 72 set a null and 4 more hold
  nulls by default; note of 2026-11-08.)


## 6. The options across languages

### 6.1. A null in a format, and Hoare's mistake

InfoQ's summary of the talk: "Tony Hoare introduced Null references in
ALGOL W back in 1965 "simply because it was so easy to implement", says
Mr. Hoare. He talks about that decision considering it "my
billion-dollar mistake""; and its show notes, at 27:40: "the null value
is a member of every type, and a null check is required on every use of
that reference variable, and it may be perhaps a billion dollar
mistake" ([Hoare]). The fault is that every reference may be null, so
every use must check or fail. The languages that fixed it (Rust, Swift,
Kotlin, C# in part) kept "no value" and made it explicit: a `String` is
a string, a `String?` may be none, and the compiler makes the code
handle the second.

In a store whose objects outlive their classes, absence is always
possible: any field of any stored object may be missing (an older
class, another language). A reader must handle that for every field,
in every language. A stored null adds a second "no value" to every
`s`, `b`, `a` and `o` field: a reader of a present string must still
check it for null. Without null, a present field always holds a value
of its type, and absence is the one explicit "no value": the format's
counterpart of `T?`.

### 6.2. What a binding does under each option

The options are those of 020-02, question 1b: (a) keep null; (b) refuse
null; (c) null is absence, a null field left out; (d) as (c), and a put
refused where a null would not read back.

| Binding    | (a) null kept             | (b) null refused | (c), (d) null is absence     |
|---|---|---|---|
| Java, C#   | `null` both ways          | every field set  | `null` left out              |
| Kotlin     | `T?` for every s, b, a, o | `T` fields only  | `T?` or a default            |
| Swift      | `T?` likewise             | `T` fields only  | `T?` (absent: `nil`)         |
| Rust       | `Option<T>` likewise      | `T` fields only  | `Option<T>` or a default     |
| Go         | `*T`; or no effect        | value types only | absent: zero value           |
| Python     | `None`; but which type?   | `None` refused   | `None` key left out          |
| JavaScript | `null`; `undefined`?      | `null` refused   | `null`, `undefined` left out |
| C          | `NULL`; number flags      | no flags         | a flag per optional field    |

* Under (a) a binding in a language whose plain types have no null
  (Rust, Swift, Kotlin's non-null types, Go's value types, C's numbers)
  must give every `s`, `b`, `a` and `o` field an optional type, since
  any stored one may be null, or refuse the object; and it must handle
  absence besides. A binding in a language
  with one untyped null (Python, JavaScript, Go's `nil` interface) must
  choose a type for the null it writes: Java writes a null `Integer` as
  an `o`, so even Java's choice is arbitrary (5.1). JavaScript has two
  nulls to map to BergDB's four.
* Under (b) every binding refuses a null at a put. A language whose
  objects are maps (Python, JavaScript) says "no value" by leaving the
  key out, as Binson's API does. A class (Java, C#, Kotlin, Swift) has
  every field always: it cannot leave one out, so it cannot say "no
  value" at all, only a sentinel ("" or −1) or a flag; proto3 found that
  presence was needed (section 3).
* Under (c) and (d) the binding maps its language's "no value" to
  absence: Java's, C#'s and Kotlin's `null`, Python's `None`,
  JavaScript's `null` and `undefined`, Swift's `nil`, Rust's `None`, a
  nil Go pointer; and absence back to the language's own default for a
  missing field, as its JSON libraries do (section 2). A present value
  is never null in any language. (d) adds, for languages whose classes
  give fields initial values (Java, C#, Kotlin), a check at the put
  that a null field has no non-null initial value.
* A JSON document with null converts under (a) as it is; under (c) and
  (d) a null member becomes absent and a null array element is refused,
  as in protobuf's JSON form; under (b) it is refused, as by
  binson-java (BN3).


## 7. The programs and their results

On F53 (macOS 27, arm64), 2026-11-07; the outputs in full are the
`out.txt` files in `/Users/f/fl/bench/006-14/020-null/`, by directory.

BergDB, the jar of `b7fc20a` (`bergdb/NullProbe.java`):

* BG1. A class with null `String s`, `byte[] b`, `String[] a`, `Inner
  o`, `Integer w`: stored types `s`, `b`, `a`, `o`, `o`, each null; a
  missing field: type `z`, no value; `getString` null for both; `has`
  true for the null, false for the missing.
* BG2. Into `New { name = "dflt"; count = 42; int n = 7 }`: missing
  fields give dflt, 42, 7; null fields give null, null.
* BG3. A null `String` into `int name`: 0; into `Integer name`: 0; a
  null `Integer` into `Integer count`: null; into `int count = 5`:
  `Bug` (an `IllegalArgumentException` of `Field.set`).
* BG4. Stored elements: `String[] {"a", null}`: `s`, `s` null;
  `Integer[] {1, null}`: `i`, `o` null; `Object[] {null, "x"}`: `o`
  null, `s`. Read back: `[a, null]`, `[1, null]`, `[null, null]`.
  `Integer[] {1, null}` into `int[]`: `IllegalArgumentException: null`.
* BG5. `put(key, null)`: `IllegalArgumentException: object == null not
  allowed`; a missing key reads as null, `exists` false; the null
  object's bytes `626572676f01ffff`, an empty object's
  `626572676f010000`.
* BG6. A `long` index over `Integer v` with one null of three: 2
  entries; a `string` index over `inner.name` with one null `inner`: 2
  entries; a `string` index over `name`, a put with a null name:
  `IllegalArgumentException: A null String cannot be indexed.`, the
  database goes on; `eq(null)`: `IllegalArgumentException`.

Java 27 and Gson 2.15.0 (`java/`):

* J1. `int x = (Integer) null`: `NullPointerException`. J2.
  `Optional.of(null)`: `NullPointerException`; `ofNullable(null)`:
  empty. J3. `Optional` is not `Serializable`. J4. `new String[2]`:
  `[null, null]`; `new int[2]`: `[0, 0]`.
* JL1. `Rec { name = "dflt"; count = 42; n = 7 }` with name and count
  null, to JSON: `{"n":7}`; with `serializeNulls()`:
  `{"name":null,"count":null,"n":7}`.
* JL2. `{}` reads as dflt, 42, 7; `{name, count, n: null}` as null,
  null, 7 (the `int` unchanged).
* JL3. The round trip of JL1's object reads dflt and 42.
* JL4. A record `R(String name, int n)` from `{"name": null}`:
  `R[name=null, n=0]`.
* JO1. Java serialization: an object of a class with `name` only, read
  by a class that added `int count = 42` and `String note = "dflt"`:
  count 0, note null.

Python 3.14.7 and its libraries (`python/`):

* PY1. `{}` and `{"x": null}`: `.get("x")` None and None; `"x" in d`
  False and True. PY2. `{"x": None}` to JSON: `{"x": null}`. PY3. A
  dataclass takes `name=None` for a `str` field. PY4. `None + 1`:
  `TypeError`.
* PL1. cbor2: None is `f6`, undefined `f7`. PL2. msgpack: None is
  `c0`. PL3. bson: `{"x": None}` is element type 0x0a; a 0x06 element
  reads as None.
* PL4. protobuf 7.36.2, a proto3 message built at run time: an empty
  message is 0 bytes; `a = None`: `TypeError`; `HasField("a")` on a
  field without presence: `ValueError`; an `optional` field set to 0
  is written (`1000`), a plain one is not; a wrapper and a message
  field are unset when new.
* PL5. ProtoJSON `{"a": null, "s": null, "w": null, "b": null}`: 0, "",
  and the wrapper and the optional unset; `Int32Value(0)` is written as
  `{"w": 0}`; an empty message is `{}`.
* PL6. `append(None)` to a repeated `int32`: `TypeError`.

Node 26.9.0 and its libraries (`js/`):

* JS1. `typeof null` is "object"; `null == undefined` but not `===`.
  JS2. `{}`: `.x` undefined; `{"x": null}`: null; `in` false and true.
* JS3. `JSON.stringify({a: undefined, b: null})`: `{"b":null}`;
  `[undefined, null]`: `[null,null]`. JS4. A default parameter applies
  to `undefined`, not to `null`. JS5. So does a destructuring default;
  `Number(null)` is 0. JS6. A property set to `undefined` is in the
  object until deleted.
* JSL1. js-bson 7.3.4: `{x: null}` written with 0x0a; `{x: undefined}`
  written as an empty document; a 0x06 element reads as `undefined`.
* JSL2. cbor-x 1.6.9: `null` is `f6`, `undefined` `f7`, kept in a map.
* JSL3. @msgpack/msgpack 3.1.3: `null` and `undefined` both `c0`;
  `undefined` reads back as `null`.

Go 1.27.0 (`go/`), Swift 6.4 (`swift/`), C (`c/`), SQLite 3.54.0
(`sqlite/`), binson-java (`binson/`):

* GO1. The zero value of `{Name string; Count int}`: "" and 0. GO2.
  `{}` and `{name: null, count: null}` into a struct preset to dflt and
  42: unchanged both times. GO3. Into pointers, null and missing both
  give nil; nil pointers are written as `null`. GO4. `omitempty` and
  `omitzero` leave fields out; a nil slice is `null`, an empty one
  `[]`. GO5. A map tells null from missing by `ok`. GO6. `[1, null, 3]`
  into `[]int`: `[1 0 3]`.
* SW1. An `Int?` may be nil; an `Int` cannot. SW2. `Rec { name: String
  = "dflt"; count: Int? = 42 }`: `{}` throws `keyNotFound` for name;
  `{"name": "a"}` gives count nil, not 42; `{"name": null}` throws
  `valueNotFound`. SW3. A struct without defaults: `keyNotFound`. SW4.
  A nil property is left out when written. SW5. `[1, nil]` is
  `[1,null]`.
* C1. `{ .name = "a" }`: count and has_count 0. C2. `{ 0 }`: name is
  `NULL`.
* SQ1 to SQ11: as in section 4's notes (SQ11: a NULL into a `NOT NULL`
  column is refused).
* BN1. `put("s", (String) null)`, `put("b", (byte[]) null)` and an
  array's `add(null)`: `IllegalArgumentException`. BN2. `getString` of
  a missing field: `BinsonFormatException`; `hasString`: false; a field
  of another type: the same exception. BN3. `fromJson` of `{"x": null}`
  and of `{"x": [1, null]}`: `IllegalArgumentException: not a Binson
  value`.

Not run (no toolchain on F53): Rust, Kotlin, C#, MongoDB, Avro, Ion,
Cassandra, DynamoDB, Firestore, Realm, Prevayler (JO1 shows Java
serialization, the format its page implies).


## 8. Sources

Read on 2026-11-07; copies of most are in
`/Users/f/fl/bench/006-14/020-null/sources/`.

* [Hoare]: InfoQ, "Null References: The Billion Dollar Mistake", Tony
  Hoare, QCon London 2009, on InfoQ 2009-08-25, the summary and the
  show notes,
  https://www.infoq.com/presentations/Null-References-The-Billion-Dollar-Mistake-Tony-Hoare/
* [Binson]: https://binson.org/, BINSON-SPEC-1.1 (sections 1 to 5),
  page version 2026-10-07; [Binson Schema]:
  https://binson.org/binson-schema.html; binson-java, master,
  release 3.5: https://github.com/franslundberg/binson-java
  (`Binson.java` `put`, `putElement`; `lowlevel/ValueType.fromObject`;
  `lowlevel/JsonNull`; `lowlevel/JsonParser.parseValue`).
* [RFC 8259]: JSON, section 3, https://www.rfc-editor.org/rfc/rfc8259
* [RFC 7396]: JSON Merge Patch, sections 1 and 2,
  https://www.rfc-editor.org/rfc/rfc7396
* [RFC 8949]: CBOR, sections 2.1, 3.3, 5.7, 6.1,
  https://www.rfc-editor.org/rfc/rfc8949
* [BSON spec]: https://bsonspec.org/spec.html, version 1.1, element
  types 0x06 and 0x0A.
* [XSD 1]: XML Schema Part 1: Structures, sections 2.6.2 (xsi:nil) and
  3.3.1 ({nillable}), https://www.w3.org/TR/xmlschema-1/
* [MessagePack spec]: https://github.com/msgpack/msgpack/blob/master/spec.md,
  "nil format".
* [Avro spec]: https://avro.apache.org/docs/1.12.0/specification/,
  "Primitive Types", "Unions", "Records", "Schema Resolution".
* [Ion spec]: https://amazon-ion.github.io/ion-docs/docs/spec.html,
  "Null Values".
* [PB presence]: protobuf, `docs/field_presence.md`, "Background" and
  "Presence in tag-value stream (wire format) serialization",
  https://github.com/protocolbuffers/protobuf/blob/main/docs/field_presence.md;
  [ProtoJSON]: https://protobuf.dev/programming-guides/json/, null
  values, wrapper types, presence when printing.
* [BEP 3]: The BitTorrent Protocol Specification, "bencoding",
  https://www.bittorrent.org/beps/bep_0003.html
* [TOML 1.0]: https://toml.io/en/v1.0.0 (no null among its types);
  [TOML #30]: https://github.com/toml-lang/toml/issues/30 (mojombo,
  2013-02-24; pradyunsg, 2023-10-07).
* [Mongo null]: https://www.mongodb.com/docs/manual/tutorial/query-for-null-fields/,
  "Equality Filter", "Type Check", "Existence Check"; [Mongo sparse]:
  https://www.mongodb.com/docs/manual/core/index-sparse/; [Mongo
  unique]: https://www.mongodb.com/docs/manual/core/index-unique/,
  "Missing Document Field in a Unique Single-Field Index".
* [SQLite nulls]: https://www.sqlite.org/nulls.html
* [Firestore queries]: https://firebase.google.com/docs/firestore/query-data/queries
  ("Not equal", "not-in"); [Firestore order]:
  https://firebase.google.com/docs/firestore/query-data/order-limit-data
  ("Limitations").
* [DynamoDB types]:
  https://docs.aws.amazon.com/amazondynamodb/latest/developerguide/HowItWorks.NamingRulesDataTypes.html,
  "Null"; [DynamoDB sparse]:
  https://docs.aws.amazon.com/amazondynamodb/latest/developerguide/bp-indexes-general-sparse-indexes.html
* [Cassandra JSON]:
  https://cassandra.apache.org/doc/latest/cassandra/developing/cql/json.html,
  "INSERT JSON".
* [Realm Kotlin types]:
  https://www.mongodb.com/docs/atlas/device-sdks/sdk/kotlin/realm-database/schemas/supported-types/
* [Prevayler]: https://prevayler.org/
* [Java Optional]:
  https://docs.oracle.com/en/java/javase/25/docs/api/java.base/java/util/Optional.html,
  the API Note.
* [C# NRT]: https://learn.microsoft.com/en-us/dotnet/csharp/nullable-references;
  [STJ nullable]:
  https://learn.microsoft.com/en-us/dotnet/standard/serialization/system-text-json/nullable-annotations,
  "Missing values versus null values".
* [Kotlin null safety]: https://kotlinlang.org/docs/null-safety.html;
  [kotlinx JSON config]:
  https://kotlinlang.org/docs/serialization-json-configuration.html,
  "Encode default values", "Omit explicit nulls", "Coerce input values";
  [kotlinx options]:
  https://kotlinlang.org/docs/serialization-customization-options.html,
  "Set default values for optional properties".
* [Rust Option]: https://doc.rust-lang.org/std/option/index.html;
  [serde de.rs]: serde, `serde/src/private/de.rs`, `missing_field`
  (master, 2026-11-07); [serde default]: https://serde.rs/attr-default.html
* [Go json]: https://pkg.go.dev/encoding/json, `Unmarshal` and
  `Marshal` (go1.27).
* [TS config]: https://www.typescriptlang.org/tsconfig/,
  `strictNullChecks`, `exactOptionalPropertyTypes`.
* [Lua]: Lua 5.4 Reference Manual, section 2.1,
  https://www.lua.org/manual/5.4/manual.html (read through a fetch
  tool's summary; no copy kept).
* [F1-007]: the f1 repo, `a/007-bergdb-261012/bergdb/doc/2013/2013-05-db-object.txt`
  (Frans, 2013-05-22) and `2013-05-notes.txt`.


## 9. Log

2026-11-07. Written by agent n02 of coord-1107 at Frans's request
(12:15), with the programs in `/Users/f/fl/bench/006-14/020-null/`;
the question and its options are in 020-02, question 1b.

2026-11-08. Notes added by coord-1108's agent d02 (020-02, section 4)
from 020-04, section 10: BG3's silent 0 is any `String`'s (sections 1
and 5.2), and the count of tests with a null (section 5.3); a long line
of section 6.2 wrapped. Frans leans to no null (020-02, section 4.1).
