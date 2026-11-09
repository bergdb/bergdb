# 020-24-12 A domain model of Java types as Data Objects

Created 2026-11-09 by Frans Lundberg.

An application written as a new user of 2026.4 would write it (u12, for coord-1109, round 4
of the common brief of 020-24): only the release jar on the class path, built from a clone
of main at `20e8d5a`, and only what a user reads (README.md, `java/src/overview-pub.html`,
the Javadoc of `bergdb.pub`, `releases/next.md`). The implementation was read only
afterwards, to explain U12-1 and U12-2.


## 1. The application

A domain model written the way Java developers write one, stored as Data Objects, with
every type the Javadoc allows and many it does not, read back into the classes, into
`DbObject` and into changed classes. All is in `/Users/f/fl/bench/2026-11-09/app-u12/app/`:
`src/app/Main.java` drives it and checks every result, `Model.java` holds the classes the
Javadoc allows and the grey zone, `Bad.java` the field types it does not, `Check.java` the
field-by-field comparison and a walk of a `DbObject` against the object put, `Fill.java`
random objects; `src/gen/` is made by `../tools/gen.py` (the conversion targets, classes of
500 and of 1,000 to 32,768 fields, an inheritance chain of 101 classes, long field names);
`src/ünïcödé/модель/` is a package with a Unicode name, with the classes `Kund` and `顧客`;
`probe/` holds what a user tries beyond the main flow: `HugeProbe`, `FieldsProbe` and
`BigStringProbe` (objects over 2^31 - 1 bytes), `TextProbe`, `FloatProbe`, `WideProbe`,
`ManySmallProbe` (a million objects or arrays in one array), `LoaderProbe` (two versions of
one class in two class loaders, as a reload makes), `ManyProbe` (16 threads using 300
classes for the first time at once), `OrderProbe` (169 field names above the surrogates and
beyond the BMP), `RwProbe` (refusals inside `rw()` and `w()`), `HideProbe`, `OddGetProbe`,
and `ConvFuzz` (random stored objects, made with the Builders, into classes of every field
type). `run.sh` compiles all and runs the application, then the probes, one JVM at a time;
`run.txt` is the last run's output.

The natural model comes first: an `Order` with an enum status, an `Instant`, a
`List<OrderLine>`, an `Optional<String>` and a `BigDecimal`. Its put is refused, one field
at a time (U12-4), and the BergDB form is a `String` status, a `long` of milliseconds, an
`OrderLine[]`, a nullable `String` and a `Money` of `long` cents and a currency.

What it checks, and exits with 1 on a wrong result:

* Exact round trips. Each object is put, then read back as its class and compared field by
  field (floats and doubles by their bits, every NaN one value, -0.0 kept); as a `DbObject`,
  whose bytes equal `toDbObject()`'s and a get as `byte[]`, walked field by field: each
  field's type char and value, through nested arrays and objects; as `Object.class` (a
  `DbObject`); by `toJavaObject()`; and again after a restart with a cache of 8 MB (757
  objects). The objects: the eight primitives and their wrappers at their extremes (MIN,
  MAX, -1, -0.0, NaN with a payload, subnormals, 2^53 + 1, lone surrogates in `char`,
  `Character`, `char[]` and `Character[]`); every array of the closed list of one to three
  dimensions, jagged and empty; a `Customer` with orders, lines and nested `Money`; 50
  fields named as reserved words of other languages (`select`, `def`, `self`, `None`,
  `nil`, `__proto__`, `constructor`, `$ref`, and BergDB's `p` and `array`); Unicode field
  names (`名前`, `größe`, `π`, `µ` and `μ`, `é` precomposed and decomposed, `ǅ`, `𝔘𝔫`); a
  `Kund` read by the class `顧客`; a chain of 101 classes by inheritance, read also as its
  top superclass; 500 fields of 13 types; 32,767 int fields; an abstract superclass; a
  class nested in an interface; volatile, static and private transient fields; two
  references to one array and to one object; null fields with initial values; linked
  lists of 15 and 16 nodes; 700 random objects of 7 classes.
* The grey zone and the types not on the list, each by a put and a get, with the field
  null and with a value: the exception, its message, nothing written, and the database
  going on (124 refusals). Private, protected and package-private fields; a JavaBean; a
  superclass with a private field; a public field of a package-private superclass; inner,
  local and anonymous classes (double-brace initialization); no, or a private, no-argument
  constructor; a package-private class; a constructor that throws; `Box<T>`, a subclass of
  `Box<String>`, `Bounded<T extends Address>`; a `Circle` in a `Shape` field and in a
  `Shape[]`; classes that extend `Number` and `ArrayList`; enums, records, a sealed
  interface, `Runnable`, `CharSequence`, `Comparable`, an abstract class, `Number`,
  `Object`, `Object[]`, `List`, `ArrayList`, `Map`, `HashMap`, `Set`, `Optional`,
  `OptionalInt`, `LocalDate`, `Instant`, `Date`, `BigDecimal`, `BigInteger`, `UUID`,
  `StringBuilder`, `AtomicLong`, `Class`, `List[]`, a `Map` three levels down; field names
  of 255 and 256 bytes; 32,767 and 32,768 fields; a list of 17 nodes; a cycle, also through
  an array element.
* Values at a key: `Integer`, `Long`, `Short`, `Byte`, `Character` (a lone surrogate too),
  `Boolean`, `Float` (NaN), `Double` (-0.0), `int[]`, `int[][]`, `String[]`, `char[]`,
  `boolean[]`, `Address[]`, `Integer[]`, `byte[][]`, each read back exactly, also as
  `int.class` and `long.class`; and 18 values refused (an enum, a record, `List.of`,
  `Map.of`, an `Optional`, a lambda, an `Object[]`, ...).
* Conversions: one object of 45 fields (every primitive, extremes, NaN, the infinities,
  1e300, 30 texts) read into 15 classes with the same field names, each class's fields of
  one type (`boolean` to `double`, `String`, `byte[]`, `Integer`, `Character`, `int[]`,
  `String[]`, `Double`): 675 conversions, the documented ones checked, all printed (the
  `MATRIX` lines of `run.txt`); 12 arrays and objects into 12 array and object types
  (`ARRCONV`); a `Customer` read by a changed class (a field renamed, `Integer` to `int`,
  `Boolean` to `boolean` with an initial value, `Double` to `float`, `byte[]` to `String`,
  `String` to `int`, `char` to `String`, `short` to `byte`, an object to `long`, `float`
  to `double`, a new field), a read-modify-write by it, and the first class reading that.
* User indexes on a `char`, a `float`, a `short`, a `byte`, an `Integer` with nulls, a
  `boolean`, a `double` with NaN, -0.0 and the infinities, and a `byte[]`, over 300
  products, against the application's own model; a scan into a changed class.
* Sizes (section 3), arrays of a million elements of each type, ten million ints; objects
  of 1,000 to 32,767 fields timed.
* Huge objects: 2,100 and 4,097 references to one 1 MiB `byte[]` in an array (2.2 and 4.3
  GB stored), 4,096 and one of 100 bytes (2^32 + 105), 2,100 references to one 1 MiB
  `String`; 1,000 references (1.05 GB); 25 fields of one 100 MiB `byte[]` (2.6 GB); a
  `String` field and a `String` value of 2.2 GB of UTF-8; by put, `w()`, `rw()` and
  `toDbObject()`, with 3 to 8 GB of heap.

Size: `Main.java` 1,212 lines, `Model.java` 386, `Check.java` 197, `Fill.java` 76,
`Bad.java` 66, the Unicode package 25, the probes 694 (and 301 generated classes), `gen.py`
69 (its classes 2.3 MB of source), `run.sh` 52. A run: the application 53 to 57 s with
241,476 checks (53.4 s in the last), the probes about 2 minutes, on F53 under a load of 20
to 30. The last run: every check passed but the four of U12-1.


## 2. The findings

Most severe first. A reproduction names a file in `probe/` or a section of `Main.java`.

| ID | Kind | Severity | What | Reproduction |
|----|------|----------|------|--------------|
| U12-1 | bug | high   | an array over 2^31 - 1 bytes: OutOfMemoryError, not refused  | HugeProbe |
| U12-2 | doc | medium | a put needs 4 to 5 times the object's size in heap           | HugeProbe |
| U12-3 | doc | low    | Data Object rules missing: superclasses, inner, generics     | Main, 2   |
| U12-4 | API | low    | messages name a field's type, not the class; one field a run | Main, 3   |
| U12-5 | doc | low    | "a text read as a number" is Java's grammar: "42d", "0x1p4"  | TextProbe |
| U12-6 | doc | low    | a float is a double: eq(0.1) misses 0.1f; 9 bytes an element | Main, 10  |
| U12-7 | doc | low    | a get as a wrapper reads the field "p", null if it is absent | Main, 4   |
| U12-8 | doc | low    | bytes into an int[] give null, the reverse gives bytes       | Main, 5b  |

### U12-1. An array over 2^31 - 1 bytes throws OutOfMemoryError (bug, high)

The package's "Objects" says that a put refuses "a stored value of more than 2^31 - 1
bytes" with `IllegalArgumentException` and before anything is written, and
`WBuilder.put()` that it refuses an object "larger than a stored value may be". With
`-Xmx3g`, a put of an object of 2,100 references to one 1 MiB `byte[]`, 2.2 GB stored and
1 MiB in memory, throws `OutOfMemoryError` after 0.5 to 1 s, from `put()`, `w()` and
`DbObject.toDbObject()`. In `rw()` the error fails the database: the next put throws
`DbFailedException` ("Cannot call execute(): the database failed (the cause) and must be
restarted."). Outside `rw()` the database goes on, but the Javadoc tells the application to
end its process after an Error (`Database`, "Errors"). The same for 4,097 references (4.3
GB, past 2^32), for 4,096 and one of 100 bytes, and for 2,100 references to one 1 MiB
`String`. With `-Xmx8g` the same put is refused as documented, with
`IllegalArgumentException`, at a resident size of 4.6 GB. It is the array: an object of 25
`byte[]` fields, each one 100 MiB array (2.6 GB), is refused with
`IllegalArgumentException` in 0.4 s with `-Xmx3g`, in `rw()` too, and so is a `String`
field of 2.2 GB of UTF-8 with `-Xmx4g` (`FieldsProbe`, `BigStringProbe`).

```java
// probe/HugeProbe.java, shortened; java -Xmx3g ... HugeProbe rw 2100
public static class Huge { public byte[][] parts; public Huge() {} }
Huge h = new Huge();
h.parts = new byte[2100][];
Arrays.fill(h.parts, new byte[1 << 20]);       // 1 MiB in memory, 2.2 GB stored
c.rw(env -> env.put("/huge", h));              // OutOfMemoryError: Java heap space
c.put("/after.txt", "x");                      // DbFailedException
```

Why, read afterwards: `DataObjects` turns each `byte[]` into a `DbByteArray`, whose
constructor clones it, and `DbArray.Builder.add()` writes each element into its growing
buffer; `ObjectFormat.checkValueSize()` refuses only the element that takes the array past
2^31 - 1 bytes, so about 2 GB is copied before the refusal. An object's fields are summed
before they are written ("a stored value of 2202009789 bytes or more"), an array's elements
are not. Suggested: the array's size first, as the object's, by a walk that adds sizes
without copying, and the refusal before any copy. The Javadoc does not say that two
references to one array are stored as two copies (they are, and read back as two arrays,
which is right); so an application that keeps one large array in several places meets this
with a small object. The message at 8 GB, "size: a value of 2147493890 bytes; a stored
value has at most 2^31 - 1 bytes, and an object's frame some of them (bergdb 020-07, R15)",
starts with the internal "size:", gives the size where the writer stopped, not the object's
2.2 GB, and names no place, where `WBuilder.put()` says that the message names the class or
the place. High, as U5-2: a call that the Javadoc says is refused fails the database in
`rw()`.

### U12-2. The heap a put of a large object needs (doc, medium)

A legal object of 1.05 GB (1,000 references to one 1 MiB `byte[]`) throws
`OutOfMemoryError` from a plain `put()` with `-Xmx3g`, while the object is made, and the
database goes on; with `-Xmx4g` it throws after 7 s, in the transaction, and the database
fails (the next put throws `DbFailedException`). With `-Xmx5g` it is stored in 7 s; an
object of 0.52 GB is stored with 4 GB. So a put needs about 4 to 5 times the object's
stored size in heap, beside the object itself. The Javadoc gives 2^31 - 1 bytes as a stored
value's limit and 1.88 GB as a transaction's, and says nothing of the heap a put needs; a
user who stores a 1 GB object in a JVM of 4 GB loses the database at the put. Suggested:
the factor in the package's "Objects" or at `Connection.put()`, beside U4-1's heap of a
database; or fewer copies (the clones and the growing buffer of U12-1).

### U12-3. Data Object rules that the Javadoc does not give (doc, low)

The Javadoc's rules (a public class, a public no-argument constructor, public fields not
final, no hiding, the closed list; "Not on it: Object, interfaces, enums, records,
abstract classes, the classes of the Java platform") do not cover four cases that a Java
model meets, each refused, at the put and at the get, with a clear message:

* A public field declared by a superclass that is not public: "its field 'fromPkgBase' is
  declared by app.Model$PkgBase, which is not public (V4)". "Objects" says that the fields
  of the superclasses are stored, and nothing of their access. (A public abstract
  superclass works.)
* A class that extends a class of the Java platform: "it extends java.util.ArrayList, a
  class of the Java platform (V5)"; also `Number`. The list names such classes as field
  types only.
* An inner class, not static, whose source has `public Inner() {}`: "it is an inner class,
  not static (V1)".
* A field of a type variable: `public T value` of `Box<T>`, also in `StringBox extends
  Box<String>` and in `Bounded<T extends Address>`, whose erasure is a Data Object class:
  "its field 'value' is of a type variable, T, which BergDB does not store (V9)".

Suggested, in "Objects": a Data Object class is top-level or static nested; its
superclasses are public Data Object classes, or Object; a field of a type variable is not
stored, whatever its bound.

### U12-4. Messages of a field type not on the list (API, low)

A field of a type not on the list is refused with the field's type as the subject: "The
class java.util.List at 'list' is not a Data Object: it is an interface (V2)", for `public
List<String> list` in `ListField`. The class that was put, or got, is not named, and the
message reads as if the user had tried to store a `List` as a Data Object. A field of type
`Object` gets the other form, which names both: "The class app.Bad$ObjectField is not a
Data Object: its field 'any' is of the type java.lang.Object, which BergDB does not store
(V9)". The natural model's put (an enum, an `Instant`, a `List`, an `Optional` and a
`BigDecimal`) names one field, 'created', and the user meets the next at the next run:
five runs for five fields. No message says what to use instead: a `String` for an enum, an
array for a `List`, a `long` for an `Instant`, a nullable field for an `Optional`.
Suggested: the second form for every field type, all the class's bad fields in one
message, and a hint for the common types. The size message of U12-1 belongs here too.

### U12-5. "A text read as a number" is Java's grammar (doc, low)

The Javadoc says that a get reads a text as a number, and gives "12.7" as 12, but not which
texts are numbers. They are those of `Double.parseDouble()` after `trim()`, it seems
(`TextProbe`): "42d", "42f", "042", "4.2e1" and "\t42\n" read as 42 into an `int`, a
`long`, a `double` and a `float`; "0x1p4", a Java hex float, as 16, but "0x2A" as 0;
"42L", "4_2", "1,5", "\u00a042" (a no-break space), "١٢" (Arabic-Indic digits), "inf" and
"nan" as 0; "Infinity" as `Integer.MAX_VALUE`; "1e3" into a `byte` as 127. A reader in
another language, for which the format is "the same in every language", would read "42d"
and "0x1p4" otherwise. Suggested: the grammar in "Objects", or a portable one, such as
JSON's number with ASCII whitespace around it.

### U12-6. A float is a double (doc, low)

The Javadoc says that a `float` is stored as a double. Four consequences it does not say: a
"double" index on a `float` field finds none of the 31 products of weight 0.1f with
`eq(0.1)` and all 31 with `eq(0.1f)`, as the stored double is 0.10000000149011612; a
`float` field changed to a `String` reads 0.1f as "0.10000000149011612" and 19.99f as
"19.989999771118164" (`FloatProbe`), where Java's `Float.toString()` gives "0.1" and
"19.99"; a `float[]` takes 9 bytes an element, against 4 in Java (a million floats
9,000,019 bytes); and a double read into a `float` field is Java's `(float)` cast: 1e300
gives Infinity and 1e-300 0.0, where "the nearest value", beside "an integer clamped",
suggests `Float.MAX_VALUE`. Suggested: a sentence at `IndexBuilder`'s "double" and in
"Objects".

### U12-7. A get as a wrapper reads the field "p", and gives null when it is absent (doc, low)

`get(key, Integer.class)`, or `int.class`, of any stored object reads its field "p": the
`Reserved` object of 50 int fields, one of them named `p`, reads as 16. A `Customer`,
without a "p", reads as null, as it does by `int[].class` without an "array" field.
`Connection.get()` says that null means "no entry for the key"; only
`DbObject.toJavaObject()` says "null if it is absent". So a Data Object with a field named
"p" or "array" cannot be told from a value put as a wrapper or an array. Suggested: say it
at `Connection.get()`.

### U12-8. Bytes and arrays of integers (doc, low)

A stored `byte[]` field read into an `int[]`, `long[]`, `double[]`, `String[]`,
`Integer[]`, `char[]` or `boolean[]` field gives null; an `int[]` {1, -1, 300, 70000} read
into a `byte[]` field gives {1, -1, 127, 127}, and a `char[]` {'A', U+D800} gives {65,
127}. The conversions of "Objects" say that "a scalar read into an array other than a
byte[]" gives the zero, which covers the first only if bytes are a scalar, which it does
not say (bytes are one of the seven types, beside the array), and they do not give the
second. A natural change of a class, `byte[] flags` to `int[] flags`, so loses the data
at the next read-modify-write. Suggested: say that bytes count as a scalar here and that an
array of integers reads into a `byte[]` clamped; or read bytes into an array of integers,
as the reverse does.


## 3. Sizes

Measured with `DbObject.toDbObject(o).getBytes().length`, equal to the stored value
(`get(key, byte[].class)`). The bytes of `{a: "abc"}` are `82 48 01 07 01 61 14 03 61 62
63`: the header, three bytes of the object and its table of fields' ends, then each field
as its name's length, its name and its value as Binson's; so an empty object is 3 bytes,
and a field costs 2 bytes and its name besides its value.

| Object                                    |      Bytes |
|-------------------------------------------|------------|
| empty object                              |          3 |
| one int field `a` = 0 (also 127, -1)      |          8 |
| one int `a` = 128 (also 32,767)           |          9 |
| one int `a` = 32,768                      |         11 |
| one long `a` = 2^31 (also Long.MAX_VALUE) |         15 |
| two int fields `a`, `b` = 0               |         13 |
| one int, a name of 100 chars              |        107 |
| one double or one float `a`               |         15 |
| one boolean `a`                           |          7 |
| one String `a` = "", "abc", 200 chars     | 8, 11, 209 |
| one int[] of 0, 1 and 10 zeros            |  8, 10, 28 |
| one empty nested object                   |          8 |
| an Integer 42 at a key (the field "p")    |          8 |
| an int[] {1, 2, 3} at a key ("array")     |         18 |
| AllPrims, every field zero                |         56 |
| AllPrims at its extremes                  |        158 |
| Address (3 Strings, a char)               |         72 |
| Customer (an order, a line, Money)        |        452 |
| AllArrays, one to three dimensions        |        687 |
| Reserved, 50 int fields                   |        508 |
| Wide500, random                           |     15,619 |
| Chain C100, 101 fields, random            |      1,184 |
| 32,767 int fields of 0                    |    425,977 |

Arrays of a million elements, one array in an object, each put in one transaction:

| Elements | Bytes an element | Put ms | Get ms |
|----------|------------------|--------|--------|
| `int`, random              | 5.00 | 132 |  81 |
| `long`, random             | 9.00 | 189 | 110 |
| `double`, random           | 9.00 | 142 |  96 |
| `float`, random            | 9.00 | 154 |  94 |
| `boolean`                  | 1.00 | 117 |  31 |
| `byte` (a `byte[]`, bytes) | 1.00 |   6 |   0 |
| `char`, random             | 4.00 | 156 |  77 |
| `short`, random            | 3.00 | 136 |  59 |
| `String` "s0" to "s999999" | 8.89 | 128 | 119 |
| `Integer` 0 to 999,999     | 4.93 | 129 |  71 |

Ten million ints, 0 to 9,999,999, are 49,934,353 bytes, put in 1.8 s. Objects of 1,000,
4,000, 16,000 and 32,767 int fields are put in 0.6, 1.7, 4.1 and 8.2 ms, got in 0.2, 0.9,
4.3 and 9.6 ms (`WideProbe`): linear.


## 4. What went well

* Every round trip was exact, as the class, as a `DbObject` walked field by field, by
  `toJavaObject()` and after a restart: 241,476 checks, among them 700 random objects with
  NaN payloads, subnormals, lone surrogates in chars, strings of every plane and the
  extremes of every integer type.
* The refusals are by type, so a null field does not hide a bad type, at a put and at a
  get, also at a key without a value; each of the 124 wrote nothing, and the database went
  on after each (but U12-1).
* The messages of the grey zone are precise: the class, the field and why, as "its field
  'secret' is not public and not transient", "it is an inner class, not static", "it has
  no public no-argument constructor", "it is an anonymous or a local class, never public",
  "a record, which 2026.4 does not store", "The value at 'shapes[1]' is a
  app.Model$Circle, not a app.Model$Shape", the depth with its path, a cycle as "the
  TextProbe$N at kids[1] is also at the top", a name of "258 bytes in UTF-8; a name has 1
  to 255", "32768 stored fields, more than 32767".
* No class name is stored, so a class may move to another package or be renamed: `Kund`
  in `ünïcödé.модель` is read by `顧客`, and a chain of 101 classes by its top superclass.
  Unicode field names of every plane are kept, `µ` and `μ`, `é` and `e` + U+0301 apart,
  and 169 names that sort otherwise in UTF-16 than in UTF-8 (fullwidth letters, Hangul,
  CJK compatibility ideographs against Fraktur and Deseret letters) are found by every
  lookup, also in an object of the Builder (`OrderProbe`).
* Two versions of one class name in two class loaders, as a reload makes, each read and
  wrote with its own fields (`LoaderProbe`); 16 threads that used 300 classes for the
  first time at once, by put and by `w()`, read back 4,800 objects exactly (`ManyProbe`).
* "A get never throws for the data" held: random stored objects, made with the Builders
  (any type in any field, mixed arrays, bytes that look like an object, texts such as
  "1e400" and "0x1p4"), read into 16 classes and types by a get and by `toJavaObject()`,
  1,280,000 times over four seeds, 640,000 of them in `run.txt`, threw nothing
  (`ConvFuzz`).
* A refused put inside `rw()` that the action catches leaves the rest of the transaction
  to commit, and a `WBuilder` stays usable after a refused put (`RwProbe`); a subclass's
  public field may have the name of a superclass's private transient or static field
  (`HideProbe`).
* Every documented conversion holds, in the 675 scalar and 144 array cases: integers
  clamped, never wrapped; a double cut toward zero, NaN as 0 and as false; chars as their
  numbers; booleans as 1 and 0, "true" in any case; bytes as UTF-8 with U+FFFD; an array
  into a scalar as the zero; and the changed `Customer` came out as the rules say, also
  after its read-modify-write.
* The user indexes on the small types are right against the model: a `char` level by its
  code (`eq('B')` takes `eq(long)`, lone-surrogate chars in order), a `byte` signed, a null
  `Integer`, a NaN and a `boolean` without an entry, -0.0 and 0.0 one key, a `byte[]`
  prefix; a scan into a changed class converts as a get does.
* Wide objects are cheap and linear to 32,767 fields; a million-element array takes 6 to
  189 ms to put, an array of a million small objects 0.6 s and a get of it 0.3 s
  (`ManySmallProbe`).

## 5. Fixes

Made 2026-11-09 for coord-1109, in `clone-o23`, by the rule for 2026.4: a
plain bug fixed with a failing test first; elsewhere the Javadoc made true
where the code is as designed; no new API and no change of meaning. The
entry is 021-23. The two commits, on main at `9ed1e6c`, gated on one tree
under the gate lock: BEFORE COMMIT OK (149 s, unit 1582, f 86, demos), JAVADOC PUB OK.

* **U12-1** (`71e909b`, 021-23, tests failing first): a put counts the object's
  stored bytes first, exactly as the build writes them and without a copy,
  and refuses it with `IllegalArgumentException` where the count passes
  2^31 - 9 bytes, the largest Java array (`DbObject.Builder`'s limit
  already; the format allows 2^31 - 1): "The object is too large: its
  stored value passes 2147483639 bytes at 'parts[2047]'. A stored value
  has at most 2^31 - 1 bytes, and in Java at most 2^31 - 9, the largest
  Java array (bergdb 020-07, R15; 020-09, section 4.7)." `HugeProbe` with
  `-Xmx3g`, put, w, rw and todb, 2,100 and 4,097 references: refused in 12
  to 16 ms, nothing written, the database goes on; `FieldsProbe` refused
  at 'b20' in 10 ms, where it cloned 2.6 GB first. The walk adds about
  0.5 µs to `toDbObject()` of a 14-field object, a few per cent of a put.
  Tests in `DataObjectsTester`: `testPutTooLarge`, `testStoredSizeExact`,
  and `r1()` for each random object. The Javadoc gives the limit as Java
  has it, and says that a referenced array is stored once per reference.
* **U12-2** (`4d65bb5`): the package's "Objects" and `Connection.put()`: a put
  of a large object needs heap of about 4 to 5 times its stored size;
  `put()` and `WBuilder.put()` convert at the call, so an
  `OutOfMemoryError` there fails only the call, and one in `rw()`'s action
  or in a transaction fails the database; keep an object below a fifth of
  the free heap. The copies are as before; one exact allocation, now that
  the size is known first, would lower the factor (not done: no change
  asked).
* **U12-3** (`4d65bb5`): "Objects" says that a Data Object class is top-level or
  static nested (V1), that a superclass that declares a stored field is
  public (V4), that no class of the Java platform is a superclass (V5),
  and that a field of a type variable is not stored, whatever its bound
  (V9).
* **U12-4**: not changed; an API point for Frans: the message of a field
  type not on the list could name the class put and the field, as the
  `Object` field's form does, list all bad fields at once, and suggest a
  type (a `String` for an enum, an array for a `List`, a `long` for an
  `Instant`). Not trivial: the class check keeps one fault a class, and
  the get's messages share it.
* **U12-5** (`4d65bb5`): "Objects" gives the grammar of a text read as a number,
  020-09, section 5.5: Java's, with the texts that read as 42, as 16 and
  as 0.
* **U12-6** (`4d65bb5`): "Objects" and `IndexBuilder`: a float is stored as
  `(double) f`, so `eq(0.1f)` finds 0.1f and `eq(0.1)` does not; its text
  as a `String`; 9 bytes an element; a double into a float is Java's cast,
  1e300 Infinity.
* **U12-7** (`4d65bb5`): `Connection.get()` says that a primitive, wrapper or
  array class reads the field "p" or "array" of any stored object, and
  gives null when it is absent, also in its `@return`.
* **U12-8** (`4d65bb5`): "Objects" says that bytes count as a scalar, so a
  stored `byte[]` reads as null into an `int[]`, and that an array reads
  into a `byte[]` element by element, clamped (020-09, sections 5.4 and
  5.7).
