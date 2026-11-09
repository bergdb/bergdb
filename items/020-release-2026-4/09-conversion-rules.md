# 020-09 Data Objects and DbObjects: the conversion rules

Created 2026-11-08 by Frans Lundberg. Status: open; decided, for 020-08's
step 8, which codes it. The exact rules of the conversion between Data
Objects and `DbObject`s in Java for release 2026.4, both ways: which
classes are Data Objects, what a put stores and refuses, what a get sets
and throws, how today's code differs, and the tests. Step 8 can be coded
and tested from this document, 020-07 (the stored format) and the code.
No code changed.

The decisions it holds (020-02, section 2's decision and section 5.1b):

* Frans, 2026-11-08, 21:47: "[...] for 2026.4, let's go with
  best-effort. [...] Users who want full control need to get object of
  type DbObject and from that convert to Data Objects explicitely.
  Regarding puts and null fields. Allow it a null-valued field in the Data
  Object. Such a field is not written, it is not a field in the DbObject.
  Regarding gets. When a field name matches, always make a conversion,
  best effort. There are many details for how to do this. You can propose
  the exact rules."
* The coordinator's principles and table (21:48), principle 4 revised by
  Frans (21:56: "If there is a field name match, the fields data always
  depends only on the database value, not of a Java default."), accepted
  at 21:59: "Yes, do so."
* Data Objects, public fields only (20:44); the layers (20:23, 20:44); no
  key field and no `put(Object)` (19:21); `createFast()` goes (19:43).
* Frans delegated the rest, 22:17: "make the decisions needed to get the
  2026.4 release ready". A rule marked **(delegated)** is the
  coordinator's decision under that delegation, taken by the principles,
  with its reason; section 6 lists them, one line each, for Frans's
  information.

Where this document and 020-02 differ, 020-02 wins. Code read at
`b9d87e7` (`java/` as at `460709a`); today's behaviour, where section 7
gives it, was also probed on 2026-11-08 with a small program against the
jar built from that code.


## 1. In short

* **Two layers** (020-02, section 5.1b): layer 1, a `DbObject` and its
  stored bytes, exact (020-07); layer 2, this document, between
  `DbObject`s and Data Objects. A get as `String`, `byte[]`, `DbObject`
  or `Object` is not layer 2 and does not change.
* **A Data Object class** is public, with a public no-argument
  constructor; its stored fields are the public, non-static,
  non-transient fields of it and its superclasses; every other instance
  field is transient; each stored field's type is on a closed list. One
  check per class, the same at a put and at a get (section 3).
* **The put is exact** (section 4): each field by its declared type to
  one stored kind; a null field left out; a null array element, a value
  of another class than its field's, a cycle and a depth above 16
  refused with `IllegalArgumentException`, naming the path.
* **The get is best effort** (section 5): by name; a value that fits is
  set exactly, else the nearest value, integers clamped; the type's zero
  where no sensible conversion exists; never a throw for the data. It
  throws `ObjectCreationException` for a class that is not a Data Object
  (also for a key without a value), for a value that is not a stored
  object (layer 1, as today), and for a constructor that throws.
* **24 decisions under the delegation** (section 6), among them: text
  trimmed and read with ASCII digits only; a `char` read from text as a
  number; a `float` by `Float.parseFloat`; no class of the Java platform;
  no field that hides another; a value's class must be its field's.
* **Today's code** (section 7): 005-22's `DataFormatException` at a get
  goes; so do S2-F4, F6, F7, F8, F9, F18, F19 and F21 (020-01, section
  5.3); the field `key` becomes an ordinary field.
* **Tests** (section 8): 122 get cases, 18 class cases, 36 put cases, and
  three properties: the round trip, a reference of the table, and
  principle 4.


## 2. Terms

* **Stored kinds**: 020-07's seven types: boolean, integer (64 bits),
  double, string, bytes, array, object. A **scalar** is a value of the
  first five (020-07, section 2.2): strings and bytes included.
* **Field type**: a field's declared type (`Field.getType()`); for an
  array's element, the array type's component type; at the top of a get,
  the class given (section 5.9).
* **The closed list**, the types that layer 2 converts:
  * `boolean`, `byte`, `short`, `char`, `int`, `long`, `float`, `double`;
  * their wrappers, `Boolean`, `Byte`, `Short`, `Character`, `Integer`,
    `Long`, `Float`, `Double`;
  * `String` and `byte[]`;
  * `E[]` for every `E` on the list, of any number of dimensions,
    `byte[][]` included;
  * Data Object classes (section 3).

  Nothing else (section 3.2, V9).
* **Integer types**: `byte`, `short`, `char`, `int`, `long` and their
  wrappers. **Number types**: these and `float`, `double` and theirs. A
  wrapper converts as its primitive, the result boxed.
* **The zero** of a type T (principle 4, decided): `false`, `0`,
  `'\u0000'`, `0L`, `0.0f`, `0.0` for each primitive and its wrapper (an
  `Integer` field gets 0, never null); null for `String`, `byte[]`,
  arrays and Data Object classes.
* **Clamped**: a value below the type's least is the least, above its
  greatest the greatest: `byte` −128 to 127, `short` −32,768 to 32,767,
  `char` 0 to 65,535, `int` −2^31 to 2^31 − 1, `long` −2^63 to 2^63 − 1.
* **Path**: where a value is, from the top object, as 021-04's: field
  names joined by `.`, an element's index in brackets, `inner.names[3]`;
  "the top" for the top object.
* **A put** of an object: `Connection.put`, `WBuilder.put` and
  `RwEnvironment.put` of a value that is not a `String`, a `byte[]` or a
  `DbObject`, and the conversion by hand, `DbObject.toDbObject` (020-08,
  section 3). **A get** into a class: `get(key, C)` for a class C other
  than `String`, `byte[]`, `DbObject` and `Object`, the scans and index
  reads of objects of C (`usePrimary`, `useIndex`), and the conversion by
  hand, `DbObject.toJavaObject(Class)` (020-08, section 3). The same rules
  everywhere.
* **Java's binding.** These are the rules of Java's binding. A binding in
  another language converts in its own way over the same stored objects
  (020-02, section 2.5), so Java's syntaxes here (`Double.parseDouble`'s)
  are not rules of the format.


## 3. Data Object classes

### 3.1. The rule

Frans, 2026-11-08, 20:44, to "Do you decide (i), public only, with other
instance fields refused unless transient?": "Yes, let's go for public
fields only. For 2026.4." The rule, as 020-02, section 5.1b, records it:
"BergDB stores the public, non-static, non-transient fields of a public
class with a public no-argument constructor, inherited public fields
included; a put refuses a class with another instance field that is not
transient, naming the field". The check of section 3.2 makes it exact.
Nothing in it depends on the data.

### 3.2. The check

A class C is a Data Object class if and only if:

* **V1. Public**: `Modifier.isPublic(C.getModifiers())`. A nested class
  is one if it is a public static member class; its enclosing classes
  need not be public, as reflection reads C's own access. An anonymous or
  a local class is never public.
* **V2. A public no-argument constructor**: `C.getConstructor()` finds
  one; and C is not abstract, an interface, an enum, a record, an array
  or a primitive. Records are not Data Objects in 2026.4 **(delegated:**
  question 2's lean, 020-02, section 5.1b; a record's components are
  private final fields, read by accessors, a later addition**)**.
* **V3. The fields**: each non-static field declared by C or by a
  superclass of C (up to `Object`, not included) is one of:
  * a **stored field**: public, not final, not transient;
  * transient, of any access: not stored, not set;
  * synthetic (`Field.isSynthetic()`), made by a compiler or a tool:
    ignored, as today **(delegated)**.

  Any other instance field makes C not a Data Object, and is named: a
  field that is not public and not transient (decided, 20:44); a public
  final field **(delegated:** question 2's lean; a get cannot set it
  without deep reflection, so it could not read back, and S2-F9's silent
  loss goes**)**.
* **V4. A public declaring class (delegated)**: each class that declares
  a stored field is public. A public field of a package-private
  superclass cannot be read or set without `setAccessible`, which the
  rule of 20:44 leaves out.
* **V5. Not a class of the Java platform (delegated)**: C's class loader,
  and that of each superclass of C below `Object`, is neither the
  bootstrap loader (`null`) nor `ClassLoader.getPlatformClassLoader()`
  (the superclasses since 2026-11-09, from a review of 020-08's step 8: a
  `Stamp extends Date` was stored as `{}`, a `Money extends Number` as an
  integer). Such classes are not made for
  storage, and some pass V1 to V4 by chance: `java.util.Date` has only
  transient instance fields, so it would be stored as `{}` and read back
  as the time of the read (S2-F18), and `java.lang.Object` has none. The
  platform types that BergDB takes are the closed list's.
* **V6. Exported to BergDB (delegated)**: `C.getModule().isExported(
  C.getPackageName(), M)`, M the module of BergDB's classes. True for
  every class on the class path, and for a package of a named module that
  `exports` it (`opens` is not needed). Else `Field.get` would throw
  `IllegalAccessException` at the first use; the check says why first.
* **V7. Names**: each stored field's name is 1 to 255 bytes in UTF-8, with
  no lone surrogate (020-02, sections 4.4 and 4.9; 020-07, R6). javac
  takes longer names (256 ASCII letters), and a generated class may have
  any.
* **V8. One stored field a name (delegated)**: no two stored fields have
  one name, as when a subclass declares a public field with a public
  superclass field's name. The put is exact, and one of the two values
  would be lost (S2-F19: today the superclass's value is stored and read
  into both).
* **V9. Types**: each stored field's type is on the closed list (section
  2); a Data Object class by this check, recursively (a class may refer to
  itself, directly or through others; each class is checked once). Not on
  it **(delegated)**: `Object` and `Object[]` (a get cannot know which
  Java type to make, and an `Integer` put would read back as another
  type; S2-F7 and S2-F8 go with them), interfaces, abstract classes,
  enums, records, platform classes (V5), `DbObject` and `DbArray` (no
  public no-argument constructor; a `DbObject` field may come later, to
  keep a part of a stored object as it is), and a type variable (erased to
  `Object` or its bound).
* **V10. Count**: at most 32,767 stored fields (020-07, R3).

The result, valid with the stored fields in name order and the
constructor, or not valid with the reason, is kept per class for the
JVM's life (a `ClassValue`), so the check runs once per class.

### 3.3. When it runs, and what it throws

* **At a put**: on the class of each object met, from the top:
  `IllegalArgumentException`, its message naming the path where the class
  was met, the class, the field and the reason (section 4.7).
* **At a get**: on the class given, before the value is read, also when
  the key has no value **(delegated:** principle 1; a programming error is
  found whatever the data, and a get that threw only when the key holds a
  value would throw by the data**)**: `ObjectCreationException`, its
  message as at a put, the path counted from the class given. It is
  today's exception of a get that cannot make its object, for a class
  without a no-argument constructor **(delegated)**.
* The check of C covers its field types, so C is not valid when a Data
  Object class it reaches is not, whether or not a stored object has that
  field.
* A `LinkageError` while C or a field's type is loaded for the check (a
  `NoClassDefFoundError`) is the class's fault: C is not valid, with the
  error as the cause **(delegated)**. A `VirtualMachineError` passes as
  it is (P7, 018-01).


## 4. The put: Data Object to DbObject, exact

### 4.1. What exact means

A put stores each value so that a get into the same class reads it back
equal (section 8.5, R1), but in one case that Frans decided: a null field
over a value that the class's constructor gives reads back as that value
(section 4.3). What cannot be stored so is refused before anything is
written; nothing is stored as nothing (020-02, section 5.1b).

### 4.2. Field types and stored kinds

Each stored field and each array element by its field type (section 2),
not by its value's class:

| Field type                               | Stored                                             |
|------------------------------------------|----------------------------------------------------|
| `boolean`, `Boolean`                     | boolean                                            |
| `byte`, `short`, `int`, `long`, wrappers | integer, the value                                 |
| `char`, `Character`                      | integer, the char's code, 0 to 65,535              |
| `float`, `Float`                         | double, `(double) f`, exact                        |
| `double`, `Double`                       | double; any NaN as `0x7ff8000000000000`; −0.0 kept |
| `String`                                 | string; a lone surrogate refused (021-04)          |
| `byte[]`                                 | bytes, copied                                      |
| `E[]`, other than `byte[]`               | array, each element by E's row                     |
| a Data Object class D                    | object: D's stored fields by this table            |

* A `char` is a number: a lone surrogate in a `char` or a `char[]` is
  stored as its code and reads back exactly (021-04's rule for `char[]`).
* NaN and −0.0: 020-07, R12 (020-02, section 4.8). A `float` NaN becomes
  the double NaN and reads back as `Float.NaN`.
* Integers are written in the fewest bytes (020-07, R9): 5 in a `byte`
  and 5 in a `long` are the same bytes, `10 05`.

### 4.3. Null

* **A null field** of a reference type is left out of the stored object,
  at any depth (decided: 020-04's (c), Frans, 21:47). A get then leaves
  the field at the class's constructor's value: the one case where a put
  does not read back exactly (020-04, section 2.6).
* **A null array element** is refused, naming its index, in an array of
  any element type and at any depth (`names[1]`, `rows[1]`, `[0]` at the
  top), and so is an array not filled (`new String[3]`) **(delegated:**
  (c) as 020-04, section 2.6, and 020-02, section 2b.3, define it; the
  format has no null and an array no absent element (020-07, section 3),
  and a zero or a dropped element would store another value than the one
  put**)**.
* **A null at the top**, `put(key, null)`, is refused, as today.

### 4.4. Arrays

* The component type comes from the field's declared type, or, at the
  top, from the array's class. An array of a primitive type has no null
  element; one of a reference type is checked element by element.
* `char[]`, `short[]`, `int[]` and the like are arrays of integers,
  `boolean[]` of booleans, `float[]` and `double[]` of doubles,
  `String[]` of strings, `byte[][]` of bytes, `int[][]` of arrays, `D[]`
  of objects. An empty array is an empty array.
* **The class of the value (delegated)**: an array value's class is its
  field's type exactly, and each element of a `D[]` is of class D
  exactly; else the put is refused, naming the path. Array covariance lets
  a `D[]` field hold an `E[]` of a subclass E; the get would make a `D[]`
  (section 4.5's reason).

### 4.5. Nested Data Objects

* A field of a Data Object class D holds a D, stored as an object of D's
  stored fields, recursively, each object one level deeper.
* **Its class (delegated)**: the value's class is D exactly; a subclass
  E of D is refused, naming the path and both classes. The put is exact:
  stored by E's fields, the get would make a D and drop E's; stored by
  D's, E's fields would be lost at the put.
* **Shared objects**: an object met twice, not on its own path, is stored
  twice; a get makes two objects, equal. A stored object holds no
  references (020-02, section 4.10).
* **Cycles**: an object that is on its own path is refused, as since
  005-23, with its message ("The object has a reference cycle: the C at
  next.next is also at the top."). An array can be on a cycle only through
  an object, since `Object[]` is not on the list (V9).

### 4.6. The top level

`put(key, x)` by the class of x:

| Class of x                         | Stored at the key                                |
|------------------------------------|--------------------------------------------------|
| null                               | refused, as today                                |
| `String`, `byte[]`, `DbObject`     | as today: not layer 2                            |
| a wrapper (`Integer`, `Character`) | an object with one field `p`, by section 4.2     |
| an array other than `byte[]`       | an object with one field `array`, by section 4.4 |
| a Data Object class                | an object, by section 4.2                        |
| anything else                      | refused (section 3)                              |

The fields `p` and `array` are today's wrapping (020-02, section 5.2;
020-07, section 12), a convention of Java's binding. The wrapping object
is level 1, a wrapped array level 2.

### 4.7. Refusals and limits

Every refusal is an `IllegalArgumentException` whose message names the
path, before anything is written: `put` and `w().put` throw at the call,
and the transaction holds nothing of the value (020-04, N5); inside
`rw()` it is the action's exception, the transaction is not committed,
and the database goes on.

1. A class that is not a Data Object class (section 3), where it is met.
2. A value whose class is not its field's type (sections 4.4 and 4.5)
   **(delegated)**.
3. A string with a lone surrogate (021-04, as today).
4. A null array element (section 4.3) **(delegated)**.
5. A container above level 16: the top object level 1, each object or
   array in it one level more, a scalar no level (020-02, section 4.10;
   020-07, R14 and Q1).
6. A cycle (section 4.5; 005-23).
7. A stored value above 2^31 − 1 bytes (020-07, R15); the Core refuses a
   transaction before that (020-07, section 11).
8. A null at the top (section 4.6).

The messages, drafts in 021-04's style:

* "The class com.example.Inner at 'inner' is not a Data Object: its field
  'secret' is not public and not transient (bergdb 020-09, section 3)."
* "The array element at 'names[1]' is null: BergDB stores no null, and an
  array has no absent element (bergdb 020-09, section 4.3)."
* "The value at 'inner' is a com.example.SubInner, not a
  com.example.Inner, the field's type (bergdb 020-09, section 4.5)."
* "The object is nested deeper than 16 levels of objects and arrays, at
  'next.next.(10 more).next' (bergdb 020-09, section 4.7)."


## 5. The get: DbObject to Data Object, best effort

### 5.1. The principles

Frans's decision of 21:47 and the principles as revised at 21:56 and
accepted at 21:59 (020-02, section 5.1b):

1. A get never throws for the data. It throws for a programming error
   (section 5.2).
2. By name: a stored field with a matching field of the class is
   converted; a stored field the class lacks is ignored; a field of the
   class without a stored field keeps the constructor's value.
3. Nearest value: a value that fits the field's type is set exactly; else
   the nearest value of the type; integers saturate, never wrap.
4. A matching field always gets a value that depends only on the stored
   value and the field's type, never on the constructor; where no
   sensible conversion exists, the type's zero (section 2).

"Matching" is by name only: the stored field's name and a stored field's
name of the class (V3) as equal UTF-8 bytes. A stored field named as a
transient, static or synthetic field of the class is ignored, as the class
has no stored field of that name (principle 2).

### 5.2. What a get throws

* `ObjectCreationException`, its message naming the class, the reason
  and, where there is one, the path, when:
  1. the class given, or a class it reaches through its field types, is
     not a Data Object class (section 3), checked before the value is
     read, also for a key without a value **(delegated)**;
  2. the value at the key is not a stored object: layer 1, 020-07's full
     check refuses it (format 1 named, 020-08's step 3), as today for
     bytes that are not an object, such as a `String` value read into a
     class;
  3. a constructor of the class or of a nested Data Object class throws:
     with that exception as the cause, every time, the constructor run
     once per object made **(delegated:** the class's fault, a
     programming error; today `ObjectCreationException`, or a `Bug` after
     a first success, S2-F21**)**. An `ExceptionInInitializerError` of the class's first
     use is the same, and so is an `Error` that a static initializer throws, which Java
     does not wrap (020-14, X2); a `VirtualMachineError` passes as it is (P7).
* `IllegalArgumentException`: a null class, or a key that is not valid,
  as today.
* Nothing else, and nothing for a value of the data: no
  `DataFormatException` (005-22's goes), no `Bug`, no reflection
  exception, no `NullPointerException`, no `ArrayStoreException`.
* Inside `rw()` each is the action's exception, not an `Error`: the
  database goes on (019-10).

A nested class's constructor runs only for a stored object that needs
it, so its throw shows with such data only. It is still the class's
fault, which no check can find before the constructor runs.

### 5.3. Making the object

For a stored object s and a Data Object class D:

1. A new D by its public no-argument constructor
   (`Constructor.newInstance()`, without `setAccessible`).
2. For each stored field f of D (V3), in the order of the names' UTF-8
   bytes, which is the stored fields' order (020-07, R7) **(delegated:**
   one order, the one that a walk of both in name order gives (020-02,
   section 5.1); only a nested constructor's side effects could show
   it**)**: if s has a field of f's name, f is set to its value converted
   to f's type (sections 5.4 to 5.8), by `Field.set`; else f is not
   touched.
3. The object is returned. No field of it is read, and none is set twice.

A matching field is set even when its value equals the constructor's:
principle 4 says what it holds, not whether it is written.

### 5.4. The table

Stored kind against field type; a wrapper as its primitive, its result
boxed; v an integer, x a double, s a string, b bytes. Frans accepted the
table (21:48 to 21:59); the rows marked † are made exact by the delegated
decisions below the table and in sections 5.5 to 5.7.

| Stored  | Field type             | Result                                                 |
|---------|------------------------|--------------------------------------------------------|
| integer | `long`                 | v                                                      |
| integer | `int`, `short`, `byte` | v clamped                                              |
| integer | `char`                 | v clamped to 0 to 65,535                               |
| integer | `double`               | `(double) v`, the nearest double                       |
| integer | `float`                | `(float) v`, the nearest float, from the long †        |
| integer | `boolean`              | `v != 0`                                               |
| integer | `String`               | `Long.toString(v)`                                     |
| double  | `double`               | x, its bits as stored (NaN, −0.0, ±Infinity)           |
| double  | `float`                | `(float) x`: the nearest; ±Infinity beyond; NaN to NaN |
| double  | an integer type        | `(long) x` (toward zero, NaN 0, saturated), clamped †  |
| double  | `boolean`              | `x != 0.0 && !Double.isNaN(x)`: −0.0 and NaN are false |
| double  | `String`               | `Double.toString(x)`                                   |
| boolean | `boolean`              | the value                                              |
| boolean | a number type          | 1 or 0 (`1.0`, `'\u0001'`, ...)                        |
| boolean | `String`               | `"true"` or `"false"`                                  |
| string  | `String`               | s                                                      |
| string  | an integer type        | parsed: section 5.5 †                                  |
| string  | `double`               | `Double.parseDouble(s)`; unparseable 0.0               |
| string  | `float`                | `Float.parseFloat(s)`; unparseable 0.0f †              |
| string  | `boolean`              | `Boolean.parseBoolean(s)`                              |
| string  | `byte[]`               | its UTF-8 bytes                                        |
| bytes   | `byte[]`               | b, a new array                                         |
| bytes   | `String`               | `new String(b, UTF_8)`, ill-formed parts as U+FFFD †   |
| array   | `E[]`, `byte[]` too    | the same length, element by element: section 5.7 †     |
| object  | a Data Object class D  | a new D, made by section 5.3, recursively              |
| other   | any other              | the type's zero                                        |

The other pairs, in full:

* bytes, an array or an object into a number type or `boolean`: the zero
  (a wrapper the boxed zero);
* an array or an object into `String`: null;
* an integer, a double, a boolean or an object into `byte[]`: null;
* a scalar or an object into `E[]` other than `byte[]`: null. A stored
  scalar never becomes a one-element array (Frans accepted, for
  simplicity); bytes are a scalar, so bytes into `Byte[]` or `int[]` give
  null;
* a scalar or an array into a Data Object class: null.

The double row into an integer type, exactly: `(long) x` by Java's
narrowing (JLS 5.1.3: toward zero; NaN gives 0; beyond `long`'s range,
`Long.MIN_VALUE` or `Long.MAX_VALUE`), then clamped to the field's type as
an integer is **(delegated:** principle 3; Java's own `(short) x`, `(byte)
x` and `(char) x` go through `int` and wrap, `(short) 40000.0` being
−25,536**)**. `(int) x` gives the same as this for every x.

### 5.5. Text into numbers, booleans and chars

A string into an integer type T, `char` included, beyond the table's
"parsed as a decimal integer, else as a double then as a double is
converted, unparseable 0" **(delegated)**:

1. t = `s.trim()`: the chars up to U+0020 removed at both ends, as
   `Double.parseDouble` removes them anyway. So the integer way and the
   double way take the same texts; without it, `" 9007199254740993 "`
   would read through a double, as 9007199254740992.
2. If t is an optional `+` or `-` and one or more ASCII digits `0` to `9`:
   its value, exact, clamped to T; a value beyond `long`'s range gives
   `Long.MIN_VALUE` or `Long.MAX_VALUE`, then is clamped. ASCII only:
   `Long.parseLong` takes the digits of other scripts (`"١٢"` is 12) and
   `Double.parseDouble` does not; one syntax for both ways.
3. Else, if `Double.parseDouble(t)` gives x: x into T, as a double (the
   table): `"1.5"` is 1, `"-1.9"` is −1, `"1e3"` is 1000, `"NaN"` is 0,
   `"Infinity"` is T's greatest. Its syntax is Java's: a fraction and an
   exponent, `NaN`, `Infinity`, a hexadecimal number with a binary
   exponent (`"0x1p3"` is 8), a final `d`, `D`, `f` or `F`.
4. Else 0: `""`, `"abc"`, `"0x10"` (hexadecimal without a binary
   exponent), `"1_000"`, `"١٢"`.

And:

* **`char` (delegated)**: an integer type here: `"65"` is `'A'`, `"A"` is
  `'\u0000'`. A `char` is stored as its code, and an integer reads into a
  `String` as decimal text, so a `char` read into a `String` and read back
  into a `char` is the same char; a text's first char instead would read
  `"65"` as `'6'`.
* **`double`**: `Double.parseDouble(s)` (it trims); unparseable 0.0;
  `"1e400"` is Infinity.
* **`float` (delegated)**: `Float.parseFloat(s)`, the same syntax, rounded
  once to the nearest float (principle 3). `(float)
  Double.parseDouble(s)` rounds twice and differs for some texts:
  `"1.00000017881393432617187499"` gives 1.0000001f, and 1.0000002f by the
  double.
* **`boolean`**: `Boolean.parseBoolean(s)`, the table's: true only for
  `"true"` in any case, not trimmed; `"1"` and `" true"` are false.

The table's own consequence, kept: a text with a fraction reads into an
integer type through a double, so one with more than about 16
significant digits may differ from its truncation in its last digits.

### 5.6. Strings and bytes

* A string into `byte[]`: its UTF-8 bytes, exact, as a stored string is
  well-formed (020-07, R11).
* Bytes into `String` **(delegated:** Java's decoder, the simplest
  code**)**: `new String(b, StandardCharsets.UTF_8)`, which puts U+FFFD
  for each ill-formed part as Java's UTF-8 decoder finds it: `61 ff 62` is
  `"a\ufffdb"`, the cut `e2 82` one U+FFFD, `c0 af` two, an encoded
  surrogate `ed a0 80` one (Unicode's recommended practice gives three).
  The result is always well-formed, so a put of it is taken.

### 5.7. Arrays

* An array into `E[]`: a new `E[n]` for its n elements; element i is the
  stored element i converted to E by section 5, in index order. An element
  with no sensible conversion gets E's zero: `0` in an `int[]` or an
  `Integer[]`, null in a `String[]`, in an `int[][]` (a row) or in a
  `D[]`.
* **`byte[]` (delegated:** the table's "T[] of any element type" read
  literally**)**: a stored array into a `byte[]` field is converted
  element by element, clamped: `[1, 300, "x"]` gives `{1, 127, 0}`. Java's
  `byte[]` is an array of `byte`, and the conversion is a sensible one
  (principle 4). A stored bytes value is not an array: bytes into
  `Byte[]` or `int[]` give null.
* Several dimensions: the same, recursively; a stored element that is not
  an array, read into a row of an `int[][]`, gives a null row.
* So a get may make arrays with null elements; a put of the object back
  is refused (section 4.3) until they are set. The get is best effort,
  the put exact.

### 5.8. Objects

* An object into a Data Object class D: a new D, made by section 5.3; its
  fields without a stored match hold D's constructor's values.
* The field's value from the constructor is replaced, never filled: a
  class whose constructor sets `inner.w = 8` reads `{inner: {v: 3}}` as a
  new `Inner` with `v` 3 and `w` as `Inner`'s constructor gives it
  (principle 4).
* A stored object has at most 16 levels (020-07, R14), so the recursion is
  bounded.

### 5.9. The top level

`get(key, C)`, by the class C:

* `String`, `byte[]`, `DbObject` and `Object`: as today, not layer 2. A
  `DbObject` is the stored object exactly; no field `key` is added
  (decided, 020-02, section 5.1b).
* A primitive class or a wrapper (`int.class`, `Integer.class`): the value
  at the key must be a stored object (section 5.2, case 2); its field `p`,
  converted to C by section 5.4, boxed. No field `p`: null **(delegated:**
  there is no instance and no constructor's value; null is how a get says
  "no value" at the top, as for a key without a value**)**.
* An array class other than `byte[]` (`int[].class`, `String[][].class`,
  `Inner[].class`): its element type is checked as a field's type (section
  3); the field `array`, converted to C by section 5.7. No field `array`:
  null **(delegated**, as for `p`**)**.
* Any other class: checked (section 3), then the stored object made into a
  new C by section 5.3.
* A key without a value: null, after the check.

`get(key, int.class)` of `{p: 5}` is 5, of `{p: "12"}` 12, of `{p: {}}`
0, and of a `Person`'s object null.


## 6. Decided under Frans's delegation

For Frans's information: each decided by the coordinator under his
delegation of 2026-11-08, 22:17, by the principles; the reasons are in
the sections named.

1. A get checks its class first, also for a key without a value (3.3).
2. A get's programming errors are `ObjectCreationException`, today's
   (3.3, 5.2).
3. A constructor that throws: `ObjectCreationException` with the cause,
   every time (5.2).
4. A public final field makes a class not a Data Object, question 2's
   lean (V3).
5. Records are not Data Objects in 2026.4, question 2's lean (V2).
6. Synthetic fields are ignored (V3).
7. A class that declares a stored field is public (V4).
8. No class of the Java platform is a Data Object, as `Date` (V5).
9. A Data Object class's package is exported to BergDB (V6).
10. No two stored fields of one name: no field hiding another (V8).
11. `Object`, `Object[]`, interfaces, enums, `DbObject` and type variables
    are not on the list (V9).
12. A `LinkageError` in the check makes the class not valid, with the
    cause (3.3).
13. A null array element is refused (4.3).
14. A value's class is its field's type exactly, arrays and their elements
    too (4.4, 4.5).
15. Fields are set in the order of their names' UTF-8 bytes (5.3).
16. An integer into `float` by `(float)` of the long; a double into
    `short`, `byte`, `char` by `(long)`, then clamped (5.4).
17. Text is trimmed before it is read as an integer (5.5).
18. Only ASCII digits in an integer's text (5.5).
19. A decimal integer beyond `long`'s range saturates, exactly (5.5).
20. A `char` reads text as a decimal number (5.5).
21. A `float` reads text by `Float.parseFloat` (5.5).
22. Bytes into `String` by Java's UTF-8 decoder (5.6).
23. A stored array into `byte[]` element by element; bytes into `Byte[]`
    null (5.7).
24. A top-level get of a primitive, a wrapper or an array class from an
    object without `p` or `array`: null (5.9).

The plan's decisions under the same delegation are in 020-08, sections 2
and 3.


## 7. Today's code and the change

Today's behaviour at `460709a`, from the code and the probe; the
conversion is `DbValue.toJavaObject` (lines 160 to 209) with `checkFits`
(211 to 254) and `toLong()` (128 to 130, 0 for a value that is not a
number), `DbDouble.toString`, `DbByteArray.toJavaObject`,
`DbArray.toJavaObject` (79 to 110), `DbObject.toJavaObject` (607 to 696),
`getEligibleFields` (421 to 444, `setAccessible` on every field that is
not static, final, transient or synthetic), `toDbObjectOnPath` (558 to
605), the key in `getDbValue` (731 to 733), `BlankConstructorFactory` and
`KvToObjectImp.newObject` (125 to 141).

| Case                                  | Today                              | 020-09            |
|---------------------------------------|------------------------------------|-------------------|
| integer beyond a narrower field       | `DataFormatException` (005-22)     | clamped           |
| double NaN or beyond, into an integer | `DataFormatException`              | `(long)`, clamped |
| double beyond `float`'s range         | `DataFormatException`              | ±Infinity         |
| double 2^63 into `long`               | `Long.MAX_VALUE` (S2-F5)           | the same          |
| double 0.5 into `boolean`             | false: `(long) x != 0`             | true              |
| double 1.5 into `String`              | "d:1.5" (S2-F4)                    | "1.5"             |
| string "12" into a number             | 0 (`toLong()`, BG3)                | 12                |
| boolean into a number                 | 0 (`toLong()`)                     | 1 or 0            |
| bytes into a primitive                | `Bug` (S2-F6)                      | 0                 |
| bytes into `String`; into a wrapper   | null; null                         | decoded; 0        |
| object into a primitive               | `Bug`; with a field `p`, its value | 0                 |
| object into `String`                  | `InaccessibleObjectException`      | null              |
| array into `String`                   | "a:2" (`DbArray.toString`)         | null              |
| array with an object, into `int[]`    | `IllegalArgumentException`         | 0 for it          |
| array with an object, into `String[]` | `InaccessibleObjectException`      | null for it       |
| scalar into an array or class field   | null                               | the same          |
| non-public class, field, constructor  | read and written (`setAccessible`) | refused           |
| `Object` field, `Object[]`            | read as null (S2-F7, F8)           | refused           |
| final field                           | not stored (S2-F9)                 | refused           |
| a field that hides another            | one value for both (S2-F19)        | refused           |
| `Date` or `DbObject` field            | stored as nothing (S2-F18)         | refused           |
| a subclass of the field's class       | stored by its own class            | refused           |
| field `key` at a get                  | the database key                   | ordinary          |
| `DbObject.getString("key")`           | the database key                   | stored field      |
| constructor throws                    | OCE, or `Bug` later (S2-F21)       | OCE               |
| null field                            | a typed null, read as null         | left out          |
| null array element                    | stored                             | refused           |
| depth                                 | 1,000 objects (005-23)             | 16 levels         |
| invalid class, key without a value    | null                               | OCE               |

OCE: `ObjectCreationException`. And what goes with it in the code: the
three null encodings' readers and writers (020-08, step 2), `checkFits`,
the value classes' conversions (`toBoolean()` to `toStringValue()`,
`defaultValue`, `toNullDbValue`), `BlankConstructorFactory`,
`ClassToObject`, `ObjectFactory`, and `PubUtil` (020-08, section 5).


## 8. Tests

### 8.1. Notation and classes

Stored values: integers as decimal numbers (`5`, `-3000000000`); doubles
always with a point or an exponent, or as `NaN`, `Infinity`, `-Infinity`,
`-0.0` (`1.5`, `5.0`, `1e300`); `true`, `false`; strings in double quotes
with Java's escapes; bytes as `b(61 ff 62)`; arrays `[1, "a"]`; objects
`{v: 3}`. A get case puts `{F: S}`, built by `DbObject.Builder`, at a key,
gets it as `All` and reads the field F; "each" means that each field
named gives the result; `;` pairs the values of a row in order; "refs"
are the fields `bytes`, `ints`, `strs` and `inner`.

The classes, in the test, public static:

```java
public static class Inner {
    public int v = 5;
    public int w = 6;
    public Inner() {}
}

public static class All {           // initial values no case expects, but z's
    public boolean z = true;        public Boolean wz = true;
    public byte b = 7;              public Byte wb = 7;
    public short s = 7;             public Short ws = 7;
    public char c = 'x';            public Character wc = 'x';
    public int i = 7;               public Integer wi = 7;
    public long l = 7;              public Long wl = 7L;
    public float f = 7;             public Float wf = 7f;
    public double d = 7;            public Double wd = 7.0;
    public String str = "init";     public byte[] bytes = {9};
    public int[] ints = {9};        public Integer[] wints = {9};
    public String[] strs = {"init"};
    public int[][] ints2 = {{9}};   public byte[][] bytes2 = {{9}};
    public Inner inner = new Inner();
    public Inner[] inners = {new Inner()};
    public All() {}
}
```

`All0`: `All`'s fields with no initial values, so `z` and `wz` start
false; every case runs on both (G111). `Node`: `public int v; public Node
next;`.

### 8.2. Get cases

| ID   | Stored                           | Field                    | Result                  |
|------|----------------------------------|--------------------------|-------------------------|
| G1   | `5`                              | `l`                      | `5L`                    |
| G2   | `5`                              | `i`, `wi`                | `5`                     |
| G3   | `3000000000`                     | `i`                      | `2147483647`            |
| G4   | `-3000000000`                    | `i`                      | `-2147483648`           |
| G5   | `40000`                          | `s`, `ws`                | `32767`                 |
| G6   | `-40000`                         | `s`                      | `-32768`                |
| G7   | `200`                            | `b`, `wb`                | `127`                   |
| G8   | `-200`                           | `b`                      | `-128`                  |
| G9   | `65`                             | `c`, `wc`                | `'A'`                   |
| G10  | `-1`                             | `c`                      | `'\u0000'`              |
| G11  | `70000`                          | `c`                      | `'\uffff'`              |
| G12  | `9007199254740993`               | `d`                      | `9.007199254740992E15`  |
| G13  | `9223372036854775807`            | `f`                      | `9.223372E18f`          |
| G14  | `0`                              | `z`, `wz`                | `false`                 |
| G15  | `-7`                             | `z`                      | `true`                  |
| G16  | `-42`                            | `str`                    | `"-42"`                 |
| G17  | `5`                              | refs                     | `null` each             |
| G18  | `1.5`                            | `d`, `wd`                | `1.5`                   |
| G19  | `-0.0`                           | `d`                      | `-0.0`, its bits        |
| G20  | `NaN`                            | `d`                      | `NaN`                   |
| G21  | `1e300`                          | `f`                      | `Infinity`              |
| G22  | `-1e300`                         | `f`                      | `-Infinity`             |
| G23  | `0.1`                            | `f`, `wf`                | `0.1f`                  |
| G24  | `1.9`                            | `i`, `wi`                | `1`                     |
| G25  | `-1.9`                           | `i`                      | `-1`                    |
| G26  | `NaN`                            | `i`, `l`                 | `0`                     |
| G27  | `1e10`                           | `i`                      | `2147483647`            |
| G28  | `-Infinity`                      | `i`                      | `-2147483648`           |
| G29  | `9.223372036854775807E18`        | `l`                      | `Long.MAX_VALUE`        |
| G30  | `1e19`                           | `l`                      | `Long.MAX_VALUE`        |
| G31  | `40000.5`                        | `s`                      | `32767`, not −25,536    |
| G32  | `-40000.5`                       | `s`                      | `-32768`                |
| G33  | `300.7`                          | `b`                      | `127`                   |
| G34  | `-5.5`                           | `c`                      | `'\u0000'`              |
| G35  | `1e300`                          | `c`                      | `'\uffff'`              |
| G36  | `0.5`                            | `z`                      | `true`                  |
| G37  | `0.0`, `-0.0`                    | `z`                      | `false`                 |
| G38  | `NaN`                            | `z`                      | `false`                 |
| G39  | `Infinity`                       | `z`                      | `true`                  |
| G40  | `1.5`                            | `str`                    | `"1.5"`                 |
| G41  | `5.0`                            | `str`                    | `"5.0"`                 |
| G42  | `NaN`                            | `str`                    | `"NaN"`                 |
| G43  | `1e300`                          | `str`                    | `"1.0E300"`             |
| G44  | `-0.0`                           | `str`                    | `"-0.0"`                |
| G45  | `2.5`                            | refs                     | `null` each             |
| G46  | `true`                           | `z`, `wz`                | `true`                  |
| G47  | `true`                           | `i`, `l`, `wi`           | `1`                     |
| G48  | `false`                          | `i`, `l`, `wi`           | `0`                     |
| G49  | `true`                           | `c`                      | `'\u0001'`              |
| G50  | `true`                           | `d`; `wf`                | `1.0`; `1.0f`           |
| G51  | `false`                          | `str`                    | `"false"`               |
| G52  | `true`                           | refs                     | `null` each             |
| G53  | `"abc"`                          | `str`                    | `"abc"`                 |
| G54  | `"12"`, `"+12"`                  | `i`                      | `12`                    |
| G55  | `"-12"`                          | `i`                      | `-12`                   |
| G56  | `" 12 "`, `"\t12\n"`             | `i`                      | `12`                    |
| G57  | `"1.5"`, `"1.5f"`                | `i`                      | `1`                     |
| G58  | `"-1.9"`                         | `i`                      | `-1`                    |
| G59  | `"1e3"`                          | `i`                      | `1000`                  |
| G60  | `"0x1p3"`                        | `i`                      | `8`                     |
| G61  | `"abc"`, `""`, `"0x10"`          | `i`, `wi`                | `0`                     |
| G62  | `"1_000"`, `"١٢"`                | `i`                      | `0`                     |
| G63  | `"99999999999999999999"`         | `l`                      | `Long.MAX_VALUE`        |
| G64  | `"-99999999999999999999"`        | `l`                      | `Long.MIN_VALUE`        |
| G65  | `"99999999999999999999"`         | `i`; `b`                 | `2147483647`; `127`     |
| G66  | `"9007199254740993"`             | `l`                      | `9007199254740993L`     |
| G67  | `" 9007199254740993 "`           | `l`                      | `9007199254740993L`     |
| G68  | `"NaN"`                          | `l`                      | `0L`                    |
| G69  | `"Infinity"`                     | `l`                      | `Long.MAX_VALUE`        |
| G70  | `"-Infinity"`                    | `l`                      | `Long.MIN_VALUE`        |
| G71  | `"1.5"`, `" 1.5 "`               | `d`                      | `1.5`                   |
| G72  | `"abc"`                          | `d`                      | `0.0`                   |
| G73  | `"1e400"`                        | `d`                      | `Infinity`              |
| G74  | `"NaN"`                          | `d`                      | `NaN`                   |
| G75  | `"1.00000017881393432617187499"` | `f`                      | `1.0000001f`            |
| G76  | `"true"`, `"TRUE"`               | `z`                      | `true`                  |
| G77  | `" true"`, `"yes"`, `"1"`        | `z`                      | `false`                 |
| G78  | `"65"`                           | `c`                      | `'A'`                   |
| G79  | `"A"`, `"-5"`                    | `c`                      | `'\u0000'`              |
| G80  | `"70000"`                        | `c`                      | `'\uffff'`              |
| G81  | `"é"`                            | `bytes`                  | `{-61, -87}`            |
| G82  | `"12"`                           | `wi`                     | `12`                    |
| G83  | `"x"`                            | `wi`                     | `0`, not null           |
| G84  | `"abc"`                          | `ints`, `strs`, `inner`  | `null` each             |
| G85  | `b(01 02)`                       | `bytes`                  | `{1, 2}`, a new array   |
| G86  | `b(61 62)`                       | `str`                    | `"ab"`                  |
| G87  | `b(61 ff 62)`                    | `str`                    | `"a\ufffdb"`            |
| G88  | `b(e2 82)`, `b(ed a0 80)`        | `str`                    | `"\ufffd"`              |
| G89  | `b(c0 af)`                       | `str`                    | `"\ufffd\ufffd"`        |
| G90  | `b(01)`                          | `i`, `wi`; `z`; `d`      | `0`; `false`; `0.0`     |
| G91  | `b(01 02)`                       | `ints`, `wints`, `inner` | `null` each             |
| G92  | `[1, 2]`                         | `ints`                   | `{1, 2}`                |
| G93  | `[]`                             | `ints`                   | `{}`                    |
| G94  | `[3000000000, "7", 1.9, true]`   | `ints`                   | `{2147483647, 7, 1, 1}` |
| G95  | `[1, 300, -300, "x"]`            | `bytes`                  | `{1, 127, -128, 0}`     |
| G96  | `[1, "a", 1.5]`                  | `strs`                   | `{"1", "a", "1.5"}`     |
| G97  | `[{}, [2]]`                      | `strs`                   | `{null, null}`          |
| G98  | `[1, {}, "x"]`                   | `ints`, `wints`          | `{1, 0, 0}`             |
| G99  | `[[1, 2], [3], 4]`               | `ints2`                  | `{{1, 2}, {3}, null}`   |
| G100 | `[b(01), "a", 5]`                | `bytes2`                 | `{{1}, {0x61}, null}`   |
| G101 | `[{v: 3}, 5]`                    | `inners`                 | an `Inner` (v 3), null  |
| G102 | `[1, 2]`                         | `i`; `z`                 | `0`; `false`            |
| G103 | `[1, 2]`                         | `str`; `inner`           | `null` each             |
| G104 | `{v: 3}`                         | `inner`                  | a new `Inner`, v 3, w 6 |
| G105 | `{}`                             | `inner`                  | a new `Inner`, v 5, w 6 |
| G106 | `{v: "7", x: 1}`                 | `inner`                  | a new `Inner`, v 7, w 6 |
| G107 | `{v: 3}`, `{p: 3}`               | `i`; `str`               | `0`; `null`             |
| G108 | `{v: 3}`                         | `ints`, `bytes`          | `null` each             |
| G109 | no field of its name             | each                     | its initial value       |

The principles, the class's shape, the top level and the exceptions:

* **G110, principle 4 nested**: `Init { public Inner inner; public Init()
  { inner = new Inner(); inner.w = 8; } }` reads `{inner: {v: 3}}` with
  `inner` another object than the constructor's, `v` 3, `w` 6.
* **G111, principle 4**: each stored value of G1 to G109, read into `All0`,
  gives the field the same value as in `All`.
* **G112, ignored names**: `T { public transient int t = 5; public static
  int st = 5; public int n; }` reads `{t: 9, st: 9, n: 1}` as `t` 5,
  `T.st` 5, `n` 1.
* **G113, `key`**: `K { public String key; public int n; }` at `/k` reads
  `{n: 1}` with `key` null, and `{key: "x", n: 1}` with `key` `"x"`;
  `get("/k", DbObject.class).getString("key")` is null for the first.
* **G114, order**: `Log`, whose constructor gives each object the next
  number of a static counter, in `Two { public Log b; public Log a; }`:
  `{a: {}, b: {}}` reads with `a`'s number below `b`'s.
* **G115, top `p`**: after `put(k, 5)`: `get(k, int.class)` 5,
  `get(k, long.class)` 5L, `get(k, int[].class)` null.
* **G116, top `array`**: `{array: [1, "2", 3.5]}` at k: `get(k,
  int[].class)` `{1, 2, 3}`, `get(k, String[].class)` `{"1", "2", "3.5"}`,
  `get(k, Inner[].class)` `{null, null, null}`.
* **G117, top values**: `{p: "12"}` as `Integer.class` 12; `{p: {}}` as
  `int.class` 0; `{v: 3}` as `int.class` null.
* **G118, not an object**: a `String` value `"abc"` at k: `get(k,
  Inner.class)` and `get(k, int.class)` throw `ObjectCreationException`.
* **G119, the check first**: at a key without a value, `get(k,
  Inner.class)` is null and `get(k, Bad.class)` (K4's class) throws
  `ObjectCreationException`.
* **G120, in `rw()`**: G118's and G119's exceptions are the action's; the
  database goes on, and the next transaction commits.
* **G121, constructors**: `Throws { public Throws() { throw new
  IllegalStateException("t"); } }`: a get of `{}` as `Throws` throws
  `ObjectCreationException` with the `IllegalStateException` as its
  cause, at two gets in a row. `Holder { public Throws t; }` reads `{}`
  (a `Holder`, `t` null), and throws for `{t: {}}`.
* **G122, scans**: `usePrimary(All.class).objects()` over the stored
  objects of G94, G104 and G109 gives each as a get does.

### 8.3. Class cases

Each class is refused at a put of an object of it, or holding it, with
`IllegalArgumentException` naming the path, the class and the field, and
at a get as it with `ObjectCreationException`, also at a key without a
value; the valid ones are taken by both.

| ID  | Class                                                           | Result                 |
|-----|-----------------------------------------------------------------|------------------------|
| K1  | `private static class P { public int v; }`                      | refused (V1)           |
| K2  | a public class with a private no-argument constructor           | refused (V2)           |
| K3  | a public class with only a constructor `C(int)`                 | refused (V2)           |
| K4  | `Bad`, a public class with `int v` (package access)             | refused, names `v`     |
| K5  | a public class with `private transient int t`                   | valid, `t` ignored     |
| K6  | `public final int v`                                            | refused (V3)           |
| K7  | a field of `Object`, `List<String>` or `Runnable`               | refused (V9)           |
| K8  | a field of an enum, of `java.util.Date`, of `DbObject`          | refused (V9, V5)       |
| K9  | a field of `Object[]`                                           | refused (V9)           |
| K10 | `B { public int x; }`, `C extends B { public String x; }`       | refused (V8)           |
| K11 | `Outer { public Bad b; }`; at a get also of `{}`                | refused, names `b`     |
| K12 | `public int x` in a package-private `B`; `C extends B`          | refused (V4)           |
| K13 | an abstract class, an interface, an enum, a record              | refused (V2)           |
| K14 | a field name of 256 ASCII letters; of 255                       | refused (V7); valid    |
| K15 | `Box<T> { public T value; }`                                    | refused (V9)           |
| K16 | `new Object() { public int x = 1; }`, at a put                  | refused (V1)           |
| K17 | `Node`; a chain of 17 `Node`s, at a put                         | valid; refused (depth) |
| K18 | the shape of 2026.3's `Data.Index`: `String[]`, `String`, `int` | valid                  |

### 8.4. Put cases

| ID  | Value put                                           | Result                             |
|-----|-----------------------------------------------------|------------------------------------|
| W1  | `boolean true`; `Boolean false`                     | booleans                           |
| W2  | 5 in `byte`, `short`, `int`, `long` and wrappers    | integer 5, the bytes `10 05`       |
| W3  | `char 'A'`                                          | integer 65                         |
| W4  | `char '\ud800'`                                     | integer 55296                      |
| W5  | `1.5f`; `-0.0f`                                     | 1.5; −0.0                          |
| W6  | `Float.NaN`; `Float.MAX_VALUE`                      | NaN; 3.4028234663852886E38         |
| W7  | `Double.longBitsToDouble(0x7ff0000000000001L)`      | the NaN `0x7ff8000000000000`       |
| W8  | `"é"`                                               | string `c3 a9`                     |
| W9  | `"a\ud800"` in `str`                                | refused, names `str`               |
| W10 | `byte[] {1, 2}`, changed after the put              | bytes `01 02`                      |
| W11 | `new byte[0]`                                       | bytes of length 0                  |
| W12 | `int[] {1, 2}`; `char[] {'a'}`                      | `[1, 2]`; `[97]`                   |
| W13 | `float[] {1.5f}`; `boolean[] {true}`                | `[1.5]`; `[true]`                  |
| W14 | `byte[][] {{1}}`                                    | `[b(01)]`                          |
| W15 | `String[] {"a", null}` in `strs`                    | refused, names `strs[1]`           |
| W16 | `Integer[] {1, null}` in `wints`                    | refused, names `wints[1]`          |
| W17 | `int[][] {{1}, null}` in `ints2`                    | refused, names `ints2[1]`          |
| W18 | `Inner[] {null}` in `inners`                        | refused, names `inners[0]`         |
| W19 | `new String[2]` in `strs`                           | refused, names `strs[0]`           |
| W20 | null in `str`, `bytes`, `ints`, `wi`, `inner`       | each left out: `getType` `z`       |
| W21 | `String s = "dflt"` set to null                     | left out; a get reads `"dflt"`     |
| W22 | a `SubInner` in an `Inner` field                    | refused, names the field           |
| W23 | a `SubInner[]` or a `SubInner` element in `Inner[]` | refused, names the path            |
| W24 | a chain of 16 `Node`s; of 17                        | taken; refused                     |
| W25 | at the top, `int[]...` of 15 dimensions; of 16      | taken; refused                     |
| W26 | `a.next = a`                                        | refused: a cycle at `next`         |
| W27 | `a.x = b; a.y = b`                                  | two equal objects; a get makes two |
| W28 | at the top: `null`; `new Object[] {1}`              | refused                            |
| W29 | at the top: `5`; `'A'`                              | `{p: 5}`; `{p: 65}`                |
| W30 | at the top: `new int[] {1}`                         | `{array: [1]}`                     |
| W31 | a field named `key`                                 | an ordinary field `key`            |
| W32 | transient and static fields                         | not stored                         |
| W33 | fields declared `b` then `a`                        | stored `a`, then `b`               |
| W34 | a class with no stored field                        | `82 48 00`                         |
| W35 | a refused value and a valid one in one `w()`        | nothing written                    |
| W36 | a refused value in `rw()`                           | refused; the database goes on      |

### 8.5. Properties

Seeded, as 020-08's H0: in `before-commit.sh`'s unit group with a fixed
seed and sizes that take under 2 seconds, and with more seeds as a night
test.

* **R1, the round trip** (the put is exact): for each valid Data Object
  o, made at random over `All`, `Inner`, `Node` and classes of every field
  type, with values at every edge (each type's least and greatest, NaN,
  −0.0, ±Infinity, strings from U+0000 to U+10FFFF with surrogate pairs,
  empty arrays, depth 1 to 16) and null fields but no null array element,
  let r be the get of the put of o into o's class. For each stored field
  f: if `o.f` is not null, `eq(r.f, o.f)`; if it is null, `eq(r.f, new
  C().f)`. And when o has no null field, the put of r has the bytes of the
  put of o. `eq`: boxed `equals` for primitives and wrappers (so
  `Double.equals`: NaN equals NaN, −0.0 is not 0.0), `String.equals`,
  `Arrays.equals` for `byte[]`, arrays of one class and length with `eq`
  elements, Data Objects of one class with `eq` stored fields.
* **R2, the table** (the get is best effort): random stored objects of
  format 2, their names drawn from `All`'s fields and others, their values
  of every kind and edge (the texts of section 5.5, ill-formed UTF-8 in
  bytes, nested arrays and objects), read into `All`: no exception; each
  matching field equals the value of a reference of section 5's rules,
  written in the test from this document; each other field holds `All`'s
  initial value.
* **R3, principle 4**: the stored objects of R2, read into `All` and into
  `All0`, give each matching field the same value.


## 9. Questions for Frans

None. Frans delegated the remaining decisions (22:17); section 6 lists
those taken here.


## 10. Sources

* 020-02, sections 2 (the decision of 21:47), 2.5, 2b.3, 4.1, 4.4, 4.8,
  4.9, 4.10, 5.1, 5.1b and 5.2; 020-04, sections 2.1, 2.6 and 5.2; 020-07,
  sections 2.2, 3, 5 (R3, R6, R7, R9, R11, R12, R14, R15), 11, 12 and 14
  (Q1, Q4); 020-01, sections 4.1 and 5.3 (S2-F4 to F9, F18, F19, F21);
  021-04; 005-22; 005-23; 019-10; 018-01 (P7).
* The code at `b9d87e7`: `java/src/bergdb/pubimp/DbObject.java`,
  `DbValue.java`, `DbArray.java`, `DbInt.java`, `DbLong.java`,
  `DbDouble.java`, `DbBoolean.java`, `DbString.java`, `DbByteArray.java`,
  `KvToObjectImp.java`, `BlankConstructorFactory.java`, `PubUtil.java`,
  `RwEnvironmentImp.java`, `IndexManager.java`, `Data.java` (whose
  `Data.Index` goes in 020-10's step I2).
* Java SE 17: `Double.parseDouble`, `Float.parseFloat`, `Long.toString`,
  `Double.toString`, `Boolean.parseBoolean`, `String.trim`,
  `Class.getConstructor`, `Module.isExported`, `ClassValue`; the Java
  Language Specification, section 5.1.3 (narrowing primitive conversion).


## 11. Log

2026-11-08. Written for coord-1108 at Frans's request (21:59, "Yes, do
so": the rules in full, with a test for each), with what the decisions
left open decided under his delegation of 22:17 (section 6); read-only at
`b9d87e7`, today's behaviour probed against its build. No code changed.
020-08 brought up to date with it (its steps 7 and 8).

2026-11-09. Section 5.2: the Codex review's X2 (020-14) fixed, with its
test: an `Error` of a static initializer.
