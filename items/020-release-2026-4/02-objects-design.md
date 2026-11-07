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
