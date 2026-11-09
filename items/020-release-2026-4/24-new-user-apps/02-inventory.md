# 020-24-02 An inventory with user indexes

Created 2026-11-09 by Frans Lundberg.

An application written as a new user of release 2026.4 would write it
(020-24's brief): the release jar alone on the class path, and only what a
user reads (README.md, the Pub API's Javadoc in `java/src/bergdb/pub`,
`overview-pub.html`, `releases/next.md`). The jar was built from `b7aa2a0`.
The implementation and the items were read only afterwards, to explain a
surprise (020-09 for I-1).


## 1. The application

**What it does.** An inventory of products and stock movements, in seven
phases, each a JVM of its own, run by `run.sh`:

1. `load`: 30,000 products and 16 edge products in `/p/`; four indexes
   built over them; gets; 4,000 random updates; stock levels and
   movements; an index deleted and made again; the API's documented
   corners; several writes to one key in one transaction.
2. `concurrent`: after a restart, two indexes built while four writer
   threads write the directory (about 190,000 writes in all), then twelve
   rounds of every index against the primary scan at one frozen lookup
   time while the writers go on.
3. `restart`: 300,000 products in `/big/`, an index started and the
   database closed at once; at the next start the build resumes, with a
   writer in the directory, and ends active.
4. `crash`: two writers in `/big/` and a new two-level index; the JVM halts
   (`Runtime.halt`) when the build has read a third of the directory.
5. `aftercrash`: the build resumes and ends active; every index agrees
   with the data that the crash left.
6. `v2`: version 2 of `Product` (field `name` renamed to `title`, `weight`
   removed, `price` from `long` to `int`, `supplier` with an initial value
   and `discontinued` added) reads version 1's data, rewrites 3,000 old
   products, writes 1,000 new ones and an index of `supplier`; a second
   class, `Bundle`, puts objects with other kinds under the same field
   names in the same directory.
7. `v1again`: version 1 reads what version 2 wrote.

**How it uses BergDB.** Data Objects `Product` (sku, name, category,
price as `long`, weight as `double`, tags as `String[]`), `Stock`,
`Movement` and `Bundle`. Writes through `put`, `w()` and `rw()`; the
movements are written by four threads in `rw()` transactions that read and
update a stock level, with `/mov/m${transactionTime}` keys. Indexes:
`by-cat` (string), `by-price` (long), `by-weight` (double),
`by-cat-price` (string, long), `by-name`, `by-cat-weight` (string,
double), `by-supplier`, `mov-by-sku` (string, long), `big-by-price` and
`big-by-cat-weight`. Queries: `eq()` on one or two levels, `from()` and
`to()` inclusive or not, `prefix()`, `backward()`, as `kvs()` and
`objects()`, as `DbObject` and as the application's classes; lookups at
earlier times, `freezeLookupTime()`, `usePrimary()`.

**How it checks itself.** Every index query is compared with an oracle:
the index function of `IndexBuilder`'s Javadoc applied in memory to the
documents (absent field or another kind: no entry; NaN: none; -0.0 as 0.0;
levels over 4,096 bytes: none; strings in code point order; then the keys),
filtered and ordered for the query. The documents come from the
application's own model of what it wrote (kept in a file between runs), or,
where writers run or a crash lost writes, from the primary scan at the same
frozen lookup time. 400 to 2,100 queries a phase, about 6,000 in a run,
random and fixed (level-1 values both ways, full scans, the double and
long edges, empty ranges, prefixes). Every stored object is compared
exactly with the model, field by field. The stock levels are checked
against the sum of their movements, through the index and through the
primary scan. A run makes about 1.2 million checks; `main` exits non-zero on a wrong result. The
last run, `run3.txt` beside the code: `APP OK (331 s)`.

**Size.** 2,400 lines of Java in 14 files and `run.sh`, in
`/Users/f/fl/bench/2026-11-09/app-u2/app/`; a run takes about 5 minutes on
F53 under a load of about 25.


## 2. The findings

No wrong result, no throw from legal use and no hang in BergDB: every query
of every phase agreed with the oracle, also across the crash in a build.
The findings are of the documentation and the API.

| ID | Kind | Severity | What | Reproduction |
|----|------|----------|------|--------------|
| I-1 | doc | medium | A double read into an integer field is cut toward zero, not rounded | 2.1 |
| I-2 | API | medium | A DbObject cannot list its fields' names                            | 2.2 |
| I-3 | API | medium | No way to list the indexes or read an index's definition            | 2.3 |
| I-4 | doc | low    | A get into a newer class and a put back drop fields, silently       | 2.4 |
| I-5 | API | low    | An rw() transaction cannot read through an index                    | 2.5 |
| I-6 | doc | low    | Key replace in rw() and the replaced text are not documented        | 2.6 |
| I-7 | API | low    | DbObject.Builder and DbArray lack double, boolean, String[] cases   | 2.7 |
| I-8 | doc | low    | Index scans: the key order of equal levels, prefix(""), not said    | 2.8 |

### 2.1. I-1: a double into an integer field is cut toward zero

The package's "Objects" says of a get: "a value that fits the field's type
is set exactly, else the nearest value (an integer clamped, never wrapped;
...)"; `DbObject.toJavaObject` says "the nearest value where it does not
fit", and `releases/next.md` "else the nearest value (integers clamped)". A
stored double 12.7 read into an `int` or a `long` field gives 12, and
-12.7 gives -12: Java's `(long) x`, toward zero, then clamped. That is
020-09's decision (section 5.4, "`(long) x` (toward zero, NaN 0,
saturated), clamped"), so the code is as designed and the Javadoc is wrong:
a user who changes a field from `double` to `long`, as a price in units to
a price in cents, expects 12.7 to read as 13. The same holds for a text
with a fraction ("1.5" is 1). Fix: say "a double into an integer field:
toward zero, as Java's cast, then clamped" where "nearest value" is
written, or round (a change of 020-09).

    public class A { public double price = 12.7; }      // put at /x/a
    public class B { public int price; }                // get /x/a as B: price 12

### 2.2. I-2: a DbObject cannot list its fields' names

`DbObject` has `getFieldCount()`, `has(name, type)`, `getType(name)` and
the typed getters, all by name. The Javadoc says "To read a stored object
exactly as it is, get it as a DbObject", but a program that does not know
the names cannot read it: a dump or an export, a migration that copies the
fields it does not know, a generic tool. The application's oracle reads a
`DbObject` through a list of every name its classes ever had and compares
the count with `getFieldCount()` to see that none is missed. An iterator of
the fields (name, type) or `getFieldNames()` would close the gap.

### 2.3. I-3: no way to list the indexes or read a definition

`Database` has `indexBuilder()`, `deleteIndex()` and `indexJob()` only. An
application cannot ask which indexes exist, nor what an index's directory
and levels are. At its start it can only try `indexJob(name)`
(`NoSuchIndexException`) or `start()` (`IndexAlreadyExistsException`). So an
application whose index definition changed between versions cannot see
that the stored index is the old one: in `load`, `by-price` was made with
one level, deleted and made again with two (`price`, `sku`); the next
version of the code would get the scans' grammar of whatever is stored,
and an `IllegalStateException` from `eq().eq()` if the old definition is
there. Workaround: a version in the index's name (`by-price-v2`) and the
old names to delete in the code.

### 2.4. I-4: a get into a newer class and a put back drop fields

Version 2 of `Product` reads version 1's objects as documented: `title` is
null (the stored field is `name`), `supplier` is "unknown" (its initial
value), the stored `weight` is ignored, a price outside `int`'s range is
clamped. Put back, the object has lost `name` and `weight`, and the four
edge products' prices are clamped for good (`Long.MAX_VALUE` stored as
2,147,483,647): the objects silently leave `by-name` and `by-weight`. Each
step follows the rules ("a stored field that the class does not have is
left out"), but the Javadoc does not say what the combination does, the
common read-modify-write of an application that has changed its class.
A sentence in "Objects" would help; a rename has no support (no alias).

### 2.5. I-5: an rw() transaction cannot read through an index

`RwEnvironment` has `get()` and `exists()` only. A rule such as "a product
name is unique" or "ship from the cheapest product of a category" needs a
scan inside the transaction, so that a concurrent change of the result
makes it run again. A scan outside `rw()` is not part of its conflict
check. The application keeps to rules on known keys (a stock level at
`/stock/SKU`). Perhaps by design; worth a sentence in `RwEnvironment`.

### 2.6. I-6: key replace in rw() and the replaced text

The movements are written in `rw()` at `/mov/m${transactionTime}` with key
replace on, and each got a key of its own (a probe in `/probe/` first got
`/probe/m017942262024060000`).
`setEnableKeyReplace` says "in the key of a put"; `RwEnvironment.put` and
`WBuilder.put` do not mention it, so whether `rw()` replaces had to be
tried. The replaced text, the transaction's time in clock units as 18
decimal digits with leading zeros, is not documented either; an
application that parses or orders the keys needs it (the zeros keep the
keys in time order).

### 2.7. I-7: missing cases in DbObject.Builder and DbArray

`DbObject.Builder` has `addInt`, `addLong`, `addString`, `addObject` and
`addArray`, but no `addDouble`, `addBoolean` or `addByteArray`: they go
through `addDbValue(name, new DbDouble(x))`. `DbArray` has `toIntArray`,
`toLongArray` and `toDoubleArray`, but no `toStringArray`: the
application's `tags` is read from a `DbObject` by iterating the `DbValue`s
and casting each to `DbString`.

### 2.8. I-8: index scans, two points not stated

`UseIndexBuilder` says that a scan gives the values "in the order of the
index's levels, then their keys", but not the keys' order;
`UsePrimaryBuilder` says it (the names' UTF-8 bytes), and the index scans
follow it, as the oracle checked. `prefix("")` is not mentioned; it lists
every entry of the level, which is what a user would expect.


## 3. What went well

* Every query agreed with the oracle, about 6,000 queries in a run of 1.2
  million checks: equality, ranges with every inclusive combination,
  prefixes, backward, two levels, empty ranges, the edges of the index
  function (-0.0 and 0.0 one key, NaN no entry, ±infinity at the ends,
  `Long.MIN_VALUE` and `Long.MAX_VALUE`, an absent field, a category of
  5,000 chars, the empty string, code point order where UTF-16 order
  differs: U+FF5E before U+1F600).
* Indexes follow every write: categories moved in `rw()`, prices in `w()`,
  two products swapped in one transaction, deletes, a `String` and a
  `byte[]` over an object and the object back, several writes to one key
  in one `w()` or `rw()`, objects of another class with other kinds under
  the same names (no entry, as documented).
* Builds over existing data while four writers write: the index agreed with
  the primary scan at twelve frozen times during the writes and with the
  writers' own models after them.
* A build interrupted by `close()` resumed at the next start (BUILDING,
  `useIndex()` refused meanwhile with `NoSuchIndexException`, "The index
  'big-by-price' is building at the lookup time."), with a
  writer in the directory, and ended active; so did one interrupted by a
  halt of the JVM, the writers' last writes lost and the indexes agreeing
  with what the crash left. The start after the crash took 4 s.
* Delete and make again: `NoSuchIndexException` at once after
  `deleteIndex()`; a scan at a lookup time before the deletion still reads
  the old index, also when the name has a new definition with two levels;
  a scan that runs across the deletion of its index goes on at its time; a
  deletion during a build ends it FAILED with the reason "deleted", and
  `join()` throws `IndexBuildException` at every call.
* Objects: `get` as the class, as `DbObject` and as `Object`,
  `toJavaObject`, `toDbObject` (the stored bytes exactly), the exact put
  (-0.0, NaN, the infinities, empty and absent arrays), and the class
  changes in both directions: every conversion as documented (by name,
  absent fields, clamped integers, a number written as a text and a text
  read as a number), except I-1's.
* Stock: about 830 movements from four threads in conflicting `rw()`
  transactions; every level equals the sum of its movements, through the
  index and through the primary scan, in every phase.
* The Javadoc was enough to write all of it: the grammar of the scans,
  the index function and the job's states are precise, and each of the 29
  documented refusals that the application tries (the scan's grammar, the
  builder's, the deletions', the put's) threw what the Javadoc says.
* Speed, on F53 under a load of 15 to 25: four builds of 30,000 values in
  about 2 s; a resumed build of 300,000 values in about 16 s while a writer
  made 250,000 puts there; an index scan at 2.4 to 6.8 µs a value; a start
  of the 1.4 GB database in about 2.5 s, and 4.2 s after the crash.


## 4. Fixes

By coord-1109's fixer x24, 2026-11-09, in the clone
`/Users/f/fl/bench/2026-11-09/clone-x24` rebased on `main` at `ec8d16f`, under Frans's rule for
2026.4 (2026-11-09): fix faults against today's specs and Javadoc, make the Javadoc true
where the code is as designed, no new API and no change of meaning. Each commit below has
its tests in `PubTesterJavadoc` and a line in `releases/next.md`, Documentation; JAVADOC
PUB OK. The gate under the lock, on the clone's tip `ed23b80`: BEFORE COMMIT OK (187 s, unit
1535, f 86, demos; `/Users/f/fl/bench/2026-11-09/x24-gate2.txt`).

* I-1 and I-4: `4340ea6`. The package's "Objects", `DbObject.toJavaObject()`,
  `releases/next.md` and docs/levels.md say that a double, or a text with a fraction, read
  into an integer field is cut toward zero, then clamped (12.7 is 12), as 020-09, section
  5.4 decided; "Objects" says what a get into a class and a put back store: the put drops
  the stored fields that the class lacks, keeps a converted value as converted, and the
  object leaves the indexes of the fields it lost. Test `testGetIntoANewerClass`.
* I-6: `00523e0`, with 020-24-01's U1-3: `setEnableKeyReplace()`, `WBuilder.put()` and
  `RwEnvironment.put()` say that the puts of `w()` and `rw()` are replaced, and the text.
  Test `testKeyReplaceText`.
* I-8: `ed23b80`. `UseIndexBuilder` says that the keys of equal levels are in the order of
  their names' UTF-8 bytes, as the primary scan's, and that `prefix("")` (or an empty
  `byte[]`) takes every value of the level. Test `testIndexKeyOrderAndEmptyPrefix`.
* For Frans: rounding a double into an integer field, in place of I-1's cut, would change
  020-09. I-2, I-3, I-5 and I-7 are API, not changed.
