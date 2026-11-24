# 026-02. A public key check: options and a recommendation

Created 2026-11-12 by Frans Lundberg. Status: done (2026-11-13): on
`main` since `6e27cf17`, the merge of `026-02-limits`; QK1 to QK4
(Frans, 09:11), Q9-1 (09:29) and D3 (09:32) decided.

Frans, 2026-11-12, 09:34: "Add a todo item for public key-checking. There
are some options. [...] Investigate the options and recommend an
implementation. No need to implement it. This can be done for next
release."

The background is 024-27, QR1 (decided 09:34): an `rw()` action that
catches a refused `env.put()` and returns normally commits its other
writes, and stays so; since 024-27 a refused call spoils a `WBuilder` and
a Core `Trans.Builder`. Either way a user who wants to handle a key that
is too long (skip it, shorten it, use another key) cannot ask in advance
whether a key fits: the Pub API has no public check, and the rule is
subtle (024-26, U26-3). First a study, no product code, made by the
agent "keychk" of coord-1112 (sections 1 to 8). Cite the options as "026-02, option A", the
questions as "026-02, QK1".

Implemented on 2026-11-13 by the agent "keys" of coord-1113, after
Frans's answers of 09:11 (section 8): option A without A2, for 2026.6
(section 9). Cite its decisions as "026-02, D1".


## 1. In short

Written 09:40 (2026-11-12), as the study's recommendation. Implemented
2026-11-13 as decided (section 8): `Limits` with the six constants,
`keyBytes` and `checkKey`; no `levelBytes` (QK3), no `isKey` (QK2), no
`Connection.checkPut`. Section 9 has what was made, section 10 the state.

* **Recommended: option A with A2**, a small final class
  `bergdb.pub.Limits` in the Pub API: the six limits as constants, and
  three static methods, `keyBytes(String key)` (a key's bytes as stored),
  `checkKey(String key)` (throws the very `IllegalArgumentException` that
  a put or a delete throws for the key) and `levelBytes(Object level)`
  (one level's bytes in an index entry, for L6). No database, no
  connection: the key rule depends on the key alone.
* **One source of truth**: put, delete and `checkKey` call one method of
  `pubimp`; a property test compares `keyBytes` and `checkKey` with what
  a put on a memory database does, for random and boundary keys.
* **Not recommended**: a `tryPut` (option B), a builder's remaining room
  (option C, not knowable before the commit when objects are indexed), a
  dry-run put on a connection (option D, later if asked), and a doc-only
  answer (option F; the rule is too subtle to leave to each user).
* **The Core API** (option E) needs no new method: a byte[] key's
  stored size is its length, and `Db.MAX_KEY_BYTES` is public; one
  sentence in Db's Limits says so. The C clone (022) is not concerned.
* **Size**: about 1 day: half a day for the code and tests, a quarter for
  the Javadoc, the rest for a gate (before-commit.sh) and a review.
* **Questions**: QK1 to QK4 (section 8): the class's name and place,
  a boolean check beside the throwing one, `levelBytes` now or later,
  and whether 2026.5 takes it after all.


## 2. What refuses today

Read 09:35 to 09:38 on main `78a24cd5`.

| Limit | Refused by | When | Exception |
|---|---|---|---|
| L2 key, Pub | `RwEnvironmentImp.checkKeyBytes` | at put, delete | IAE |
| L2 key, Core | `Trans.Builder.checkKeyBytes` | at the call | IAE |
| L2, key replace, Core | `Db.transformKeys` | at execute | DbException |
| L4 value | `checkValueBytes`, `Trans.Builder.checkValue` | at the call | IAE |
| L6 levels | `IndexDefinition.entryForPut` | at the commit | IAE |
| L1, L3, L5 | `Db.checkLimits` (from `checkSize`) | at execute | DbException |

IAE: IllegalArgumentException.

* **L2 in the Pub API.** `PubKeys.u2i(ukey)` makes the ikey ("/a/b" is
  "/da/-b": a byte after each '/') and refuses a bad form (null, empty,
  no leading '/', a trailing '/', "//", a lone surrogate); then
  `checkKeyBytes(ukey, ikey)` refuses an ikey whose UTF-8 has more than
  111 bytes. The bkey is the ikey's UTF-8 with each byte shifted
  (`dag.Keys.toBytes`), so the ikey's UTF-8 size is the stored size
  exactly; U+0000 and U+0001 are one byte in a key (two only in an index
  level). Key replace keeps a key's length ("${transactionTime}" is 18
  chars, the time 18 digits), so the key as written is checked.
* **Also key-related at a put**: `checkReplaceInDirectory` refuses
  "${transactionTime}" in an object key's directory when key replace is
  on (020-14, X1), and an object at a key with a suffix is refused. Both
  depend on the connection's setting or the value, not on the key alone.
* **L6** is refused at the commit, for the indexes active on the
  directory then (`RwEnvironmentImp.indexEntries`): in an `rw()` after
  the action returned, in a `w()` at `execute()`. A string level takes
  its UTF-8, one byte more for each U+0000 and U+0001, and a terminating
  byte; a bytes level likewise (`IndexKeys.escapedLength`); a long or a
  double 8 bytes; the levels of an entry at most 111 bytes in all.
* **L1, L3, L5** are counted on the Core transaction, after the Pub API
  has added the index entries: an object at a directory with k indexes
  costs 1 to 1 + 2k operations, by its old value (024-26, U26-7).
* **A `get()` or `exists()`** of a key over 111 bytes returns null or
  false (U26-6): it does not tell a user that a put would be refused.


## 3. What a user needs

1. Before a put or a delete, to know whether the key is accepted, and if
   not, how far over it is (to shorten it, or to pick a hashed key).
2. To know it without a database or a connection: keys are often made
   in code far from the transaction, and validated at input.
3. The same answer that the put gives, in this release and later ones
   (the limits may be raised, never lowered: 024-17, 6.3).
4. For an indexed directory, the same for the levels of an object (L6),
   which a user meets less often but with a subtler rule (U26-3).
5. In a `w()`, not to spoil the builder; in an `rw()`, not to rely on
   catching an `IllegalArgumentException` that may mean several things
   (a bad form, a long key, a null object, an object at a suffix key).


## 4. The options

### 4.1 Option A: a static check in the Pub API

```java
public final class Limits {                 // bergdb.pub
    public static final int MAX_KEY_BYTES = Db.MAX_KEY_BYTES;          // 111, L2
    public static final int MAX_VALUE_BYTES = Db.MAX_VALUE_BYTES;      // 8 MiB, L4
    public static final int MAX_OPERATIONS = Db.MAX_OPERATIONS;        // 500, L1
    public static final int MAX_TRANS_KEY_BYTES = Db.MAX_TRANS_KEY_BYTES;  // 56 KiB, L3
    public static final long MAX_TRANS_BYTES = Db.MAX_TRANS_BYTES;     // 32 MiB, L5
    public static final int MAX_LEVEL_BYTES = Db.MAX_KEY_BYTES;        // 111, L6

    /** The key's bytes as stored; IllegalArgumentException if not a valid key. */
    public static int keyBytes(String key) { ... }

    /** Throws the IllegalArgumentException that put() or delete() throws for the key. */
    public static void checkKey(String key) { ... }
}
```

What the user writes:

```java
String key = "/files/" + name;
if (Limits.keyBytes(key) > Limits.MAX_KEY_BYTES) {
    key = "/files/#" + sha256Hex(name);     // a key that always fits
}
b.put(key, data);
```

* **Where.** A class of its own, `Limits`, named as the package's
  section "Limits", so the Javadoc of each constant is the rule and the
  package's section links to it. Alternatives: static methods on the
  `Connection` interface (Java 17 allows them; discoverable, but a
  connection is a per-thread object, and the check needs none); a class
  `Keys` (clashes in name with `bergdb.dag.Keys`, which `pubimp` imports
  widely); `Factory` (it starts databases, not this).
* **Which arguments.** The key alone, as put and delete check it. Not
  key and value: L4 for a byte[] or a String is plain for the user, and
  an object's stored size needs its serialization (option D).
* **keyBytes and checkKey.** `keyBytes` answers "how far over", which
  shortening needs; it throws for a key of a bad form, whatever its
  length, so its answer is the stored size of a key that can be stored.
  `checkKey` throws exactly what put and delete throw for the key: the
  same message, so a user's log shows the same text either way. A
  boolean `isKey(String)` is easy to add (QK2); left out to keep one way.
* **Scope, said in the Javadoc**: the key's form and L2. A put may still
  refuse the call for its value, an object at a key with a suffix, or
  "${transactionTime}" in an object key's directory with key replace on.
* **Constants.** Today a Pub user meets the limits only as numbers in
  the package's Javadoc, or through the Core's `Db`, which the Pub API
  does not ask a user to read. They are compile-time constants, inlined
  in user code; that is safe, as a later release only raises a limit.
* **Keeping in step.** One method in `pubimp`, say
  `PubKeys.checkedIkey(String ukey)`, does `u2i` and `checkKeyBytes`;
  `RwEnvironmentImp.put` and `delete` call it, and so do `checkKey` and
  `keyBytes`. The constants are `Db`'s, by reference.
* **Test.** A property test: for random keys (ASCII, two-, three- and
  four-byte UTF-8, U+0000, many '/', the 110 to 112 byte boundary, a bad
  form, "${transactionTime}" with key replace on and off), `checkKey`
  throws if and only if a put on a memory database throws, with the same
  message, and `keyBytes` equals the bkey's length that the put stored
  (`Keys.toBytes(ikey).length`, read back by a scan of the Core).
* **C clone (022).** No: it is the Core in C, without the Pub API.

### 4.2 Option A2: an index level's size (L6)

```java
    /** A level's bytes in an index entry: Long, Integer, Double 8; a String, a byte[] ... */
    public static int levelBytes(Object level) { ... }
```

The user sums the levels of an index, which he defined, and compares
with `MAX_LEVEL_BYTES`. It is the U26-3 rule as code: the two-byte
U+0000, U+0001 and 0x00, 0x01, and the terminating byte. Static and
exact: the user knows his index's levels; the race of option D (an index
made between a check and the commit) does not arise, as the user asks
about an index he names. Kept in step by calling `IndexKeys.escapedLength`,
the product's counter, and tested against `IndexReference.encodedSize`,
the test oracle's independent one, for random levels, and against a put
of an object with those levels at the 111 and 112 byte boundary.

### 4.3 Option B: a "try" put

`boolean WBuilder.tryPut(String key, Object value)` and the same on
`RwEnvironment`: false, and nothing added and nothing spoiled, if the put
would be refused. What the user writes: `if (!b.tryPut(k, v)) { ... }`.

* It doubles the write calls of two interfaces (put and delete, on
  `WBuilder` and `RwEnvironment`), and answers only yes or no: a user
  who shortens a key still needs the size (option A).
* A false hides which rule refused: a bad form is a bug in the caller,
  a long key a case to handle. A result object fixes that at more API.
* It cannot cover L6 or L1, L3, L5, which are refused at the commit.
* Kept in step for free (it runs the put), tested as the put. Not
  recommended: option A gives the same with less API and more answer.

### 4.4 Option C: a builder's remaining room (L1, L3, L5)

`int WBuilder.operations()` or `remainingOperations()`, and the same
for key bytes and bytes.

* Exact only for plain values. An object put at an indexed directory
  costs 1 to 1 + 2k operations and some key bytes by its old value and
  the indexes active at the commit (`indexEntries`), known only then; a
  builder's count before it would be a lower bound, and a user who fills
  a builder to it may still be refused, so the promise would be weak.
* For plain values the user counts himself: one operation a key (the
  last call on a key wins), a key's `keyBytes`, a value's length. The
  package's Limits says so today, with 500 and 166 as examples.
* Not recommended. If wanted later, `Transaction` could report what a
  committed transaction took, which is exact (an item of its own).

### 4.5 Option D: a dry run on a connection

`void Connection.checkPut(String key, Object value)`: every check of a
put without the write: the key, L4 on the stored value, the object rules,
and L6 for the directory's indexes active now.

* Covers what option A cannot: an object's stored size, and L6 without
  the user summing levels. Costs a serialization, as the put does.
* L6 is checked against the indexes of now; one made before the commit
  may still refuse (state, not a pure function; the Javadoc must say it).
* Kept in step if it runs the put's own code into a scratch environment
  (`RwEnvironmentImp.put` and `entryForPut`); about 1.5 to 2 days with
  tests. Not recommended now: A and A2 meet the need of section 3 at a
  fraction; D is a later item if users ask (QK3).

### 4.6 Option E: the Core API

* A byte[] key: its stored size is its length; a String key of
  `Trans.Builder.put(String, ...)`: its UTF-8 (no byte after '/', unlike
  the Pub API). `Db.MAX_KEY_BYTES` and the other limits are public.
* So no method: one sentence in Db's Limits, "a key fits if
  `key.length <= Db.MAX_KEY_BYTES`", and the Pub check is not built on
  a Core method (it is the ikey's UTF-8 size, a Pub rule).
* A key that a key transformation makes longer is refused at execute
  (DbException, `Db.transformKeys`); only BergDB's own transformations
  are in the Pub API, and they keep the length.
* C clone (022): its update to 2026.5 takes the limits; a check there
  would be the same comparison. Nothing for this item.

### 4.7 Option F: only document the rule

The package's Limits and Connection's "Keys" give the rule; add an
example ("/customers/12345678" is 21 bytes is there). Costs nothing to
keep, but each user writes the count himself, and U26-3 shows that a
careful reader (app 3 of 024-26) found the rule's edges by testing. The
example of option A goes into the Javadoc in any case.

### 4.8 Option G, a note: a subclass of the exception

A `KeyTooLongException extends IllegalArgumentException` would let an
`rw()` action catch only the long key. Compatible, but one class a limit,
and it helps only after the call; a `WBuilder` is spoiled by then. Not
recommended; option A answers before the call.


## 5. Comparison

| Option | Answers before the call | Gives the size | New API | Days |
|---|---|---|---|---|
| A, Limits.keyBytes, checkKey | yes, exact | yes | 1 class, 2 methods | 0.75 |
| A2, Limits.levelBytes | yes, exact for a named index | yes | 1 method | 0.25 |
| B, tryPut | no, it is the call | no | 4 methods | 0.5 |
| C, remaining room | a lower bound | partly | 3 methods | 1 |
| D, Connection.checkPut | yes, for the indexes of now | no | 1 method | 1.5 to 2 |
| E, Core | yes (length) | yes | none, 1 sentence | 0 |
| F, documents only | by hand | by hand | none | 0.1 |


## 6. Recommendation

Options A and A2, with E's sentence and F's example: `bergdb.pub.Limits`
with the six constants, `keyBytes`, `checkKey` and `levelBytes`. Each is
a pure function of its argument, exact in this release, and built on the
code that refuses, so it cannot drift without a failing test. It meets
section 3's needs 1 to 5 but the object's stored size (L4 for an object)
and L1, L3, L5, which a user meets far less often, and which depend on
the commit.


## 7. The plan

In a clone, on a branch `026-02-limits`; about 1 day.

1. **pubimp** (1 hour): `PubKeys.checkedIkey(String ukey)`, the form
   checks of `u2i` and L2 (`checkKeyBytes` moved from
   `RwEnvironmentImp` to `PubKeys`); `RwEnvironmentImp.put` and `delete`
   call it. `IndexKeys.levelBytes(Object)` from `escapedLength` and the
   8 of a number.
2. **bergdb/pub/Limits.java** (2 hours with its Javadoc): the constants,
   each with its rule from the package's Limits (L1 to L6) and its ID;
   `keyBytes`, `checkKey`, `levelBytes`; the example of section 4.1 and
   one for a level sum. A null argument is refused with
   `IllegalArgumentException` that names it (020-27, Q2).
3. **Javadoc** (1 hour): the package's Limits links each limit to its
   constant and says "Limits.checkKey() checks a key before a call";
   Connection's "Keys", `WBuilder` (a refused call spoils it: check
   first) and `RwEnvironment`'s "Refused calls" link to it; Db's Limits
   gets option E's sentence.
4. **Tests** (2 hours), in `PubTesterLongKeys` (no new tester to list):
   the property test of section 4.1 (a few thousand random keys, about a
   second); the boundary keys 111 and 112 bytes of each kind; a
   `levelBytes` test against `IndexReference.encodedSize` and a put of an
   object at 111 and 112 bytes of levels in an indexed directory; a
   constants test (`Limits.X == Db.X`).
5. **Release jar**: `stress/release-jar/ReleaseDemo.java` calls
   `Limits.checkKey` once, so that the jar check (`build.sh`, check 3)
   compiles user code against it.
6. **releases/next.md**: a line under the Pub API's additions.
7. **Gate**: `java/before-commit.sh` once on the head (a slot). No Lean
   change (the model has the Core's limits, not the Pub key rule), no
   level script, no performance run: the put's path gains no work (the
   same calls, moved into one method).

No changed expected value in an existing test is foreseen; the messages
of put and delete stay as they are.


## 8. Questions for Frans

* **QK1. The name and place.** `bergdb.pub.Limits` (recommended), static
  methods on `Connection`, or another class name?
  **Decided** (Frans, 2026-11-13, 09:11): `bergdb.pub.Limits`, as
  recommended: a small final class with the limits as public constants,
  by reference to Db's, `keyBytes(String key)` (a key's bytes as stored)
  and `checkKey(String key)` (throws the very `IllegalArgumentException`,
  same message, that a put or delete throws for the key).
* **QK2. A boolean too?** `Limits.isKey(String)` beside `checkKey` and
  `keyBytes`. Recommended: no, one way (`keyBytes(k) <= MAX_KEY_BYTES`).
  **Decided** (Frans, 2026-11-13, 09:11): no `isKey`, as recommended.
* **QK3. Levels now, the dry run later?** `levelBytes` (A2) with the key
  check, and `Connection.checkPut` (option D) only if users ask.
  Recommended: yes.
  **Decided** (Frans, 2026-11-13, 09:11): `levelBytes` is left out:
  "Leave it out. We can easy add it if requested."; no
  `Connection.checkPut` (option D) either. The Javadoc of `Limits` states
  L6's rule in words (a level's bytes in an index entry), so that a user
  can count without a method.
* **QK4. Which release?** 2026.6 as Frans said; it is about a day and
  touches no format, so 2026.5 could take it if its plan has room.
  Recommended: 2026.6, as said.
  **Decided** (Frans, 2026-11-13, 09:11): 2026.6.

Frans's answers came through the coordinator, coord-1113; the words of
QK3 are his.




## 9. The implementation

2026-11-13, 09:12 to 09:27, by "keys" of coord-1113, in a clone of main
`da0596a8`, branch `026-02-limits`. Section 7's plan without A2: no
`IndexKeys.levelBytes`, no `levelBytes` test.

### 9.1 What was made

* **`bergdb.pub.Limits`**, new: a final class with no instances. The
  constants `MAX_OPERATIONS` (L1), `MAX_KEY_BYTES` (L2),
  `MAX_TRANS_KEY_BYTES` (L3), `MAX_VALUE_BYTES` (L4), `MAX_TRANS_BYTES`
  (L5, a long) and `MAX_LEVEL_BYTES` (L6), each `= PubKeys.X`, which is
  `Db.X` (L6 is `IndexKeys.MAX_LEVEL_BYTES`, `Db.MAX_KEY_BYTES`), so
  compile-time constants (D3, revised); each with its rule and ID in its
  Javadoc. Two static methods:

  ```java
  public static long keyBytes(String key)   // a key's bytes as stored
  public static void checkKey(String key)   // throws what a put or delete throws
  ```

  The class Javadoc: why to check first (a refused call spoils a
  `WBuilder`; an `rw()` action that catches it commits its other
  writes), section 4.1's example, the scope (the key's form and L2; what
  a put may still refuse: the value, an object at a key with a suffix,
  X1 with key replace on), L6's rule in words (QK3), and L1, L3, L5 at
  the commit.
* **pubimp, one check** (section 4.1, "Keeping in step"):
  `PubKeys.checkedIkey(ukey)` is `u2i` and then `checkKeyBytes`, which
  moved here from `RwEnvironmentImp` unchanged but for its count;
  `RwEnvironmentImp.put` and `delete` call it in place of the two calls,
  and `Limits.checkKey` calls it. `PubKeys.keyBytes(ukey)` is
  `storedBytes(u2i(ukey))`, and `checkKeyBytes` counts with the same
  `storedBytes` (the ikey's UTF-8). The put's path has the same calls
  in the same order: no new work.
* **Javadoc**: the package's Limits says `Limits` has the limits and
  checks a key, and each item names its constant; Connection's "Keys",
  `WBuilder`'s paragraph on a refused call and `RwEnvironment`'s
  "Refused calls" point to `checkKey` and `keyBytes`; Db's Limits has
  option E's sentence (a Core key fits if its bytes, a byte[]'s length or
  a String's UTF-8, are at most `MAX_KEY_BYTES`; no method).
  `javadoc-pub.sh` passes.
* **pub's dependencies as before**: common, nanotest, pub.util and
  pubimp; the constants come through pubimp's `PubKeys` (D3, revised).
* **ReleaseDemo** (`build.sh`, check 3) calls `Limits.checkKey` and
  `Limits.keyBytes` ("/fruit/apple" is 14 bytes, "/" and 110 letters
  112), so user code is compiled against the release jar's `Limits`.
* **releases/next.md**: an entry under a new heading "Pub API", before
  026-06's under "Core API".

### 9.2 Decisions made here

* **D1. `keyBytes` returns a long**, not the int of section 4.1's sketch:
  exact for every String, as `StringUtil.utf8Size` is a long; a key of
  more than 716 million three-byte characters passes 2^31 - 1 bytes, and
  an int would need a clamp. `keyBytes(k) > Limits.MAX_KEY_BYTES` reads
  the same. Question Q9-1 below.
* **D2. `keyBytes` does not call `checkedIkey`**: it answers for a key
  over L2 too ("how far over"), which `checkedIkey` refuses. It runs the
  same two parts, `u2i` for the form and `storedBytes` for the count;
  the property test checks that `keyBytes` is over 111 exactly when
  `checkKey` throws L2's message, and that both give the same message
  for a bad form.
* **D3. The constants come through pubimp; pub does not depend on
  core.** First built with `Limits.X = Db.X` and core added to pub's
  package.html list, which `deps.py` checks (`a06e0de6`). Frans,
  2026-11-13, on that: "Tell me why it is needed and how it was avoided
  before", and at 09:32 "Yes" to option 1, to avoid the new package
  dependency through pubimp (through the coordinator, coord-1113). So
  since `aecd641f`: `PubKeys.MAX_OPERATIONS` and the four other limits
  are `Db`'s, `PubKeys.MAX_LEVEL_BYTES` is `IndexKeys.MAX_LEVEL_BYTES`
  (the index code's L6, package-private), all compile-time constants, and
  `Limits.X = PubKeys.X`; pub's package.html is as before, as pub
  reaches pubimp already (Factory, Time, DbObject). `deps.py` passes.
* **D4. No null check of its own**: `checkKey(null)` and `keyBytes(null)`
  throw what a put of null throws, "null is not a valid key.", which
  names it (020-27, Q2), so that the message is the put's.

### 9.3 Tests

In `PubTesterLongKeys` (no new tester to list), unit group:

* **`testLimitsConstants`**: each constant equals `Db`'s
  (`MAX_LEVEL_BYTES` is `Db.MAX_KEY_BYTES`), L2 is 111, and the
  package's example "/customers/12345678" is 21 bytes.
* **`testLimitsMatchPut`**, the property test of section 4.1, about
  0.2 s, seed fixed (2602). Keys: 16 boundary keys, 111 and 112 bytes of
  each kind (ASCII; many '/', "/a" 37 times; å, two bytes; 中, three; an
  emoji, four; U+0000; "${transactionTime}" in a directory and in a
  name), whose sizes the test asserts by the rule in words (UTF-8 and one
  for each '/'); 19 keys of a bad form (null, "", "/", no leading '/',
  "//", a trailing '/', lone surrogates, some of them over 200
  characters); 600 random keys, of pieces of 1 to 4 bytes of UTF-8,
  U+0000, U+0001, '.', "${transactionTime}", with few or many '/', a
  suffix ".txt" or ".obj" one time in four, a stored size of 100 to 117
  bytes two times in three, else 2 to 160, and a bad form one time in 12.
  Each key with key replace off and on, on a memory database:
  * `checkKey`'s message, or none, is that of `Connection.delete`,
    `w().delete().execute()` and `Connection.put` of a byte[];
  * `keyBytes` throws `checkKey`'s message for a bad form; else it is the
    rule's count, and over 111 exactly when `checkKey` throws L2's;
  * a put that is taken stores one new key in the Core (a `getMany` of the
    latest state, without the keys at the start), and its bkey has
    `keyBytes` bytes; it differs from the key's own bkey exactly when key
    replace is on and the key holds "${transactionTime}". The Core then
    deletes it;
  * X1 (key replace on, "${transactionTime}" in an object key's
    directory; 020-14) is the one other refusal of such a put: `checkKey`
    takes the key, the put refuses it with X1's message;
  * each outcome, taken, too long, bad form and X1, comes more than 20
    times (asserted).
* A mutation, `checkKey` with `u2i` only, fails the test at the first
  key of 112 bytes.
* No expected value of an existing test changed; the messages of put and
  delete are as before.

### 9.4 Gates

On the code's commit `a06e0de6`, one slot each (heavy2), one after the
other:

* **`java/before-commit.sh`**: BEFORE COMMIT OK (66 s), 09:21 to 09:22:
  unit 1706 tests, f-tests 89, demos 14 runs; deps.py and doubles.py
  pass. Log: `/Users/f/fl/bench/2026-11-13/keys/before-commit.txt`, the
  script's logs in `keys/before-commit-logs/`.
* **`java/stress/level1.sh`**: LEVEL 1 OK, 09:22:36 to 09:25:06. Log:
  `/Users/f/fl/bench/2026-11-13/keys/level1.txt`.
* **`java/javadoc-pub.sh`**: JAVADOC PUB OK (doclint on the new class
  and links).

Again on `aecd641f` (D3 revised, after the coordinator's merge of main,
`aa76d437`), one slot (heavy), 09:34 to 09:35:
`java/before-commit.sh` BEFORE COMMIT OK (63 s; deps.py: 9 packages as
their package.html allows) and `java/javadoc-pub.sh` JAVADOC PUB OK.
Log: `/Users/f/fl/bench/2026-11-13/keys/gates2.txt`. Level 1 was not run
again: the change moves six constants, with the same values.

No level script beyond level 1, no performance run, no Lean change: the
put's path has the same calls (section 7, step 7).

### 9.5 Questions for Frans

* **Q9-1. `keyBytes` a long or an int?** **Decided** (Frans,
  2026-11-13, 09:29): a long, as built ("Yes"). A long (D1), exact for any
  String; an int as in section 4.1's sketch reads a little simpler in
  user code (`int n = Limits.keyBytes(k)`), with a clamp at
  `Integer.MAX_VALUE` for keys of more than 2 GB as stored. Recommended:
  the long, as built.


## 10. State

2026-11-13, 09:36, by "keys" of coord-1113.

* **Ready to land.** Branch `026-02-limits` in
  `/Users/f/fl/bench/2026-11-13/keys/clone`: the code `a06e0de6`, the
  items `f701338e`, the coordinator's merge of main `aa76d437`, D3
  revised `aecd641f` (gated, section 9.4), then one commit of items only
  (this file). The commits are in Frans's name; the coordinator lands
  them.
* **Done:** sections 9.1 to 9.4, as decided in section 8; Q9-1 and D3
  decided by Frans (09:29, 09:32); the entry in `releases/next.md`.
* **Open:** nothing.
* **To continue** if main moves before landing: merge main into the
  branch, run `java/before-commit.sh` again (one slot).
* The study's state of 2026-11-12 (written 09:40 by "keychk"): the
  study, the recommendation and the plan, no code; done.

2026-11-24. Status set after the release (lead-1124).
