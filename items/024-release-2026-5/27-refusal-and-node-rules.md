# 024-27. Refused calls, theta's floor and the largest node size

Created 2026-11-12 by Frans Lundberg. Status: done (2026-11-12): on
`main` since `a7dfb6f7`, QR1's Javadoc since `10408f2b`; QR1 and QR2
decided.

Four decisions of Frans, 2026-11-12, 07:36, made in Java, Lean and the
documents, as one branch for the coordinator to land:

* **024-26, U26-5, option B**: "B. Ensure the behaviour is clear in the
  Javadoc." A refused call spoils the builder, the Pub API's `WBuilder`
  and the Core's `Trans.Builder` alike (section 2).
* **024-26, U26-1 to U26-4 and U26-8**: the Javadoc fixes as 024-26,
  section 4, describes them (section 3). U26-6 and U26-7 are notes only,
  left as they are.
* **024-19, Q4**: the floor of theta is 2, so 2 at B = 8; 3, 7 and 14 at
  14, 30 and 62 unchanged (section 4).
* **024-19, Q6 and Q1**: 62 is the largest node size; B = 30 stays the
  default and the Pub API's only size, "Document this." (section 5).

Made by the agent "rules" of coord-1112. Cite the decisions taken here as
"024-27, R1", the questions as "024-27, QR1".


## 1. In short

Written 08:14 (2026-11-12); section 9 has the exact state. Done.

* **R1, a spoiled builder.** A call of a `Trans.Builder` or a `WBuilder`
  that throws, as one refused with `IllegalArgumentException` for its
  arguments or a limit, adds nothing and spoils the builder: its
  `build()` (Core), `Db.execute(Trans.Builder)` and `WBuilder.execute()`
  throw `IllegalStateException` and write nothing, and so does every later
  call on it, at once. The message names the first refused call; its
  exception is the cause.
* **theta's floor 2**: `Dag.theta`, the Lean model's `Params.thetaFor` and
  `thetaFor_values`, `docs/levels.md`, releases/next.md, 024-02.
* **62 the largest node size**: `Dag.MAX_NODE_SIZE`; a `Dag` of a larger
  size is refused when it is made, and a meta block that gives one is
  refused at the start as damaged. The rule is in 024-02, section 6.
* **Changed tests**: six, each its own commit (section 6): testTheta's
  expected value, one test's transaction count, four tests that used a
  builder after a refusal.
* **Lean and the trace format**: neither covers the builder's refusals
  (section 2.6); nothing to change there for R1.


## 2. A refused call spoils the builder (024-26, U26-5)

### 2.1 Before

A `WBuilder` whose `put()` threw `IllegalArgumentException` (a key over
111 bytes, L2; a value over 8 MiB, L4; a bad key or object) went on: a
caller that caught the exception and called `execute()` committed the
other puts and deletes, against the package's "all of them, or none"
(024-26, U26-5, found by app 1's oracle). The Core's `Trans.Builder` did
the same: `build()` gave a transaction of the calls that were not
refused.

### 2.2 The rule (R1)

* **What**: a call on a builder that throws spoils it. The call has added
  nothing (each call checks all its arguments before it adds, as before).
  From then on `build()`, `Db.execute(Trans.Builder)` and
  `WBuilder.execute()` throw `IllegalStateException`, nothing is built or
  written, and every later call on the builder throws the same
  `IllegalStateException`.
* **When**: at the refused call (the builder keeps the first refused
  call's name and exception, in the fields `refusal` and `refusedCall`),
  and at every later call (`checkNotSpoiled`, the first statement of each
  public adding method and of `build()` / `execute()`).
* **By whom**: `Trans.Builder` (bergdb.core) for the Core API, and
  `WBuilderImp` (bergdb.pubimp) for the Pub API. Each public method's body
  runs in `try { ... } catch (RuntimeException | Error e) { spoil(...);
  throw e; }`, so that any exception spoils, not only the checks' own
  `IllegalArgumentException`s: one from `Keys.toBytes` (an empty key, a
  lone surrogate), from the Pub layer's object checks, or an
  `OutOfMemoryError` in the middle of an add. A call on a spent
  `WBuilder` (after `execute()`) still throws the spent message first,
  and does not spoil.
* **How it is checked**: `Trans.testRefusedCallSpoilsBuilder` (seven
  refusals: a long key in a put and in a delete, a value over 8 MiB, a
  null value, a negative hash, a negative read time, a null read key;
  for each, seven later calls including `build()` and `Db.execute(b)`
  throw `IllegalStateException` naming the refused call, its cause the
  refusal, nothing written; a `Trans` built before the refusal still
  runs; a new builder works), and `PubTester.testRefusedCallSpoilsWBuilder`
  (a long key in a put and in a delete, a null value; later `put()`,
  `delete()` and two `execute()`s throw, nothing written, a new builder
  works). The changed tests of section 6 check it too.

`Trans.Builder.build()` may still be called more than once on a builder
that was never refused, as before; a `Trans` it gave before a refusal is
not changed.

### 2.3 The exception: IllegalStateException

* It is what both builders already throw for "this builder cannot do
  that now": `WBuilder`'s spent builder (020-21, 2) and a builder that
  another thread holds (021-22). A spoiled builder is the same kind of
  state: the call is valid in itself, the builder is not.
* Not `IllegalArgumentException`: `execute()` has no argument, and a
  caller who catches `IllegalArgumentException` around a put to skip a
  bad key would catch this one too and go on, the very case R1 closes.
* Not `DbException`: nothing reached the database, and the Pub API's
  `DbException` means that the database refused a transaction (a limit at
  the commit, a stopping database); a spoiled builder never asks it.
* The message names the call and the first refused call, and gives the
  refusal's text, for example: "execute() on a spoiled builder: its
  put() was refused (java.lang.IllegalArgumentException: The key has 116
  bytes, ...), so the transaction would lack an operation; nothing of it
  is written. Get a new builder with Connection.w() (bergdb 024-26,
  U26-5)." The refusal is the cause, so a stack trace shows where it was
  thrown.

### 2.4 Later calls throw at once

Considered: (a) later calls are taken and only `execute()` throws; (b)
later calls throw too. Chosen (b), because

* the caller learns at the next call, next to the cause, not at the end
  of a loop that may have built 499 more operations for nothing;
* nothing is added to a transaction that can never be built, so there is
  no state of a spoiled builder to describe beyond "spoiled";
* it is how a spent `WBuilder` behaves already: every later call throws
  `IllegalStateException`. One rule for "a builder that cannot go on".

The cost: a caller that catches `IllegalArgumentException` from a put
and goes on now gets `IllegalStateException` from the next call. That is
the point of R1; the Javadoc says it, and says to get a new builder.

### 2.5 Where it is said

* `Trans.Builder`'s class Javadoc, "A refused call spoils the builder";
  each refusing method's Throws ("The call adds nothing and spoils the
  builder", and `@throws IllegalStateException If the builder is
  spoiled`); `build()`'s Throws; `Db.execute(Trans.Builder)`'s Throws;
  `Db`'s "Limits" (L2: "which spoils the builder").
* `WBuilder`'s class Javadoc, "A refused put() or delete() spoils the
  builder"; `put()`'s and `delete()`'s Throws; `execute()`'s Throws;
  `WBuilderImp`'s class comment.
* The package's "Several writes at once" (after "all of them, or none")
  and its "Limits" ("A put() or delete() of a w() over one spoils its
  builder, whose execute() then writes nothing").
* releases/next.md, "Limits".

### 2.6 What R1 does not cover

* **The Lean model and the trace format**: neither has the builders'
  calls. The model's transactions are the operation lists that reach
  `Db.execute` (its `Trans.Builder.build` rule, the last operation on a
  key, in `SIS/Tree/Spec.lean` and `Props.lean`), and a trace's TX lines
  are executed transactions; a refused call or a spoiled builder makes no
  transaction, before and after R1. `Limits.release` (Bound.lean) bounds
  what a transaction may hold, not how a builder refuses. Nothing to
  change.
* **rw()**: an action that catches a refused `env.put()` and returns
  normally still commits its other writes (`RwEnvironmentImp` is not
  spoiled). Not in the decision; QR1.
* **`Connection.put()` and `delete()`** are one operation each: nothing
  else to commit.


## 3. The Javadoc of U26-1 to U26-4 and U26-8

* **U26-1** (`KeyTransformation.transform`): the stale "The new key is
  not size-checked: Db.checkSize counts the key before the
  transformation" replaced by what `Db.transformKeys` does since 024-24:
  a transformed key over 111 bytes (L2), or keys over L3, refuse the
  transaction with a `DbException`, nothing written. `trans.kvs[index].key`
  became "the key of trans.kvs[index] (Kv.setKey())", and
  `trans.transTime` became `trans.tt`.
* **U26-2** (`Trans.Builder`): `put(long[], byte[])`, `put(long[],
  KeyTransformation, byte[], ValueTransformation)`, `delete(byte[])`,
  `delete(long[])`, `delete(String)`, `put(String, String)` and
  `put(String, byte[])` list L2 (and L4 for the puts) under Throws.
  `keyRead()`: "Its length is not checked: Db.MAX_KEY_BYTES (L2) is a
  limit of the keys a transaction writes, and a read key is only a hash."
* **U26-3** (the package's "Limits"): a string level takes its UTF-8 and
  a byte, "but the characters U+0000 and U+0001 two bytes each"; a bytes
  level "its bytes and a byte, but the bytes 0x00 and 0x01 two each (so
  one bytes level holds at most 110 bytes, or 55 zero bytes)", as
  `IndexKeys`' encoding E escapes 00 and 01.
* **U26-4**: "A delete is an operation whether its key has a value or
  not" in the package's "Limits"; in `Db`'s "Limits" (L1) "a delete
  counts whether its key has a value or not, though one of a key without
  a value stores nothing (getTrans())"; in `Trans.Builder.delete(byte[])`
  the same.
* **U26-8** (`DatabaseBuilder.start()`, Throws `DbException`): "a
  VersioningStreamException if a release before 2026.5 wrote the database
  (record format 6 of 2026.4, 5 of 2026.1 to 2026.3): this release does
  not open it, the message names the release that does, and the start, as
  create() on its directory, changes no file".


## 4. theta at least 2 (024-19, Q4)

* **Java**: `Dag.theta(b)` is `max(THETA_MIN, 7 b / 30)` from b = 8, with
  `THETA_MIN = 2` (was `max(1, ...)`); its Javadoc says why (024-19,
  section 4.5: theta 1 at 8 compacted at every second dead klong and
  cost 25 percent of the bytes a put).
* **Lean**: `Params.thetaFor M = if M < 8 then 0 else max 2 (7 * M / 30)`
  (`SIS/Tree/Node.lean`); `thetaFor_values` now states 2 at 8, and
  `thetaFor_pos` 2 ≤ theta from 8 (`DeadProps.lean`); `TreeTest.lean`'s
  comment of `runThetaSet` (8, 10 and 12 all theta 2 now). A trace's TREE
  line carries theta from Java (`Dag.theta`), so `treecheck` takes it
  from the trace; no stored trace pins it.
* **Documents**: `docs/levels.md` (level 2, "at least 2"), releases/next.md
  ("2, 3 and 14 at 8, 14 and 62"), 024-02, section 6 (the rule, new).
* **Tests**: `DeadKlongTester.testTheta` (1 becomes 2 at 8), and
  `Eviction.testLoweredBudgetAfterPinsFell`, whose state at node size 8
  moved (section 6).
* **Not changed, for the coordinator** (items I may not write): 024-23
  states theta 1 at 8 in section 1 ("1, 3, 14 at 8, 14, 62"), 2.3, 3
  (`thetaFor_values`, "theta 1" at 8 in the runs), 4, 5 and its QO2
  (section 8); 024-23's review.md (lines 130, 240); 024-19, sections 3,
  4.5 and 5 (the measurements, which stay true of their build). These are
  records of what ran then; a line at 024-23's QO2, "Decided by 024-19,
  Q4 (2026-11-12): at least 2; made in 024-27", would close it. The C
  clone (012) follows release 2026.2, not main: nothing there.


## 5. 62 the largest node size (024-19, Q6), and B = 30 (Q1)

**What main allowed.** The Core API offers exactly 8, 14, 30 and 62
(`DbBuilder.maxNodeSize8()` to `maxNodeSize62()`; the field is
package-private, and no code in `java/` sets it otherwise), and the Pub
API always 30. But `Dag`'s public constructor and `Dag.createEmpty` took
any size: 024-19's measuring build ran 126 and 254 through them, and
`UnlinkFuzz` and `A2A3Check2` take `-Dmaxnode=N`. A start compared the
meta block's size with the builder's, so a block giving 126 was refused
with a message naming `DbBuilder.maxNodeSize126()`, which does not exist.

**Made (R2).**

* **What**: 62 is the largest node size, `Dag.MAX_NODE_SIZE`, because a
  delete bitmap names 62 klongs (`Klong.DELETE_BITS`, 024-02, 11.2).
* **When, by whom**: `Dag`'s constructor and `createEmpty` refuse a size
  above 62 with `IllegalArgumentException` ("The node size 63 is above
  62, the largest: a delete bitmap names 62 klongs of its node (bergdb
  024-19, Q6)"), before anything is made; `Db.refuseOtherNodeSize`
  refuses a meta block that gives a size above 62 with a
  `StreamFormatException` ("... above 62, the largest node size of
  BergDB ...: the block is damaged, or the stream is not BergDB's. The
  start has written nothing."), before any write.
* **How checked**: `DagTester.testNodeSizeAbove62Refused` (62 taken; 63,
  64 and 126 refused by both; `MAX_NODE_SIZE` equals
  `Klong.DELETE_BITS.length`), `DbTesterRestart.testNodeSizeAbove62Refused`
  (a block patched to 63 and 126, started with 30 and 62: refused, the
  stream unchanged). No size below 8 is refused: the Dag tests use 4 and
  6 on purpose.
* **Where written**: 024-02, section 6 (a paragraph "The node size" after
  the meta block's table, its row, "Checked on reading"; section 11.3's
  bound on n); `DbBuilder.maxNodeSize62()`'s Javadoc ("the largest").

**Q1, B = 30.** `DbBuilder`'s class Javadoc gave 30 as the default and
`maxNodeSize30()` "the default and the Pub API's"; now "the Pub API's
only size (bergdb 024-19, Q1)". `docs/levels.md` did not state the node
size: the new paragraph of 024-02, section 6, does; I did not add one to
levels.md, whose level 2 speaks of B only through the thresholds ("at
node size 30"). The Pub API's Javadoc has no node size (010-01: not a
setting of the Pub API), as it should.


## 6. Changed tests

Each its own commit on the branch, approved by Frans's decisions as the
brief says (the first two follow from Q4, the rest from U26-5):

| Commit     | Test                                               | Change                      |
|---|---|---|
| `33e0a97c` | `DeadKlongTester.testTheta`                        | theta at 8: 1 becomes 2     |
| `cedbcde3` | `Eviction.testLoweredBudgetAfterPinsFell`          | 520 transactions become 550 |
| `bc446d74` | `DbTesterJavadoc.testRangeArguments`               | a builder a refused call    |
| `bc446d74` | `DbTesterJavadoc.testTransBuilderNullArguments`    | a builder a refused call    |
| `ffe004ee` | `DbTesterLimits.testValueBytes`                    | its other put not written   |
| `cb5dab4a` | `PubTesterJavadocRest.testWBuilderOneTransaction`  | a builder a refused call    |

* **testLoweredBudgetAfterPinsFell** is not an expected value but its
  setup: 520 transactions at node size 8 reached its state (resident
  detachable bytes between the budget and P0) with theta 1, not with 2
  ("detachable objects resident: 3383 bytes, budget 3390"). Counts 480
  to 600 by tens: 550 and 600 reach it, the others not, a test sensitive
  to the tree's shape, as 024-23 found (500 to 520). 550 passed five
  runs of five. Frans may prefer a test that finds its count itself.
* **The four of U26-5** made their refused calls on one builder and then
  used it: each refused call now has a builder of its own, and the test
  checks that each such builder is spoiled (`build()` or `execute()`
  throws `IllegalStateException`, the refusal its cause). testValueBytes
  expected `/x`, put before the refused value, to be written; now it
  expects nothing written.


## 7. Gates

On the branch's head `40275fd7` (section 9), each once, in a slot of
its own (before-commit on `cb5dab4a`, the head but for releases/next.md):

| Gate                                  | When           | Result                              |
|---|---|---|
| `java/before-commit.sh`               | 07:52 to 07:53 | BEFORE COMMIT OK (62 s), 1,688 unit |
| `lake build` in lean/                 | 07:54 to 07:58 | OK, 215 jobs; no sorry in lean/     |
| `java/stress/level1.sh`, full         | 07:58 to 08:00 | LEVEL 1 OK                          |
| `java/stress/level2.sh`, full         | 08:00 to 08:13 | LEVEL 2 OK, conformance TRACECHECK  |


## 8. Questions for Frans

* **QR1. rw().** An `rw()` action that catches a refused `env.put()` and
  returns normally commits its other writes. Spoil the rw environment
  too (the commit then throws `IllegalStateException`, nothing written)?
  Recommended: yes, for the same "all of them, or none"; a small change
  in `RwEnvironmentImp` and its Javadoc. Not made: outside the decision.
  **Decided** (Frans, 2026-11-12, 09:34: "So, this is decided. Keep as
  is, ensure its in the Javadoc."): the rw environment is not spoiled; a
  refused call changes nothing, and an action that catches it and returns
  commits its other writes. The reason (Frans, 09:16): "the rule is that
  use of the Pub API must keep the integrity of the database. Including
  features in the pub layer. This includes indexes. But only indexed
  created by the database itself. [...] the user is responsible for the
  code in Action. The example code is bad as it is. It is broken. But the
  database is not broken." The database's index entries are made after
  the action returns, from what it wrote (RwTransaction). Said in
  `RwEnvironment`'s Javadoc ("Refused calls"). A public key check, so
  that a user can test a key before a call: 026-02.
* **QR2. testLoweredBudgetAfterPinsFell** (section 6): keep 550, or let
  the test search its count? Recommended: keep 550 now; the search when
  it moves again.
  **Decided** (Frans, 2026-11-12, 08:51: "QR2, as recommended."): keep
  550.


## 9. State

Written 08:14, 2026-11-12, by "rules" of coord-1112. **Done**; every
gate of the brief OK (section 7). Nothing runs; no slot is held.

* **Clone** `/Users/f/fl/bench/2026-11-12/rules/clone`, branch
  `024-27-rules` from main `c0a8cadf`, head **`40275fd7`**, working tree
  clean. Commits: `ac0e4bdf` (the code, Lean, Javadoc, docs/levels.md,
  new tests), the five test commits of section 6 (`33e0a97c`,
  `cedbcde3`, `bc446d74`, `ffe004ee`, `cb5dab4a`), and `40275fd7`
  (releases/next.md).
* **Main tree**: this file, and 024-02's section 6 (the node size
  paragraph, the table row, "Checked on reading") and 11.3 (two bullets).
  Nothing committed there.
* **Gates**: section 7, all OK on the head.
* **For Frans**: the five test commits of section 6 (approved by his
  decisions; the Eviction one is a setup change, QR2); QR1 (rw()).
* **To continue**: the coordinator lands the branch; a line at 024-23's
  QO2 (section 4) closes it there.

2026-11-13. Status set after the release (coord-1113).
