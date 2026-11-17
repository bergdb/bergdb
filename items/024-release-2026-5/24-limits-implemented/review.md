# 024-24, review (rev24)

An independent review of the branch `024-24-limits`, head `4a9ebcb2`
(`git diff 08659847 98454653`; `0cb7eff7` is main's option-2 landing),
before it lands. By rev24, an agent of coord-1111, 2026-11-11, 18:51 to
19:04. I read the diff first, then 024-17 (sections 5.2a, 5.5, 6, 8) and
the item (024-24).

Where: my clone `/Users/f/fl/bench/2026-11-11/rev24/clone` at `4a9ebcb2`
(clean, nothing changed), the base `/Users/f/fl/bench/2026-11-11/rev24/base`
at `0cb7eff7`, both built with `java/build.sh`; probes in
`/Users/f/fl/bench/2026-11-11/rev24/probe/src/bergdb/core/` (`Rev24Probe.java`,
`Rev24Reclaim.java`), LimitsTester outputs in
`/Users/f/fl/bench/2026-11-11/rev24/limits-{base,clone}.txt`. No slot taken:
single JVMs of about a minute each.


## 1. Verdict

**LAND WITH FIXES.** The limits are where 024-17 puts them, counted as it
says, refused before the go point with messages that name them, and the
Lean side is as decided (the count with q, `ReleaseFits` by `decide`).
The 22 changed tests keep their purpose, with the notes of R7 to R9. One
fix should go in before it lands, as it is a database failure that the
branch makes possible and the item's own design rule forbids:

* **R1** (should fix, before landing; two lines): `Trans.Builder.putLongKey()`
  checks L4 though its Javadoc and the item (section 2, section 5's first
  decision) say it does not, and reclaim's step calls it inside a user
  transaction's go point. A value over L4 in the database then fails it
  when reclaim rewrites the value; shown by a probe, with the value put
  through the public `Trans.kvs`, which `Db.execute` does not check for L2
  or L4.

The rest are Javadoc that is not true to the code (R3, R4, R5), a
documented promise that a check is unreachable which a probe reaches (R3),
and notes. Landing without them writes no wrong data.


## 2. Findings

### R1 (should fix, before landing). putLongKey checks L4; reclaim then fails the database

* **Where:** `java/src/bergdb/core/Trans.java:290-299` (`putLongKey` calls
  `checkValue`, which since this branch refuses a value over 8 MiB,
  `Trans.java:508-512`); its Javadoc at `Trans.java:281` says "Neither the
  key's length (L2) nor the value's (L4) is checked here". The item says
  the same (024-24, section 2: "check neither L2 nor L4"; section 5, the
  first decision: "Internal calls skip L4 too ... a refusal inside its step
  would fail the database"). `Reclaim.java:647` calls `putLongKey` for each
  live value it rewrites.
* **Failure:** a value over L4 that is in the database, when reclaim
  rewrites it, throws `IllegalArgumentException` inside the go point of
  the user transaction whose listener runs the step: the database fails.
  How such a value gets in: `Trans.kvs` is public and `Kv`'s constructors
  are public, and `Db.checkLimits` (`Db.java:2810`) checks L1, L3 and L5
  only, not L2 or L4 per KV. Probe `Rev24Reclaim`: a 9 MiB value put through
  `t.kvs` is taken; later small puts with a retain duration of a second
  give `DbFailedException`, cause "The value has 9437184 bytes, more than
  8388608 (bergdb 024-17, L4)". (Probe `Rev24Probe` 2: a key of 5,000 bytes
  and a value of 10 MiB through `t.kvs`, taken.) A restart reruns the same
  step from reclaim's stored state, so it probably fails again (not probed);
  015-50 was this kind of loop.
* **Severity:** should fix before landing. The way in is not a
  `Trans.Builder` call, but the failure is the one 015-50 fixed and the
  item's design rule names, and the fix is small.
* **Fix:** (a) in `putLongKey`, check the value for null only (as the
  Javadoc says), so that reclaim's copy never throws for a size; (b) in
  `Db.checkLimits`, for user transactions, refuse a KV whose value (the
  input) passes L4, and one whose key passes L2 unless `kv.longKey`, with
  `DbException`: it already loops over the KVs with each key's bytes and
  value's length. Then nothing over L4 enters, whatever builds the `Trans`.

### R2 (note, or should fix if cheap). The internal calls are public

* **Where:** `Trans.java:290` `putLongKey`, `Trans.java:306` `deleteLongKey`:
  public methods of `Trans.Builder`, which `Db.trans()` gives every Core
  user; "Internal, not API" in their Javadoc only (as `Db.lookupTime`).
* **Failure:** a Core user can put a key of up to 57,344 bytes (L3) with
  `putLongKey`, past L2. The bound is not hurt (L3 and L5 hold, and
  `Limits.release` takes a key as long as L3 allows), but Db's Javadoc
  "Limits" says a longer key is refused by the call. The brief's question
  "the internal call cannot be reached from the public API": it can, from
  the Core API; not from the Pub API (every Pub write goes through
  `RwEnvironmentImp.put/delete`, which check L2 on the ikey).
* **Fix:** in `Db.checkLimits`, refuse a `longKey` KV over L2 whose key
  does not start with 01 25 (the bkey of "/#", BergDB's keys by Db's
  Javadoc): every key BergDB puts through these calls over L2 is under
  "/#i/"; reclaim's copies of user keys are within L2. Or leave it, and say
  in Db's "Limits" that the internal calls are not checked.

### R3 (should fix: Javadoc and levels.md). 005-31 refuses transactions within the limits

* **Where:** `Db.java:266-269` ("The checks of the record's size and of
  the index nodes a transaction can make dirty (bergdb 005-17, 005-31)
  stay, as refusals that a transaction within the limits does not meet"),
  `docs/levels.md:162-163` (the same), and 024-17's L8 ("a theorem;
  005-31's check as `Bug`", QL5).
* **Failure:** `Db.checkDirtyNodes` counts a KV with a key transformation
  coarsely, `(delete ? 20 : 3) * height * segments + 3`, and a KV with a
  value transformation as a delete (`Db.java:2872`, `2887`), with `height`
  from the stream's length. A transaction of 500 KVs of 111-byte keys,
  each with a key and a value transformation, counts 500 x (320 h + 3)
  nodes. At node size 62 (1,056 bytes a node) that passes the dirty limit
  once h >= 12, a stream of 49 KB; at node size 30 once h >= 24, about
  200 MB. Probe `Rev24Probe` 3: node size 62, a stream of 258 KB, 500
  such KVs (identity transformations), refused: "up to 2241500 [nodes] ...
  more than 2013265912 (bergdb 005-31)"; at node size 30 taken. On a
  100 GB stream (h = 32) at node size 62, 187 such KVs are refused. A value
  transformation alone also walks the key twice (as a put and a delete),
  a count the model's `Limits.dirtyNodes` (one operation a KV) does not
  bound.
* **Severity:** should fix the statements now: the refusal is clean (a
  `DbException` before the go point), but the Javadoc promises it cannot
  happen. For QL5 it is a precondition: 005-31 cannot become a `Bug` while
  this count exists.
* **Fix:** say in Db's "Limits" and in levels.md that a transaction with
  key or value transformations can still meet 005-31's refusal (the count
  of a key transformation is coarse); add to 024-17's QL5 that the `Bug`
  step needs a count of transformed KVs within the model's bound.

### R4 (should fix: Pub Javadoc). Stale and missing @throws

* `java/src/bergdb/pub/WBuilder.java:60-73`, `put`'s
  `@throws IllegalArgumentException`: still "whose UTF-8 takes more than
  2^31 - 9 bytes" for a String and "larger than a stored value may be in
  Java, 2^31 - 9 bytes" for an object; it names neither L2 (a key over 111
  bytes) nor L4 (8 MiB). `Connection.put` (`Connection.java:401-406`) and
  `RwEnvironment.put` (`RwEnvironment.java:91-95`) refer to it.
  `Connection.delete`'s and `RwEnvironment.delete`'s IAE do not name L2.
* L6's refusal is an `IllegalArgumentException` thrown by
  `RwEnvironmentImp.indexEntries`, so by `WBuilder.execute()` for a w()
  (not by `put()`), by `Connection.rw()` after the action, and by
  `Connection.put`: none of their `@throws` says so (`WBuilder.java:84-114`
  lists `DbException`, `DataFormatException`, `IllegalStateException`).
* `java/src/bergdb/pub/IndexBuilder.java:48`, the index's rules: "If the
  levels' encodings take more than 4,096 bytes in all, v has no entry."
  Now: more than 111 bytes, and a put of such a value is refused; a build
  over values put before gives no entry (024-17, 6.2 (e) listed this
  line).
* **Fix:** the three places, in the words of the package's "Limits".

### R5 (note: wording). L3 is all the keys, not BergDB's own

* `java/src/bergdb/pub/package.html:238` ("BergDB's own keys of the
  transaction, its index entries among them, take at most 56 KiB") and
  `releases/next.md:130` ("BergDB's own keys of it, its index entries among
  them, at most 56 KiB"). `Db.checkLimits` counts every key of the
  transaction, the user's too (Db's Javadoc says so correctly).
* **Fix:** "the keys of the transaction, its index entries among them,
  take at most 56 KiB".

### R6 (note). Many indexes in a directory make one object put too large

* No limit on the indexes of a directory (none in `IndexManager`,
  `IndexBuilderImp`). An object put is 1 + k operations (new) or 1 + 2k
  (an update), entries of up to 497 bytes: with k >= 250 (update) or 500
  (new) every object put in the directory is refused by L1; with long
  index names and long levels, by L3 from k = 58 (update) or 116 (new).
  The refusal is clean, but its message says "Split it into
  transactions", which a single put cannot.
* **Fix (later is fine):** a limit on the live indexes of a directory,
  checked when an index is created, or a sentence in the package's
  "Limits"; the release notes can say it too.

### R7 (note: tests). 021-16's depth is no longer reached at the Db level

* `DbTesterLongKeys` (`c303944c`) and `PubTesterLongKeys` (`5f9a5c89`) were
  021-16's regression tests: a recursion with a frame a segment overflowed
  at a key of about 90 KB at the start's check and at 1 MB after 100 kB in
  `Dag.dirtyNodeBound` (`freshTreeBound`). The longest key the Core takes
  now is 57,344 bytes (8,193 segments), which the rewritten test puts, but
  with the default stack a reintroduced recursion would likely pass there.
  `DagTester.testLongKeyWalks` (400 kB) covers the visits and the iterator,
  not `dirtyNodeBound` and not a restart.
* The new tests are right at the limits (I checked the byte counts: 111 =
  "/dd/-" + 102 + ".txt"; 109 for 34 directories; 110 for 54 letters å; one
  more of each refused).
* **Suggestion:** run the 57,344-byte put and a restart in a thread with a
  small stack (such as 128 kB), so that a frame a segment overflows; or a
  `DagTester` case of `dirtyNodeBound` for a key of 1 MB after one of
  100 kB with the same start.

### R8 (note: tests). LimitsTester reaches 005-31 less often

* `5182cc8f`: with keys of at most 111 bytes and putManyKeys over 500
  refused by L1 first, the refusals of 005-31 fell. Seeds 5000 to 5011,
  500 steps each, the same on both trees: base "37 index nodes", branch
  "8 index nodes" (size 228 and 239; 100 refusals of the limits). Still
  reached, so the purpose holds.
* **Suggestion:** putManyKeys's n between 300 and 500 more often, or with
  node size 8, to keep 005-31's refusal frequent.

### R9 (note: tests). L6 checked in one direction by the harnesses

* `71b40e6b` IndexHarness: a refusal is checked to have a cause (a write
  whose levels pass L6 for the live index named; an index not live in the
  reference is not checked), but a put that should be refused and is taken
  goes unseen: Java and the reference both give it no entry.
* `b6b8e563` FormatFuzzer: the expected refusal is computed by calling
  `IndexDefinition.entryForPut` itself, the code under test.
* The boundary itself is tested independently (`IndexReference.tooLong`,
  `IndexDefinitionTester.testFunctionLimit`,
  `PubTesterIndexJobs.testLargeValueNoEntry`), so this is a note.
* **Suggestion:** in IndexHarness, after a commit, assert with
  `ref.tooLong` that no write of it had levels over L6 for a live index.

### R10 (note, for QL5). L7 is not a consequence of L1 to L5 with value transformations

* L5 counts a value transformation's input; its result may be up to L4
  (QL6), so 500 of them make about 4 GB, over the record limit. 005-17's
  check after the go point then fails the database, as levels.md says
  (015-51's rule, kept). So 024-17's "L7: a theorem from L1 to L5" holds
  only without value transformations; QL5's `Bug` step for 005-17 needs
  the results counted too. (A key transformation can lengthen keys by up
  to 500 x 111 bytes after L5's count: negligible.)

### R11 (note: tests). QL7's test does not show "before the record is read"

* `NodeStreamTester.testRecordHeaderFirst` uses records of 1,000 bytes: the
  iterator's case passes on the base too (the old code read the record
  whole, then `StoredTrans` refused the format). The L7 case is a size the
  stream does not hold. Nothing shows that no buffer of the record's size
  is made first.
* **Suggestion:** a stream stub whose length is about 2^31 and whose
  `read` of more than a few bytes throws.

### R12 (note). Q2's 'in one transaction'

* `ced8c219` DbTesterDelete.testDeleteEveryKey: at n = 2,000 the deletes
  are four transactions of 500; the whole tree is still emptied in one
  transaction at n = 100 (node size 8). Adding n = 500 would keep a deeper
  tree emptied whole in one transaction. Q2's recommendation (approve the
  set) is right otherwise.


## 3. What I checked and found sound

* **Core, L2 and L4 at the call.** Every `Trans.Builder` call that takes a
  key checks L2 as stored (`put` of `byte[]`, `long[]`, `long[]` with
  transformations; `delete` of `byte[]`, `long[]`; `put` and `delete` of
  `String` through them); every put checks L4 (`put(String, String)`
  through `put(byte[], byte[])`). `keyBytes` is the bkey's length
  (7 (segments - 1) + the last segment's). Messages name the limit.
* **L1, L3, L5** in `Db.checkLimits`, from `checkSize`, before the write
  lock, the warmup and any time, for user transactions; counted after the
  builder's one-a-key rule; Pub transactions are user transactions, their
  index entries counted.
* **Key transformations** (`transformKeys`): L2 on each transformed key but
  `longKey` ones, L3 on the sum; `giveBack` restores keys, hashes, `t.tt`
  and the clock, as 024-16's refusal; before the go point.
* **QL6:** the check after `transformValue` in `putKvs`, user transactions
  only; DbTesterLimits shows the failure and the restart's state.
* **Pub:** `checkKeyBytes` counts the ikey's UTF-8 exactly as the Core
  stores it (the fast path 3 x chars <= 111 is safe); key replace keeps a
  key's length ("${transactionTime}" is 18 chars, the time `%018d`, with
  an assert); every Pub write goes through `RwEnvironmentImp.put/delete`
  (WBuilderImp, ConnectionImp.put/delete, rw()); L4 before any copy for
  `byte[]`, `String` (`stringValue`), objects (`DataObjects.toDbObject`
  with the limit), `DbObject` by its bytes. L6: `entryForPut` refuses in
  `indexEntries`, before `createTrans` and `Db.execute`, nothing written;
  the previous value's entry by `entry()` (no refusal on a delete or an
  overwrite of an old long value); a build gives no entry.
* **BergDB's own transactions within the limits:** a build step 25 values;
  a cleanup step 100 deletes of entries of at most 497 bytes, 49,700 bytes
  (under 57,344); a reclaim step's scan counts at least 108 bytes a KV
  against 16 kB, so about 150 KVs, keys under 16 kB.
* **QL7:** `readRecordHeader` reads 4 bytes, refuses a size over
  `MAX_RECORD_SIZE` and beyond the stream before any buffer, then the last
  byte and, for a committed record, the format byte; an uncommitted tail is
  skipped as before; the old minimum sizes are kept (<= 6 and < 17).
* **Lean:** `nodesALevel` = 5 + ceil(2 (q + 2) / (q - 1)) (+1 at q = 2);
  `roomAfterReplacement` with `withMerges` is 2, 4, 10 and 24 at node sizes
  8, 14, 30 and 62, so 14, 9, 8, 8 (q >= 2 always, by its `max 2`).
  `Params.java` sets `format7` (mergeBelow >= 1). `ReleaseFits` recomputed:
  at 30, H = 22: 8 x 24 x 8,692 + 7,000 = 1,675,864 nodes x 544 bytes =
  0.91 GB; at 8, H = 61: 7,673,344 x 192 = 1.47 GB; both under
  2,013,265,912 (15/16 of 2^31 - 9, `StoredTrans.dirtyLimit`). `nodeBytes`
  and the two top nodes are `Db.checkDirtyNodes`'s. Proved by `decide`, no
  `native_decide`, no `sorry`. TP26 restated over the sum; treetest and
  C-T8 (`Check/Tree.lean`) give each transaction its own operations,
  longest key and sum of segments. TP23 unchanged. `ReleaseFits` is
  arithmetic only; no theorem joins it to TP26 (as the item says).
* **Java's count against the model's:** Java's walked `dirtyNodeBound` is
  the model's (C-T8 on traces of node sizes 8 to 62); at one delete on a
  full path Java's per-operation count allows 766, 1,215, 1,478 and 996
  operations against the count with q's 742, 1,210, 1,251 and 822
  (024-17, 5.2a), so Java is within the model's bound there. The coarse
  counts of transformed KVs are not (R3).
* **The changed tests, one by one:** CapacityTester (500 loads still under
  pressure), KeyFactory.crazyKey (20 to 111 bytes), DbTesterDelete (R12),
  DbTesterGetMany (2,000 deleted long keys in 4 transactions, the walk's
  claim unchanged), DbTesterJavadoc (111 taken, 112 refused), DbTesterLongKeys
  and PubTesterLongKeys (R7), Eviction (keys of 111 still long: 16
  segments), LimitsTester (R8), DataObjectsTester (L4 at the put, 2^31 - 9
  kept for `toDbObject`), the index testers (L6 boundaries at 111 and 112,
  with 00 and 01 escapes and two-byte chars; R9), PubTesterIndexJobs (QL4
  refused, the build part kept), PubTesterIndex, PubTesterPrimary,
  PubTesterThreads (the same claims in w() of at most 500 operations with
  entries), testTooManyDirtyNodes (still refused by 005-31 at the lowered
  record limit), DbTesterStream, Crazy, BigDb (8 MiB), and the programs.
  None tests nothing now; the losses are R7 and R8, and Q2's.
* **Docs:** levels.md section 3 and next.md match the code but for R3 and
  R5; the user wording "A key is at most 111 bytes; about 100 characters
  as a rule of thumb ..." is in Db's Javadoc, the pub package's "Limits"
  and next.md; Connection's "Keys" says L2 with the "/" counted twice.
* **Gates by lim3 on `4a9ebcb2`** (from `lim3/gates.out`, at 19:02): Lean
  (test-traces) OK, before-commit OK, level1 OK, unlinkfuzz OK; level2 was
  running.


## 4. What I did not check

* The gates after unlinkfuzz (level2's treeconf with C-T8 at node sizes 30
  and 62, level3, level4, conformance); `lake build` myself.
* The night tests (`@Nano("night")`, `src-dev/bergdb/test/night`) beyond a
  grep for batches over 500, keys over 111 and values over 8 MiB (none
  found in PayTest's new batches, Issue150420's keys of at most 21
  characters, IndexJobsHarness's w() of 50); LimitsTester's night set only
  as in R8.
* Whether a restart after R1's failure fails again (likely: reclaim resumes
  its step).
* The interplay with 024-25 (CRC32C, a format change): `readRecordHeader`
  compares with `StoredTrans.RECORD_FORMAT`, so it follows a new number.
* The C clone, performance, and the proofs that 024-17 leaves for later
  (TP23, TP26, TP30).
