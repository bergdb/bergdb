# 020-30-04. The options outside the write path: format, Lean, C, tests

By agent f30 of coord-1110, 2026-11-10, read-only, from `main` at `772c1e5a`.
Phase 1: an overview of costs, not a proposal. A: the delete goes upward. B:
reclaim cleans up. C: both. D: merging underfull nodes. B has three parts here.
B1: reclaim does not copy nodes that are unreachable at every time from the
first available time f on. B2: it compacts the nodes it rewrites. B3: its own
transactions make emptied subtrees unreachable.

## 1. Main findings

1. The bytes are no problem; the rerun is. Every option writes only klong
   kinds and node shapes that today's and 2026.3's parser accept. But startup
   reruns the section's transactions through the Dag, so the Dag's rules are
   part of what a record means. A, B2, B3 and D are format changes in the
   sense of 018-01, section 2. Each needs Frans's approval and a new
   `RECORD_FORMAT` (5 to 6). B1 alone is not a format change.
2. The Lean model needs no change for A, B1, B3, D, or for B2 done as a new
   node. Only B2 "in place" is outside the model: a node that keeps its id
   and drops old entries. That would be a large change.
3. The C port (022) must port every option byte for byte before it can
   follow 2026.4.
4. StreamDigest: all 12 configurations delete. A and D change most of them,
   B only the 4 `l3-*`.

## 2. Stream format

* Klong kinds are TIME 0, KEY 1 and DELETE_BITMAP 3 (Klong.java:64-70). The
  parser accepts any of them in any key node, leaf or not, and a node with
  0 klongs (StoredKeyNode.java:166-186; Phys.lean:427).
* Today only segment leaves get delete bitmaps (Dag.java:794); with A, inner
  nodes do too. Reads already skip a deleted klong in any node
  (KeyNode.java:403-455).
* Versions: `RECORD_FORMAT = 5` (StoredTrans.java:53, the same in 2026.3,
  checked at :340). Each node kind has its own byte: key node 2
  (StoredKeyNode.java:55,108), value node 4, top node 2. The framing version
  is 154 (MetaBlock.java:51). An unknown version gets a
  `VersioningStreamException`. Nothing records which Dag rules wrote a
  record.
* The rerun: DbStarter.java:438-465 reruns each record's puts (`dag.putKv`).
  Then it looks up the record's got-dirty (id, spos) pairs, and fails with
  "startup error, node ... not found" if the rerun made other ids. The touch
  is not stored and not rerun (DbStarter.java:480-484).
  * If 2026.3 opens a stream written with A or D, it reruns with the old
    rules: other node contents, so other splits and ids. The start fails, or
    the tree silently differs. The same holds the other way round.
  * This needs a new format byte, and then a choice: either rerun format-5
    records with the old rules, or refuse 2026.3 databases ("new databases
    only", StoredTrans.java:43). 2026.3 still opened 2026.2's databases, so
    the choice is Frans's.
  * B2 and B3 change node contents in a reclaim step, which the rerun does
    not rerun. The record must store the step (its range and f): a new header
    field, a format change.
  * B1 changes only which nodes become dirty, and startup rebuilds D from the
    stored ids. So B1 is not a format change.
* Two notes for the Dag study (03):
  * Today a put throws "corrupt data" when an inner node has no live klong
    at or below the key (`checkFound`, Dag.java:835; C dag.c:436). So A must
    not delete the first live klong of a node that keys are still routed to.
  * A alone never cleans the garbage that 2026.3 databases already hold:
    those need B, or must be refused.
* Trace format (docs/trace-format.md): no change for A, B1, B3 or D, since
  `D` entries and `TOUCH` and `CUT` lines exist. B2 in place would need a new
  entry kind.

## 3. Determinism and digests

* Within one release, each option is a function of the transaction and
  P@(i-1) (A1, `Spec.exec` in Basic.lean). B must take f from the record or
  the table, never from a clock or from what is evicted.
* StreamDigest (java/stress/StreamDigest.java:76-91): 12 configurations, all
  with `del=1`.
  * A changes those where a node loses its last live klong, likely most.
  * D changes those with underfull nodes.
  * B changes only `l3-every1`, `l3-node8`, `l3-node14` and `l3-node62`.
* Its four modes (plain, reads, restarts, restarts-once) must still agree.
  That agreement is the real determinism check.
* Changed digests are acceptable. Within a format, 018-01, section 2 asks for
  the digests before and after in the entry, and a line in releases/next.md.
  With a format bump, the change is approved as a format change, and 2026.2's
  baseline no longer compares for those configurations.

## 4. The Lean model

* SIS is abstract ("Nothing here depends on klongs", docs/sis-model.md). T1,
  T2, T8, T12 and T13 hold for any `exec` that meets these assumptions:
  * `StepOK` (Assumptions.lean:88): A2 to A5 and the touch rules.
  * `PhysStep` (Phys.lean:534).
  * TREE, A6' and A-COPY (Phys.lean:621-670).
* `CutOK` (Reclaim.lean:102) is a hypothesis of T8 and T12, checked on
  traces (C-CUT) and not proved of Java.
* BergDB's instance (Check/Trace.lean:16-60, `BVal.del`, `blive`) already
  reads a delete entry in any key node.

| Option   | Lean change                                    | Watch                        |
|----------|------------------------------------------------|------------------------------|
| A        | none in SIS; maybe a checker check, ~100-200   | A5: no re-use of a dead node |
| B1       | none                                           | dead at every t >= f (CutOK) |
| B2 new id| none (as a time split)                         | A-COPY, adopt                |
| B2 in pl.| new change kind, history no longer append-only | ~28 prefix uses in SIS/Proof |
| B3       | none (adds in a touch step)                    | touchReach, touchUp          |
| D        | none: merged siblings are replaced (`pathOf`)  | TREE, A6', A-COPY            |

* A theorem of the rule itself (zero cost eventually, O(n) scans) needs a
  model of keys and deletes, which SIS lacks. SIS/Bound.lean bounds only the
  startup section. Such a theorem would be new work of hundreds to thousands
  of lines, and optional.

## 5. The C port (022)

* items/022-bergdb-c/c follows Java 2026.4 byte for byte (c/readme.md);
  `test/cross/cross.sh full` compares streams with Java on StreamDigest's 12
  configurations. Item 012's copy stays at 2026.2: no cost there.
* Places: src/dag.c (`check_found` :436, `set_value` :459,
  `append_delete_klong` :597, splits :714-970), src/knode.c
  (`kn_last_version_given_del` :650), src/reclaim.c (touch step :881),
  src/db.c (`touch_range` :844), src/starter.c (rerun), src/snode.h (parse).
* Rough lines, ported once Java is settled: A 150-300, B1 about 100, B2 or B3
  200-400, D 300-600. The format byte is small; two rule sets (format 5 and
  6) would double the Dag's rerun paths.

## 6. Tests and conformance to redo

* before-commit.sh: delete and structure unit tests (DagTester,
  KeyNodeTester, DbTester, Reclaim's `testDeletedKeysAfterCut`), the version
  refusals (StoredTrans.java:1145-1166).
* level1.sh: DagFuzz, DeleteRepro, RestartStress, RestartInvariance, Props'
  SS limit. level2.sh: RestartStress, RestartInvariance, CrashTest,
  `conformance.sh small`. level3.sh: ReclaimStress, RestartInvariance and
  CrashTest with reclaim, ReclaimReaders, LoadTest, PowerLoss,
  `conformance.sh reclaim` (C-CUT). level4.sh: EvictionInvariance,
  `conformance.sh evict` (C-P, C-H), LargerThanMemory.
* A and D need all four levels, B levels 3 and 4; all need `night.sh large`.
  Traces are made fresh by TraceExport; the 20 hand-made traces in
  lean/test-traces are unaffected.
* New: the rule's check of 020-30, section 2 (own script and a night.sh
  step); 2026.3's jar (releases/2026.3) against a 2026.4 stream and the
  reverse; C's cross tests with the new pin.
