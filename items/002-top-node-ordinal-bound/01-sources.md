002-01. Sources on the top node ordinal bound
=============================================

By Claude (Opus 5.5, Claude Code) for Frans Lundberg, 2026-10-17. What
exists about the bound, gathered as a starting point for the item. Code at
bergdb `d540066`. Nothing here was run; the statements about code come from
reading it. Section 5 says what each source adds, and what is still open.


## 1. The question

Every new super root gets the ordinal of the previous one plus one
(`TopDs.newSuperRoot`). The ordinal is a Java `int`, and `TopNode.height`
refuses ordinals above `MAX_TOP_NODE_ID_VALUE` = 2^30 − 1. So a database can
make about 1.07 · 10^9 super roots in its whole life. Reclaim (Level 3)
bounds the stream, so a database can now run indefinitely, but the ordinals
never restart.

Register row M46 ([docs/level4-alignment.md](../../docs/level4-alignment.md),
section 3) proposes two ways out, for Frans to choose: a wider ordinal (the
header has 48 bits for it) or a clean refusal before the transaction changes
anything. Also listed as "not settled" in its section 6.4, and as "Open for
Frans (not urgent)" in
[001-02](../001-lean-model-levels-3-4/02-progress.md), "Frans's go and
decisions".


## 2. The code today

* `java/src/bergdb/dag/TopNode.java`:
  * `public final int topNodeId`, the ordinal.
  * `MAX_HEIGHT = 30`; `height(id)` is the bit length of `id` (the number of
    skip pointers), and throws `IllegalStateException("Bad id value")` for
    `id > MAX_TOP_NODE_ID_VALUE`.
  * `MAX_TOP_NODE_ID_VALUE = power2(MAX_HEIGHT) - 1` = 2^30 − 1.
  * The constructor allocates three arrays of length `height(id)`.
* `java/src/bergdb/dag/TopDs.java`, `newSuperRoot` (line 42): a second
  root change in one transaction updates that transaction's super root in
  place, with no new ordinal. Otherwise `new TopNode(superRoot.topNodeId +
  1, ...)` (line 59), and for each set bit i of the new ordinal, slot i
  inherits the old super root's slot i, or points to the old super root.
  The constructor is where the bound throws: before TopDs calls its own
  listeners, but after `Dag` has already made the new root key node and
  reported it (`Dag.spaceSplitInPlace` line 867, `timeSplit` 919,
  `spaceSplit` 986).
* Where new super roots come from: a time split or a space split of the
  space root (the three `Dag` call sites above). A hot key fills the root
  with versions, so the root time-splits often; that is why one hot key
  gives a new top about every 15 transactions (section 3).
* `java/src/bergdb/core/StoredTopNode.java`, the format (top node format
  version 2): bytes 8 to 15 are one long, `pointersLength | (topNodeId <<
  16)`, so byte 8 is the pointer count, byte 9 is zero, and bytes 10 to 15
  hold the ordinal, 48 bits. `toLongs` writes all 48 (widened since WP A3,
  line 199); `parse` reads bytes 10 to 13 as an `int`, skips 14 and 15
  ("2 zero bytes"), and refuses a negative ordinal or one above
  `MAX_TOP_NODE_ID_VALUE`. Since A3 it also refuses a top node whose skip
  pointers do not fit its ordinal (lines 133 to 149). Byte size: 40 + 16 ·
  height.
* Tests: `TopNode.testHeight1`, `testHeight2` (height 30 at 2^29);
  `StoredTopNode.testOrdinalsRoundTrip` (up to `MAX_TOP_NODE_ID_VALUE`,
  built directly), `testParserRefusesSlotsThatDoNotFit`;
  `DbTesterRestart.testRestartAfterManyTopNodes`. Nothing tests what
  happens at the bound in a running database.
* The Lean model has no bound: ordinals are natural numbers, and the top
  level is `Spec.topLevel` ([docs/level2-alignment.md](../../docs/level2-alignment.md),
  8.2 and 8.4; the checker's C-S checks the layout of every top node, 13.5).


## 3. The 2026 findings

* **F1-008-13, Codex**, in the f1 repository:
  `f1/b/008-bergdb-lean-model/13-topnodes-feasibility-codex/13-topnodes-feasibility-codex.md`.
  Found the codec defect (its 5.1): the ordinal was shifted as an `int`
  before widening, so from 32,768 on it was written wrong. Says the model
  can use natural numbers with a separate Java bound.
* **review-13-claude**, same directory, `review-13-claude.md`:
  * Section 2: the codec defect measured end to end, and the rate of new
    tops by workload ([TopNodeRate.java](../../../f1/b/008-bergdb-lean-model/13-topnodes-feasibility-codex/review-13-claude/TopNodeRate.java)),
    at node size 30 unless noted:

    | Workload | Transactions per top |
    |---|---|
    | One key, one put per transaction | 15 (4 at node size 8; 31 at node size 62) |
    | 10 keys, one put per transaction | 10 |
    | 1,000 keys, one put per transaction | 909 |
    | 1,000 keys, ten puts per transaction | 149 |
    | 100,000 keys, one put per transaction | 7,143 |
    | New keys with a common prefix, appended | no new top in 50,000 transactions |

  * Section 3, "The ordinal bound is a lifetime limit under reclaim": with
    one hot key, the bound is about 1.6 · 10^10 transactions, about 186 days
    at 1,000 transactions per second, about 5 years at 100. Java's behavior
    at the bound is untested; it throws in the middle of the root split. The
    two options: a wider ordinal (48 bits in the header; `long` ordinals and
    `MAX_HEIGHT` up to 48) or a clean early refusal.
  * Section 4.3: a search follows at most h(H) top nodes, the bit length of
    the head's ordinal, and the bound is tight; slot inspections grow with
    its square (391 at bit length 30). A search at time q loads, besides the
    answer, only tops created at or after q (the footprint lemma). Relevant
    to a wider ordinal (more hops, at most 48) and to any renumbering.
  * Section 6: the Java facts about `TopDs` and `TopNode`, with lines.
* **bergdb item 001**:
  * WP A3 fixed the codec (`280525a`): [docs/levels.md](../../docs/levels.md),
    "Bugs found by the alignment of Levels 3 and 4", bug 1;
    [docs/log.md](../../docs/log.md), 2026-10-16; register row M30, closed.
  * WP A2 registered the bound as M46, from review-13-claude, 3. 001-02
    records it under "Open for Frans (not urgent)", with Frans's 15:43
    instruction to adopt review-13-claude's 7.1 (the repair of old streams,
    its point 5, was not adopted).


## 4. The 2012 to 2015 history

From the archive F1-007 (`f1/a/007-bergdb-261012/`, read-only), its
`bergdb/doc/` notes and the original git history (`bergdb-git.bundle`).

* **`bergdb/doc/2012/2012-05-TopDS.txt`** (2012-05-11), the design of the
  top data structure: the skip list by the bits of the ordinal, the search
  algorithm, and the construction ("fast and beautiful"). On height:
  * "There is no reason for a predetermined maximum height. Instead the
    height of a new top node floor(log2(id))."
  * The estimate: "For 1M added KVs, we need about 64 (2^6) top nodes; so
    the top node height would be 6. For 1G added KVs, we need about 2^9 top
    nodes; so the top node height would be 9. We will never see a height
    about 12, I believe." And: "More then h = 15 may never happen."
  * An alternative, "DECREASE the top node height": "When the pointer with
    the highest pointer id, has a right-most pointer that points to a top
    node that is too old (spos is 'forgotten' because of stream refresh), we
    can reduce the height. Simply by omitting the right-most pointer." So
    the interaction with reclaim ("stream refresh") was in view in 2012.
* **`bergdb/doc/log-old/2012-log.txt`**, 2012-04-20: "Refactored TopNode.
  New class TopDS handles top data structure now."
* **`bergdb/doc/2013/2013-05-notes.txt`** and `2013-active-replica.txt`:
  the stored top node, "topNodeId - Special id for top nodes (consecutive
  integers)"; "Serialized TopNodes do not change".
* **The code in 2013** (first commit of the git repository, `76c4792`,
  2013-06-06, `KissDB/src/kissdb/core/TopNode.java`): already `MAX_HEIGHT =
  30`, with a precomputed `power2` table of 30 entries. `height(id)` had no
  check: for an ordinal of 2^30 or more it returned 30, so the new top
  would have had no slot for its highest bit (2^30 itself: no skip pointers
  at all), and the older tops would no longer be reachable.
* **`2c6ceb5`, 2014-08-03**, "Refactored TopNode. (Remove precomputed
  values, little or no performance gain.)": removed the table, added
  `MAX_TOP_NODE_ID_VALUE = power2(MAX_HEIGHT) - 1`, the throw in `height`,
  and the parser's check "TopNode ID too large in stream". This is the
  bound as it stands today.
* **`bergdb/log.md`**, 2015-07-21 (`91dd40c`): "IMPORTANT FIX, finding
  latest super node in startup section fixed. There was a bug when multiple
  top nodes with different top node id are in the startup section
  (DbStarter)."
* **`java/src/bergdb/core/doc-files/stream-format.txt`** (July 2015, also in
  bergdb today): the node header and format
  versions; the top node's own layout is left to `StoredTopNode`.

No note found on why 30 was chosen, on the 2 zero bytes after the ordinal,
or on what should happen when the bound is reached. Searched: the F1-007
archive's `bergdb/doc/` (2012 to 2016, `algos/`, `log-old/`), `bergdb/log.md`,
and the commit messages of the original git history.


## 5. What the sources add up to, and what is open

* The 2012 design assumed few top nodes (a new top node for about every
  15,000 added keys, by its estimate). Today's measurements show that a top
  node comes with every time split or space split of the space root, which a
  few hot keys make every 10 to 15 transactions. That, not the height of
  the skip list, is what makes 2^30 reachable. Without reclaim the stream
  would be large by then: about 0.5 TB for the top nodes alone (1.07 · 10^9
  times about 520 bytes at height 30; my estimate).
* The format already has room: 48 bits written, 32 read, 16 always zero.
  Not known yet whether a wider ordinal needs a new top node format version.
* The 2012 idea of decreasing the height after a stream refresh suggests a
  third way: under reclaim, tops below the cut are never searched (the
  footprint lemma, review-13-claude 4.3), so the ordinals could perhaps be
  renumbered or wrapped. Not examined.
* Open questions for the item: what Frans worked out back then (if not in
  these notes, perhaps elsewhere); a wider ordinal, a clean refusal, or a
  renumbering; what a reader or a restart sees at the bound today (a test);
  and whether the model or the checker should know the bound.
