028-22. Fix: Java comments that describe the old writer as today's
==================================================================

Status: done. Kind: Fix. Frans: none.
Created 2026-11-19 by Frans Lundberg.

What: since record format 8 the writer is PE (026-25; 027-08). 026-25
changed the comments that cited the old writer's methods, but some
comments still describe the old writer's mechanisms (splits, rule O,
the upward unlink, the take-back, the merges at the delete, the key
access path, a put at a time) as what the code does now. Found while
bringing 027 up to date (branch `027-pe`, at `b03dcea7`):

* `dag/Dag.java`: `roomAfterReplacement`'s Javadoc ("a node made by rule
  O or by a merge", "a time split's last version", "a space split's
  half"); `MERGE_MIN_NODE_SIZE` ("a space split's halves");
  `MERGE_CAP_30` ("more make two new nodes of about half each": PE cuts
  a joined list into parts of at most c, `nParts`, which can be three).
* `dag/TopDs.java` (`newSuperRoot`, about :65): "a second new space root
  in the same transaction, for example a time split of the root followed
  by a space split"; PE calls `newSuperRoot` once a transaction
  (`PeWriter.run`), so say whether the branch is still reached.
* `dag/KeyNode.java`, `check(int)`: allows B + 1 klongs, the old writer's
  node overfull for a moment before its split; PE never makes more than B
  (027-03, section 11.3). Say so, or tighten the check (then
  before-commit and the level scripts).
* `dag/GetData.java` (`kvTime`, about :29): "replaces a full key node, by
  a time split or a space split": now by new nodes (a replacement, a cut,
  a join, a compaction).
* `core/Db.java`: the cheap count's comment in `checkDirtyNodes` (about
  :3209: "the upward unlink and the merges"); the value transformations'
  Javadoc (about :3672: "the index nodes that the step's touch and puts
  made dirty": since 026-25 the touch's only, 027-13, section 1.4).
* `core/Trans.java`: the Javadoc of the touch's counts (about :102: "by
  the puts and the touch": the touch's only since 026-25).
* `java/stress/TraceExport.java`: the TREE line's comment ("rule O's h",
  about :1710; the roles in PE are 027-02, section 4) and the unreached
  nodes' comment (about :1646: PE makes none).
* Tests whose Javadoc explains today's behaviour by the old writer:
  `DbTesterDelete`'s class comment and its test at about :131
  ("Dag.deleteUpward throws Bug"); `DagTester` at about :521 (the key
  access path, `handleFullNode`); `DeadKlongTester`'s class comment and
  its test at about :165 (rule O, a time split); `DbTesterJavadoc` at
  about :703 ("a space split"); `Residents.testReplacedNodeCounted`
  (about :554, `handleFullNode`). Regression notes that tell what
  happened then (for example `DagTester` at about :179,
  `Reclaim` at about :2153) are history and stay.

Why: 027 documents the code, and the code's comments may repeat it
(027-04's decision): a comment that names a mechanism that is gone
misleads the next reader of the writer or of its tests.

Frans: none.

Done when: each comment above says what the code does since format 8,
with the old mechanism named as history where it helps ("until record
format 8, ..."); comments only, unless `KeyNode.check` is tightened; a
grep of `java/` for `rule O`, `time split`, `space split`, `take-back`,
`deleteUpward`, `handleFullNode`, `KeyAccessPath` finds only history;
`java/before-commit.sh` BEFORE COMMIT OK (diff -w shows comments only).

First step: the grep above, from `java/src` and `java/stress`.


Log
---

2026-11-19. Registered by an agent of coord-1118 while bringing 027 up
to date with PE (branch `027-pe`).

2026-11-19. Checked the listed comments against PE and updated the stale
ones for record format 8. Kept the old mechanisms as explicit history,
including the historical threshold assertions. KeyNode.check(int) still
allows B + 1; its comment states PE's B-klong limit. Db's
value-transformation comment already described the touch's counts only.
The named grep in java/src and java/stress now finds only history;
java/src-dev's example also names its split as history. Java executable
text is unchanged. The whitespace and ordinary diff statistics match.
java/before-commit.sh: BEFORE COMMIT OK (86 s), on the final comments.
