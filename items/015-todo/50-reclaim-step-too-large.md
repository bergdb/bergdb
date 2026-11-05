015-50. Fix: a reclaim step that rewrites old values beyond the value limit fails the database, at every restart
================================================================================================================

Status: done 2026-11-05, night 006-12. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

After release 2026.2 (a known issue of it); in 2026.1 too.

What: review R7's finding R7-F1 (items/016-release-2026-2/06-reviews/R7.md,
section R7-F1: where, intended, actual, effect, a proposed fix), shown by a
probe in 06-reviews/R7/. No second agent has checked it yet.

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`.

First step: verify it (016-06, section 2.6), then the probe made a test.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).

2026-11-05. Done in the night 006-12 (W1, clone `g3a`). Verified with R7's probe
made a test: at the base, the database failed at about the 400th small put ("The
transaction is too large: its values and keys take 90596 bytes in the stream, more
than 87500"), as R7-F1 says.

* Test: `Reclaim.Tester.testStepWithinValueLimit` (f-test, 0.1 s), the probe's case
  with the record limit lowered to 100 kB: ten old values of 4 kB and `/b`, whose
  node takes `valueLimit()` - 1000 bytes (a step's scan takes `/a/9` and `/b`), and
  a second run with `/b` at `valueLimit()` (alone with the step's row it passes the
  limit). Each run must make three cuts, the last past `/b`'s record, and a restart
  on a copy must take commits and read every value. Before the fix it fails with the
  message above; with the step's bound and without the exemption below, the second
  run fails ("87560 bytes ..., more than 87500"); with both it passes.
* Fix, in two parts. (1) `Reclaim.step` bounds the value nodes it rewrites by
  `StoredTrans.valueLimit()`, counted as `Db.checkSize` counts them
  (`StoredValueNode.getByteSizeLong`): a value that would take them past the limit
  ends the step before it (its `lastKey` the KV before, not the end of the scan),
  unless it is the step's first rewritten value; it is then the first of the next
  step. (2) `Db.checkSize` no longer applies to internal transactions, as
  `checkDirtyNodes` already did not: they run inside a user transaction's go point,
  where its refusal failed the database. A step's values are then within the limit,
  each value alone as its user transaction was; the step's row comes on top (its
  real size is not known to `checkSize` anyway, it is a value transformation's
  result, 015-51); the table and the settings are small. The 1/8 of the record left
  besides `valueLimit()` takes the row, as it takes a user transaction's index nodes.
* The stream's bytes (P2): a step that did not pass the limit is the same as before
  (the bound counts what `checkSize` counted, without the row's few bytes, so it
  stops a step only where `checkSize` refused it). StreamDigest `all` against the
  base: DIGESTS IDENTICAL (48 of 48). The format is unchanged.
* 010-01: no new setting, no global state, no thread; reclaim's work is as before.
  No departure.
* Javadoc of `Db.checkSize`, the step's comment, docs/levels.md (section 6, a step),
  a line in `releases/next.md` (Reliability).
* Not done: the record limit in `store()` for a step whose touch makes many index
  nodes dirty (R7: "not probed"); the take bounds the index nodes it adds to the
  record by what is left of the limit, so it was not pursued.
