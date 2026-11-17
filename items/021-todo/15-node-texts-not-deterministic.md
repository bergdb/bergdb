021-15. Fix: a start's refusal texts name a node by its identity hash
=====================================================================

Status: done. Kind: Fix. Frans: none.
Created 2026-11-09 by Frans Lundberg.

What: three texts of `KeyNode.validateStreamNode`, which a start refuses
a stream with (`StreamFormatException`, through
`DbStarter.validateKeyNode`), name the node by `KeyNode.toString`, which
holds the last two hex digits of `Object.toString`'s identity hash: "Bad
spos of pointer 0 of node K/44 22807:36536 L ..." in one run, "K/ab" in
the next. One of them prints the whole node over many lines
(`KeyNode.print`). Two Java runs give two texts, and since 021-12 a start
reaches them (`CorruptStreamTester.testFound021_12`, the third copy).
Found by the session porting the Core to C (022), while porting 021-12:
its corrupt sets match Java's refusal texts byte for byte.

Why: a refusal's text is part of what a start does with a damaged
stream; a port of the Core (022) and a test can match it only if it is
the same in every run. A text that dumps the node is long and says no
more than the node's id and position.

Frans: none.

Done when: every refusal text of the start and of the node checks names
a node by its kind, id and position, not by its identity or a dump; the
other refusal texts of the start looked at for identity hashes and
objects without a stable `toString`; a test that fails before the fix
(the texts of 021-12's copies, exact); `BEFORE COMMIT OK` and
`java/stress/level1.sh` under the gate lock; a line in
`releases/next.md`.

First step: grep `StreamFormatException` and the texts of 019-32, 021-11
and 021-12 for `toString()`, `print()` and objects in a message.


Log
---

2026-11-09. Registered by coord-1109 from the C port's finding and taken
by its agent p15 (clone `clone-p15`).

2026-11-09. Fixed by p15: commit 39db0a8 in `clone-p15`, on main's
7e89eaa (first made as f43afa1 on ea1fa31), to land.

* Confirmed: the third copy of `testFound021_12` was refused with "Bad
  spos of pointer 0 of node K/44 22807:36536 L" and the node's 23 klongs
  on 23 more lines, in one run, and "K/ab" in the next.
* The new `Node.name(node)`: "key node I at P", "top node I at P" or
  "value node I at P", by the node's id and position. Every text that
  named a node by `toString()` or `print()` at a start or in a key node's
  check now names it so. The new texts (I the node's id, P its position,
  N the pointer's index, S its position, T the startup time):

  * `KeyNode.validateStreamNode`: `Key node I at P with size 0.`; for a
    pointer of a time after the startup time `Bad spos of pointer N of key
    node I at P: S.`; at or before it `Bad spos of pointer N of key node I
    at P: S, at or before the startup time T.`
  * `KeyNode.check`: `Bad spos of pointer N of key node I at P: S.`, `Bad
    reference of pointer N of key node I at P: R.`; `check(maxNodeSize)`:
    `Overfull node, size=Z, maxNodeSize=M, key node I at P.`
  * `DbStarter.validateNode`: `Bad spos of key node I at P.`
  * `DbStarter.checkStreamPointers`, a key node or a top node: `Unexpected
    stream pointer S, index N of key node I at P.` (`top node I at P`).
  * `DbStarter.checkPrimordialTransaction`: `Expected TopNode, got key
    node I at P.`, `Expected KeyNode, got top node I at P.` (whichever
    node it got).
  * `DbStarter.checkThatValueNodesHaveSpos`: `value node got no spos
    during startup, value node I at P.`

  The `KeyNode.check` texts are `AssertionError`s (a bug, not a
  refusal); `validateStreamNode`'s become `StreamFormatException`s with
  the same text (`DbStarter.validateKeyNode`).
* Looked at and left: every other `StreamFormatException` of the Core
  (`bergdb.core`, `bergdb.storage`) names nodes and records by numbers,
  021-11's and 021-12's texts too. The record checks of
  `DbStarter.validateTransactions` ("non-increasing tt, " and three more)
  end with `StoredTrans.toString`, which is deterministic but puts a
  record's got-dirty ids on a second line; the C port matches it already,
  so it is unchanged. `Db.parseTrans` wraps a parse's `RuntimeException`
  with its `toString()`, the JDK's text; no malformed node reaches it since
  015-07. `KeyNode.toString` itself keeps the identity hash, for debug
  printing (asserts of the writer).
* Tests, each failing before the fix: `CorruptStreamTester.testFound021_12`
  checks the three copies' refusal texts exactly ("Time not increasing,
  400, 16712050, index=13"; "Key node 22807 at 36536, before the startup
  section, has the time 16712120, after the startup time 470."; "Bad spos
  of pointer 0 of key node 22807 at 36536: -1, at or before the startup
  time 470."); `KeyNodeTester.testNodeTextsSameInEveryRun`;
  `DbStarter.testCheckStreamPointersOfKeyNode` checks its text.
* `releases/next.md`, Core API, a line.

Runs, under the gate lock (2026-11-09): on 39db0a8 (main's 7e89eaa with
the fix), `BEFORE COMMIT OK (181 s)` (unit 1549, f 86, demos) and
`java/stress/level1.sh`: `LEVEL 1 OK`; on f43afa1 (ea1fa31 with the fix)
the same, 201 s.
