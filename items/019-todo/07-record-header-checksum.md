019-07. Implement: a checksum of the record header, at the next RECORD_FORMAT change
====================================================================================

Status: waiting (for the next change of the record format). Kind:
Implement. Frans: decision.
Created 2026-11-05 by Frans Lundberg.

Not for 2026.3, and not before a change of `RECORD_FORMAT` is planned:
Frans took it for that change, with 015-73's option (a) (2026-11-05,
15:35). It is his exception to the rule that an open entry is done before
the next release.

What: a checksum of a record's header, written by
`StoredTrans.Serializer` and checked by `StoredTrans.Parser.parse`. The
header is 32 bytes: the size (4 bytes), the format byte, 3 unused bytes,
the time, `startupPos` and `topPos` (8 bytes each). No checksum covers it
today; the nodes have their own (`NodeChecksum`). The 3 unused bytes after
the format byte can hold the checksum, such as a 16-bit one like a
node's. A new `RECORD_FORMAT` (6), since a stream of format 5 has zeros
there; a start refuses a stream of another format.

Why: 015-73 (016-06's R6-F2). A last record's startupPos damaged to the
exact start of an earlier record that the take never reached passes the
checks of 015-72 and 015-75, and the start succeeds without the
transactions before it. A checksum of the header catches that, and any
other damaged header field too: the time (005-75) and the size (015-72).
It catches random damage, a flipped bit or a torn write; a change made
with the checksum made right again, as harness 6.1's copies are (018-01,
section 6.1), stays outside the fault model.

Why (a) was chosen for 2026.3, and not this:

* A start uses only the last record's startupPos
  (`Db.getStartupPosFromLastTransaction`).
* A cut of the stream's tail, the crash contract's damage (prefix
  interruption, 014-01, section 7), never changes it: a torn last record
  is completed as an aborted one, and the record before it is used.
* After 015-72 and 015-75 only an exact landing on an earlier record's
  start gets through.
* The other option, (b), a check that reads back before the section,
  works against the bounded startup (007), which reads only the section,
  and covers one field only.
* No format change is planned now: 015-87 kept its settings in an
  internal KV instead.

Frans: a decision. The checksum is a change of the stream format, and
needs his approval (018-01, section 2): the proposal, written here when a
change of `RECORD_FORMAT` is planned, says which bytes, which sum and how
a start refuses a wrong one. The C clone (012) follows.

Done when: Frans has approved the format change; a test with a record
whose header has a damaged field (R6's startupPos probe among them) is
refused at a start, and fails on the code before the change; the change
is in `main` after `before-commit.sh` and the level script of the
mechanism (AGENTS.md); `releases/next.md` has its line under Format; the
entry becomes a folder that keeps StreamDigest's digests before and
after (018-01, section 2).

First step: when a change of `RECORD_FORMAT` is planned, write the
proposal here and ask Frans; until then, nothing.


Log
---

2026-11-05. Registered in night 006-12, at Frans's decision on 015-73
(15:35, to session bergdb-a2: "Yes. Go ahead.", to "do you take (a),
plus a 019 entry for (c)?").
