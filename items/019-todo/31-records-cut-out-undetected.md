019-31. Decide: whole records cut out of a stream's middle pass a start undetected
==================================================================================

Status: waiting. Kind: Decide. Frans: decision.
Created 2026-11-06 by Frans Lundberg.

What: a copy of a stream with a range of whole records cut out of its
middle, the records after it moved back to fill the gap, starts, holds
the last transaction by its counter, and answers other values than the
original, with no error. Harness 6.1 (018-07) found two such copies in
the sample of seed 1, both in the `all` configuration (startup distance
1 MB, so the startup pos stays 0 and the section is the whole stream; 31
records, 8,176 bytes):

```text
all, cut out, bytes 264 to 7392 cut out: undetected: holds 30 transactions by the
  counter, and /a is null, not "..."
all, cut out, bytes 720 to 7712 cut out: undetected: holds 30 transactions by the
  counter, and /a is null, not "..."
```

So the records from the first user transaction's (264) to the last but
one's (7392) were cut out, and the start took the two that were left
(the creation's and the last ones) as the database. The records' own
positions (their `startupPos`, `topPos` and got-dirty positions, and
the nodes' pointers) are absolute; after the cut they name other bytes,
and still the start found nothing wrong. Why it found nothing is the
first question: which of the last record's positions the start reads,
and why a `topPos` now past the stream's end, or at another record's
bytes, did not fail it.

Why: damage other than a cut tail is outside the crash contract, and its
detection is best effort (018-01, section 6.1; 014-01, section 7); but
018-01's goal list keeps cheap refusals of violations (015-72, 015-75,
019-01), and a position that names no node of the stream may be one.

The cause (night 006-12, 04:14, a probe on the harness's copy, bytes 264
to 7392 cut out of the `all` stream of seed 1): the stream left is a
valid stream of fewer transactions. With startup distance 1 MB the take
writes no index node: every record's `startupPos` is 0 and its `topPos`
is 160, the creation's top node in the first record, which the cut does
not touch. The start reads the section from 0, finds 3 records (the
creation's and the two after the cut, now at 264 and 584), and reruns
their transactions; their nodes' positions are computed from their own
records, and no field names a cut record. So the start holds the
creation and the last two transactions (`/d/f`, `/d/g/h` and `/x/y/z` as
the original; `/a`, `/c`, `/d/g/i`, `/k1` and `/k6`, written by the cut
records, null), with the counter of the last. Nothing in the format links
a record to the one before it (a sequence number, the previous record's
position, a running checksum), so no check of the fields that are there
can tell; a gap in the times is legal.

Frans: a decision:

* (a) outside the fault model for 2026.3, as 015-73 and (if chosen)
  019-30: the harness counts such copies as known to pass undetected;
* (b) a link between records at the next change of the record format,
  with 019-07's header checksum: the previous record's position or a
  sequence number in the header, checked at a start. A change of the
  stream format, which needs Frans's approval (018-01, section 2).

No cheap check was found: every field of the records left is right.

Recommendation: (a) for 2026.3, as 015-73; (b) considered with 019-07.

Done when: Frans has chosen, and the harness's skip list line "019-31"
is gone (moved to `KNOWN`, or fixed with (b)).

First step: Frans's decision. The probe:
`/Users/f/fl/bench/006-12/h61-patches/probe/bergdb/core/Probe31.java`
(arguments 264 7392; `-cp` the probe's directory before the jar).


Log
---

2026-11-06. Registered in night 006-12 by the agent of harness 6.1
(018-07), with the line "019-31" in `CorruptStreamTester.SKIP`.

2026-11-06, 04:14. The cause found by a probe (above): the copy is a
valid stream of fewer transactions, which no field shows; the entry
became a Decide, waiting for Frans, with (a) recommended.
