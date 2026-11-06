019-31. Investigate: whole records cut out of a stream's middle pass a start undetected
======================================================================================

Status: open. Kind: Investigate. Frans: decision.
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

Frans: a decision, after the investigation:

* (a) outside the fault model for 2026.3, as 015-73 and (if chosen)
  019-30: the harness counts such copies as known to pass undetected;
* (b) a cheap check that the investigation finds (such as: a `topPos`
  or a got-dirty position names a node of the right id and type, inside
  the stream), with a test that fails before it, `BEFORE COMMIT OK`, and
  the stream's bytes unchanged.

Recommendation: investigate first; (b) if a check of a few lines catches
it without reading records before the startup section (007's bounded
startup), else (a).

Done when: the cause is written here, Frans has chosen, and the harness's
skip list line "019-31" is gone (fixed, or moved to `KNOWN`).

First step: `CorruptStreamTester.cutOut` on the `all` original of seed 1
(`CorruptStreamTester.write(ALL, 1 * 31 + "all".hashCode())`), bytes 264
to 7392, started with a print of the start's `StartInfo` and of the
top node it takes.


Log
---

2026-11-06. Registered in night 006-12 by the agent of harness 6.1
(018-07), with the line "019-31" in `CorruptStreamTester.SKIP`.
