028-65. Investigate: a database not written to keeps several times its live values
==================================================================================

Status: open. Kind: Investigate. Frans: none.
Created 2026-11-26 by Frans Lundberg.

What: a database written only while its stream is below twice the
startup distance, then left to `maintain()`'s calls, keeps the stretch
of its one reclaim iteration for good: the values rewritten, and the
index nodes that the calls' takes wrote there, most of them replaced
since. 031-03, section 9.3: `IdleShapeProbe 3000 2 100 50000000 20`
(3,000 values of 100 bytes overwritten 20 times, sd 50 MB, 40 R of
calls) keeps 3,256 kB under 031-03's design and 3,245 kB on `main`, 7.0
times the stream of the same values put once. A space cost, not a
released bug: no promise of the README or the Javadoc is broken (the
Javadoc promises about 400 kB only for an emptied database; Frans,
2026-11-26).

Why: the space amplification of a database not written to, the stream
kept over its live bytes, is what an application that calls
`maintain()` while idle expects to come down. For a database not
written to for longer than R, the stream kept beyond the live bytes is
exactly what reclaim could give back (031-04, section 2).

Done when: kept / live measured on `main` and on the design of
`maintain()` that Frans chooses (031-04, the study of `maintain(int
budget)`, whose passes cut at their own start, is expected to remove
it): the review's case and a sweep of sizes, value sizes, node sizes
and startup distances; if the chosen design leaves a ratio well above
about 2 after its calls, the cause and a fix as a 028 entry, or the
reason it stays, written here.

First step: 031-03, sections 9.3 and 7 (`IdleShapeProbe`); 031-04's
measurements of 9.3 (asked of its study).


Log
---

2026-11-26. Registered by lead-1126, from 031-03, section 9.3 (Frans:
a 028 entry, not a released bug).
