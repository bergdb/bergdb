028-63. Investigate: week.sh's large reclaim run: the fresh fill is 3.4 times 028-43's
=====================================================================================

Status: in progress. Kind: Investigate. Frans: none.
Created 2026-11-25 by Frans Lundberg.

What: `week.sh` on `main` at `09bf9efb` (2026-11-25, step
large-reclaim, `java/stress/large.sh` full, seed 20782, 10,000,000
keys): the fresh fill reached a stream of 7,244,195,488 bytes, and the
run failed its first check, "fresh database is too large for the fixed
space envelope" (`LargeReclaimRun.fill`: 8 L0 + 2 GB must be below the
40 GB cap). 028-43's full run of 2026-11-21 (seed 20778, the database
at `40cb9ae9`) filled 2,106,983,240 bytes. The fill writes the same
10,000,000 puts of 8-byte keys and 64-byte values in transactions of
100, in an order that the seed gives, with no reclaim.

Why: the same fill writing 3.4 times the bytes is either the seed (the
order of the keys) or a change of the database since `40cb9ae9` that
writes more index nodes for the same puts: a large rise of the write
amplification at 10 million keys, where BergDB is meant to be best
(Frans: optimize for large databases). The stream's bytes are
deterministic (010-01, P2), so the lengths compare exactly.

Frans: none.

Done when: the fill's length at 10,000,000 keys for seeds 20778 and
20782 on `40cb9ae9` and on `main`; if `main` writes more for the same
seed, the commit that raised it found by bisection (the fill only), the
cause named, and a 028 entry for the fix (or the reason it stays); if
the seed alone explains it, the harness's envelope or its choice of
orders fixed so that every seed passes, with `java/stress/large.sh
quick` passing.

First step: 028-43, sections on the space envelope and the full run;
`LargeReclaimRun.fill` and `keyAt`; a probe or a mode of the runner that
stops after the fill and prints the length.


Log
---

2026-11-25. Registered by lead-1125, from `week.sh`'s report
(2026-11-25-1409); taken by an agent of lead-1125.
