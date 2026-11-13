# 026-10. The node-id cache after back to empty

Created 2026-11-13 by Frans Lundberg. Status: open (registered).

For release 2026.6, found by 026-07: with the write buffer no longer a
fixed 10 MB on both sides, G4 and G5 (024-30, the count gates' heap
after back to empty) showed an emptied database holding 2.0 (G4) and
3.7 (G5) times its twin's heap. Most of it is `NodeCollection.idByPos`,
an LRU map of node ids by stream position of up to 100,000 entries
(boxed `Long` to `Long`), which still holds about 49,000 entries
(4.4 MB) after back to empty, plus about 2.2 MB of `long[]` not traced.
By the rule that a deleted KV eventually costs nothing (020-30), an
emptied database should hold about what a new one holds.

Until this is done, G4 and G5 compare each heap plus the 10 MB they were
calibrated with (`CountGates.BUFFER`; Frans, 2026-11-13, 09:48, 026-07's
Q4: "ok"); after it, they gate the plain heaps.

Done when: G4 and G5 pass on the plain heaps; the 2.2 MB of `long[]`
traced (fixed here or named); before-commit, level1, count-gates.

First step: find what keeps `idByPos`'s entries after back to empty
(positions below the first position kept after a cut cannot be read
again, so their entries can go at the cut), and trace the `long[]`.
Keep it simple (Frans, 10:06, on 026-07's Q2: "KISS. Complexity and code
size are costs too.").


Log
---

2026-11-13. Registered by coord-1113 (026-07's Q4; Frans, 09:48).
