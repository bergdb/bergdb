019-46. Investigate: an INV-SLOT violation in EvictionAccountingTester under load
================================================================================

Status: open. Kind: Investigate. Frans: none.
Created 2026-11-08 by Frans Lundberg.

What: one run of `java/before-commit.sh` on the night of 2026-11-08 (in
the clone of 021-09, on `main` at 559b9ac plus 021-09's change to
`PubKeys`, no Core change of the night yet) failed in
`bergdb.core.EvictionAccountingTester.testAccounting`:

    seed 2: batch 12: the audit: [INV-SLOT: node 1599105, slot 4 for node
    1599101 names 1857728, its latest version is at 1859536 (stream)]

The test runs reader threads beside eviction. It passed three times
alone and in every later gate; the failing run was under load (a load
average of about 8, with the night's parallel gates). The log:
`/Users/f/fl/bench/006-15/night/evict-accounting-flake-unit.txt`. Found by
the agent of 021-09 (coord-1108's night).

Why: INV-SLOT is one of the Core's invariants (docs/levels.md): either a
pointer of a node can name an old version of another node (a real fault
of the bug-free Core of 2026.3, a stale pointer under eviction and
concurrent reads), or the audit reads a state that is not stable (a fault
of the test). Either way it must be known before 2026.4.

Done when: the cause is found and shown (a reproduction, by load or by a
forced schedule), and fixed in the Core or in the test, with a test that
fails before the fix; the level script of the mechanism run
(`java/stress/level*.sh`); `BEFORE COMMIT OK`; a line in
`releases/next.md` if the Core changed.
