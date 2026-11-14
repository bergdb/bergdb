028-13. Decide: the startup distance's two ranges disagree
==========================================================

Status: open. Kind: Decide. Frans: decision.
Created 2026-11-14 by Frans Lundberg.

What: the Core API sets the startup distance in two places, with
different ranges and different handling of a value outside them:

* `DbBuilder.startupDistance(int)`, at make or open: 10 bytes to 10^9,
  a value outside refused with `IllegalArgumentException` (above 10^9
  since 028-12).
* `Db.setStartupDistance(int)`, on a running database: a negative value
  refused; any other value clamped to 400,000 to 10^9 bytes (twice
  `RecoverableStream.META_BLOCK_DISTANCE` to 10^9), and the clamped value
  set, with no exception (since 005-53).

So 100 kB is taken by the builder and raised to 400 kB by the setter, and
2^31 - 1 is refused by the builder and lowered to 10^9 by the setter. Both
are documented; nothing is wrong today. The Pub API takes 5 to 1,000 MB.

Why: one rule is easier to learn and to keep; the Core API's setters may
be reviewed with 2026.6's stable format (026-12).

Frans: decision. The options (coord-1114, 2026-11-14, 12:17):

* A. Leave both as they are, documented (chosen for now, Frans, 12:18).
* B. The setter refuses outside its range, as the builder does: one
  rule, but a running database's call changes behaviour; a caller that
  passes a large value to mean "as large as possible" gets an exception.
* C. The builder clamps as the setter does: one rule, but silent, and it
  undoes 028-12's choice.
* Also open in B and C: whether the builder's low end (10 bytes, which
  tests use, e.g. G4's 100 kB) should meet the setter's (400 kB).

Done when: Frans has chosen; for B or C the change, its tests and
`java/before-commit.sh` OK.

First step: list the callers of both in `java/` with the values they
pass.


Log
---

2026-11-14. Registered by coord-1114 from 028-12's landing (Frans, 12:18:
"Yes" to "pick A today and register a 028 entry").
