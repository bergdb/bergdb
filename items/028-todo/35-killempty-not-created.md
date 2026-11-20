028-35. Fix: the user app KillEmpty and a kill during a database's creation
===========================================================================

Status: open. Kind: Fix. Frans: none.
Created 2026-11-20 by Frans Lundberg.

What: in `week.sh short` on 2026-11-20 (030-30's gates), the user app
KillEmpty (`java/stress/apps/b5-kill/KillEmpty.java`) failed its final
check when a kill cut a database's creation: a start of such a directory
throws `DatabaseNotCreatedException`, which KillEmpty does not handle,
where Kill (`a4-kill/Kill.java`) and Buffers (`b3-buffers`) do. A fault
of the app, not of the database, as far as known.

Why: a false failure of week.sh's apps costs a week's result and hides
real ones.

Frans: none.

Done when: KillEmpty treats a database whose creation a kill cut as Kill
does (and checks that the refusal is the expected one); a run that hits
the case, or a test of it; `java/before-commit.sh` BEFORE COMMIT OK; the
apps' kill round OK.

First step: compare KillEmpty's start and final check with Kill.java, line
172.


Log
---

2026-11-20. Registered by coord-1120, from 030-30's report.
