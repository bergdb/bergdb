028-37. Change: contractconf.sh runs the bridge checker twice
=============================================================

Status: open. Kind: Change. Frans: none.
Created 2026-11-20 by Frans Lundberg.

What: `java/stress/contractconf.sh` runs the contract checker's
`check.sh`, which runs both the contract and the bridge checker, and then
`lean/contract/bridge-check.sh` again on the same traces. The second run
is most of `night.sh`'s step 11b, about 30 minutes (noted by 030-30).

Why: time of night.sh for no extra check.

Frans: none.

Done when: each trace is checked by the bridge checker once; the fault
test of `bridge-check.sh` still runs; the step's report says the same
checks; `java/stress/level2.sh` LEVEL 2 OK and a DRY night.sh show it.

First step: read contractconf.sh around its call of bridge-check.sh and
check.sh's steps.


Log
---

2026-11-20. Registered by coord-1120, from 030-30's report.
