028-37. Change: contractconf.sh runs the bridge checker twice
=============================================================

Status: done. Kind: Change. Frans: none.
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


Result
------

`lean/contract/check.sh` runs both checkers on each trace of a set, at
once, after their fault tests: faults.sh, faults-top.sh, and
bridge-faults.sh when a small and a reclaim trace are in
`java/build/traces/` (else it prints "(bridge-faults.sh not run ...)").
`lean/contract/bridge-check.sh` runs bridge-faults.sh under the same
condition and the bridge checker again: on a set that check.sh had
checked, nothing new.

* `java/stress/contractconf.sh` (night.sh's steps 11b and 12b): runs only
  check.sh; prints its line on bridge-faults.sh when check.sh did not run
  it, then "contract and bridge (check.sh), N s:" with check.sh's two
  summaries, `tree-SET: contract: ...` and `tree-SET: bridge: ...` (until
  now the same two lines after "contract, N s:", and the bridge's again
  after "bridge, N s:"). A failing trace is listed from both checkers'
  outputs, as before.
* `java/stress/level2.sh`, step 8b, ran the same pair on the small and
  drain sets: now check.sh alone. The check that a reclaim trace is there,
  for bridge-faults.sh, comes before it, and the step fails if check.sh
  says it did not run bridge-faults.sh, so the fault test runs as before.
  Its lines: `   tree-small: contract: ...` and `bridge: ...` for each set.
* `java/night.sh`'s header, step 11b, says so. `bridge-check.sh` is kept,
  the bridge checker alone, for a run by hand (lean/ unchanged).

Each trace is checked by the bridge checker once; the fault tests run as
before; the reports name the same checks. The time saved is the second
bridge run, which 030-30 put at about 30 minutes of step 11b; not
measured here (the medium set was not run).


Gates
-----

On the branch `028-fx1` (after 028-38 and 028-39's commits, with this
entry's change):

* `java/before-commit.sh`: BEFORE COMMIT OK (67 s).
* `java/stress/level2.sh`: LEVEL 2 OK; its step 8b ran check.sh alone,
  bridge-faults.sh included, and printed `tree-small: contract: 70
  traces ...`, `tree-small: bridge: 70 traces ...` and the same for
  drain (110 traces), 0 failures.
* `DRY=1 java/night.sh`: lists step `contract-medium sh
  stress/contractconf.sh medium` and `contract-day`, as before (status 0).
* `java/stress/contractconf.sh small 1`: CONTRACTCONF OK in 10 s, the
  report "contract and bridge (check.sh), 9 s:" with both summaries, 7
  traces each, 0 failures; bridge-faults.sh ran (no "not run" line).


Log
---

2026-11-20. Registered by coord-1120, from 030-30's report.

2026-11-20. In progress: fx1 of coord-1120, on the branch `028-fx1`.

2026-11-20. Done by fx1 of coord-1120: contractconf.sh and level2.sh run
lean/contract/check.sh alone, each trace once with each checker.
