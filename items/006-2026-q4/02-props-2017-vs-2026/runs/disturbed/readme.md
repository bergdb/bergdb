Runs set aside
==============

These Props runs overlapped the work of the Claude session that ran the
measurements (tool calls, writing files, streaming its replies, with the
editor showing them). By that criterion, decided from the session's times and
not from the results, they are left out of the tables. Each was replaced by a
run with the session idle (`phases.sh` 6 and 7).

| Run | Overlapped |
|---|---|
| `20261019-132340-pilot-2017.txt`, `-132456-pilot-2026.txt` | the pilot, 13:23 to 13:26: the builds and writing the probe (the versions were then named 2017 and 2026; same classes as 2017-08-01 and 2026-10-19) |
| `20261019-132918-pilot-2015-12-28.txt`, `-133009-pilot-2017-07-29.txt` | the pilot of the two older versions |
| `20261019-133153-main-2017-08-01.txt`, `-133320-main-2026-10-19.txt`, `-133419-main-2026-10-19.txt` | the first three runs of phase 1, while `summary.py` was written and tried |
| `20261019-140335-parallel-2015-12-28.txt` | the first run of phase 3, while the report's first lines were written |
| `20261019-143116-parallel-2017-08-01.txt` to `-143555-parallel-2026-10-19.txt` (six) | the first six runs of the first phase 6, while the report's draft was written |

The 4-thread test, `get4t`, is the one that moved: 0.43 to 0.53 in nine of
these fourteen runs, against 0.31 to 0.39 in the runs with the session idle.
`get` was up to 16 percent slower in some; MEM and SS were the same.
