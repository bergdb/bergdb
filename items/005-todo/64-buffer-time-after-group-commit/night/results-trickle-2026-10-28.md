005-64: trickle and idle on F53, 2026-10-28 19:59 to 20:23
==========================================================

`night/trickle.sh` on `main-bf9fc7f`, 2 rounds; quietness not checked.
Summary by `tools/trickle-table.py` (CHECK OK, 4 rows); the raw output is
not kept here.

Medians of up to 2 rounds (range when wider than 15 %). Wake-ups, CPU and energy from proc_pid_rusage over the window; the consumer's CPU and the forces from the probe over the whole phase.

Trickle: small transactions, no sync, at the rate of the first column.

| process | runs | transactions/s | wake-ups/s | pkg idle wake-ups/s | CPU ms/s | energy uW | consumer CPU ms/s | forces/s |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| database, 20 ms | 2 | 10.0 | 85 | 3 (0–6) | 21.58 (17.93–25.23) | 1316 | 9.85 (8.21–11.49) | 10.0 |
| database, 50 ms | 2 | 10.0 | 84 | 2 (0–3) | 23.66 (18.13–29.19) | 1303 | 11.15 (8.55–13.75) | 10.0 |
| database, 100 ms | 2 | 10.0 | 65 | 1 (0–2) | 20.02 (16.67–23.37) | 1299 | 7.79 (6.59–8.99) | 7.5 |

Idle: after the trickle, nothing written.

| process | runs | wake-ups/s | pkg idle wake-ups/s | CPU ms/s | energy uW | consumer CPU ms/s | forces/s |
|---|---:|---:|---:|---:|---:|---:|---:|
| database, 20 ms | 2 | 25 | 0 (0–0) | 1.70 (1.26–2.14) | 50 | 0.01 | 0.01 |
| database, 50 ms | 2 | 25 | 0 (0–1) | 1.83 (1.25–2.40) | 52 | 0.01 (0.01–0.01) | 0.01 |
| database, 100 ms | 2 | 25 | 0 (0–0) | 2.60 (2.32–2.87) | 51 | 0.01 | 0.01 |
| JVM only, no database | 2 | 25 | 0 | 2.29 | 49 | 0.00 | 0.00 |
