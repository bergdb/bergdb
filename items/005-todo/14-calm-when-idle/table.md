005-14: the idle cost of a database, by buffer time (tools/idle-table.py).

The fix, 2026-10-21 09:12 to 09:22 (runs-final/); cur is fdee608, before it. VS Code was in use in these windows (see its rows).

Medians of 2 rounds of 60 s (range when wider than 15 %).

| process | wakeups/s | CPU ms/s | on P-cores ms/s | consumer thread CPU ms/s | energy, uW | instructions/s |
|---|---:|---:|---:|---:|---:|---:|
| JVM only, no database | 26 | 1.39 (1.27–1.51) | 0.26 (0.23–0.30) | 0.00 | 98 (83–114) | 806,995 |
| database, 20 ms, before the fix | 187 | 5.37 | 0.90 (0.63–1.18) | 4.04 | 422 (346–499) | 3,616,994 |
| database, 20 ms, with the fix | 26 | 1.43 | 0.30 (0.26–0.35) | 0.00 | 103 | 809,928 |
| database, 100 ms, with the fix | 26 | 1.44 | 0.13 (0.08–0.18) | 0.00 | 66 (55–78) | 820,578 |

Reference processes in the same windows (all 8 windows):

| process | wakeups/s | CPU ms/s | energy, uW |
|---|---:|---:|---:|
| Dock | 0 | 0.00 | 0 |
| Finder | 0 (0–1) | 0.71 (0.52–1.56) | 26 (18–196) |
| VS Code, main process | 7 (3–13) | 14.82 (4.16–28.94) | 4632 (436–8247) |
| VS Code's Java language server (a JVM) | 6 (6–9) | 3.49 (0.23–12.78) | 3620 (6–22358) |

Before the fix, quiet machine, 08:02 to 08:14 (runs-quiet/).

Medians of 2 rounds of 60 s (range when wider than 15 %).

| process | wakeups/s | CPU ms/s | on P-cores ms/s | consumer thread CPU ms/s | energy, uW | instructions/s |
|---|---:|---:|---:|---:|---:|---:|
| JVM only, no database | 25 | 1.29 | 0.05 | 0.00 | 45 | 753,747 |
| database, 100 ms, before the fix | 56 | 2.19 | 0.07 | 1.04 | 76 | 1,305,354 |
| database, 50 ms, before the fix | 85 | 2.90 | 0.10 (0.09–0.11) | 1.76 | 107 | 1,800,535 |
| database, 20 ms, before the fix | 163 | 4.42 | 0.17 (0.15–0.18) | 3.25 | 182 | 3,164,658 |
| database, 20 ms, consumer sleeps when idle (prototype) | 25 | 1.28 | 0.04 (0.03–0.05) | 0.00 | 44 | 762,845 |

Reference processes in the same windows (all 10 windows):

| process | wakeups/s | CPU ms/s | energy, uW |
|---|---:|---:|---:|
| Dock | 0 | 0.00 | 0 |
| Finder | 0 | 0.53 (0.41–1.18) | 15 (11–64) |
| VS Code, main process | 2 | 0.96 | 25 (19–34) |
| VS Code's Java language server (a JVM) | 6 | 0.20 (0.18–0.23) | 6 (5–7) |

Before the fix, 07:40 to 07:58 (runs-busy/); round 1 began while Photos analysis (mediaanalysisd) used a core, round 3 was quiet.

Medians of 3 rounds of 60 s (range when wider than 15 %).

| process | wakeups/s | CPU ms/s | on P-cores ms/s | consumer thread CPU ms/s | energy, uW | instructions/s |
|---|---:|---:|---:|---:|---:|---:|
| JVM only, no database | 26 | 2.30 (1.87–2.81) | 0.07 (0.04–0.21) | 0.00 | 69 (66–83) | 822,917 |
| database, 100 ms, before the fix | 58 | 2.89 (2.22–3.02) | 0.10 (0.09–0.13) | 1.53 (1.07–1.59) | 99 (79–107) | 1,380,127 |
| database, 50 ms, before the fix | 95 | 5.23 (2.82–8.43) | 0.14 (0.10–0.32) | 3.57 (1.71–5.70) | 188 (105–216) | 2,173,639 (1,798,518–2,178,519) |
| database, 20 ms, before the fix | 186 | 7.27 (4.44–15.41) | 0.19 (0.15–0.56) | 5.74 (3.26–12.65) | 319 (182–360) | 3,787,396 (3,169,934–3,802,412) |
| database, 20 ms, consumer sleeps when idle (prototype) | 25 | 1.34 (1.25–1.58) | 0.05 (0.04–0.05) | 0.00 | 46 (42–51) | 766,220 |

Reference processes in the same windows (all 15 windows):

| process | wakeups/s | CPU ms/s | energy, uW |
|---|---:|---:|---:|
| Dock | 0 | 0.00 | 0 |
| Finder | 0 (0–1) | 1.14 (0.46–2.52) | 53 (12–165) |
| VS Code, main process | 2 (2–8) | 1.02 (0.92–22.87) | 82 (21–3350) |
| VS Code's Java language server (a JVM) | 6 | 0.25 (0.19–0.39) | 8 (5–33) |
