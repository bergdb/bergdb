# 030-20: the commit check's cost, the summaries

Measured 2026-11-18 on s1 (2 vCPUs, 3.8 GB, Linux, OpenJDK 27, G1, assertions off), the
clone of main at 5e0e2162; made by summarize.py, perf-summary.py and jfr-share.py from the
logs in /Users/f/fl/bench/2026-11-18/cc/s1-out/ (F53). Off: -Dtranscheck=0; on:
-Dtranscheck=1. Each JVM alone on s1 (s1-run.sh's quiet check), runs in ABBA order.

The files here: CCBench.java (the driver of sets 1, 3, 4, 5), tuned/TransCheck.java (set 5's
tuned copy, for measuring only), make-jobs.sh and jobs-*.txt (the runs), run-s1.sh (copy,
start, fetch from F53) and s1-run.sh (the runner on s1), summarize.py, perf-summary.py and
jfr-share.py (this file's sections).

## Set 1: CCBench, 1M keys of 100 bytes, heap 2 GB

Runs: 4 off, 4 on.

Load (transactions of 500 puts, execute's time): off 6.3 s, on 49.4 s, ratio 7.82.

Time per operation in µs (median, range), and per transaction (median of the runs' medians):

- update, 1 a transaction: off 10.10 (8.80–10.69), on 50.81 (50.13–51.34), ratio 5.03; a transaction 6 → 43 µs
- insert, 1 a transaction: off 9.54 (8.85–10.29), on 54.83 (51.64–57.63), ratio 5.75; a transaction 7 → 47 µs
- delete, 1 a transaction: off 11.20 (9.75–12.17), on 55.07 (53.31–59.02), ratio 4.92; a transaction 8 → 49 µs
- mixed, 1 a transaction: off 9.72 (9.46–11.01), on 53.91 (50.02–55.40), ratio 5.54; a transaction 8 → 48 µs
- update, 10 a transaction: off 9.01 (8.38–9.77), on 47.53 (44.98–49.47), ratio 5.28; a transaction 84 → 446 µs
- insert, 10 a transaction: off 8.43 (8.08–10.34), on 46.76 (46.18–51.15), ratio 5.55; a transaction 80 → 439 µs
- delete, 10 a transaction: off 8.66 (8.43–8.94), on 47.20 (45.04–50.08), ratio 5.45; a transaction 78 → 448 µs
- mixed, 10 a transaction: off 8.98 (8.63–9.26), on 53.99 (50.88–56.86), ratio 6.01; a transaction 86 → 452 µs
- update, 100 a transaction: off 8.85 (8.66–10.53), on 48.15 (43.12–56.30), ratio 5.44; a transaction 865 → 4556 µs
- insert, 100 a transaction: off 7.83 (7.47–10.01), on 55.59 (54.34–61.68), ratio 7.10; a transaction 763 → 5129 µs
- delete, 100 a transaction: off 8.14 (7.87–9.30), on 49.47 (48.06–61.96), ratio 6.07; a transaction 737 → 4804 µs
- mixed, 100 a transaction: off 9.52 (9.20–11.50), on 47.80 (44.73–57.74), ratio 5.02; a transaction 899 → 4539 µs
- update, 500 a transaction: off 9.44 (8.96–9.86), on 57.40 (52.85–62.26), ratio 6.08; a transaction 4594 → 27660 µs
- insert, 500 a transaction: off 9.60 (9.21–10.34), on 60.07 (56.70–66.33), ratio 6.26; a transaction 4458 → 29133 µs
- delete, 500 a transaction: off 8.40 (7.76–10.05), on 61.03 (56.04–66.56), ratio 7.27; a transaction 3628 → 29637 µs
- mixed, 500 a transaction: off 10.23 (9.68–10.72), on 57.99 (50.75–64.39), ratio 5.67; a transaction 4879 → 28131 µs

- 1 a transaction, all kinds: ratio 5.29, the check 81 % of a commit with it
- 10 a transaction, all kinds: ratio 5.57, the check 82 % of a commit with it
- 100 a transaction, all kinds: ratio 5.85, the check 83 % of a commit with it
- 500 a transaction, all kinds: ratio 6.28, the check 84 % of a commit with it

## Set 4: CCBench, 10M keys of 8 bytes, heap 2.9 GB (2.5 GB used after the load)

Runs: 3 off, 3 on.

Load (transactions of 500 puts, execute's time): off 151.3 s, on 791.0 s, ratio 5.23.

Time per operation in µs (median, range), and per transaction (median of the runs' medians):

- update, 1 a transaction: off 23.70 (23.20–25.16), on 82.63 (78.70–97.16), ratio 3.49; a transaction 8 → 64 µs
- mixed, 1 a transaction: off 17.97 (17.77–18.09), on 79.86 (75.50–84.48), ratio 4.44; a transaction 12 → 64 µs
- update, 10 a transaction: off 16.07 (15.41–18.02), on 78.96 (73.63–85.77), ratio 4.91; a transaction 117 → 711 µs
- mixed, 10 a transaction: off 16.85 (16.59–17.81), on 72.06 (69.10–80.38), ratio 4.28; a transaction 146 → 627 µs
- update, 100 a transaction: off 20.63 (20.30–20.66), on 83.22 (82.15–101.48), ratio 4.03; a transaction 1706 → 7621 µs
- mixed, 100 a transaction: off 17.98 (16.80–19.30), on 88.88 (79.86–98.64), ratio 4.94; a transaction 1776 → 8434 µs
- update, 500 a transaction: off 23.22 (21.09–26.91), on 101.17 (96.49–124.49), ratio 4.36; a transaction 10861 → 49913 µs
- mixed, 500 a transaction: off 21.90 (19.02–22.84), on 103.89 (102.71–112.91), ratio 4.74; a transaction 10443 → 48229 µs

- 1 a transaction, all kinds: ratio 3.90, the check 74 % of a commit with it
- 10 a transaction, all kinds: ratio 4.59, the check 78 % of a commit with it
- 100 a transaction, all kinds: ratio 4.46, the check 78 % of a commit with it
- 500 a transaction, all kinds: ratio 4.54, the check 78 % of a commit with it

## Set 5: CCBench as set 1, the tuned copy of the check (tuned/TransCheck.java)

Runs: 3 off, 3 on.

Load (transactions of 500 puts, execute's time): off 6.3 s, on 37.4 s, ratio 5.95.

Time per operation in µs (median, range), and per transaction (median of the runs' medians):

- update, 1 a transaction: off 9.93 (8.76–11.16), on 38.64 (36.43–49.59), ratio 3.89; a transaction 6 → 30 µs
- insert, 1 a transaction: off 10.13 (9.34–11.44), on 40.84 (38.13–40.84), ratio 4.03; a transaction 7 → 34 µs
- delete, 1 a transaction: off 10.24 (10.21–11.11), on 44.39 (41.85–44.43), ratio 4.34; a transaction 8 → 38 µs
- mixed, 1 a transaction: off 10.78 (9.54–11.54), on 43.21 (40.15–43.80), ratio 4.01; a transaction 8 → 37 µs
- update, 10 a transaction: off 9.08 (8.67–10.20), on 39.94 (39.41–44.09), ratio 4.40; a transaction 87 → 377 µs
- insert, 10 a transaction: off 8.87 (7.98–9.87), on 39.70 (39.49–40.39), ratio 4.48; a transaction 83 → 381 µs
- delete, 10 a transaction: off 8.61 (8.18–8.73), on 40.50 (40.38–40.83), ratio 4.70; a transaction 77 → 386 µs
- mixed, 10 a transaction: off 9.22 (8.88–9.59), on 49.11 (38.34–50.70), ratio 5.33; a transaction 86 → 357 µs
- update, 100 a transaction: off 9.07 (8.96–10.10), on 47.06 (43.09–49.67), ratio 5.19; a transaction 893 → 4251 µs
- insert, 100 a transaction: off 9.09 (8.88–9.29), on 50.65 (43.53–51.56), ratio 5.57; a transaction 824 → 4272 µs
- delete, 100 a transaction: off 8.87 (8.38–8.95), on 45.90 (40.00–48.53), ratio 5.17; a transaction 749 → 4493 µs
- mixed, 100 a transaction: off 10.56 (9.70–11.82), on 44.33 (39.14–45.00), ratio 4.20; a transaction 947 → 3764 µs
- update, 500 a transaction: off 10.61 (10.56–11.58), on 48.20 (44.96–49.83), ratio 4.54; a transaction 5258 → 23462 µs
- insert, 500 a transaction: off 9.73 (9.40–10.31), on 48.67 (46.11–51.38), ratio 5.00; a transaction 4329 → 23161 µs
- delete, 500 a transaction: off 8.90 (8.38–9.55), on 51.62 (49.54–53.23), ratio 5.80; a transaction 3804 → 25054 µs
- mixed, 500 a transaction: off 10.80 (9.33–10.82), on 50.96 (50.09–54.98), ratio 4.72; a transaction 4968 → 24947 µs

- 1 a transaction, all kinds: ratio 4.07, the check 75 % of a commit with it
- 10 a transaction, all kinds: ratio 4.73, the check 79 % of a commit with it
- 100 a transaction, all kinds: ratio 5.00, the check 80 % of a commit with it
- 500 a transaction, all kinds: ratio 4.98, the check 80 % of a commit with it

## Sets 2 and 6: Perf, the suites' commit scenarios

Scenario parameters as in java/stress/performance-quick.suite and performance.suite;
heap 2 GB (2.5 GB for w-uni-100-inf; 8 GB on F53's references), so not comparable with
the references of java/bench/.

- d-1k-t1: 3 off, 3 on
  - puts/s: off 169 (155–184), on 154 (148–165), on/off 0.91
  - mean µs: off 71.4 (69.0–82.0), on 128.7 (123.3–140.4), on/off 1.80
  - p50 µs: off 59.4 (58.9–74.2), on 122.4 (114.7–130.6), on/off 2.06
  - p99 µs: off 200.7 (182.3–202.8), on 282.6 (233.5–303.1), on/off 1.41
  - durable mean µs: off 5720.1 (5251.7–6295.0), on 6310.6 (5869.3–6597.3), on/off 1.10
  - durable p50 µs: off 5144.6 (4620.3–5308.4), on 5111.8 (5013.5–5177.3), on/off 0.99
  - durable p99 µs: off 15728.6 (13434.9–18350.1), on 24641.5 (15073.3–29360.1), on/off 1.57
- d-1k-t16: 3 off, 3 on
  - puts/s: off 1249 (1122–1395), on 1418 (1288–1521), on/off 1.14
  - mean µs: off 35.3 (28.9–43.8), on 227.5 (204.2–230.0), on/off 6.44
  - p50 µs: off 21.9 (18.7–23.3), on 117.2 (100.9–122.4), on/off 5.36
  - p99 µs: off 192.5 (163.8–333.8), on 925.7 (876.5–1056.8), on/off 4.81
  - durable mean µs: off 12417.7 (11197.6–14008.2), on 11101.2 (10210.5–12230.2), on/off 0.89
  - durable p50 µs: off 11075.6 (10616.8–12386.3), on 9961.5 (9830.4–11141.1), on/off 0.90
  - durable p99 µs: off 31064.1 (27000.8–41156.6), on 30801.9 (17170.4–33161.2), on/off 0.99
- w-uni-100-inf: 3 off, 3 on
  - puts/s: off 80447 (59839–85650), on 18662 (17601–20101), on/off 0.23
  - mean µs: off 11.4 (10.8–15.1), on 52.7 (48.8–55.8), on/off 4.64
  - p50 µs: off 8.4 (8.1–10.0), on 46.3 (42.5–48.1), on/off 5.49
  - p99 µs: off 43.0 (36.6–55.3), on 108.5 (100.9–126.0), on/off 2.52
- w-uni-1k-fin: 3 off, 3 on
  - puts/s: off 54794 (48128–59656), on 18733 (18568–19657), on/off 0.34
  - mean µs: off 15.6 (14.9–18.1), on 52.0 (49.4–52.3), on/off 3.34
  - p50 µs: off 6.0 (5.7–6.0), on 37.9 (36.4–38.7), on/off 6.33
  - p99 µs: off 122.4 (115.2–123.4), on 264.2 (252.9–264.2), on/off 2.16
- w-uni-1k-inf: 3 off, 3 on
  - puts/s: off 88468 (87421–88775), on 23662 (21551–23674), on/off 0.27
  - mean µs: off 9.1 (8.9–9.3), on 41.0 (40.9–44.8), on/off 4.49
  - p50 µs: off 5.6 (5.5–5.8), on 35.3 (35.1–36.4), on/off 6.31
  - p99 µs: off 31.4 (31.2–31.5), on 88.6 (86.5–89.1), on/off 2.82

## Set 3: JFR, the check's share of one commit (1M keys, updates, the check on)

```
update, 1 a transaction: phase 11.1 s, 1007 samples of main, 992 in Db.execute, 773 in TransCheck: 78 % of execute's samples; GC pauses in the phase 411 ms
TransCheck's samples by its innermost TransCheck method:
   22.1 %  TransCheck.get
   19.8 %  TransCheck$Prefix.key
   13.8 %  TransCheck$Walk.visit
    9.7 %  TransCheck.live
    9.6 %  TransCheck.check
    5.0 %  TransCheck$Walk.interesting
    4.8 %  TransCheck.hash
    4.3 %  TransCheck.frame
    2.5 %  TransCheck.begin
    2.5 %  TransCheck$Walk.through
    1.7 %  TransCheck.compare
    1.4 %  TransCheck.snapshot
and by the class of the frame at the top of the stack:
   19.8 %  bergdb.core.TransCheck$Prefix
   19.0 %  bergdb.core.TransCheck
   16.8 %  bergdb.dag.KeyNode
   15.3 %  bergdb.dag.Handle
    8.2 %  java.util.IdentityHashMap$IdentityHashMapIterator
    8.0 %  java.util.IdentityHashMap
    5.4 %  java.util.WeakHashMap
    4.0 %  bergdb.core.TransCheck$Walk
    1.7 %  java.util.HashMap
    0.8 %  java.util.HashMap$HashIterator
    0.6 %  java.util.Arrays
    0.1 %  jdk.internal.util.ArraysSupport
update, 500 a transaction: phase 12.5 s, 1162 samples of main, 1151 in Db.execute, 963 in TransCheck: 84 % of execute's samples; GC pauses in the phase 297 ms
TransCheck's samples by its innermost TransCheck method:
   41.7 %  TransCheck$Walk.visit
   36.8 %  TransCheck.get
    5.3 %  TransCheck.frame
    3.7 %  TransCheck.live
    3.4 %  TransCheck.compare
    2.6 %  TransCheck$Walk.interesting
    2.2 %  TransCheck.hash
    1.3 %  TransCheck$Walk.through
    0.9 %  TransCheck.snapshot
    0.8 %  TransCheck.check
    0.3 %  TransCheck.nodeCheck
    0.2 %  TransCheck$KeyOf.equals
and by the class of the frame at the top of the stack:
   27.2 %  bergdb.core.TransCheck$Walk
   25.3 %  bergdb.dag.Handle
   17.3 %  bergdb.dag.KeyNode
   11.1 %  bergdb.core.TransCheck
    6.2 %  java.util.WeakHashMap
    6.0 %  java.util.IdentityHashMap
    3.2 %  java.util.HashMap
    2.4 %  java.util.HashMap$HashIterator
    0.2 %  java.util.IdentityHashMap$KeyIterator
    0.2 %  jdk.internal.util.ArraysSupport
    0.2 %  bergdb.core.TransCheck$Prefix
    0.2 %  java.util.Arrays
update, 1 a transaction: phase 2.3 s, 194 samples of main, 183 in Db.execute, 0 in TransCheck: 0 % of execute's samples; GC pauses in the phase 236 ms
TransCheck's samples by its innermost TransCheck method:
and by the class of the frame at the top of the stack:
```

The tuned copy, profiled on F53 (not quiet: the shares only), 300,000 keys:

```
update, 1 a transaction: phase 3.3 s, 259 samples of main, 256 in Db.execute, 184 in TransCheck: 72 % of execute's samples; GC pauses in the phase 117 ms
TransCheck's samples by its innermost TransCheck method:
   30.4 %  TransCheck$Walk.visit
   22.3 %  TransCheck.live
   10.9 %  TransCheck$Walk.interesting
    7.1 %  TransCheck.compare
    7.1 %  TransCheck.hash
    5.4 %  TransCheck.check
    3.3 %  TransCheck.lowerBound
    2.7 %  TransCheck.get
    2.7 %  TransCheck$Walk.through
    1.6 %  TransCheck$Walk.walk
    1.1 %  TransCheck$Walk.kidCheck
    1.1 %  TransCheck.frame
and by the class of the frame at the top of the stack:
   35.9 %  bergdb.core.TransCheck
   16.8 %  bergdb.dag.Handle
   14.1 %  bergdb.core.TransCheck$Walk
   10.9 %  java.util.IdentityHashMap
    8.2 %  java.util.HashMap
    4.9 %  bergdb.dag.KeyNode
    3.8 %  java.util.IdentityHashMap$IdentityHashMapIterator
    1.1 %  java.util.WeakHashMap
    1.1 %  bergdb.core.TransCheck$Prefix
    1.1 %  jdk.internal.util.ArraysSupport
    1.1 %  java.util.HashMap$HashIterator
    0.5 %  java.util.ArrayDeque
update, 500 a transaction: phase 2.6 s, 214 samples of main, 211 in Db.execute, 160 in TransCheck: 76 % of execute's samples; GC pauses in the phase 18 ms
TransCheck's samples by its innermost TransCheck method:
   28.1 %  TransCheck$Walk.interesting
   23.8 %  TransCheck$Walk.visit
   11.9 %  TransCheck.live
    6.9 %  TransCheck.compare
    6.2 %  TransCheck.hash
    4.4 %  TransCheck$Walk.through
    3.8 %  TransCheck$Prefix.key
    3.1 %  TransCheck.lowerBound
    3.1 %  TransCheck.get
    2.5 %  TransCheck.check
    1.9 %  TransCheck.nodeCheck
    1.9 %  TransCheck$KeyOf.<init>
and by the class of the frame at the top of the stack:
   30.0 %  java.util.IdentityHashMap
   25.0 %  bergdb.core.TransCheck
   13.8 %  java.util.HashMap
   12.5 %  bergdb.dag.Handle
    8.1 %  bergdb.core.TransCheck$Walk
    3.8 %  bergdb.core.TransCheck$Prefix
    3.1 %  bergdb.dag.KeyNode
    1.9 %  java.util.Arrays
    1.2 %  java.util.WeakHashMap
    0.6 %  java.util.HashMap$HashIterator
```

## What the check did (TransCheck's summary line, one run of each)

```
cc1m-r1-tc1: TRANSCHECK: 1069521 transactions, 36844408 nodes visited, 692098 made, 0 made or changed and not reached, 4840001 keys of the transactions, 127859142 reads, 0 faults made on purpose found; no failure
cc10m-r1-tc1: TRANSCHECK: 286881 transactions, 72778784 nodes visited, 1798669 made, 0 made or changed and not reached, 10960001 keys of the transactions, 330873570 reads, 0 faults made on purpose found; no failure
cctuned1m-r1-tc1: TRANSCHECK: 1069521 transactions, 36844408 nodes visited, 692098 made, 0 made or changed and not reached, 4840001 keys of the transactions, 127859142 reads, 0 faults made on purpose found; no failure
w-uni-100-inf-r1-tc1: TRANSCHECK: 5510001 transactions, 71780738 nodes visited, 955095 made, 0 made or changed and not reached, 6500001 keys of the transactions, 166617570 reads, 0 faults made on purpose found; no failure
```
