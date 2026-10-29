007-07: the quick performance suite, 2026-10-28 night
====================================================

The comparison of `performance.sh ab` with `SUITE=quick`, run by
[run-quick.sh](run-quick.sh) on F53 from 19:13 to 19:27 on 2026-10-28:
reference `main-cefb473` (main just before 007-07), candidate
`d4b-f89846d` (007-07's code, step 3 with D4:B), 3 runs of each build per
scenario in ABBA order. The machine was not quiet (84.52 % idle CPU before
the runs, under performance.sh's 90 %; run with `FORCE=1`), so the results
are not a reference. Discussed in 007-07, section 12. The raw runs and the
per-scenario summaries (`ab.txt`, `summary-ref.txt`, `summary-cand.txt`)
stayed in the main tree's untracked `night/out/quick/`; the sessions are in
`/Users/f/fl/bench/006-09/d2-007-07/java/build/perf/runs/`.

performance.sh's comparison, verbatim (the median of 3 runs, the CV, and
the change of the candidate's median against the reference's):

```
COMPARE reference cefb473c-20261028T191355-quick-g1-8g-ref [cefb473c61ede0915e69b6a51d8f5f1d9d0f2cb3, build main-cefb473, jar 12777591]
        candidate f89846da-20261028T191355-quick-g1-8g-cand [f89846da227160851753909e9cce5ea7cb4a9487, build d4b-f89846d, jar 756a375f]
thresholds: /Users/f/fl/bench/006-09/d2-007-07/java/bench/thresholds.json (missing): {warm_read_throughput=0.05}  (NOT FROZEN: only the provisional warm-read target raises alerts)

SCENARIO r-1k-fin [restart] reference 3 runs, candidate f89846da-20261028T191355-quick-g1-8g-cand 3 runs
  metric                                       ref median  ref CV      cand median cand CV    change  status
  mix.commits_per_s                              53,420.7 0.2% n3         54,127.3 0.4% n3     +1.3%  
  mix.gets_per_s                                2,357,620 1.3% n3        2,460,360 1.7% n3     +4.4%  
  mix.puts_per_s                                 53,420.7 0.2% n3         54,127.3 0.4% n3     +1.3%  
  startup.sec                                      0.6918 0.9% n3           0.7002 0.7% n3     +1.2%  
  (36 more metrics compared, nothing to report; --all shows them)

SCENARIO read-1k [read] reference 3 runs, candidate f89846da-20261028T191355-quick-g1-8g-cand 3 runs
  metric                                       ref median  ref CV      cand median cand CV    change  status
  get_historical.ops_per_s                      1,208,380 1.5% n3        1,224,990 0.9% n3     +1.4%  
  get_latest.ops_per_s                          1,262,180 1.4% n3        1,267,990 1.1% n3     +0.5%  
  get_latest_mt4.ops_per_s                      4,252,840 1.1% n3        4,248,190 1.9% n3     -0.1%  
  get_longkey.ops_per_s                         857,252.0 3.7% n3        884,190.0 2.4% n3     +3.1%  
  scan_back.kvs_per_s                           4,057,180 2.2% n3        4,036,170 0.9% n3     -0.5%  
  scan_back.scans_per_s                          40,571.8 2.2% n3         40,361.7 0.9% n3     -0.5%  
  scan_fwd.kvs_per_s                            3,818,580 2.6% n3        3,812,810 1.3% n3     -0.2%  
  scan_fwd.scans_per_s                           38,185.8 2.6% n3         38,128.1 1.3% n3     -0.2%  
  scan_fwd_hist.kvs_per_s                       3,533,570 2.2% n3        3,442,840 3.5% n3     -2.6%  
  scan_fwd_hist.scans_per_s                      35,335.7 2.2% n3         34,428.4 3.5% n3     -2.6%  
  (42 more metrics compared, nothing to report; --all shows them)

SCENARIO w-uni-1k-fin [write] reference 3 runs, candidate f89846da-20261028T191355-quick-g1-8g-cand 3 runs
  metric                                       ref median  ref CV      cand median cand CV    change  status
  commits_per_s                                  66,622.2 0.1% n3         66,683.1 0.2% n3     +0.1%  
  puts_per_s                                     66,622.2 0.1% n3         66,683.1 0.2% n3     +0.1%  
  restart.startup_sec                              0.5954 1.0% n3           0.6196 2.0% n3     +4.1%  
  user_mb_per_s                                    66.889 0.1% n3           66.950 0.2% n3     +0.1%  
  (29 more metrics compared, nothing to report; --all shows them)

SCENARIO w-uni-1k-inf [write] reference 3 runs, candidate f89846da-20261028T191355-quick-g1-8g-cand 3 runs
  metric                                       ref median  ref CV      cand median cand CV    change  status
  commit.append.max_us                              139.8 172.8% n3         32,011.7 99.8% n3 +22806.4%  EXPLAIN (maximum much larger than the reference's)
  commits_per_s                                 103,664.0 0.4% n3        103,400.0 0.5% n3     -0.3%  
  puts_per_s                                    103,664.0 0.4% n3        103,400.0 0.5% n3     -0.3%  
  restart.startup_sec                              0.6172 1.0% n3           0.6250 0.2% n3     +1.3%  
  slowest_commit_ms                                0.1398 172.8% n3           32.012 99.8% n3 +22806.4%  EXPLAIN (maximum much larger than the reference's)
  user_mb_per_s                                     104.1 0.4% n3            103.8 0.5% n3     -0.3%  
  (21 more metrics compared, nothing to report; --all shows them)

NO ALERTS
Comparison exit code 0 (0: no alerts, 1: alerts to repeat in a matched run, 3: incompatible, 4: failed or missing runs)
```

The metrics of `summary-ref.txt` and `summary-cand.txt` whose 3 runs do
not overlap, with a change of 2 % or more (median, then min..max):

| scenario | metric | main-cefb473 | d4b-f89846d | change |
|---|---|---|---|---|
| w-uni-1k-fin | commit.append.p95_us | 47.4 (47.4..47.4) | 49.9 (49.9..50.2) | +5.4 % |
| w-uni-1k-fin | commit.append.p99_us | 64.5 (64.5..64.5) | 70.1 (70.1..70.1) | +8.7 % |
| w-uni-1k-fin | commit.append.p999_us | 92.7 (92.2..92.7) | 102.9 (101.9..103.4) | +11.0 % |
| w-uni-1k-fin | rec.step_bytes_per_put | 430.0 | 462.8 | +7.6 % |
| w-uni-1k-fin | rec.user_index_bytes_per_put | 170.7 | 138.0 | -19.2 % |
| w-uni-1k-fin | rec.user_bytes_per_put | 1257.1 | 1224.2 | -2.6 % |
| w-uni-1k-fin | bytes_appended_per_put (for comparison; overlapping) | 1687.2 | 1687.1 | 0.0 % |
| w-uni-1k-fin | restart.startup_sec | 0.595 (0.594..0.605) | 0.620 (0.610..0.635) | +4.1 % |
| r-1k-fin | prepare.commit.append.p99_us | 64.3 (64.3..64.5) | 70.1 (70.1..70.1) | +9.2 % |
| r-1k-fin | prepare.commit.append.p999_us | 92.7 (91.6..92.7) | 102.4 (101.9..103.4) | +10.5 % |
| r-1k-fin | mix.commit.append.p50_us | 10.18 (10.18..10.30) | 9.60 (9.47..9.60) | -5.7 % |
| r-1k-fin | mix.commit.append.p99_us | 88.1 (88.1..90.6) | 92.2 (92.2..92.2) | +4.7 % |
| r-1k-fin | mix.commit.append.p999_us | 145.4 (145.4..148.5) | 150.5 (149.5..151.6) | +3.5 % |
| r-1k-fin | mix.get.p99_us | 1.46 (1.46..1.50) | 1.30 (1.30..1.34) | -11.5 % |
| r-1k-fin | mix.gets_per_s | 2,357,620 | 2,460,360 | +4.4 % |
| r-1k-fin | transactions rerun at the start (every run) | 32,540 | 33,355 | +2.5 % |
| w-uni-1k-inf | gclog.pause.total_ms | 243.9 (235.8..245.4) | 251.8 (245.7..254.6) | +3.2 % |

w-uni-1k-inf's slowest commit (EXPLAIN above) is a GC pause's: every run
of both builds had a G1 pause of 151 to 170 ms (gclog.pause.max_ms), and
the per-run maxima were 0.09, 0.14 and 163.96 ms (reference) and 32.01,
159.37 and 30.74 ms (candidate).
