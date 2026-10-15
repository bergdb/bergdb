### Session 506510d9-dd36ba4-20261014T112710-quick-g1-8g-baseline1  (506510d9196bbf940a8bf6f4df3d5571699e845b + working-tree diff)

#### r-1k-fin  [restart, 3 runs, workload 57e71d6450818537+c2a684be74cb422d]
| metric | n | median | min | max | CV |
|---|---|---|---|---|---|
| first_gets.max_us | 3 | 145.3 | 110.9 | 165.3 | 19.6% |
| first_gets.mean_us | 3 | 2.993 | 2.963 | 3.011 | 0.8% |
| first_gets.p50_us | 3 | 0.7510 | 0.7510 | 0.7910 | 3.0% |
| first_gets.p95_us | 3 | 11.967 | 11.775 | 12.159 | 1.6% |
| first_gets.p999_us | 3 | 27.263 | 25.471 | 27.903 | 4.7% |
| first_gets.p99_us | 3 | 14.463 | 14.399 | 14.527 | 0.4% |
| gclog.pause.max_ms | 3 | 86.723 | 83.569 | 94.828 | 6.6% |
| gclog.pause.total_ms | 3 | 134.4 | 132.1 | 143.1 | 4.3% |
| gclog.safepoint.max_ms | 3 | 86.810 | 83.639 | 94.909 | 6.6% |
| gclog.safepoint.total_ms | 3 | 134.7 | 132.5 | 143.5 | 4.2% |
| heap.after_gc_mb_max | 3 | 146.8 | 142.6 | 146.8 | 1.7% |
| mix.commit.append.max_us | 3 | 83,736.9 | 37,520.3 | 86,917.2 | 39.8% |
| mix.commit.append.mean_us | 3 | 22.518 | 22.248 | 23.131 | 2.0% |
| mix.commit.append.p50_us | 3 | 12.223 | 12.159 | 12.479 | 1.4% |
| mix.commit.append.p95_us | 3 | 77.311 | 76.799 | 81.407 | 3.2% |
| mix.commit.append.p999_us | 3 | 175.1 | 160.8 | 185.3 | 7.1% |
| mix.commit.append.p99_us | 3 | 112.1 | 111.1 | 119.3 | 3.9% |
| mix.commits_per_s | 3 | 42,814.8 | 41,219.9 | 43,274.4 | 2.5% |
| mix.get.max_us | 3 | 86,852.8 | 83,668.1 | 94,938.6 | 6.6% |
| mix.get.mean_us | 3 | 1.119 | 1.091 | 1.187 | 4.4% |
| mix.get.p50_us | 3 | 0.8350 | 0.8350 | 0.8750 | 2.7% |
| mix.get.p95_us | 3 | 1.959 | 1.959 | 2.175 | 6.1% |
| mix.get.p999_us | 3 | 16.383 | 16.383 | 17.535 | 4.0% |
| mix.get.p99_us | 3 | 4.351 | 4.351 | 4.479 | 1.7% |
| mix.gets_per_s | 3 | 1,624,720 | 1,533,640 | 1,675,950 | 4.5% |
| mix.puts_per_s | 3 | 42,814.8 | 41,219.9 | 43,274.4 | 2.5% |
| prepare.commit.append.max_us | 3 | 276,077.0 | 266,110.0 | 277,110.0 | 2.2% |
| prepare.commit.append.mean_us | 3 | 17.550 | 17.371 | 17.606 | 0.7% |
| prepare.commit.append.p50_us | 3 | 10.687 | 10.623 | 10.687 | 0.3% |
| prepare.commit.append.p95_us | 3 | 56.319 | 55.807 | 56.575 | 0.7% |
| prepare.commit.append.p999_us | 3 | 135.2 | 132.1 | 143.4 | 4.3% |
| prepare.commit.append.p99_us | 3 | 79.359 | 78.335 | 79.359 | 0.7% |
| rss_mb_max | 3 | 1,971.0 | 1,945.4 | 1,978.0 | 0.9% |
| second_gets.max_us | 3 | 45.750 | 40.292 | 2,368.4 | 164.1% |
| second_gets.mean_us | 3 | 0.6495 | 0.6452 | 0.7357 | 7.5% |
| second_gets.p50_us | 3 | 0.5830 | 0.5830 | 0.5870 | 0.4% |
| second_gets.p95_us | 3 | 0.8750 | 0.8350 | 1.335 | 27.4% |
| second_gets.p999_us | 3 | 4.959 | 4.927 | 5.087 | 1.7% |
| second_gets.p99_us | 3 | 3.551 | 3.343 | 3.679 | 4.8% |
| startup.sec | 3 | 0.7020 | 0.6825 | 0.7160 | 2.4% |
  longest GC pauses of run1 (3 in the window, total 134.4 ms): 83.6 ms (Pause Young (Normal) (G1 Evacuation Pause) at uptime 8.5 s); 33.7 ms (Pause Young (Normal) (G1 Evacuation Pause) at uptime 3.9 s); 17.2 ms (Pause Young (Normal) (G1 Evacuation Pause) at uptime 2.0 s);

#### read-1k  [read, 3 runs, workload 54f8384ff215e80c]
| metric | n | median | min | max | CV |
|---|---|---|---|---|---|
| gclog.pause.max_ms | 3 | 0.0000 | 0.0000 | 0.0000 | - |
| gclog.pause.total_ms | 3 | 0.0000 | 0.0000 | 0.0000 | - |
| gclog.safepoint.max_ms | 3 | 0.0000 | 0.0000 | 0.0000 | - |
| gclog.safepoint.total_ms | 3 | 0.0000 | 0.0000 | 0.0000 | - |
| get_historical.get.max_us | 3 | 169.0 | 49.958 | 1,928.1 | 146.9% |
| get_historical.get.mean_us | 3 | 0.8356 | 0.8323 | 0.8611 | 1.9% |
| get_historical.get.p50_us | 3 | 0.7510 | 0.7110 | 0.7510 | 3.1% |
| get_historical.get.p95_us | 3 | 1.543 | 1.503 | 1.583 | 2.6% |
| get_historical.get.p999_us | 3 | 5.215 | 5.087 | 5.215 | 1.4% |
| get_historical.get.p99_us | 3 | 3.583 | 3.263 | 3.679 | 6.2% |
| get_historical.ops_per_s | 3 | 1,098,460 | 1,089,740 | 1,130,200 | 1.9% |
| get_latest.get.max_us | 3 | 43.541 | 35.417 | 124.9 | 72.8% |
| get_latest.get.mean_us | 3 | 0.7884 | 0.7873 | 0.8403 | 3.8% |
| get_latest.get.p50_us | 3 | 0.7110 | 0.6670 | 0.7510 | 5.9% |
| get_latest.get.p95_us | 3 | 1.503 | 1.463 | 1.503 | 1.6% |
| get_latest.get.p999_us | 3 | 5.151 | 5.087 | 5.215 | 1.2% |
| get_latest.get.p99_us | 3 | 3.503 | 3.471 | 3.599 | 1.9% |
| get_latest.ops_per_s | 3 | 1,144,930 | 1,122,670 | 1,167,840 | 2.0% |
| get_latest_mt4.ops_per_s | 3 | 2,403,910 | 2,395,180 | 2,419,390 | 0.5% |
| get_longkey.get.max_us | 3 | 3,353.4 | 46.334 | 6,693.9 | 98.8% |
| get_longkey.get.mean_us | 3 | 1.241 | 1.166 | 1.294 | 5.2% |
| get_longkey.get.p50_us | 3 | 1.127 | 1.127 | 1.167 | 2.0% |
| get_longkey.get.p95_us | 3 | 1.671 | 1.543 | 1.799 | 7.7% |
| get_longkey.get.p999_us | 3 | 5.855 | 5.631 | 5.983 | 3.1% |
| get_longkey.get.p99_us | 3 | 4.351 | 3.967 | 4.671 | 8.1% |
| get_longkey.ops_per_s | 3 | 868,595.0 | 830,267.0 | 876,723.0 | 2.9% |
| heap.after_gc_mb_max | 3 | 623.3 | 623.2 | 623.6 | 0.0% |
| rss_mb_max | 3 | 1,633.3 | 1,625.0 | 1,638.8 | 0.4% |
| scan_back.kvs_per_s | 3 | 3,695,970 | 3,623,650 | 3,696,890 | 1.1% |
| scan_back.max_us | 3 | 163.9 | 141.4 | 3,804.9 | 153.9% |
| scan_back.mean_us | 3 | 27.057 | 27.050 | 27.597 | 1.2% |
| scan_back.p50_us | 3 | 20.991 | 20.991 | 21.119 | 0.4% |
| scan_back.p95_us | 3 | 84.991 | 83.455 | 84.991 | 1.0% |
| scan_back.p999_us | 3 | 124.4 | 110.1 | 223.2 | 40.4% |
| scan_back.p99_us | 3 | 96.255 | 94.207 | 98.815 | 2.4% |
| scan_back.scans_per_s | 3 | 36,959.7 | 36,236.5 | 36,968.9 | 1.1% |
| scan_fwd.kvs_per_s | 3 | 3,525,700 | 3,485,870 | 3,561,080 | 1.1% |
| scan_fwd.max_us | 3 | 182.4 | 159.3 | 192.4 | 9.5% |
| scan_fwd.mean_us | 3 | 28.363 | 28.081 | 28.687 | 1.1% |
| scan_fwd.p50_us | 3 | 22.527 | 22.143 | 22.527 | 1.0% |
| scan_fwd.p95_us | 3 | 86.015 | 84.991 | 87.039 | 1.2% |
| scan_fwd.p999_us | 3 | 114.2 | 111.6 | 122.9 | 5.1% |
| scan_fwd.p99_us | 3 | 97.279 | 94.719 | 102.4 | 4.0% |
| scan_fwd.scans_per_s | 3 | 35,257.0 | 34,858.7 | 35,610.8 | 1.1% |
| scan_fwd_hist.kvs_per_s | 3 | 3,269,590 | 3,262,270 | 3,393,920 | 2.2% |
| scan_fwd_hist.max_us | 3 | 884.8 | 866.0 | 1,111.2 | 14.3% |
| scan_fwd_hist.mean_us | 3 | 30.585 | 29.465 | 30.654 | 2.2% |
| scan_fwd_hist.p50_us | 3 | 22.911 | 22.527 | 23.167 | 1.4% |
| scan_fwd_hist.p95_us | 3 | 90.623 | 83.967 | 92.159 | 4.9% |
| scan_fwd_hist.p999_us | 3 | 177.2 | 169.0 | 180.2 | 3.3% |
| scan_fwd_hist.p99_us | 3 | 125.4 | 125.4 | 128.0 | 1.2% |
| scan_fwd_hist.scans_per_s | 3 | 32,695.9 | 32,622.7 | 33,939.2 | 2.2% |

#### w-uni-1k-fin  [write, 3 runs, workload affdfe7d5e46a3e9]
| metric | n | median | min | max | CV |
|---|---|---|---|---|---|
| bytes_appended_per_put | 3 | 1,693.7 | 1,693.7 | 1,693.7 | 0.0% |
| bytes_appended_per_user_byte | 3 | 1.687 | 1.687 | 1.687 | 0.0% |
| commit.append.max_us | 3 | 269,981.0 | 260,022.0 | 270,859.0 | 2.3% |
| commit.append.mean_us | 3 | 17.283 | 17.179 | 17.873 | 2.1% |
| commit.append.p50_us | 3 | 10.687 | 10.623 | 10.687 | 0.3% |
| commit.append.p95_us | 3 | 55.551 | 55.295 | 56.319 | 1.0% |
| commit.append.p999_us | 3 | 127.5 | 124.4 | 141.3 | 6.9% |
| commit.append.p99_us | 3 | 77.823 | 77.311 | 79.359 | 1.4% |
| commits_per_s | 3 | 55,592.1 | 54,033.1 | 55,724.6 | 1.7% |
| disk_over_kept_max | 3 | 1.197 | 1.195 | 1.432 | 10.7% |
| disk_over_kept_mean | 3 | 1.080 | 1.078 | 1.129 | 2.6% |
| gclog.pause.max_ms | 3 | 128.9 | 122.9 | 156.9 | 13.3% |
| gclog.pause.total_ms | 3 | 319.6 | 299.5 | 521.9 | 32.4% |
| gclog.safepoint.max_ms | 3 | 128.9 | 123.0 | 157.0 | 13.3% |
| gclog.safepoint.total_ms | 3 | 319.9 | 299.8 | 522.3 | 32.3% |
| heap.after_gc_mb_max | 3 | 146.8 | 138.4 | 159.4 | 7.1% |
| kept_mb_max | 3 | 582.6 | 575.3 | 586.7 | 1.0% |
| kept_mb_mean | 3 | 455.0 | 455.0 | 455.0 | 0.0% |
| puts_per_s | 3 | 55,592.1 | 54,033.1 | 55,724.6 | 1.7% |
| rec.other_bytes_per_put | 3 | 0.0000 | 0.0000 | 0.0000 | - |
| rec.step_bytes_per_put | 3 | 432.3 | 432.3 | 432.3 | 0.0% |
| rec.table_bytes_per_put | 3 | 0.0534 | 0.0534 | 0.0534 | 0.0% |
| rec.user_bytes_per_put | 3 | 1,261.3 | 1,261.3 | 1,261.3 | 0.0% |
| rec.user_index_bytes_per_put | 3 | 182.4 | 182.4 | 182.4 | 0.0% |
| rec.user_value_bytes_per_put | 3 | 1,036.0 | 1,036.0 | 1,036.0 | 0.0% |
| restart.startup_sec | 3 | 0.6032 | 0.6003 | 0.6257 | 2.3% |
| rss_mb_max | 3 | 2,689.5 | 2,594.9 | 3,165.8 | 10.9% |
| se | 3 | 0.4458 | 0.4458 | 0.4458 | 0.0% |
| se_offered | 3 | 0.5304 | 0.5304 | 0.5304 | 0.0% |
| slowest_commit_ms | 3 | 270.0 | 260.0 | 270.9 | 2.3% |
| storage.disk_mb_max | 3 | 586.7 | 580.0 | 592.3 | 1.1% |
| user_mb_per_s | 3 | 55.814 | 54.249 | 55.948 | 1.7% |
| we | 3 | 0.5928 | 0.5928 | 0.5928 | 0.0% |
  longest GC pauses of run1 (5 in the window, total 521.9 ms): 156.9 ms (Pause Young (Normal) (G1 Evacuation Pause) at uptime 10.4 s); 149.3 ms (Pause Young (Normal) (G1 Evacuation Pause) at uptime 20.7 s); 133.6 ms (Pause Young (Normal) (G1 Evacuation Pause) at uptime 14.8 s); 42.1 ms (Pause Young (Normal) (G1 Evacuation Pause) at uptime 4.9 s); 39.9 ms (Pause Young (Normal) (G1 Evacuation Pause) at uptime 2.9 s);
  slowest commits of run1:
    260.02 ms at 3748 ms into the phase, 0 index nodes written; overlapping: none
    157.16 ms at 7838 ms into the phase, 0 index nodes written; overlapping: GC pause Pause Young (Normal) (G1 Evacuation Pause) 156.9 ms; safepoint G1CollectForAllocation 157.0 ms;
    149.61 ms at 18105 ms into the phase, 0 index nodes written; overlapping: GC pause Pause Young (Normal) (G1 Evacuation Pause) 149.3 ms; safepoint G1CollectForAllocation 149.4 ms;
    133.94 ms at 12198 ms into the phase, 1 index nodes written; overlapping: GC pause Pause Young (Normal) (G1 Evacuation Pause) 133.6 ms; safepoint G1CollectForAllocation 133.7 ms;
    48.78 ms at 6558 ms into the phase, 1 index nodes written; overlapping: none

#### w-uni-1k-inf  [write, 3 runs, workload 1e8fb7fcb249a754]
| metric | n | median | min | max | CV |
|---|---|---|---|---|---|
| bytes_appended_per_put | 3 | 1,228.1 | 1,228.1 | 1,228.1 | 0.0% |
| bytes_appended_per_user_byte | 3 | 1.223 | 1.223 | 1.223 | 0.0% |
| commit.append.max_us | 3 | 6,880.5 | 6,438.4 | 139,889.0 | 150.6% |
| commit.append.mean_us | 3 | 10.611 | 10.608 | 10.827 | 1.2% |
| commit.append.p50_us | 3 | 8.831 | 8.767 | 8.895 | 0.7% |
| commit.append.p95_us | 3 | 17.663 | 17.535 | 17.791 | 0.7% |
| commit.append.p999_us | 3 | 46.591 | 45.567 | 47.615 | 2.2% |
| commit.append.p99_us | 3 | 24.319 | 23.935 | 24.575 | 1.3% |
| commits_per_s | 3 | 87,611.0 | 87,107.2 | 87,933.3 | 0.5% |
| gclog.pause.max_ms | 3 | 152.2 | 139.7 | 152.8 | 5.0% |
| gclog.pause.total_ms | 3 | 241.1 | 223.4 | 244.5 | 4.8% |
| gclog.safepoint.max_ms | 3 | 152.3 | 139.8 | 152.9 | 5.0% |
| gclog.safepoint.total_ms | 3 | 241.4 | 223.7 | 244.8 | 4.8% |
| heap.after_gc_mb_max | 3 | 125.8 | 125.8 | 130.0 | 1.9% |
| puts_per_s | 3 | 87,611.0 | 87,107.2 | 87,933.3 | 0.5% |
| rec.other_bytes_per_put | 3 | 0.0000 | 0.0000 | 0.0000 | - |
| rec.step_bytes_per_put | 3 | 0.0000 | 0.0000 | 0.0000 | - |
| rec.table_bytes_per_put | 3 | 0.0000 | 0.0000 | 0.0000 | - |
| rec.user_bytes_per_put | 3 | 1,228.1 | 1,228.1 | 1,228.1 | 0.0% |
| rec.user_index_bytes_per_put | 3 | 149.8 | 149.8 | 149.8 | 0.0% |
| rec.user_value_bytes_per_put | 3 | 1,036.0 | 1,036.0 | 1,036.0 | 0.0% |
| restart.startup_sec | 3 | 0.7217 | 0.6992 | 0.7676 | 4.8% |
| rss_mb_max | 3 | 2,317.2 | 2,298.1 | 2,364.5 | 1.5% |
| slowest_commit_ms | 3 | 6.881 | 6.438 | 139.9 | 150.6% |
| storage.disk_mb_max | 3 | 1,453.7 | 1,450.8 | 1,454.8 | 0.1% |
| user_mb_per_s | 3 | 87.962 | 87.456 | 88.285 | 0.5% |
| we | 3 | 0.8175 | 0.8175 | 0.8175 | 0.0% |
  longest GC pauses of run1 (3 in the window, total 223.4 ms): 139.7 ms (Pause Young (Normal) (G1 Evacuation Pause) at uptime 10.2 s); 45.7 ms (Pause Young (Normal) (G1 Evacuation Pause) at uptime 5.0 s); 37.9 ms (Pause Young (Normal) (G1 Evacuation Pause) at uptime 3.1 s);
  slowest commits of run1:
    139.89 ms at 7442 ms into the phase, 0 index nodes written; overlapping: GC pause Pause Young (Normal) (G1 Evacuation Pause) 139.7 ms; safepoint G1CollectForAllocation 139.8 ms;
    13.02 ms at 26 ms into the phase, 0 index nodes written; overlapping: none
    7.31 ms at 7837 ms into the phase, 0 index nodes written; overlapping: none
    6.49 ms at 10122 ms into the phase, 1 index nodes written; overlapping: none
    5.57 ms at 4765 ms into the phase, 0 index nodes written; overlapping: none
