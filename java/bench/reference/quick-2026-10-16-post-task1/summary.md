### Session 50a2a7be-d92fa83-20261016T164646-quick-g1-8g-post-task1  (50a2a7bed6dc854eea497ac4bbeac0777d3bf6b3 + working-tree diff)

#### r-1k-fin  [restart, 3 runs, workload 57e71d6450818537+c2a684be74cb422d]
| metric | n | median | min | max | CV |
|---|---|---|---|---|---|
| first_gets.max_us | 3 | 124.8 | 117.5 | 131.2 | 5.5% |
| first_gets.mean_us | 3 | 2.691 | 2.679 | 2.708 | 0.5% |
| first_gets.p50_us | 3 | 0.7110 | 0.6670 | 0.7110 | 3.6% |
| first_gets.p95_us | 3 | 10.751 | 10.751 | 10.815 | 0.3% |
| first_gets.p999_us | 3 | 22.143 | 22.015 | 22.399 | 0.9% |
| first_gets.p99_us | 3 | 11.903 | 11.647 | 12.543 | 3.8% |
| gclog.pause.max_ms | 3 | 85.517 | 82.263 | 89.631 | 4.3% |
| gclog.pause.total_ms | 3 | 134.2 | 126.5 | 135.4 | 3.7% |
| gclog.safepoint.max_ms | 3 | 85.565 | 82.318 | 89.732 | 4.3% |
| gclog.safepoint.total_ms | 3 | 134.6 | 126.8 | 135.7 | 3.7% |
| heap.after_gc_mb_max | 3 | 151.0 | 151.0 | 151.0 | 0.0% |
| mix.commit.append.max_us | 3 | 85,741.6 | 82,437.1 | 89,773.1 | 4.3% |
| mix.commit.append.mean_us | 3 | 20.267 | 20.214 | 20.298 | 0.2% |
| mix.commit.append.p50_us | 3 | 11.455 | 11.455 | 11.519 | 0.3% |
| mix.commit.append.p95_us | 3 | 68.095 | 68.095 | 68.607 | 0.4% |
| mix.commit.append.p999_us | 3 | 144.4 | 144.4 | 145.4 | 0.4% |
| mix.commit.append.p99_us | 3 | 98.303 | 98.303 | 98.815 | 0.3% |
| mix.commits_per_s | 3 | 47,313.8 | 47,239.1 | 47,547.9 | 0.3% |
| mix.get.max_us | 3 | 85,703.7 | 82,417.3 | 89,820.5 | 4.3% |
| mix.get.mean_us | 3 | 0.9602 | 0.9581 | 0.9999 | 2.4% |
| mix.get.p50_us | 3 | 0.7950 | 0.7910 | 0.7950 | 0.3% |
| mix.get.p95_us | 3 | 1.591 | 1.543 | 1.631 | 2.8% |
| mix.get.p999_us | 3 | 14.975 | 13.695 | 18.175 | 14.8% |
| mix.get.p99_us | 3 | 3.503 | 3.471 | 3.711 | 3.7% |
| mix.gets_per_s | 3 | 1,864,460 | 1,797,470 | 1,889,000 | 2.6% |
| mix.puts_per_s | 3 | 47,313.8 | 47,239.1 | 47,547.9 | 0.3% |
| prepare.commit.append.max_us | 3 | 263,773.0 | 263,096.0 | 267,679.0 | 0.9% |
| prepare.commit.append.mean_us | 3 | 16.596 | 16.373 | 16.764 | 1.2% |
| prepare.commit.append.p50_us | 3 | 9.471 | 9.151 | 9.471 | 2.0% |
| prepare.commit.append.p95_us | 3 | 53.247 | 52.991 | 53.503 | 0.5% |
| prepare.commit.append.p999_us | 3 | 115.2 | 114.7 | 115.7 | 0.4% |
| prepare.commit.append.p99_us | 3 | 73.727 | 73.727 | 74.239 | 0.4% |
| rss_mb_max | 3 | 1,989.8 | 1,974.3 | 2,000.5 | 0.7% |
| second_gets.max_us | 3 | 24.541 | 18.292 | 49.000 | 53.0% |
| second_gets.mean_us | 3 | 0.5566 | 0.5557 | 0.6388 | 8.2% |
| second_gets.p50_us | 3 | 0.5430 | 0.5430 | 0.5870 | 4.6% |
| second_gets.p95_us | 3 | 0.7510 | 0.7510 | 0.8750 | 9.0% |
| second_gets.p999_us | 3 | 0.9190 | 0.9190 | 4.671 | 99.8% |
| second_gets.p99_us | 3 | 0.8350 | 0.8350 | 1.127 | 18.1% |
| startup.sec | 3 | 0.6545 | 0.6544 | 0.6569 | 0.2% |
  longest GC pauses of run1 (3 in the window, total 126.5 ms): 82.3 ms (Pause Young (Normal) (G1 Evacuation Pause) at uptime 8.0 s); 27.6 ms (Pause Young (Normal) (G1 Evacuation Pause) at uptime 3.7 s); 16.6 ms (Pause Young (Normal) (G1 Evacuation Pause) at uptime 1.8 s);

#### read-1k  [read, 3 runs, workload 54f8384ff215e80c]
| metric | n | median | min | max | CV |
|---|---|---|---|---|---|
| gclog.pause.max_ms | 3 | 0.0000 | 0.0000 | 0.0000 | - |
| gclog.pause.total_ms | 3 | 0.0000 | 0.0000 | 0.0000 | - |
| gclog.safepoint.max_ms | 3 | 0.0000 | 0.0000 | 0.0000 | - |
| gclog.safepoint.total_ms | 3 | 0.0000 | 0.0000 | 0.0000 | - |
| get_historical.get.max_us | 3 | 26.667 | 23.875 | 88.083 | 78.5% |
| get_historical.get.mean_us | 3 | 0.7468 | 0.7421 | 0.7838 | 3.0% |
| get_historical.get.p50_us | 3 | 0.7110 | 0.7110 | 0.7110 | 0.0% |
| get_historical.get.p95_us | 3 | 1.295 | 1.295 | 1.423 | 5.5% |
| get_historical.get.p999_us | 3 | 1.919 | 1.879 | 4.351 | 52.1% |
| get_historical.get.p99_us | 3 | 1.591 | 1.583 | 1.879 | 10.0% |
| get_historical.ops_per_s | 3 | 1,259,480 | 1,250,360 | 1,274,740 | 1.0% |
| get_latest.get.max_us | 3 | 26.334 | 25.375 | 27.792 | 4.6% |
| get_latest.get.mean_us | 3 | 0.7158 | 0.7061 | 0.7217 | 1.1% |
| get_latest.get.p50_us | 3 | 0.6670 | 0.6670 | 0.6670 | 0.0% |
| get_latest.get.p95_us | 3 | 1.335 | 1.335 | 1.423 | 3.7% |
| get_latest.get.p999_us | 3 | 1.919 | 1.919 | 2.175 | 7.4% |
| get_latest.get.p99_us | 3 | 1.631 | 1.631 | 1.751 | 4.1% |
| get_latest.ops_per_s | 3 | 1,283,300 | 1,261,160 | 1,287,390 | 1.1% |
| get_latest_mt4.ops_per_s | 3 | 3,415,780 | 3,047,680 | 3,556,180 | 7.9% |
| get_longkey.get.max_us | 3 | 31.042 | 30.834 | 52.291 | 32.4% |
| get_longkey.get.mean_us | 3 | 1.099 | 1.098 | 1.140 | 2.2% |
| get_longkey.get.p50_us | 3 | 1.087 | 1.087 | 1.127 | 2.1% |
| get_longkey.get.p95_us | 3 | 1.423 | 1.423 | 1.543 | 4.7% |
| get_longkey.get.p999_us | 3 | 2.047 | 1.839 | 4.351 | 50.8% |
| get_longkey.get.p99_us | 3 | 1.631 | 1.583 | 1.751 | 5.2% |
| get_longkey.ops_per_s | 3 | 952,357.0 | 915,452.0 | 967,552.0 | 2.8% |
| heap.after_gc_mb_max | 3 | 624.0 | 623.6 | 624.1 | 0.0% |
| rss_mb_max | 3 | 1,616.6 | 1,615.5 | 1,619.8 | 0.1% |
| scan_back.kvs_per_s | 3 | 3,875,050 | 3,791,610 | 3,923,760 | 1.7% |
| scan_back.max_us | 3 | 141.5 | 121.1 | 150.2 | 10.9% |
| scan_back.mean_us | 3 | 25.806 | 25.486 | 26.374 | 1.7% |
| scan_back.p50_us | 3 | 20.607 | 20.479 | 21.119 | 1.6% |
| scan_back.p95_us | 3 | 82.431 | 79.359 | 83.455 | 2.6% |
| scan_back.p999_us | 3 | 96.767 | 94.719 | 106.0 | 6.1% |
| scan_back.p99_us | 3 | 88.575 | 85.503 | 95.231 | 5.5% |
| scan_back.scans_per_s | 3 | 38,750.5 | 37,916.1 | 39,237.6 | 1.7% |
| scan_fwd.kvs_per_s | 3 | 3,699,150 | 3,584,220 | 3,739,720 | 2.2% |
| scan_fwd.max_us | 3 | 113.3 | 107.5 | 124.5 | 7.5% |
| scan_fwd.mean_us | 3 | 27.033 | 26.740 | 27.900 | 2.2% |
| scan_fwd.p50_us | 3 | 22.015 | 21.759 | 22.143 | 0.9% |
| scan_fwd.p95_us | 3 | 81.407 | 80.895 | 87.039 | 4.1% |
| scan_fwd.p999_us | 3 | 93.695 | 93.183 | 112.6 | 11.1% |
| scan_fwd.p99_us | 3 | 87.551 | 87.039 | 101.4 | 8.8% |
| scan_fwd.scans_per_s | 3 | 36,991.5 | 35,842.2 | 37,397.2 | 2.2% |
| scan_fwd_hist.kvs_per_s | 3 | 3,476,190 | 3,432,630 | 3,504,320 | 1.0% |
| scan_fwd_hist.max_us | 3 | 875.1 | 851.3 | 1,206.8 | 20.3% |
| scan_fwd_hist.mean_us | 3 | 28.767 | 28.536 | 29.132 | 1.0% |
| scan_fwd_hist.p50_us | 3 | 22.271 | 21.887 | 22.399 | 1.2% |
| scan_fwd_hist.p95_us | 3 | 83.967 | 81.407 | 87.039 | 3.4% |
| scan_fwd_hist.p999_us | 3 | 170.0 | 163.8 | 171.0 | 2.3% |
| scan_fwd_hist.p99_us | 3 | 123.9 | 121.9 | 126.5 | 1.9% |
| scan_fwd_hist.scans_per_s | 3 | 34,761.9 | 34,326.3 | 35,043.2 | 1.0% |

#### w-uni-1k-fin  [write, 3 runs, workload affdfe7d5e46a3e9]
| metric | n | median | min | max | CV |
|---|---|---|---|---|---|
| bytes_appended_per_put | 3 | 1,687.2 | 1,687.2 | 1,687.2 | 0.0% |
| bytes_appended_per_user_byte | 3 | 1.680 | 1.680 | 1.680 | 0.0% |
| commit.append.max_us | 3 | 270,723.0 | 267,650.0 | 274,683.0 | 1.3% |
| commit.append.mean_us | 3 | 16.609 | 16.576 | 16.709 | 0.4% |
| commit.append.p50_us | 3 | 9.279 | 9.215 | 9.343 | 0.7% |
| commit.append.p95_us | 3 | 52.991 | 52.991 | 53.247 | 0.3% |
| commit.append.p999_us | 3 | 115.7 | 115.2 | 117.2 | 0.9% |
| commit.append.p99_us | 3 | 73.727 | 73.215 | 73.727 | 0.4% |
| commits_per_s | 3 | 58,402.9 | 58,223.2 | 58,577.5 | 0.3% |
| disk_over_kept_max | 3 | 1.208 | 1.204 | 1.212 | 0.4% |
| disk_over_kept_mean | 3 | 1.074 | 1.071 | 1.076 | 0.3% |
| gclog.pause.max_ms | 3 | 140.2 | 135.5 | 143.9 | 3.0% |
| gclog.pause.total_ms | 3 | 317.5 | 308.1 | 318.3 | 1.8% |
| gclog.safepoint.max_ms | 3 | 140.2 | 135.6 | 144.0 | 3.0% |
| gclog.safepoint.total_ms | 3 | 317.9 | 308.4 | 318.7 | 1.8% |
| heap.after_gc_mb_max | 3 | 159.4 | 155.2 | 159.4 | 1.5% |
| kept_mb_max | 3 | 609.1 | 604.5 | 609.8 | 0.5% |
| kept_mb_mean | 3 | 453.9 | 453.9 | 453.9 | 0.0% |
| puts_per_s | 3 | 58,402.9 | 58,223.2 | 58,577.5 | 0.3% |
| rec.other_bytes_per_put | 3 | 0.0000 | 0.0000 | 0.0000 | - |
| rec.step_bytes_per_put | 3 | 430.0 | 430.0 | 430.0 | 0.0% |
| rec.table_bytes_per_put | 3 | 0.0555 | 0.0555 | 0.0555 | 0.0% |
| rec.user_bytes_per_put | 3 | 1,257.1 | 1,257.1 | 1,257.1 | 0.0% |
| rec.user_index_bytes_per_put | 3 | 170.7 | 170.7 | 170.7 | 0.0% |
| rec.user_value_bytes_per_put | 3 | 1,036.0 | 1,036.0 | 1,036.0 | 0.0% |
| restart.startup_sec | 3 | 0.5823 | 0.5687 | 0.5898 | 1.8% |
| rss_mb_max | 3 | 2,836.9 | 2,805.7 | 2,855.7 | 0.9% |
| se | 3 | 0.4470 | 0.4470 | 0.4470 | 0.0% |
| se_offered | 3 | 0.5319 | 0.5319 | 0.5319 | 0.0% |
| slowest_commit_ms | 3 | 270.7 | 267.7 | 274.7 | 1.3% |
| storage.disk_mb_max | 3 | 612.5 | 609.1 | 616.3 | 0.6% |
| user_mb_per_s | 3 | 58.637 | 58.456 | 58.812 | 0.3% |
| we | 3 | 0.5951 | 0.5951 | 0.5951 | 0.0% |
  longest GC pauses of run1 (4 in the window, total 308.1 ms): 135.5 ms (Pause Young (Normal) (G1 Evacuation Pause) at uptime 10.9 s); 105.5 ms (Pause Young (Normal) (G1 Evacuation Pause) at uptime 15.7 s); 36.3 ms (Pause Young (Normal) (G1 Evacuation Pause) at uptime 5.1 s); 30.8 ms (Pause Young (Normal) (G1 Evacuation Pause) at uptime 3.3 s);
  slowest commits of run1:
    267.65 ms at 3601 ms into the phase, 1 index nodes written; overlapping: none
    135.68 ms at 7973 ms into the phase, 1 index nodes written; overlapping: GC pause Pause Young (Normal) (G1 Evacuation Pause) 135.5 ms; safepoint G1CollectForAllocation 135.6 ms;
    105.78 ms at 12783 ms into the phase, 1 index nodes written; overlapping: GC pause Pause Young (Normal) (G1 Evacuation Pause) 105.5 ms; safepoint G1CollectForAllocation 105.5 ms;
    44.12 ms at 6237 ms into the phase, 0 index nodes written; overlapping: none
    36.45 ms at 2095 ms into the phase, 0 index nodes written; overlapping: GC pause Pause Young (Normal) (G1 Evacuation Pause) 36.3 ms; safepoint G1CollectForAllocation 36.3 ms;

#### w-uni-1k-inf  [write, 3 runs, workload 1e8fb7fcb249a754]
| metric | n | median | min | max | CV |
|---|---|---|---|---|---|
| bytes_appended_per_put | 3 | 1,224.1 | 1,224.1 | 1,224.1 | 0.0% |
| bytes_appended_per_user_byte | 3 | 1.219 | 1.219 | 1.219 | 0.0% |
| commit.append.max_us | 3 | 157,773.0 | 15,385.7 | 162,910.0 | 74.7% |
| commit.append.mean_us | 3 | 10.453 | 10.417 | 10.599 | 0.9% |
| commit.append.p50_us | 3 | 8.383 | 8.383 | 8.447 | 0.4% |
| commit.append.p95_us | 3 | 15.999 | 15.935 | 16.063 | 0.4% |
| commit.append.p999_us | 3 | 34.047 | 33.279 | 34.303 | 1.6% |
| commit.append.p99_us | 3 | 21.375 | 21.247 | 21.503 | 0.6% |
| commits_per_s | 3 | 90,110.1 | 89,914.4 | 90,816.1 | 0.5% |
| gclog.pause.max_ms | 3 | 161.7 | 157.6 | 162.8 | 1.7% |
| gclog.pause.total_ms | 3 | 241.7 | 241.3 | 243.7 | 0.5% |
| gclog.safepoint.max_ms | 3 | 161.7 | 157.7 | 162.8 | 1.7% |
| gclog.safepoint.total_ms | 3 | 242.0 | 241.6 | 244.0 | 0.5% |
| heap.after_gc_mb_max | 3 | 142.6 | 142.6 | 146.8 | 1.7% |
| puts_per_s | 3 | 90,110.1 | 89,914.4 | 90,816.1 | 0.5% |
| rec.other_bytes_per_put | 3 | 0.0000 | 0.0000 | 0.0000 | - |
| rec.step_bytes_per_put | 3 | 0.0000 | 0.0000 | 0.0000 | - |
| rec.table_bytes_per_put | 3 | 0.0000 | 0.0000 | 0.0000 | - |
| rec.user_bytes_per_put | 3 | 1,224.1 | 1,224.1 | 1,224.1 | 0.0% |
| rec.user_index_bytes_per_put | 3 | 138.2 | 138.2 | 138.2 | 0.0% |
| rec.user_value_bytes_per_put | 3 | 1,036.0 | 1,036.0 | 1,036.0 | 0.0% |
| restart.startup_sec | 3 | 0.6050 | 0.5941 | 0.6102 | 1.4% |
| rss_mb_max | 3 | 2,505.0 | 2,485.9 | 2,534.0 | 1.0% |
| slowest_commit_ms | 3 | 157.8 | 15.386 | 162.9 | 74.7% |
| storage.disk_mb_max | 3 | 1,445.9 | 1,445.8 | 1,448.0 | 0.1% |
| user_mb_per_s | 3 | 90.471 | 90.274 | 91.179 | 0.5% |
| we | 3 | 0.8202 | 0.8202 | 0.8202 | 0.0% |
  longest GC pauses of run1 (3 in the window, total 241.7 ms): 157.6 ms (Pause Young (Normal) (G1 Evacuation Pause) at uptime 10.8 s); 54.3 ms (Pause Young (Normal) (G1 Evacuation Pause) at uptime 5.2 s); 29.7 ms (Pause Young (Normal) (G1 Evacuation Pause) at uptime 3.2 s);
  slowest commits of run1:
    157.77 ms at 7844 ms into the phase, 0 index nodes written; overlapping: GC pause Pause Young (Normal) (G1 Evacuation Pause) 157.6 ms; safepoint G1CollectForAllocation 157.7 ms;
    12.14 ms at 3465 ms into the phase, 0 index nodes written; overlapping: none
    11.57 ms at 2556 ms into the phase, 0 index nodes written; overlapping: none
    9.66 ms at 1080 ms into the phase, 1 index nodes written; overlapping: none
    8.61 ms at 2289 ms into the phase, 0 index nodes written; overlapping: none
