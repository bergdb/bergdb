# 006-11 benchmark aggregates

Rates are medians of fresh JVM runs, successful transactions/s. Percentiles are medians of per-run histogram upper bounds; max is across runs.

## Main resident runs

| Workload | Serial 1 | Optimistic 1 | Optimistic 2 | Optimistic 4 | Optimistic 8 | O8 / S1 | O8 / S8 |
|---|---:|---:|---:|---:|---:|---:|---:|
| hot-r8-cpu10 | 57,428 | 57,216 | 55,061 | 56,577 | 54,621 | 0.95x | 1.07x |
| p-r1-none | 238,190 | 249,943 | 239,792 | 215,679 | 223,876 | 0.94x | 1.00x |
| p-r8-cpu10 | 53,887 | 52,291 | 87,581 | 104,427 | 97,275 | 1.81x | 1.94x |
| p-r8-cpu100 | 9,597 | 9,597 | 18,553 | 35,981 | 67,714 | 7.06x | 7.15x |
| p-r8-none | 114,026 | 113,632 | 130,956 | 125,206 | 122,586 | 1.08x | 1.14x |
| u-r8-cpu10 | 55,357 | 54,692 | 63,880 | 79,661 | 91,694 | 1.66x | 1.89x |
| u-r8-none | 108,443 | 111,675 | 112,811 | 118,385 | 122,064 | 1.13x | 1.16x |

## Main runs: eight-worker latency and fairness

| Workload | Mode | Rate | Drained rate | Attempts/commit | p99 us | Max ms | Worst worker active commits | Rate min–max | CV |
|---|---|---:|---:|---:|---:|---:|---:|---|---:|
| hot-r8-cpu10 | optimistic | 54,621 | 29,573 | 1.00067 | 31.7 | 10,258.8 | 1 | 54,337–57,369 | 2.5% |
| hot-r8-cpu10 | serial | 50,838 | 50,835 | 1.00000 | 36.9 | 121.7 | 13,700 | 50,371–52,183 | 1.5% |
| p-r1-none | optimistic | 223,876 | 223,872 | 1.00000 | 442.4 | 10.5 | 76,981 | 215,745–228,805 | 2.4% |
| p-r1-none | serial | 223,482 | 223,474 | 1.00000 | 18.4 | 33.1 | 66,901 | 205,268–225,247 | 4.1% |
| p-r8-cpu10 | optimistic | 97,275 | 97,274 | 1.00000 | 376.8 | 7.9 | 36,023 | 96,669–99,126 | 1.1% |
| p-r8-cpu10 | serial | 50,107 | 50,104 | 1.00000 | 36.9 | 87.7 | 12,822 | 49,639–50,901 | 1.0% |
| p-r8-cpu100 | optimistic | 67,714 | 67,713 | 1.00000 | 229.4 | 2.8 | 25,342 | 67,694–68,405 | 0.5% |
| p-r8-cpu100 | serial | 9,467 | 9,466 | 1.00000 | 127.0 | 1,744.9 | 203 | 9,221–9,468 | 1.2% |
| p-r8-none | optimistic | 122,586 | 122,584 | 1.00000 | 376.8 | 5.0 | 44,419 | 118,906–124,127 | 1.8% |
| p-r8-none | serial | 107,163 | 107,157 | 1.00000 | 24.6 | 38.5 | 30,446 | 106,541–107,429 | 0.3% |
| u-r8-cpu10 | optimistic | 91,694 | 91,410 | 1.00432 | 204.8 | 51.0 | 30,325 | 90,440–92,053 | 0.8% |
| u-r8-cpu10 | serial | 48,642 | 48,640 | 1.00000 | 41.0 | 134.0 | 15,064 | 48,125–50,089 | 1.7% |
| u-r8-none | optimistic | 122,064 | 121,662 | 1.00349 | 188.4 | 53.9 | 36,035 | 114,087–123,008 | 3.3% |
| u-r8-none | serial | 105,517 | 105,513 | 1.00000 | 25.6 | 51.8 | 33,390 | 96,548–106,787 | 4.4% |

## Serial-only bypass controls

| Workload | Threads | Stock | Bypass validation/recording | Bypass + no warm-up | Partial runtime stripping | Narrow gain | Stripped gain |
|---|---:|---:|---:|---:|---:|---:|---:|
| p-r1-none | 1 | 245,622 | 256,376 | 291,662 | 298,027 | +4.4% | +21.3% |
| p-r8-cpu10 | 1 | 56,298 | 59,554 | 60,375 | 61,100 | +5.8% | +8.5% |
| p-r8-cpu100 | 1 | 9,678 | 9,654 | 9,678 | 9,869 | -0.2% | +2.0% |
| p-r8-none | 1 | 115,974 | 131,262 | 128,355 | 141,847 | +13.2% | +22.3% |
| p-r8-none | 8 | 106,551 | 121,054 | 120,600 | 131,599 | +13.6% | +23.5% |

## Optimistic actions versus the stripped single-caller control

| Workload | Stripped serial 1 | Stock optimistic 4 | Ratio | Stock optimistic 8 | Ratio |
|---|---:|---:|---:|---:|---:|
| p-r1-none | 298,027 | 215,679 | 0.72x | 223,876 | 0.75x |
| p-r8-cpu10 | 61,100 | 104,427 | 1.71x | 97,275 | 1.59x |
| p-r8-cpu100 | 9,869 | 35,981 | 3.65x | 67,714 | 6.86x |
| p-r8-none | 141,847 | 125,206 | 0.88x | 122,586 | 0.86x |

## Supplementary sessions

| Session | Workload | Threads | Mode | Rate | Drained | Attempts/commit | p99 us | Max ms |
|---|---|---:|---|---:|---:|---:|---:|---:|
| eviction | file-eviction-r8 | 1 | optimistic | 20,741 | 20,741 | 1.00000 | 77.8 | 2.1 |
| eviction | file-eviction-r8 | 8 | optimistic | 39,166 | 39,166 | 1.00000 | 1,310.7 | 4.2 |
| eviction | file-eviction-r8 | 1 | serial | 19,910 | 19,910 | 1.00000 | 86.0 | 2.8 |
| eviction | file-eviction-r8 | 8 | serial | 19,137 | 19,136 | 1.00000 | 94.2 | 462.0 |
| file | file-append-cpu10 | 1 | optimistic | 55,866 | 55,867 | 1.00000 | 28.7 | 1.8 |
| file | file-append-cpu10 | 4 | optimistic | 108,229 | 108,229 | 1.00000 | 180.2 | 10.7 |
| file | file-append-cpu10 | 8 | optimistic | 98,476 | 98,475 | 1.00000 | 376.8 | 14.3 |
| file | file-append-cpu10 | 1 | serial | 55,283 | 55,283 | 1.00000 | 28.7 | 0.7 |
| file | file-append-cpu10 | 4 | serial | 50,066 | 50,065 | 1.00000 | 36.9 | 70.5 |
| file | file-append-cpu10 | 8 | serial | 51,023 | 51,020 | 1.00000 | 34.8 | 93.5 |
| file | file-durable-cpu100 | 1 | optimistic | 174 | 174 | 1.00000 | 10,485.8 | 18.6 |
| file | file-durable-cpu100 | 4 | optimistic | 384 | 385 | 1.00000 | 16,252.9 | 26.0 |
| file | file-durable-cpu100 | 8 | optimistic | 770 | 771 | 1.00000 | 18,874.4 | 32.8 |
| file | file-durable-cpu100 | 1 | serial | 177 | 177 | 1.00000 | 11,010.0 | 24.9 |
| file | file-durable-cpu100 | 4 | serial | 380 | 380 | 1.00000 | 16,252.9 | 23.7 |
| file | file-durable-cpu100 | 8 | serial | 763 | 762 | 1.00000 | 16,777.2 | 27.9 |

Verified result files: 276. Summary script SHA-256: 0790c4cebe1338f37de1751fb3719de2e029927ff887ef7ae776eb92cba65f65.
