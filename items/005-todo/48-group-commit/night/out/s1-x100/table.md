Medians of 6 runs of HEAD and 6 of the prototype (range when wider than 10 %).

Durable commits: sync(ORDINARY) after each transaction, 1 KB values (question 1).

| scenario | build | commits/s | sync p50 ms | p99 ms | max ms | forces/s | KB per force | ms per force |
|---|---|---:|---:|---:|---:|---:|---:|---:|

Writers that do not sync: one thread; x100 is 100 puts per transaction (question 2).

| scenario | build | puts/s | user MB/s | append p50 us | p99.9 us | max ms | forces/s | KB per force | ms per force | force busy |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| a-1k-x100-b20 | HEAD | 89,598 | 90.0 | 960.5 | 2572.3 (1482.8–3113.0) | 153.06 (5.42–166.42) | 45.1 | 2,327 | 15.38 (13.51–16.16) | 70 % |
| a-1k-x100-b20 | prototype | 90,534 | 90.9 | 944.1 | 2940.9 (2424.8–4112.4) | 51.26 (14.59–151.14) | 45.1 | 2,330 | 14.87 (14.31–16.08) | 68 % |
