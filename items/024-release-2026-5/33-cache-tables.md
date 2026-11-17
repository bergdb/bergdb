# 024-33. The cache's tables shrink (ST6)

Created 2026-11-12 by Frans Lundberg. Status: done (2026-11-12): on
`main` since `75baf383`.

Frans, 2026-11-12, 12:10, for release 2026.5: ST6 "As recommended" (fix
it). ST6 (024-05, section 3; 023-08, section 4): after a fill and a mass
delete, the node table's maps keep their peak size. 024-30's G4 (back to
empty at 1M keys) measured 226,400 slots against a hello-world twin's
60,272 (3.76 times) and printed it as a known failure.

Done by the agent "tidy" of the day's coordinator, in its own clone; the
other agents of the day ("pace", 024-31; "maint", 024-32) work elsewhere:
this item touches `Cache3` and G4's ST6 lines in `CountGates` and
`count-gates.sh` only.


## 1. In short

* **The mechanism.** The node table is 4,096 `java.util.HashMap`s
  (`Cache3`), and HashMap only doubles its table, never halves it. Now a
  removal that leaves a map's entries under 1/8 of its capacity replaces
  the map by a copy with a capacity of the least power of two at least
  twice its entries (at least 16). HashMap grows it again above 3/4.
* **Hysteresis.** After a grow or a shrink a map is 1/4 to 1/2 full; only
  a change of its entries by a factor of at least 1.5 up or 2 down
  resizes it again. A shrink copies fewer than capacity / 8 entries and
  follows more than capacity / 8 removals since the last resize, so its
  cost is O(1) a removal, amortized, and at most one map (1/4,096 of the
  table) is copied at a time, under that map's lock.
* **No stream bytes change**; nothing in the Lean model has a capacity.
* **G4's ST6** now counts by default (the known-failure path removed):
  63,744 slots against the twin's 60,272, 1.058 times (024-30: 226,400,
  3.76 times). The other G4 lines as in 024-30, section 9.
* **Performance**: not worse. `performance.sh ab` of `main` against the
  change at 1M keys: warm gets (read-100, 3 runs each) get_latest +4.0 %,
  historical +0.1 %, 4 threads +3.2 %, long keys -3.2 %, all within the
  runs' spread (CV to 8 %); writes with finite retention (w-uni-100-fin,
  1 run each) +0.3 %. No alerts. A get on the hot path follows handles
  and does not touch the table, so none was expected.
* **Gates** on `ab418a6e`, 2026-11-12: before-commit OK (71 s), level1
  OK, level3 (full) OK, level4 quick OK, count-gates OK (G1 to G4, ST6
  counted). No expected value of a test changed.


## 2. What was changed

* `Cache3.Table` (new, nested): one map of the node table, its lock and
  its capacity. The lock was the HashMap itself (`getLock`); a shrink
  replaces the map, so the lock is now the Table, and every access reads
  `Table.map` under the Table's monitor (`getLock`, `handles`, `entries`,
  `nodes`, `clockStep`, `mapHandles`, `deadStep`, `internalGet`,
  `internalPut`, `internalRemove`). Memory: 4,096 Table objects of 24
  bytes, about 100 kB a database.
* `Table.capacity` follows HashMap's rule: 16 at the first put, doubled
  when a put takes the size over 3/4 of it, and what a shrink chose.
  HashMap also doubles a table under 64 slots that gets a bin of 8
  (`treeifyBin`), which the Fibonacci hashing of `mapIndex` makes rare
  (`testBinsStaySmall`); the tracked value is then below the table's,
  and the next shrink comes later than it would, never sooner. G4 reads
  the real table lengths by reflection, so it would show a drift.
* `Table.shrinkIfSparse()`: what, when, by whom. What: the test
  `entries < capacity / 8` and capacity above 16; then a new
  `HashMap(c)`, `putAll`, and the new map and capacity stored. When:
  after every removal from the map, under its Table's monitor, never
  inside an iteration of the map: `internalRemove` (eviction's `evict`,
  `dropNode`, `dropIfEmpty`) and at the end of each CLOCK step and dead
  hand step over a map (`clockStep`, `deadStep`), after their loops. By
  whom: the thread that removed, the writer or eviction.
* The order of a map's handles (`handles()`, eviction's walks) follows its
  bins, so a shrink changes it, as a grow always did. Eviction chooses by
  that order; what is written does not depend on it.
* `testTablesShrink` (unit): 300,000 handles, all but every 100th
  removed: every map at most 8 times its entries' need or at 16, the sum
  under a quarter of the peak, every handle left found; all removed: every
  map at 16; put again: the peak's capacities again.
* `CountGates` reads `Cache3.tables` and each Table's map; G4's ST6 is a
  gate like the others (`g4slots`, factor 2); `g4st6` is gone.


## 3. Measurements

**G4 at 1M keys** (`count-gates.sh` on `ab418a6e`), the cache's table
slots, the sum of the 4,096 HashMap tables' lengths, read by reflection:

| Run                      | Slots   | Over the twin |
|---|---|---|
| hello-world twin         | 60,272  | 1             |
| emptied, `main` (024-30) | 226,400 | 3.76          |
| emptied, this change     | 63,744  | 1.058         |

**Timing** (`performance.sh ab ref1446 st6a`, builds of `325bde75` and
of this change, ABBA, both slots held, `FORCE=1`: the machine was 63 to
77 % idle from system daemons, mds_stores and mediaanalysisd, so the
results are not a reference). Medians:

| Scenario, metric                  | main      | change    | Change |
|---|---|---|---|
| read-100, get_latest (3 runs)     | 850,960/s | 884,908/s | +4.0 % |
| read-100, get_historical (3 runs) | 827,431/s | 828,152/s | +0.1 % |
| read-100, get_latest_mt4 (3 runs) | 3,391,380 | 3,498,460 | +3.2 % |
| read-100, get_longkey (3 runs)    | 643,627/s | 623,255/s | -3.2 % |
| w-uni-100-fin, commits (1 run)    | 104,348/s | 104,609/s | +0.3 % |

A first read-100 run of one each showed -16 % for get_latest; the three
runs each that followed did not repeat it (one candidate run of 847k
equals the reference's runs). Sessions in the clone's
`java/build/perf/runs/` (`...T122025...` and `...T125559...`).


## 4. Questions for Frans

None.


## 5. State

PART 1 GATED, head `ab418a6e` (branch `024-33-cache-tables`), 12:45.

* Clone `/Users/f/fl/bench/2026-11-12/tidy/clone`, branch
  `024-33-cache-tables`, head `ab418a6e` (one commit on `main`
  `325bde75`).
* Done: the code, the unit test, G4's ST6 as a gate, the gates.
* Not done: nothing of the brief.
* To continue: the coordinator lands the branch. 024-34's branch
  `024-34-reclaim-reads` starts at this head.

2026-11-13. Status set after the release (coord-1113).
