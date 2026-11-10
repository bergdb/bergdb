# 023-10. The ratchet test of the dirty top-node window

Created 2026-11-10 by Frans Lundberg. Status: open.

The ratchet test of 023-06, section 18.6, item 3: does the run of dirty
top nodes that a mass delete leaves in D (the window, Z13; 023-05 P6,
section 5) grow from disturbance to disturbance? Frans decided (023-08,
Q6) to leave fix (a) for later unless this test shows that it grows.
Measured on `main` (no unlink at the delete) and on `023-core` (023-09),
with the same workload on both. Work directory:
`/Users/f/fl/bench/2026-11-10/ratchet/`.

In short:

* **Bounded, not growing, on both builds.** No run shows the window
  growing from disturbance to disturbance. By Q6, fix (a) stays for
  later.
* **T4's queue has no window** on either build: it makes almost no top
  nodes. `main`: 1 dirty top node throughout; `023-core`: at most 12
  after the disturbances, its twin up to 19 (section 3).
* **T1's drive on `023-core`**: each mass delete wipes the window, and a
  new one forms in the next 1,000 to 5,000 transactions, while the
  reclaim iteration that spans the disturbance runs. Its size is set by
  that disturbance: after nine of 1M keys, 18, 9, 38, 18, 39, 9, 34, 11
  and 16 inversions (the twin 11). 99 small disturbances that leave the
  window standing add no inversions (sections 4 and 5).
* **Not within the twin's steady value** on `023-core` after a large mass
  delete: up to 152 dirty top nodes in a segment's second half against
  the twin's 48 to 66 (bound 87) after 1M keys; within after 100,000 keys or
  fewer. The same window as T1's miss at 1M (023-09, 5.1).
* **`main` cannot show it**: from the first mass delete on, its reclaim
  stops cutting, and its dirty top nodes stay below the twin's (at most
  38, 4 inversions).
* **The full run** (1M transactions, a mass delete every 200,000, both
  workloads, both builds): `night-ratchet.sh`, about 10 minutes; the
  marker `READY` is set (section 7).


## 1. The question

* **The window** (023-06, 18.1; P6, 5.1 and 5.2). After a mass delete, a
  run of consecutive top nodes stays dirty. Rule A keeps each one dirty
  through a skip target that waits in a newer got-dirty list; at an
  inversion, the newer node waits in an older list than its predecessor.
  The inversions stay frozen while new top nodes are made, so the run
  neither grows nor shrinks.
* **The risk** (P6, 5.2, "a risk not measured"): a later disturbance may
  add inversions to the run and so ratchet it up.
* **The test** (023-06, 18.6, item 3): "T4's queue for 1M transactions with
  a mass delete every 200,000, a restart after each, and a reclaim
  iteration spanning each; D's top nodes at every checkpoint within the
  twin's steady value, before and after each disturbance."


## 2. The test

### 2.1 The probe and the builds

* **The probe**: `CleanupRatchet` (`probe/CleanupRatchet.java`, about 490
  lines), made from P7's CleanupRule (023-05 P7, section 1.1: D's top
  nodes and the inversions), without the counters that only P7's branch
  has. It is in package `bergdb.core` and compiled apart against each
  build's `bergdb.jar` (into `classes-main/` and `classes-core/`), as
  023-09, section 6, did with CleanupRule. Nothing in `java/src` changes.
* **The builds**: worktrees of the clone `ratchet/clone`, each built with
  `build.sh`: `wt-main` at `main`'s `dcfe3b4f`, and `wt-core` at
  `023-core`'s `2c67f887` (branch `023-core-2c67`).
* **Settings**: T1's (023-03, section 2.1): a CutStream, a test clock of
  1 ms a transaction, R = 1 s, a startup distance of 100 kB, node size 30,
  no eviction.

### 2.2 The schedule

Two databases, one after the other, in one JVM:

* **twin**: the workload, with a restart at each disturbance point and
  nothing else.
* **dist**: the same workload; at each disturbance point a disturbance:
  n keys put, 100 a transaction, values of 100 bytes, then deleted, 100 a
  transaction, both in key order, then a restart. Each disturbance has
  keys of its own ("/k/", its number, "/", i).

Two workloads:

* **queue**: T4's (023-03, section 4.2): 1,000 live keys in time order;
  each transaction puts key i and deletes key i - 1,000.
* **drive**: T1's drive (023-03, section 2.3): overwrites of "/a.txt" with
  1,000 bytes. Added because the queue makes almost no top nodes
  (section 3); the window was found in T1's drive (P6, section 5.1).

### 2.3 The measures

* At every 10,000 transactions; at 1,000, 2,000 and 5,000 after each
  disturbance; and before the fill, after the fill, after the deletes and
  after the restart:
  * D, the dirty index nodes;
  * tops, D's top nodes; inv, the inversions (P7, 1.1); rootDirty, the
    dirty top nodes whose root is dirty;
  * made, the top nodes made (the super root's ordinal);
  * resident objects, kept bytes, the lag, reclaim's cuts.
* D, tops and inv are also sampled every 100 transactions. "Most" in the
  tables is the most sampled in a segment.
* **The reclaim iteration spanning each disturbance**: the probe prints
  the iteration in progress at the end of the deletes, with the time it
  started, and the transactions from the restart to the first cut.
* **Lookups** against a model (CleanupRule's check: 300 keys at three
  times within R, three scans) after the deletes and the restart of
  each disturbance, and at the end. No run found a wrong answer.

### 2.4 Pass and growth

* **Within** (023-06, 18.6): in every segment after a disturbance, the most
  dirty top nodes sampled at most the twin's steady most (sampled, from
  10,000 transactions on) + a_n, with 023-03's bounded allowance a_n =
  10 + h_fill (023-03, 2.6), h_fill = 7 for 1M keys (023-03, 8.1). From
  run F on, the probe measures h_fill after each fill (as CleanupRule
  does): 6 for 20,000 keys, 7 for 200,000; `summary.py` uses it.
* **Grows**: the window after a later disturbance is larger than after the
  earlier ones, disturbance after disturbance. This is what Q6 asks.


## 3. The queue: no window on either build

Runs A (300,000 transactions, a disturbance of 1M keys every 100,000) and
E (500,000, every 50,000), the workload 023-06, 18.6, names. "Most after
each" is the most dirty top nodes sampled in each segment after a
disturbance, in order.

| Run, build | Top nodes made, twin / dist | Twin, most | Most after each       | Within |
|---|---|---|---|---|
| A, main     | 1 / 3     | 1  | 1, 1                          | yes |
| A, 023-core | 98 / 103  | 19 | 12, 12                        | yes |
| E, main     | 1 / 8     | 1  | 2, 1, 1, 1, 1, 1, 1, 1, 1     | yes |
| E, 023-core | 164 / 185 | 19 | 8, 9, 8, 11, 12, 12, 7, 12, 8 | yes |

* **The queue makes almost no top nodes.** A top node is made when the
  space root splits (a time or space split, `Dag.timeSplit`,
  `Dag.spaceSplit`) or, on `023-core`, collapses. The queue changes leaves
  below a root that seldom fills: on `main` 1 top node in 300,000
  transactions; on `023-core` about 1 in 3,000 (P7, 6.4: 32 in 100,000).
  Without new top nodes no window forms (P6, 5.2: inversions are passed
  on at the rate top nodes are made).
* **On `main`**: one dirty top node, the super root, at every checkpoint,
  in the twin and after every disturbance.
* **On `023-core`**: 1 to 19 dirty top nodes in the twin and 1 to 12 after
  the disturbances, nearly all with a dirty root: the queue keeps its
  roots dirty (P7, 6.4), not the skip targets. No growth.
* **Reclaim**: on `main` the ordered queue all but stops the cuts in the
  twin already (023-03, 8.4: U16-1), and the disturbed database keeps
  0.8 GB (A) and 3.4 GB (E) from the decided cut. On `023-core` the first
  cut after each restart comes 925 to 4,363 transactions later, and the
  kept bytes stay at the twin's (1.5 MB against 1.6 MB).

So T4's queue cannot answer Q6: there is no window to ratchet. Sections 4
and 5 use T1's drive instead, which makes a top node about every 14
transactions (P6, 5.1).


## 4. T1's drive: the window forms, and each disturbance replaces it

### 4.1 Disturbances of 1M keys on `023-core`

Run C: 500,000 drive transactions, 1M keys put and deleted every 50,000,
nine disturbances. "Tops" and "inv" are the range at the checkpoints of
a segment's second half; "most" the most sampled in the segment; "cut"
the transactions from the restart to the first cut after it.

| Seg | Twin tops | Twin inv | Dist tops | Dist inv | Most | Cut   |
|---|---|---|---|---|---|---|
| 0 | 58-59 | 11 | 58-59   | 11 | 65  |  |
| 1 | 56-57 | 11 | 80-84   | 18 | 93  | 1,712 |
| 2 | 55-60 | 11 | 46-53   | 9  | 111 | 4,248 |
| 3 | 55-64 | 11 | 140-141 | 38 | 150 | 4,303 |
| 4 | 55-57 | 11 | 83-86   | 18 | 101 | 3,189 |
| 5 | 57-58 | 11 | 131-136 | 39 | 150 | 2,651 |
| 6 | 56-59 | 11 | 48-49   | 9  | 54  | 971 |
| 7 | 57-60 | 11 | 129-132 | 34 | 140 | 4,810 |
| 8 | 61-62 | 12 | 59-64   | 11 | 109 | 3,029 |
| 9 | 57-66 | 12 | 77-80   | 16 | 143 | 3,663 |

Run B (300,000, every 100,000), the same settings: 104 to 112 dirty top
nodes with 26 inversions after the first disturbance, 141 to 152 with 44
after the second (most 118 and 161; cuts 2,032 and 3,604).

* **No growth.** The inversions after the nine disturbances are 18, 9,
  38, 18, 39, 9, 34, 11 and 16: no trend, 20.8 on average for the first
  four and 21.8 for the last five. The window after a disturbance does
  not depend on how many came before. B's 26 then 44 is two draws of the
  same kind, not a ratchet.
* **Each disturbance wipes the window.** Right after the deletes, before
  the restart, D holds 1 to 3 top nodes and 0 or 1 inversion in every
  disturbance of every run. During the 20,000 transactions of the fill
  and the deletes, no drive runs and 2 or 3 top nodes are made; the take
  writes the old window's lists in order, and Rule A's chains clean.
* **A new window forms after the restart**, in the first 1,000 to 5,000
  drive transactions, while the reclaim iteration that spans the
  disturbance runs: in every disturbance an iteration was in progress at
  the end of the deletes (its tStart during the fill or the deletes),
  and its cut came 971 to 4,810 transactions after the restart. This is
  P6's account (5.2: "what formed the run at 1M"). Its size then stays
  frozen until the next disturbance: in each segment's second half the
  inversions do not change and the dirty top nodes vary by at most 11.
* **Not within the twin's steady value.** The twin's most is 70 (48 to 66
  at the checkpoints, 11 or 12 inversions); with a_n = 17 the bound is
  87. 8 of C's 9 segments and both of B's are over it, by up to 74
  (161). At the checkpoints alone, 6 of 9 (C) and 2 of 2 (B). This is the
  same window as T1's miss at 1M (023-09, 5.1: C9 over by 6), which
  023-03, section 10, accepts as a named allowance.

### 4.2 Smaller and more frequent disturbances on `023-core`

| Run | Disturbances | Dist tops | Dist inv | Within |
|---|---|---|---|---|
| D | 5 of 100,000 keys, every 50,000  | 42-63 | 7-12 | 5 of 5 |
| F | 39 of 20,000 keys, every 5,000   | 27-74 | 5-14 | 39 of 39 |
| G | 19 of 200,000 keys, every 10,000 | 32-95 | 6-20 | 15 of 19 |

* "Dist tops" and "Dist inv": the range at every checkpoint after the
  first disturbance.
* The twin in these runs: 48 to 64 dirty top nodes at the checkpoints, 11
  inversions; the bound, the twin's most sampled + a_n, is 81 or 82.
* A fill of 20,000 keys, 200 transactions, already wipes the window: 1 or
  2 dirty top nodes after every one of F's 39 deletes.
* The window that forms after a disturbance grows with its size: the
  twin's after 20,000 or 100,000 keys, up to 95 after 200,000 (G), up to
  154 at the checkpoints after 1M (B, C). It does not grow with the
  number of disturbances: G's inversions after its 19 disturbances are
  10, 15, 13, 13, 20, 9, 17, 9, 13, 11, 14, 12, 19, 18, 16, 13, 9, 12, 13.

### 4.3 `main`: reclaim stops, and the window drains

| Run | Disturbances | Dist tops | Dist inv | Cuts after the first |
|---|---|---|---|---|
| B | 2 of 1M keys, every 100,000      | 4-28 | 0-3 | none |
| C | 9 of 1M keys, every 50,000       | 4-38 | 0-4 | none |
| D | 5 of 100,000 keys, every 50,000  | 3-31 | 0-3 | 1, then none |
| F | 39 of 20,000 keys, every 5,000   | 1-28 | 0-2 | 3, then none |
| G | 19 of 200,000 keys, every 10,000 | 1-38 | 0-3 | 1, then none |

* "Dist tops" and "Dist inv": the range at every checkpoint after the
  first disturbance. The last column counts the cuts in the first segment
  after a disturbance.
* `main`'s twin has the window: 48 to 66 dirty top nodes at the
  checkpoints, 11 or 12 inversions, the same counts as `023-core`'s twin.
* After the first mass delete, `main`'s reclaim stops cutting: its
  iteration in progress never ends, as 023-03, 8.1, found for T1 at N =
  100,000 and 1M. The decided cut stays, and C keeps 3.95 GB at its end.
* With few or no reclaim steps, the hot segment root of the internal keys
  "/#i/dreclaim/..." that keeps the newest replaced roots dirty (P6, 5.1)
  is seldom written (023-03, 8.2: "in the window the stuck iteration
  makes no step"); this is the likely cause.
* After the first mass delete, `main`'s dirty top nodes stay below its
  twin's at every checkpoint of every run: 1 to 38, 0 to 4 inversions.
  In some segments a short window of 24 to 38 with 2 to 4 inversions
  holds to the segment's end; in others it drains below 10 with none. No
  trend: G's segments end at 9, 18, 26, 21, 8, 8, 30, 24, 33, 38, 28, 27,
  then 1 or 2 for the last seven.
* C's ninth restart ran out of its 8 GB heap (`CutStream.copy` of 3.95 GB
  kept): its eight disturbances before that are counted. The full run's
  `main` drive keeps about 2.5 GB at its last restart, and gets 12 GB.
* So on `main` this test cannot show the window after a mass delete: the
  stopped reclaim, a larger fault (020-30), hides it. It shows no growth
  either.


## 5. Small disturbances, too small to wipe the window

Runs H: 200,000 drive transactions, a disturbance every 2,000 (99 in
all), each followed by a restart. The fill and the deletes of n = 300
keys write about 50 kB, less than a startup distance, so they do not
wipe the window (P6, 5.2, "a risk not measured": a later disturbance
adds inversions). "Ends by quarter": the inversions at each segment's
end, averaged over each quarter of the 99 segments.

| Build, n         | Tops, all checkpoints | Inv  | Most | Inv at the ends, by quarter | Within |
|---|---|---|---|---|---|
| 023-core, 300   | 33-67 | 6-12 | 68 | 9.4, 8.8, 10.1, 8.4 | yes |
| 023-core, 1,000 | 24-65 | 4-12 | 68 | 8.9, 8.7, 8.5, 8.3  | yes |
| 023-core, 3,000 | 17-64 | 2-12 | 67 | 9.0, 8.5, 8.1, 7.5  | yes |
| main, 300       | 0-68  | 0-11 | 68 | 3.0, 0.2, 0.1, 0.2  | yes |
| main, 1,000     | 0-46  | 0-9  | 58 | 1.3, 0.1, 0.2, 0.2  | yes |
| main, 3,000     | 0-26  | 0-6  | 58 | 0.4, 0.3, 0.2, 0.3  | yes |

The twin: 52 to 65 dirty top nodes, 11 inversions, most 65; the bound is
81 or 82.

* **On `023-core`** the deletes of 300 keys leave 37 to 64 dirty top nodes:
  the window survives them. 99 such disturbances do not add inversions:
  the count at the segments' ends stays at 8 to 10 on average, below the
  twin's 11, and does not rise from quarter to quarter. Larger small
  disturbances (1,000 and 3,000 keys) wipe more of it and the count falls
  slightly.
* **On `main`** reclaim keeps cutting after deletes of 300 keys (787 cuts,
  the twin 795), slows after 1,000 (652) and stops after 3,000 (130). The
  drive makes far fewer top nodes after the deletes: 3,574 for n = 300,
  against the twin's 14,285 (`023-core`: 14,300). With few new top nodes
  no inversion is passed on (P6, 5.2), and the window drains to 1 or 2
  dirty top nodes. Why `main` makes fewer top nodes after deletes was not
  studied.


## 6. The answer

* **Bounded, not growing, on both builds.** No run shows the window
  growing from disturbance to disturbance: not 9 mass deletes of 1M keys
  (C), not 19 of 200,000 (G), not 39 of 20,000 (F), not 99 small ones
  that leave the window standing (H). By Frans's rule (023-08, Q6), fix
  (a) stays for later.
* **Why it cannot ratchet** (sections 4 and 5): a disturbance large
  enough to form a large window first wipes the one before it, because
  its fill and deletes make almost no top nodes while the take writes the
  old lists in order. A disturbance too small to wipe it is too small to
  form one; 99 of them added no inversions. So the window after a
  disturbance is set by that disturbance alone, its size and its phase
  against the take and reclaim, and holds until the next one.
* **But on `023-core` it is not within the twin's steady value after a
  large mass delete.** After 1M keys, 46 to 152 dirty top nodes in the
  segments' second halves (154 at most at a checkpoint), 9 to 44
  inversions, against the twin's 48 to 66 and 11 or 12; over the bound in
  8 of 9 (C) and 2 of 2 (B) segments, by up to 74. After 200,000 keys,
  in 4 of 19. After 100,000 keys or fewer, within. This is the window
  that T1 shows at 1M (023-09, 5.1), now with its range: a named
  allowance for it (023-03, section 10) could say "at most about 2.5
  times the twin's dirty top nodes, after a mass delete of 1M keys, until
  the next one".
* **On `main`** the test cannot show the window after a mass delete: from
  the first one on, reclaim stops cutting (023-03, 8.1), and after the
  mass deletes of B, C, D, F and G the dirty top nodes stay at or below
  38, under the twin's. After small deletes that leave reclaim running,
  `main` makes a quarter of the twin's top nodes and the window drains.
  `main`'s twin has the window, the same as `023-core`'s twin.
* **T4's queue** has no window on either build: it makes almost no top
  nodes (section 3).
* **The reclaim iteration spanning each disturbance**: on `023-core`, in
  every disturbance of 1M keys an iteration was in progress at the end of
  the deletes and cut 971 to 4,810 transactions after the restart; the
  window formed in that time. On `main`, after at most one more cut, one
  iteration spans all later disturbances and never ends.
* **For reading the full run**: four disturbances are few. B's two gave
  26 then 44 inversions, and four draws from C's range (9 to 44) rise at
  every step by chance about once in 24. A ratchet would show as inversions
  beyond C's range, or a rise over more disturbances than that.


## 7. The full run, for tonight

* **Script**: `/Users/f/fl/bench/2026-11-10/ratchet/night-ratchet.sh`. Start
  it with `nohup .../night-ratchet.sh > .../runs/full/driver.txt 2>&1 &`
  (the command is in its header); it refuses to start without the marker
  `/Users/f/fl/bench/2026-11-10/ratchet/READY`.
* **What it runs**, one JVM at a time: the queue (023-06, 18.6, item 3, as
  written) and T1's drive, each on `main` and on `023-core`: 1,000,000
  transactions, a mass delete of 1M keys every 200,000 (four), a restart
  after each, measures every 10,000 and around each disturbance.
* **Output**: `runs/full/<run>-<build>.txt`; `runs/full/summary.txt`,
  with section 4's table for each run, the bound and the line "inversions
  rising at every disturbance"; the driver's last line `RATCHET FULL
  DONE` (with `FAILED:` and the runs if a JVM failed), and the marker
  `runs/full/DONE`.
* **Expected duration**: about 10 minutes; allow 30. The scaled runs took
  0.1 to 2.8 minutes each on a busy F53 (load 12 to 20).
* **Memory**: -Xmx12g, one JVM at a time. `main`'s runs keep about 2 to
  2.5 GB of stream after the mass deletes, and a restart copies it.
* **Checked**: `night-ratchet.sh smoke` ran the whole script at 20,000
  transactions in under a minute (`runs/full-smoke/`).
* **What to expect**, from sections 3 to 6: the queue within on both
  builds; the drive on `023-core` over the bound after most mass deletes,
  with 9 to 44 inversions, not rising beyond that range; the drive on
  `main` below the twin, with reclaim stopped after the first mass delete.


## 8. Files and state

In `/Users/f/fl/bench/2026-11-10/ratchet/`:

* `probe/CleanupRatchet.java`: the probe; `classes-main/`, `classes-core/`:
  it compiled against each build.
* `wt-main/`, `wt-core/`: the worktrees and their builds; `clone/`: the
  clone, with the two worktrees added and nothing else changed.
* `scaled.sh`, `extra.sh`, `extra2.sh`: the scaled runs A to H;
  `runs/scaled/`: their outputs (`runs/` also holds the first trial runs,
  the same counts).
* `summary.py`: the tables of sections 3 to 5 from an output.
* `night-ratchet.sh`: the full run (section 7); `READY`: its marker.

State, 2026-11-10, 18:30: the scaled runs done on both builds (sections
3 to 5); the full run ready for the night, not started. No change to the
repository or to any other clone.
