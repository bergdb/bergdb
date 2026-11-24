028-52. Investigate: CountGates' G4 fails ST6 at C2's settings
===============================================================

Status: done: the gate was wrong; G4's ST6 takes G5's floor.
Kind: Investigate. Frans: none.
Created 2026-11-24 by Frans Lundberg.

What: G4 of `CountGates` (`java/stress/count-gates.sh g4`) at 026-13's
C2 settings, `g4sd=1000000 dt=50000` (a startup distance of 1 MB, R =
200 drive transactions, 40 R), fails its gate ST6 on `main`: the
emptied database's cache table slots are 62,912 against the twin's
25,488, 2.47 times, over the limit of 2 (`g4slots`). The gate passes at
G4's own settings (sd 100 kB, R = 1,000). The same holds with 028-47's
options B and B2 (2.40 to 2.47 times). Found by 028-47's study,
sections 1 and 6, F3.

Why: either the gate is wrong at these settings (it compares slots that
depend on the cache's history, not on what the database holds), or the
emptied database keeps cache tables that it should shrink (024-33, ST6;
the tables shrink to `Table.MIN_CAPACITY`), which G4 at its own
settings does not reach. At C2's settings G4's lag gate fails too
(14.8 R against 2 R), as the cut waits for the startup pos (028-47,
section 3); whether ST6 follows from that is part of the question.

Frans: none.

Done when: the entry says why ST6 is 2.47 times the twin's at C2's
settings (which maps hold the slots, and why they have not shrunk), and
whether the gate or the database is wrong; with the run's lines quoted.
If the database is wrong, a 028 entry for the fix (and an RB entry in
033 if it is a fault of a released version, 033's rules); if the gate,
its fix or a note in `CountGates` on the settings where it holds.

First step: read 028-47's study, section 1, `CountGates.g4` and
`Cache3`'s shrinking (024-33); run `count-gates.sh g4` with
`g4sd=1000000 dt=50000` on `main` and print the slots by map for the
emptied database and the twin.


Result
------

Done 2026-11-24 by an agent of lead-1124, in a clone of `main` at
6d1d7805. The gate was wrong, not the database: G4's ST6 compared the
emptied database's slots, which sit at the tables' floor, with twice the
twin's, which grow with the twin's drive. No 028 entry for the database,
no RB entry.

### 1. The slots by map

`CountGates g4` prints, since this entry, the 4,096 maps of the node
table (`Cache3`) by the length of their HashMap's table: maps, entries,
empty maps (printed, not gated). On `main` with that line alone:

* C2's settings, `g4sd=1000000 dt=50000` (R = 200, a drive of 8,000):

      G4 g4-twin slots by table length: 0: 2503 maps, 0 entries, 2503 empty; 16: 1593 maps, 1754 entries, 165 empty;
      G4 g4-emptied slots by table length: 0: 164 maps, 0 entries, 164 empty; 16: 3932 maps, 2017 entries, 2333 empty;
      G4 ST6 cache table slots over the twin's (62912 / 25488) value 2.468 limit 2.000 margin 0.81 FAIL

* G4's settings (sd 100 kB, R = 1,000, a drive of 40,000):

      G4 g4-twin slots by table length: 0: 356 maps, 0 entries, 356 empty; 16: 3740 maps, 432 entries, 3337 empty;
      G4 g4-emptied slots by table length: 0: 30 maps, 0 entries, 30 empty; 16: 4066 maps, 475 entries, 3622 empty;
      G4 ST6 cache table slots over the twin's (65056 / 59840) value 1.087 limit 2.000 margin 1.84 PASS

(The lines were printed with the earlier spelling `0:2503 maps 0
entries 2503 empty;`; the counts are the same.)

### 2. Why 2.47 times

* Every map with a table has 16 slots, `Table.MIN_CAPACITY`, in both
  databases and at both settings: no map is above the least capacity, so
  the shrink of 024-33 has done all it can. The emptied database's
  62,912 slots are 3,932 maps of 16, below the floor of 4,096 maps of 16
  (65,536); its entries, 2,017 handles, are 1.15 times the twin's 1,754
  (M11 passes).
* A map keeps a table of 16 once it is used: HashMap keeps its table
  when its entries are removed, and `Table.shrinkIfSparse` does not copy
  a map at the least capacity. Only a batch removal that empties a
  larger map (`clockStep`, `deadStep`) leaves a map with no table (a
  copy of an empty map has none): the 164 and 30 maps of length 0 in
  the emptied database. The fill of 1M keys uses nearly every map, so
  the emptied database ends at the floor at any drive.
* The twin's slots count the maps that its drive's node ids reached:
  each drive transaction writes index nodes with new ids, each id's
  handle goes to the map that `mapIndex` picks, and the map keeps its 16
  slots after the handle leaves. After 40,000 transactions 3,740 maps
  are used, after 8,000 only 1,593. So at G4's settings twice the twin's
  is above the floor and the gate passes; at C2's settings, with a drive
  a fifth as long, it is below, and the emptied database at the floor
  fails.
* It does not follow from the lag (14.8 R at C2's settings, 028-47,
  section 3): the emptied database is at the floor whatever the cut
  does, and its handles are within 1.15 times the twin's.

### 3. The fix

G4's ST6 takes G5's limit, the larger of twice the twin's (`g4slots`)
and the tables' floor, 2^MAP_BITS maps of `Table.MIN_CAPACITY` slots
(024-32, section 4, where G5's twin uses 5 maps): one method,
`CountGates.slotGate`, for both gates, with the reason in its comment
and in the class comment. The gate still finds what ST6 was made for,
tables kept at their peak after a mass delete: 226,400 slots before
024-33, 3.5 times the floor. G5's limit is unchanged.

### 4. Runs and gates

Commit 97c3aa5d. `count-gates.sh g4 g4sd=1000000 dt=50000` (the emptied
database's slots differ by a few maps from run to run, 62,912 and
62,944):

    G4 g4-emptied slots by table length: 0: 162 maps, 0 entries, 162 empty; 16: 3934 maps, 2017 entries, 2335 empty;
    G4 ST6 cache table slots over the larger of 2.0 times the twin's and the tables' floor 65536 (62944 / 25488) value 0.960 limit 1.000 margin 1.04 PASS

The run still ends `COUNT GATES FAILED`, on the lag (`value 14.845
limit 2.000`), as in 028-47, section 3: at C2's settings the cut waits
for the startup pos. That is not ST6's question; the lag gate holds at
G4's own settings, which `count-gates.sh` runs.

`count-gates.sh` (all, G4's own settings):

    G4 ST6 cache table slots over the larger of 2.0 times the twin's and the tables' floor 65536 (65088 / 59840) value 0.544 limit 1.000 margin 1.84 PASS
    G5 ST6 cache table slots over the larger of 2.0 times the twin's and the tables' floor 65536 (62272 / 96) value 0.950 limit 1.000 margin 1.05 PASS
    COUNT GATES OK

`java/before-commit.sh`: `BEFORE COMMIT OK (62 s)`.


Log
---

2026-11-24, 12:30. Registered by an agent of lead-1124, from 028-47's
finding F3 (Frans, 2026-11-24, 12:30).

2026-11-24, 12:35. Taken by an agent of lead-1124 (in progress), in a
clone of `main` at 6d1d7805, on the branch 028-52.

2026-11-24. Done by an agent of lead-1124: the gate was wrong, not the
database (the Result above); G4's ST6 takes G5's limit with the tables'
floor (commit 97c3aa5d). Gates: `COUNT GATES OK`; `BEFORE COMMIT OK (62 s)`.
Status done; moved to Closed.
