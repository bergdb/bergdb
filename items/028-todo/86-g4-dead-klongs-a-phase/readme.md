028-86. Investigate: count-gates' G4 fails M5 after 031-06's pace: two phases compared
=====================================================================================

Status: done: no regression; G4's M5 takes G5's limit.
Kind: Investigate. Frans: none.
Created 2026-11-28 by Frans Lundberg.

What: `java/night.sh` on `main` at `16c64d9a` (2026-11-28, 11:44)
failed its step count-gates (`java/stress/count-gates.sh`):

    G4 M5 dead KEY klongs over the twin's (34 / 13) value 2.615 limit 2.000 margin 0.76 FAIL

Every night before passed it, the last on `50c60f13` (2026-11-27, 22:25)
with (20 / 14), 1.429. M5 (024-30, section 8): the KEY klongs, deleted
or shadowed, in the key nodes that a scan of every key follows at the
end of G4's drive, of the emptied database against its hello-world
twin, at most 2 times the twin's.

Why: a functional gate of `main` failed, priority 1. 031-05's F9, G4's
M5 at 1.933 of 2.0 (29 of 15) on 031-05's prototype, unexplained, was
the same measure near its limit.

Frans: none. The limit taken is G5's, to which Frans said yes in
026-09's Q2 (2026-11-14); the lead lands it, as 028-52 gave G4's ST6
G5's limit.

Done when: the cause known; a fix in the code if reclaim leaves more
dead klongs than its design allows (theta a key node), else the gate's
limit corrected with its reason; `count-gates.sh` prints COUNT GATES OK
twice with the same counts.

First step: whether the counts are the same on reruns of one build; a
bisect of `java/src` from `50c60f13` to `16c64d9a`.


Result
------

### 1. Deterministic

Two runs of `count-gates.sh` (all five gates) on `16c64d9a`, 2026-11-28
from 13:15, at a load of 21 to 29: every count is the night's. G1
108,332 bytes, G2 1.234, G3 4.699, G4's M5 (34 / 13), the emptied
database's stream after the fill and the deletes 310,790,176 bytes, G5's
M5 (31 / 10). Only the heap after a GC and the cache's table slots
differ, by less than 0.3 % (G4's emptied heap 2,947,216 and 2,942,192
bytes; G5's emptied slots 58,592 and 58,752), within their margins (1.86
and 1.12). So the gate is functional, and its counts repeat: a failure
of M5 is not a fluke of the machine.

### 2. The bisect

`git bisect` over the 21 commits from `50c60f13` to `16c64d9a` that
touch `java/src` or `java/stress`, `count-gates.sh g4` on each:

* `1a136a9c`, `05087002`, `e9e93cbd` and `96daa4bb`: (34 / 13); the
  emptied database's stream after the fill and the deletes 310,790,176
  bytes;
* `b7f21db4`: (20 / 14), 319,985,616 bytes, as on `50c60f13`.

The first commit is `96daa4bb` (031-06, landing step 3, the pace). It
gives the final numbers; no later commit changes them.

### 3. The cause

The probe [G4Dump.java](G4Dump.java) runs G4 on either database and then
lists each key node that the scan follows with its KEY klongs (live,
shadowed, deleted); it also sums the dead klongs after each of the
drive's last 1,000 transactions (the last R) and after every 1,000th. It
gives CountGates' numbers: 34 and 13 on `16c64d9a`, 20 and 14 on
`b7f21db4`.

* **The same nodes, nothing left of the deleted keys.** Both databases
  end with the same 7 key nodes, the segment leaves of "/a.txt" and of
  BergDB's own keys (`/#i/-sd`, reclaim's `-current.txt`,
  `-settings.txt` and `-table.txt`): no deleted klong, no key of the
  million deleted ones. Each node holds 0 to theta = 7 dead klongs
  (024-23's compaction; `Dag.theta` at node size 30), and no node held
  more than 7 at any of the 1,040 samples of either build.
* **The dead klongs at the end**, node by node in the scan's order:
  * on `16c64d9a`, the emptied database 6, 5, 4, 7, 7, 4, 1 (34), the
    twin 1, 1, 3, 0, 7, 0, 1 (13);
  * on `b7f21db4`, the emptied database 3, 5, 2, 3, 2, 4, 1 (20), the
    twin 2, 1, 3, 0, 7, 0, 1 (14).
* **Each count is a sum of 7 phases**: how many times each leaf was
  written since its last compaction. In the last R:
  * the twin, on both builds: 10 to 37 (mean 26.2);
  * the emptied database: 13 to 30 (mean 20.7) on `b7f21db4`, 21 to 39
    (mean 29.8) on `16c64d9a`;
  * the ratio of the two: 0.47 to 1.80 on `b7f21db4`; 0.66 to 3.30 on
    `16c64d9a`, above 2 after 35 of the 1,000 transactions.
  * Over the whole drive, every 1,000th transaction, the emptied
    database has the same range on both builds (10 to 41 on `b7f21db4`,
    13 to 37 on `16c64d9a`), and on `b7f21db4` the ratio was above 2
    once of 40 (2.43, after 1,000 transactions).
* **What `96daa4bb` changed**: the stream that both databases write,
  so the transactions at which each leaf is compacted, and so the phases
  at the drive's end. A step's charge, the row's rewritten, counts also
  the index nodes that its record's batch makes dirty on the step's paths
  (`Db.chargeStep`; 25 to 40 % of the charge, 031-06, section 4.6), and
  the row holds it at a fixed width: the allowance, the fraction less
  rewritten, is spent sooner, and the steps, with the row's writes, come
  at other transactions. The commit's other change of the
  stream, a commit's step of up to twice the allowance of the
  application's last record, is not what moved M5: `96daa4bb` with every
  commit's step at 16 kB as before (a test switch, not kept) gives (33 /
  13), the stream after the fill 311,141,840 bytes.

### 4. The judgment

No regression. The emptied database is back to the twin's key nodes and
keys, and every node stays within theta, as the design says. `96daa4bb`
is a correct change (031-06's landing, reviewed and gated) that moved a
phase.

The limit's reason does not hold for this measure. 024-30 (section 8)
set the factor 2 from one calibration run, ratios 1.00 to 1.46 (M5: 24
against 18), and noted that a drive of 4 R fails M1, M5, M11 and the
heap; M5's figure there, 22 against 10 with 6 key nodes in each, was a
phase too, and M1, M11 and the heap fail at 4 R on their own. Twice the
twin's at the drive's end compares two phases: on either build M5 passes
or fails by the transaction at which the drive ends. 026-09 (section 6.3,
Q2) found the same for G5, whose limit became the twin's plus 70, theta
in each of a_n = 10 key nodes (Frans's yes, 2026-11-14).

### 5. Options

* **(a) G4's M5 as G5's**: at most the larger of twice the twin's and
  the twin's plus 70. What is left of deleted keys still fails a gate:
  more key nodes fail M4 (twice the twin's), and dead klongs beyond
  theta in the nodes that M4 allows fail M5. On `16c64d9a`: 34 against
  83, value 0.410; at most 0.427 in the last R. **Recommended, and
  built.**
* **(b) The design's rule itself**: at most theta times the emptied
  database's reachable key nodes (M4), here 49; nothing compared with
  the twin.
* **(c) Twice the twin's, on the most in the last R** of each, as M1:
  39 against 37 on `16c64d9a` (1.05), 30 against 37 on `b7f21db4`
  (0.81); a scan after each of the drive's last 1,000 transactions.

### 6. The change

* `CountGates.g4`: M5 by `gateSmall("G4", ...)`, the larger of twice the
  twin's and the twin's plus 70, with its reason in a comment; the class
  comment says so. `gateSmall` takes the gate's name; G5's calls are
  unchanged.
* `count-gates.sh`'s header: G4's dead klongs as G5's; G5's dead klongs
  the twin's plus 70 (it said 30, the limit before 026-09).
* No change in `java/src`. 024-30 is a finished item and is not edited:
  this entry is the record of the change of G4's limit, as 028-52 is of
  ST6's.

### 7. Gates


Log
---

2026-11-28. Registered by lead-1127 from night.sh's failure on
`16c64d9a`, and taken by an agent of lead-1127, branch `028-86` of a
clone of `main`. 13:14 to 13:40: the counts repeat (section 1); the
bisect names `96daa4bb` (section 2); the probe's dump of the key nodes
(section 3); no regression, G4's M5 a comparison of two phases (section
4); option (a) built (sections 5 and 6).
