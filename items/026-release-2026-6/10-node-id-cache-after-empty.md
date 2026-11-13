# 026-10. The node-id cache after back to empty

Created 2026-11-13 by Frans Lundberg. Status: STATUS_PLACEHOLDER

For release 2026.6, found by 026-07: with the write buffer no longer a
fixed 10 MB on both sides, G4 and G5 (024-30, the count gates' heap
after back to empty) showed an emptied database holding 2.0 (G4) and
3.7 (G5) times its twin's heap. Most of it is `NodeCollection.idByPos`,
an LRU map of node ids by stream position of up to 100,000 entries
(boxed `Long` to `Long`), which still holds about 49,000 entries
(4.4 MB) after back to empty, plus about 2.2 MB of `long[]` not traced.
By the rule that a deleted KV eventually costs nothing (020-30), an
emptied database should hold about what a new one holds.

Until this is done, G4 and G5 compare each heap plus the 10 MB they were
calibrated with (`CountGates.BUFFER`; Frans, 2026-11-13, 09:48, 026-07's
Q4: "ok"); after it, they gate the plain heaps.

Done when: G4 and G5 pass on the plain heaps; the 2.2 MB of `long[]`
traced (fixed here or named); before-commit, level1, count-gates.

First step: find what keeps `idByPos`'s entries after back to empty
(positions below the first position kept after a cut cannot be read
again, so their entries can go at the cut), and trace the `long[]`.
Keep it simple (Frans, 10:06, on 026-07's Q2: "KISS. Complexity and code
size are costs too.").

Made by the agent "idpos" of coord-1113 in a clone, branch
`026-10-idbypos`; the coordinator lands it. The probes are in
`10-node-id-cache-after-empty/`: `ForgetProbe.java` (section 4) and
`heap-walk.patch` (a temporary change of `CountGates` that prints
`idByPos` and walks the database's objects from `Db` by reflection,
summing the `long[]` by the field that holds them; section 2).


## 1. Why `idByPos`'s entries stayed

`idOf(pos)` gives the node id of the version at a stream position: from
the map, else from the node's header, read from the stream (32 bytes)
and put in the map. Its callers: the writer's `resolvePointers`, before
each index node is written, for each pointer to an index node that has
no handle and names a position at or above the stream's first position;
and at startup `linkToCanonical`'s fallback for a top node's pointer and
its check (`checkLinkById`). All run under the write lock, or in the
start's single thread.

What the map held at the heap measure (`heap-walk.patch`):

| Database | Entries | Positions (MB) | First available position (MB) |
|---|---|---|---|
| G5 emptied | 49,949 | 28.5 to 234.1 | 302.6 |
| G4 emptied | 48,837 | 38.7 to 234.1 | 360.3 |

Every entry named a version written in the fill or the delete, below
the first available position, so dead for every lookup time still
available. All were put there by `resolvePointers` for key nodes (none
for top nodes): during the delete, key nodes evicted and read again
have pointers without handles, and each write of such a node looks up
their ids. Nothing removed an entry but a newer one (the LRU's bound),
and a quiet database adds none.

**Can such a position be asked again?** `idOf`'s callers skip positions
below the *stream's* first position (`NodeStream.getFirstPos`), which
lags the decided cut: Reclaim makes the cut (`pretruncate`) only when
the table that marks it is durable (`cutIfDurable`), and a `FileStream`
cuts whole files (200 kB to 500 MB and more). In G4's drive, 40,000
transactions without a sync, 161 cuts were decided and none made after
the fill: `pretruncate` ran 4 times in all, the last at 38.7 MB. So a
first try that forgot the entries at `pretruncate` passed G5 and left
G4's 48,837 entries. The entries go when Reclaim *decides* the cut, at
its first available position `pCut`.

Forgetting an entry is always correct: the id of the version at a
position never changes, and `idOf` reads the header again if asked. Does
it cost reads? The lookups and header reads of every count gate at 1M
keys, without and with the forget (a temporary counter; `cmp-base.txt`
and `cmp-fix.txt` of section 6):

| Run | Lookups, without | Reads, without | Lookups, with | Reads, with |
|---|---|---|---|---|
| G1         | 748,270 | 310,535 | 748,239 | 310,523 |
| G2 sparse  | 342     | 315     | 346     | 319     |
| G2 mass    | 692     | 631     | 671     | 609     |
| G3         | 0       | 0       | 0       | 0       |
| G4 emptied | 139,511 | 49,897  | 139,696 | 49,934  |
| G5 emptied | 139,552 | 49,945  | 139,609 | 49,945  |

The same within noise: no forgotten entry was asked again. The twins
look up none.

**A smaller bound?** No: a bound alone still keeps up to the bound after
back to empty, and the map saves reads (G1: 438,000 of 748,000 lookups
found in it). Whether 100,000 entries (about 9 MB when full) is the
right size for large databases is a question of performance, not of
this item.


## 2. The `long[]`: `KeyModSet`

The walk of `heap-walk.patch` gave every `long[]` of the emptied
databases to `KeyModSet$Bin.subBins`, the arrays of Db's set of recent
writes for the optimistic conflict check (`Db.stmCheckConflicts`,
`stmRecordKeys`):

| Database | Arrays | Bytes |
|---|---|---|
| G5 emptied | 507 | 2,470,032 |
| G4 emptied | 385 | 1,808,720 |
| twins      | 0   | 0         |

`KeyModSet` holds (time, key hash) pairs of every transaction's writes,
the internal ones too, in 4 bins of 32,000 pairs; a new bin replaces the
oldest when the newest is full; a commit whose lookup time is before the
oldest bin's first time is rerun. Nothing removed a pair by time: the
set held the last 128,000 pairs, about 2.5 MB, for as long as no newer
writes came, so an emptied and quiet database kept the hashes of its
last 128,000 deletes.

It is fixed here too, as G5 cannot pass without it: in
`count-gates.sh all` (the gate), G5's twin holds 0.61 MB (1.88 MB when
G5 runs alone, with the classes it loads first), and the emptied
database's 2.47 MB of `KeyModSet` alone is 4 times that.

Seen on the way, not changed: the keys of `CountGates` (`/k/%010d`)
fall in 507 of the 32,000 sub-arrays, about 250 pairs each, so
`modifiedAfter` scans about 250 pairs a bin for each key a commit read:
`Keys.hash` mixes the key's 8-byte segments by `* 37 +`, and the bin's
index is the hash modulo 8,000 (question Q2).


## 3. The change

On branch `026-10-idbypos` (section 8):

* **`Db.cutDecided(pos, time)`**, called by
  `Reclaim.pretruncateIfPossible` under the write lock right after it
  moves the first available position to `pCut` and the first available
  lookup time to `tEnd`. It calls the two below.
* **`NodeCollection.forgetIdsBelow(pos)`**: removes the entries below
  `pos` (`removeIf`); if less than a quarter is kept, the entries kept go
  to a new map, in their LRU order, as a `HashMap` keeps its table when
  entries go (131,072 slots, 0.5 MB, at 49,000 entries). The map is
  replaced, so it is guarded by a lock object of its own (`idLock`), not
  by itself; `idOf`'s two blocks take it.
* **`KeyModSet.forgetUpTo(time)`**: the bins are kept down to the first
  that begins at or before `time`; the older ones go. If that is the
  newest bin, a new bin begins at the last add (so that a later cut
  forgets the pairs before it), and the old one goes at once if the last
  add is at or before `time`. The answers of `modifiedAfter` for lookup
  times from `time` on do not change; for an earlier lookup time it says
  "modified", as for any time before the set's first time, and the
  transaction is rerun (question Q1). Constant time.
* Tests: `NodeCollection.testForgetIdsBelow` (forgotten entries read
  again, kept ones not), `KeyModSet.testForgetUpTo` (the bins kept, the
  new bin, the answers before and after `time`).
* `CountGates`: G4 and G5 compare the plain heaps; `BUFFER` is gone,
  and the comment at the heap's wait says why it was there.

A Pub transaction that is rerun runs again with a new environment and
reads at the latest time (`RwTransaction.executeRwInner`), so a rerun
for an old lookup time does not repeat. Reclaim's steps read at their
own time, after the cuts they follow.


## 4. The pause (P1)

`forgetIdsBelow` runs under the write lock and `idLock`: it delays the
commit that decides a cut; readers take neither. `ForgetProbe` times it
on a map of 100,000 entries (F53, load 8 to 14 from other work):

| Kept | First call | Later calls |
|---|---|---|
| all        | 5.7 ms | 0.3 to 0.5 ms            |
| about 30 % | 4.3 ms | 0.9 ms                   |
| about 20 % | 4.4 ms | 2.0 to 3.1 ms (the copy) |
| none       | 4.2 ms | 0.8 to 0.9 ms            |

The first version copied the kept entries at every cut: up to 11.7 ms
in G1 (71,212 kept, in the count gates' run), the reason for the copy
only below a quarter. `forgetUpTo` drops at most three references and
makes one bin (a 32 kB array).


## 5. Heap after back to empty

`count-gates.sh all` at 1M keys, the plain heaps (bytes after a GC):

| Tree | G4 emptied / twin | G4 | G5 emptied / twin | G5 |
|---|---|---|---|---|
| main (c91443d8), no BUFFER | 8,514,776 / 2,721,392 | 3.129 | 7,152,856 / 610,416 | 11.718 |
| `idByPos` forgotten        | 4,790,064 / 2,721,528 | 1.760 | 3,431,776 / 610,592 | 5.620  |
| and the old bins go        | 2,905,744 / 2,688,320 | 1.081 | 1,377,824 / 610,536 | 2.257  |
| and a new bin at a cut     | 2,926,872 / 2,721,184 | 1.076 | 899,672 / 610,536   | 1.474  |

The third line kept `KeyModSet`'s newest bin: in G5's drive each cut
was decided after an internal transaction's add, so the newest bin,
begun in the delete, never ended before a cut's time. The fourth line
is the change of section 3 (`count-all-2.log`; again on the final
head in section 6). The rest of G5's difference, 0.29 MB, is mostly the
cache tables' slots (ST6: 48,320 against the twin's 80, 4 bytes each),
which ST6's own gate holds to the tables' floor (024-33), and
`KeyAccessPath`'s arrays (ST7, not gated).


## 6. Gates

GATES_PLACEHOLDER


## 7. Questions for Frans

Each is decided here by the recommendation, so that the work goes on;
Frans may overturn it.

* **Q1. `KeyModSet` after a cut** (section 3): a commit whose lookup
  time is before the first available lookup time (and before the oldest
  bin kept) is rerun, even if no key it read was written since. Until
  now it was rerun only if its lookup time was before the last 128,000
  writes. Such a transaction read a state that can no longer be read (a
  read at its lookup time throws `LookupTimeNotAvailableException`), and
  took longer than the retain duration. Options: (a) as made; (b) leave
  `KeyModSet` as it was, and give G5's heap an allowance of 2.5 MB.
  Recommended: (a).
* **Q2. `KeyModSet`'s bin index** (section 2, seen on the way):
  sequential keys fill few sub-arrays, about 250 pairs each in G5,
  scanned for each key a commit read. Recommended: a 028 entry (a hash
  that mixes the bits before the modulo, and a count of the pairs
  scanned), not this item.


## 8. State

STATE_PLACEHOLDER


Log
---

2026-11-13. Registered by coord-1113 (026-07's Q4; Frans, 09:48).

2026-11-13. Made by idpos (coord-1113) on branch `026-10-idbypos`.
