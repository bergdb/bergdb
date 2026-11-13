# 024-15. The memory cost of key shape: documented and bounded

Created 2026-11-11 by Frans Lundberg. Status: done (2026-11-11): on
`main` since `1e77cfc6`.

Option (a) of 024-08, section 9, carried out: the memory cost of a key's
shape documented where a user and a reader of the algorithm look, and
guarded by a bound and runs of `Mem`. Frans, 2026-11-11, 07:30, asked
whether this cost is within aim 3 of release 2026.5: "Yes." (024-04,
log); so it is documented and bounded, not fixed. 024-08 is the study:
its figures are cited here, not measured again, except the runs of
section 3. Asked by the day's coordinator (coord-1111) at 09:34.


## 1. In short

* **The cost.** A prefix of 7, 14 or 21 bytes that only one key has,
  the whole key included when it is exactly that long, is a segment
  tree of one key node: about 226 heap bytes while in memory (024-08,
  section 4), where a KV whose key shares its prefixes costs about 130
  in all.
* **The bound** (024-08, section 7, BD12): without eviction, keys put in
  key order, heap <= fixed + 131 K + 230 T + V; K the KVs, T the segment
  trees beyond the first segment's, V the values' byte arrays.
* **The runs** (section 2): `Mem` takes `-n` and `-keys`; `level1.sh`
  step 6 checks SEG, the T constant (1M keys `%07d` minus MEM, at most
  230), in quick and full runs, and in its full run MEM10M (10M keys
  `/k/%010d`, at most 131). `night.sh` runs `level1.sh` full, so both
  are night checks; `before-commit.sh` is not changed.
* **The documentation** (section 4): `Connection`'s "Keys" (the Pub
  API, the user's advice), `Db`'s "Keys and values" (the Core API, with
  the bound) and `docs/levels.md`, section 4 (the reader of the
  algorithm, with the checks).
* **Not done here** (section 5): 024-08's options (b), a node table
  without boxed `Long` keys, and (d), a one-key tail in the parent leaf,
  are later candidates.


## 2. What was added where

Branch `024-15-key-shape-cost` of the clone (State has its head). One
commit; no change of the algorithm, no test's expected value changed.

* **`java/src-dev/bergdb/dev/props/Mem.java`.** Two options: `-n N`, the
  number of KVs (a positive multiple of 100, by default 1,000,000), and
  `-keys FORMAT`, the keys as `String.format(Locale.ROOT, FORMAT, i)`
  (by default `"" + i`, as since 2015). Without options it measures what
  it always did (024-08, Q2: keep MEM as the historical figure). The
  report keeps `MEM:` and the rounded figure and adds the figure with
  one decimal, the number of KVs and the keys' format:
  `MEM:130 (129.6 bytes a KV, 1000000 KVs, keys "" + i)`. `Props` and
  `props.sh` print it unchanged; `level1.sh`'s parse of `MEM:` reads the
  same digits.
* **`java/stress/level1.sh`, step 6.** Beside MEM and SS, in parallel
  with them:
  * **SEG**, both modes: `Mem -keys %07d` (1M keys of exactly 7 bytes,
    each a one-key segment tree) minus MEM, with one decimal; fails over
    `SEG_MAX=230`.
  * **MEM10M**, full mode only: `Mem -n 10000000 -keys /k/%010d` in a
    JVM with `-Xmx4g` (keys of 13 bytes that share their first 7, so no
    one-key trees); fails over `MEM_MAX`, 131, the same limit as MEM:
    the check that no term grows with the count.
  * Both are checked only with compact object headers, as MEM is, and
    printed otherwise. The header's step 6 and the comment above the
    limits say what they are, with 024-08 and 024-15.
* **`night.sh`** is not changed: its step `level1` runs `level1.sh` in
  full mode, so MEM10M is a night check, part of an existing step (the
  brief's alternative to a step of its own). Reason: one place for the
  MEM limits, the compact-header test and the parse; a step of its own
  would repeat them.
* **`before-commit.sh`** is not changed and runs no `Mem`.


## 3. The limits and today's figures

| Check  | Run                                   | Limit | 2026-11-11       |
|---|---|---|---|
| MEM    | `Mem`, 1M keys `"" + i`               | 131   | 129.1 to 130.1   |
| SEG    | `Mem -keys %07d` minus MEM            | 230   | 225.9 to 227.0   |
| MEM10M | `Mem -n 10000000 -keys /k/%010d`      | 131   | 127.1            |

* MEM and SEG by hand on F53 (OpenJDK 27.0.1, G1, compact object
  headers), six runs of MEM and four of `%07d` at 09:39 to 09:42,
  without the lock (1M KVs, a few seconds each): MEM 130.1, 129.9,
  129.4, 129.6, 129.7, 129.1; `%07d` 356.1, 356.0, 355.7, 356.1. SEG from the pairs run
  together: 226.1 and 227.0; from 024-08's figures, 356.0 - 129.6 =
  226.4. Its noise is MEM's, about one byte.
* **SEG's limit, 230**, is 024-08's proposal: today's figure and 3 to 4
  bytes, as MEM's limit is its figure and one step. The T constant of
  the bound is SEG; 024-08 measured 223 to 226 for each further segment
  of random keys too (section 5).
* **MEM10M's limit, 131**, is MEM's: 024-08 measured 127.0 at 10M and
  130.3 at 1M for `/k/%010d`, so a term that grows with the count would
  show here first.
* **Time.** SEG adds 0.5 to 0.7 s to step 6 (6.9 s without it, 7.4 and
  7.6 s with it; it runs beside MEM and SS). MEM10M runs beside them
  in the full run (024-08: 19 s alone); not timed apart. `level1.sh`
  full took 3 min 51 s at 11:57, with the other heavy-run slot busy.
* **`level1.sh` full on `877ddf20`**, 11:57 to 12:01, one slot: LEVEL 1
  OK, with `MEM:129 (at most 131)`, `SEG:226.9, MEM with keys %07d 356.1
  minus MEM 129.2 (at most 230)`, `MEM10M:127.1, 10M keys /k/%010d (at
  most 131)`. This is also the night check: `night.sh`'s step `level1`
  runs this script in full mode.


## 4. The documentation

**`Connection`, "Keys"** (the Pub API, preferred; after the stream
figures of 020-24-13, U13-1, and before the advice):

> Keys share key nodes by their starts of 7, 14, 21 bytes, a key's
> bytes being its UTF-8 and one more for each '/'. A start of 7, 14 or
> 21 bytes that no other key has, the whole key included when it has
> exactly 7, 14 or 21 bytes, costs a key node of its own, about 226
> bytes of heap while in memory; so one byte more or less of a key or of
> a common prefix can add or save a key node a key. With empty values
> and every node in memory, a million keys that shared their starts took
> about 130 bytes of heap a key (127 at ten million), keys of 7 bytes
> 356, and random keys, put in random order, of 6 bytes 181 and of 36
> bytes, such as UUIDs, 1,305 (bergdb 024-08, sections 5 and 7). With a
> cache budget below the data (DatabaseBuilder.cacheSizeInMb()) the heap
> stays near the budget whatever the keys, and the nodes cost stream
> bytes and time instead: 3 million keys of 32 random hex digits, put in
> random order, wrote 819 bytes of the stream a put and read 5.6 nodes
> from the stream a get, and a put took 4.6 times as long, against 226
> bytes and 1.2 nodes for keys that shared their start (bergdb 024-08,
> section 8). Keep keys short, put large data in values, and let keys
> that are written together share their start.

"Its UTF-8 and one more for each '/'": the Pub layer stores a key with
a byte after each '/' (`PubKeys.u2i`), as `Connection`'s size rule for
a transaction already says (020-24-13, U13-2).

**`Db`, "Keys and values"** (the Core API; after 021-16's figures):

> The keys that share their first j segments, their first 7j bytes,
> share a segment tree, a tree of key nodes, and a key of exactly 7, 14
> or 21 bytes ends with an empty segment (Keys.toSegments). So a prefix
> of 7, 14 or 21 bytes that only one key has, the whole key included
> when its length is exactly that, is a key node for that key alone:
> about 226 bytes of heap when in memory, where a KV with an empty value
> whose key shares its prefixes costs about 130 in all. A random key of
> L bytes, such as a UUID, pays it L / 7 times, rounded down (5 for 36
> bytes), and one byte more or less of a fixed-width key can add or save
> a node a key. With noEvict() and keys put in key order, the heap above
> the empty database's is at most about 131 K + 230 T bytes and the
> values' byte arrays, K the KVs and T the segment trees beyond the
> first segment's; in random key order K's constant is about 181 (bergdb
> 024-08, sections 5 and 7). With eviction the heap stays near the
> budget whatever the keys, and those nodes cost stream bytes and node
> reads instead (024-08, section 8). Keep keys short, put large data in
> values, and let keys that are written together share their start.

**`docs/levels.md`**, a paragraph "The keys' shape and the heap" at the
end of section 4 (Level 1, the map in memory: the segments, the
one-key trees, the bound, eviction's effect, the three checks and
Frans's decision), and section 2's line on `level1.sh` names it. 327 is
not quoted anywhere.

**Each figure against 024-08:** 226 (section 4: 223 to 226; 225.9 and
226.4 by runs); 130 and 127 (section 5: `/k/%010d` 130.3 at 1M, 127.0
at 10M; MEM 129.6); 356 (`%07d` 356.0); 181 and 1,305 (section 5, random
characters, random order); about 181 for K in random order (section 5,
175 to 181); L / 7 (section 5: 8 and 13 bytes 1 tree, 16 bytes 2, 32
hex 4, 36 bytes 5); eviction (section 8: heap 173 and 213 MB at a budget
of 200 MB; stream 226 and 819 bytes a put, 3.6 times; 4.9 and 22.6 µs a
put, 4.6 times; 1.2 and 5.6 nodes read a get in round 1).


## 5. What is left

* **Later candidates, not part of this item** (024-08, section 9): (b)
  a node table without boxed `Long` keys, about 39 bytes less an index
  node (226 to about 187 a one-key tree, 130 to about 126 a KV), no
  format change; (d) a one-key tail kept in the parent leaf, the fix
  that makes the cost follow the key's bytes, a format change and a
  change of the Lean model. Frans's answer of 07:30 puts no fix in
  2026.5.
* 024-08, Q3 (024-03's and 024-04's 327) is the coordinator's.
* Not measured: SEG and MEM10M on s1; the bound with values other than
  empty ones in a check (024-08 measured 100-byte values at 1M by hand).


## 6. Log

2026-11-11, 09:34 to 12:02. Read 024-08, `level1.sh`, `Mem`, `night.sh`
and the Javadoc; the clone; `Mem`'s options, `level1.sh`'s checks and
the three texts; SEG measured by hand at 1M (no lock needed). The lock
was held by the integration gates until about 10:08 and the slots were
busy after; `before-commit.sh` ran 11:27 to 11:31 and `level1.sh` full
11:57 to 12:01, each in one slot. Both passed.


## State

Written 2026-11-11, 12:02. Status: done; the branch is for the coordinator to land.

* **Done:** the code (`Mem`, `level1.sh`), the documentation
  (`Connection`, `Db`, `levels.md`), committed on the branch; SEG
  measured by hand.
* **Gates:** `before-commit.sh` on `877ddf20`: BEFORE COMMIT OK (287 s,
  11:27 to 11:31, one slot); `level1.sh` full on `877ddf20`: LEVEL 1 OK
  (11:57 to 12:01, one slot), MEM 129.2, SEG 226.9, MEM10M 127.1.
  No slot is held.
* **Not done:** nothing of this item's task; section 5 lists what is
  left for later (024-08's options (b) and (d), Q3).
* **Clone:** `/Users/f/fl/bench/2026-11-11/shape/clone`, branch
  `024-15-key-shape-cost` from main `0da2cdd4`, head `877ddf20`.
* **To continue:** land the branch on main (the coordinator); nothing
  else is pending in this item.

2026-11-13. Status set after the release (coord-1113).
