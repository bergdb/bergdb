# 020-30-02. Deleted keys: the original intent and prior art

Created 2026-11-10 by agent p30 of coord-1110 (phase 1 of 020-30, a
25-minute overview). Sources: Frans's F1-007 notes (`bergdb/doc/`), the
papers and systems named below, and `Dag.java` on `main` for one check.


## 1. The original intent (F1-007, 2012)

* Merge was planned. `log-old/2012-log.txt`, 2012-01-27: "Merges are made
  when the current version of a node shrinks because of a delete. It may
  then be merged with its parent." `2012-02-notes.txt`: "Space merge.
  Merge a supernode with its parent of post-cost lower than pre-cost."
* Then postponed. `log-old/2012-log.txt`, 2012-02-17: "DECISION. Keep the
  klong-array approach. Implement working split. Optimize split/merge
  later. Start with split, no merge right now." 2012-03-19, a limitation:
  "no node deletion (always grows in memory)".
* An empty node leaves its parent. `2012-06-notes.txt` (the delete-bitmap
  design, merged 2012-06-19): "The last version of the full [node] could
  be empty (no key klongs). This happens when all key klongs have been
  deleted. In this case, we want to delete the node by adding a delete
  klong to its parent." Its summary: "If lastVersion is empty, remove from
  parent. If lastVersion is small, add lastVersion to parent."
* Reclaim rewrites live KVs. `2012-07-space-reclaim.txt`: "For each KV at
  lookup time t1 [...] If KV not written (set/delete) since t1. Rewrite
  KV". It does not mention deleted keys or index nodes; it assumes the
  current tree reaches only live data. The 2013 to 2016 notes and
  backlogs do not return to merge or empty nodes.
* Not done. In `Dag.java` (about line 972) a delete that fills a node
  time-splits it to `lastVersionGivenDel()`, which may be empty, and the
  parent keeps its live klong to it. Frans's 2012 intent and his 2026
  rule agree: the emptying transaction unlinks the node.


## 2. Multiversion B-tree (Becker et al., VLDB Journal 1996)

An entry has a lifespan; a delete sets its end time. A live node must
hold at least d live entries. When a delete breaks this (weak version
underflow), the node is version-split: its live entries are copied to a
new node, the old one dies, and a too small copy is merged with a
sibling's live entries. Space is never freed (all history is kept); what
is bounded is work: each version's tree is a B-tree over its live
entries, so a range query costs O(log_b m_t + r/b). Old versions can be
dropped by dropping the roots and nodes whose lifespan ended before a
horizon. For BergDB: this is Frans's scan bound; the time split is the
version split; the missing part is the underflow rule (unlink or merge),
done in the deleting transaction at amortized O(log n) cost.


## 3. Time-split B-tree (Lomet and Salzberg, SIGMOD 1989)

A full current node is split by time (the versions valid now go to a new
current node, the old one becomes read-only history) or by key. A delete
writes a delete stub, which a time split does not carry forward. No
merge in the original; their Pi-tree (SIGMOD 1992) adds node
consolidation as a separate, lazy action. History is kept for ever. For
BergDB: this is BergDB today, and it shows the gap: a current node can
become empty and stay linked. Consolidation may be lazy.


## 4. Copy-on-write B-trees (LMDB, Btrfs, CouchDB)

LMDB: a delete removes the key in a copied leaf; a page below a fill
threshold is merged with or borrows from a neighbour (`mdb_rebalance`),
an empty page is removed, all in the deleting transaction. Freed pages
are reused once no reader holds an older snapshot. Btrfs (Rodeh, ACM TOS
2008): the same, with proactive merge on the way down; snapshot deletion
is a background cleaner that drops reference counts. CouchDB: compaction
copies the live tree to a new file (no old snapshots kept); a deleted
document stays as a tombstone until an explicit `_purge`. For BergDB:
LMDB and Btrfs split the work as Frans's rule allows: the transaction
fixes the structure, the space waits for the oldest snapshot (in BergDB:
the retain duration and the cut). CouchDB's tombstones warn that a
marker kept for some reason costs space for ever.


## 5. LSM trees (LevelDB, RocksDB, Cassandra)

A delete writes a tombstone. Compaction drops values it hides once no
snapshot sees them, and drops the tombstone at the bottom level once it
is older than the oldest snapshot. RocksDB's `DeleteRange` writes one
range tombstone, dropped by the same rules. With user-defined timestamps,
`full_history_ts_low` is the horizon: compaction may drop older versions
but keeps, per key, the newest version below it. Before compaction,
tombstones cost scan time; queues are the known bad case (Cassandra's
tombstone warnings, RocksDB's deletion-triggered compaction and
`iterate_upper_bound`). For BergDB: `full_history_ts_low` is the first
available time, and "keep the newest version below it" is what reclaim
must keep when it rewrites a node. Leaving all to reclaim gives LSM-like
behaviour: no scan bound until reclaim has passed (020-24-16's job queue).


## 6. Summary for 020-30

1. Frans's 2012 intent is his 2026 rule: the transaction that empties a
   node removes it from its parent; a shrunk node was to be merged. Both
   were postponed in 2012 and never done.
2. Structures with a scan bound in live keys (MVBT, LMDB, Btrfs) unlink
   and merge in the deleting transaction. Those that leave it to
   background work (LSM, CouchDB, TSB-tree) have no bound until it runs.
3. All free the bytes only after the oldest snapshot or horizon: in
   BergDB, the retain duration, reclaim and its cut.
4. Unlinking empty nodes alone leaves a worst case of one live klong per
   node; MVBT's merge of underfull nodes is what bounds that case.

Sources: Becker, Gschwind, Ohler, Seeger, Widmayer, "An asymptotically
optimal multiversion B-tree", VLDB Journal 5(4), 1996. Lomet, Salzberg,
"Access methods for multiversion data", SIGMOD 1989; "Access method
concurrency with recovery", SIGMOD 1992. Rodeh, "B-trees, shadowing, and
clones", ACM TOS 3(4), 2008. LMDB `mdb.c`. CouchDB docs (compaction,
`_purge`). RocksDB wiki (DeleteRange) and commits #7556, #7740, #7884,
#9116 (`full_history_ts_low`).
