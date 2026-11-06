019-21. Fix: a start counts the startup section's nodes before its rerun changes them
=====================================================================================

Status: done 2026-11-06, night 006-12. Kind: Fix. Frans: none.
Created 2026-11-06 by Frans Lundberg.

What: an ordinary start (`DbStarter.doOrdinaryStartup`) registers the
nodes of the startup section in the node table (`registerSectionNodes`),
which counts them (`Residents.added`), and then reruns the transactions
after the startup position (`rerunTransactions`), which adds klongs and
values to those nodes (`KeyNode.addKlong`). Nothing counts them again:
they stay counted below their bytes, the rerun's changes not counted,
until they are written or evicted.

Why: as 019-20: the resident bytes, the capacity controller's measure, are
to be exact but for the objects the writer changed since their last count
(`Residents`). A database opened for reads writes nothing, so the
difference stays for as long as it runs. Its size: the rerun's klongs and
values in the section's nodes, bounded by the startup distance.

Source: harness 6.5 of 018-01 (018-05, `EvictionAccountingTester`), its
recount after a restart, unit seed 2: "the clean object of node 4293 is
counted with 430 bytes, its bytes now 608". Traced: `added` in
`registerSectionNodes`, then `addKlong` from `DbStarter.rerunTransaction`.

Frans: none.

Done when: a test that fails before the fix passes after it, and the
harness's recount passes after its restarts; `before-commit.sh`;
`level4.sh` (full).


Log
---

2026-11-06. Found by harness 6.5 (018-05) in night 006-12, registered and
fixed there.

* Fix: after the rerun, `doOrdinaryStartup` counts each object of the node
  table with its bytes now (`Residents.resync(cache.nodes())`, by
  differences, as 015-69 made it). Javadoc of `Residents` (the class,
  `resync`).
* Test: `Residents.testSectionNodesCountedAfterRerun` (unit group): 20
  transactions of three keys of 50, a startup distance of 3,000 bytes, a
  restart; then every clean object of a live handle is counted with its
  bytes now. Before the fix: "the clean object of node 3487 is counted
  with 303 bytes, its bytes now 362"; after it, none.
* P1 to P12 (010-01): one pass over the node table once per start, whose
  objects the start itself made (the section's nodes and the rerun's): no
  more than the start's own work (P5, 007's bounded start); no setting,
  thread or API. Eviction does not change the stream's bytes.
