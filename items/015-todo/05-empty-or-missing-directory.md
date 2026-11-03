015-05. Decide: a start on an empty or missing directory creates a database
===========================================================================

Status: open. Kind: Decide. Created 2026-11-03 by Frans Lundberg.

For Frans, after release 2026.2. 015-01's case 3: a volume that is not
mounted, or a wrong path. The directory is empty or missing; the start
creates it (with its missing parents, `mkdirs`) and a new database in it,
and says nothing. 015-01's fix (A with A+) covers cases 1 and 2, where
`created.txt` shows that a database was there; it cannot cover case 3
without a change of the Pub API's usage.

The options (015-01, "The options"):

* B1: `start()` refuses a directory with no stream byte unless the
  builder was told `createIfMissing()` (as LevelDB's and RocksDB's
  `create_if_missing`, false by default). Covers case 3. Every program
  that creates a database must call it: about 40 builder calls in the
  repository, the Javadoc's examples and README. A new setting (P10).
* B2: the opposite default, with a new `mustExist()`. Compatible, but
  protects only the programs that call it; 015-01's Javadoc recipe (check
  `created.txt` before `start()`) gives the same with no new method.
* E: create only the last directory (`mkdir`, not `mkdirs`). Covers a
  missing mount point (macOS's `/Volumes/X`), not an empty one (Linux's
  `/mnt/x`). Changes `dir()`'s promise.
* Nothing more: case 3 stays a known issue, with the recipe.

Recommendation: B1 in the next release with a public API, since it is
the only option that covers case 3, and 2026.2 is internal (016-01, D1);
until then the recipe. Frans decides.

Done when: Frans has chosen, and the choice is an Implement entry or a
known issue.

Found 2026-11-03 in 015-01's study.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).

2026-11-03, 17:18. Frans: "As recommended." B1 after the release; a known
issue of 2026.2 until then, with the recipe in `DatabaseBuilder`'s Javadoc.
