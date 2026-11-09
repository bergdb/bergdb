021-18. Fix: GetMany.Prefix stops at the prefix's own key
=========================================================

Status: done. Kind: Fix. Frans: none.
Created 2026-11-09 by Frans Lundberg.

What: the Core's stop conditions `GetMany.Prefix` and `GetMany.PrefixN`
stopped at a key equal to the prefix, as `Keys.isPrefix()` is a strict
prefix. So the usual prefix scan, `startKey` the prefix and `inclusive`
true (its default), gave no KV at all whenever the prefix was itself a
key, and a backward scan left that key out. The Javadoc said "Stops when
the key is no longer has a given prefix". Found by a new-user
application, 020-24-09, U9-1 (high for Core users); the reproduction
`Probe2 DIR prefix` in `/Users/f/fl/bench/2026-11-09/app-u9/app/src/`.

Why: a Core user who scans `user/` and has a key `user/` gets an empty
result and no error.

Frans: none.

Done when: a test that fails before; the two stop conditions add the
prefix's own key and their Javadoc says so; every other user of
`Keys.isPrefix` checked for the same assumption; `BEFORE COMMIT OK` and
`java/stress/level1.sh` under the gate lock; a line in `releases/next.md`.

First step: the stop conditions and `Keys.isPrefix`.


Log
---

2026-11-09. Registered by coord-1109 from 020-24-09's U9-1, and taken by
its agent c18b (clone `clone-c18b`, on main's 62345d3).

2026-11-09. Done by c18b: the commit "021-18: ..." in `clone-c18b`, to
land. Severity: high for Core users, as 020-24-09 gave it. In 2026.1 to
2026.3: the code is the 2017 baseline's.

* Fix: `GetMany.hasPrefix(prefix, key)`, `Keys.isPrefix` or
  `Arrays.equals` (a key has one segment array, `Keys.toSegments`), used
  by `Prefix` and `PrefixN`; their Javadoc says that the prefix's own key
  is added, and that a forward scan from the prefix, inclusive, gives
  every key with it. `Keys.isPrefix` stays strict, as its callers below
  rely on or do not mind.
* Test: `DbTesterGetMany.testPrefixHasThePrefixKey`: nine keys around a
  segment of 7 bytes and the empty key, twelve prefixes (keys and not);
  forward inclusive and exclusive, `PrefixN` of 100 and 1, backward from
  the last key with the prefix. It failed before: `prefix "", Prefix,
  expected [, a, ab, abc, abcdefg, abcdefgh, abcdefghi, abd, b], got []`.
* The other users of `Keys.isPrefix`, each right as it is:
  * The Pub API's listing (`UsePrimaryBuilderImp.Page`): its prefix is
    the directory's file prefix, the idir and '-'. A key equal to it is
    the ikey of a ukey that ends with '/', which `PubKeys.u2i` refuses, so
    no key of the Pub API. A forward listing starts after the prefix
    (exclusive, or at the prefix and a name, which `startAt` refuses
    empty); a backward one that stops at the prefix's own key has passed
    every key under it.
  * Index builds (`IndexBuilderImp.lastKeyOfDirectory` and `step`): the
    same prefix; the build starts at it, exclusive, and ends at the last
    key strictly under it.
  * `IndexManager.scan`: takes the prefix's own key already (020-16,
    F16-2, the same fault, fixed there with `Arrays.equals`).
  * Index scans (`UseIndexBuilderImp`): bounds [lo, hi) with
    `Keys.compareKeys`; no `isPrefix`.
  * Reclaim: none in `Reclaim`. `ConnectionImp.isReclaims` tests
    `Reclaim.KEY_PREFIX_SKEY` ("/#i/dreclaim/"), whose own key reclaim
    never writes (its table and rows are under it).
  * The internal prefix "/#i/" in `ConnectionImp.transactionInfo()`,
    `DbScan` and `DbUtil`'s checksums: BergDB writes no key equal to it.
    For `transactionInfo()` it is no ukey's key and is left out anyway
    (`PubKeys.i2uOrNull`); in the checksums, tools of tests, such a key
    written through the Core counts as a user's, the same way in both
    databases compared.
  * Testers (`PubTesterPrimary.internalKeys`, `PubTesterIndex`,
    `PubTesterIndexRaces`): exclusive starts, or no such key.
* Not changed, for 022: the C port has the same stop conditions
  (`items/022-bergdb-c/c/src/getmany.c`, `prefix_handle` and
  `prefix_n_handle` with `keys_is_prefix`), and `bergdb.h`'s read range
  documents the strict prefix ("a key equal to the prefix stops the
  read; start after it"). It is to follow Java in 022's next round,
  before `test/cross`'s `JAVA_REF` moves past this commit: the cross
  test's `prefix10` (`test/cross/java/Dump.java`, a `PrefixN` of 10 from
  the first half of a sampled key, inclusive; the key itself for a key of
  one byte) gives the prefix's own key in Java now, and C would differ.

Runs, under the gate lock (2026-11-09), on the tree of 021-18 and 021-19:
see 021-19's log.
