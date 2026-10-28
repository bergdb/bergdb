005-73. Fix: seven small findings in `Db`'s API (012-03)
========================================================

Status: open. Kind: fix. Created 2026-10-28.

Registered by Claude (Opus 5.5, Claude Code), the conductor of 012, from
012-03's mapping of `Db`'s public methods to the C API (012-03, section
6.8), as 012-01's decision D5 says. None changes the stream's bytes. F1 to
F4 and F6 were shown by a probe on `main` at `0b6d08e`.


The findings
------------

* **F1.** `StartInfo.startupDistance` is −1 on every start: `startInner`
  sets it from its parameter, `StartParams.NULL` for `start()`, as
  `handleStartParams` replaces only its own local `params`.
* **F2.** `getCachePutSize()` is a constant, 10,000: `Cache3.putSize` is
  set at the construction and nothing advances it. Read only by `Jmx`.
* **F3.** `getDirtyFraction100()` and `getDirtyFraction1000()` only decay:
  `Aux.updateStats` sets `ordinaryNodeCount` to the record's node count, so
  `dirtyNodeCount` is always 0, the figures fall from 0.10 by 1 % (0.1 %) a
  transaction, and they turn NaN for good after an empty transaction (0/0).
  Read only by `Jmx`.
* **F4.** `setReclaimInternalFraction(Double.NaN)` passes `Reclaim`'s check
  (`f < 0.001 || f > 0.90` is false for NaN); the internal fraction is then
  NaN.
* **F5.** `close()` and `stop()` drop `closeStorage`'s `IOException`: a
  failed last flush is reported only by a later start that throws (as
  suppressed).
* **F6.** `GetMany.Endpoint(long[] key)`'s comment says "Non-inclusive",
  but the code makes it inclusive (`this(key, true, false)`).
* **F7.** Dead fields: `GetMany.cache` is read nowhere; `GetData`'s
  `followMemoryPointerCount` and `followStreamPointerCount` are only
  written.


What to do
----------

Each is small. Recommended: F4 refused as an argument error (it can make
reclaim's arithmetic NaN; 012-02, section 10.4, D9 has the same for a
stored startup distance), F5 reported by `close()` (as the C clone does,
012-03, D10), F6's comment corrected, F1 set from the distance in force;
F2, F3 and F7 removed or fixed with `Jmx` (P12: a small Core), or left.
Frans decides which, and whether they wait for a release.

For 012: the C clone does as Java does where it has the behaviour (F1's
−1, F4, F6's inclusive end); it leaves out F2, F3 and F7 (read only by
JMX); F5 is a departure written in 012-03 (D10).


Done when
---------

Each finding fixed or accepted, the fixes with `before-commit.sh`.
