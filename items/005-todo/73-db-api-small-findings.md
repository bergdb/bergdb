005-73. Fix: seven small findings in `Db`'s API (012-03)
========================================================

Status: done. Kind: fix. Created 2026-10-28. Closed 2026-11-02.

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


Note: 005-79
------------

2026-10-29, Frans (15:48): 005-79 makes `setReclaimInternalFraction`
take an integer (parts of 2^16 or per mille), so the NaN that the double
setter accepts goes with it; the range check stays (0.001 to 0.90 in the
integer's unit).

2026-11-02: Frans chose to fix NaN rejection here and deal with 005-79
separately. The setter continues to take a double.


Implementation, 2026-11-02
--------------------------

Frans approved the recommendations for 005-73, initially deferring F4
to inspect `setReclaimInternalFraction`. After review he approved F4's
NaN rejection too, with 005-79 to be handled separately. The double API
and reclaim's arithmetic stay as they are.

* **F1 fixed.** `StartInfo.startupDistance` reports the distance in force
  after startup, including the stored setting at a restart.
* **F2 removed.** The constant `Cache3.putSize`, `Db.getCachePutSize`,
  JMX's attribute and its derived speed attributes are gone. The manual
  interactive tool reports resident bytes instead.
* **F3 removed.** Both dirty fractions, their JMX attributes and the
  unused node counters in `Aux` are gone. Transaction and KV counts stay.
* **F4 fixed.** `Reclaim.setInternalFraction` explicitly rejects NaN
  with `IllegalArgumentException`, before changing the setting. The
  existing inclusive range, 0.001 to 0.90, and double API are unchanged.
  A regression checks NaN, both infinities, values immediately outside
  the range, both valid endpoints, and an unchanged setting on refusal.
* **F5 fixed.** `close()` throws `StreamIoException` for a failed final
  flush or storage close, after cleanup. The first I/O failure is retained
  under `closeLock`, so callers waiting for another close, and repeated
  calls, report it too. `stop()` returns immediately as before; a later
  `close()` waits and reports its failure. A close inside a transaction
  still closes directly when another closer is waiting for the write
  lock, and now reports that close's I/O error too. A failed start still
  adds its cleanup error as suppressed to the startup exception.
* **F6 fixed.** The endpoint constructor's comment says inclusive.
* **F7 partly corrected.** The unused `GetMany.cache` field and the
  assignment to it in `LargerThanMemory` are removed; that assignment
  never disabled caching. The two `GetData` pointer counters are **kept**:
  the finding that they were only written was wrong. The manual `Huge`
  benchmark reads them and `Dag.newGetData` installs their listener.

Validation is recorded in [73-db-api-small-findings/](73-db-api-small-findings/).
The three new regressions fail against the original code: startup info
reports −1, the final flush failure is discarded, and a block exception
has no suppressed storage-close failure. The final-flush regression also
checks `close()` after `stop()` and repeated `close()` calls.

Initial validation, before F4: `BEFORE COMMIT OK` (1,089 unit tests, 78 f-tests,
96 s); all 36 StreamDigest results identical to the baseline. No level
mechanism or stream format changed. Java only; the C clone is unchanged.

F4 validation and closure, 2026-11-02: its regression fails against the
original setter on NaN and passes with the check. `BEFORE COMMIT OK`
(1,090 unit tests, 78 f-tests, 95 s); all 36 StreamDigest results still
identical. All findings are now fixed, removed or corrected as recorded
above. Status changed to done; 005-79 remains separate.
