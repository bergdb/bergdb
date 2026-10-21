005-21. Fix: smaller overflows
==============================

Status: open. Kind: fix. Created 2026-10-21.

Found on 2026-10-21 in a review of the Java code for overflow, by Claude
(Opus 5.5, Claude Code), at Frans's request. Each is unlikely, or latent;
together in one entry and one commit.


The issues
----------

1. `Time.millis(long)` multiplies by 10,000 without a check:
   `Time.millis(1844674407370956)` is a time in 1970 (8,384 units), not an
   exception.
2. `TimeResolver` reads the seconds as a `double` and casts to `int`: any
   seconds from 2^31 up give 2081-01-19 03:14:07, and `NaN` seconds give
   0.
3. `TransSeq.take` computes `valueCount * 4` in `int`. Not reachable (more
   than 536 million values in one transaction), but the unit tests pass
   `Integer.MAX_VALUE` as "no limit" and get a limit of 2,097,147.
4. `Keys.hash` makes the hash non-negative with `-value`, which stays
   negative for `Long.MIN_VALUE`. Real keys cannot give it (the hash is
   always odd: 37 is odd and every segment a multiple of 8), but `KeyModSet`
   uses the hash as an array index, checked by an assert only, and
   `Trans.Builder.addReadHash` and `addVirtualWriteHash` take any `long`;
   a negative write hash throws in `stmRecordKeys`, after the go point.
5. `DbObject`: a field name is checked in chars (`name.length() >
   Short.MAX_VALUE`) but stored as a `short` count of UTF-8 bytes; the field
   count is a `short` checked by an assert only, and 65,535 fields would
   read back as the null object.
6. A corrupt record or node gives `NegativeArraySizeException` instead of
   `StreamFormatException`: `StoredTrans.Parser` (`new long[gotDirtyCount *
   2]`) and `StoredTopNode.parse` (the skip pointer count, a signed byte).


The fix
-------

1. `Math.multiplyExact`; an overflow is an `IllegalArgumentException`.
2. Seconds that are not finite, negative, or do not fit an `int` are a
   `BadFormatException`.
3. `valueCount * 4L`.
4. `Keys.hash` maps a negative value with `& Long.MAX_VALUE` after the
   negation, so the result is never negative; `KeyModSet` takes the index of
   `hash & Long.MAX_VALUE`; `addReadHash` and `addVirtualWriteHash` refuse a
   negative hash.
5. The name's byte length and the field count are checked, with an
   `IllegalArgumentException`.
6. The counts are checked against the bytes there are, with a
   `StreamFormatException`.


Done when
---------

* A unit test for each, where it can be made.
* `java/before-commit.sh` prints `BEFORE COMMIT OK`.
