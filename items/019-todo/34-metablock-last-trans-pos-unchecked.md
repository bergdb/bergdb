019-34. Fix: a meta block's last-transaction position past the stream gives an IllegalArgumentException at a start
==================================================================================================================

Status: open. Kind: Fix. Frans: none.
Created 2026-11-06 by Frans Lundberg.

What: recovery starts at the transaction that the last valid meta block
names (`MetaBlock.getLastTransSpos()`, the 8 bytes at offset 16). A
meta block whose checks pass but whose position names a place past the
stream's end reaches `RecoverableStream.fixLastTransactionIfNeeded`,
whose `getRemainingTransBytes` throws an `IllegalArgumentException`
("spos >= streamSize"), not a `StreamFormatException`: the start fails
with an exception that says nothing of a damaged stream, and is not the
`DbException` that a start throws for a refused stream.

Found by harness 6.1 (018-07), the full set of the night 006-12 (seed
20398), a byte flipped in the first meta block, in both the `all` and
the `take` stream:

```text
all, flip, xor 128 at 23 (meta block): the start threw java.lang.IllegalArgumentException:
  spos >= streamSize, 9223372036854775807, 8008 (at
  storage.RecoverableStream.getRemainingTransBytes:388)
all, flip, xor 255 at 23 (meta block): ... spos >= streamSize, 72057594037927935, 8008
```

Byte 23 is the position's high byte. The flip leaves the meta block valid
to recovery's checks, so they do not cover that byte (the first question
is why: which bytes the meta block's checks cover).

Why: 019-01's class (a meta block's field not checked), a fault of the
Core (018-01, W3): a violation is refused rather than used (014-01,
section 7, point 4 (a)).

Frans: none.

Done when: recovery refuses a meta block whose last-transaction position
is neither `SposNULL` nor a position inside the stream's record bytes,
with a `StreamFormatException` and nothing written (as 005-40 refuses an
unreadable meta block), or takes the meta block before it if the code's
rules say so; a test (the harness's copy: the first meta block's byte 23
flipped) that fails before the fix; the line "019-34" removed from
`CorruptStreamTester.SKIP`; `BEFORE COMMIT OK`; the stream's bytes
unchanged.

First step: `java -ea -cp build/bergdb.jar bergdb.core.CorruptStreamTester
20398 full 4` (64 s) shows the copies; read `RecoverableStream.recover`
and `readLastValidMetaBlock`.


Log
---

2026-11-06. Registered in night 006-12 by the agent of harness 6.1
(018-07), with the line "019-34" in `CorruptStreamTester.SKIP`. Not fixed
that night: found at 03:44 by the first full run, too late for a fix and
its gate before the night's stop.
