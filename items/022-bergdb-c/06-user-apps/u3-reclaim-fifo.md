# 022-06 U3-1 and U3-2: reclaim under a log keyed by time

Created 2026-11-09 by Frans Lundberg. Status: open; the cause and the
fix are Java's (coord-1109).

Worker f1 of the session `022-bergdb-c`. User u3 of the C library
(022-06-3, `/Users/f/fl/bench/022/apps/u3/report.md`) found two medium
bugs in an audit log whose keys are in time order: a FIFO of keys, the
newest put and the oldest deleted, with a retain duration set.

* U3-1: reclaim stops cutting after a while. The first available time
  falls behind, and the directory grows without a bound, though the live
  data is under 1 MB.
* U3-2: now and then a transaction of one put and one delete writes a
  record of MBs, and these records grow with the run.

**In short.** Java's Core does the same. For the same workload, C's
stream equals Java's byte for byte, and C's cuts stop where Java's do
(section 3). So this is not a fault of the port. C changes nothing
and follows Java's fix when a release that C ports has it. The cause is
with coord-1109's agent g30. Its lead is reclaim's step, which touches
its key range at the current time, the deleted keys too (Reclaim's class
comment). The fix goes on Frans's list.


# 1. The workload

u3's `repro_fifo.c`:

* One transaction puts one record under `/t/` and the transaction's time
  in 16 lowercase hex digits, an ikey of 19 characters. The value is
  80 to 479 bytes.
* From the 1,024th transaction on, it also deletes the key put 1,024
  transactions back. So 1,024 keys are live, about 300 KB.
* A test clock of 1.5 ms per transaction, from 17626464000000000.
* A startup distance of 2,000,000 bytes, and a node size of 30.
* A retain duration of 20 s, set before transaction 1,000.
* 300,000 transactions.

c/readme.md, section 9, point 9, promises that "the directory stays within
what the retention needs". So does Java's Level 3 (`docs/levels.md`,
section 6): an iteration every quarter of the retain duration, once the
stream has grown by twice the startup distance, here every 4 MB. The
stream kept should be the retention window plus one or two iterations'
spans.


# 2. C

u3's `repro_fifo.c`, built against `c/build/release/libbergdb.a` of
int.git's `2026.4` at `c6d8628` (`clang -O2 -flto`), gives exactly u3's
numbers with the user kit at `391c3cf5`:

* 16 cuts, the last between transactions 225,000 and 230,000.
* At the end, the first available time is 129.7 s back, with a retain
  duration of 20 s.
* The directory grows from 65 MB at transaction 230,000 to 115 MB.
* The stream is 224 MB.
* The largest record is 5,108,904 bytes, at transaction 213,939.
* The program prints `NOT CUT` and exits 1.

Before the stop, each cut leaves the first available time 20 to 27 s
back, as it should with 20 s.


# 3. Java, and C beside it

The same workload in the cross harness's format, `bergdb-workload 1`, is
section 5's generator. Java's `bergdb.cross.Run` and C's `bergdb-run`,
which take the same text, ran it. The harness was built with
`JAVA_REF=git:a2fa9df440383c9197181150a10dfbb9e3b839de`, `main` at
2026-11-09 with 021-14. Run's setup is `testSetupExceptStream`: the test
clock, the test id and no eviction.

**Equal.** For the workload with a sync every 5,000 transactions, the two
outputs are identical, 300,065 lines each: every transaction's `tt`,
`tpos` and `lastPos`, and every `status` line. The 22 stream files of the
two directories are equal byte for byte. Without the syncs it is the
same: identical outputs, 22 equal files, the same end state. Java's run
took 15 s.

**Java's cuts.** From the `status` lines after each sync. "Back" is the
first available time's distance from the clock, in seconds:

| After tx | Stream | First available | Back |
|---|---|---|---|
| 25,000  | 14,664,504  | 4,000,424  | 23.8  |
| 40,000  | 24,675,096  | 8,001,256  | 24.2  |
| 45,000  | 28,794,184  | 12,001,632 | 20.5  |
| 55,000  | 36,621,640  | 16,001,984 | 24.4  |
| 60,000  | 41,135,456  | 20,002,224 | 23.8  |
| 65,000  | 43,890,568  | 24,003,456 | 21.8  |
| 75,000  | 51,903,448  | 28,003,464 | 26.4  |
| 80,000  | 56,265,768  | 32,749,632 | 21.8  |
| 90,000  | 61,934,480  | 38,039,856 | 23.2  |
| 100,000 | 72,859,688  | 44,171,440 | 22.2  |
| 115,000 | 84,306,016  | 51,147,848 | 26.5  |
| 125,000 | 89,693,600  | 59,159,800 | 20.4  |
| 150,000 | 108,963,464 | 68,456,840 | 27.4  |
| 165,000 | 121,445,224 | 79,062,480 | 20.3  |
| 195,000 | 144,326,616 | 94,443,912 | 24.7  |
| 300,000 | 226,557,072 | 94,443,912 | 182.2 |

* The first seven cut points are 4 MB apart, as designed. Then the gaps
  between cut points grow: 4.7, 5.3, 6.1, 7.0, 8.0, 9.3, 10.6 and
  15.4 MB, and the time between cuts with them.
* After the 15th cut, made by transaction 195,000, there is none to the
  end. The stream grows from 144 to 227 MB and the directory reaches
  137 MB. At the end the first available time is 182 s back, with a
  retain duration of 20 s (U3-1).

**Java's large records (U3-2).** These are the records of one-put
transactions, `lastPos - tpos + 1`, over 1 MB. There are 20 of them, and
they grow:

* 1,067,240 bytes at i = 45,559 and 1,371,944 at 59,670.
* 2,040,264 at 92,935 and 3,345,048 at 132,131.
* 4,170,176 at 180,041, the largest.
* Then 1,004,280 at 222,868, growing again to 3,127,816 at 295,719.

C's records are the same, as its output is Java's.

u3's program stops at another place than the workload: 16 cuts against
15, and 129.7 s back against 182.2 s. Its stream differs from the
workload's from the start (13.9 MB at transaction 25,000, against
14.7 MB). The program has a random database id where Run has the test
id, and values of one repeated letter where the workload's are random
bytes of the same lengths. The memory budget makes no difference: with
`set budget 200000000`, C's output is the same as with no eviction. The
syncs make none either. In both, the cuts stop and the records grow.

**coord-1109's g30**, by the session, 2026-11-09: g30 reproduced it with
Java's Core API (a test clock of 1.5 ms, sd 2 MB, retain 20 s, 300,000
transactions):

* The last cut is before transaction 210,000.
* The first available time is 182 s back, and the directory is 135 MB.
* 20 records are over 1 MB, the largest 4.17 MB.

Java 2026.3 gives the same stream as `main`, so it is not a regression.
The C port of 2026.3 (int.git's `022`) writes 2026.3's bytes, so it
has it too.


# 4. The cause, and what to do

**The cause** is with coord-1109's g30, on Reclaim's step. A step "touches
the same key range at the current time (Trans.touch): every index node on
the way gets dirty and is written again, also nodes that hold deleted keys
only" (Reclaim's class comment). Under a FIFO of keys in time order, the
deleted keys are all in front of the live ones. Not worked on here, at the
session's word.

**Changed in C:** nothing. C's stream is Java's (section 3), and a C that
cut here and Java did not would break the port's first rule: Java's bytes
(c/readme.md, "Which Java").

**Recommended:**

1. Fix it in Java, on Frans's list. C follows Java's fix byte for byte in
   the release that C ports next with it (2026.4, if the fix makes the
   candidate).
2. With the fix, add a small form of this workload to
   `c/test/cross/workloads/` (and Java's own test), so that both sides
   check that the cuts keep coming. It needs to fail before the fix, so
   choose its length by a run with the fix: here the cuts stop only after
   190,000 transactions, which is too long for `cross quick`.
3. Until the fix, the release notes should name the limit. A log keyed by
   time, with deletes of the oldest keys and a retain duration, can stop
   reclaim's cuts and write records of MBs. c/readme.md, section 9,
   point 9, holds only once Java's fix is in.


# 5. The reproduction

Files in `/Users/f/fl/bench/022/f1/repro/`:

* `fifo-wl.py`, the generator below.
* `fifo300k.wl`, its output for 300,000 transactions with a sync every
  5,000, 23 MB.
* `java-a2fa9df.out` and `c.out`, the two equal outputs.

The commands, from `items/022-bergdb-c/c` of a clone of int.git's
`2026.4`:

    JAVA_HOME=/opt/homebrew/opt/openjdk \
        JAVA_REF=git:a2fa9df440383c9197181150a10dfbb9e3b839de test/cross/java-build.sh
    python3 fifo-wl.py 300000 5000 > fifo300k.wl
    /opt/homebrew/opt/openjdk/bin/java -ea -Xmx2g -cp build/java/classes \
        bergdb.cross.Run fifo300k.wl DIRJ > java.out
    ./build.sh && build/release/bergdb-run fifo300k.wl DIRC > c.out
    cmp java.out c.out; grep '^status' java.out

The generator:

    #!/usr/bin/env python3
    # u3's repro_fifo.c as a cross workload (bergdb 022-06, U3-1, U3-2).
    # Usage: fifo-wl.py NTX [SYNCEVERY (0: none)] [hashed] > FILE.wl
    import sys
    n = int(sys.argv[1])
    every = int(sys.argv[2]) if len(sys.argv) > 2 else 5000
    hashed = len(sys.argv) > 3 and sys.argv[3] == "hashed"
    T0 = 17626464000000000
    def key(t):
        kt = t
        if hashed:
            kt = ((kt * 0x9E3779B97F4A7C15) & 0xFFFFFFFFFFFFFFFF) >> 8
        return "/t/%016x" % kt
    out = sys.stdout
    out.write("bergdb-workload 1\n")
    out.write("set maxnode 30\nset sd 2000000\n")
    out.write("clock %d\n" % T0)
    times = [0] * 1024
    t = T0
    for i in range(n):
        if i == 1000:
            out.write("setretain 200000000\n")
        t += 15000
        vl = 80 + ((i * 2654435761) & 0xFFFFFFFF) % 400
        ops = "p %s r:%d:%d" % (key(t), i, vl)
        if i >= 1024:
            ops += " d %s" % key(times[i % 1024])
        times[i % 1024] = t
        out.write("t %d %s\n" % (t, ops))
        if every and (i + 1) % every == 0:
            out.write("sync\n")

`hashed` hashes the time in the key, as u3's `KEYS=hashed`, so that the
keys are not in time order; u3 saw the cuts go on then (022-06-3,
section 1.1).


# Log

2026-11-09, 18:00 to 18:15. Worker f1: reproduced U3-1 and U3-2 in C at
`c6d8628` and in Java at `main`'s `a2fa9df` through the cross harness.
C's stream equals Java's. The workload went to the session at 18:05, for
coord-1109. Nothing in `c/` changed, so the gate was not run
(022-01, section 5).
