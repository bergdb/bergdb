R2 attachments
==============

Base: b1651a5. Run from `/Users/f/fl/bench/016/R2`.

All programs use one JVM at a time and put temporary data under out/R2.
The lock probes use a short Python process for native POSIX locks; they
do not launch another JVM. No Db is left running.

```sh
mkdir -p out/R2/classes out/R2/tmp
javac --release 17 -cp repo/java/build/bergdb.jar -d out/R2/classes out/R2/*Probe.java
```

Run one probe at a time:

```sh
java -ea -cp out/R2/classes:repo/java/build/bergdb.jar bergdb.core.LockLoaderProbe out/R2 repo/java/build/bergdb.jar
java -ea -cp out/R2/classes:repo/java/build/bergdb.jar bergdb.core.CutEndProbe out/R2
java -ea -cp out/R2/classes:repo/java/build/bergdb.jar bergdb.core.FailedOpenProbe out/R2
java -ea -cp out/R2/classes:repo/java/build/bergdb.jar bergdb.core.Max2GProbe out/R2
java -ea -cp out/R2/classes:repo/java/build/bergdb.jar bergdb.core.NegativeAppendProbe out/R2
java -cp out/R2/classes:repo/java/build/bergdb.jar bergdb.core.NegativeAppendProbe out/R2
java -ea -cp out/R2/classes:repo/java/build/bergdb.jar bergdb.core.CloseLockProbe out/R2
java -ea -cp out/R2/classes:repo/java/build/bergdb.jar bergdb.core.IoInterruptProbe out/R2
```

The first five probe classes reproduce the reported faults. The last two check correct
close/open exclusion and retry after interrupts inside real JDK I/O calls.
The saved output files contain only the small result summaries.

`R2-regressions.patch` adds five Nano methods to FileStream's embedded
tests against b1651a5; it makes no production change. In a fresh clone:

```sh
cd repo
git apply ../out/R2/R2-regressions.patch
cd java
sh build.sh
java -ea -cp build/bergdb.jar bergdb.dev.Unit -c bergdb.stream.FileStream -m testReviewCutAtEmptyEnd
java -ea -cp build/bergdb.jar bergdb.dev.Unit -c bergdb.stream.FileStream -m testReviewCutAtNonemptyEnd
java -ea -cp build/bergdb.jar bergdb.dev.Unit -c bergdb.stream.FileStream -m testReviewMax2GJump
java -ea -cp build/bergdb.jar bergdb.dev.Unit -c bergdb.stream.FileStream -m testReviewUncheckedOpenClosesHandle
java -ea -cp build/bergdb.jar bergdb.dev.Unit -c bergdb.stream.FileStream -m testReviewNegativeAppendRejected
```

All five report `FAILURE` on the base production code, as recorded in
`regression-tests.output.txt`. Unit exits 0 even on a printed failure;
check its result text. The review clone already contains these test-only
edits and was rebuilt for these five checks. Do not apply the patch twice.

`Max2GProbe` uses sparse extension and omits forces to exercise size
selection without physical gigabytes of writes. It generates its prefix
through public append/close/reopen calls, rather than fabricating a
directory layout. It is not a power-loss or performance measurement.

`FailedOpenProbe` closes its captured data handles. The directory lock
leaked by the failed Error constructor has no returned public owner;
that lock ends when this short probe's JVM exits. No Db is started.
