# Level 3 power-loss ordering

011-07. Moved here from `docs/level3-durability.md` on 2026-10-26 (006-07); history, not kept up to date.

Codex for Frans Lundberg, 2026-10-14.

The FileStream power-loss ordering work is implemented. It establishes the
tested recovery behavior under a fault model and verifies the actual force
operations on macOS/APFS and a Linux VM. It is conditional on the OS and
storage stack honoring successful force operations; no physical power-cycle
or independent hardware certification was performed.

The baseline is this repository's `bdba113`, plus the uncommitted changes
listed here. All source inspection and implementation used this repository.
The original buffer timing, retention policy, format and reclaim parameters
are preserved. Infinite retention remains the default. Level 4 is not
implemented; the longer soak and performance reference are still pending.

## Production changes

`FileStreamIo` is a package-private boundary for physical operations and
fault injection. `FileStream` opens files with `rw` and explicitly calls
`FileChannel.force(true)` after each appended file chunk before returning
completion to `BufferedStream`. It forces a new backing file and its directory
entry before publishing it. Newly created directory ancestors and the database
directory's immediate parent are forced during creation/opening.

Each prefix unlink or debug rename is followed by a directory force before
the next removal. Forcing only after the whole deletion batch would permit
an older name to survive while a newer one disappears, leaving a hole that
FileStream would reject before it could read the reclaim table. A failed
force stops further deletion. Already existing ancestors outside the
created path are assumed to be durably established by their owner.

`BufferedStream` now reports a deferred pretruncate failure through the same
failure path as a failed append. Previously it saved the exception but still
published the flushed length and notified the durability listener. The new
regression fails with the original `BufferedStream` class: **failed pending
cut acknowledged**. It passes with the correction and the durable frontier
stays unchanged after the injected failure.

`FileStream.close()` releases remaining handles even after an earlier I/O
failure or partial deletion, while preserving the original error. Failed
construction also releases already opened files. The force-failure tests
check for leaked handles.

The public stream contract now states the persistent-backend requirement:
append completion supplied to StorageManager must mean forced bytes and
backing-file names, rather than just read visibility. This validation covers
FileStream and wrappers delegating to it. Memory/test streams, including the
non-forcing OneFileStream test helper, do not acquire a hardware guarantee.

## Fault model and checks

`FileStreamPowerLossTester` replaces physical force operations while using
the production FileStream control flow and real temporary files for volatile
contents. It separately tracks forced byte arrays, durable file names and
pending removals. A cut never implicitly forces replacement bytes.

Power-loss images include loss of an unforced tail, survival of an arbitrary
prefix of that tail, deletion surviving while replacement data or names are
lost, rollback of the latest unlink, and out-of-order survival of unforced
unlinks. The directory-order negative control exposes a hole when intermediate
forces are omitted. Images are bounded reservoirs per checkpoint family;
the model does not keep a new whole-database copy for every event.

The database trace has puts, deletes and reinserts on 12 long keys, values
of 1–2 KB and occasional 18 KB values, a 20 KB startup distance and two-second
retention under a deterministic clock. Checkpoints cover append/force/open/
delete boundaries, writeout progress, iteration end, cut decisions and durable
publication. The synthetic clock and small overrides force many cuts; this
is correctness evidence, not a representative long-duration workload.

Each selected image starts a fresh Db over restored backing files. Checks
compare the current recovered state and retained historical states with the
transaction model at the actual recovered time, retain acknowledged commits
and acknowledged lookup frontiers, and enforce the retention boundary at the
image's logical time. Recovery is followed by a write, sync, another cold
restart and readback. The smaller functional case exhaustively checks the
available user-transaction times; stress cases sample history and check all
keys at each selected time.

Nine unit tests cover force barriers, failed file/directory forces, failed
deferred cuts, partial deletion, leaked handles, per-unlink recovery and the
unordered-deletion negative control. Two functional tests cover cold database
recovery and omitted file/directory-force negative controls. The full Level 3
gate adds eight stress seeds, 1,500 transactions each and 440 initial cold
recovery images, each followed by a second restart. Omitting file forces
produces inconsistent surviving file offsets; omitting directory forces loses
all backing names after an acknowledged commit. Setup failures do not count
as successful negative controls.

## Native force audit

`java/stress/flush-order.sh` runs a small creation/rotation/append/deletion
probe and validates real system-call ordering with
`java/stress/validate-flush-trace.py`. The macOS dyld interposer is test-only;
BergDB has no added native-library dependency. Linux uses strace. The trace
requires every replacement file's last write and name to be forced before
unlink, and a directory force between prefix deletions and after the last one.

| Target | Environment | Native result |
|---|---|---|
| macOS | 27.0.1, arm64, APFS; Homebrew OpenJDK 27 build 27 | Four writes, nine successful file `F_FULLFSYNC`, twelve successful directory `F_FULLFSYNC`, two deletions; no weaker fsync fallback |
| Linux VM | Docker Desktop, Linuxkit 7.0.12 aarch64, overlay filesystem; Temurin 21.0.12.1+1 LTS | Four writes, nine successful file `fsync`, twelve successful directory `fsync`, two deletions |

The installed macOS JDK's FileChannel dispatcher was also checked through
bytecode and native disassembly: its force path calls fcntl command 51
(`F_FULLFSYNC`). FileDescriptor.sync follows the weaker fsync path. On Linux,
force(true) reaches fsync. The actual successful calls above are recorded
separately from these implementation inspections.

Apple explains why database write ordering needs a full device-cache flush.
[Apple fsync manual](https://developer.apple.com/library/archive/documentation/System/Conceptual/ManPages_iPhoneOS/man2/fsync.2.html).
The Unix force implementation distinguishes fsync and fdatasync.
[OpenJDK UnixFileDispatcherImpl](https://github.com/openjdk/jdk/blob/master/src/java.base/unix/native/libnio/ch/UnixFileDispatcherImpl.c).
These sources explain the primitives; the native traces identify the tested
runtime behavior.

## Validation and reproduction

The full macOS **Level 1, Level 2 and Level 3 gates passed**. Level 3 includes
**905 unit tests**, **37 functional tests**, 200 reclaim-stress rounds,
four byte-identical reclaim/restart traces, 25 random crash rounds, and 36
concurrent-reader rounds with zero incorrect gets/scans. The file-backed
load case made six cuts, with a restart and full key check after each cut.
The new power-loss stage passed **eight seeds / 440 initial cold recovery
images**, each followed by another write, sync and restart. Both omitted-force
controls detected recovery loss; the unordered-unlink control also passed.

Linux passed **905 unit tests**, **two focused functional tests**, **eight
power-loss seeds / 440 cold recovery images**, both database negative controls,
and the native force audit. The unordered-deletion negative control is also
part of the unit tests. Linux is a VM test, not a bare-metal drive power test.

The macOS runtime was Homebrew OpenJDK 27 build 27 on macOS 27.0.1 build
26A434, arm64/APFS. Linux used Temurin 21.0.12.1+1 LTS on Linuxkit 7.0.12,
aarch64/overlay, in a disposable Docker Desktop container (Engine 29.7.2).
Compilation targeted Java 8 using `--release 8`; Java 8 runtime behavior was
not tested. No Lean source changed, and no implementation claim is inferred
from the abstract proofs.

A final integration build included the concurrent performance-harness
additions without changing them. It passed all 905 unit tests and both new
functional tests. Its 1,052 library class files are byte-identical to the
full-gate build. The native validator distinguishes and rejects fdatasync,
and was checked against both real traces and a weakened trace. Negative
controls accept explicit inconsistent-file/incorrect-state failures; ordinary
setup I/O exceptions escape the control and fail the test.

Source identity is baseline `bdba113885b26eaac76cae37d271d590f3d3ec54` plus
the delivered working-tree diff. Each source manifest lists 427 Java source,
dependency, build and stress files. Their SHA-256 values are:

* `gate-source-manifest.json` and `source-manifest.json`:
  `24844caa1f0b7f079a7861b1d0dde401801977dacd1f0f641d25d0ff6e114e56`.

The installed macOS binaries inspected were `libnio.dylib` SHA-256
`8e8eaac1d06689e8136d41cf1ecb071e8299c6d894f360dc86a289b122129c90`
and `libjava.dylib` SHA-256
`41ebeeed1a0ceb1572e45ed8a8ffb3c83c090bd8ce8041d82152b23f4e6979a8`.

```sh
cd java
export JAVA_HOME=/opt/homebrew/opt/openjdk/libexec/openjdk.jdk/Contents/Home
export PATH="$JAVA_HOME/bin:$PATH"
./build.sh
java -ea -Xmx2g -cp build/bergdb.jar bergdb.dev.Unit
java -ea -Xmx2g -cp build/bergdb.jar bergdb.dev.F -c 'bergdb.stream.FileStreamPowerLossTester'
java -ea -Xmx2g -cp build/bergdb.jar:build/stress bergdb.stream.PowerLossTest 1 8 1500 3
sh stress/flush-order.sh
sh stress/level1.sh
sh stress/level2.sh
sh stress/level3.sh
```

The native audit additionally needs clang and Python 3 on macOS, and strace
and Python 3 on Linux. The existing build uses unzip. The Linux test image was
`eclipse-temurin:21-jdk`, pinned to
`sha256:f9bf7e9fe2f9bc4657537c1a7e20c768f0c3bafca41598263be4714783dd62eb`,
with disposable test data inside the container. Raw logs, the runtime metadata,
the original-buffered-class regression log and source identity are retained
under ignored `java/build/powerloss/2026-10-14/`.

## Limits and next work

This result assumes successful OS forces persist the requested data and
namespace, and later appends do not corrupt previously forced bytes. It does
not establish behavior with dishonest device acknowledgements, arbitrary
media corruption, torn previously durable sectors, remote filesystems,
Windows, or replication with cuts. Directory-forcing providers that reject
the operation fail opening/writing rather than silently acknowledge durability.
The Linux guest test does not validate every layer of a bare-metal or
virtualized storage stack. No reclaim theorem or hard latency bound is claimed.

The two remaining tasks in [level3-plan.md](06-level3-plan.md) measure a longer
file-backed run and produce the reproducible performance reference before
Level 4. Stronger forces and per-unlink barriers can change I/O cost; that
cost has not been benchmarked here. The buffer/group-commit scheduling stays
unchanged.
