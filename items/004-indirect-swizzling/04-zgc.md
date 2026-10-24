004-04. ZGC on today's code
===========================

By Claude (Opus 5.5, Claude Code) for Frans Lundberg, 2026-10-24, at Frans's request: "OK,
for now: start with 'the ZGC run on today's code, which is cheap and decides the GC
assumption'." It follows the discussion after 004-03 of what is missing before a plan for
handles: handles remove the sweep, but not the full collections that G1 runs under
eviction.

Status: **running**, started 2026-10-24 at about 16:50. Results in section 3.


## 1. The question

Evicted objects have lived through several collections, so G1 has moved them to its old
generation by the time BergDB releases them. G1 frees old garbage only after a concurrent
marking cycle has found it. When eviction fills the old generation faster than that, G1
runs out of free regions to copy into (an evacuation failure) and falls back to a full
collection: every thread stops while the whole heap is marked and compacted, for a time
that grows with the live heap. Handles do not change this; eviction makes the same garbage.

* **P4** ([docs/level4-evidence.md](../../docs/level4-evidence.md); 8 GB heap, budget 1.6
  GB, two measured hours): 81 full collections, 22.7 s in all, median 0.27 s, and 392
  evacuation failures. A typical one: `Pause Full (G1 Compaction Pause) 8192M->1473M(8192M)
  269 ms`, the heap full and 82 percent of the old regions garbage (2,034 regions to 368).
* **004-02's 100M load** (budget 8 GB, heap 20 GB): during its sweep of 266 s, two full
  collections, 19,817 MB to 16,134 MB in 12.7 s and 16,134 MB to 16,106 MB in 16.3 s. The
  live heap, 16.1 GB, was about twice what BergDB counted as resident when the sweep began
  (7.8 GB); what the rest was is not measured.

ZGC, generational in JDK 27 (the only mode left), marks and compacts while the program runs;
its pauses stay below a millisecond whatever the heap's size. Its costs: no compressed
references (64-bit colored pointers, so every reference takes 8 bytes instead of 4, and
BergDB's pointer arrays double), barriers on reference loads, CPU for its own threads, and
a failure mode of its own, the allocation stall: a thread that allocates waits until the
collector has freed memory.

* **Z1 Pauses.** With eviction at work: the longest GC pause, full collections, allocation
  stalls, and the longest waits of gets and commits.
* **Z2 Memory.** The heap per key without eviction; the heap that a budget needs.
* **Z3 Speed.** Gets in memory and from the OS cache, the load's puts a second, the soak's
  commits and reads; the sweep's time.
* **Z4 CPU.** The process's CPU time (user and system) for the same work.

How it decides: if ZGC removes the full collections without allocation stalls, at a cost in
memory and speed that Frans accepts, the plan for handles assumes ZGC, and allocates a
handle right before its object (ZGC keeps the allocation order, 004-02 part B). Otherwise
the plan assumes G1 and must bound its full collections some other way.


## 2. The runs

F53 only (MacBookPro18,3, OpenJDK 27 from Homebrew). bergdb `7d14f65` built in a scratch
clone, `bergdb.jar` SHA-256 `e6d52dc6ac78aafb7fb150d65c49c360cab35e183766f4a6b0597171af4281db`.
Each configuration runs with G1 and with ZGC, back to back, with 004-02's flags otherwise
(`-Xms` equal to `-Xmx`, `AlwaysPreTouch` for ScaleBench, `gc*` and `safepoint` logged).
The tools are unchanged: 004-02's ScaleBench and `java/stress/Soak.java` (`soak.sh`, which
takes `GC=g1|zgc`). [javatime.sh](04-zgc/javatime.sh) runs each JVM under `/usr/bin/time
-l` for its CPU time and peak RSS. The script: [run.sh](04-zgc/run.sh).

| Run | What | Heap | With G1 before |
|---|---|---|---|
| m-10m | 10M key24 keys loaded with no eviction (M), then the get phases in the same JVM | 6 GB | 004-02: 98 s, 243 bytes of heap per key |
| c-10m-b133 | the same database, budget 133 MB, the stream in the OS cache (C) | 600 MB; ZGC also 1,200 MB | 004-02: 49 full collections, longest sweep 0.6 s |
| c-10m-b665 | the same, budget 665 MB | 2,660 MB | 004-02: 12 full collections, longest sweep 6.0 s |
| p4z | P4's soak, shortened: 1M keys and 1,000 long ones, 1,000-byte values, retention 5 minutes, a writer at 200 transactions a second, 3 readers at 5,000 operations a second, a budget of 1.6 GB; 30 measured minutes and one restart instead of two hours and three | 8 GB | P4: 81 full collections in two hours |

Order: the ScaleBench block (about 35 minutes), then the soak with G1 and with ZGC (about an
hour each, with P4's warm-up of about 20 minutes). Each block waits for a quiet machine as
in 004-02 (`quiet.sh`: a load below 2.0, no other JVM or gate, no Claude session busy from
05:00 to 22:00, nothing from 02:00 to 05:00).

Not in this run: s1 (two virtual CPUs, where ZGC's threads compete with BergDB's), the 100M
sizes, other collectors, G1 tuned (a larger heap per budget, an earlier marking start).


## 3. Results

To come.
