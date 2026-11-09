# 022-06 U2-2, U2-3, U2-6, U2-8, U1-1 and U1-2 in Java's Core

Created 2026-11-09 by Frans Lundberg. Status: done. C has two fixes in
`dag_dirty_node_bound`; the rest is Java's.

Worker f2 of the session `022-bergdb-c`. Users u2 and u1 of the C library
found faults that might be Java's too:

* u2: 022-06-2 ([u2-error-paths.md](u2-error-paths.md)), with its
  reproductions `repro_*.c` in `/Users/f/fl/bench/022/apps/u2/`.
* u1: 022-06-1 ([u1-device-store.md](u1-device-store.md)), with its
  reproductions in `/Users/f/fl/bench/022/apps/u1/repro/`.

For each finding this record asks whether Java's Core does the same. Each
check is a small program against Java's Core API (`bergdb.core.Db`,
`DbBuilder`), run beside C. U2-1 (the clock past `MAX_TIME` at a
`current_time`) and U2-4 (`get_trans` inside a record) went to
coord-1109's agent h31. h31 checks them in Java and fixes them there if
the fix is small; C then follows the candidate's diff.

**In short.** Java's Core does U2-8, U2-6, U2-2 and U1-2 the same way, and
it also does the part of U2-3 and U1-1 that remains after C's fixes. One
part of U2-3 and U1-1 was C's own: the put of a long key that shares a
long prefix with a stored key. C's port of `Dag.dirtyNodeBound` was
quadratic there, and Java's is not. The check found a second quadratic in
the same function: a transaction with many new keys at one node. Both are
fixed in C (section 7).

| ID   | What the user found                                 | Java                | C changed  |
|------|-----------------------------------------------------|---------------------|------------|
| U2-8 | a put under reclaim's settings key: no open again   | the same            | no         |
| U2-3 | the long key's own put slow                         | no: 0.24 s, C 4.3 s | yes, fixed |
| U2-3 | then a 4 MB put slow                                | the same, slower    | no         |
| U2-2 | the zero fill needs the failed record's size free   | the same            | no         |
| U2-6 | a stream file deleted while open: no error, no open | the same            | no         |
| U1-1 | a key sharing a long prefix: seconds to minutes     | no: C's own         | yes, fixed |
| U1-1 | a key that extends a stored key; 4 MiB after 2 MiB  | the same            | no         |
| U1-2 | long keys take 10 times their size                  | the same stream     | no         |
| (f2) | many new keys at one node in one transaction        | no: 0.7 s, C 8.3 s  | yes, fixed |


# 1. How Java was run

Java's Core is `main` at `b3a6b05` (2026-11-09, after `a2fa9df`). C's
harness compiles it, the Core Layer alone:

    git fetch /Users/f/fl/repos/bergdb main:refs/remotes/repo/main
    JAVA_REF=git:b3a6b05ab9d0b9baabe1b7588694938f8bba1b59 c/test/cross/java-build.sh

The classes land in `c/build/java/classes`, CLASSES below. OpenJDK
27.0.1, `-ea`.

The programs are in [u2-in-java/](u2-in-java/), in the default package.
Each opens a `bergdb.stream.FileStream` on a new directory, or a
`MemoryStream` where the C program uses memory. Each keeps the builder's
defaults: startup distance 50 MB, cache size indicator 200 MB, the system
clock. These are the defaults of `bergdb_options_init` in C. To run one:

    javac -cp CLASSES -d WORK u2-in-java/U2_8.java
    cd WORK && java -ea -cp CLASSES:. U2_8 DIR        (DIR new)

C beside it: int.git's `2026.4` at `96cf492`, with
`c/build/release/libbergdb.a`. The users' reproductions are built against
it with `cc -std=c17 -O2`. Each pair ran once on F53, a shared machine.
Times are from single runs, not benchmarks.

The counts in sections 3 and 6 come from probes outside the repository.
Java's probe is a copy of `DbHelper.java` on the class path before
CLASSES. C's is a copy of `src/` built with the program. Each adds a
counter of passes, visited nodes and marked nodes to the still-dirty loop
of `store`: Java's `DbHelper.handleStillDirtyNodes` and C's
`handle_still_dirty_nodes` in `db.c`. Each prints the counts when a loop
of more than 2 passes ends.


# 2. U2-8: a put under reclaim's settings key

u2: a put of `garbage` under `/#i/dreclaim/-settings.txt` is taken. Every
later open gives `BERGDB_FORMAT`, and nothing in the API repairs it.

**Java** (`U2_8.java`) calls `setRetainDuration(1 h)`, then
`db.execute(db.trans().put("/#i/dreclaim/-settings.txt", "garbage"))`.
The key is the bkey (`Keys.toBytes`), as u2's `bergdb_ikey_to_bkey` gives
it. Then a close and a start:

    put under /#i/dreclaim/-settings.txt: taken
    start: bergdb.core.InternalDataException: Bad value of /#i/dreclaim/-settings.txt,
      reclaim's settings: not the two lines retain=<time units> and fraction=<units of
      2^-16>, in range, that this version writes (bergdb 015-87): 'garbage'.

**C** (`repro_reserved_key.c`): the put gives `BERGDB_OK`, and the open
gives `BERGDB_FORMAT` with the same text, byte for byte.

**Verdict: Java does the same, as its documentation says.** Db's Javadoc,
in "Keys and the layers above", says of every key that starts with `/#`:
"Do not write them. Data there that does not parse is refused with
InternalDataException, at a start or at the read that meets it."
`bergdb.h`, section E, tells C's users the same. A refusal of puts and
deletes under `/#` would change Java's API. That is for after the
release, and C would follow it.


# 3. U2-3: long keys sharing a prefix, then a slow put

u2's finding has three parts:

* Keys of 128 KB, 512 KB and 2 MB share all but their last byte. The
  2 MB key's put takes 4.2 s (0.07 s alone).
* After them, a 4 MB value under another, 2-byte key takes 16 s. The
  profile is in `store` and `kn_get_pointer`.
* A key costs about 51 bytes of memory per key byte.

**Java** (`U2_3.java`) repeats u2's `repro_long_key.c` with N = 1,048,576:

* Keys of 64 KB, 256 KB and 1 MB, each put with a value of 1 byte in its
  own transaction.
* Ten small transactions.
* Puts of 1, 4 and 16 MB under a 2-byte key.
* The heap is measured after `System.gc()`.

| Call                   | Java, run 1 | Java, run 2  | C before | C fixed  |
|------------------------|-------------|--------------|----------|----------|
| the 64 KB key          | 0.031 s     | 0.021 s      | 0.002 s  | 0.002 s  |
| the 256 KB key         | 0.153 s     | 0.056 s      | 0.005 s  | 0.006 s  |
| the 1 MB key           | 0.286 s     | 0.192 s      | 0.962 s  | 0.028 s  |
| ten small transactions | 0.003 s     | 0.004 s      | 0.0001 s | 0.0001 s |
| a 1 MB value           | 0.007 s     | 0.007 s      | 0.004 s  | 0.004 s  |
| a 4 MB value           | 47.6 s      | 28.8 s       | 7.0 s    | 6.6 s    |
| a 16 MB value          | 0.83 s      | (not waited) | 0.50 s   | 0.50 s   |

`jstack` sampled run 2. The "keys" variant puts the three keys only, with
N = 2,097,152 (u2's sizes):

| Call                              | Java    | C before | C fixed |
|-----------------------------------|---------|----------|---------|
| the 2 MB key after the 512 KB key | 0.238 s | 4.296 s  | 0.050 s |

The C runs use a copy of `repro_long_key.c` that stops after the keys,
built with `-g`.

**The long key's own put is C's own fault.** macOS's `sample` of C during
the 2 MB key's put shows all of its 2,267 samples in
`dag_dirty_node_bound`. Section 7 has the cause and the fix.

**The 4 MB put after the keys is Java's.** Five `jstack` samples of Java's
main thread during the 4 MB put, over 25 s:

* Four are in `Db.store` -> `Db.handleStillDirtyNodes` ->
  `DbHelper.handleStillDirtyNodes`.
* The fifth is in `BufferedStream.append`, the record's append.

That loop makes one pass over all the record's index nodes. The pass marks
dirty each clean node that has a dirty child, and the loop repeats until a
pass marks none. The 4 MB value's record is the one whose take
(`TransSeq.take`, level 2's startup pace) takes the long key's chain of
key nodes into it. Each pass then marks one node of the chain. The probes
(section 1) count the same in C and Java for that put: 37,451 passes,
1,402,577,401 nodes visited, 37,451 marked. C's `handle_still_dirty_nodes`
is the same loop, and it is u2's profile.

**Memory.** Java's heap after a GC grew by 41.5 MB for the three keys.
That is 1,376,256 key bytes, about 30 bytes per key byte. For the 2 MB
keys: 82.2 MB for 2,752,512 bytes. C's peak (`struct bergdb_mem`'s
`peak_total`) grew by 35.7 MB with the 1 MB key, about 34 bytes per byte.

**Verdict.**

* The long key's own put is C's fault. It is fixed (section 7).
* The slow put after the long keys is Java's, and Java is slower at it.
  It is a Java fault for after the release: the still-dirty marking could
  walk once from the leaves up. C follows Java's fix.
* Neither `bergdb.h` nor Db's Javadoc says what long keys cost.


# 4. U2-2: the zero fill after a full disk

u2: a 12 MB transaction fails on a nearly full disk. The next open writes
zeros over the torn record's whole declared length. So the database does
not open until that much space is free, and the zeros stay in the stream.

**Java** (`U2_2.java` and `U2_2.sh`) repeats u2's
`repro_full_zerofill.sh` on a 40 MB HFS+ image: 20 MB reserved, then the
rest filled but 2 MB. The two last columns are the bytes of the stream
files after each step.

| Step                      | Java                  | C             | Java bytes | C bytes    |
|---------------------------|-----------------------|---------------|------------|------------|
| the 12 MB transaction     | DbFailedException     | BERGDB_FAILED | 2,000,000  | 2,000,000  |
| 6 MB more freed: the open | OK, length 12,591,624 | BERGDB_IO     | 8,000,000  | 8,000,000  |
| all freed: the open       | OK                    | BERGDB_OK     | 12,591,624 | 12,591,624 |

The texts:

* The 12 MB transaction fails the same way in both: "failed after it
  began".
* C's open with 6 MB free: "IOException: Write of 1000000 bytes at 0
  failed: No space left on device".
* Java's start with 6 MB free puts the zeros in its storage's buffer and
  returns. The storage's thread then fails to write them, and the first
  `execute` is refused: "DbFailedException: Cannot call execute(): the
  database failed (the cause) and must be restarted." In a first run,
  which had no transaction there, the close threw "StreamIoException: No
  space left on device".

**Verdict: Java does the same.** The zero fill is Java's
(`RecoverableStream.fixLastTransactionIfNeeded`, 014-01). It appends zeros
up to the torn record's declared size, 12,591,360 bytes from position 264,
so the stream ends at 12,591,624. The one difference is when the failure
shows: C fails in the open, and Java just after its start. That is C's
design: C has no thread, so the call that asks for a write makes it
(`c/readme.md`, the opening of section 11).


# 5. U2-6: a stream file deleted while the database is open

u2: the only stream file is deleted under an open database. Later
transactions, the sync and the close succeed, and the next open refuses
the directory.

**Java** (`U2_6.java`) repeats u2's `repro_deleted_file.c`: a put of
100 kB, a sync, `00000000000000.bergdb` deleted, three puts of 100 kB, a
sync, a close and a start:

    put 0: OK
    delete 00000000000000.bergdb: true
    put 1: OK
    put 2: OK
    put 3: OK
    sync: OK
    close: OK
    files: 00000000000002.bergdb 00000000000004.bergdb bergdb.lock
    start: bergdb.storage.StreamIoException: Cannot read at spos 128, below the first
      position, 200000.

**C**: the puts, the sync and the close give `BERGDB_OK`. The same two
stream files are left, and the open gives `BERGDB_NOT_AVAILABLE` with the
same text.

**Verdict: Java does the same.** Neither checks that the file it writes
is still linked. u2 proposes `fstat`'s `st_nlink` at a sync. That would
first be a change of Java's `FileStream`.


# 6. U1-1 and U1-2: u1's long keys

**U1-1.** u1's `long_key_time.c` runs in memory. Random keys of 256 KiB
to 2 MiB each share the key before as a prefix. Then come the 1 MiB key +
1 byte, a 1 MiB key of zeros, and that key + 1 byte. The Java version,
`U1_1.java`, does the same in a `MemoryStream`, with random bytes from
`java.util.Random`, not C's `rand()`:

| Put                         | u1 (C before) | C fixed | Java    |
|-----------------------------|---------------|---------|---------|
| 256 KiB                     | 0.006 s       | 0.007 s | 0.040 s |
| 512 KiB, sharing 256 KiB    | 0.010 s       | 0.009 s | 0.041 s |
| 1 MiB, sharing 512 KiB      | 5.6 s         | 0.022 s | 0.161 s |
| 2 MiB, sharing 1 MiB        | 18.4 s        | 0.050 s | 0.200 s |
| the 1 MiB key + 1 byte      | 24.6 s        | 5.7 s   | 18.6 s  |
| zeros, 1 MiB, then + 1 byte | 19.7 s (app)  | 5.8 s   | 18.4 s  |

After C's fix, what is left is the key that extends a stored key. In both
C and Java that time goes to the still-dirty loop, as in section 3. macOS
`sample` puts C's time in `store`'s loop with `node_get_pointer`. The
probes count the same in C and Java:

* the 1 MiB key + 1 byte: 37,452 passes and 1,402,614,852 visits;
* zeros + 1 byte: 37,450 passes and 1,402,465,050 visits.

u1's `long_key_4mib.c` (a random key of 2 MiB, then one of 4 MiB that
shares it), with the fix:

* C: the 2 MiB key takes 0.1 s. The 4 MiB key had not returned after
  4 minutes; `sample` shows `store`'s still-dirty loop, and it was
  stopped.
* Java (`U1_1 4mib`): the 2 MiB key takes 0.21 s. The 4 MiB key had not
  returned after 3 min 49 s (3:42 of CPU); `jstack` shows
  `DbHelper.handleStillDirtyNodes`, and it was stopped.

**Verdict on U1-1.** The shared prefix's cost was C's own and is fixed
(section 7). A key that extends a stored key is slow in Java too, and so
is the 4 MiB case: that is Java's still-dirty loop, as in U2-3.

**U1-2.** u1's `long_key_memory.c` puts 16 random keys of 1 MiB, each with
the value `0123456789` in its own transaction. Its cache size indicator
is 10 MB, in a directory. Java (`U1_2.java`) puts the same 16 keys:
`keys16.c` writes them to a file from C's `srand(3)` and `rand()`. Java's
stream is 172,678,296 bytes after the 16 keys and after a restart. C's is
172,678,296 too: 160,000,000 bytes in full files and 12,678,296 in the
last. Both directories take 168,724 KB.

The bytes are not compared, because the system clock and the database id
differ. Java's heap after a GC is 655.2 MB after the keys and 565.3 MB
after a restart. C's live total is 288.5 MB and 263.8 MB.

**Verdict on U1-2: Java's design.** The stream is the same length, and
Java holds more in memory than C. A key's cost belongs in Java's
documentation and in `bergdb.h`.


# 7. What changed in C

Two changes to `src/dag.c`'s `dag_dirty_node_bound`, the port of
`Dag.dirtyNodeBound`. That function is Db's bound, before the go point,
on the index nodes that a transaction can make dirty or create (005-31).
It runs only when a cheap estimate exceeds the record limit, as in Java.
Both changes give the same bound as before, so the sum is still Java's.
Only the time changes.

**1. Deepest first in one pass.** Java sorts the walked nodes by depth,
deepest first. Then each node comes after the nodes below it, whose
overflows add to its klongs. C went over every walked node once per depth,
from the largest depth. That is quadratic in a long key's chain of walked
nodes: about 75,000 squared for a key that shares 512 KB.

Now C goes once from the last walked node to the first. A node is walked
after its up, so this order also puts each node after the nodes below it.
An assert checks it, and the unused `depth` field is gone.

**2. New keys counted when sorted.** Java's `Walked.fresh` counts one
klong for each distinct missing segment, found in a HashMap. C's
`dnb_fresh` scanned the node's list of new keys for each new key. That is
quadratic in the new keys of one node.

Now C counts the distinct segments where it already sorts that list by
the segment, before the node's klongs are read. `many_fresh.c` puts
100,000 new keys of 16 bytes in one transaction, in memory:

| Keys    | C before | C fixed | Java (`ManyFresh.java`) |
|---------|----------|---------|-------------------------|
| 100,000 | 8.3 s    | 0.22 s  | 0.71 s                  |
| 200,000 | -        | 0.48 s  | 1.34 s                  |

**Tests.** Two unit tests are new in `test/unit/t_getmany.c`, next to
`dag_dirty_node_bound`. Each times the bound with an `mdb` and requires
less than 2 s, as `sdb_find_node` does.

* `dag_dirty_node_bound_long_key`: a key of 2^20 bytes, after one of 2^19
  bytes with the same prefix.
* `dag_dirty_node_bound_many_new_keys`: 100,000 new keys of 16 bytes in
  an empty database.

| Test, the bound's time               | Before, release | Before, test build |
|--------------------------------------|-----------------|--------------------|
| `dag_dirty_node_bound_long_key`      | 3,948 ms        | 11,585 ms          |
| `dag_dirty_node_bound_many_new_keys` | 10,094 ms       | 36,865 ms          |

After both changes, the three `dag_dirty_node_bound` tests take 0.20 s
in all in the release build and 0.35 s in the test build.

Each test fails before its change, in both builds. The second test ran
before change 2 with change 1 already in. The bounds are the same before
and after each change: 149,797 and 216,666. Java's `dirtyNodeBound`
vectors (`t_dagvec.c`) and the random test `dag_dirty_node_bound` pass
unchanged. With the fix, u1's and u2's programs give the times of the
tables above.

The gate's result is in the landing commit's message.

**Not changed:** the still-dirty loop (sections 3 and 6). It is Java's,
and C follows Java's fix of it.
