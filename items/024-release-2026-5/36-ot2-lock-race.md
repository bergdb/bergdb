# 024-36. OT2: the Linux "directory in use" race, fixed

Created 2026-11-12 by Frans Lundberg. Status: done (2026-11-12): on
`main` since `c49351e1`.

Frans, 2026-11-12, 14:33: "OT2; fix it." OT2 (024-01, section 11.2;
024-35, finding 1; 006-17, section 6.2; 2026.4's Known issues: "The fix
is for 2026.5"): `FileStream.unlockDir()` closed `bergdb.lock` before it
removed the directory from `LOCKED_DIRS`, so a start in the same JVM
right after a close could find a new directory still listed and refuse
it as in use. Only the test half went in on 11-10 (`d99ff27c`).

Done by the agent "ot2" of the day's coordinator, in its own clone, on
branch `ot2-unlock-race`.


## 1. In short

* The fix is 006-17's `product-fix-idea.patch`, unchanged in substance:
  `unlockDir()` closes the lock file and removes the directory's keys,
  from the system properties and `LOCKED_DIRS`, in one hold of
  `LOCKED_DIRS`'s monitor, the monitor under which `lockDir()` checks.
  The patch applied to today's `FileStream` as it was (no commit to the
  file since 11-09); the comment is new.
* A new unit test fails before the fix on macOS, deterministically,
  without a reused inode, and passes after.
* Gates on the branch's head `6103608d`: BEFORE COMMIT OK, LEVEL 1 OK.
* s1, JDK 17, 006-17's probe on today's code without the test fix: 19
  refusals in 60,000 tests before the fix, 0 after (section 5).


## 2. The change and the order it guarantees

Before, in `unlockDir()` (under the stream's own monitor only):

1. `lockFile.close()`: the process's lock on `bergdb.lock` is released;
   if the directory was deleted while the stream closed (as after
   `stop()`, which closes in the background), this closes its last open
   file, and Linux ext4 gives the directory's inode at once to the next
   new directory (020-23, section 5, V5-1: 50 of 50 on s1).
2. The two system properties are removed (015-24).
3. The two keys, file key and path key, leave `LOCKED_DIRS`.

A start between 1 and 3 in a new, empty directory that got the inode
read that file key, found it in `LOCKED_DIRS` under the monitor, and was
refused: `DirectoryInUseException` "in use by another BergDB database in
this JVM". The window is short, but s1 saw it 10 times in 30,000 probe
runs (006-17, section 6.2).

Now steps 1 to 3 run in one `synchronized (LOCKED_DIRS)` block, in the
same order. `lockDir()` checks and adds the keys under the same monitor
(`LOCKED_DIRS` is a `Collections.synchronizedSet`, whose methods lock the
set itself). What that guarantees, and why it is safe:

* **A start of this copy of the class sees the directory either still
  held (before step 1) or gone (after step 3), never the file closed and
  the keys listed.** A start reads its key (a `stat`) before it takes the
  monitor. A new directory can have the freed inode only if it was made
  after step 1 (V5-1: the inode is not reused while the lock file is
  open), so its key was read after step 1, and its check, which needs
  the monitor, waits for the end of step 3.
* **The lock file is still closed first.** A start must not open a second
  channel of `bergdb.lock` in this JVM while the first is open: closing
  that channel on a refusal would release the process's lock for other
  processes (`LOCKED_DIRS`'s comment, 005-63). The keys are therefore
  removed only after the close, as before.
* **The properties go in the same hold.** A start of this copy that had
  passed `LOCKED_DIRS` would put its property with the same value (the
  copy's `COPY`); a later `remove(name, COPY)` by the closing stream would
  then remove the new stream's property, and another class loader would
  no longer be refused. In one hold, no start of this copy passes
  `LOCKED_DIRS` before the removals are done.
* **No deadlock.** Lock order in `unlockDir()`: the stream's monitor,
  then `LOCKED_DIRS`, then (inside `Properties.remove`) the properties'
  monitor. `lockDir()` takes `LOCKED_DIRS`, the properties and the
  stream's monitor one at a time, never nested; no other code holds
  `LOCKED_DIRS` and then takes a stream's monitor.
* **Cost.** Other starts and closes in the JVM wait for one file close
  under the monitor, microseconds; none waits for I/O of the stream's
  data, which `close()` finishes before `unlockDir()`.
* **Left.** A start in another copy of the class (another class loader
  in the same JVM, 015-24) checks the system properties without this
  monitor and can still, rarely, be refused in that moment; a retry
  works. Closing it would need a monitor shared across class loaders,
  such as the system properties object itself, which relies on
  `Properties`' implementation; not done. Said in `unlockDir()`'s comment
  and in `releases/next.md`.

Files: `java/src/bergdb/stream/FileStream.java` (`unlockDir()` and its
comment; the test), `releases/next.md` (Known issues: OT2 fixed, and what
is left).


## 3. The test

`FileStream.testNoStartSeesAClosedLockStillListed` (unit group). It
needs no reused inode, so it fails before the fix on every system:

1. A `FileStream` on a temporary directory.
2. The test thread holds the monitor of `System.getProperties()`; a
   "closer" thread calls `close()`, which stops in `unlockDir()` at the
   removal of its property, right after the lock file's close (the test
   waits until the closer is `BLOCKED`, at most 10 s).
3. The test checks that the lock file is closed: a new channel of
   `bergdb.lock` gets the lock.
4. A "checker" thread does what `lockDir()` does: `LOCKED_DIRS.contains`
   of the directory's key under `LOCKED_DIRS`'s monitor. The test waits
   until it is `BLOCKED` or done, then lets go of the properties.
5. Expected: the checker found the key not listed. Before the fix it ran
   at once and found it listed (the assertion "a start found the
   directory listed after its lock file was closed" failed, macOS, JDK
   27, 14:37); after, it waits for the closer's block and finds it gone.
   A new `FileStream` on the directory then opens.

A stress loop of close and start in one JVM cannot fail on macOS: APFS
does not reuse a deleted directory's inode number (the probe of section
5 on F53: 2,000 rounds, the inode reused 0 times). That probe,
`/Users/f/fl/bench/2026-11-12/ot2/probe/CloseStartRace.java` (outside the
repo), did not hit the window on s1 either (section 5), so the evidence
on Linux is 006-17's probe.


## 4. Gates

On the branch's head `6103608d` (F53, each in a slot):

| Gate                   | Result                                                 |
|---|---|
| `java/before-commit.sh` | BEFORE COMMIT OK (64 s; unit 1,698, f 89, demos 14)   |
| `java/stress/level1.sh` | LEVEL 1 OK (2.4 min; MEM 130, MEM10M 127.1, SS 1.53)  |


## 5. s1

s1 (ext4, 2 cores, JDK 17.0.21, idle before), 14:39 to 14:52, in
`/opt/bergdb-bench/2026-11-12-ot2/` (outputs `lwp-*-17-*.txt`,
`before-17-*.txt`). Two JVMs at a time.

| Probe and jar                              | Tests  | Refused |
|---|---|---|
| `LockWindowProbe`, today without the fix      | 60,000 | 19      |
| `LockWindowProbe`, today with the fix         | 60,000 | 0       |
| `CloseStartRace`, 2026.4's candidate (no fix) | 30,000 | 0       |

* `LockWindowProbe` is 006-17's probe
  (`/Users/f/fl/bench/2026-11-10/jdk17-f/probe/`): it loops
  `FileStreamPowerLossTester`'s three failure tests, 10,000 rounds of 3
  tests a JVM. The tests themselves no longer race since `d99ff27c`, so
  the jars are the branch's head with that test fix reverted
  (`git apply -R test-fix.patch`), "without the fix" also with
  `unlockDir()`'s `synchronized (LOCKED_DIRS)` taken out; built on F53,
  `/Users/f/fl/bench/2026-11-12/ot2/probe/{before,after}-notestfix.jar`.
  Every refusal before: the key in `LOCKED_DIRS` at the refusal and gone
  soon after (a close under way, not a leak), as on 11-10. About 65 s a
  run.
* `CloseStartRace` (a stream's directory deleted, the stream closed on
  another thread, new directories made until one has the old inode, a
  start there): the inode was reused in 29,654 of 30,000 rounds, but the
  start never came inside the window; its path from `mkdir` to the check
  is long against the closer's few removals. Not a useful check; kept
  only as a record.

To repeat in a release night (about 2.5 minutes on s1), with the two jars
in `/opt/bergdb-bench/2026-11-12-ot2/` and `lwp-before`, `lwp-after` the
probe compiled against each (`javac -cp $v-notestfix.jar -d lwp-$v
lwp-src/core/LockWindowProbe.java`):

    cd /opt/bergdb-bench/2026-11-12-ot2 && J=/opt/bergdb-bench/jdk-17/bin/java
    for v in before after; do for i in 1 2; do
      $J -ea -Djava.io.tmpdir=$PWD/t$i -cp lwp-$v:$v-notestfix.jar \
        bergdb.core.LockWindowProbe 10000 pending > lwp-$v-17-$i.txt 2>&1 &
    done; wait; done
    grep -c "PROBE REFUSED" lwp-*-17-*.txt

`-Djava.io.tmpdir` matters: s1's `/tmp` is tmpfs, the race was seen on
ext4.


## 6. Questions for Frans

None. One decision made by rule: the other class loader's window
(section 2, "Left") is not closed; it would need a monitor shared across
class loaders, and a start there is as rare as two copies of BergDB in one
JVM and a reused inode at once; a retry works.


## 7. State

Done, 2026-11-12, 14:55.

* Clone `/Users/f/fl/bench/2026-11-12/ot2/clone`, branch
  `ot2-unlock-race`, head `6103608d`, one commit on `main` `2cf42560`:
  `FileStream.java` (the fix, its comment, the test) and
  `releases/next.md` (Known issues: OT2 fixed, what is left).
* Gated on that head: BEFORE COMMIT OK, LEVEL 1 OK. s1 probe: 19 to 0.
* Not done: landing on `main` (the coordinator's). After landing, 024-01
  section 11.2 and 024-35 finding 1 can point here.

2026-11-13. Status set after the release (coord-1113).
