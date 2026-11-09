# 006-18-03 Android check

Created 2026-11-09 by Frans Lundberg. Status: done.

This is part of 006-18, BergDB in languages other than Java. It asks
whether BergDB's Java code runs on Android, and what it takes. Frans said
on 2026-11-09 at 12:43: "Is Android in scope? ... Yes, is it in scope.
Check this."

This is the first of 006-18's first steps (section 6, step 1):

* A static check of the jar against each Android API level (section 2).
* The jar itself on an emulator of Android 13 and of Android 14 (sections
  3 and 4).
* Two fixes, made on a branch of a clone (section 5).
* What a real app and a supported release would need (sections 6 and 7).


## 1. In short

**Yes.** BergDB's Java code runs on Android with two small fixes:

* The Core and the Pub API's other values run from Android 13 (API level
  33).
* Objects run from Android 14 (API 34).
* On unchanged `main`, it fails at the first wait for room in the write
  buffer.

| API   | Build      | Runs                                | Fails |
|---|---|---|---|
| 26–32 | any        | nothing (static check; not run)     | the Core: `VarHandle`             |
| 33    | `main`     | to the first wait for buffer room   | that wait: `java.lang.management` |
| 33    | fix 1      | Core; Pub API: Strings, byte arrays | objects: `ClassValue`             |
| 34    | fix 1      | as on 33                            | objects, refused: V5, V6          |
| 34    | fixes 1, 2 | Core, Pub API, objects, demos, R8   | 15 of 1,505 tests, 13 tests' own  |

**The commits.** For 2026.4, by Frans's word at 16:03 ("Is this an easy
fix we can get into 2026.4, let's fix it."), they are on the branch
`006-18-03-android` of the clone `/Users/f/fl/bench/2026-11-09/android/bergdb`,
on `main` at `9ed1e6c`. Neither fix changes the JVM's behaviour (section
5). On the tree of the three: BEFORE COMMIT OK (145 s), and LEVEL 1 OK,
both under the lock.

* `53f4f5c`, fix 1: `BufferedStream`'s wait statistics without
  `java.lang.management`; +42, -2 lines. It was first `14e4b8e` on
  `aa55efc`.
* `a25a7e8`, fix 2: `DataObjects`' V5 and V6 without modules; +36, -4
  lines. It was first `99a3c83`.
* `3926a12`: `releases/next.md`, a Platforms section with G88 as a known
  difference, and a line in README.md.

**The floors.**

* The Core needs API 33, because handles (009) use `VarHandle`.
* Objects (Data Objects and `DbObject`, which goes through `DataObjects`)
  need API 34, because `DataObjects` uses `ClassValue`.

**The effort.** A supported Android release takes about 3 to 5 days
(section 7):

* a night step on the emulator, so that Android does not break again
  unseen;
* an AAR with R8 rules;
* a sample app for the app's life cycle.

**A real difference.** Android's UTF-8 decoder replaces a malformed
sequence with more U+FFFD than the JDK's: three for the bytes `ed a0 80`,
where the JDK gives one (020-09's case G88). So the same stored bytes give
a different String (section 4.2).

**History.** The 2013 to 2017 code ran on Android. Frans's log in F1-007's
`bergdb/log.md` has "All non-file-system unit tests now run on Android"
(2013-02-21) and "Works with Android (but Java 8 is problematic)"
(2017-07-29). `Util.runsAndroid()` and its guards in tests are from then.
Each of today's blockers came in the last two weeks:

* `VarHandle`, from 009 (`4e66a59`, 2026-10-25);
* `java.lang.management` in the write path, from 005-46 (`eaec93e`,
  2026-10-27);
* `DataObjects`' `ClassValue`, modules and platform loader, from 020-08
  (`ca67411`, 2026-11-08).


## 2. The static check

The checks ran on the release jar (`build/bergdb-release.jar`) of a clone
at `main` (`aa55efc`). The jar has 976 classes, `src`'s tests among them.

**jdeps** (`jdeps -summary`) names three modules: `java.base`,
`java.management` and `jdk.management`. Of the last two:

* `java.lang.management.ManagementFactory` is used by:
  * `BufferedStream.Waits.add`, for the JVM's uptime, at every wait for
    room in the write buffer that is among the five longest, so at the
    first wait (005-46);
  * `core.Jmx`, which has no callers but tests and `src-dev`'s
    `Interactive`;
  * the tests in `Eviction`, `DbTesterFailure`, `PubTester` and
    `FormatFuzzer`.
* `javax.management.*` is used by `Jmx` only.
* `com.sun.management.*` is used by the tests `PubTester` and
  `FormatFuzzer`.

**ApiCheck** checks the jar against each API level. jdeps names classes,
not methods, and knows nothing of Android, so `ApiCheck.java` (section 8)
does this:

1. With the JDK's class-file API, it reads each of the jar's references
   to a platform class (`java.*`, `javax.*`, `sun.*`, `jdk.*`,
   `com.sun.*`): to a class, a method or a field.
2. It looks each one up in the API level's `android.jar`, through the
   owner's supertypes. The methods that d8 backports at that level count
   as present (d8's `BackportedMethodList`).
3. A use counts as a test's when its method has `@Nano`, its name starts
   with `test`, or its class is a `...Tester`, a `...Harness` or a
   `...Fuzzer`.

The uses outside tests, on the jar with fix 1:

| Missing on Android                     | Levels   | Used by |
|---|---|---|
| `VarHandle` and its factories          | below 33 | `Handle`, `KeyNode`, `TopNode`            |
| `Arrays.compareUnsigned(byte[], ...)`  | below 33 | `DbObject`, `ObjectFormat`, `DataObjects` |
| `BigInteger.longValueExact()`          | below 31 | `Eviction`, `TransSeq`                    |
| `Class.getPackageName()`               | below 31 | `DataObjects`                             |
| `ClassValue`, `Record`                 | below 34 | `DataObjects`                             |
| `Class.getModule()`, `Module`          | all      | `DataObjects`, V6                         |
| `ClassLoader.getPlatformClassLoader()` | all      | `DataObjects`, V5                         |
| `java.lang.management.*`               | all      | `BufferedStream`: fix 1 guards it         |
| `javax.management.*`                   | all      | `Jmx`                                     |

The levels checked were 26, 28, 30, 31, 32, 33, 34, 35, 36 and 37.0.
Levels 34 to 37.0 give the same list.

* d8 desugars the invokedynamic bootstraps at any level:
  `LambdaMetafactory` in 48 classes, `StringConcatFactory` in 272, and
  `ObjectMethods` in one record, a test's.
* d8 9.2.4 dexed the jar for API 33 with no warning.
* `Jmx` is never loaded. Nothing in `Db` or in the Pub layer refers to
  it, and ART loads a class only at its first use. None of the emulator
  runs touched it.


## 3. The set-up

Nothing needed sudo, a GUI step or an account of Frans's.

* **The tools.** Google's command-line tools for macOS on arm64,
  `commandlinetools-mac_arm64-16111833_latest.zip` (version 23.0), from
  `dl.google.com`. Its SHA-1 matched the one in Google's
  `repository2-3.xml` (`ad03dc49...`).
* **The "Android CLI".** In version 23, `sdkmanager` wraps a new tool,
  `android`. It ran with `--no-metrics`. It has no `--licenses`: after
  printing a link to the SDK's terms, it accepted the licence itself.
* **What was installed**, into `/Users/f/fl/bench/2026-11-09/android/sdk`:
  * platform-tools 37.0.1;
  * build-tools 37.0.0, with d8 and R8 9.2.4;
  * emulator 37.2.13;
  * the platforms of section 2;
  * the system images `android-33/default/arm64-v8a` and
    `android-34/default/arm64-v8a` (AOSP, without Google's APIs).

  With the AVDs, this takes 10 GB on disk.
* **`~/.android`.** `ANDROID_USER_HOME` kept the AVDs and the tool's files
  in the bench directory. adb and the emulator still wrote five small
  files to `~/.android`: an adb key, a user id, an update check and the
  modem's state.
* **The emulator.** Each AVD is a Pixel 6 with 4 cores and 4 GB. The
  emulator ran headless (`-no-window -no-audio -no-snapshot -gpu
  swiftshader_indirect`) and booted in 30 s on a busy F53. One emulator
  ran at a time, and none runs now.

**The jar on the device, without an app:**

1. d8 dexes `build/bergdb.jar` (`src` and `src-dev`):
   * `--min-api` 33 or 34, with that level's `android.jar` as `--lib`;
   * `--force-enable-assertions`, as the JVM's tests run with `-ea` and
     d8 removes `assert` by default;
   * the jar's four resource files are added.

   This gives one `classes.dex` of 2.1 MB, in a jar of 1.0 MB.
2. adb pushes it to `/data/local/tmp/b/`.
3. `app_process` runs a class's `main` as the shell user:
   `CLASSPATH=$JAR app_process -Xmx1g -XX:HeapGrowthLimit=1g
   -Djava.io.tmpdir=/data/local/tmp/b/tmp /system/bin CLASS ARGS`.
   * `app_process`'s default heap is 192 MB.
   * `app_process` calls `main` only in a public class, so `Run.java`
     calls the `main` of a class that is not public, such as
     `bergdb.demo.Demo`.


## 4. On the emulator

### 4.1 Android 13, API level 33

**`main`, unchanged:**

* `bergdb.demo.Demo` ran: the Pub API with a String, with put, get, delete
  and get, each in a new process. It printed "Hello world!" and then
  "null", as `before-commit.sh` wants.
* 006-08's `CoreDemo` ran and printed "the same reads after a restart".
  It had to take `SyncLevel` from `bergdb.pub.util`; 006-08's copy no
  longer compiles.
* `KillDemo` died at its first transaction that waited for room in the
  write buffer. Its 20 kB values and 8 kB buffer made that wait come at
  once.
  * The error: `NoClassDefFoundError: Failed resolution of:
    Ljava/lang/management/ManagementFactory;`.
  * The trace: `BufferedStream$Waits.add`, `BufferedStream.append`,
    `StorageManager.append`, `RecoverableStream.append`,
    `NodeStream.appendNodes`, `Db.store`, `Db.execute`.
  * The error left `Db.execute` after its go point. Android's default
    handler of uncaught exceptions killed the process, as it kills an
    app.
* The Core's unit tests (`bergdb.dev.Unit -c
  "bergdb\.(common|core|dag|storage|stream|nanotest)\..*"`): 42 of 831
  failed, in 107 s. They were the tests whose writer waits for room, such
  as `BufferedStream.testWriteMuch`, `StorageContractTester` and
  `Reclaim`'s.

**With fix 1:**

* `KillDemo` wrote 400 transactions, closed, and its check passed. The
  waits line: "waits for room in the write buffer 432, 6465.9 ms in all;
  longest at uptime 6.333s (100.2 ms) ...". The uptime is now the time
  since `BufferedStream.Uptime` was initialized.
* `kill.sh` ran 20 rounds on one file database. Each round:
  1. `KillDemo write` writes 2 kB values and syncs every 50
     transactions;
  2. `kill -9` kills it after 0.5 to 3 s;
  3. `KillDemo check` starts the database and checks it.

  All 20 rounds passed: `/last` was at or after the last "SYNCED", and
  every key up to it was there with its bytes, none above it. 9 kills
  landed during the start. At the end the database held 37,050
  transactions, 77 MB in 50 files. The checks' starts took 0.3 to 2.6 s
  (median 1.1 s), on an emulator on a busy F53: not a phone's figure.
* The Core's unit tests: 4 of 831 failed, in 73 s.
  * Three tests call `java.lang.management` themselves:
    `DbTesterFailure.testWriterWaitingForTheLock`,
    `Eviction.testBatchFailureBeforeTheLockGoes` and
    `Eviction.testInterruptedWhileAWriterWaits`.
  * The fourth, `databasesStopped`, follows from the first of them.
  * The tests that start a child JVM already return early on Android
    (`Util.runsAndroid()`).
* All of `Unit`: 180 tests failed before the run died.
  * `DataObjects` failed at its first use, with `NoClassDefFoundError`
    for `java.lang.ClassValue`. Every put or get of an object goes
    through it, `DbObject`'s too (`DbObject.toDbObject`).
  * The failed tests left their databases open, each with a 10 MB write
    buffer, and at the 192 MB heap the run then died of
    `OutOfMemoryError`.

**So, on API 33 without objects:** the Core works: transactions, reads,
restarts, kills and 827 of its 831 unit tests. The Pub API works with
String and byte array values. Anything that reaches `DataObjects` fails.

### 4.2 Android 14, API level 34

**With fix 1 alone**, objects are refused. GetStarted1's `Person` fails
with "The class bergdb.demo.Person is not a Data Object: a class it uses
could not be loaded, java.lang.NoSuchMethodError: No static method
getPlatformClassLoader()". `checkClass`'s catch of `LinkageError` turns
the missing methods into a refusal.

**With fixes 1 and 2** (`tools/device.sh`, output in
`runs-device-fix2-34.txt`):

* **The demos** of `before-commit.sh` passed, as there, with the same
  lines: PayDemo's create, pay, iter and access on 10,000 accounts (Data
  Objects), WebsiteCode, Demo, and GetStarted1 to 5.
* **ReleaseDemo** (the Pub API, a `DbObject`, `rw()` and `Db`, with a
  restart) passed in two forms:
  * dexed by d8 with the whole release jar;
  * shrunk by R8 with the app's rules (section 6), once R8 kept the fields
    that `findVarHandle` finds by name. Without that rule it failed:
    `ExceptionInInitializerError` from `NoSuchFieldException: No field
    rootPointer`, as R8 had renamed `TopNode.rootPointer`.
* **The kill loop**: 20 of 20 rounds passed, 5 kills during the start. At
  the end the database held 62,700 transactions; the checks' starts took
  0.2 to 2.9 s.
* **All of `Unit`**: 15 of 1,505 failed, in 121 s (66 s on the JVM on
  F53, in the gate). 13 of the failures are the tests' own:
  * 9 call `java.lang.management`: the 3 Core tests of section 4.1, and
    6 in `FormatFuzzer`, whose class initialization takes a
    `ThreadMXBean`.
  * `DataObjectsTester.testClassesOfAModule` makes a module layer.
  * `DbObjectFormatTester.testPackagesSealed` reads the jar's sealing,
    through a `ProtectionDomain` that a dex jar does not have.
  * `PubTester.testConnectionOfEndedThreadNotKept` expects
    `System.gc()` to collect. ART's `System.gc()` does not, unless a
    finalization ran just before: a weakly held object was still there
    after 50 calls of it, and gone after one `Runtime.getRuntime().gc()`
    (`GcCheck`). The behaviour that the test checks, `DatabaseImp`'s
    `WeakHashMap` of threads, is not in question.
  * `databasesStopped` follows from the first Core test.
* **The 2 real failures** are `DataObjectsTester.testGetTable` and
  `testTableReference`, in case G88. They read the malformed bytes `ed a0
  80` as a String: the JDK gives one U+FFFD, Android three.
  * `ObjectFormat` decodes with `new String(..., UTF_8)`, which is the
    platform's decoder, so the same stored bytes give another String on
    Android.
  * Android's three are Unicode's recommended practice, maximal subparts.
  * Whether format 2 defines the replacement, and so needs its own
    decoder, is a question for 020's spec. It matters to the C port too.


## 5. The fixes

Both were made on the branch `006-18-03-android` of
`/Users/f/fl/bench/2026-11-09/android/bergdb`, on `aa55efc`. Each was
gated with `lockf /Users/f/fl/bench/006-15/gate.lock sh
java/before-commit.sh`. Since 16:25 they are `53f4f5c` and `a25a7e8` on
`9ed1e6c`, with `3926a12` for the notes (section 9).

### 5.1 Fix 1: the uptime of the wait statistics, `53f4f5c`

* `Waits.add` takes the uptime from a new `BufferedStream.Uptime`.
* At its initialization, `Uptime` calls
  `ManagementFactory.getRuntimeMXBean().getUptime()` once:
  * If that works, as on every JVM, `Uptime.millis()` returns the JVM's
    uptime, by the same call as before. It still lines up with GC logs.
  * If the call throws a `LinkageError`, as on Android,
    `Uptime.millis()` returns the time since `Uptime` was initialized.
* The new test `BufferedStream.testUptimeIsTheJvms` checks both:
  * on a JVM, the uptime lies between two reads of
    `RuntimeMXBean.getUptime()`;
  * on Android, it is not the JVM's.

  It passed on both.

### 5.2 Fix 2: Data Objects without modules, `a25a7e8`

* **V5, the Java platform's classes.** `isPlatformClass` compares a
  class's loader with `PLATFORM_LOADER`, taken once at class
  initialization:
  * On a JVM, it is `ClassLoader.getPlatformClassLoader()`, as before.
  * Where that method is missing, as on Android, it is
    `Object.class.getClassLoader()`. For its own classes, Android returns
    its boot class loader, not null.
* **V6, exported packages.** Both checks now call `exported(c)`: the one
  of the class's own package, and, since 020-14's X3, the one of the
  package of each class that declares a stored field.
  * Wherever `MODULES` is true, `exported(c)` makes the same call as
    before: `c.getModule().isExported(c.getPackageName(),
    DataObjects.class.getModule())`.
  * `MODULES` is true where `DataObjects.class.getModule()` works at
    class initialization, which is on every JVM. So X3's check is kept on
    the JVM, and so is its test, `DataObjectsTester.testClassesOfAModule`.
  * Where Java has no `java.lang.Module`, as on Android, `exported(c)` is
    true. There is no module boundary there for reflection to cross:
    `Field.get` and `Field.set` check only Java's access modifiers, and
    V1, V3 and V4 already check those.
* `ClassValue` stays, so objects need API 34. On 33, a map from class to
  result would replace it. That map must not hold on to the user's
  classes, and it is more code than a fix.


## 6. What a real Android app needs

* **Packaging.**
  * The release jar works as a plain Java dependency.
  * An AAR is better: its manifest carries `minSdk` (34, or 33 without
    objects), and its `proguard.txt` carries the consumer rules below.
  * There is no native code, so there are no ABIs, and Google Play's
    16 kB page rule does not apply.
* **Size.**
  * The release jar dexes to 1.98 MB of `classes.dex` (0.89 MB
    compressed), its tests included.
  * R8 shrinks it, with ReleaseDemo, to 283 kB (143 kB compressed).
* **R8 rules.**
  * R8 stops at missing classes. It needs `-dontwarn` for
    `java.lang.management.**`, `javax.management.**`,
    `com.sun.management.**`, `java.lang.module.**`, `java.lang.Module`
    and `java.lang.ModuleLayer`.
  * R8 must keep the fields that `findVarHandle` finds by name:
    `Handle.state`, and `TopNode.rootPointer` and `rootPointerPos`.

  An AAR would ship both kinds of rule. Both are in
  `tools/r8-app.pro`.
* **The user's Data Objects.** R8 renames fields, and the field names
  are the stored names (020-09). So an app must keep the fields and the
  no-argument constructors of its Data Object classes. Only the app knows
  those classes, so the documentation must say this.
* **The directory.** The Pub API takes a directory name, and an app's
  working directory is `/`. An app gives an absolute path:
  * under `getNoBackupFilesDir()`; or
  * under `getFilesDir()`, with the database excluded from Auto Backup,
    which copies a live database's files one by one, up to 25 MB.

  The files are private to the app, on ext4 or f2fs, where
  `FileChannel.force(true)` is `fsync`.
* **One process.** `bergdb.lock` refuses a second process. An app with a
  second process (`android:process`) opens the database in only one of
  them.
* **Not on the main thread.**
  * A start reads; `execute`, `sync` and `close` write. All of them
    belong on a background thread, such as an executor or Kotlin's
    `Dispatchers.IO`.
  * StrictMode flags disk access on the main thread, and an ANR comes
    after 5 s of a blocked main thread.
  * A start with bounded startup (007) fits Android vitals' 5 s for a
    cold start (006-18, section 5), off the main thread.
* **Process death is a crash.** Android kills background apps with
  SIGKILL, with no callback. BergDB recovers as from `kill -9` (sections
  4.1 and 4.2). What it loses are the transactions not yet synced: at
  most 50 ms of the write buffer (its buffer time) while the app runs.
* **Freezing.** Android 14 and later freeze cached apps, and BergDB's
  threads stop with them: the buffer's writer and the evictor. So
  durability "within 50 ms" does not hold once an app is in the
  background. An app calls `sync()` in `onStop`, or `close()`.
* **Uncaught exceptions end the app.** On a JVM, an exception that
  leaves one of BergDB's threads (the buffer's writer, the evictor, an
  index build) ends that thread. On Android it ends the process, as
  sections 4.1 and 4.2 saw.
* **Memory.** An app sets the cache size; the default does not fit.
  * Each database allocates a 10 MB write buffer
    (`StorageManager.DEFAULT_BUFFER_SIZE`).
  * The default cache size indicator is 200 MB (`DbBuilder`), more than
    the 192 MB heap that `app_process` and many apps get. An app's heap is
    192 to 512 MB.
  * On the final tree (section 9), `KillDemo check` read all of a
    database of 180,000 transactions (390 MB). It died of
    `OutOfMemoryError` with the default cache, and passed with a 50 MB
    cache.
* **Not checked:** a real phone, its speed, power loss on its flash, an
  app's life cycle (freezing, background kills), and API levels above
  34 at run time. The static check gives 35 to 37.0 the same list as 34.


## 7. A supported Android release

1. Fixes 1 and 2 on `main`, reviewed: 1 hour.
2. The tests: `Util.runsAndroid()` guards for the 13 test failures, and
   `Runtime.gc()` in `testConnectionOfEndedThreadNotKept`: 2 to 4 hours.
3. G88: whether format 2 defines how malformed UTF-8 is replaced. Frans
   decides, in 020.
4. `java/stress/android.sh`, as a night step: 1 day. It takes the SDK at
   pinned versions, runs d8, boots AVDs of API 34 and of the newest level,
   and runs `Unit`, the demos and the kill loop.
5. The AAR, made by a script: half a day. It holds the release jar, a
   manifest with `minSdk`, and `proguard.txt`.
6. A sample app in Kotlin, built with Gradle: 1 to 2 days. It opens the
   database off the main thread, syncs in `onStop`, uses R8, and has an
   instrumented test of a kill in the background.
7. The documentation, an Android section: half a day. It covers the floor,
   threads, the directory, sync, R8 and Data Objects' fields.

This is about 3 to 5 days in all.

* **Why a night step and not the gate.** A boot takes 30 s, `Unit` 2
  minutes, and the SDK 10 GB, which is too much for before-commit.sh
  (Frans, 2026-11-05).
* **Why it matters.** All three blockers came in within two weeks
  (section 1), and without a step that runs on Android, the next one will
  be found only by a user.

**Frans decides:**

* the floor: 34 for everything, or 33 for the Core and the Pub API
  without objects;
* G88;
* whether Gradle and a sample app enter the repository, or stay in an
  item;
* whether to publish on Maven Central;
* a test on a real phone (adb over USB, with USB debugging on).

The licence (006-18, section 5; 017-01's option 1) decides whether app
makers can use BergDB, on Android as for every port.


## 8. Files

All of these are in `/Users/f/fl/bench/2026-11-09/android`, outside the
repository. They can be copied into `03-android-check/` if they are to be
kept.

**Tools, in `tools/`:**

* `ApiCheck.java`: the check of section 2. Usage: `java -cp tools/classes
  ApiCheck JAR ANDROID_JAR [BACKPORTS]`.
* `levels.sh`: runs `ApiCheck` against each installed platform.
* `dex.sh`: d8 for the device (section 3).
* `device.sh`: runs, on a running emulator, the demos, ReleaseDemo with d8
  and with R8, `Unit` and the kill loop.
* `kill.sh`: the kill loop on the device.
* `KillDemo.java`: writes and checks a file database through `Db`.
* `CoreDemo.java`: 006-08's, with today's import.
* `Run.java`: calls a class's `main` for `app_process`.
* `gc/GcCheck.java`: `System.gc()` against `Runtime.gc()`.
* `r8-app.pro`: the R8 rules of section 6.

**Runs, in the bench directory:**

* `api/fixrel-*.txt`: `ApiCheck` per level, jar with fix 1.
* `api/release-33.txt`, `api/release-34.txt`: on `main`.
* `api/dev-34.txt`: on `bergdb.jar`, with `src-dev`.
* `runs-unit-core-main-33.txt`, `runs-unit-core-fix-33.txt`: the Core's
  tests on 33.
* `runs-unit-fix-33.txt`: all of `Unit` on 33, with fix 1.
* `runs-kill-fix-20.txt`: the kill loop on 33.
* `runs-device-fix2-34.txt`, `runs-unit-fix2-34.txt`: API 34 with both
  fixes.
* `gate1.txt`, `gate2.txt`: the gates of the two commits.

**The SDK and the AVDs:** `sdk/` and `user/`, 10 GB. The environment:
`ANDROID_HOME=$PWD/sdk ANDROID_USER_HOME=$PWD/user
ANDROID_AVD_HOME=$PWD/user/avd`. Delete them when they are no longer
needed, and `~/.android` with them.


## 9. Log

* 2026-11-09, 12:44 to 13:37: sections 1 to 8. The fixes were on the
  branch as `14e4b8e` and `99a3c83`, based on `aa55efc`.
* 2026-11-09, 16:03, Frans: "Is this an easy fix we can get into 2026.4,
  let's fix it."
* 2026-11-09, 16:25: the two fixes were rebased onto `main` at `9ed1e6c`.
  The rebase had no conflict: neither file had changed in a way that
  touched them. A third commit adds a Platforms section to
  `releases/next.md`, with G88 as a known difference, and a line in
  README.md, Build and test. `docs/levels.md` lists no platforms. The
  commits on the branch `006-18-03-android` of the clone are `53f4f5c`
  (fix 1), `a25a7e8` (fix 2) and `3926a12` (the notes); on `main`, `07df96d`,
  `0cb5a82` and `435dde7`. On their tree:
  BEFORE COMMIT OK (145 s), and LEVEL 1 OK under the lock.
* 2026-11-09, 16:25 to 16:53, the final tree on the API 34 emulator
  (`runs-device-final-34.txt`, `runs-unit-final-34.txt`,
  `runs-kill-final-34.txt`):
  * The 14 demo runs passed, and so did ReleaseDemo, with d8 and with R8.
  * `Unit`: 17 of 1,581 failed. These are the 15 of section 4.2 and two
    tests newer than `aa55efc`:
    * `DbTesterFailure.testGetTransOfARecordBeingAppended`, which calls
      `ManagementFactory` itself.
    * `StreamContractTester.testOneFileStream`, through 021-14's read past
      the end at a position near `Long.MAX_VALUE`. `OneFileStream`'s
      `RandomAccessFile.seek` throws `IOException: lseek failed: EINVAL`
      on Android, where the JVM's seeks. `OneFileStream` is the simple
      stream, "good for testing"; `Db` uses `FileStream`.
  * The kill loop's first run hid 12 failures, which turned out to be
    `KillDemo`'s own, not BergDB's: its check read the whole database
    with the default 200 MB cache in a 192 MB heap, and died of
    `OutOfMemoryError` (section 6, Memory). The same database of 179,850
    transactions passed the check with a 50 MB cache. A new run, with the
    check at 50 MB, passed all 20 rounds, 157,700 transactions at the
    end.
  * The emulator was shut down at 16:53.
* 2026-11-09, 16:58, Frans: "I think it makes sense to run an Android
  test before a release. At least on the unit tests." Two more commits on
  the branch, on `main` at `e65678a`, which the first three were rebased
  onto without conflict: `c5835a2`, `787cbf1`, `cfc2a29`, then `61e63cc`
  (the tests) and `a3c56cf` (`android.sh`); on `main`, the first three are
  `07df96d`, `0cb5a82` and `435dde7`, the last two `2dad395` and `7406674`.
  BEFORE COMMIT OK (230 s) on the five.
  * **Platform-neutral tests.** The new `bergdb.nanotest.Platform` has
    `android()`, `skipOnAndroid(reason)` and `waitsFor(thread, state,
    lockClass)`. `waitsFor` uses one `ThreadInfo` on a JVM, as before,
    and `Thread.getState()` on Android. `ConsoleUI` counts a skipped test
    apart, prints `SKIPPED test: reason`, and ends with "SUCCESS, N
    successful tests, M skipped". Without skips, as on a JVM, the line is
    unchanged.
  * **What became of the 17 tests that failed on Android.** 12 run there
    now, and 5 skip themselves:
    * DbTesterFailure's two tests wait by `Platform.waitsFor`.
    * G88 has a row of its own on Android: `ed a0 80` as three U+FFFD.
    * `FormatFuzzer`'s six tests fuzz without the allocation bound, which
      only a JVM measures.
    * `testConnectionOfEndedThreadNotKept` calls `Runtime.gc()`.
    * `databasesStopped` follows.
    * Skipped: a lock's owner and a thread's CPU time (Eviction's two
      tests), a module layer, the jar's sealing, and `OneFileStream` near
      `Long.MAX_VALUE`.
  * **`java/stress/android.sh`**, with a line in README.md's list of
    scripts. It is not in before-commit.sh. Its first run: "ANDROID OK
    (1584 tests, 5 skipped) in 119 s; 10 demo runs". On the committed
    tree: "ANDROID OK (1584 tests, 5 skipped) in 151 s; 10 demo runs". The
    JVM runs the same 1,589 tests, none skipped.
