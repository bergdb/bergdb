# 020-14 A Codex review of 2026.4's code

Created 2026-11-09 by Frans Lundberg. Status: open (findings to fix).

An independent review of release 2026.4's new production code by
OpenAI's Codex CLI (model GPT-6.1-Sol, reasoning effort max, Frans's
subscription), before the release candidate. Kept apart from 020-11 (the
known issues) and 020-13 (the test study) until it is done; each finding
is then checked by a failing test before any fix.

Frans, 2026-11-09, 08:45 (to coord-1108): a review by GPT-6.1 Sol Max;
09:11 (to coord-1109): "Codex command line is installed, let it do the
code review. Use latest Sol, effort Max." The latest Sol in Codex's
model list (codex-cli 0.167.0) is `gpt-6.1-sol`.


## 1. How it runs

* Clone: `/Users/f/fl/bench/2026-11-09/clone-codex`, `main` at
  `a9e5488`, made for the review alone.
* Command, from coord-1109 (directory `/Users/f/fl/bench/2026-11-09/codex`,
  the brief of section 2 in `prompt.md`):

      codex exec -m gpt-6.1-sol -c model_reasoning_effort="max" \
        -c approval_policy="never" -s workspace-write \
        -C /Users/f/fl/bench/2026-11-09/clone-codex \
        -o last-message.md - < prompt.md > codex.log 2>&1

* Sandbox `workspace-write` in the clone, not `read-only`: the clone is
  thrown away afterwards, and Codex may then compile and run small
  probes, so a finding comes with a reproduction that ran. No network.
  `main` and the other clones are outside its reach.
* Output: the findings in `last-message.md`, the run's log in
  `codex.log`; the coordinator copies the findings into section 3.


## 2. The brief

The prompt given to Codex, verbatim:

<!-- BRIEF START -->
You are reviewing BergDB, an append-only database for Java, in this
clone (a Git repository; read AGENTS.md and README.md first). Release
2026.4 is about to be cut. Its theme is "a bug-free database". Your task
is an independent code review that finds real defects in the production
code that 2026.4 adds or changes, before the release candidate is made.

What counts as a defect: a wrong result; data lost, corrupted or made
unreadable; a legal call that throws or hangs; a race or a lost update
under concurrent use; a start or a reopen that fails or gives other data;
a refusal that the spec or the Javadoc does not allow, or a missing
refusal that it requires; behaviour that contradicts the spec or the
public Javadoc. Not wanted: style, naming, performance (unless a cost is
unbounded, such as quadratic work or memory without a limit), wishes for
new features.

The code to review, in this order of priority (the change since the last
release is `git diff release-2026.3..HEAD -- java/src`):

1. User indexes, their maintenance and their build jobs, in
   java/src/bergdb/pubimp: IndexManager, IndexBuilderImp, IndexReference,
   IndexDefinition, IndexKeys, Entries, PubKeys, RwEnvironmentImp (the
   index maintenance at a write), UseIndexBuilderImp,
   UsePrimaryBuilderImp, DatabaseImp (deleteIndex, indexJob), and
   java/src/bergdb/pub/util/Job.java and JobStatus.java. Look hardest at
   concurrency: a build running while writers write, a delete or a stop
   during a build, a restart in the middle of a build, the read time
   used by a lookup against the index's generation.
2. ObjectFormat (the stored format of objects, "format 2") against its
   spec and the conformance vectors in
   java/src/bergdb/pubimp/doc-files/object-vectors.txt.
3. DataObjects (the conversion between plain Java objects and DbObject)
   against its rules.
4. The public API classes in java/src/bergdb/pub (DbObject, DbArray,
   DbValue and its subclasses, Connection, IndexBuilder, UseIndexBuilder,
   UsePrimaryBuilder, Database, Kv) and pub/util: does the code do what
   the Javadoc promises?
5. Two fixes in the Core (the layer below, a key-value store of byte
   arrays): commits 68830b8, 25978bc and dee3e48 (a stale-pointer race in
   java/src/bergdb/core/Cache3.java, NodeCollection.java and
   java/src/bergdb/dag/Handle.java), and c126d7d (a start that kept a
   large value in memory: core/Db.java, core/Eviction.java). Are the
   fixes correct and complete?

The specs, in items/020-release-2026-4/: 07-object-spec.md (the stored
format), 09-conversion-rules.md (Data Objects), 10-indexes-design.md (the
indexes), and the Javadoc. 11-known-issues.md lists what is already
known: report a finding listed there only if its row says it is fixed or
not a fault and you find that it is not so.

What you may do:

* Read anything in the clone, including Git history.
* Build with `java/build.sh` (JAVA_HOME is set) and run single unit test
  classes, for example `java/unit.sh -c IndexManagerTester`.
* Write small probe programs or tests under the directory `probes/` at
  the clone's top, and run them, to show a defect. A probe in a package
  of bergdb (to reach package-private members) runs with
  java/build/classes before anything else on the class path, not the
  jar, since the jars seal bergdb.pub and bergdb.pubimp.

What you must not do:

* Change the production code or the existing tests (a finding is a
  report, not a fix), or write in items/ or docs/.
* Run java/before-commit.sh, java/night.sh, java/stress/*.sh,
  java/perf.sh or anything long or heavy: the machine is shared and
  timings run on it. Keep to one JVM at a time, each run under a few
  minutes.

The report, as your final message, in Markdown:

1. Findings, most severe first. For each: an ID (X1, X2, ...); a
   severity (critical: data lost or corrupted, or a start that fails;
   high: a wrong result or a throw from legal use; medium: a contract
   broken in a corner; low: a small mismatch with the spec or the
   Javadoc); the file and line; what is wrong, in a few sentences; the
   spec section or Javadoc it breaks; a reproduction (the probe's path
   and what it printed, or exact steps); and how sure you are
   (confirmed by a run, or by reading only).
2. What you reviewed and found sound, area by area, in a few lines each.
3. What you did not get to.

Prefer few real findings over many weak ones. A finding by reading only
is welcome when it is precise: the exact interleaving or input that
breaks it.
<!-- BRIEF END -->


## 3. Findings

Codex ran 09:14 to 09:29 (exit 0; Codex session
01a1bf5f-46d2-7122-ad08-9c011b43b01d). Its report, verbatim (the probes are
in `/Users/f/fl/bench/2026-11-09/clone-codex/probes/`, run with
`sh probes/run.sh` after `java/build.sh`):

<!-- CODEX REPORT START -->
Reviewed `release-2026.3..a9e5488`. **Three confirmed findings.** Only `probes/` was added; production code and existing tests are unchanged.

After `java/build.sh`, reproduce all three with `sh probes/run.sh`.

**1. Findings**

**X1 — high — Directory key replacement leaves persistent missing index entries**

Location: [RwEnvironmentImp.java:417](/Users/f/fl/bench/2026-11-09/clone-codex/java/src/bergdb/pubimp/RwEnvironmentImp.java:417), also line 401.

Index maintenance selects the directory’s indexes and reads the previous value using the unexpanded key. The transaction later expands `${transactionTime}` in directory components. Maintenance consequently modifies the wrong directory’s index: it can remove an unchanged object’s entry, while an active index of the actual destination misses the new object. Reopening preserves the incorrect index.

This breaks **020-10, sections 3.3 and 5.1**, `IndexBuilder`’s maintenance promise, and `Connection.setEnableKeyReplace()`, which permits replacement throughout a put’s key.

Reproduction: [DirectoryKeyReplaceProbe.java](/Users/f/fl/bench/2026-11-09/clone-codex/probes/DirectoryKeyReplaceProbe.java). Store and index an object under the literal directory `/p/${transactionTime}/`; then enable replacement and put through the same key. The original object remains, but disappears from its index:

```text
literal index before=1
literal direct after=7
expanded direct=9
literal index after=0
reopened literal direct=7
reopened literal index=0
```

The probe also demonstrates a destination index returning zero results while its primary scan returns one.

**Confidence:** confirmed by execution, including reopen.

**X2 — high — A non-VM initializer error during conversion fails the database**

Location: [DataObjects.java:609](/Users/f/fl/bench/2026-11-09/clone-codex/java/src/bergdb/pubimp/DataObjects.java:609).

`make()` translates constructor exceptions, `ExceptionInInitializerError` and `LinkageError`, but misses an `AssertionError` thrown directly by a static initializer. That error escapes conversion. Inside `rw()`, the transaction wrapper then marks the whole database failed, although no transaction has committed.

This breaks **020-09, section 5.2**: conversion programming faults must become `ObjectCreationException`, with `VirtualMachineError` explicitly allowed through; inside `rw()`, the database should continue. It is an uncovered variant of **020-11’s R8-2**, marked fixed.

Reproduction: [InitializerErrorProbe.java](/Users/f/fl/bench/2026-11-09/clone-codex/probes/InitializerErrorProbe.java). Its public Data Object class has a static initializer throwing `AssertionError`; reading it inside `rw()` printed:

```text
conversion=java.lang.AssertionError: bad initializer
next put=bergdb.pub.util.DbFailedException: Cannot call execute(): the database failed (the cause) and must be restarted.
```

**Confidence:** confirmed by execution.

**X3 — medium — Inherited fields from a non-exported package pass validation but fail conversion**

Location: [DataObjects.java:260](/Users/f/fl/bench/2026-11-09/clone-codex/java/src/bergdb/pubimp/DataObjects.java:260); reflection fails at lines 505 and 634.

The class check verifies that the concrete class’s package is exported, but retains `Field` objects declared by its superclasses without checking their package accessibility. A public class in an exported package can inherit a public field from a public superclass in a non-exported package. Ordinary Java field access works, and BergDB accepts the class, but its reflective get/set fails.

This breaks **020-09, sections 3.1–3.3 and 5.2**: inherited public fields are included, the stated class rules accept this shape, and class-access failures should be established independently of the stored data.

Reproduction: [InheritedModuleFieldProbe.java](/Users/f/fl/bench/2026-11-09/clone-codex/probes/InheritedModuleFieldProbe.java), with its module sources under `probes/module-src/`. It printed:

```text
ordinary Java field access=42
empty get=model.Person
```

Put conversion threw `IllegalArgumentException`; conversion of a matching stored field threw `ObjectCreationException`. Both reported `IllegalAccessException` because `review.model` does not export `hidden`.

**Confidence:** confirmed by execution.

**2. What I reviewed and found sound**

- **Indexes and jobs:** Apart from X1, I found no additional defect in definition locking, directory conflict hashes, generation isolation, build-step validation, delete/cleanup ordering, restart resumption, job snapshots or joins. Scan definitions, entries and objects use one resolved lookup time. `PubTesterIndexRaces`, `PubTesterIndexJobs` and the unit `IndexHarness` passed. `IndexReference` is a test reference, rather than production maintenance code.
- **ObjectFormat:** Reviewed canonical widths, integers and lengths, field extents and ordering, UTF-8, NaN, depth limits and binary lookup. `ObjectFormatTester`, including the conformance vectors, passed; no additional defect found.
- **DataObjects:** Reviewed class validation, exact puts, null omission, cycles, array covariance, numeric saturation, conversions and absent-field defaults. Apart from X2 and X3, no additional defect found. `DataObjectsTester` passed.
- **Public API:** Reviewed the named object/value classes, builders, connection reads, primary/index iteration, `Database`, `Kv`, `Job` and `JobStatus` against their promises. Copies and immutable views appeared consistent. `PubTesterPrimary` passed.
- **Core fixes:** The current drop handshake preserves an object installed during the race, and the writer’s forced caching closes the empty-handle path. Startup admission now visits resident key-node pointers, including values linked from the startup section’s first transaction. `NodeCollection` and the focused startup-admission regression passed; no defect found in these fixes.

`java/build.sh` passed. All runs used one JVM at a time.

**3. What I did not get to**

I reached all five requested areas, but did not exhaustively audit every other `pub/util` implementation or changed helper outside the named scope. I did not independently enumerate all concurrent schedules, inject crash images, or exercise near-2-GB limits. No prohibited heavy scripts were run.
<!-- CODEX REPORT END -->


## 4. State

The review is done. X1 to X3 go to a fixer agent (x14): a failing test
from each probe, then a fix, gated in its clone; then into `main`.


Log
===

2026-11-09. Created by coord-1109 at Frans's word (09:11); the clone and
the brief made, Codex started.

2026-11-09. Codex done in 15 minutes: X1 (high), X2 (high), X3 (medium),
all confirmed by a run; the report copied into section 3.
