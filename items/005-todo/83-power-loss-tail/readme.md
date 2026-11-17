005-83. Power-loss tail experiment
=================================

Ongoing correction/format work moved on 2026-11-03 to
[014-01](../../014-stream/01-correction.md). The original report, runner
and evidence stay here; the bug is not fixed by the promotion.

2026-11-02, by Codex, at Frans's request after discussing 005-82.
Experiment complete; [recovery design](design.md) proposed on the same
date at Frans's request, then [reconsidered for strictly append-only
storage](append-only-reconsideration.md). Design and implementation remain
open. The conclusions below describe the experiment, before any production
change.

The present recovery fails the tested holes in an unforced append. All
56 ordinary controls recover and remain usable; none of the 56 hole
images produces a completely readable transaction prefix. Some open
successfully and fail only on a later read. These are counterexamples
under the stated fault model, not physical power-cycle tests or a claim
that acknowledged bytes were lost.


1. Source and method
--------------------

The full run uses Java at `afc3d207335cc615fdd6f96a68a43ada2bb8a405`,
including 005-74, 005-75 and 005-73, compiled with `--release 17` and run
on F53 with OpenJDK 27, `-ea -Xmx256m`. The earlier `2306213` run gives
the same structured outcomes, recovered times, write counts and error
states. A `git archive` build excludes concurrent worktree edits.

`CaptureIo` exercises production `FileStream` through `FileStreamIo`. It
calls the real file and directory forces, records completed forced data
and names, and snapshots a write after `write` but before its force.
Every admitted image preserves every already-forced byte and name.
No force is disabled. This extends the earlier prefix-only data images
of 011-07, "Fault model and checks", as proposed in 005-47, "Constraints".

There are 24 seed transactions (times 100 to 123), then a sync, then 12
tail transactions (200 to 211). Each tail transaction reads and increments
the preceding counter and writes a new value key. The final sync requests
the flush; snapshots precede that sync's completion. Their acknowledged
time is 123, not 211.

The default 10 MB buffer has a 60-second buffer time solely to batch
deterministically. Selected physical writes are 65 to 253 kB, within the
normal buffered-write size. Node size is 8; retention forever, eviction
off, plaintext, one main storage, no replicas. Two seeds, 11 and 29,
exercise four shapes:

* `replay`: 50 MB startup distance, about 28 kB forced before the write.
* `bounded`: 2,048-byte startup distance, about 37 kB forced.
* `meta`: a file boundary at 200,000; earlier parts of the tail have
  already been forced, so the image preserves those too.
* `lazy`: about 4.34 MB forced, a 2,048-byte startup distance and a
  larger file. A valid later meta block survives after the damaged
  record, allowing startup to pass that record without parsing it.

Each shape has seven controls: the whole write survives or is lost,
and retained prefixes ending at a record boundary, after one or three
header bytes, inside a value, or before a commit byte. Seven hole images
zero the record size, record time, node size, node checksum, 512 value
bytes, an aligned 4,096-byte page, or a commit byte. Later record commit
bytes remain intact. Every hole is checked in two fresh databases: value
reads first, and the damaged transaction's `getTrans` first.

The oracle requires an acknowledged transaction prefix, compares latest
and every retained historical user state with it, and checks transaction
records. A successful case closes and reopens recovery, writes another
transaction, syncs, reopens again, and checks readback. Eight deliberately
lost-synced-data images, outside the fault model, test the oracle itself.

The independent Python checker verifies 120 input images against their
forced prefix, checks that holes change only the declared bytes to zero,
checks 594 retained later commit markers, and independently verifies 16
node-checksum mismatches. The eight negative controls are excluded from
preservation counts. No probe write-budget guard fired.


2. Results
----------

There are 128 distinct images and 184 database checks: 56 controls, 112
hole checks (56 images, two reading orders), eight negative controls and
eight extra corrupt-size checks. All controls recover and complete
write/sync/reopen; all negative controls are detected.

The hole checks all fail the readable-prefix oracle:

| Shape | Checks | Startup refusals | Later failures |
|---|---:|---:|---:|
| replay  | 28 | 28 |  0 |
| bounded | 28 | 20 |  8 |
| meta    | 28 | 20 |  8 |
| lazy    | 28 |  0 | 28 |

Thus 68 refuse at startup and 44 reach ACTIVE but fail a later read or
transaction-history consistency check. With a zero record time, values
can remain readable while `getTrans` returns a time inconsistent with
that history. The result is not merely an over-strict startup check.

In `lazy-s11/zero-value-512`, the forced prefix ends at 4,335,336. Only
512 bytes at 4,336,184 are zeroed in the write ending at 4,588,096. The
node starts at 4,336,096; an intact later meta block is at 4,400,000.
Startup returns time 211, then:

* An ordinary value read throws `DbFailedException` caused by
  `StreamChecksumException` and makes the instance inactive.
* `getTrans` throws `StreamChecksumException`, leaves it active, and
  another transaction is accepted and synced on that copied image.

Eight transaction-first checks accept a write after their parsing error:
node-size, checksum, value and page damage, for both seeds. This
reproduces 005-82 with crash-generated fixtures, rather than only an
arbitrary edit to an established database.


3. Corrupt sizes and the original case
--------------------------------------

These are additional corrupt-input checks, separate from zero-hole
images. Flipping a size bit to increase a record by 1 MiB makes the first
three shapes recover an earlier prefix while appending 949,496 to 994,208
bytes of recovery padding. The two `lazy` variants open and fail when
transaction records are read.

Padding may remain buffered after `sync()`, which waits for the last
committed transaction. The probe records logical growth at startup and
counts physical writes on close, before new user writes.
`growth_after_start` is that completed recovery growth. Legitimately
torn controls also write padding; this is not a claim that sync lost data.

The original 012-14, section 6.6 fixture was copied and reopened on the
current snapshot. Its record at 1,057,744 had size 104 before a flipped
bit changed it to 40. Startup refuses with `Bad lastByte: -105`, after
appending **1,057,153 bytes**: 1,059,016 becomes 2,116,169. All original
bytes remain unchanged. The fixture's acknowledgement boundary is unknown;
it is not counted as an admitted power-loss image. Its input hashes and
output are archived; reproducing it requires the original local fixture.


4. Recommendation and limits
----------------------------

Agree this recovery contract first: an interrupted unforced append must
not make an intact forced prefix unusable. Startup must expose a
consistent prefix before reads and writes begin, preserving every
acknowledged transaction. The experiment shows that today's code does
not meet the stronger hole-tolerant version of that contract.

Next, design how to establish that prefix with bounded work. Study
integrity for the whole record, including header and completion data,
and validation of the possibly incomplete suffix before accepting a
later meta block as the starting point. A surviving marker alone is
insufficient. A format change may be necessary; none is chosen here.
Preserve legitimate failed slots left by previous recoveries: dropping
everything after the first zero commit byte would discard valid later work.

005-82 remains a separate live-read inconsistency. Failing that instance
would stop subsequent writes after a detected error, but would not fix
recovery. Keep the recovery-policy decision explicit before treating
that small patch as a power-loss fix.

These are modeled persistence images captured at the actual write/force
boundary, not actual power cycles. They establish failures for the
patterns tested, not their frequency on F53, or all possible device
behavior. Admitted images never corrupt already-forced bytes. Reclaim,
encryption, replicas, C and Windows are outside the experiment. No
production Java, Lean, format or durability mode was changed. Production
gates were not rerun for this item-local probe.


5. Files and reproduction
-------------------------

* `PowerLossTailProbe.java`: capture, images, oracle and continuation.
* `RefusedStartProbe.java`: the original fixture, on a fresh copy only.
* `analyze.py`: independent image checks and summary.
* `run.sh`: archive build, compilation, provenance and execution.
* `evidence/`: all rows, summaries, manifests, per-transaction oracle
  hashes, example traces and the original-image result.
* `design.md`: proposed protocol, compatibility limits and acceptance work.
* `append-only-reconsideration.md`: correction of the truncation preference;
  append-only recovery checkpoints and requirements still to establish.
* `design_checks.py`: item-local framing and geometry checks; recorded
  output in `evidence/design-checks.txt`. Run with Python 3.

From the repository root, with a new output path:

    sh items/005-todo/83-power-loss-tail/run.sh /private/tmp/bergdb-83-run

The default source is `afc3d20`; `BASE_REF=2306213` selects the initial
baseline. Ordinary mode exits 0 when the experiment and its controls
complete, while reporting recovery failures. To require a hole case to
recover, this currently exits **1** (verified):

    REQUIRE_RECOVERY=true sh items/005-todo/83-power-loss-tail/run.sh \
        /private/tmp/bergdb-83-red lazy-s11/zero-value-512

`FIXTURE_DIR` optionally checks the original refused-start fixture too;
its local source is recorded in `evidence/provenance.json`. It is not
needed for the self-contained 128-image experiment. Raw images and
recovered directories stay in the output path, outside Git.

The archived full run is from
`/private/tmp/bergdb-005-83.dmAq1k/final-current`; the filtered regression
and original fixture ran in `regression-current` alongside it. These
scratch paths may later be removed; the source regenerates the main
experiment. `evidence/full-run-artifacts.sha256` identifies the full
run's jar and probe; the regression manifest also identifies its copied
runner and checker.

2026-11-05 (015-19): `PowerLossTailProbe.java` is kept for the code of its time, not
changed: it calls `DbBuilder.retainForever` (removed by 015-87; forever is
the default). It compiles against release 2026.2's jar, not against main's.
