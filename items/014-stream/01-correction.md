014-01. Stream correction at startup
====================================

Created 2026-11-03 by Frans Lundberg. Status: open; investigation/discussion.
The contract for release 2026.3 decided (Frans, 2026-11-05): prefix
interruption, section 7; the broader crash model and its protocol remain
open. Promoted from 005-83. Historical search complete for this revision.
No implementation change.


1. Question and present position
--------------------------------

What can an interrupted append leave behind, and which outcomes should
startup correct automatically? Frans recalls the 2012 assumption as:
appended bytes are correct, but the final append may stop after a correct
prefix. The old sources strongly support that intended model. The Java
interface did not explicitly specify all interrupted-write or power-loss
outcomes, so this is evidence of design intent, not a hardware guarantee.

Preserve strictly append-only storage: correction may append bytes and
change which records belong to the logical history, but may not overwrite
existing bytes or shorten the stream. Front reclaim is a separate,
already explicit operation. Whether a broader crash model requires a new
format, checkpoint or other mechanism is still open.


2. Historical evidence
-----------------------

Source IDs H1–H8 are resolved in section 8. These are original notes and
code, not retrospective assumptions about the behavior of disks.

**2008: an explicit choice against tail truncation.** H1, 2008-09-22,
describes WriteOnceStream as a byte-storage interface with no knowledge
of its contents. On 2008-10-01 Frans considered truncating a half-written
transaction, then decided: “Use abort instead of truncate to make
WriteOnceStream even simpler.” Remote storage without truncation support
was a reason. The entry requires reading a whole transaction before using
it at startup. On 2008-10-17 it also proposes room for “append-only fixes”.
This anticipates our correction discussion; it does not specify a protocol
for holes followed by intact later records.

**January 2012: arbitrary prefix recovery.** H2, “Append-only Databases”,
says: “The stream can be truncated from the end at any position” and that
it represents “the state of the last transaction completely written to
the stream.” This describes tolerance of a cut in the input image, not
an instruction for recovery to truncate physical storage. H2's v5 copy
retains the statement. It supports Frans's recollection of the prefix
model; it does not explicitly state every outcome of append throwing.

**April–August 2012: correction by appending.** H3, “Stream startup”,
starts from a fixed-location meta block and fills the interrupted final
transaction with zeroes. Its absent success byte becomes zero, so the
slot is invalid and can be skipped. “Two streams in one” also fills the
meta stream's tail. The draft says “completely written” in the zero-fill
condition; context and H6 indicate a missing “not”, not a policy of
invalidating completed transactions. H1's separate 2012 log records
RecoverableStream on 2012-04-30 and integration on 2012-05-02. Its
2012-08-20 entry excludes incomplete creation: the primordial transaction
must have completed before an existing database is recoverable.

**2012: storage, recovery and durability are distinct layers.** H4,
“Layers”, places RecoverableStream above AppendOnlyStream; the latter
exposes append/read/pretruncate. Its format/I/O exceptions are fatal.
H5 separates buffering, failed-child handling and configurable durability
levels, including surviving a process versus surviving the OS. Therefore
“append returned”, “transaction committed” and “durable” must not be
silently treated as the same historical promise.

**2013 source: direct tests of correct prefixes.** H6's earliest archived
commit, 2013-06-06, documents immutable appended bytes and successful-append
readability. It does not explicitly define partial-failure atomicity or
power-loss ordering. RecoverableStream's tests `crashInFirstTransaction`,
`crashInTransactionSize` and `crashInThirdTransaction` supply only the first
10, 2 and 10 bytes respectively of an interrupted 20-byte transaction.
Recovery appends zeroes; iteration skips slots without the success byte.
These are executable examples of prefix interruption, not hole tests.
The bundle begins in 2013, so it is not independent 2012 source history.

**2013–2016: checksums and append-only state.** H7 discusses node checksums
for integrity while normally assuming untampered data; the 2015 log records
Fletcher-16 checks and fixes for crashes in headers/meta blocks. These
checks are not a whole-record recovery guarantee. H8 still requires
purely append-only state and says appended data is never modified.
Nothing found adopts arbitrary corruption as automatically correctable.


3. Name the fault model, not “acceptable corruption”
----------------------------------------------------

Prefer **recoverable interruption** for a permitted crash outcome and
**integrity failure** for damage that violates the selected contract.
Call the two candidate crash models **prefix interruption** and
**unforced-tail damage**. “Recoverable” is conditional on a specified
model, not an intrinsic property of a checksum exception.

Let B be the concatenation of bytes submitted to one serialized storage
stream, and d its guaranteed durable frontier. Under prefix interruption,
the retained crash image is B[0:k], with k >= d: every surviving byte is
correct and no later byte survives a missing earlier byte. Account for
front reclaim by applying this to the retained position range.

This is a global ordering property, not merely a statement that each
individual write may be short. Losing the end of one append but retaining
a later append would violate it. With several completed but unforced
appends, a crash may lose several calls' output; “only the last call can
be partial” additionally needs a durable completion guarantee. Today's
persistent append contract is stronger than the early readability text.
BufferedStream is another boundary: its append can return before disk I/O.

The candidate broader model permits holes or altered/missing bytes in the
unforced suffix, while all already-forced bytes and names survive. This
is a proposed extension, not a guarantee established by the 2012 notes.
Changes to already durable bytes, lost durable file names and inconsistent
identity lie outside both models. Wrong keys/versions and read I/O errors
are separate refusal conditions, not evidence of a correctable tail.
A checksum alone does not establish the cause or the affected frontier.


4. What the new experiment adds
--------------------------------

005-83, power-loss report, sections 1–4, keeps actual forces enabled and
changes only one unforced physical write. All 56 prefix/whole/lost-write
controls recover; all 56 hole images fail the readable-prefix oracle,
checked twice each: 68 startup refusals and 44 later failures. Some
getTrans errors leave the instance active (005-82). A valid later meta
block can survive damage earlier in that same write.

These are captured/modelled persistence images, not physical power-cycle
measurements. They show that current recovery does not implement the
broader model; they do not establish that a particular device violates
the prefix model or loses acknowledged data. The original size-flip
fixture additionally appends 1,057,153 bytes before refusing startup.

Existing recovery already demonstrates a strictly append-only solution
for the narrower model: complete a torn slot as an aborted record and
continue beyond it. A legitimate aborted slot can therefore precede valid,
durable later work. Treating its zero completion byte as a new corruption
and dropping all later history would be wrong.


5. Correction rules to investigate
-----------------------------------

Keep physical bytes distinct from accepted history. With A, B, damaged C
and intact D, startup may retain A and B, but cannot retain D merely
because D's checksum passes: D may depend on C. Never fabricate a committed
transaction or silently skip arbitrary records in the accepted history.

For prefix interruption, retain the old abort/padding idea as the baseline;
a corrupted size cannot be trusted as instructions for unbounded padding.
For the broader model, an appended recovery checkpoint could select the
last validated state, mark the abandoned interval and give a safe resume
position. New transactions would use fresh positions beyond physical EOF:

    Physical: A | B | damaged C | D | recovery checkpoint | E
    Logical:  A | B | E

This is feasible in principle, not yet a complete BergDB protocol. Merely
appending a normal record after broken framing is insufficient. Readers
must find correction metadata independently of damaged lengths, validate
its dependencies and agree on accepted records, including getTrans and
historical iteration. Establish retained-state and checkpoint durability
before new writes are accepted. Repeated crashes during correction must
not revive C/D or silently lose acknowledged transactions.

Known correction gaps remain different from corruption encountered during
ordinary reads: the latter fails the running instance, as in 005-82.
Append-only repair avoids deliberately reusing abandoned positions, but
encrypted partial blocks/checkpoints still need analysis. Reclaim must
retain checkpoint dependencies; replicas need consistent history selection.
A scan of all old repair attempts would violate bounded startup.

The earlier 005-83 truncation proposal was withdrawn. Its SHA-256 framing,
format numbers and 8 MB window remain proposals, not decisions; its
truncation model checks do not validate an append-only replacement.


6. Decisions and completion criteria
-------------------------------------

1. Choose the storage contract: require prefix interruption from each
   provider, support unforced-tail damage in database recovery, or define
   explicit provider capabilities. Establish which physical failures each
   supported provider actually promises to contain.
2. Specify normal return, exception and restart states, readability and
   durability/acknowledgement separately. Locate the protected frontier;
   decide incomplete-creation and wrong-format/key refusal behavior.
3. Specify integrity and framing sufficient to recognize the chosen class
   without trusting damaged lengths or a surviving marker alone. Preserve
   legitimate old aborted slots and decide format/version compatibility.
4. Specify correction publication/discovery, all readers' treatment of
   excluded ranges, and bounds on work, added bytes and retained metadata.
   Test repeated interruption, reclaim, encryption and replica interactions.
5. Compare Java/C results on header/body/commit/meta tears, holes with later
   intact records, corrupt sizes, and no-write refusal cases. Check latest
   and retained historical state, acknowledgement preservation, continuation
   after recovery, and clean-restart determinism (010-P2).

Done when the contract, refusal boundary and append-only protocol are
explicitly decided, and the selected guarantees have implementation and
appropriate crash/conformance evidence. This document records the
investigation and discussion; it does not authorize code changes.


7. The decision for release 2026.3
-----------------------------------

Frans, 2026-11-05, 14:30: “The assumption is the following. A stream is
written correctly or not. The only errors BergDB should recover from is
truncation at the end. The database can assume all written bytes are
correct but that the end of the stream may be truncated. The user can
assume transactions are written correctly or not at all. With force to
storage, we get additional durability guarantees, but what is written is
always assumed to be correct. It is the responsibility of the underlying
stream storage (file system, block storage, flash, whatever) to ensure
this. With this assumption, can we mostly settle 014-01? At least enough
to get 2026.3 done.”

This is prefix interruption (section 3), the 2012 intent (sections 1 and
2), and what recovery implements today: a torn last record is completed
as an aborted record by appending, and 005-83's 56 truncation cases all
recover (section 4). Session bergdb-e8 answered with points 1 to 4, and
Frans accepted them at 14:36: “Yes, do it.”

1. **The contract is written down.** As the provider's duty, in
   AppendOnlyStream's Javadoc: the bytes are read back exactly as they
   were appended; after a crash the stream is a prefix of what was
   appended, at least up to what was forced; the provider, with the
   storage under it, ensures this, not BergDB. As BergDB's assumption, in
   docs/levels.md, section 8, and the release notes: a transaction is
   seen whole or not at all; `sync()` adds durability; a start recovers
   only a truncated tail; any other damage is an integrity failure outside
   the contract.
2. **014-01's fault leaves release 2026.3's goal list** (018-01, section
   3.1), as 015-27 did: under the decided contract the recovery of holes
   in an unforced tail is not a fault. 014-01 stays open in item 014 as
   the longer investigation: a broader crash model (unforced-tail damage,
   sections 3 and 5) and what each provider guarantees.
3. **Harness 6.1** (018-01, section 6.1): its core is that a stream
   truncated at any byte starts with exactly the committed prefix, the
   contract and a hard requirement. Other damage is outside the contract;
   its detection is best effort: the start refuses it, or a read fails the
   database (010-01, P7).
4. **Consequences**, confirmed by Frans:
   * (a) the corrupt-stream checks 015-72, 73, 75 and 019-01 stay in the
     goal list as cheap refusals: a violation is refused rather than used;
   * (b) FileStream, BergDB's own provider, must keep the prefix across
     its files (checked by another agent, 2026-11-05);
   * (c) POSIX does not promise prefix behaviour for unforced appends,
     though common file systems keep appends in order: the release notes
     say that FileStream relies on a file system that does.

Note, 2026-11-26 (028-60, part 2; RB-012): on APFS (macOS) a kill of the
process during an append can leave zeros within the last file's length
where the cut write's bytes should be (031-02, F1; 035-01), not a prefix.
For point 4 (b), `FileStream` restores the prefix: at the open it leaves
a run of zero bytes of at most 8 MB at the end of its last file out of
the stream, and its first append truncates the file there, on every
system (Frans, 2026-11-26). The contract above is
unchanged; nothing above `FileStream` changed (027-14).

Of section 6's decisions, the first is made for 2026.3: each provider must
give prefix interruption. For the broader model, decisions 1 to 5 and
section 6's completion criteria remain open.


8. Sources and search scope
----------------------------

F1-007 is the read-only archive at
`/Users/f/fl/repos/f1/a/007-bergdb-261012`. Relative archive filenames below
are locators within that item, not new document IDs.

* **H1.** F1-007, `bergdb/doc/log-old/2008-2011-log.txt`, dated entries
  080922, 081001 and 081017; `bergdb/doc/log-old/2012-log.txt`, 120430,
  120502 and 120820. The abort decision is explicit, not reconstructed.
* **H2.** F1-007, `bergdb/doc/2013/2013-self-indexed-streams/`:
  `self-indexed_streams_v4_120104.odt`, “Append-only Databases”, paragraph
  beginning “The stream should always represent a consistent state”. Its
  title page says January 2012; v4_110630 and v5_130704 contain the same
  claim. The archive directory's year is not the draft's date.
* **H3.** F1-007, `bergdb/doc/2012/2012-04-stream-format.txt`, “Stream
  startup”, “Two streams in one”, “Recoverable stream”.
* **H4.** F1-007, `bergdb/doc/2012/2012-08-layers.txt`, “Layers”,
  “RecoverableStream”, “AppendOnlyStream”, and their exception sections.
* **H5.** F1-007, `bergdb/doc/2012/2012-stream-manager.txt`, “General”
  (buffering/failure/durability bullets) and “Durability control”.
* **H6.** F1-007, `bergdb-git.bundle`, commit
  `1f4d0b6e21a94077964e72a0f264f193ae0a55e0` (2013-06-06):
  `KissDB/src/kissdb/stream/AppendOnlyStream.java`, class/append Javadoc;
  `KissDB/src/kissdb/storage/RecoverableStream.java`, recovery, Iterator
  and the three named tests. Compared with original 2017 commit
  `50786b2350c01df00452011f851d2e97b49f4aab` in the same bundle.
* **H7.** F1-007, `bergdb/doc/2013/2013-04-notes.txt`, “Stream encryption
  and integrity check”; `bergdb/log.md`, 130508, 150725 and 150726;
  H6's 2017 `bergdb/src/bergdb/core/doc-files/stream-format.txt`,
  “Meta Format Version”, “Trans Format Version” and “Node Format Versions”.
* **H8.** F1-007, `bergdb/doc/2016/startup/startup.md` (2016-05-05),
  “Introduction”, requirement 3, and “Database”'s stream definition.

Searched old text/Markdown notes and logs, extracted ODT text read-only,
and inspected the original bundle in a disposable bare clone outside F1.
The 2014 startup ODT also describes incomplete final meta blocks. No
explicit general interrupted-append guarantee covering holes was found
in this search; that is a search result, not proof that none ever existed.
Current cross-checks: AppendOnlyStream and RecoverableStream; 011-07,
“Fault model and checks” and “Limits and next work”; 012-02, sections 1–4;
005-83's report and append-only reconsideration. Formal-model recovery
results do not establish byte/device persistence behavior.
