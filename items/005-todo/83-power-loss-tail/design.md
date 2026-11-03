005-83. Initial recovery proposal: truncation
============================================

Reconsidered at Frans's request on 2026-11-02: the recommendation to
truncate is withdrawn in favor of investigating strictly append-only
recovery checkpoints. See [reconsideration](append-only-reconsideration.md),
sections 1–5. The original proposal below is retained for its integrity,
validation and tradeoff analysis. Its trim protocol and model checks do
not establish an append-only implementation or its startup bound.

2026-11-02. Design requested by Frans after the power-loss experiment.
Status: initial proposal, superseded as indicated above; no production
change or format decision has been made. The experiment is in 005-83,
power-loss report, sections 1–5.

Recommendation: introduce integrity for entire records and meta blocks,
enforce a maximum physical write window, validate consecutively from an
older, forced anchor, then remove only the rejected suffix before ACTIVE.
Do not repair by trusting a damaged size or by skipping to a later record.
The proposed first implementation covers plaintext main file storage.
Encryption, legacy streams and replicas have explicit restrictions below.


1. Contract and assumptions
---------------------------

An interrupted append may leave any subset of its bytes, including holes
followed by intact later records and meta blocks. Earlier completed forces
preserve their bytes and file names. Writes are serialized. A completed
sync acknowledges only complete transactions covered by those forces.
Creation, deletion and force ordering remain part of the storage contract.
This is the experiment's fault class, extended with interrupted suffix
removal in section 6. It excludes damage to previously forced bytes,
lying devices, arbitrary namespace corruption and adversarial edits.

On a supported image, startup returns a consecutive transaction prefix
containing every acknowledged transaction. It may retain additional whole,
valid transactions. It never retains a later transaction after discarding
an earlier one: that later transaction may have read the discarded state.
Startup finishes validation and repair before accepting any user operation.
Normal recovery needs no user decision; report discarded bytes and the
last recovered time in StartupInfo and diagnostics.

A checksum failure during ordinary operation still fails the instance
(P7 and 005-82). Recovery permission applies only to the startup suffix
identified below. Corruption outside the supported fault class is not
promised automatic repair. In particular, without a persistent exact force
frontier, old corruption in that suffix cannot always be distinguished
from crash damage. The protocol is not a general bit-rot recovery scheme.

Integrity conclusions assume that the digests detect the damage. No
finite checksum can prove that an arbitrary altered record is original.
Use SHA-256 rather than the existing 16-bit node sum for this decision;
this is corruption detection, not authentication against a malicious writer.


2. Establish a physical window, independently of buffering
---------------------------------------------------------

Use W = 8,000,000 physical stream bytes, fixed by the new format version.
A persistent storage writer must force after at most W newly issued bytes,
before issuing any more. Split larger appends, including single huge
records. Count meta blocks and bytes crossing file boundaries. Force and
publish a new file's name before its data can become part of the stream.
There must be no second outstanding unforced write window on the main.

This is a new enforced invariant, not an inference from the default
10 MB buffer. Its ordinary flush currently contains at most 5 MB, so this
cap alone requires no additional forces for that configuration. Larger
buffers, direct appends and custom providers must also obey the cap. A
provider without that guarantee cannot use this recovery mode. A future
written-without-force mode (005-47) must preserve a finite window too.

Let L be the physical EOF seen after a crash and F the unknown last
completed force frontier. Under this invariant:

    F <= L <= F + W
    T = max(0, L - W)

Every byte strictly below T is forced. A complete meta block ending at or
before T is therefore an anchor candidate even when a newer, perfectly
checksummed meta block lies after a hole. Never select that newer block
as the initial authority. W cannot be increased by a runtime setting:
older readers would then scan too little. A change needs a new protocol.

First creation must force the initial meta block and creation transaction
before publishing ACTIVE. When L < W, scan from the initial block and
creation transaction instead. An incomplete first creation remains a clear
refusal (005-33), without writing a replacement database over it. After
reclaim, section 4 guarantees an older anchor remains available.


3. Proposed format 155 / record 6
---------------------------------

Reserve these version numbers subject to checking again at implementation.
Keep the 128-byte meta block and 200,000-byte spacing. Keep existing node
formats and their checksums. All integer fields below are little endian,
matching the present stream. Align complete logical records to 8 bytes.
Logical record bytes exclude the interleaved meta blocks.

A concrete framing proposal is a 64-byte header, the existing node and
got-dirty-list body, zero alignment padding, then a 48-byte footer. There
is no old format-5 completion byte in the body. The minimum record is 120
bytes (64 + two four-byte body terminators/counts + 48). The maximum stays
at StoredTrans.MAX_RECORD_SIZE, with the larger framing charged to it.

| Header offset | Bytes | Field |
|---|---|---|
|  0 |  4 | Total logical record length |
|  4 |  1 | Record version = 6 |
|  5 |  1 | Kind = 0, data record |
|  6 |  2 | Header size = 64 |
|  8 |  8 | Transaction time |
| 16 |  8 | Startup position |
| 24 |  8 | Top-node position |
| 32 |  8 | This record's physical position |
| 40 |  8 | Reserved, zero |
| 48 | 16 | First 16 bytes of header SHA-256 |

The header digest is SHA256(domain || dbId || header), with bytes 48–63
zero during hashing. Its domain is the ASCII bytes `bergdb155/header`
followed by a zero byte. Validate this small fixed header before trusting
its length, pointers or allocation request. A matching digest with an
unsupported version/kind is a refusal, not permission to discard it.

| Footer offset | Bytes | Field |
|---|---|---|
|  0 | 32 | Whole-record SHA-256 |
| 32 |  4 | Repeated logical length |
| 36 |  4 | ASCII bytes `bEND` |
| 40 |  7 | Reserved, zero |
| 47 |  1 | Completion byte = 10 |

The whole digest is SHA256(domain || dbId || logicalRecord), with only
its own 32-byte field zero during hashing. Its domain is `bergdb155/record`
plus a zero byte. It covers the size, header digest, time, pointers,
position, every body/padding byte, repeated length and completion data.
Meta blocks are checked separately. Read and hash in fixed 64 KiB chunks;
check length bounds, overflow and available logical bytes before allocating
or parsing a record. Header hashing and full hashing are separate passes
over only the header, not two passes over the whole body.

Extend the existing meta layout using its reserved bytes:

| Meta offset | Bytes | Field |
|---|---|---|
|  0 | 46 | Existing fields, version now 155 |
| 46 |  8 | This meta block's physical position |
| 54 |  4 | W = 8,000,000 |
| 58 |  2 | Protocol flags = 0 |
| 60 | 35 | Reserved, zero |
| 95 | 32 | SHA-256 of this block |
|127 |  1 | Existing completion byte = 10 |

Hash `bergdb155/meta` plus a zero byte, then the entire 128-byte block
with bytes 95–126 zero. Its dbId and self-position bind it to this stream
and location. Retain lastTransSpos: it names the preceding complete
transaction and gives a conservative record boundary for scanning. Inside
a large record it may be far behind the meta block. Validate the named
record too; never search payload bytes for a plausible header or marker.
Use the first record after the initial meta block as the special creation
anchor when no preceding transaction exists.

Java 17 supplies streaming SHA-256 through MessageDigest; see the
[official API](https://docs.oracle.com/en/java/javase/17/docs/api/java.base/java/security/MessageDigest.html).
C needs the same byte-level digest definition and shared vectors. This
proposal chooses SHA-256 for integrity margin; its throughput cost must be
measured before implementation is considered release-ready.


4. Keep an anchor through reclaim and interrupted recovery
----------------------------------------------------------

Two durability frontiers are necessary:

* D: physical bytes whose force has completed.
* C: end of the latest complete, published transaction covered by D.

Track C from committed-record end positions and D; never infer it from
an incomplete record's header. A conservative lag is safe. Updating C
needs synchronization with publishing record completion: a flush may
finish before the writer publishes that completion. Sync must not
acknowledge beyond the covered complete-record frontier.

For reclaim, select a complete regular meta block A whose end is at or
before max(0, C - W), and retain A plus its referenced record start r0.
If there is no such block yet, retain the creation area. The actual
physical cut must be no later than both the existing logically safe cut
and r0, rounded down to a file boundary. Keep the existing durable reclaim
table conditions too. Apply the restriction to deferred deletion, not
merely to a logical first-position variable.

Why C, rather than D? A huge transaction may have many forced chunks
while none of it is committed. Recovery must discard that whole record.
Using D could reclaim the only anchor needed after that discard.

For any admitted crash, L >= C, so the retained A ends before L - W.
If recovery keeps prefix E, then E >= C: no complete forced transaction
can fail integrity under the assumptions. Therefore A also ends before
E - W. It is still a safe anchor if suffix removal itself crashes and
leaves the shorter length E. This is the reason the retention rule is
part of recovery, not a later reclaim optimization.

Let M = 200,000 and R be the maximum physical span of a legal record,
including inserted meta blocks. Anchoring through lastTransSpos adds at
most two such spans. Integrity scanning adds at most W + M + 2R bytes,
apart from creation and existing startup replay/reference reads. The
extra retention has the same conservative scale, plus whole-file rounding.
R is presently about 2 GB, not a small-record promise. This does not
close T4 or prove a practical constant-time startup. It avoids a scan of
the whole retained database, but very large records can still be costly.
Reclaim lag may increase disk use substantially; measure it.


5. Read-only startup, then a specific repair plan
------------------------------------------------

1. Obtain exclusive ownership of the directory. Open inspection handles,
   without buffered flush workers, replication copying or recovery writes.
   Determine L and T from the fixed protocol, then validate the selected
   anchor at/before T. A malformed anchor in this forced region is fatal;
   do not silently walk backwards through corruption looking for another.
   Check identity, key, version and settings before planning any change.
2. Scan consecutive records from r0. Check every crossed meta block,
   header, complete-record digest, footer and structural/ordering rules.
   Maintain the last valid record's physical end E, time, startup pointer,
   top pointer and metadata state. A record spanning T must be checked in
   full, including its earlier bytes. Do not let an intact later meta block
   bypass this scan. A valid digest with impossible record semantics is
   a refusal: a failed serializer or incompatible implementation is not
   evidence of an interrupted append.
3. On missing bytes or a digest/completion failure touching bytes after T,
   stop at the preceding complete record. Discard the entire remainder,
   even if later complete records survive. A failed header wholly before
   T, a bad meta wholly before T, or a bad complete record ending before
   T is fatal. The implementation must distinguish damaged framing from
   read I/O failure, wrong key, unknown format and allocation failure;
   those failures never authorize trimming. An invalid header is checked
   for integrity before interpreting its potentially damaged version.
4. Reconstruct the database against a read-only view ending at E, using
   the accepted record's startup pointer, never a rejected tail's pointer.
   Run normal replay, reference, time, root and reclaim-table checks.
   Do not eagerly hash every historical value: older forced bytes remain
   an assumption. If this reconstruction fails, close with no writes.
5. For a fully valid image, keep it unchanged, including a valid eager
   trailing meta block. Otherwise produce the exact plan [E, L) to remove.
   Apply section 6 and force the result. If a record ends exactly at a meta
   boundary, regenerate that eager meta from the accepted state, not from
   the damaged template; this is at most 128 bytes. Validate the regenerated
   block, and force any accepted bytes that had survived without a force.
6. Reopen ordinary storage at the repaired EOF, initialize normal durable
   frontiers and fresh clock/STM/cache state, then publish ACTIVE. No old
   transaction, read set or node handle survives the restart (005-70).

The scan must also check the anchor record that precedes r0's successors;
if an anchor points into unavailable reclaimed bytes, refuse before any
write. An interrupted trailing meta block can be removed without removing
the complete transaction before it. Do not extend any purported record
with zeroes, and never synthesize a successful transaction.


6. Startup-only physical suffix removal
---------------------------------------

Do not weaken AppendOnlyStream.append or its increasing-length contract.
Introduce a separate exclusive startup capability, conceptually
`inspect -> plan -> trimSuffixAndForce(E) -> openAppendOnly`. It cannot be
called on an ACTIVE database. An unsupported provider refuses this mode.
Only bytes outside the recovered prefix may be removed; surviving bytes
and their logical positions stay unchanged.

For FileStream: quiesce deferred cuts and all channels; remove files
wholly beyond E from highest position to lowest, forcing the directory
after each removal. Then truncate the boundary file to E and force its
length/data metadata. If E is a file boundary, retain a contiguous prefix
of file names and handle an empty next file consistently. Reopen channels
and compute lengths afresh. A failed operation closes startup; it never
publishes a partly repaired database.

Highest-first deletion means each interrupted removal still leaves a
contiguous prefix of names. Model a pending truncation as preserving the
bytes below E and leaving a size between E and the old EOF. Both sizes
retain the protected anchor from section 4. Any remaining malformed tail
will be recognized at the next start. Directory force and boundary-file
force must complete before subsequent appends can reuse positions.

This pending-truncation behavior is a new storage assumption requiring
fault-injection tests and native audits; Java's API alone does not prove
power-loss atomicity. Java documents truncation and forcing separately in
[FileChannel](https://docs.oracle.com/en/java/javase/17/docs/api/java.base/java/nio/channels/FileChannel.html);
Linux also requires a directory sync for directory entries, as described
in [fsync(2)](https://man7.org/linux/man-pages/man2/fsync.2.html).

Trimming reuses positions of discarded, unacknowledged records. The public
TransactionInfo exposes time and KVs, not a durable physical identifier.
Nevertheless document that low-level positions and handles belonging to
a lost suffix cannot be carried into a new instance. Synced transactions'
positions and times are preserved. This is a deliberate change from
padding failed slots and needs the new format/storage contract.


7. Compatibility and scope restrictions
----------------------------------------

**Existing format 154.** It lacks full integrity, so it cannot obtain this
guarantee retroactively. Keep a separate legacy reader; no automatic
in-place conversion and no new framing appended to an old stream. Create
a new format-155 database or explicitly export/import a validated legacy
database, preserving supported retained history. Legacy failed slots
(last byte zero) may precede valid, durable work. Do not apply the new
stop-at-first-invalid rule to those slots. Old binaries must refuse 155
before writing. Migration is a separate deliverable, not presumed trivial.

**Encryption.** Do not pass suffix trimming through today's SalsaStream.
Its key/nonce and position determine the keystream; position reuse would
reuse that keystream for different plaintext. This is an inference from
its constructor and append implementation, not a tested encryption fix.
The first implementation must reject encrypted format-155 recovery that
needs trimming, without writes. To offer the same guarantee for encryption,
a separate provider design must give each reused range a new, durably
selected nonce/generation while preserving reads of the retained prefix.
Copying and re-encrypting the entire retained database would lose bounded
startup. Encryption support is a release blocker if this guarantee is
advertised for encrypted databases; it is not covered by the plaintext plan.

**Replicas.** Current startup syncStreams copies before recovery. That
ordering must not be used here. Inspect each copy read-only first; never
propagate rejected tail bytes or pick a winner solely by length. For the
first implementation, refuse attaching replicas in the new recovery mode
before any writes. Single-main recovery does not establish STRONG sync or
multi-copy prefix selection; that remains part of 005-11. Existing
experimental replication behavior receives no new guarantee.

**Java and C.** Reserve and implement the format together, including byte
vectors, digest domains, meta insertion and boundary truncation. Java/C
must choose the same recovered prefix and generate identical subsequent
bytes. Update the format specification in 012-02 as part of implementation.

**P2.** Digests, framing and regular meta blocks are deterministic. Physical
write splitting and forces add no timing-dependent stream bytes. A clean
restart writes nothing. An interrupted write can contain transactions
accepted before the crash that do not survive recovery. Do not relabel
them as refused requests. Compare continuation bytes from the same
recovered prefix; this is not a proof of P2 across crash histories with
different lost transactions. Keep that distinction explicit in 010-01;
the current Lean restart theorem does not model torn physical records.


8. Alternatives and implementation sequence
--------------------------------------------

Only fixing 005-82 stops subsequent live writes after detecting corruption;
it cannot make a crash-damaged suffix readable. Only adding a record digest
still misses holes before an intact later meta block unless startup scans
them. Scanning all retained data loses bounded startup. Forcing every
200 kB meta interval is simpler to anchor but changes the force granularity
substantially; do not assume its throughput cost is acceptable. Persisting
exact force frontiers in a sidecar adds another crash-consistency protocol.
Retaining arbitrary failed slots through append-only repair seals avoids
position reuse, but introduces authenticated gap indexing and its own
bounded-startup problem. Prefer explicit startup truncation for plaintext.

Proposed implementation units, in dependency order:

1. Freeze the byte specification and vectors; implement read-only framing,
   hashes and validator in Java/C. Run the old experiment as a red baseline.
2. Enforce W in physical storage; track C and protect anchors in reclaim.
   Test direct appends and oversized buffers, not only default batching.
3. Add the exclusive repair capability and failure injection at every
   delete, force, truncation and regenerated-meta boundary. Move startup
   copying/workers after inspection; enforce the scope restrictions.
4. Integrate prefix-view replay and diagnostics. Fix 005-82 independently
   with its original live-read regression; recovery does not excuse it.
5. Run the acceptance matrix below, then performance and native audits.
   Only then decide whether the proposed format is ready for release.

Acceptance requires all of the following:

* Rebuild the 56 hole fixtures and 56 controls for the new format; latest
  state, every retained historic state and transactionInfo equal one prefix
  containing every acknowledged transaction. Reopen, write, sync and reopen.
* Holes/bit flips in every framing field, node, value, padding and meta
  block; intact later frames; header/record/footer/meta/file boundary tears;
  several records per physical write and one record spanning many forces.
* Crash at every repair step, repeatedly, including the long incomplete
  record with D far beyond C, reclaim on, delayed deletion and post-repair
  reclaim. Check all retained references and anchor availability.
* Wrong key/version/settings, digest-valid invalid semantics and corruption
  wholly before T refuse without writes. A corrupt size causes neither
  unbounded allocation nor padding. Inspect-only plans never modify bytes.
* Clean restart byte equality; Java/C cross-open and continuation digests;
  explicit legacy failed-slot fixtures and new-mode provider restrictions.
* Java before-commit, Levels 2 and 3 (full), Level 4 because startup and
  handle reconstruction change; C gates and matching conformance. Measure
  hash throughput, sync latency, startup reads, memory and retained bytes
  with default settings, large records and reclaim. Do not claim existing
  Lean proofs or prefix-only power-loss tests prove this new protocol.


9. Checks performed for this proposal
-------------------------------------

`design_checks.py` is an item-local model, not production recovery. It checks
concrete proposed header/footer/meta hashing, changed-byte rejection,
truncated frames, stopping before valid later records, bounded length
handling, the C-based anchor inequalities and highest-first file deletion.
It also demonstrates negative cases for trusting a later meta block,
using D for retention, ignoring the W cap and deleting files lowest first.
Run with Python 3; the recorded output is `evidence/design-checks.txt`.

The model does not implement FileStream, meta insertion, reconstruction,
replicas or encryption, and does not emulate filesystem persistence. These
checks support the format arithmetic and design arguments; they are not
an implementation pass, a Lean proof or a physical power-cycle result.
