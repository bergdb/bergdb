017-08. Checksums in the stream
===============================

Status: open (notes only). May or may not be added in some future
release; not 2026.3. Created 2026-11-06 by Frans Lundberg, at his
decision on 019-30, 019-31 and 019-33 (10:42), as a long-term topic;
019-07, a checksum of the record header, moved here the same day.

What this topic holds: checksums and links that cover the whole stream,
so that a start or a read detects damage that passes today: a checksum
of the record header, a link between records, and a stronger node
checksum. Nothing here is planned.


Frans's words
-------------

Frans, 2026-11-13, 06:01, on hearing that the node checksum (Fletcher-16,
CRC32C since 024-25) came with the 2017 code: "This is not the time or
place to decide this. But good to know. I conclude that the current
implementation is inconsistent in this regard. We should either assume
the storage may be corrupted or we assume if cannot be (except that tail
could be unwritten)."

The node checksum's cost, measured 2026-11-13 (releases/2026.5's notes,
Baseline): Fletcher-16 took about 5.6 ms a MB, CRC32C about 0.12 ms a MB
(024-25). Between the commits just before and after that change
(e9b9b4cd, 3dd38b23; `performance.sh`'s `w-uni-1k-inf`, values of 1 kB,
one run each, F53 not quiet), commits a second went from 93,892 to
236,737 (+152 %) and a restart from 0.705 to 0.463 s (-34 %), with the
same durability. So in 2026.4 the checksum, which the design does not
need if the storage is trusted, took more than half of a 1 kB put's
commit time. With CRC32C what is left is small: 4 bytes a node and
about 0.12 ms a MB.

Frans, 2026-11-06, 10:42, deciding 019-30, 019-31 and 019-33, each as
recommended (option (a), outside the fault model for 2026.3, as 015-73):
"Yes, as recommended. BergDB assumes correct storage. Which makes sense.
Ensure this is documented in the relevant Javadoc comments. However, use
of checksums in the stream is also a reasonable design. Going in that
direction is definitely not for 2026.3. Remember the target: bug-free
Core. Move the possibility of checksums in the stream to a new item in
017. This may or may not be added in some future release."

Frans, 2026-11-05, 15:35, on 015-73, to session bergdb-a2, which asked
"do you take (a), plus a 019 entry for (c)?": "Yes. Go ahead." Option
(c), a checksum of the record header, became 019-07, waiting for the next
change of `RECORD_FORMAT`; it is in this topic since 2026-11-06.


What it is
----------

Today (the records' format 5, `RECORD_FORMAT`; meta blocks of version
154):

* **The record header**, 32 bytes: the size (4 bytes), the format byte,
  3 unused bytes, the time, `startupPos` and `topPos` (8 bytes each). No
  checksum covers it. A start checks its fields only against each other
  and the stream: the content fills the size exactly (015-72), the times
  increase and are in range (005-75), the `startupPos` is one the take
  can have written (015-75), and the last record's `topPos` is the newest
  version of its top node in the startup section (015-75).
* **The nodes**: each has a 16-bit checksum in its bytes 6 and 7,
  `NodeChecksum`, Fletcher-16 with its two sums modulo 255 (since the
  format of 2015.4). A sum modulo 255 does not tell a byte of 0x00 from
  one of 0xff.
* **Between records**: nothing. A record does not name the one before
  it, by its position, a sequence number or a running checksum.
* **The meta blocks**: a magic, a version, a last byte and checks of
  their fields (019-01, 019-34); no checksum. 81 bytes are reserved.

The direction, in three parts that may be taken together or alone:

1. **A checksum of the record header** (019-07's proposal, below): in
   its 3 unused bytes after the format byte, such as a 16-bit sum like a
   node's, written by `StoredTrans.Serializer` and checked by
   `StoredTrans.Parser.parse`. It catches any damaged header field: the
   size, the time, `startupPos` and `topPos`.
2. **A link between records** (019-31's option (b)): the previous
   record's position, or a sequence number, in the header, checked at a
   start; then a range of whole records cut out of the stream's middle
   no longer leaves a valid stream of fewer transactions.
3. **A stronger node checksum** (019-33's option (b)): Fletcher-16
   modulo 256, or a CRC such as CRC32C, instead of Fletcher-16 modulo
   255.

A wider form of the same: one checksum per record that covers its header
and its content (the nodes and the got-dirty list), such as a CRC32C,
with or without the nodes' own sums.


Why it matters
--------------

BergDB assumes correct storage (Frans, 2026-11-06, 10:42): the crash
contract is prefix interruption, written bytes are correct and only a cut
tail is recovered (014-01, section 7; 018-01, section 6.1). Its checksums
and checks of other damage are a best effort: a start refuses what they
see, or a read fails the database (P7). What they do not see is taken,
and reads answer other values than were written, with no error. Four
such kinds are known, each decided outside the fault model for 2026.3:

* **015-73** (016-06's R6-F2; Frans, 2026-11-05, 15:35): the last
  record's `startupPos` changed to the exact start of an earlier record
  that the take never reached; the start begins there, and the
  transactions before it are lost.
* **019-30** (harness 6.1, 018-07; Frans, 2026-11-06, 10:42): a
  record's time changed within its neighbours', so a read at its own time
  misses the transaction; the last record's `topPos` set to a version of
  its top node before the startup section, so the start takes an older
  index.
* **019-31** (the same): whole records cut out of the stream's middle,
  the records after them moved back; the stream left is a valid stream of
  fewer transactions, as nothing links a record to the one before it.
* **019-33** (the same): a node byte changed between 0x00 and 0xff, as
  a torn or zeroed sector may do; Fletcher-16 modulo 255 does not see it.

Parts 1 to 3 catch these: part 1 the first two (and any other damaged
header field), part 2 the third, part 3 the fourth. None of them catches
a change made with the checksums made right again, as harness 6.1's node
copies are (018-07, section 2); such a change is a valid stream with
another meaning.


What is known
-------------

* **No cheap check without a format change** catches these (019-30,
  019-31, 015-73): a time within its neighbours' is a valid time; an
  older version of a top node before the section, or the transactions
  before a moved `startupPos`, are known only by reading records before
  the section, which the bounded startup (007) does not do; after a cut,
  every field of the records left is right.
* **The costs** of any part:
  * a change of the stream format, which needs Frans's approval before it
    is made (018-01, section 2): a proposal in its entry, with which
    bytes, which sum and how a start refuses a wrong one;
  * a new `RECORD_FORMAT` (6) for parts 1 and 2, and a node format for
    part 3; a start refuses a stream of another format, so streams of
    format 5 are refused, unless the code reads both;
  * the C clone (012), which writes Java's bytes, follows;
  * StreamDigest's digests change: the entry keeps them before and after
    (018-01, section 2), and the release notes name the format change;
  * room: the header's 3 unused bytes hold a 16-bit sum, not a 32-bit
    CRC; a link of 8 bytes, or a 32-bit sum, makes the header larger; a
    node has 2 bytes for its sum;
  * time: a sum per record written and per record read at a start.
    `java.util.zip.CRC32C` (Java 9 and later) uses the CPU's instructions
    where it has them.
* **Shared cost**: 019-07's view was to make the change with another
  change of the record format, when one is planned. None is: 015-87 kept
  its settings in an internal KV instead.
* **Block storage** (017-05): a stream on a raw device, without a file
  system's own checks, may need these more.


Open questions
--------------

1. Whether at all: does BergDB stay with "BergDB assumes correct
   storage", the storage's duty (`AppendOnlyStream`'s Javadoc; a file
   system or a device with its own checksums), or detect such damage
   itself?
2. Which parts: the header only (1), the header and a link (1 and 2),
   all three, or one checksum per record over its header and content?
3. Which sum: Fletcher-16 modulo 256, Adler-32, CRC32C, or another; and
   where its bytes go.
4. Old streams: is a stream of format 5 refused, or read as before
   without the new checks?
5. When: alone, or with another change of the format to share its cost.
6. The meta blocks: a checksum in their reserved bytes too?


The entry 019-07, as it was when it moved
-----------------------------------------

Status then: waiting (for the next change of the record format). Kind:
Implement. Frans: decision. Created 2026-11-05 by Frans Lundberg.

Not for 2026.3, and not before a change of `RECORD_FORMAT` is planned:
Frans took it for that change, with 015-73's option (a) (2026-11-05,
15:35). It was his exception to the rule that an open entry is done
before the next release.

What: a checksum of a record's header, written by
`StoredTrans.Serializer` and checked by `StoredTrans.Parser.parse`. The
header is 32 bytes: the size (4 bytes), the format byte, 3 unused bytes,
the time, `startupPos` and `topPos` (8 bytes each). No checksum covers it
today; the nodes have their own (`NodeChecksum`). The 3 unused bytes after
the format byte can hold the checksum, such as a 16-bit one like a
node's. A new `RECORD_FORMAT` (6), since a stream of format 5 has zeros
there; a start refuses a stream of another format.

Why: 015-73 (016-06's R6-F2). A last record's startupPos damaged to the
exact start of an earlier record that the take never reached passes the
checks of 015-72 and 015-75, and the start succeeds without the
transactions before it. A checksum of the header catches that, and any
other damaged header field too: the time (005-75) and the size (015-72).
It catches random damage, a flipped bit or a torn write; a change made
with the checksum made right again, as harness 6.1's copies are (018-01,
section 6.1), stays outside the fault model.

Why (a) was chosen for 2026.3, and not this:

* A start uses only the last record's startupPos
  (`Db.getStartupPosFromLastTransaction`).
* A cut of the stream's tail, the crash contract's damage (prefix
  interruption, 014-01, section 7), never changes it: a torn last record
  is completed as an aborted one, and the record before it is used.
* After 015-72 and 015-75 only an exact landing on an earlier record's
  start gets through.
* The other option, (b), a check that reads back before the section,
  works against the bounded startup (007), which reads only the section,
  and covers one field only.
* No format change is planned now: 015-87 kept its settings in an
  internal KV instead.

Frans: a decision. The checksum is a change of the stream format, and
needs his approval (018-01, section 2): the proposal, written here when a
change of `RECORD_FORMAT` is planned, says which bytes, which sum and how
a start refuses a wrong one. The C clone (012) follows.

Done when: Frans has approved the format change; a test with a record
whose header has a damaged field (R6's startupPos probe among them) is
refused at a start, and fails on the code before the change; the change
is in `main` after `before-commit.sh` and the level script of the
mechanism (AGENTS.md); `releases/next.md` has its line under Format; the
entry becomes a folder that keeps StreamDigest's digests before and
after (018-01, section 2).

First step: when a change of `RECORD_FORMAT` is planned, write the
proposal here and ask Frans; until then, nothing.

Its log: 2026-11-05, registered in night 006-12, at Frans's decision on
015-73 (15:35, to session bergdb-a2: "Yes. Go ahead.", to "do you take
(a), plus a 019 entry for (c)?").


Log
---

2026-11-06. Created at Frans's decision on 019-30, 019-31 and 019-33
(10:42), each closed as decided with option (a), outside the fault
model for 2026.3; their options (b) and (c), a header checksum, a link
between records and a stronger node checksum, are parts 1 to 3 here.
019-07 moved here by 017's rule for moved entries: its contents above,
its row in 019's Closed table (moved), its file a short note with a link.
