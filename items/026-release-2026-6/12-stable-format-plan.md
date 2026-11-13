# 026-12. The stable stream format: a draft plan

Created 2026-11-13 by Frans Lundberg. Status: open (a draft for Frans).

Every open question that bears on release 2026.6's stable stream
format, gathered into one plan: what must be decided, in which order,
what depends on what, and a recommendation for each. Frans, 2026-11-13,
10:24, "Yes" to: "an agent at xhigh gathers them into one draft plan for
026: what must be decided, in which order, what depends on what, and a
recommendation for each. Then we walk through it one question at a
time". Nothing here is decided by this file; the decisions already
taken are quoted in section 2.1, so that they are not asked again.

Sources read (at `main` `eefd8bb4`, items only, nothing run): 026's
readme, 026-01, 026-03, 026-05 (its row and bytes), 026-08 and 026-09;
027-03 (sections 1 to 23: its gaps G1 to G21 and J1 to J8, its questions
Q1 to Q23, its section 21's V-A to V-D); 024-01 (CL1, CL2, CL4, PF2,
CA1, PA5, PA9, OT1, OT4, CC2), 024-04 (section 5), the questions of
024-18, 024-22 (sections 2.1a, 2.9 and 9) and 024-25, 024-37, 024's Log;
017-07 (section 2), 017-08, 017-10, 017-11; 018-01 (section 2); 019-07,
019-30, 019-31; 005-72; 010-01 and 010-04; 014's and 022's readmes; the
release notes of 2026.5. Cite as "026-12, SF3".


## 1. In short

* **What "stable" would promise** (as recommended here): from release
  2026.6 on, every later release opens a database of a stable format
  and writes on it; an older release that meets a newer format refuses
  it before it writes, with a message that names the release needed;
  what a release writes may still change within the format (018-01,
  section 2). The promise covers the stream and its meaning, the Core's
  internal keys, the directory's reader rules and the Pub layer; not
  encryption, the test node sizes or the files' sizes.
* **11 questions**, SF1 to SF11 (section 2), merged from the open
  points of 027-03 (Q1 to Q23, V-A to V-D, the gaps of its section 19)
  and of the other sources (the map in 2.2). 14 points are already
  decided and quoted in 2.1, among them the compact form (026-01, QC1),
  the node size 30 (026-08), QM1 and the versioning rule as decided work
  (Frans, 09:23).
* **The proposed order** (section 3): the promise and its rule first
  (SF1 to SF4), then the reader's rule (SF5), integrity (SF6), the
  startup distance (SF7), the compact form's open points (SF8) and what
  is checked before the promise (SF9): all can be decided now, but for
  SF7 (b) and (c), which wait for a measurement, and SF8's two encoding
  points, settled with its code. Merges in place and net (SF10) after a
  model run, M1; the fixed numbers (SF11) last, as a checklist. Then the
  code in one batch, so that the bytes, the specification, CST and the C
  clone change once.
* **The three that matter most**: SF1 (what the promise is: everything
  kept in the code for good follows from it), SF5 (refuse what a reader
  does not know: it decides which later changes stay additive),
  and SF10 (the tree a record means: the rules that a stable format
  keeps for good, so QM1 is settled before the freeze).


## 2. The questions

### 2.1 Already decided: not asked again

1. **The theme, and when.** "a stable stream" (Frans, 2026-11-11, 06:56);
   the format is made stable when the algorithms have stopped moving
   (026's readme; 024-04, section 5).
2. **Frans approves every change of the format** (018-01, section 2;
   Frans, 2026-11-05, 09:43: "All changes to the stream format must be
   approved by Frans."). The format there is "the layout and meaning of
   what a start reads: the meta blocks, record headers and records, the
   node encodings, reclaim's table, the version numbers and the reserved
   internal keys"; "A change of which bytes a workload writes, within
   the format, is not a change of the format."
3. **The compact stored form in 2026.6** (026-01, QC1; Frans,
   2026-11-12, 07:26: "QC1. For 2026.6 as recommended. QC2,3,4,5 should
   wait since it is for 2026.6.").
4. **The node size 30 for users**, 8, 14 and 62 for BergDB's tests only,
   the meta block's field kept, written 30 and checked, "the hook for a
   later release" (026-08; Frans, 2026-11-13, 09:17: "This is something
   that is easy to keep a constant first, then allow variation in later
   versions if needed. The other way around is hard."; 09:21, "Yes").
   027-03's Q19 (the node size read from the stream) is dropped.
5. **QM1, and the versioning rule with the corpus, are 2026.6's work**
   (Frans, 2026-11-13, 09:23: "Yes, decided work."); for QM1, "settled
   in 2026.6, with measurements, not that the merge changes" (026's
   readme).
6. **Merges at the delete** (MG; 027-03's Q1, 024-01's CL2) and **dead
   klongs bounded by option 2 at theta 7** (Q2, CL4): format 7, in
   2026.5 (024-21, 024-23; 2026.5's notes).
7. **CRC32C as the node checksum** (024-25; Frans's QL9 in 024-17), in
   the 12-byte node header of format 7.
8. **One operation a key in a transaction, strict** (Q5, CA1; 024-10,
   024-16): a writer writes one value or delete node a key; whether a
   reader refuses two is SF5's (Q22).
9. **P8's endKey in reclaim's row** (Q8, CL1; 026-05, Frans, 09:41:
   "Yes to all four."), read leniently as 027-03, section 15, says.
10. **BergDB assumes correct storage; detection of other damage is best
    effort.** The crash contract is prefix interruption (014-01,
    section 7; Frans, 2026-11-05). Frans, 2026-11-06, 10:42 (017-08):
    "BergDB assumes correct storage. Which makes sense. [...] However,
    use of checksums in the stream is also a reasonable design."
    2026-11-12, 07:26: "Sure, we want a corrupted stream (not an
    unwritten tail) to produce an error message when we open the
    database. But this is best effort, we do assume correct bytes from
    storage". 015-73, 019-30 and 019-31 are outside the fault model.
11. **The file layout is not made a function of the stream** (005-72;
    Frans, 2026-11-05: "Drop B, close").
12. **The Core refuses a caller's writes at its own keys** (024-37, CA3;
    010-04, R5): `/#i/-dummy` and `/#i/dreclaim/`; part of G17 closed.
13. **Encryption is out of the API** (020-28); 017-10 holds the options,
    nothing decided about its return.
14. **Reclaim's keys-only scan in 2026.6** (026-09; Frans, 09:38): it
    changes the bytes written, "no record format".

Precedents: "2026.5 does not need to open 2026.4 databases. But at some
point we want to publish this and then I would like the stream format
to be more stable." (Frans, 2026-11-10, 19:49). The meta block is "for
settings that cannot be stored in other ways. Only for this." (Frans,
2026-11-05, 13:04; 017-07, section 2). "The Pub API is the stable,
default, and preferred API. [...] The Core layer is mostly an internal
layer to develop Pub Layer on top." (Frans, 2026-11-09, 16:27; 020-27).

### 2.2 Where each open point went

| Source             | The point                                        | Here           |
|---|---|---|
| 027-03, 21.3       | V-A to V-D; "what stable means"; first format    | SF1, SF3, SF4  |
| 027-03, 21.3       | the corpus                                       | SF9            |
| 027-03, Q1, Q2     | merges (MG), dead klongs (option 2)              | 2.1-6; SF10    |
| 027-03, Q3         | a compact key node; delta writes                 | 2.1-3; SF8     |
| 027-03, Q4         | the startup distance in a KV (024-01, OT4)       | SF7 (a)        |
| 027-03, Q5, Q22    | one node a key; the nodes' order refused         | 2.1-8; SF5     |
| 027-03, Q6, Q10    | key spaces reserved; a Pub format version        | SF2            |
| 027-03, Q7         | a clean stop's mark (024-01, OT1 (c))            | SF6            |
| 027-03, Q8         | P8's row with E (CL1)                            | 2.1-9; SF5     |
| 027-03, Q9         | reclaim's texts: order, version, strictness      | SF5, SF11      |
| 027-03, Q11        | encryption's place (024-01, PA9)                 | SF2            |
| 027-03, Q12, Q23   | checksums; startupPos (015-73)                   | SF6, SF5       |
| 027-03, Q13 to Q16 | zero bits; reserved bytes; refusing start; types | SF5; Q15 SF3   |
| 027-03, Q17        | the file layout                                  | SF2            |
| 027-03, Q18, Q20   | the constants; the time                          | SF11           |
| 027-03, Q19        | the node size from the stream                    | dropped, 2.1-4 |
| 027-03, Q21        | every check a refusal, with or without -ea       | SF5            |
| 027-03, G1 to G21  | what the code accepts (section 19)               | SF5, SF2, SF6  |
| 027-03, J1 to J8   | what depends on Java                             | SF11, SF2, SF9 |
| 026-01, QC2, QC4   | nominal accounting; reclaim's charge             | SF8            |
| 026-01, QC3        | the startup distance's unit                      | SF7 (b)        |
| 026-01, QC5        | delta writes                                     | SF8; section 4 |
| 024-22, QM1, QM2   | merges in place and net; MF1                     | SF10           |
| 026-08             | the node-size field as a hook                    | SF5, SF8       |
| 024-01, PA5        | a place for objects' storage                     | SF2            |
| 024-01, CC2        | the C clone follows                              | SF9            |
| 017-08, 1 to 6     | header sum, link, node sum, meta sum             | SF6            |
| 017-10, 1 to 4     | encryption's design                              | section 4      |
| 017-11, D3         | a key count in the stream                        | SF7 (c)        |
| 019-30, 019-31     | damage that passes a start                       | SF6            |

### SF1. What "stable" promises

**The question.** What does a stable format promise a user, and for how
long?

**Why it matters.** Every other answer is measured against it: what the
code keeps for good, what a later release may change, what the corpus
tests. 027-03, section 21.3, names it first among the points to decide
with the rule; no item says it yet.

**Options.**

* **(a) Later releases, for good.** Every later release opens a
  database of any stable format and writes on it. An older release that
  meets a newer format refuses it, before it writes, with a message that
  names the release needed (as `StoredTrans.formatRefused` names the
  releases of older formats today). What a release writes may change
  within the format (2.1, item 2); StreamDigest records each such change.
  Cost: each stable format's parsers and rerun rules stay in the code
  and its tests for good; paid only when a change cannot be made
  additive (SF5 makes most changes additive). Later freedom: any change,
  at the price of keeping the old reader.
* **(b) Later releases, for a window**: the stable formats of the last N
  releases or years; an older database is copied through an
  intermediate release. Cost: less code kept; a weaker promise to
  publish; users upgrade in steps.
* **(c) Both ways**: an older release also opens a newer database when
  it uses nothing the older one lacks (027-03's V-D: feature flags,
  read-only modes). Cost: flags, read-only paths, a test matrix of
  releases against databases; against P13 (KISS); no user has asked.
* **(d) No promise**, as today (V-A): each release reads only its own
  format. Not a stable format (027-03, section 21.3: "only a promise not
  to change it").

**Depends on.** Nothing. SF2 to SF5 and SF9 depend on it.

**Recommended: (a).** It is what "a stable stream" says and what
publishing needs (Frans, 2026-11-10, 19:49, in 2.1). Its cost comes
only with a change that is not additive, and SF3 and SF5 keep those
rare. Databases made at the test node sizes 8, 14 and 62 carry no
promise (026-08).

### SF2. What the promise covers

**The question.** Which of a database's bytes are under the promise.

**Why it matters.** 018-01's definition (2.1, item 2) covers the Core's
stream and its internal keys. The Pub layer, the directory and
encryption are outside it, and 027-03 asks about each (Q6, Q10, Q11,
Q17; G15, G20, G21, J5, J6). The recommended answer for each part:

* **(i) The stream and its meaning**: the meta blocks, the framing and
  recovery's fill, the records, the nodes, the tree a record means.
  In; there is no other choice.
* **(ii) The Core's internal keys and their texts**: reclaim's table,
  row and settings (027-03, section 15), and SF7's setting. In: every
  database holds them, and a start refuses what it cannot parse.
* **(iii) The directory.** Options: the reader's rules in (file names
  of exactly 14 ASCII digits, G15; the files contiguous; each but the
  last a multiple of 100,000), the writer's file sizes and the lock file
  out (005-72; J5, J6); or the directory out entirely (the concatenated
  stream is the database). **Recommended: the reader's rules in**: a
  tool or the C clone opens a directory, and the rules are code already
  (`FileStream.checkDbFiles`); the sizes stay the writer's (2.1, 11).
* **(iv) The Pub layer**: its keys (ukey to ikey), objects (format 2,
  frozen at 2026.4 with vectors, 020-07), index definitions
  (`version=1`), entries and markers (027-03, section 17). Options: in,
  with one internal KV written when a Pub database is created that names
  the Pub layer's format version (Q10, G21), refused by a Pub start that
  does not know it; or in without the KV; or out, under a rule of its
  own later. **Recommended: in, with the version KV.** The Pub API is
  the stable, preferred API (Frans, 2026-11-09, in 2.1); a Pub user's
  data is objects and index entries, and without them the promise is
  empty. The KV is the "place reserved for objects' storage" of the first
  theme (024-01, PA5): a later Pub layer that stores values otherwise
  (017-09) knows which version wrote a database. Cost: one KV of a few
  bytes and one read at a Pub start; no Core change (P12).
* **(v) The reserved key spaces** (Q6): the rest of `/#i/` and of `/#`,
  reserved for later releases by the specification (020-22, section
  4.1). A Pub user's keys map outside them (the mapping puts "d" or "-"
  before each name; 027-03, section 17); 024-37 refuses a Core
  caller's writes at the Core's own keys; a refusal of all of `/#` to
  Core callers would be a later, additive change.
* **(vi) Encryption** (Q11, PA9). Options: a place reserved in the plain
  format now (a marker, a nonce, room for a MAC); or none: an encrypted
  database, if encryption returns (017-10), is a container around the
  stream with its own header in clear, version, nonce and tags.
  **Recommended: none in the plain format.** Today's `SalsaStream`
  encrypts every byte from position 0, meta blocks included, so a marker
  cannot be in them (027-03, Q11), and 017-10's designs (epochs,
  authenticated pages whose file positions differ from the stream's)
  sit under the framing in any case.
* **(vii) `created.txt` and `bergdb.lock`**: out; outside the stream,
  informational or the operating system's.

**Depends on.** SF1.

**Recommended.** (i), (ii), the reader's rules of (iii), (iv) with the
Pub version KV, (v) by the specification; (vi) and (vii) out.

### SF3. The compatibility rule (decided work)

**The question.** By which mechanism does a later release read older
stable formats: 027-03, section 21.3's V-A to V-D?

**Why it matters.** It sets what each later change costs and what 2026.6
must write now so that the rule can work.

**Options** (in full in 027-03, section 21.3):

* **V-A. One format a release.** SF1 (d): not stable.
* **V-B. Each record carries its format; a release reads every stable
  format and writes its newest.** A stream may mix formats; the rerun
  switches on each record's format; old nodes are parsed by their own
  format byte. Cost: for each stable format, its node parsers (small)
  and its rerun rules (large if the tree's rules differ) kept; old
  records are rerun only in the starts while they are in the startup
  section, but the code stays; the Lean model checks the newest rules,
  the corpus the older ones. An upgrade is one way: the older release
  then refuses the database.
* **V-C. A database's format fixed at its creation.** A release writes
  on an older database in that database's format (old writers kept), or
  opens it read-only and a tool copies it to the new format. Cost: old
  writers, or read-only paths and a copy tool.
* **V-D. Feature flags** in the meta block (compatible, read-only
  compatible, incompatible), with V-B or V-C: SF1 (c).

**What 2026.6 does for V-B.** No new byte: records and nodes carry their
format numbers already (027-03, section 21.2). The reader dispatches on
them and refuses one it does not know (SF5). And one rule: **every
change that an older release cannot read raises the meta version**
(154 today), so that an older release refuses the database before it
writes anything (`readMetaBlock` writes nothing before its checks,
005-40). That closes G18 and Q15 by rule: today a start may append
recovery's fill to a stream whose record format it then refuses. The
code for a second stable format comes with that format; how an upgrade
happens (at the first write, or only when the builder asks) is decided
then.

**Depends on.** SF1 (a).

**Recommended: V-B, without V-D.** The format already offers it; old
databases open without a copy; with no promise to older releases (SF1)
flags are not needed; V-C's read-only paths and copy tool cost more code
than a kept rerun for a change of the rules that should come seldom. It
is also what the coordinator recommended on 2026-11-10 (006-21, "For
Frans to decide", point 2), not then decided.

### SF4. The first stable format, and the databases before it

**The question.** Which release's format is the first stable one, and
does 2026.6 open 2026.5's databases (record format 7)?

**Why it matters.** A format read by a later release is kept for good
(SF1). Format 7 has been released (2026.5, 2026-11-13); 2026.6 changes
the bytes anyway (SF8, perhaps SF6 and SF10).

**Options.**

* **(a) 2026.6's format is the first stable one.** Record format 8 with
  the compact nodes (SF8; new node format numbers, 026-01, section 5.5),
  meta version 155 (SF3's rule). 2026.6 refuses format 7 and older with
  a message that names the release, as every release has done (2026.4
  refused 2026.3's, 2026.5 refuses 2026.4's). A user makes the database
  again: reads with 2026.5, puts with 2026.6 (2026.4's notes). Every
  "absent means older" path goes: a reclaim row without endKey
  (026-05), a meta block without the node size (0, before 2026-10-27),
  format 6's message. Cost: one constant, messages, tests; less code.
* **(b) As (a), and 2026.6 also reads format 7** under V-B: format 7
  becomes stable after the fact; its fixed-width nodes (formats 3, 3, 5)
  and P5's merges kept for good, which QC1's "the bytes changed once"
  (026-01, section 6) meant to avoid.
* **(c) Format 7 is the stable one**: 2026.6 changes no byte. Against
  2.1, item 3: the compact form would come later, as a second stable
  format with its own kept reader.
* **(d) As (a), but 2026.6's format a candidate**: the promise starts at
  2026.7 if nothing needed a change. A buffer against a mistake kept for
  good, at the price of one more release without a promise.

**Depends on.** SF1, SF3.

**Recommended: (a)**, with (d) as the fallback if SF9's checks (the
completed specification and the C port) are not done by the tag. Reasons:
the bytes change in 2026.6 anyway; reading format 7 would keep its
reader for good; (a) removes code; with the meta version raised, 2026.5
refuses a 2026.6 database before it writes.

### SF5. What a reader does with what it does not know

**The question.** Reserved bytes, unused bits, paddings, unknown node
types, node formats, klong types, setting names, absent fields: refused,
or ignored and passed on?

**Why it matters.** 027-03, section 22, puts Q14 and Q16 right after the
rule: "they decide which later changes are additive". A stable reader's
acceptance cannot be tightened later without refusing databases that a
release accepted; a refusal can always be lifted.

**Options.**

* **(a) Strict: know or refuse.** Every reserved byte, unused bit and
  padding is written zero and refused if not (Q13, Q14; G2 to G4, G7,
  G11's padding). An unknown node type, node format or klong type is
  refused with a message that names the release needed (Q16). A field
  may be absent only where the stable format gives its default. Every
  check is a refusal, with or without -ea (Q21; G14, J3). The other
  gaps of 027-03, section 19, become refusals: n against the node size
  at parse (G5), the first klong a time klong and time klongs increasing
  at every read (G6), the meta block's last byte 0 or 10 (G8) and its
  ranges (G9), the top node's skip times (G10), a value node's size and
  offset (G11), the nodes' order and one value or delete node a key
  (G12, Q22), startupPos never decreasing from record to record (Q23's
  first half), the file names (G15), reclaim's row parsed as strictly as
  its settings, unknown names refused (G16). A later release adds a field
  by giving a meaning to bytes that are zero today; older releases
  refuse such a database (SF1). Cost: about 15 of section 19's gaps,
  each a few lines and a one-change refusal test (CST's tables; C's
  `records.txt` has 359 such cases at format 5); a little CPU a node
  parsed; no byte.
* **(b) Ignored and copied**, 005-50's way for the meta block: a later
  field read by newer releases and passed on by older ones. Cost: none
  now. Risk: an older reader acts on a database whose new field it does
  not understand, without a word (027-03, Q8: an older reader would run
  a reclaim row with E wrongly). It buys forward compatibility, which
  SF1 does not promise.
* **(c) Mixed**: strict in records and nodes; the meta block's 81
  reserved bytes ignored and copied (Q14's choice by range).

**Depends on.** SF1 (no promise to older releases), SF3.

**Recommended: (a).** Frans's rule for the node size (2.1, item 4):
"easy to keep a constant first, then allow variation in later versions
if needed. The other way around is hard." It is also the best-effort
detection of damage that Frans wants (2.1, item 10), without a new
byte, and one rule for Java, C and the specification. 026-08's node-size
field fits it: written 30, anything else refused, as
`Db.refuseOtherNodeSize` does; a later release that allows other sizes
reads 2026.6's databases, and 2026.6 refuses its.

### SF6. Integrity: which checksums the stable format carries

**The question.** Does the stable format detect damaged bytes with
checksums, and in which structures?

**Why it matters.** Frans, 2026-11-13, 06:01 (017-08): "I conclude that
the current implementation is inconsistent in this regard. We should
either assume the storage may be corrupted or we assume [it] cannot be
(except that tail could be unwritten)." Today each node has a CRC32C
(024-25); the record header, the got-dirty list and the meta block have
none (027-03, G12; Q12). The bytes for a checksum are fixed by the
freeze: one added later is a new record format (SF3). Damage known to
pass a start, each outside the fault model: a header field changed
within its checks (015-73, 019-30), whole records cut out (019-31).

**Options.**

* **(a) Trust the storage throughout.** No checksum; the node header
  loses its CRC32C: 4 bytes a node, 2.4 % of a compact key node at B =
  30 (165.9 bytes, 026-01, section 7), more of a small value node.
  Damage is found by SF5's structure checks only.
* **(b) As today**: the nodes only. The inconsistency Frans named.
* **(c) Every structure a start reads carries a CRC32C**: the nodes (as
  today), the record's header and got-dirty list (4 bytes a record, in
  the record frame that SF8's R1 rewrites anyway), the meta block (4 of
  its reserved bytes). It detects random damage of any header field
  (015-73, 019-30), not records cut out whole (019-31) nor a change made
  with its sums made right (018-01, section 6.1). Cost: 4 bytes a record
  and a meta block; one CRC32C a record written and parsed, about 0.12
  ms a MB (017-08, measured for the nodes); `NodeChecksum`'s function
  reused; CST's cases for the new sums.
* **(d) (c) and a link between records** (017-08, part 2): the previous
  record's position or a sequence number, 8 bytes or a varint a record,
  checked through the startup section; it catches 019-31.
* With it, **a clean stop's mark** (Q7; 024-01, OT1 (c)): a record kind
  of the framing, so a start can tell a lost last file from a torn
  tail; or nothing in the format (OT1 (b), an API; or later an internal
  KV, additive).

**Depends on.** SF1, SF2. It sets the node header and the record frame
that SF8 encodes.

**Recommended: (c), and no clean-stop mark in the format.** It makes
the stance consistent (every byte a start reads is covered; detection
stays best effort, the storage still owns integrity) at a cost measured
to be small, in the release that rewrites the record frame anyway: the
last time it comes without a new format. (a) is the consistent
alternative if Frans prefers the bytes to the detection. (d) costs up
to 8 bytes a record for damage that only a harness cutting at record
boundaries has made (019-31).

### SF7. The startup distance: its place, its unit, and a key count

**The question.** (a) Where the stable format keeps the startup
distance sd (024-01, OT4; Q4); (b) in which unit (026-01, QC3); (c)
whether it keeps a count of keys, for a default sd that follows the
database's size (017-11, D3).

**Why it matters.** (a) is a meta block layout; (c) has a deadline:
"Frans decides D3: the measure, and whether a field is reserved in
2026.6's stable format. This decision has a deadline: 026's format
work." (017-11, section 5, step 4).

**(a) The place.** Options: the meta block (bytes 40 to 43), as today,
with the 200,000-byte `/#i/-dummy` KV that forces a meta block at each
change (027-03, section 15); or an internal KV of the Core, read at the
end of a start (only the writer uses sd: the start takes its position
from the last record) and written by a small transaction when sd
changes; the meta bytes become reserved zero and the dummy goes (017-07,
section 2). With SF4 (a), no fallback for older streams. **Recommended:
the KV**, by Frans's rule for the meta block (2.1, precedents). Cost: a
KV and a read at the start; 200 kB less at each change.

**(b) The unit.** Options: stream bytes, as today (a compact stream at
the same sd keeps about 1/r times the transactions, r 0.44 to 0.81 by
workload, so a longer start and fewer bytes a put; 026-01, section 5.2);
or nominal bytes (today's start; a second count of the stream).
**Recommended: stream bytes, the default set again by measurement**
(M2), as 026-01 recommends.

**(c) A key count K.** Options: none (a later release learns K only by
a scan; older databases never get a default that follows K without
one); K in each record, the count after it (a varint in R1's frame, a
few bytes a record, kept by the rerun; 017-11, section 3.3, (a)); K in
the meta block, brought up to date by the rerun (its (b)); reclaim's
count, with a finite retention only (its (c)). **Recommended:
017-11's step 1 first** (Frans's D1: may a default's start grow with K,
and up to what?; about an hour of an agent, no machine; M3). If D1 is
yes, K in each record in 2026.6; if no, nothing.

**Depends on.** (a): SF4. (b): SF8, M2. (c): M3 and D1.

### SF8. The compact stored form: its open points

**The question.** 026-01's QC2, QC4 and QC5, and two points of the
encoding that a stable format keeps for good. Decided: encoding C for
key nodes, V1 for value and delete nodes, R1 for the record frame, T1
for top nodes, in 2026.6 (2.1, item 3).

**Why it matters.** It is the format's largest single part (026-01,
section 6): the stream 19 to 52 % smaller, the index bytes cut to 38 to
47 %.

**The points, each with its recommendation.**

* **QC2. The accounting.** The take, the record limit,
  `dirtyNodeBound`, 024-24's limits and the Lean bounds keep counting a
  key node at its nominal size (32 + 16 n), and no node is written
  longer than that. **Recommended: yes** (026-01, 5.1: every bound of
  format 7 holds unchanged; nothing in `lean/` changes).
* **QC4. Reclaim's charge** counts what a step's record really adds, not
  nominal index bytes against real growth. **Recommended: real bytes**
  (026-01, 5.1: else a step counts its index nodes at about 2.4 times
  their cost).
* **QC5. Delta writes** left unstudied. **Recommended: yes**: an
  algorithm, not an encoding (reads, Rule R and the cut change; 026-01,
  5.6); section 4.
* **One encoding or two.** 026-01 writes a node in the fixed format when
  its encoding would not be shorter, so the stable format would hold two
  encodings of each node kind for good. Options: keep that fallback; or
  one encoding, if a bound shows that encoding C is never longer than
  the nominal size within the format's ranges. **Recommended: one
  encoding if the bound holds** (a shorter specification, fewer tests);
  else the fallback, as designed. Proposed with the implementation, for
  Frans's approval (018-01, section 2).
* **The range.** Encoding C holds n in 7 bits of the header's byte 6 and
  a bitmap as its bit indexes, a byte each (026-01, section 7), so it
  expresses node sizes up to 62. **Recommended: keep that range**, so
  026-08's field stays a hook without a new node format.

**Depends on.** SF5 (026-01, 5.4's parse checks of varints and tags are
SF5's rule), SF6 (the CRC32C in the 12-byte header). Cost (026-01,
sections 5 and 6): about a week of work with the parse checks and CST,
and its review; about 300 lines of C; 1 to 3 % of a put's CPU.

### SF9. What is checked before the format is promised

**The question.** What must exist before 2026.6 promises the format:
the specification, vectors, the corpus (decided work), the C clone?

**Why it matters.** After the promise a mistake is kept for good (SF1).
027-03 is a skeleton: recovery's fill (7), the got-dirty list (8.4),
what a node holds (11.3), the start's rules (14) and the directory (4)
are "to be written". The C clone is at release 2026.4, format 6 (022-07);
the only pinned bytes are C's vectors at format 5 (027-03, section 18).

**The parts.**

* **(a) The specification complete**, every section filled, each
  refusal of SF5 a named rule of the specification, not a Java class or
  message (J7). **Recommended: required.**
* **(b) Vectors**: the creation's bytes, one record of each kind, one
  refusal a rule. **Recommended: required**; Java writes them.
* **(c) The corpus** (027-03, section 21.3; decided work): databases
  written by 2026.6 at B = 30, of the kinds that SD's configurations
  make (deletes, reclaim's cuts, values across meta blocks, each
  workload with a torn tail), with their expected answers at several
  times; every later release opens them in a night step (before-commit
  stays fast). Options: the databases' bytes committed (a few MB, under
  `java/`, since nothing outside `items/` depends on `items/`); or made
  at test time by the release's jar, kept in `releases/`, from a fixed
  workload, compared by digest. **Recommended: the bytes committed**:
  they are what the promise is about, and an old jar may not run on a
  later JDK.
* **(d) The C clone ported to 2026.6** (024-01, CC2; how long C follows
  is Frans's, 022's readme). Options: before the tag, as the second
  implementation that checks the specification (written from 027-03
  first, Java's code second); after the release; or not, with vectors
  and the corpus only. **Recommended: before the tag**, or the format
  is a candidate (SF4 (d)): "The applications of new users (020-24) and
  the C clone found most of 2026.4's bugs" (025-01's readme), and a
  second implementation is how a byte-level specification is known to
  be complete.

**Depends on.** SF1, SF4; done last, when the bytes are final.

### SF10. The tree a record means, and merges in place and net

**The question.** Are format 7's tree rules kept as the stable format's,
or do merges change to "in place and net" first (024-22, QM1)?

**Why it matters.** The rerun's rules are what a record means (027-03,
sections 8.2, 11.3 and 14). Under SF3 a later change of them is a new
record format with the old rules kept for good. QM1 is decided work:
settled in 2026.6, with measurements (2.1, item 5).

**Format 7's rules** (frozen if nothing changes): the upward unlink, the
take-back, the empty key first, root collapse, a space split in place
(027-03, section 8.2); merges at the delete with m, h and c at 8, 17
and 17 (024-22, section 2.1a); at most theta = 7 dead key klongs a node
(024-23). With B fixed (026-08) the specification states them as numbers
at B = 30; their functions of B stay for the tests.

**Options.**

* **(a) P5's way, as 2026.5 has it**: a merge makes new nodes, a node of
  the transaction that it leaves out is taken back, and every klong that
  names it is pointed again (`retarget`). No change; 024-22's proofs in
  progress (TP30 to TP33) stay on it. MF1's waste and the retarget's
  case stay in the specification.
* **(b) In place and net** (024-22, section 2.9): a node of the
  transaction is changed in place, the parent's entries are the net
  change. Fewer take-backs (0.10 to 1.26 a merge in the model's runs;
  every merge after rule O takes back the time split's node), no
  retarget, MF1 gone, and QM2 with it. It changes ids and the parents'
  klongs, so the bytes and what a start reruns. Cost: "perhaps 60 lines
  of `merge` and `mergeParent`" in the model, then Java, conformance and
  the proofs that touch merges.

**Depends on.** M1; SF3 for what a later change costs.

**Recommended: M1 first, then (b) only if it makes the specification's
rerun rules shorter** (no retarget, no MF1 case) **and its proofs fit
2026.6; else (a).** A stable format keeps these rules for good, so
their length in the specification and their proofs decide; the bytes a
delete saves are measured too.

### SF11. The fixed numbers and texts

**The question.** Confirm as numbers that do not move what 027-03 lists
(Q18, Q20; J1, J2, J4, J8), and replace what depends on Java.

**Why it matters.** A specification states numbers, not Java's types or
iteration orders; C copies Java's `HashMap` order today
(`c/src/strmap.h`).

**The list, each recommended as it is but the last:**

* D = 200,000 and M = 128 (the meta blocks); records 8-aligned; the
  file unit 100,000.
* The record size an `i32`; the largest record the largest multiple of
  8 not above 2^31 − 9 (J4).
* The time: units of 100 ns since 1970-01-01 UTC, 56 bits, to about the
  year 2198 (Q20).
* The limits L1 to L6, fixed for every database: a later release may
  raise them, never lower them (2026.5's notes).
* B = 30 and the thresholds of SF10.
* Every range unsigned unless the specification says otherwise (J8);
  numbers in texts as ASCII decimals without sign or leading zeros (J2).
* **Reclaim's texts** (Q9, J1): options (a) a declared line order, as
  text; (b) a binary form; (c) Java's `HashMap` order, described in the
  specification. **Recommended: (a)**: a change of the writer's bytes
  only (the reader takes the names in any order), readable in a dump,
  no `HashMap` in C.

**Depends on.** SF8 and SF10 (the final bytes). A checklist, last.


## 3. The order

| SF   | Depends on | Decided                                     | Measurement |
|---|---|---|---|
| SF1  | -         | now                                         | -      |
| SF2  | SF1       | now                                         | -      |
| SF3  | SF1       | now                                         | -      |
| SF4  | SF1, SF3  | now                                         | -      |
| SF5  | SF1, SF3  | now                                         | -      |
| SF6  | SF1, SF2  | now                                         | -      |
| SF7  | SF4; SF8  | (a) now; (b) after M2; (c) after M3 and D1  | M2, M3 |
| SF8  | SF5, SF6  | QC2, QC4, QC5 now; the encoding in its code | M2     |
| SF9  | SF1, SF4  | now; done last                              | -      |
| SF10 | SF3; M1   | after M1                                    | M1     |
| SF11 | SF8, SF10 | texts now; the numbers last, a checklist    | -      |

**Decided now**, in this order, one at a time: SF1, SF2, SF3, SF4, SF5,
SF6, SF7 (a), SF8's QC2, QC4 and QC5, SF9, and SF11's texts (Q9). No
measurement is needed:
the costs that matter are known (CRC32C, 0.12 ms a MB, 017-08; the
compact form's bytes and CPU, 026-01).

**After measurements.**

* **M1, QM1 in the model** (for SF10). The Lean model's `merge` and
  `mergeParent` in place and net (024-22, section 2.9), run on 024-22's
  exhaustive and random sets (section 3): the nodes made, the take-backs,
  the node writes, the properties (A6), and which proofs (TP30 to TP33)
  it touches; the rerun rules written as they would stand in 027-03.
  An agent, about a day; no timing slot. Frans decides SF10.
* **M2, the compact form in Java** (for SF7 (b) and SF8's details), the
  implementation's own measurement: bytes a put at 1M and 10M keys
  (026-01's matrix), the CPU in a timing hold, a warm start at 10M keys
  with 007-05's StartupBench at the default sd and at sd r; one slot
  for bytes, both for timing. Frans decides the default sd.
* **M3, 017-11's step 1** (for SF7 (c)): 006-19's model with a start's
  time and heap, R0 to R4 and R1p for K from 100k to 1G (017-11,
  section 5); about an hour of an agent, no machine. Frans decides D1,
  then D3.

**The work after the decisions**, in one batch, so that the bytes, the
specification, StreamDigest, CST and the C clone change once (024-01,
section 12: "batch them"). Record format 8 is raised at the first byte
change; its meaning may change on `main` until the tag, as format 7's
did, since no release writes it before then.

1. SF5's strict reader, and SF4's meta version 155 with the refusal of
   format 7; SF7 (a)'s KV, the dummy gone; SF2's Pub version KV.
2. SF6's sums; SF11's declared text order.
3. SF8's compact form with its parse checks (026-01, 5.4), then M2 and
   SF7 (b).
4. SF10's outcome, if (b).
5. SF11's checklist; 027-03 completed; vectors; the corpus saved; the C
   port (SF9). The promise in 2026.6's release notes.

Changes of the bytes within the format (026-09's keys-only scan, a
single maintenance step if 026-03 takes the filler form) land before or
after the freeze: they change what is written, not what a reader
accepts (2.1, item 2).


## 4. Not in scope

* **Encryption itself** (017-10): the cipher, the nonce, the tags and
  whether it returns. Only SF2 (vi): it would be a container around the
  stream.
* **The Pub layer's design** (024-01, PA5's study; 017-09, objects at
  object keys only; type tags of values): Pub API questions. The format
  gets the Pub version KV and the reserved key spaces (SF2).
* **Delta writes** (026-01, QC5) and writing nodes without their dead
  klongs (026-01's K5): algorithms, not encodings (026-01, 5.6).
* **Other node sizes for users** (026-08): decided; the B-functions of
  the thresholds are for the tests.
* **Forward compatibility**: older releases reading newer databases,
  read-only modes, feature flags (SF1 (c), V-D), unless Frans takes them
  in SF1.
* **The form of an upgrade between two stable formats** (at the first
  write, or only when asked): decided with the first format after
  2026.6 (SF3).
* **The writer's choices within the format**: the take, reclaim's
  pacing and steps (026-05, 026-09), the single maintenance step
  (026-03), the write buffer (026-07), the files' sizes. They change
  the bytes written, not what a reader accepts (018-01, section 2),
  and stay free after the freeze; StreamDigest records each.
* **Damage beyond SF6**: changes made with their sums made right,
  records cut out whole (unless SF6 (d)), a lost last file (024-01,
  OT1): best effort and low priority (2.1, item 10).
* **Replication** (017-03) **and block storage** (017-05), which may
  want more integrity later.
* **The trace format** (027-02) **and the Lean model's bytes**: the
  model has none (026-01, 5.5); it changes only for SF10 (b).
* **The Core API's stability**: the format is promised, not the Core
  API, which stays low-level and may change (Frans, 2026-11-09, 16:27,
  020-27).
* **The C clone's own departures and API** (022).


## 5. State

2026-11-13, written 10:26 to 10:50 by the agent sfplan of coord-1113,
from the sources named at the top, at `main` `eefd8bb4`: items only, no
code read, nothing run. A draft for
Frans: 11 questions, SF1 to SF11, each with a recommendation; none
decided. Next: the walk through them with Frans, one at a time, in
section 3's order; then M1 and M3 (agents, no timing slot) beside the
first decisions.
