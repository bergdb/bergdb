# 006-15 Day work, 8 November 2026

Created 2026-11-08 by Frans Lundberg. Status: done (2026-11-09; see
Outcome). The plan for the
coordinator's day of 2026-11-08 (coord-1108), a Sunday: the work on
release 2026.4 (020), the progress and the outcome. The way of working is
013-02's (the coordinator).


## 1. The request

Frans, 2026-11-08, 09:01, reading 020-05 (Binson as DbObject's format):
he likes Binson for its many implementations, which matter when a value
is read as raw bytes (the Core API, or C reading a database written in
Java), and DbObject's format for its fast field lookups through the
field table, without parsing the whole object. His question: does the
fixed size of DbObject's values matter for lookups, and can a format get
both Binson's compact values and DbObject's lookups?

Frans, 09:18: "I am thinking of a non-Binson format that gets both the
benefit of variable-length values (compact representation) like Binson
and fast field lookups like the current DbObject. [...] Let's consider
DbObject format as today, but with variable-size values like Binson. How
about that? The idea is that is could support more compact
representation, fast field lookup, and a virtual representation of a
DbObject that is very similar to a Binson object, so conversion would be
straigh-forward."

The coordinator's sketch in the chat (09:18): Binson's value encodings
unchanged; an object framed as a type byte that gives the offset width
(1, 2 or 4 bytes, the smallest that fits the fields), the field count,
one offset per field, then the fields in name order (name length, name,
value); a field's extent from two offsets, so no size fields; arrays in
Binson's framing; no hash, a binary search on the names. A `Payment` is
35 bytes, as in Binson (DbObject today: 71).

Frans, 09:32: "Yes, this is interesting. Start a subagent at XHigh to
investigate this in detail and update 020-05. Start another subagent at
XHigh to investigate the performance of lookup scans of 16-bit hashes vs
binary search for fields as above. I think this should be measured.
Scanning only the beginning of the value bytes to find a field is more
cache-aware. A linear search using compact hashes could be faster than
binary search. We will see. Normally, we have fewer than 100 fields of an
object. This can be assumed. This is recommanded by Binson and for actual
object in object-oriented languages, we typically have less than 20
fields, I think."


Frans, 15:22: "Create a subagent at XHigh to go through the findings of
020-02, 03, 04, 05, 06. Summarize, check and make the documents coherent
and ready for decisions. I lean towards: no nulls, binary search for
fields (no hash list), binson value format but not the whole Binson
format. The API and converting between DbObject and Java objects is not
yet decided, but there are good options that have been researched."


## 2. Ground rules

* Effort: the session high while the usage level is `tight` (013-02);
  agents high, xhigh where Frans says so (both of 09:32).
* Agents at a time: at most 2 while the level is `tight`.
* Usage: up to 95% of the week (Frans, 2026-11-07, 08:22, carried over
  until he says otherwise). Week 82% at 09:33. From 17:12 Ultra, twice the
  usage (Frans: "I did upgrade my subscription of Claude to Ultra, twice
  as much usage"); level plenty.
* Commits to `main` by the coordinator, by path, in Frans's name, with no
  AI attribution; Java changes after `BEFORE COMMIT OK`. Gate lock, if
  one is needed: `/Users/f/fl/bench/006-15/gate.lock`.
* Timing runs on F53 need a quiet machine: no other timing run, gate,
  level script or night run at the same time.


## 3. The work

| Task | Item | Agent | Effort | Scratch | Status |
|---|---|---|---|---|---|
| The format "DbObject's framing, Binson's values", in detail | 020-05 | f05 | xhigh | `/Users/f/fl/bench/006-15/020-05/` | done, 37e8db7 |
| Field lookup measured: 16-bit hash scan against binary search | 020-06 | m06 | xhigh | `/Users/f/fl/bench/006-15/020-06/` | done |
| Objects' storage ready for decisions: 020-02 to 020-06 checked, summarized in 020-02 | 020-02 | d02 | xhigh | none | done |
| The spec of stored objects, with vectors; the implementation plan (no code) | 020-07, 020-08 | s07 | xhigh | `/Users/f/fl/bench/006-15/020-07/` | done |
| Step 1 of 020-08: the codec, the vectors as a test, the harness H0 | 020-08 | i01 | xhigh | `/Users/f/fl/bench/006-15/clone-020-08/` | done |

020-05's programs (`/Users/f/fl/bench/006-14/020-binson/`) were deleted
after 2026-11-07's handover; the agents write their own.


## 3b. The night of 8 to 9 November: unattended coding

Frans, 22:03: "Yes, this is ok and implement. Before you start, do you
need me for more decisions? I want the coding ready at 07:00 tomorrow.
Keep working until you have a solution for 2026.4 with no known issues.
[...] Run subagents at xhigh. We can affort it now." 22:08: "All as
recommended in general" (020-01, section 14.1). 22:12: a fourth index
type `bytes`, "Yes"; "no "night.sh large" tonight. Focus on unattended
coding. You can go fast. Use up to 8 subagents as needed."

* Mode: unattended until 2026-11-09 07:00; check-ins every 20 minutes;
  the watchdog; no quiet block (020-08's step 4, the measurements, waits
  for a quiet hour, or the morning).
* The work, in Frans's order: objects (020-08, updated with 020-09), then
  the indexes (020-01, section 14.1: F4, F5, F3, F6, F7, F8, with the
  `bytes` type), designed first in an item (020-10, its internal keys'
  layout for Frans's review), then built in steps.
* Each coding agent works in its own clone, rebases on `main`, gates with
  `java/before-commit.sh` under the lock
  `/Users/f/fl/bench/006-15/gate.lock`, and commits in its clone; the
  coordinator moves each gated commit to `main` (fast-forward, or a
  rebase and a new gate). Independent reviews of each step before it
  goes to `main` where time allows. `level2.sh` after the objects' switch.
* At most 8 agents at a time, xhigh. A question for Frans goes on the
  list below with a recommendation; the work goes on with the default.
* By 07:00: a summary in `news.md` and in section 6.

Frans, 22:17: "What could there be for me to decide? I think you can
continue to work, you make sensible decisions yourself. Do not wait for
me, make the decisions needed to get the 2026.4 release ready. What
layout of internal keys? Not sure I need to look at that. I don't know
what you mean by this. A stream format change?" So the night decides
for itself; its decisions are listed for his information in the
morning, under "Decided under Frans's delegation". The internal keys'
layout (the Pub layer's own KVs for index definitions and entries; no
change of the Core's stream bytes) needs no review by him.


## 4. If the coordinator stops

The state is in `/Users/f/fl/bench/coord/2026-11-08/state.md`; a new
session continues with `/coordinator resume` (013-02).


## 5. Progress

* 08:36 coord-1108 started; coord-1107 closed at 08:35 (006-14).
* 09:01 to 09:32 Frans and the coordinator on 020-05: fixed against
  variable value sizes, and a format with both (section 1).
* 09:35 Agents f05 (020-05) and m06 (020-06) started, xhigh.
* 09:59 f05 done: 020-05's option (f), DbObject's table with Binson's values
  (section 12b), now recommended; the lookup's variant waits for 020-06;
  committed 37e8db7. Questions for Frans: 020-05, section 12b.11.
* 11:00 m06 done: 020-06 written; a scan of 16-bit hashes (FNV-1a,
  a word at a time) is faster than binary search under 20 fields, hot
  and on cold misses; recommended for (f), 2 bytes a field. 020-05,
  section 12b.4, cites it.
* 14:58 to 15:22 Frans and the coordinator on 020-06: binary search's
  extra cost (5 to 30 ns a lookup, warm) against a whole get (0.8 to
  3.8 µs); Frans leans to binary search, no hashes (KISS).
* 15:23 Agent d02 started (xhigh): 020-02 to 020-06 ready for decisions.
* 15:44 d02 done: 020-02, sections 4 (the decisions 4.1 to 4.12), 5 (the
  API and conversion, not yet) and 6 (enough to decide: yes); 020-04,
  section 11, what (f) changes; corrections in 020-02 to 020-06. The
  coordinator's cache claim corrected: since 015-47 a get returns the
  database's own array (no copy), so under (f) a lookup can be cold.
* 15:51 to 17:09 Frans decided object storage, 020-02, sections 4.1 to
  4.12, one at a time (no null; (f); binary search; names 1 to 255 bytes;
  0x82; arrays A1; one integer; NaN; UTF-8; depth 16; old refused; the
  spec under 018-01's rule).
* 17:13 Agent s07 started (xhigh): 020-07, the spec of stored objects
  with conformance vectors, and 020-08, the implementation plan; no code.
* 17:26 Frans, reading `WebsiteCode.java` and `PayDemo.java`: keep the Pub
  API's main design (020-02, section 5).
* 17:47 s07 done: 020-07 (the spec, 33 valid and 85 invalid vectors, 8
  Binson inputs, checked by a Java and an independent Python codec) and
  020-08 (six steps, about 5 days); questions for Frans in 020-07 (Q1 to
  Q7) and 020-08.
* 17:26 to 19:43 Frans and the coordinator on the Pub API (020-02,
  section 5.1b): no key field in 2026.4, `put(Object)` goes (017-07,
  section 6, for later); `createFast()` goes. 020-07, Q1: a scalar is not
  a level. 19:43 ok-and-implement for 020-08, step 1.
* 19:44 Agent i01 started (xhigh): 020-08, step 1, in a clone.
* 20:15 i01 done: `ObjectFormat` and `ObjectFormatTester` (the vectors,
  H0a, H0b; 28 planted faults caught), the vectors moved into `java/`;
  BEFORE COMMIT OK in the clone (119 s) and on the main tree with
  Frans's `PayDemo.java` edit (120 s, 20:18); committed.
* 22:12 to 04:35 The unattended night: designs 020-09 and 020-10, the
  objects' and indexes' code, reviews, 019-45 to 019-47, 021-06, 021-09,
  021-10, NIGHT OK, the quiet measurements, the audit 020-11 (section 6;
  the minute-by-minute record is the state file,
  `/Users/f/fl/bench/coord/2026-11-08/state.md`).


## 6. Outcome

Written 2026-11-09, 04:35, by coord-1108 at the end of the unattended
night (Frans away 22:20 to 07:00, all decisions delegated at 22:17).

**In short.** Release 2026.4's code is done on `main` (621ee0e), with no
known fault open (020-11): objects in format 2 with Data Objects and
best-effort gets (020-07 to 020-09), the user indexes of 020-10 (new
layout, jobs, scans, primary scan, no ICU, `bytes` type, the API narrowed
and `DbObject` in `bergdb.pub`), two real Core faults found and fixed
(019-46, 019-47), every step reviewed independently and the findings
fixed. NIGHT OK; format 2 faster than format 1 on every path measured,
the Core unchanged against 2026.3 (020-12). Not cut: the release itself.

### 6.1. Done, in `main`

The day (2026-11-08), with Frans: 020-05's option (f) and 020-06's lookup
measurements; the twelve storage decisions (020-02, section 4); the
spec 020-07 with its vectors and the plan 020-08; the API decisions
(020-02, sections 2 and 5.1b: two layers, Data Objects with public fields
only, best effort at a get, null fields left out, no key field, no
`createFast()`; 017-07, section 6); 020-08's step 1 (9a45e06); the index
decisions (020-01, section 14.1).

The night, in order (each gated with BEFORE COMMIT OK; reviews read-only):

* Design: 020-09, the conversion rules (8876480); 020-10, the indexes'
  design (673f3d2).
* Objects (020-08): step 2, format 2 (8185c07; level2 OK); step 7,
  `put(Object)` and the key field out (80bc546); step 8, the binding
  `DataObjects` by 020-09 (ca67411); step 3, format 1 refused (38afb1a);
  step 8's review fixes (7681710); step 6, docs (9a22bd6); the format-1
  false positive for Strings and its review (e92a95a, c9e6975); step 4,
  the measurements (01f02db, 3d8b785, 621ee0e). 020-08 done.
* Indexes (020-10): B1, the release jar (c88e5fa); P1, the primary scan
  and H4 (ae68938); I0, keys and definitions (7aca256); H2 part 1
  (559b9ac); I1, maintenance (249b684); I2 part 1, the new layout, jobs
  and API (5b08db5); I3, the scans (8be9a95); B2 docs (9a9e920); B2 part
  1, ICU removed (41ea870); H3, the jobs harness (57f88ea); B2 part 2,
  `Kv.ikey()` and the narrowing (2917cdb); I2's fixes from three reviews
  and H3 (ab06e26); H2 part 2 (fd6dd09, c25808e); B3, `DbObject` into
  `bergdb.pub` (48378fe) and its review's fixes (7b008af); 020-10 done.
* Entries: 021-06 (d65f5b5, 39fb346, 3cf464e), 021-09 (913ffb4), 021-10
  (in 38afb1a), registered and fixed tonight; 019-45 answered (705a626,
  by design, documented); 019-46, a real stale-pointer race in the Core
  with `CACHE_NOTHING` readers since 2026.2 (68830b8; after review
  25978bc, dee3e48); 019-47, a start kept a value over 1 MiB in memory
  (c126d7d). The 021 and 019 lists have no open entry.
* Tools and notes: `bergdb.dev.Run` (3483a62); `releases/next.md`
  complete (c62e43a, 17f67f7, 9a7b429, b994487, d2de9af); ReleaseDemo
  covers `DbObject` (6514764).
* The audit: 020-11, the known issues of 2026.4, every row with its
  commit and test (843e2f1 to 1a61e79 and this commit).

### 6.2. The night

* Agents: up to seven at a time, all xhigh; about 25 coding and review
  tasks; each step in its own clone, gated there and again on `main`
  where the base moved.
* Independent reviews of every step (020-11, section 6): they found the
  `Job.join` race, a build starving under hot writes, H3's three faults
  after a definition's commit, a String taken for a 2026.3 object, a put
  keeping the caller's `DbObject` array, an assert firing on a legal
  schedule, and smaller points; all fixed with tests.
* `night.sh` on 48378fe: NIGHT OK (65 minutes: levels 1 to 4, the Lean
  tests, 25 night tests, conformance medium). On the final tree
  (7231771): the night tests SUCCESS (26) and LEVEL 2 OK. `level4.sh` OK
  after each Core fix. A second full `night.sh` on the final commit
  d6e8989: NIGHT OK (63 minutes, 26 night tests;
  java/build/night/2026-11-09-0436/report.txt).
* Quiet measurements (020-12): format 2 against format 1, writer 0.29 to
  0.66, lookups 0.13 to 0.44, gets 0.70 to 0.84, an index build 0.46 of
  the time; a `Payment` 36 bytes against 71; `performance.sh ab` against
  2026.3: no alerts.
* Nothing failed that is not fixed. Usage: the week from 0 % at 17:10 to
  17 % at 03:15 (Ultra).

### 6.3. For Frans to decide

1. **020-07's text**, the spec of stored objects, for your approval under
   018-01's rule (you approved its design on 2026-11-08). Read 020-07.
   Recommended: approve; it is checked by two codecs and the vectors.
2. **C-M8, a known cost**: a `w()` of one String or `byte[]` put at an
   object key is 13 % slower (2.6 µs against 2.3), the price of I1's rule
   that fixes 015-28, 015-43 and 015-46 (020-12, 020-11). Recommended:
   accept for 2026.4; a lock-free snapshot of the index set for
   directories without an index can come later.
   *Decided* (Frans, 2026-11-09, 07:18): accepted for 2026.4. "I am not
   currently concerned with the cost in time. I am more concerned with
   layers and complexity." The Core Layer knows nothing of indexes (010-01,
   P12, written down at his request, 07:18); less coupling between the
   index layer and the Pub layer's writes is a study for a later release
   (017-09).
3. **The release of 2026.4**: when to cut it, with 2026.3's candidate
   checks (`night.sh large`, the jar tests on s1, jcstress). Recommended:
   today or tomorrow, after your reading.
4. **For your reading, not decisions**: the decisions taken under your
   delegation (020-04 Q6, 020-07 Q2 to Q5; 020-09, section 6, 24; 020-10,
   section 11, 22; and the night's in the commits and 020-11).

### 6.4. Left

* Later additions, not 2026.4 faults (020-11): the `String[]` form for
  every typed getter (F6), records as Data Objects, an opt-in key field
  (017-07, section 6).
* The release's own checks and cut (6.3, point 3).
