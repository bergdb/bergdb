# 006-15 Day work, 8 November 2026

Created 2026-11-08 by Frans Lundberg. Status: open. The plan for the
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

For Frans to decide (the night's list): none yet.


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


## 6. Outcome

Not yet.
