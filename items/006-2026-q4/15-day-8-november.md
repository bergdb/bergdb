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


## 2. Ground rules

* Effort: the session high while the usage level is `tight` (013-02);
  agents high, xhigh where Frans says so (both of 09:32).
* Agents at a time: at most 2 while the level is `tight`.
* Usage: up to 95% of the week (Frans, 2026-11-07, 08:22, carried over
  until he says otherwise). Week 82% at 09:33.
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

020-05's programs (`/Users/f/fl/bench/006-14/020-binson/`) were deleted
after 2026-11-07's handover; the agents write their own.


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


## 6. Outcome

Not yet.
