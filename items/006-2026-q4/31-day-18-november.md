# 006-31 Day work, 18 November 2026

Created 2026-11-18 by Frans Lundberg. Status: started. The plan for the
coordinator's day of 2026-11-18 (coord-1118), a Wednesday: the progress
and the outcome. The way of working is 013-02's (the coordinator).


## 1. The request

coord-1117's handover (006-30, section 6): the outcome of the night of 17
November and five decisions. Week 58 % at 06:35, level tight.

Frans's words, 08:42, on the writer proof (030-10, 030-16; puts proved,
deletes in part): "Yes, Tag it and take it off main." On 006-30, section
6: "D1, delete the old proofs now. D2, D3 as recommended. D4, no. D5, as
recommended." On Codex review 3's three points: "Yes, start it."

The decisions, as recorded here:

* **The writer proof** is tagged (`writer-proof-2026-11-18`, on main
  52459c9d) and taken off main.
* **D1:** the old proofs (`lean/SIS/Tree` and the rest of the old proof
  line, frozen at the tag `proofs-2026-11-17`) are deleted now, not after
  the writer proof. Kept, as 030-04, section 4.1, says: the executable
  model (`lean/SIS/Tree`'s definitions, `treeSpec`) and the trace
  checkers that the level scripts and `night.sh` run, and what the
  contract package (`lean/contract/`) imports.
* **D2:** Java's commit-time check (TransCheck, a hook in Db.java) stays
  in `bergdb.core`, off by default.
* **D3:** only the day's coordinator pushes `main`, after a privacy check
  (013-02, section 6).
* **D4:** no proof nights for now: neither the writer proof nor
  reclaim's scheme (T-SCHEME).
* **D5:** an agent fixes Codex review 3's three small points.


## 2. The ground rules

* Usage tight: at most two agents at a time, Opus 5.5. The agents stop at
  the STOP file `/Users/f/fl/bench/2026-11-18/STOP`, touched by a usage
  watch at week 65 % (yesterday's cap was 60 %; Frans's "start it" taken
  as leave for these two tasks; he may change it).
* Agents work in their own clones and commit there; the coordinator lands
  their gated commits on main and pushes.


## 3. The work

* **W1, 030-18: the writer proof off main; the old proofs deleted**
  (agent rm, Opus high): two parts, each gated. Heavy runs (level
  scripts) one at a time.
* **W2, 030-19: Codex review 3's three points** (agent cx, Opus xhigh,
  Frans's word of 2026-11-17 for proof work): a bitmap beyond 64 bits read
  as empty; failed PROBE lines and missing GET/SCAN lines pass the
  checkers; 030-09's "4.3 million" is 3.96 million.
* **W3, D3 in 013-02** (the coordinator): only the day's coordinator
  pushes `main`.


## 4. Progress

* 06:34 Started; coord-1117 closed 06:36 (nothing running or waiting).
* 08:42 Frans's decisions (section 1).
* 08:44 Tag `writer-proof-2026-11-18` on 52459c9d, pushed. Usage watch
  (65 %) started.
* 08:47 Agents rm (030-18, Opus high) and cx (030-19, Opus xhigh)
  started, each in its own clone under /Users/f/fl/bench/2026-11-18/.
* 08:48 D3 written into 013-02, section 6.


## 5. Outcome

Not yet.
