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

* Usage: the week's stop at 80 % (Frans, 08:56: "Use 80 % as today's
  stop. For now, at least."); up to three agents, Opus 5.5. The agents
  stop at the STOP file `/Users/f/fl/bench/2026-11-18/STOP`, touched by a
  usage watch at week 80 % (65 % from 08:44 to 08:56).
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
* **W4, 026-21: a combined first study of step times and net change**
  (026-20; agent st, Opus high): the model's writer in three variants (net
  change, step times, both) beside today's, on the trace sets and two new
  workloads; step times' risk 2 first. Frans, 08:49: "Either we start
  investigating Net Change. Or we investigate Step Times. Not sure which
  to start with, or a first study of both, before we decide the direction
  of the implementation." 08:56: "OK, run the one combined study as
  proposed. Note that simplification is the overall goal, getting rid of
  take-back completely is one way to reach it. It is not a goal itself."
* **W3, D3 in 013-02** (the coordinator): only the day's coordinator
  pushes `main`.


## 4. Progress

* 06:34 Started; coord-1117 closed 06:36 (nothing running or waiting).
* 08:42 Frans's decisions (section 1).
* 08:44 Tag `writer-proof-2026-11-18` on 52459c9d, pushed. Usage watch
  (65 %) started.
* 08:44 Agents rm (030-18, Opus high) and cx (030-19, Opus xhigh)
  started, each in its own clone under /Users/f/fl/bench/2026-11-18/.
* 08:45 D3 written into 013-02, section 6.
* 08:50 026-20 written down from coord-1117's write-up (f8865cb8).
* 08:56 The stop at 80 %; agent st (026-21) started 08:57.
* 09:02 030-19 done (agent cx): Codex review 3's three points fixed, 16
  fault tests, no statement changed; LANDED e0a723b6, GATE OK (195
  theorems, the standard axioms only, 135 files pinned).
* 10:09 030-18 done (agent rm): the writer proof off main (51 files,
  lean/contract 58,347 to 18,640 lines, 195 to 126 theorems) and the old
  proofs deleted (588 files; lean/ 337,483 to 84,556 lines; lean/SIS/Tree
  210,119 to 3,507); GATE OK, LEVEL 2, 3 and 4 OK; LANDED 150a111a. Left
  for Frans: two statements and four Props kept without their proofs (030-18).
* 10:20 Frans on 030-18's two points: "1 and 2 as recommended": the
  statements kept without their proofs are dropped (agent rm, resumed
  10:21); lean/BergDB (the user indexes' proofs, 020-29) is kept.
* 10:39 030-18's follow-up (agent rm): the statements kept without their
  proofs dropped (two theorems' statements in HandleReclaimTheorems.lean,
  four Props in Tree/Props.lean; pins rewritten, no main theorem of
  lean/contract changed); lake build, gate.sh steps 1 to 3 and 5, LEVEL 2
  OK; LANDED as a merge after 756b4afd, whose message ran ahead of it.


## 5. Outcome

Not yet.
