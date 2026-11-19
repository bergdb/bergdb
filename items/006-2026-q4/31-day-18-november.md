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

* Usage: the week's stop at 85 % (Frans, 12:51; 80 % from 08:56: "Use
  80 % as today's stop. For now, at least."); up to three agents. The agents
  stop at the STOP file `/Users/f/fl/bench/2026-11-18/STOP`, touched by a
  usage watch at week 85 % (65 % from 08:44, 80 % from 08:56).
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
* **W5, 028-15: the startup distance into an internal KV** (agent sd,
  Opus high). Frans, 10:50: "SF4 (a), 028-15 A": 2026.6's format is the
  first stable one and refuses 2026.5's (026-12, SF4 (a)); a start refuses
  an older stream, no fallback (028-15, A).
* **W6, 026-22: MT against the contract** (agent mt, Opus high, 90
  minutes): do MT's in-between states meet the contract; does a read
  theorem need a live key under every index node; MT's entry-level
  take-back; what of the writer proof carries over; a format change?
* **W7, 026-23: a second opinion** (agent fb, Fable high, 90 minutes):
  open-ended proposals for a simpler, provable writer at similar
  performance, written before reading the designs so far, then compared
  with them. Frans, 11:33: "Would it make sense to ask Fable for an
  opinion on possible directions to simplify the writer? [...] open-ended
  proposals for simplifications are welcome. A Fable High agent for this.
  Just a short question, not a full study."
* **W8, 026-24: the PE trial** (agent pe, Opus xhigh, until 2026-11-19,
  07:00): 026-23's "plan, then emit" in the Lean model: a paper check,
  `plan` run on the traces as the go/no-go (refused at one contract or
  shape fault, bytes above 1.02 times, or a one-operation transaction
  unlike today's), then a proof spike of the lemmas of emit and settle.
  Frans, 12:47: "The PE trial. Yes, do it as recommended. Good if done by
  07:00 tomorrow. If possible."
* **W9, 030-20: the commit check's cost** (agent cc, Opus high, on s1,
  until 23:30 at the latest): `TransCheck` on against off in the
  performance suites, small and large transactions, a profile of one
  commit. Frans, 13:48: "Sure, start it."
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
* 10:25 Frans asked what else 2026.6 holds and whether the startup
  distance had moved (it had not; 028-15 waited for SF4).
* 10:50 Frans: "SF4 (a), 028-15 A". Agent sd (028-15) started 10:51.
* 10:52 Frans on 026-08 (the node size fixed at 30), done on a branch of
  2026-11-13, before the history was rewritten: "As recommended": Q1
  (`maxNodeSize30()` out of the API) and Q2 (`TestNodeSize` public,
  internal by its Javadoc) as applied; ported onto main after 028-15.
* 10:55 026-21 done (agent st, 08:57 to 10:55): (b), step times with the
  delete cut into pieces, recommended; landed 7552fab9 (the item and its
  evidence; lean/study/ stays on the branch `026-21-study`).
* 11:23 to 11:46 Discussion with Frans on 026-21 and other ways to avoid
  the take-back. Frans, 11:23: "The first thought while reading it is
  that it is not worth it. The performance degradation from today
  limited by significant. A potentially smaller proof; that is a benefit. But the
  real gain would be to actually get a complete proof."
* 11:51 Frans: "Let's forget about stable format for the stream. I
  decide to not focus on this for this release. The focus for the
  release are the algorithsm, simplifying them, proving them. If
  possible." SF4 open again; 028-15 and its option A stand. Agents mt
  (026-22) and fb (026-23) started 11:53, due 13:20.
* 12:11 026-23 done (agent fb, 18 minutes): four proposals, PE (plan
  then emit: each node decided once, in its parent's frame; 006-28's NW,
  never tried) first, then GS (MT with ghosts), CC (a commit check), FR
  (fewer kinds of things in a node); recommends PE, model first, two
  days, with refusal criteria. Landed (fast-forward).
* 12:37 026-22 done (agent mt): MT's in-between states fail the contract
  only through empty leaves (NonEmptyOK, which the scan's proof uses);
  every group's end meets it; no node taken back; the puts and the
  keeping leaf delete of the writer proof carry over; MT changes the
  record's meaning. Landed 31f8f08d (the item; lean/mtcheck/ stays on the
  branch).
* 12:37 028-15 done (agent sd): the startup distance in the internal KV
  `/#i/-startup-distance`, meta version 155, 2026.5's streams refused,
  `/#i/-dummy` gone; BEFORE COMMIT OK, LEVEL 1 to 4 OK; LANDED 1b1001ee.
  Four choices of the agent for Frans to confirm (028-15).
* 12:39 Agent ns started: 026-08 ported onto main (Frans, 10:52).
* 12:39 Frans on the suggestions of 12:32: "1 and 2 as recommended. 3.
  Not sure, will decide later. They may go into 2026.6 still. But must be
  done after algos settle." `night.sh` started on 1b1001ee (run
  2026-11-18-1239); 026-01 (compact nodes) and the versioning rule wait
  until the algorithms settle.
* 12:40 026-08 done (agent ns): its code has been on main since
  2026-11-13 (e277a18a); its item still said "to land". Frans's answers
  and a State note landed, f2d034e1.
* 12:43 `night.sh`'s Core-alone step failed: CoreDemo's scan of all keys
  now also returns 028-15's internal key. 12:45 Frans: "028-15, 1-4 are
  fine as recommended. But "/#i/-startup-distance" is unnecessarily long.
  I think "/#i/-sd" is better. Fits in one klong." Agent sd resumed 12:46:
  the key renamed `/#i/-sd`, CoreDemo reads only its own keys.
* 12:47 Frans: the PE trial (above). Agent pe (026-24) started 12:48.
* 12:51 Frans: "Raise the limit to 85 %. Use "/#i/-sd"." (The key takes
  two klongs, against four before; "/#i/-s" would take one.)
* 13:12 The aim of the proofs, after a discussion of what is not proved
  (the writer, reclaim's cut, and what stays tested or out of the
  model). Frans: ""the core algorithms are proved". Yes, this is the
  result to aim for. This is how far we would wish to go. If maintenable
  at a reasonable cost, this would be great. That is a valuable
  garantee." Written into 030's aim.
* 13:12 The key `/#i/-sd` and CoreDemo's fix done (agent sd): BEFORE
  COMMIT OK, CORE BUILD OK, LEVEL 1 and 2 OK; LANDED 026c322a. The key
  takes two klongs (four before).
* 13:42 Frans on CC (026-23, section 1.4): "I would like a note about
  it. [...] Just wonder about the performance cost of that. Could be too
  high, I am afraid." 030-20 written: what CC gives, what exists, what it
  would take, the cost to measure.
* 13:48 Frans: "Sure, start it. Work unattended until 07:00. I may or
  may not check in before that." Agent cc (030-20's cost) started.
* 14:33 026-24 done (agent pe, 12:50 to 14:33): go. PE in the model: no
  fault of the contract or the writer's rules on 288 traces; bytes 0.96
  to 0.99 of today's writer; the lemmas of emit and settle proved, 1,086
  lines; a complete PE writer proof estimated at 6,500 to 9,500 lines.
  One check of 026-23 fails by its letter: 6.8 % of one-operation
  transactions differ from today's change (the order of a full node's
  split). Landed aefde32e (the item; lean/pe/ and lean/peproof/ stay on
  the branch). For Frans: PE as 2026.6's writer.
* 15:28 `night.sh`: the kill-and-restart harness failed (seed 20261118,
  database 14: "a committed transaction lost, or one there that was not
  committed by then"); it passed on 2026-11-16. 028-15, landed today, is
  a suspect. Agent kr (028-17) started 15:29: reproduce, bisect, cause,
  fix.
* 16:07 028-17 done (agent kr): a real bug from 028-15, no synced
  transaction lost: since 028-15 a new Pub database's creation was not
  durable when start() returned (its second record, the startup
  distance's, waited in the write buffer); a kill then let the next start
  write that record at a later time, and the creator's startup distance
  was lost. Fix: the creating start syncs that record too (one more sync
  a creation); a unit test fails without it. BEFORE COMMIT OK, KILL
  RESTART OK (three seeds), LEVEL 1 and 2 OK; LANDED 32e72560.
* 16:08 `night.sh` ended: NIGHT FAILED: core-build, kill-restart (191
  minutes); both fixed on main since (026c322a, 32e72560); every other
  step OK.
* 16:56 030-20's cost measured (agent cc, on s1): with `TransCheck` an
  in-memory commit is 3.5 to 6 times slower (the check 74 to 84 % of a
  commit), small and large transactions alike; durable commits (with a
  sync) hardly see it. Too costly to have always on as written; a check
  designed for speed is estimated, not measured, at 1.5 to 2 times.
  Landed 52396e84.
* 21:37 Frans: "Document this work in a todo item. Start it now. One
  startup transaction." (21:30: "Either we have a fully initialized
  database or not.") 028-18 registered (5e278bdd); agent one started
  21:38, until 06:15 at the latest.
* 21:42 Frans on PE: "Go! Good luck with the proof. If you successfully
  prove it, feel free to do the Java implementation too. Opus high for
  that." Agent pw (030-21: the complete proof that the PE writer meets
  the contract, one segment first; Opus xhigh) started 21:43. If it is
  complete and gated, the Java implementation follows (Opus high).
* 23:10 028-18 stopped at the rule on pinned statements: a creation in
  one record breaks a pinned statement either way (the contract's start
  is the empty tree; the model's startup position comes before its
  record). Options A, B and C for Frans in 028-18; the Java part made and
  gated, but for the contract, on the branch `028-18-prepared`. Findings
  landed f0c30dfe.
* 02:08 (19 November) 030-21 done (agent pw, 21:43 to 02:08, with its
  sub-provers): the complete proof that PE's writer meets the writer's
  contract, TREE and the top: every history PE writes from the empty
  tree meets `MeetsTop` (`Contract.PE.pe_meetsTop_start`), so every get
  and scan at every time is right; 15,003 lines, the standard axioms
  only, GATE OK, no existing statement changed. LANDED b15f4b1b. Left:
  `MeetsFull` for PE (recovery, restarts, eviction, cuts), PE's
  acceptance (tested), Java.
* 02:10 Agent pw resumed for `MeetsFull` for PE, then acceptance; agent
  pej started: Java's writer as PE (026-25, Opus high; Frans, 21:42).
* 04:13 030-21 part 2 (agent pw): `MeetsFull` for PE proved but for one
  named premise, `Prov` (an old node a written node names was a live
  child before; it holds on all 221,142 traced transactions; a sub-prover
  is on it); with it, recovery, restarts, lazy reading, eviction and safe
  cuts hold for PE (`pe_full_of_prov`). Premises besides: distinct keys a
  transaction, fewer than 2^48 - 1 transactions. GATE OK, no statement
  changed; LANDED d035643c.
* 04:42 `Prov` proved (a sub-prover of agent pw): `MeetsFull` for PE with
  no premise of provenance: `pe_full` (every history PE writes from the
  empty tree meets `MeetsFull` and K-LEVEL) and `pe_crash_reads`; so
  recovery, restarts, lazy reading, eviction with handles and reclaim's
  safe cuts hold for PE. Premises: `Cfg.Ok`, the top's level at most
  2^62, fewer than 2^48 - 1 transactions, each transaction's keys
  distinct. GATE OK (137 theorems), no existing statement changed;
  LANDED ca51029f. Left: PE's acceptance (tested), Java (026-25, under
  way).


## 4b. Unattended, 13:48 to 07:00

What runs while Frans is away:

* `night.sh` on 1b1001ee, to about 15:45; its report goes to `news.md`.
* The PE trial (026-24, agent pe) to 07:00: the go/no-go of its model
  phase, then the proof spike.
* The commit check's cost (030-20, agent cc) on s1, to 23:30 at the
  latest.
* The coordinator: a check-in every 20 minutes (no quiet block: no timing
  on F53 tonight), lands gated work, writes `news.md` on failures; from
  06:00 the morning summary.

Decided by rule, without asking (Frans's defaults of 013-01 and today's):
the stop at week 85 %; gated work lands on main and is pushed; no new
proof or design work is started beyond the PE trial (reclaim's contract
waits for the morning); a no-go of the PE trial ends it with its result.
Changed by Frans's word in the evening: 028-18 (21:37) and the complete
PE proof, then Java if it is proved (21:42).


## 5. Outcome

Not yet.
