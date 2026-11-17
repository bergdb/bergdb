# 006-30 Day work, 17 November 2026

Created 2026-11-17 by Frans Lundberg. Status: open. The plan for the
coordinator's day of 2026-11-17 (coord-1117), a Tuesday: the progress
and the outcome. The way of working is 013-02's (the coordinator).


## 1. The request

coord-1116's handover (006-29, section 6): the night's outcome and eight
decisions. Week 20 % at 07:55, level plenty. Today Frans makes the public
release (029).

Frans's words:

* 09:13: "I am considering pausing the proof work. This is too much work
  from my side and too much token cost. Cost is too high for uncertain
  progress. I am about to make a public release of BergDB. [...] I want
  to be able to restart it in 12 months or so."
* 10:56, on the contract approach (030-04): "It is 80-20. 80 percent of
  the value, 20 percent of the work. It is very practical. Being able to
  test each transaction in isolation is very strong. [...] I like this!"
* 11:00: a restart of the whole proof work, from scratch, is to be
  considered ("I think we might be stuck in too much dependence on
  history").
* 11:14: "Let's get started as proposed. Write it down. Use an agent,
  Fable at High." Mathlib: "I delegate the decision to you." The spike's
  time: "Will be decided after this is written down." Lean in the
  release: "Keep the Lean, but ensure it is labelled as work in progress.
  Avoid mentioning it in main documentation for the user of BergDB. [...]
  Do not "brag" about it as a feaure or benefit. Should not be mentioned
  in the end user documentation."


## 2. The ground rules

* Usage plenty: up to six agents at a time.
* The proofs' main line (030, D1) is paused: no `l4` nights.


## 3. The work

* **W1, 030-04: the contract approach and a fresh start** (agent w04,
  Fable at high; Frans, 11:14): writes 030-04 and the 030 map in the main
  tree; the coordinator commits.
* **W2, Lean in the release** (agent wip, Opus at high; Frans, 11:14):
  `lean/README.md` labelled work in progress; Lean out of the users'
  README on the drafts' branch 029-public-files.


## 4. Progress

* 07:55 Started; coord-1116 closed 07:55.
* 08:04 The branch 026-19-proof-trial pushed (006-29, decision 7: keep).
* 09:13 to 11:14 Discussion with Frans: pausing the proofs; the contract
  approach; a fresh start (030-04).
* 11:16 Mathlib (Frans delegated it): yes, in the new proofs' own Lake
  package, so that `lean/`'s build and the level scripts are untouched
  (030-04 gives the reasons).
* 11:17 The freeze: tag proofs-2026-11-17 on f4d73289, pushed. Agents w04 (030-04, Fable high) and wip (Lean labelled work in progress, Opus high) started 11:16.
* 11:18 W2 done: lean/README.md labelled work in progress (050f6d93); the users' README on 029-public-files without Lean or proofs (c2266d8a, not pushed). The release notes of 2026.1 to 2026.5 still speak of the proved Lean model: Frans's call.
* 11:21 2026.5's release notes: the Lean model no longer a feature (Frans, 11:20): 67fb3327.
* 11:25 W3, Apache-2.0 everywhere (Frans, 11:23: "Change everything to that, including all releases. [...] Change in place as if not other license was ever used. History in items and so on can be kept as is."): agent apache, Opus at high.
* 11:25 W1 done: 030-04 written (440 lines) and 030's map (D0 the contract approach, D1 paused); committed. Waits for Frans: when the spike runs.
* 11:31 W3 done: Apache-2.0 everywhere, the releases' src zips and SHA256SUMS included, NOTICE, the jars ship LICENSE and NOTICE (21690937; BEFORE COMMIT OK). The drafts branch: 3c1b91be. The public history's old LICENSE: a filter rule described, for Frans.
* 11:31 W4, the spike of 030-04 (Frans, 11:30: "Run it now. Use Fable High for this. We need high intelligence for this."): agent spike, clone /Users/f/fl/bench/2026-11-17/spike/clone, branch 030-04-spike; STOP at a week of 30 % (a watcher).
* 11:42 W5, the public release (029): Frans's answers on the release checklist (11:40) and on the licence of the history ("Historically, the 2013 era using AGPL, this should stay. Everything 2026 should be Apache license."). Agents pre (the commits before the switch, clone /Users/f/fl/bench/2026-11-17/pre/clone) and pbuild (the public build's rules and a test run), Opus at high.
* 11:46 Frans 11:45: 12 and 13 as recommended (private reporting only, a week, crash on a crafted file = ordinary bug; the name paragraph in). Sent to pre.
* 11:48 W5: the pre-switch commits landed (ff to 7c06b28e, BEFORE COMMIT OK 62 s): drafts merged, 013-03 rewritten, bergdb.org, release binaries to GitHub Releases (026's readme, next.md), AGENTS.md, android.sh, night.sh, F1 note, local paths.
* 11:51 W6, the website bergdb.org (Frans, 11:47 and 11:50): agent site, Fable at high, a local draft in /Users/f/fl/bench/2026-11-17/site/bergdb.github.io; published after the switch.
* 11:55 W6: the site's draft done (local commit 039c947 in /Users/f/fl/bench/2026-11-17/site/bergdb.github.io): one page, a 404 page, CNAME, README; no scripts, no external resources.
* 11:58 bergdb.org verified for the bergdb organisation on GitHub (Frans); the TXT record by session sk26 (Hostup MCP). W5: the public build's rules for 11:40's decisions; a run on main 49af99ba passed every check (14), public main 5b5f719e.
* 12:07 Frans 12:06: staging. Private repo bergdb/bergdb-staging made; pushed public build 5b5f719e (main, map-cache-1707, 15 tags). Delete after the switch.
* 12:56 W4 done: the spike succeeded (030-05): every get and scan proved right, at every time, for any history that meets the writer's contract (4,890 lines of Lean, Lean's three standard axioms only); the contract and Java's gets and scans hold on 180 traces of the level 2 sets (21,000 transactions); the fill rule is not needed for reads. About 1.5 hours, about 4 % of the week. Merged 50cb1628. Step 4 after the switch.
* 14:18 W5 done: BergDB is public (Frans, 14:17: "go"): github.com/bergdb/bergdb, a new repository with the cleaned history from 2013; five releases with jars and Javadoc; the site https://bergdb.org (HTTPS); the old private repository archived. A privacy scan of every version found a phone number and old login names; both removed from every version before the switch.
* 14:47 W7, the contract's review (030-06; Frans, 14:47): agent review, Opus at xhigh. W8, the release's follow-ups (Frans, 14:48): agent followups, Opus at high.


## 5. Unattended, 17 November 14:51 to 18 November 07:00

Frans, 14:51: "I would like to finish my work for today. Until 07:00 in in the
morning, I want you to focus on the proofs in the new direction. Work unattended.
There should be little need for running all the testing (night.sh). Priority is the
new proofs."

The defaults below go ahead unless Frans says otherwise before he leaves.

* **The work, in order** (030-04, steps 3 and 4; 030-05's State note):
  1. W7, the review 030-06 (running). Its must-fix findings are fixed first, in
     `lean/contract/`, by the agent that fixes them (Fable at high).
  2. Step 4a: the bridge to the abstract model: the contract clauses that the
     abstract model assumes (`StepOK`, TREE, A6', A-COPY), and recovery, restarts,
     lazy reading, eviction and reclaim's cut from them by the existing proofs
     (Fable at high, as the spike; Frans 11:30: "We need high intelligence for
     this").
  3. Step 4b, beside 4a: the two simplifications 030-05 names: the top nodes and
     skip pointers in the contract's model of the top; the trace reader's step from
     trace lines to Java's tree (Opus at xhigh).
  4. Step 4c, beside: Java's check of the contract at each commit, in the tests
     (Opus at high; gated by `before-commit.sh`).
* **Landing:** only gated work: `lake build` of `lean/contract/` with no `sorry`,
  `admit`, `native_decide` or axiom of its own, `#print axioms` standard only, the
  contract check on the level 2 traces; for Java, BEFORE COMMIT OK. The coordinator
  lands on `main` and pushes. The repository is public: before each push, a check for
  private data (addresses, numbers, local paths beyond the scripts').
* **Not tonight:** `night.sh` (Frans: little need); deleting the old proofs (030-04,
  step 4's end: they go when the new package covers what they claimed, a decision
  for the morning).
* **Usage:** week 24 % at 14:51. All agents stop at 60 % of the week (a watcher
  makes their STOP files); at most six agents at a time (Frans, 15:06: "Work hard
  and unattended on this. Take it forward as far as possible. Do not stop to ask
  me, take decisions yourself on this so the work can continue. If needed you can
  use up to 60% of the AI usage").
* **15:10, the agents:** the review 030-06 is done (sound, with fixes; merged).
  Three agents from main fc183148: 030-07, the bridge to the abstract model (Fable
  at high); 030-08, the tree's shape and its top (Opus at xhigh); 030-09, the
  trace's completeness and Java's own check of the contract (Opus at high). Each
  reports its gated pieces in its item's Log; the coordinator lands them.
* **The morning:** the outcome in section 6 and a `news.md` summary by 06:30.
* 15:50 030-08 done and landed (2043fc00): the top in the contract, Java's top search proved right (TP24), Java's get and scan right at every time. Started 030-10, a spike: does the model's writer meet the contract (Fable at high; the coordinator's decision).
