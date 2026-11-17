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
* 11:17 The freeze: tag proofs-2026-11-17 on 89c6cc3a, pushed. Agents w04 (030-04, Fable high) and wip (Lean labelled work in progress, Opus high) started 11:16.
* 11:18 W2 done: lean/README.md labelled work in progress (bdeca766); the users' README on 029-public-files without Lean or proofs (6e136f82, not pushed). The release notes of 2026.1 to 2026.5 still speak of the proved Lean model: Frans's call.
* 11:21 2026.5's release notes: the Lean model no longer a feature (Frans, 11:20): ba10b652.
* 11:25 W3, Apache-2.0 everywhere (Frans, 11:23: "Change everything to that, including all releases. [...] Change in place as if not other license was ever used. History in items and so on can be kept as is."): agent apache, Opus at high.
* 11:25 W1 done: 030-04 written (440 lines) and 030's map (D0 the contract approach, D1 paused); committed. Waits for Frans: when the spike runs.
* 11:31 W3 done: Apache-2.0 everywhere, the releases' src zips and SHA256SUMS included, NOTICE, the jars ship LICENSE and NOTICE (66db6126; BEFORE COMMIT OK). The drafts branch: a8e8a94e. The public history's old LICENSE: a filter rule described, for Frans.
* 11:31 W4, the spike of 030-04 (Frans, 11:30: "Run it now. Use Fable High for this. We need high intelligence for this."): agent spike, clone /Users/f/fl/bench/2026-11-17/spike/clone, branch 030-04-spike; STOP at a week of 30 % (a watcher).
