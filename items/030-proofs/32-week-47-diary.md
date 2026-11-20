# 030-32. The proof week, 16 to 20 November 2026: a diary

Created 2026-11-20 by Frans Lundberg. Status: done (a record).

The week the Lean work went from a large model, proved step by step and
close to being given up, to BergDB's core algorithms proved, given tested
assumptions (030-26). One heading a day, then the idea that made the
difference. The details are in the subitems cited.


## Monday 16 November: one home, a large model

* 030 was made the home of all proof work: one map of every direction,
  and the rules all proof work follows.
* The proof line of the time proved the writer step by step: each split,
  merge and root collapse of the old writer, against the model's
  invariants. In the evening, what a delete does to the tree's live
  counts was proved piece by piece (030-01), and the bridges from the
  model to Java were planned (030-02); two of the planned statements
  turned out to be false as stated.
* The size of it: on Tuesday morning, before the change of approach,
  `lean/` held 747 files and 279,136 lines of Lean, most of it the
  step-by-step proofs of the key tree, and the writer was still not
  proved.


## Tuesday 17 November: the turning point

* In the morning Frans was close to giving up and deleting the whole Lean
  model. Instead he tried another approach (030-04, decided 10:56 to
  11:14): the contract approach and a fresh start.
* **The contract:** one statement of what must hold when a transaction
  ends, the post-transaction contract. What a user relies on, every get
  and every scan at every time, is proved from the contract alone. That
  the writer meets the contract is tested after every transaction of
  Java, not proved.
* **12:56, the trial worked** (030-05): reads, scans and the invariants
  proved from the contract (`get_right`, `scan_right`, `inv_right`), on
  the standard axioms only, and the contract checked on Java's traces. It
  took about an hour and a half and 4,890 lines of Lean, 867 of them to
  read and trust.
* In the afternoon: the tree property and the top node added to the
  contract (030-08), the bridge from the model to Java (030-07), Java's
  own check of the contract at each commit in its tests (030-09), and two
  independent reviews; 030-11, at 17:49: sound, with fixes, and the large
  set's 17,000 transactions passing.
* **At 18:00 Frans celebrated with champagne:** a practical Lean model,
  relying on a contract that can be tested after every Java transaction.
  The work could have stopped there with a good model.


## Wednesday 18 November: further, because it could

* The old step-by-step proofs were tagged and deleted (030-18): `lean/`
  went from 878 files and 337,483 lines to 239 files and 84,556 lines.
* Frans set the aim at 13:12: the writer meets the contract, and reclaim
  chooses only safe cuts, given tested assumptions.
* PE, a simpler writer made to be proved (plan, then emit), was tried and
  found fit (026-24).
* **The night, 21:43 to 05:23: PE proved** (030-21). At 02:08, PE meets
  the whole contract for every history it writes, tree and top included;
  by 05:23 also the contract's full form (Prov), and PE accepts every
  valid transaction. The same night, PE was written in Java, node for
  node the proved writer (026-25).


## Thursday 19 November: reclaim proved, the aim reached

* Java's PE merged into main: the writer that ships is the proved one.
* Reclaim's contract written down as four conditions a trace can test,
  RC1 to RC4 (030-22); its theorem stated and half proved (030-23); the
  other half's invariant found by an independent search.
* **Afternoon: the aim reached.** For every history PE writes, Java's
  gets and scans are right after reclaim's cuts (030-24), and reclaim's
  iteration is proved from a model of its steps (030-25). 030-26 written,
  the public statement. Java's reclaim steps checked on every trace
  (030-27); the tested writer compared with the proved one every night
  (030-28, pecmp).


## Friday 20 November: keep it true, make the links stronger

* Frans decided: 030-26 stays true and up to date, at least until 2026.6;
  "tree" stays the main word, with the DAG explained.
* PE writes at most the nodes of Java's `dirtyNodeBound` for transactions
  of puts, and accepts every transaction Java gives it (030-29; deletes
  tested, not proved).
* The trace sets on new seeds every night, and Java's contract check in
  week.sh (030-30); the user apps' workloads and reclaim across 943
  restarts and 167 crashes against the model (030-31).
* `lean/` at the end of the week: 313 files, 123,952 lines, with the
  writer and reclaim proved.


## The idea: a contract tested after every operation

The approach of Tuesday, for use elsewhere:

1. **State a contract** on the state after each operation of the
   implementation: here, what the stored tree must be after each
   transaction. Not how the implementation gets there.
2. **Prove what users rely on from the contract alone**: here, every get
   and scan. These proofs are small, and they do not change when the
   implementation does.
3. **Check the contract on the real implementation after every
   operation**: in its tests (a commit-time check) and on recorded traces
   (a checker built from the same Lean statement). A violation is caught
   where it happens, with the operation that caused it.
4. **Optionally, prove an implementation meets the contract**, when it is
   simple enough; here PE, two days later. The rest of the proof stays as
   it is.

Why it worked: the proof no longer follows every step of the
implementation, so it is small and stable; the gap between model and code
is closed by a test that runs all the time, not by trust; and a simpler
or faster implementation can replace the old one as long as it meets the
same contract.
