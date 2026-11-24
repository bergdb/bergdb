# 026-14. The Lean model's scope: three additions

Created 2026-11-13 by Frans Lundberg. Status: open: proposed for 2026.6,
not decided by its release; 030's map lists the model's scope as open,
not started (030, D5).

What the Lean model covers, where its boundary should be, and three
additions proposed for release 2026.6, in order of value.

Frans, 2026-11-13, 11:54: "What is your opinion about the coverage, the
scope of the model. Is the scope right? I mean, we don't want to model
the JVM. We need the right boundaries. The right scope. Are we there now?
Should something be added? Removed? Not now, of course..." And 12:11:
"Please add this to a new item in 026. The three things you propose to
add to the scope of the model. This is something I will consider for
this release. It depends on the result of the current Lean work, of
course. We will see. This is prio now as all major algorithms are
stabilizing."


## 1. The boundary as it is

The model covers the Core's logic that decides what is stored, what a
read returns and when something may be cut away: one writer, one step
at a time, down to the stream's records.

* **Below the line**, as assumptions, tested rather than proven: the
  storage (appends, syncs, files, power loss), threads and locks, the
  Java runtime.
* **Above the line**, as a client: the Pub layer, except where it has a
  protocol with its own state, as the user indexes (020-29, the library
  `BergDB`).

What the model would guarantee once its stated theorems are proven, and
what it would not (the coordinator's summary to Frans, 11:48): the data
is right at every supported lookup time (TP7, TP10, TP11), a crash loses
nothing synced and a restart reads the same database, lazy reading and
eviction change no read, reclaim's cuts never remove live data
(T-COVER, T-LATEST), startup and a transaction's record are bounded (T3,
T4, `ReleaseFits`), merges' costs are bounded (TP32, TP33), and the user
indexes stay consistent. Not covered: that the Java code is right (tied
to the model by conformance on traced runs, not by proof), threads,
storage's own behaviour, that the statements say what is meant (the
trusted definitions are read and reviewed), performance beyond the
bounds, and the Pub layer's object format.


## 2. Three additions, in order of value

1. **Reclaim as a whole.** Today the cut's safety is proven (T-COVER,
   T-LATEST), not the iteration around it: the steps, the end key E
   (026-05), and that the stream kept comes back down, aim 3 of 2026.5
   ("storage is proportional"; 024-04). Reclaim produced the most faults
   of the autumn (fault 12, fault 13, CA3, the back-to-empty lag that
   P8 fixed), and its rules are now stable and written exactly in
   027-13. Statements to aim at: a step keeps the cut's premises
   (REWRITES, LIVEBELOW); an iteration ends; after the writes stop, the
   stream kept falls to within a bound of the live data in a bounded
   number of steps (the lag G4 gates, 026-11).
2. **The stream format as bytes**, with 2026.6's stable format (026-12).
   Today the model starts above the bytes; only the klongs' encoding
   round trip is proven (TP1). For a stable format and a second
   implementation (the C clone, 022), the encoding of records, nodes and
   the meta block with "decode (encode x) = x", and the reader's rule of
   SF5 (know or refuse: reserved bytes zero, unknown kinds refused), make
   027-03 checkable. Moderate size; its time is when the format is made
   stable.
3. **The commit's conflict check.** That committed transactions behave as
   if run one after another (serializability), from each transaction's
   lookup time and the keys it read and wrote, and the set of recent
   writes (`KeyModSet`; changed today by 026-10: a cut forgets the writes
   before its time, and a commit older than the cut is rerun). An
   algorithm, not a matter of threads, so it fits the single-step model.
   Medium value; best when transactions are next changed.


## 3. What to make explicit instead of modelling

**The assumption list**: one short list of what the proofs assume about
storage (a synced append is durable; a crash leaves at most a torn tail),
about the runtime, and about the single writer. Today these are spread
over items. Its place: 027-17 (the model and its checks), so that the
boundary is visible and a reviewer can check it.


## 4. What stays out

* Threads and locks in Lean. Where interleavings matter, a small TLA+
  model checked by TLC within small bounds (as 020-26 for the indexes)
  and jcstress give most of the value at a fraction of the cost.
* The Pub layer's object format: frozen and tested (020-07, 020-09).
* Performance beyond the proven bounds: measurements and gates.


## 5. What to remove

Nothing large. Parts of the model (about 52,000 lines) may describe
mechanisms that have since changed; prune them as each part of 027 is
written and read closely, and consider a size-reduction pass later.


## 6. Depends on

The current proof work (024-12, its provers' board): TP7, `LatestGetOK`
and `LatestScanOK` (reduced today to `OpGetOK` and `CommitGetOK`),
TP32 and TP33. Frans decides which additions 2026.6 takes when that work
has shown how far it goes.


Log
---

2026-11-13. Created (Frans, 12:11), from the coordinator's answer of
11:54 on the model's scope.

2026-11-24. Status set after the release (lead-1124).
