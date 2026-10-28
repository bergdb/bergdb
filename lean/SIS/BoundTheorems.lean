/-
Self-indexed streams in Lean: bounds, part 1, the theorem T3 (bergdb item 007;
docs/sis-model.md, section 10).

Trusted part: the statements. The proofs are in SIS/Proof/Bound.lean and,
for BergDB's take, SIS/Proof/BoundTake.lean; the proofs here only connect them.
Added 2026-10-23; T3 for BergDB's take added 2026-10-28 (bergdb 007-08).
-/
import SIS.Proof.BoundTake

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! In all five, `size` is any cost of a record (for BergDB's startup distance,
its bytes in the stream), d > 0 is the startup distance, and the run's startup
pos policy keeps up with d (`KeepsUp`: it never asks for a startup pos before
the one that d asks for, `sdTarget`; `sdPolicy` does, by `sdPolicy_keepsUp`).
Nothing else is assumed: not A1 to A5, nor anything of the structure, the
transactions or the still-dirty test. So the bounds hold whatever the size of
P, and however long the run. The last record of a run is R(k), and s = s(k)
is its startup pos. -/

/-- T3, the startup section is bounded. After every run, the startup section
without its last record, R(s+1), ..., R(k-1), costs less than d. -/
theorem T3_section (sp : Spec V T) (al : Algo V T) (size : Record V T → Nat) (d : Nat)
    (hd : 0 < d) (hk : KeepsUp size d al) (ts : List T) :
    let S := (run sp al ts).S
    S.cost size (lastSp S + 1) (S.length - 1) < d :=
  section_run sp al size d hd hk ts

/-- T3 with restarts. The same holds for a run with restarts (crashes and
startups) after any transactions (`runRestarts`), with nothing more assumed:
a startup keeps the stream. -/
theorem T3_restarts (sp : Spec V T) (al : Algo V T) (size : Record V T → Nat) (d : Nat)
    (hd : 0 < d) (hk : KeepsUp size d al) (ts : List (T × Bool)) :
    let S := (runRestarts sp al ts).S
    S.cost size (lastSp S + 1) (S.length - 1) < d :=
  section_runRestarts sp al size d hd hk ts

/-- T3, what startup reads. Startup reads R(s), ..., R(k) (6.2). They cost less
than d plus the costs of the two records at their ends, R(s) and R(k). -/
theorem T3_reads (sp : Spec V T) (al : Algo V T) (size : Record V T → Nat) (d : Nat)
    (hd : 0 < d) (hk : KeepsUp size d al) (ts : List T) :
    let S := (run sp al ts).S
    S.cost size (lastSp S) S.length <
      S.cost size (lastSp S) (lastSp S + 1) + d + S.cost size (S.length - 1) S.length :=
  reads_of_section size _ (section_run sp al size d hd hk ts) (lastSp_lt_run sp al ts)

/-- T3, what startup reruns: the transactions T(s+1), ..., T(k) (6.2, step 6,
`sectionIdx`). If every record costs at least m, there are fewer than d / m + 1
of them, (k - s - 1) m < d; and their records, R(s+1), ..., R(k), cost less
than d plus the cost of R(k). -/
theorem T3_rerun (sp : Spec V T) (al : Algo V T) (size : Record V T → Nat) (d m : Nat)
    (hd : 0 < d) (hk : KeepsUp size d al) (ts : List T)
    (hm : ∀ R ∈ (run sp al ts).S, m ≤ size R) :
    let S := (run sp al ts).S
    ((sectionIdx S (lastSp S)).length - 1) * m < d ∧
      S.cost size (lastSp S + 1) S.length < d + S.cost size (S.length - 1) S.length :=
  rerun_of_section size _ (section_run sp al size d hd hk ts) hm

/-- T3 with records of bounded cost: if every record costs at most M, startup
reads R(s), ..., R(k) for less than d + 2 M, and reruns transactions whose
records cost less than d + M. -/
theorem T3_bounded (sp : Spec V T) (al : Algo V T) (size : Record V T → Nat) (d M : Nat)
    (hd : 0 < d) (hk : KeepsUp size d al) (ts : List T)
    (hM : ∀ R ∈ (run sp al ts).S, size R ≤ M) :
    let S := (run sp al ts).S
    S.cost size (lastSp S) S.length < d + 2 * M ∧
      S.cost size (lastSp S + 1) S.length < d + M :=
  bounded_of_section size _ (section_run sp al size d hd hk ts) (lastSp_lt_run sp al ts) hM

/-! ## T3 for BergDB's take (bergdb 007-08)

In the six below, the run's startup pos policy is BergDB's take,
`takePolicy size sd pace` (SIS/Bound.lean), with any pace, so in particular
with BergDB's own share, `javaTake size own sd`; `size` is any cost of a
record (for BergDB, its bytes in the stream), and sd i is the startup
distance's setting in transaction i. The transactions of a run ts are T(1),
..., T(k), k = ts.length, and after T(i) the stream is R(0), ..., R(i). For a
stream S, `S.span size` is the startup section without its last record,
R(s+1), ..., R(k-1), which T3 bounds: the span of the section's transactions
(`Stream.span`). As for T3, nothing else is assumed: not A1 to A5, nor
anything of the structure, the transactions, the pace or the still-dirty
test.

`KeepsUp size (2 * sd) al` does not hold for the take: on a stream whose span
is longer than 2 sd, which a decrease of the setting makes, its deadline is at
the span (SIS/BoundExample.lean has such a stream). So these are stated for
runs, from the section before each transaction. -/

/-- T3 for BergDB's take, one transaction: on any database, with a setting
sd i > 0 in transaction i, the startup section without its last record after
T(i) costs less than the larger of 2 sd i and that section before T(i), the
deadline's distance in T(i). -/
theorem T3_take_step (sp : Spec V T) (al : Algo V T) (size : Record V T → Nat)
    (sd : Time → Nat) (pace : Pace V T) (hp : al.policy = takePolicy size sd pace)
    (db : DB V T) (tr : T) (hsd : 0 < sd db.S.length) :
    (step sp al db tr).S.span size < max (2 * sd db.S.length) (db.S.span size) := by
  rcases take_step sp al size sd pace hp db tr with h | h
  · exact h
  · rw [h]; exact Nat.lt_of_lt_of_le (by omega) (Nat.le_max_left _ _)

/-- T3 for BergDB's take: if the setting is at most M > 0 in T(1), ..., T(k),
the startup section without its last record costs less than 2 M after T(k).
With a constant setting sd, less than d_h = 2 sd, 007-03's T3 for the take. -/
theorem T3_take (sp : Spec V T) (al : Algo V T) (size : Record V T → Nat) (sd : Time → Nat)
    (pace : Pace V T) (hp : al.policy = takePolicy size sd pace) (M : Nat) (hM0 : 0 < M)
    (ts : List T) (hM : ∀ i, 0 < i → i ≤ ts.length → sd i ≤ M) :
    (run sp al ts).S.span size < 2 * M := by
  unfold run
  refine fold_bound sp al size sd pace (step sp al) id (step_next sp al) hp hM0 ts (init sp)
    (by rw [init_span]; omega) (fun i h1 h2 => ?_)
  rw [init_length] at h1 h2
  exact hM i (by omega) (by omega)

/-- T3 for BergDB's take with restarts: the same for a run with restarts
after any transactions (`runRestarts`). -/
theorem T3_take_restarts (sp : Spec V T) (al : Algo V T) (size : Record V T → Nat)
    (sd : Time → Nat) (pace : Pace V T) (hp : al.policy = takePolicy size sd pace) (M : Nat)
    (hM0 : 0 < M) (ts : List (T × Bool)) (hM : ∀ i, 0 < i → i ≤ ts.length → sd i ≤ M) :
    (runRestarts sp al ts).S.span size < 2 * M := by
  rw [runRestarts_eq_fold]
  refine fold_bound sp al size sd pace (restartNext sp al) Prod.fst (restartNext_S sp al) hp
    hM0 ts (init sp) (by rw [init_span]; omega) (fun i h1 h2 => ?_)
  rw [init_length] at h1 h2
  exact hM i (by omega) (by omega)

/-- T3 for BergDB's take after a change of the setting (D4:B). Let the
setting be sd' > 0 in T(m+1), ..., T(m+n), where m = ts.length and n =
us.length (after a decrease, `Db.setStartupDistance`'s transaction is
T(m+1)). Then after T(m+n) the startup section without its last record costs
less than 2 sd', or at least n less than after T(m). So it never costs more
than after T(m), which T3_take bounds by twice the largest setting before; it
shrinks with every transaction while it costs 2 sd' or more; and it costs less
than 2 sd' after at most (its cost after T(m)) - 2 sd' + 1 transactions, and
from then on. -/
theorem T3_take_decrease (sp : Spec V T) (al : Algo V T) (size : Record V T → Nat)
    (sd : Time → Nat) (pace : Pace V T) (hp : al.policy = takePolicy size sd pace)
    (ts us : List T) (sd' : Nat) (hsd' : 0 < sd')
    (hset : ∀ i, ts.length < i → i ≤ ts.length + us.length → sd i = sd') :
    (run sp al (ts ++ us)).S.span size < 2 * sd' ∨
      (run sp al (ts ++ us)).S.span size + us.length ≤ (run sp al ts).S.span size := by
  have h : run sp al (ts ++ us) = us.foldl (step sp al) (run sp al ts) := by
    unfold run; rw [List.foldl_append]
  rw [h]
  exact fold_decrease sp al size sd pace (step sp al) id (step_next sp al) hp hsd' us _
    (fun i h1 h2 => by rw [run_length] at h1 h2; exact hset i (by omega) (by omega))

/-- T3 for BergDB's take after a change of the setting, with restarts after any
transactions: the same as `T3_take_decrease`. -/
theorem T3_take_decrease_restarts (sp : Spec V T) (al : Algo V T) (size : Record V T → Nat)
    (sd : Time → Nat) (pace : Pace V T) (hp : al.policy = takePolicy size sd pace)
    (ts us : List (T × Bool)) (sd' : Nat) (hsd' : 0 < sd')
    (hset : ∀ i, ts.length < i → i ≤ ts.length + us.length → sd i = sd') :
    (runRestarts sp al (ts ++ us)).S.span size < 2 * sd' ∨
      (runRestarts sp al (ts ++ us)).S.span size + us.length ≤
        (runRestarts sp al ts).S.span size := by
  have h : runRestarts sp al (ts ++ us) = us.foldl (restartNext sp al) (runRestarts sp al ts) := by
    rw [runRestarts_eq_fold, runRestarts_eq_fold, List.foldl_append]
  rw [h]
  exact fold_decrease sp al size sd pace (restartNext sp al) Prod.fst (restartNext_S sp al) hp
    hsd' us _
    (fun i h1 h2 => by rw [runRestarts_length] at h1 h2; exact hset i (by omega) (by omega))

/-- T3 for BergDB's take, what startup reruns (6.2, step 6): with settings at
most M > 0 in T(1), ..., T(k), the transactions T(s+1), ..., T(k), whose
records cost less than 2 M plus the cost of R(k); if every record costs at
least m, there are fewer than 2 M / m + 1 of them, (k - s - 1) m < 2 M. In
Java every record has at least 48 bytes (`TransSeq.ownBytes`). -/
theorem T3_take_rerun (sp : Spec V T) (al : Algo V T) (size : Record V T → Nat)
    (sd : Time → Nat) (pace : Pace V T) (hp : al.policy = takePolicy size sd pace) (M m : Nat)
    (hM0 : 0 < M) (ts : List T) (hM : ∀ i, 0 < i → i ≤ ts.length → sd i ≤ M)
    (hm : ∀ R ∈ (run sp al ts).S, m ≤ size R) :
    let S := (run sp al ts).S
    ((sectionIdx S (lastSp S)).length - 1) * m < 2 * M ∧
      S.cost size (lastSp S + 1) S.length < 2 * M + S.cost size (S.length - 1) S.length :=
  rerun_of_section size _ (T3_take sp al size sd pace hp M hM0 ts hM) hm

end SIS
