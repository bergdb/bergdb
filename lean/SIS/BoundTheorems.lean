/-
Self-indexed streams in Lean: bounds, part 1, the theorem T3 (bergdb item 007;
docs/sis-model.md, section 10).

Trusted part: the statements. The proofs are in SIS/Proof/Bound.lean; the
proofs here only connect them. Added 2026-10-23.
-/
import SIS.Proof.Bound

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

end SIS
