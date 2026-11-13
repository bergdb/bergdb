/-
P's key nodes start before the next transaction (bergdb 024-12, TP7; the
take-back's `BaseStartOK`): every key node of a run within reach has a history
(`KeyNonempty`, in `RunLinksOK`), so its klongs start with a time klong of an
entry, and every entry of the run is of its time or before (`treeRun_timesLE`).
-/
import SIS.Tree.TakeBackRunJ
import SIS.Tree.KeyHistRun
import SIS.Tree.GetLatest
import SIS.Tree.CacheGood

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- A history's klongs start with a time klong. -/
theorem klongsOf_head_time (es : History BVal) (h : es ≠ []) :
    ∃ t r, klongsOf es = .time t :: r := by
  cases es with
  | nil => exact (h rfl).elim
  | cons e es =>
    rw [klongsOf_eq_parse]
    unfold parseKlongEntries
    simp only [List.foldl_cons]
    obtain ⟨t, r, h1⟩ := parseKlongEntry_head ([], none, []) e (Or.inl ⟨rfl, rfl⟩)
    have hf : ∀ (qs : History BVal) (acc : KlongParseState), (∃ t r, acc.1 = .time t :: r) →
        ∃ t r, (qs.foldl parseKlongEntry acc).1 = .time t :: r := by
      intro qs
      induction qs with
      | nil => intro acc h; exact h
      | cons e qs ih => intro acc h; exact ih _ (parseKlongEntry_head acc e (Or.inr h))
    exact hf es _ ⟨t, r, h1⟩

/-- `BaseStartOK` for any run predicate that holds the runs' links (TP4 with the
histories). -/
theorem baseStartOK_of (p : Params) (R : Struct BVal → Time → Prop)
    (hR : ∀ P t, R P t → RunLinksOK p P t) : BaseStartOK p R := by
  intro ts tx _ hr q qn hq
  have hN := (hR _ _ hr).2.2
  unfold knodeOf viewOf at hq
  cases hg : (treeRun p ts).get? q with
  | none => rw [hg] at hq; cases hq
  | some nd =>
    rw [hg] at hq
    simp only at hq
    split at hq
    · cases hq
    · rename_i hc
      simp only [Option.some.injEq] at hq
      subst hq
      have hd : nd.isData = false := by
        cases h : nd.isData with
        | false => rfl
        | true => simp [h] at hc
      have hl : nd.level ≤ p.keyMax := by
        rcases Nat.lt_or_ge p.keyMax nd.level with h | h
        · simp [h] at hc
        · exact h
      obtain ⟨t0, r, hks⟩ := klongsOf_head_time nd.hist (hN q nd hg hd hl)
      have ht0 : t0 ≤ ts.length :=
        klongsOf_times nd.hist ts.length
          (fun e he => treeRun_timesLE p ts (q, nd) (mem_of_get? hg) e he) (.time t0)
          (by rw [hks]; exact List.mem_cons_self) t0 rfl
      refine ⟨t0, by omega, ?_⟩
      simp only [KNode.firstTime, hks, List.findSome?_cons]

/-- `BaseStartOK` for `RunTreeQ`. -/
theorem baseStartOK_runTreeQ (p : Params) (Q : Struct BVal → Time → Prop) :
    BaseStartOK p (RunTreeQ p Q) :=
  baseStartOK_of p _ (fun _ _ h => h.1)

end SIS.Tree
