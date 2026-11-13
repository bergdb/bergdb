/-
Proofs for `DropStepJ.kept` in 024-12's tree model of BergDB (bergdb item 007;
SIS/BoundColdDropJ.lean). Added 2026-11-13.

`blive` (SIS/Tree/Val.lean), the live children of a BergDB node, loses by an
appended entry at most `bvalW` of it: a key klong replaces the child of its
compare value (one), a delete bitmap the children of its compare values, a top
node's root pointer or the root's top node one. So a node that stays reachable
loses at most the weights of its entries (`blive_lost`).
-/
import SIS.BoundColdDropJ
import SIS.Proof.BoundColdDropJ
import SIS.Tree.Spec

set_option linter.unusedSectionVars false

namespace SIS

open SIS.Check

/-- The state of `blive`'s fold. -/
abbrev BSt := List (Nat × Option Nat) × Option Nat × Option Nat

/-- One step of `blive`'s fold. -/
def bstep (acc : BSt) (e : Entry BVal) : BSt :=
  match e.val with
  | .key c y => (setAssoc acc.1 c (some y), acc.2.1, acc.2.2)
  | .del cs =>
    (cs.foldl (fun m c => if m.any (fun p => p.1 == c) then setAssoc m c none else m) acc.1,
      acc.2.1, acc.2.2)
  | .rootKey y => (acc.1, some y, acc.2.2)
  | .top z => (acc.1, acc.2.1, some z)
  | _ => acc

/-- The live children of a state. -/
def bout (st : BSt) : List NodeId :=
  ((st.1.filterMap (·.2)) ++ st.2.1.toList ++ st.2.2.toList).eraseDups

theorem blive_eq (h : History BVal) : blive h = bout (h.foldl bstep ([], none, none)) := by
  unfold blive bout
  rfl

/-! ### The association list of a key node -/

theorem keys_setAssoc (m : List (Nat × Option Nat)) (c : Nat) (v : Option Nat) :
    (setAssoc m c v).map (·.1) =
      if m.any (fun p => p.1 == c) then m.map (·.1) else m.map (·.1) ++ [c] := by
  unfold setAssoc
  split
  · rename_i h
    simp only [List.map_map]
    apply List.map_congr_left
    intro p _
    simp only [Function.comp]
    split
    · rename_i hp; simpa using (beq_iff_eq.mp hp).symm
    · rfl
  · rename_i h
    simp

theorem nodup_keys_setAssoc {m : List (Nat × Option Nat)} (hnd : (m.map (·.1)).Nodup) (c : Nat)
    (v : Option Nat) : ((setAssoc m c v).map (·.1)).Nodup := by
  rw [keys_setAssoc]
  split
  · exact hnd
  · rename_i h
    rw [List.nodup_append]
    refine ⟨hnd, by simp, ?_⟩
    intro a ha b hb hab
    simp only [List.mem_singleton] at hb
    subst hb; subst hab
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
    apply h
    exact List.any_eq_true.mpr ⟨p, hp, by simp⟩

theorem mem_setAssoc_ne {m : List (Nat × Option Nat)} {c : Nat} {v : Option Nat}
    {p : Nat × Option Nat} (hp : p ∈ m) (hc : p.1 ≠ c) : p ∈ setAssoc m c v := by
  unfold setAssoc
  split
  · apply List.mem_map.mpr
    refine ⟨p, hp, ?_⟩
    have : (p.1 == c) = false := by simpa using hc
    simp [this]
  · exact List.mem_append_left _ hp

theorem delFold_keys (cs : List Nat) : ∀ (m : List (Nat × Option Nat)), (m.map (·.1)).Nodup →
    ((cs.foldl (fun m c => if m.any (fun p => p.1 == c) then setAssoc m c none else m) m).map
      (·.1)).Nodup := by
  induction cs with
  | nil => intro m h; exact h
  | cons c cs ih =>
    intro m h
    simp only [List.foldl_cons]
    apply ih
    split
    · exact nodup_keys_setAssoc h c none
    · exact h

theorem delFold_mem (cs : List Nat) : ∀ (m : List (Nat × Option Nat)) (p : Nat × Option Nat),
    p ∈ m → p.1 ∉ cs →
    p ∈ cs.foldl (fun m c => if m.any (fun p => p.1 == c) then setAssoc m c none else m) m := by
  induction cs with
  | nil => intro m p hp _; exact hp
  | cons c cs ih =>
    intro m p hp hc
    simp only [List.foldl_cons]
    apply ih _ p _ (fun h => hc (List.mem_cons_of_mem c h))
    split
    · exact mem_setAssoc_ne hp (fun h => hc (h ▸ List.mem_cons_self))
    · exact hp

theorem filter_key_le_one : ∀ (m : List (Nat × Option Nat)), (m.map (·.1)).Nodup → ∀ c : Nat,
    (m.filter (fun p => p.1 == c)).length ≤ 1 := by
  intro m
  induction m with
  | nil => intro _ c; simp
  | cons q m ih =>
    intro hnd c
    rw [List.map_cons, List.nodup_cons] at hnd
    by_cases hq : q.1 = c
    · have h0 : m.filter (fun p => p.1 == c) = [] := by
        rw [List.filter_eq_nil_iff]
        intro p hp
        have : p.1 ≠ q.1 := fun h => hnd.1 (h ▸ List.mem_map_of_mem hp)
        simp only [beq_iff_eq]
        rw [← hq]; exact this
      simp [hq, h0]
    · have : (q.1 == c) = false := by simpa using hq
      simp only [List.filter_cons, this]
      exact ih hnd.2 c

/-! ### What an entry kills -/

/-- The live children that entry value v may take away from state st. -/
def killed (st : BSt) (v : BVal) : List NodeId :=
  match v with
  | .key c _ => (st.1.filter (fun p => p.1 == c)).filterMap (·.2)
  | .del cs => cs.flatMap (fun c => (st.1.filter (fun p => p.1 == c)).filterMap (·.2))
  | .rootKey _ => st.2.1.toList
  | .top _ => st.2.2.toList
  | _ => []

theorem filterMap_len_le {l : List (Nat × Option Nat)} :
    (l.filterMap (·.2)).length ≤ l.length := List.length_filterMap_le _ _

theorem killed_len (st : BSt) (hnd : (st.1.map (·.1)).Nodup) (v : BVal) :
    (killed st v).length ≤ bvalW v := by
  cases v with
  | key c y =>
    simp only [killed, bvalW]
    exact Nat.le_trans filterMap_len_le (filter_key_le_one _ hnd c)
  | del cs =>
    simp only [killed, bvalW]
    rw [List.length_flatMap]
    have : ∀ c ∈ cs, ((st.1.filter (fun p => p.1 == c)).filterMap (·.2)).length ≤ 1 :=
      fun c _ => Nat.le_trans filterMap_len_le (filter_key_le_one _ hnd c)
    have h2 := sum_map_le cs (fun c => ((st.1.filter (fun p => p.1 == c)).filterMap (·.2)).length)
      (fun _ => 1) this
    rw [sum_map_const, Nat.mul_one] at h2
    exact h2
  | rootKey y =>
    simp only [killed, bvalW]
    cases st.2.1 <;> simp
  | top z =>
    simp only [killed, bvalW]
    cases st.2.2 <;> simp
  | skip a b => simp [killed, bvalW]
  | data a => simp [killed, bvalW]

theorem nodup_keys_bstep (st : BSt) (hnd : (st.1.map (·.1)).Nodup) (e : Entry BVal) :
    ((bstep st e).1.map (·.1)).Nodup := by
  unfold bstep
  split
  · exact nodup_keys_setAssoc hnd _ _
  · exact delFold_keys _ _ hnd
  · exact hnd
  · exact hnd
  · exact hnd

theorem mem_bout {st : BSt} {y : NodeId} :
    y ∈ bout st ↔ (∃ p ∈ st.1, p.2 = some y) ∨ st.2.1 = some y ∨ st.2.2 = some y := by
  unfold bout
  rw [List.mem_eraseDups]
  simp only [List.mem_append, List.mem_filterMap, Option.mem_toList]
  constructor
  · rintro ((⟨p, hp, h⟩ | h) | h)
    · exact Or.inl ⟨p, hp, h⟩
    · exact Or.inr (Or.inl (Option.mem_def.mp h))
    · exact Or.inr (Or.inr (Option.mem_def.mp h))
  · rintro (⟨p, hp, h⟩ | h | h)
    · exact Or.inl (Or.inl ⟨p, hp, h⟩)
    · exact Or.inl (Or.inr (Option.mem_def.mpr h))
    · exact Or.inr (Option.mem_def.mpr h)

theorem step_lost (st : BSt) (e : Entry BVal) {y : NodeId} (hy : y ∈ bout st)
    (hn : y ∉ bout (bstep st e)) : y ∈ killed st e.val := by
  rw [mem_bout] at hy
  rw [mem_bout] at hn
  unfold bstep at hn
  unfold killed
  split at hn
  · rename_i c y' hv
    simp only at hn
    rcases hy with ⟨p, hp, hpy⟩ | h | h
    · by_cases hpc : p.1 = c
      · exact List.mem_filterMap.mpr ⟨p, List.mem_filter.mpr ⟨hp, by simp [hpc]⟩, hpy⟩
      · exact absurd (Or.inl ⟨p, mem_setAssoc_ne hp hpc, hpy⟩) hn
    · exact absurd (Or.inr (Or.inl h)) hn
    · exact absurd (Or.inr (Or.inr h)) hn
  · rename_i cs hv
    simp only at hn
    rcases hy with ⟨p, hp, hpy⟩ | h | h
    · by_cases hpc : p.1 ∈ cs
      · exact List.mem_flatMap.mpr ⟨p.1, hpc,
          List.mem_filterMap.mpr ⟨p, List.mem_filter.mpr ⟨hp, by simp⟩, hpy⟩⟩
      · exact absurd (Or.inl ⟨p, delFold_mem cs _ p hp hpc, hpy⟩) hn
    · exact absurd (Or.inr (Or.inl h)) hn
    · exact absurd (Or.inr (Or.inr h)) hn
  · rename_i y' hv
    simp only at hn
    rcases hy with ⟨p, hp, hpy⟩ | h | h
    · exact absurd (Or.inl ⟨p, hp, hpy⟩) hn
    · simp [h]
    · exact absurd (Or.inr (Or.inr h)) hn
  · rename_i z hv
    simp only at hn
    rcases hy with ⟨p, hp, hpy⟩ | h | h
    · exact absurd (Or.inl ⟨p, hp, hpy⟩) hn
    · exact absurd (Or.inr (Or.inl h)) hn
    · simp [h]
  · exact absurd hy hn

/-- What the entries es may take away, step by step from state st. -/
def killedAll : BSt → List (Entry BVal) → List NodeId
  | _, [] => []
  | st, e :: es => killed st e.val ++ killedAll (bstep st e) es

theorem killedAll_len : ∀ (es : List (Entry BVal)) (st : BSt), (st.1.map (·.1)).Nodup →
    (killedAll st es).length ≤ (es.map (fun e => bvalW e.val)).sum := by
  intro es
  induction es with
  | nil => intro _ _; simp [killedAll]
  | cons e es ih =>
    intro st hnd
    simp only [killedAll, List.length_append, List.map_cons, List.sum_cons]
    have := killed_len st hnd e.val
    have := ih (bstep st e) (nodup_keys_bstep st hnd e)
    omega

theorem lost_sub : ∀ (es : List (Entry BVal)) (st : BSt) (y : NodeId), y ∈ bout st →
    y ∉ bout (es.foldl bstep st) → y ∈ killedAll st es := by
  intro es
  induction es with
  | nil => intro st y h1 h2; exact absurd h1 h2
  | cons e es ih =>
    intro st y h1 h2
    simp only [List.foldl_cons] at h2
    simp only [killedAll, List.mem_append]
    by_cases hm : y ∈ bout (bstep st e)
    · exact Or.inr (ih _ y hm h2)
    · exact Or.inl (step_lost st e h1 hm)

theorem nodup_keys_fold : ∀ (h : History BVal) (st : BSt), (st.1.map (·.1)).Nodup →
    ((h.foldl bstep st).1.map (·.1)).Nodup := by
  intro h
  induction h with
  | nil => intro st hnd; exact hnd
  | cons e h ih => intro st hnd; exact ih _ (nodup_keys_bstep st hnd e)

/-- `blive` loses at most the weights of the appended entries: the live
children of h that are not live children of h ++ es are at most
the sum of `bvalW` over es. -/
theorem blive_lost (h es : History BVal) :
    ((blive h).filter (fun y => !(blive (h ++ es)).contains y)).length ≤
      (es.map (fun e => bvalW e.val)).sum := by
  have hnd0 : ((h.foldl bstep ([], none, none)).1.map (·.1)).Nodup :=
    nodup_keys_fold h _ List.nodup_nil
  have hL : ((blive h).filter (fun y => !(blive (h ++ es)).contains y)).Nodup := by
    rw [blive_eq]; unfold bout
    exact nodup_filter (nodup_eraseDups _) _
  have hsub : ∀ y ∈ (blive h).filter (fun y => !(blive (h ++ es)).contains y),
      y ∈ killedAll (h.foldl bstep ([], none, none)) es := by
    intro y hy
    rw [List.mem_filter] at hy
    obtain ⟨hy1, hy2⟩ := hy
    rw [blive_eq] at hy1 hy2
    apply lost_sub es _ y hy1
    intro hm
    rw [List.foldl_append] at hy2
    simp [hm] at hy2
  exact Nat.le_trans (nodup_length_le_sub hL hsub) (killedAll_len es _ hnd0)

theorem mem_setAssoc_none {m : List (Nat × Option Nat)} {c : Nat} {p : Nat × Option Nat}
    (hp : p ∈ setAssoc m c none) (hne : p.2 ≠ none) : p ∈ m := by
  unfold setAssoc at hp
  by_cases h : m.any (fun p => p.1 == c) = true
  · simp only [h, ↓reduceIte] at hp
    obtain ⟨q, hq, hqp⟩ := List.mem_map.mp hp
    by_cases hqc : (q.1 == c) = true
    · simp only [hqc, ↓reduceIte] at hqp; subst hqp; exact absurd rfl hne
    · simp only [hqc, Bool.false_eq_true, ↓reduceIte] at hqp; subst hqp; exact hq
  · simp only [h, Bool.false_eq_true, ↓reduceIte] at hp
    rcases List.mem_append.mp hp with h1 | h1
    · exact h1
    · simp only [List.mem_singleton] at h1; subst h1; exact absurd rfl hne

/-- The live pointers of `blive` are pointers of its entries (`LiveSub`). -/
theorem bout_sub : ∀ (h : History BVal) (st : BSt) (y : NodeId), y ∈ bout (h.foldl bstep st) →
    y ∈ bout st ∨ ∃ e ∈ h, y ∈ bptrs e.val := by
  intro h
  induction h with
  | nil => intro st y hy; exact Or.inl hy
  | cons e h ih =>
    intro st y hy
    simp only [List.foldl_cons] at hy
    rcases ih (bstep st e) y hy with h1 | ⟨e', he', hy'⟩
    · rw [mem_bout] at h1
      unfold bstep at h1
      split at h1
      · rename_i c y' hv
        simp only at h1
        rcases h1 with ⟨p, hp, hpy⟩ | h | h
        · unfold setAssoc at hp
          split at hp
          · obtain ⟨q, hq, hqp⟩ := List.mem_map.mp hp
            split at hqp
            · subst hqp
              simp only [Option.some.injEq] at hpy
              subst hpy
              exact Or.inr ⟨e, List.mem_cons_self, by simp [hv, bptrs]⟩
            · subst hqp
              exact Or.inl (mem_bout.mpr (Or.inl ⟨q, hq, hpy⟩))
          · rcases List.mem_append.mp hp with hp | hp
            · exact Or.inl (mem_bout.mpr (Or.inl ⟨p, hp, hpy⟩))
            · simp only [List.mem_singleton] at hp
              subst hp
              simp only [Option.some.injEq] at hpy
              subst hpy
              exact Or.inr ⟨e, List.mem_cons_self, by simp [hv, bptrs]⟩
        · exact Or.inl (mem_bout.mpr (Or.inr (Or.inl h)))
        · exact Or.inl (mem_bout.mpr (Or.inr (Or.inr h)))
      · rename_i cs hv
        simp only at h1
        rcases h1 with ⟨p, hp, hpy⟩ | h | h
        · left
          apply mem_bout.mpr
          left
          -- a delete only sets values to none
          have key : ∀ (cs : List Nat) (m : List (Nat × Option Nat)) (p : Nat × Option Nat),
              p ∈ cs.foldl (fun m c => if m.any (fun p => p.1 == c) then setAssoc m c none else m) m →
              p.2 ≠ none → p ∈ m := by
            intro cs
            induction cs with
            | nil => intro m p hp _; exact hp
            | cons c cs ih2 =>
              intro m p hp hne
              simp only [List.foldl_cons] at hp
              have := ih2 _ p hp hne
              split at this
              · exact mem_setAssoc_none this hne
              · exact this
          exact ⟨p, key cs st.1 p hp (by rw [hpy]; simp), hpy⟩
        · exact Or.inl (mem_bout.mpr (Or.inr (Or.inl h)))
        · exact Or.inl (mem_bout.mpr (Or.inr (Or.inr h)))
      · rename_i y' hv
        simp only at h1
        rcases h1 with ⟨p, hp, hpy⟩ | h | h
        · exact Or.inl (mem_bout.mpr (Or.inl ⟨p, hp, hpy⟩))
        · simp only [Option.some.injEq] at h
          subst h
          exact Or.inr ⟨e, List.mem_cons_self, by simp [hv, bptrs]⟩
        · exact Or.inl (mem_bout.mpr (Or.inr (Or.inr h)))
      · rename_i z hv
        simp only at h1
        rcases h1 with ⟨p, hp, hpy⟩ | h | h
        · exact Or.inl (mem_bout.mpr (Or.inl ⟨p, hp, hpy⟩))
        · exact Or.inl (mem_bout.mpr (Or.inr (Or.inl h)))
        · simp only [Option.some.injEq] at h
          subst h
          exact Or.inr ⟨e, List.mem_cons_self, by simp [hv, bptrs]⟩
      · exact Or.inl (mem_bout.mpr h1)
    · exact Or.inr ⟨e', List.mem_cons_of_mem e he', hy'⟩

theorem blive_sub (h : History BVal) (y : NodeId) (hy : y ∈ blive h) : ∃ e ∈ h, y ∈ bptrs e.val := by
  rw [blive_eq] at hy
  rcases bout_sub h _ y hy with h1 | h1
  · simp [mem_bout] at h1
  · exact h1

/-! ### `kept` for any spec whose live pointers lose at most a weight -/

section Kept

variable {V T : Type} [DecidableEq V]

/-- `DropStepJ.kept` from a bound on the live pointers an appended history
takes away, with the pointers of the structure after the change going to lower
levels, and the entries before the change at times up to j - 1. -/
theorem kept_of_lost (sp : Spec V T) (w : V → Nat) (P : Struct V) (j : Time) (c : Changes V)
    (hj : 0 < j)
    (hsub : ∀ (h : History V) y, y ∈ sp.live h → ∃ e ∈ h, y ∈ sp.ptrs e.val)
    (hlost : ∀ (h es : History V) (L : List NodeId), L.Nodup →
      (∀ y ∈ L, y ∈ sp.live h ∧ y ∉ sp.live (h ++ es)) → L.length ≤ (es.map (fun e => w e.val)).sum)
    (hptrs : ∀ x n, (P.apply j c).get? x = some n → ∀ e ∈ n.hist, ∀ y ∈ sp.ptrs e.val,
      ∃ m, (P.apply j c).get? y = some m ∧ m.level < n.level)
    (htimes : ∀ x n, P.get? x = some n → ∀ e ∈ n.hist, e.time ≤ j - 1)
    (p : NodeId) (_hp : reachable sp P (j - 1) p = true) (hp' : reachable sp (P.apply j c) j p = true) :
    (lostTo sp P (P.apply j c) j p).length ≤ addsWeight w c p := by
  unfold lostTo
  cases hn : P.get? p with
  | none => simp
  | some n =>
    simp only
    have hn' := get?_apply_of_get? (i := j) (c := c) hn
    have hup : (n.hist ++ addsFor c j p).upTo j = n.hist.upTo (j - 1) ++ addsFor c j p := by
      rw [upTo_append]
      congr 1
      · unfold History.upTo
        apply List.filter_congr
        intro e he
        have := htimes p n hn e he
        simp only [decide_eq_decide]
        omega
      · unfold History.upTo addsFor
        rw [List.filter_eq_self]
        intro e he
        obtain ⟨a, -, rfl⟩ := List.mem_map.mp he
        simp
    have h1 := hlost (n.hist.upTo (j - 1)) (addsFor c j p)
      ((sp.live (n.hist.upTo (j - 1))).eraseDups.filter (fun y => !reachable sp (P.apply j c) j y))
      (nodup_filter (nodup_eraseDups _) _) (by
        intro y hy
        rw [List.mem_filter, List.mem_eraseDups] at hy
        obtain ⟨hy1, hy2⟩ := hy
        refine ⟨hy1, fun hin => ?_⟩
        rw [← hup] at hin
        obtain ⟨e, he, hye⟩ := hsub _ y hin
        have he' : e ∈ (n.hist ++ addsFor c j p) := (List.mem_filter.mp he).1
        obtain ⟨m, hm, hlt⟩ := hptrs p _ hn' e he' y hye
        have : reachable sp (P.apply j c) j y = true :=
          (reachable_iff _ _ _ _).mpr (Reach.child ((reachable_iff _ _ _ _).mp hp') hn' hin hm hlt)
        rw [this] at hy2; cases hy2)
    have e2 : (addsFor c j p).map (fun e => w e.val) =
        (c.adds.filter (fun a => a.1 == p)).map (fun a => w a.2) := by
      unfold addsFor; simp [Function.comp]
    rw [e2] at h1
    exact h1

end Kept

/-- `DropStepJ.kept` holds in BergDB's tree model: in a run of `treeSpec` with
`RunOK`, a node that stays reachable loses, to nodes made unreachable, at most
the weights `bvalW` of the entries its transaction gives it. -/
theorem kept_tree (p : SIS.Tree.Params) (al : Algo BVal SIS.Tree.Tx) (ts : List SIS.Tree.Tx)
    (hok : RunOK (SIS.Tree.treeSpec p) al ts) (hst : AlgOK (SIS.Tree.treeSpec p) al)
    (j : Nat) (hj : j < ts.length) (q : NodeId)
    (hq : reachable (SIS.Tree.treeSpec p) (run (SIS.Tree.treeSpec p) al (ts.take j)).P j q = true)
    (hq' : reachable (SIS.Tree.treeSpec p) ((run (SIS.Tree.treeSpec p) al (ts.take j)).P.apply (j + 1)
      ((SIS.Tree.treeSpec p).exec ts[j] (j + 1)
        (view (SIS.Tree.treeSpec p) (run (SIS.Tree.treeSpec p) al (ts.take j)).P j))) (j + 1) q = true) :
    (lostTo (SIS.Tree.treeSpec p) (run (SIS.Tree.treeSpec p) al (ts.take j)).P
      ((run (SIS.Tree.treeSpec p) al (ts.take j)).P.apply (j + 1)
        ((SIS.Tree.treeSpec p).exec ts[j] (j + 1)
          (view (SIS.Tree.treeSpec p) (run (SIS.Tree.treeSpec p) al (ts.take j)).P j))) (j + 1) q).length ≤
      addsWeight bvalW ((SIS.Tree.treeSpec p).exec ts[j] (j + 1)
        (view (SIS.Tree.treeSpec p) (run (SIS.Tree.treeSpec p) al (ts.take j)).P j)) q := by
  have hinv := inv_st _ al ts hok hst j (by omega)
  have hinv' := inv_st _ al ts hok hst (j + 1) (by omega)
  have hP := st_P_succ _ al ts hok hst hj
  apply kept_of_lost (SIS.Tree.treeSpec p) bvalW _ (j + 1) _ (by omega)
  · intro h y hy; exact blive_sub h y hy
  · intro h es L hL hLy
    have hsub : ∀ y ∈ L, y ∈ killedAll (h.foldl bstep ([], none, none)) es := by
      intro y hy
      obtain ⟨h1, h2⟩ := hLy y hy
      change y ∈ blive h at h1
      change y ∉ blive (h ++ es) at h2
      rw [blive_eq] at h1 h2
      rw [List.foldl_append] at h2
      exact lost_sub es _ y h1 h2
    exact Nat.le_trans (nodup_length_le_sub hL hsub)
      (killedAll_len es _ (nodup_keys_fold h _ List.nodup_nil))
  · have := hinv'.ptrs
    rw [hP] at this
    simp only [st] at this
    exact this
  · intro x n hx e he
    have := hinv.times x n (by simpa [st] using hx) e he
    simpa using this
  · simpa using hq
  · exact hq'

/-- In BergDB's tree model, `DropRunOKJ` with `bvalW` is its second point
alone: the pointers that the nodes a transaction makes unreachable lose to
nodes it makes unreachable too. -/
theorem dropRunOKJ_tree (p : SIS.Tree.Params) (al : Algo BVal SIS.Tree.Tx) (ts : List SIS.Tree.Tx)
    (hok : RunOK (SIS.Tree.treeSpec p) al ts) (hst : AlgOK (SIS.Tree.treeSpec p) al) (k : Nat → Nat)
    (hk : ∀ j (h : j < ts.length),
      let db := run (SIS.Tree.treeSpec p) al (ts.take j)
      let c := (SIS.Tree.treeSpec p).exec ts[j] (j + 1) (view (SIS.Tree.treeSpec p) db.P j)
      ((removedAt (SIS.Tree.treeSpec p) db.P c (j + 1)).map
        (fun z => (lostTo (SIS.Tree.treeSpec p) db.P (db.P.apply (j + 1) c) (j + 1) z).length)).sum ≤
        k (j + 1)) :
    DropRunOKJ (SIS.Tree.treeSpec p) al bvalW k ts := by
  intro j hj
  refine ⟨fun q hq hq' => ?_, hk j hj⟩
  exact kept_tree p al ts hok hst j hj q (by simpa using hq) hq'

end SIS
