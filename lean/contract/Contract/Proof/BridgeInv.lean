/-
The contract package (bergdb 030-07): what holds of the tree and of the
model's structure after every transaction of a history that meets the
bridge's clauses (`BInv`): the structure holds the tree (`Rep`), every klong
and every space root has a time up to now, every key node's klongs are well
formed with W5, every key klong names a node on a lower level, and the top's
link. `binv_step` proves it for one more transaction.
-/
import Mathlib.Tactic
import SIS.Proof.Init
import Contract.Proof.BridgeMap
import Contract.Proof.Frame

namespace Contract

open SIS (Struct Changes Entry History Node NewNode Spec)
open SIS.Check (BVal bptrs blive bspec)

/-! ## The history's parts -/

theorem BHist.tree_succ (h : BHist) {j : Nat} (hj : j < h.txs.length) :
    h.tree (j + 1) = h.txs[j].s := by
  simp [BHist.tree, List.getElem?_eq_getElem hj]

theorem BHist.P_succ (h : BHist) {j : Nat} (hj : j < h.txs.length) :
    h.P (j + 1) = (h.P j).apply (j + 1) h.txs[j].c := by
  simp [BHist.P, List.getElem?_eq_getElem hj]

/-! ## The invariants -/

/-- Every time klong and every space root has a time up to j. -/
def Timely (j : Nat) (s : Tree) : Prop :=
  (∀ x n, s.obj x = some (.key n) → ∀ t, Klong.time t ∈ n.ks → t ≤ j) ∧
  ∀ r ∈ s.roots, r.1 ≤ j

/-- Every key node's klongs are well formed, with W5. -/
def AllWf (s : Tree) : Prop :=
  ∀ x n, s.obj x = some (.key n) → klongsWf n.ks = true ∧ fullOk n.ks = true

/-- A4: every key klong of every key node names a node on a lower level. -/
def LevOK (s : Tree) : Prop :=
  ∀ x n, s.obj x = some (.key n) → ∀ c y, Klong.key c y ∈ n.ks →
    ∃ o, s.obj y = some o ∧ lvl o < n.level

/-- The model's structure holds the tree, a value with an entry of a time up
to j. -/
def RepT (j : Nat) (P : Struct BVal) (s : Tree) : Prop :=
  ∀ x o, s.obj x = some o →
    match o with
    | .key n => P.get? x = some { level := n.level, isData := false, hist := entriesOf n.ks }
    | .val v => ∃ t, t ≤ j ∧ P.get? x = some { level := 0, isData := true, hist := [⟨t, .data v⟩] }

theorem RepT.rep {j : Nat} {P : Struct BVal} {s : Tree} (h : RepT j P s) : Rep P s := by
  intro x o hx
  have := h x o hx
  cases o with
  | key n => exact this
  | val v =>
    obtain ⟨t, _, ht⟩ := this
    exact ⟨t, ht⟩

/-- What holds after the first j transactions of a history. -/
structure BInv (h : BHist) (j : Nat) : Prop where
  rep : RepT j (h.P j) (h.tree j)
  timely : Timely j (h.tree j)
  wf : AllWf (h.tree j)
  lev : LevOK (h.tree j)
  link : TopLink h.spec (h.P j) j (h.tree j)

/-! ## The clauses, as statements -/

theorem madeKs_sound {i : Nat} {ks : List Klong} (h : madeKs i ks = true) :
    ∃ more, ks = Klong.time i :: more ∧ more.all (fun k => !k.isTime) = true := by
  cases ks with
  | nil => simp [madeKs] at h
  | cons k more =>
    cases k with
    | time t =>
      simp only [madeKs, Bool.and_eq_true, beq_iff_eq] at h
      exact ⟨more, by rw [h.1], h.2⟩
    | key c y => simp [madeKs] at h
    | del b => simp [madeKs] at h

theorem extKs4_sound {i : Nat} {ks ks' : List Klong} (h : extKs4 i ks ks' = true) :
    ks' = ks ∨ ∃ more, ks' = ks ++ Klong.time i :: more ∧
      more.all (fun k => !k.isTime) = true := by
  simp only [extKs4, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with h | ⟨⟨h1, h2⟩, _⟩
  · exact Or.inl h
  · right
    obtain ⟨more, hm, hall⟩ := madeKs_sound h2
    refine ⟨more, ?_, hall⟩
    have hp : ks <+: ks' := List.isPrefixOf_iff_prefix.mp h1
    obtain ⟨t, ht⟩ := hp
    rw [← ht] at hm ⊢
    simp only [List.drop_left] at hm
    rw [hm]

theorem Ext.lvl {i : Time} {o o' : Obj} (h : Ext i o o') : lvl o' = lvl o := by
  cases o with
  | key n =>
    cases o' with
    | key n' => exact h.1
    | val v => exact absurd h (by simp [Ext])
  | val v =>
    cases o' with
    | key n' => exact absurd h (by simp [Ext])
    | val v' => rfl

/-- The time klongs of klongs that are no time klongs: none. -/
theorem not_time_mem {more : List Klong} (h : more.all (fun k => !k.isTime) = true) (t : Nat) :
    Klong.time t ∉ more := by
  intro hm
  have := List.all_eq_true.mp h _ hm
  simp [Klong.isTime] at this

/-- The clauses of one transaction, in one place. -/
structure StepFacts (p : Params) (h : BHist) (j : Nat) (hj : j < h.txs.length) : Prop where
  contract : Contract p (j + 1) (h.tree j) h.txs[j].ops h.txs[j].D (h.tree (j + 1))
  news : newsOk h.topLevel (h.tree j) (h.tree (j + 1)) h.txs[j].c = true
  adds : addsOk (h.tree j) (h.tree (j + 1)) h.txs[j].D h.txs[j].c = true
  loc : localOk (j + 1) (h.tree j) (h.tree (j + 1)) h.txs[j].D = true
  cur : currentOk ((h.tree (j + 1)).at (j + 1)) h.txs[j].c (reach ((h.tree (j + 1)).at (j + 1))) = true
  mkd : madeOk ((h.tree (j + 1)).at (j + 1)) h.txs[j].c (reach ((h.tree (j + 1)).at (j + 1))) = true
  nores : noResOk h.txs[j].c (reach ((h.tree j).at j)) (reach ((h.tree (j + 1)).at (j + 1))) = true
  made : Made (h.tree j) (h.tree (j + 1)) h.txs[j].c
  top : TopOK h.spec (h.P j) (j + 1) (h.tree j) (h.tree (j + 1)) h.txs[j].c
  touch : TouchOK h.spec (h.P j) (j + 1) h.txs[j].c

theorem MeetsBridge.facts {p : Params} {h : BHist} (hm : MeetsBridge p h) (j : Nat)
    (hj : j < h.txs.length) : StepFacts p h j hj := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hm.step j hj
  simp only [bridgeOk, Bool.and_eq_true, Nat.add_sub_cancel] at h2
  exact ⟨h1, h2.1.1.1.1.1, h2.1.1.1.1.2, h2.1.1.1.2, h2.1.1.2, h2.1.2, h2.2, h3, h4, h5⟩

section Step

variable {p : Params} {h : BHist} {j : Nat} {hj : j < h.txs.length}

/-- The local clauses for a key node of D. -/
theorem StepFacts.local_of (f : StepFacts p h j hj) {x : NodeId} (hx : x ∈ h.txs[j].D)
    {n' : KNode} (hn : (h.tree (j + 1)).obj x = some (.key n')) :
    (match (h.tree j).obj x with
      | some (.key n) => extKs4 (j + 1) n.ks n'.ks
      | some (.val _) => false
      | none => madeKs (j + 1) n'.ks) = true ∧
    klongsWf n'.ks = true ∧ fullOk n'.ks = true ∧ ptrsLow (h.tree (j + 1)) n' = true := by
  have := List.all_eq_true.mp f.loc x hx
  simp only [hn, Bool.and_eq_true] at this
  exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩

/-- A key node of after the transaction, as it was before: the same level, and
its klongs kept, with klongs of the transaction's time after them if any; or
made, with klongs of the transaction's time. -/
theorem StepFacts.key_cases (f : StepFacts p h j hj) {x : NodeId} {n' : KNode}
    (hn : (h.tree (j + 1)).obj x = some (.key n')) :
    (∃ n, (h.tree j).obj x = some (.key n) ∧ n'.level = n.level ∧
      (n'.ks = n.ks ∨ (x ∈ h.txs[j].D ∧ ∃ more, n'.ks = n.ks ++ Klong.time (j + 1) :: more ∧
        more.all (fun k => !k.isTime) = true))) ∨
    ((h.tree j).obj x = none ∧ x ∈ h.txs[j].D ∧ ∃ more, n'.ks = Klong.time (j + 1) :: more ∧
      more.all (fun k => !k.isTime) = true) := by
  obtain ⟨f1, f2, _⟩ := f.contract.2
  cases ho : (h.tree j).obj x with
  | none =>
    right
    have hD := f2 x n' hn ho
    have hl := (f.local_of hD hn).1
    rw [ho] at hl
    exact ⟨rfl, hD, madeKs_sound hl⟩
  | some o =>
    left
    obtain ⟨o', ho', hext, hsame⟩ := f1 x o ho
    rw [hn] at ho'
    obtain rfl : o' = .key n' := by injection ho' with h1; exact h1.symm
    cases o with
    | val v => exact absurd hext (by simp [Ext])
    | key n =>
      refine ⟨n, rfl, hext.1, ?_⟩
      by_cases hD : x ∈ h.txs[j].D
      · have hl := (f.local_of hD hn).1
        rw [ho] at hl
        rcases extKs4_sound hl with h1 | ⟨more, h1, h2⟩
        · exact Or.inl h1
        · exact Or.inr ⟨hD, more, h1, h2⟩
      · have := hsame hD
        injection this with h1
        left; rw [h1]

/-- A value of after the transaction was a value before, or is made. -/
theorem StepFacts.val_cases (f : StepFacts p h j hj) {x : NodeId} {v : Nat}
    (hn : (h.tree (j + 1)).obj x = some (.val v)) :
    (h.tree j).obj x = some (.val v) ∨ (h.tree j).obj x = none := by
  obtain ⟨f1, _, _⟩ := f.contract.2
  cases ho : (h.tree j).obj x with
  | none => exact Or.inr rfl
  | some o =>
    left
    obtain ⟨o', ho', hext, _⟩ := f1 x o ho
    rw [hn] at ho'
    obtain rfl : o' = .val v := by injection ho' with h1; exact h1.symm
    cases o with
    | key n => exact absurd hext (by simp [Ext])
    | val w =>
      have : v = w := hext
      rw [this]

/-- Clause K for every node of the tree after the transaction. -/
theorem StepFacts.adds_all (f : StepFacts p h j hj) (x : NodeId)
    (hx : ((h.tree (j + 1)).obj x).isSome = true) :
    (h.txs[j].c.adds.filter (fun a => a.1 == x)).map (·.2) =
      newVals (h.tree j) (h.tree (j + 1)) x := by
  by_cases hin : x ∈ h.txs[j].c.adds.map (·.1) ++ h.txs[j].D ++ h.txs[j].c.new.map (·.id)
  · have := List.all_eq_true.mp f.adds x hin
    simp only [Bool.or_eq_true, Option.isNone_iff_eq_none, beq_iff_eq] at this
    rcases this with h1 | h1
    · rw [h1] at hx; simp at hx
    · exact h1
  · simp only [List.mem_append, not_or] at hin
    obtain ⟨⟨h1, h2⟩, h3⟩ := hin
    have he : h.txs[j].c.adds.filter (fun a => a.1 == x) = [] := by
      rw [List.filter_eq_nil_iff]
      intro a ha hax
      exact h1 (List.mem_map.mpr ⟨a, ha, by simpa using hax⟩)
    rw [he]
    have hold : (h.tree j).obj x ≠ none := fun hno => h3 (f.made x hno hx)
    obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.mp hold
    obtain ⟨o', ho', _, hsame⟩ := f.contract.2.1 x o ho
    have h4 := hsame h2
    rw [h4] at ho'
    unfold newVals
    rw [ho', ho]
    cases o with
    | key n => simp
    | val v => simp

/-- The entries of klongs added at one time, stamped again with that time. -/
theorem restamp {i : Nat} {R : History BVal} (hR : ∀ e ∈ R, e.time = i) :
    (R.map (·.val)).map (fun v => (⟨i, v⟩ : Entry BVal)) = R := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id R]
  apply List.map_congr_left
  intro e he
  have := hR e he
  cases e
  simp_all

/-- The entries that the change adds to a node, as the model's history. -/
theorem addsFor_eq (c : Changes BVal) (i : Nat) (x : NodeId) :
    SIS.addsFor c i x = ((c.adds.filter (fun a => a.1 == x)).map (·.2)).map
      (fun v => (⟨i, v⟩ : Entry BVal)) := by
  simp [SIS.addsFor, List.map_map, Function.comp]

/-- The node of the model for a node that the change makes. -/
theorem newNodeOf_mem {c : Changes BVal} (hnd : (c.new.map (·.id)).Nodup) {nn : NewNode}
    (hnn : nn ∈ c.new) :
    SIS.newNodeOf c nn.id = some { level := nn.level, isData := nn.isData, hist := [] } := by
  unfold SIS.newNodeOf
  have h1 : ((c.new.map (fun n => (n.id, ({ level := n.level, isData := n.isData, hist := [] } :
      Node BVal)))).map (·.1)).Nodup := by
    rw [List.map_map]; exact hnd
  exact SIS.get?_of_mem_nodup h1 (p := (nn.id, _)) (List.mem_map.mpr ⟨nn, hnn, rfl⟩)

/-- The made node with id x, by clause N. -/
theorem StepFacts.new_of (f : StepFacts p h j hj) {x : NodeId} (hno : (h.tree j).obj x = none)
    (hs : ((h.tree (j + 1)).obj x).isSome = true) :
    ∃ nn ∈ h.txs[j].c.new, nn.id = x ∧ (h.P j).get? x = none ∧
      SIS.newNodeOf h.txs[j].c x = some { level := nn.level, isData := nn.isData, hist := [] } ∧
      match (h.tree (j + 1)).obj x with
      | some (.key n) => nn.level = n.level ∧ nn.isData = false
      | some (.val _) => nn.level = 0 ∧ nn.isData = true
      | none => True := by
  have hmem := f.made x hno hs
  obtain ⟨nn, hnn, rfl⟩ := List.mem_map.mp hmem
  have hnews := f.news
  simp only [newsOk, Bool.and_eq_true, decide_eq_true_eq] at hnews
  have h1 := List.all_eq_true.mp hnews.2 nn hnn
  simp only [Bool.and_eq_true] at h1
  refine ⟨nn, hnn, rfl, f.top.fresh nn hnn hno, newNodeOf_mem hnews.1 hnn, ?_⟩
  cases ho : (h.tree (j + 1)).obj nn.id with
  | none => trivial
  | some o =>
    rw [ho] at h1
    cases o with
    | key n => simpa using h1.2
    | val v => simpa using h1.2

/-- The model's structure holds the tree after the transaction. -/
theorem StepFacts.rep (f : StepFacts p h j hj) (hr : RepT j (h.P j) (h.tree j)) :
    RepT (j + 1) (h.P (j + 1)) (h.tree (j + 1)) := by
  rw [h.P_succ hj]
  intro x o' hx
  have hK := f.adds_all x (by rw [hx]; rfl)
  cases o' with
  | key n' =>
    simp only
    rcases f.key_cases hx with ⟨n, hn, hlev, hks⟩ | ⟨hno, hD, more, hks, hmore⟩
    · have hP := hr x _ hn
      simp only at hP
      rw [SIS.get?_apply_of_get? hP, addsFor_eq, hK]
      unfold newVals
      rw [hx, hn]
      simp only [Option.some.injEq, Node.mk.injEq, true_and]
      refine ⟨hlev.symm, ?_⟩
      rcases hks with h1 | ⟨_, more, h1, hmore⟩
      · rw [h1]; simp
      · rw [h1, entriesOf_append, List.drop_left]
        have hR : ∀ e ∈ entriesFrom n.ks (lastTimeOr 0 n.ks) (lastBitmap n.ks)
            (Klong.time (j + 1) :: more), e.time = j + 1 := by
          intro e he
          simp only [entriesFrom] at he
          exact entriesFrom_time more _ _ _ hmore e he
        rw [restamp hR]
    · obtain ⟨nn, _, _, hfresh, hnew, hkind⟩ := f.new_of hno (by rw [hx]; rfl)
      rw [hx] at hkind
      rw [SIS.get?_apply, hfresh, hnew, addsFor_eq, hK]
      unfold newVals
      rw [hx, hno]
      simp only [Option.none_or, Option.map_some, List.nil_append, List.drop_zero,
        Option.some.injEq, Node.mk.injEq]
      refine ⟨hkind.1, hkind.2, ?_⟩
      have hR : ∀ e ∈ entriesOf n'.ks, e.time = j + 1 := by
        intro e he
        rw [hks] at he
        simp only [entriesOf, entriesFrom] at he
        exact entriesFrom_time more _ _ _ hmore e he
      exact restamp hR
  | val v =>
    simp only
    rcases f.val_cases hx with hn | hno
    · obtain ⟨t, ht, hP⟩ := hr x _ hn
      refine ⟨t, by omega, ?_⟩
      rw [SIS.get?_apply_of_get? hP, addsFor_eq, hK]
      unfold newVals
      rw [hx, hn]
      simp
    · obtain ⟨nn, _, _, hfresh, hnew, hkind⟩ := f.new_of hno (by rw [hx]; rfl)
      rw [hx] at hkind
      refine ⟨j + 1, le_refl _, ?_⟩
      rw [SIS.get?_apply, hfresh, hnew, addsFor_eq, hK]
      unfold newVals
      rw [hx, hno]
      simp [hkind.1, hkind.2]

theorem StepFacts.timely (f : StepFacts p h j hj) (ht : Timely j (h.tree j)) :
    Timely (j + 1) (h.tree (j + 1)) := by
  refine ⟨?_, ?_⟩
  · intro x n' hx t hmem
    rcases f.key_cases hx with ⟨n, hn, _, hks⟩ | ⟨_, _, more, hks, hmore⟩
    · rcases hks with h1 | ⟨_, more, h1, hmore⟩
      · rw [h1] at hmem
        exact Nat.le_succ_of_le (ht.1 x n hn t hmem)
      · rw [h1] at hmem
        simp only [List.mem_append, List.mem_cons, Klong.time.injEq] at hmem
        rcases hmem with h2 | h2 | h2
        · exact Nat.le_succ_of_le (ht.1 x n hn t h2)
        · exact Nat.le_of_eq h2
        · exact absurd h2 (not_time_mem hmore t)
    · rw [hks] at hmem
      simp only [List.mem_cons, Klong.time.injEq] at hmem
      rcases hmem with h2 | h2
      · exact Nat.le_of_eq h2
      · exact absurd h2 (not_time_mem hmore t)
  · intro r hr
    obtain ⟨new, h1, h2⟩ := f.contract.2.2.2
    rw [h1] at hr
    rcases List.mem_append.mp hr with h3 | h3
    · exact Nat.le_succ_of_le (ht.2 r h3)
    · exact Nat.le_of_eq (h2 r h3)

theorem StepFacts.wf (f : StepFacts p h j hj) (hw : AllWf (h.tree j)) :
    AllWf (h.tree (j + 1)) := by
  intro x n' hx
  by_cases hD : x ∈ h.txs[j].D
  · have := f.local_of hD hx
    exact ⟨this.2.1, this.2.2.1⟩
  · rcases f.key_cases hx with ⟨n, hn, _, hks⟩ | ⟨_, hD', _⟩
    · rcases hks with h1 | ⟨hD', _⟩
      · rw [h1]; exact hw x n hn
      · exact absurd hD' hD
    · exact absurd hD' hD

theorem StepFacts.lev (f : StepFacts p h j hj) (hl : LevOK (h.tree j)) :
    LevOK (h.tree (j + 1)) := by
  intro x n' hx c y hmem
  by_cases hD : x ∈ h.txs[j].D
  · have := (f.local_of hD hx).2.2.2
    have h1 := List.all_eq_true.mp this _ hmem
    simp only at h1
    cases ho : (h.tree (j + 1)).obj y with
    | none => rw [ho] at h1; simp at h1
    | some o =>
      rw [ho] at h1
      exact ⟨o, rfl, by simpa using h1⟩
  · rcases f.key_cases hx with ⟨n, hn, hlev, hks⟩ | ⟨_, hD', _⟩
    · rcases hks with h1 | ⟨hD', _⟩
      · rw [h1] at hmem
        obtain ⟨o, ho, hlt⟩ := hl x n hn c y hmem
        obtain ⟨o', ho', hext, _⟩ := f.contract.2.1 y o ho
        exact ⟨o', ho', by rw [hext.lvl, hlev]; exact hlt⟩
      · exact absurd hD' hD
    · exact absurd hD' hD

/-- The invariants after one more transaction. -/
theorem binv_step (f : StepFacts p h j hj) (hi : BInv h j) : BInv h (j + 1) :=
  ⟨f.rep hi.rep, f.timely hi.timely, f.wf hi.wf, f.lev hi.lev, by
    have := f.top.link
    rwa [← h.P_succ hj] at this⟩

end Step

end Contract
