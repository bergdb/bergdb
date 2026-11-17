/-
The contract package (bergdb 030-07): the model's assumptions for a bridged
history. The start meets `SpecOK` and the invariants (`specOK_of_start`,
`binv_start`); every transaction's change meets `StepOK` on the model's
structure (`StepFacts.stepOK`); the model's run has the history's structures
(`run_P`); so the run meets `RunOK` (`MeetsBridge.runOK`).
-/
import Mathlib.Tactic
import SIS.Proof.RunFacts
import Contract.Proof.BridgeReach

namespace Contract

open SIS (Struct Changes Entry History Node NewNode Spec Reach)
open SIS.Check (BVal bptrs blive bspec)

/-! ## The start -/

theorem blive_top (t z : Nat) : blive [(⟨t, .top z⟩ : Entry BVal)] = [z] := by
  simp [blive]; rfl

theorem blive_rootKey (t y : Nat) : blive [(⟨t, .rootKey y⟩ : Entry BVal)] = [y] := by
  simp [blive]; rfl

/-- The state of `blive`'s fold after a history of entries for top nodes. -/
theorem blive_tops : ∀ (hst : History BVal), (∀ e ∈ hst, ∃ z, e.val = BVal.top z) →
    hst.foldl SIS.Check.bstep ([], none, none) =
      ([], none, hst.getLast?.bind (fun e => (bptrs e.val).head?)) := by
  intro hst
  induction hst using List.reverseRecOn with
  | nil => intro _; rfl
  | append_singleton l e ih =>
    intro hall
    rw [List.foldl_append, ih (fun e' he' => hall e' (List.mem_append_left _ he'))]
    obtain ⟨z, hz⟩ := hall e (List.mem_append_right _ List.mem_cons_self)
    simp [SIS.Check.bstep, hz, bptrs]

/-- The model's primordial structure. -/
theorem p0_eq {h : BHist} {r z lr lz l0 : Nat} (hr : r ≠ 0) (hz : z ≠ 0) (hzr : z ≠ r)
    (hnew : h.c0.new = [⟨0, l0, false⟩, ⟨r, lr, false⟩, ⟨z, lz, false⟩])
    (hadds : h.c0.adds = [(0, .top z), (z, .rootKey r)]) :
    h.p0 = [(0, { level := l0, isData := false, hist := [⟨0, .top z⟩] }),
      (r, { level := lr, isData := false, hist := [] }),
      (z, { level := lz, isData := false, hist := [⟨0, .rootKey r⟩] })] := by
  have hz' : ¬ (0 = z) := fun h => hz h.symm
  have hrz : ¬ (r = z) := fun h => hzr h.symm
  simp [BHist.p0, Struct.apply, hnew, hadds, Struct.addEntry, hr, hz, hz', hrz]

/-- The start, with the model's primordial structure and its nodes. -/
structure StartFacts (h : BHist) (r z lr lz l0 : Nat) : Prop where
  hr : r ≠ 0
  hz : z ≠ 0
  hzr : z ≠ r
  hlr : 0 < lr
  hlrz : lr < lz
  hlz0 : lz < l0
  p0 : h.p0 = [(0, { level := l0, isData := false, hist := [⟨0, .top z⟩] }),
      (r, { level := lr, isData := false, hist := [] }),
      (z, { level := lz, isData := false, hist := [⟨0, .rootKey r⟩] })]
  top : h.spec.topLevel = lz
  get0 : h.p0.get? 0 = some { level := l0, isData := false, hist := [⟨0, .top z⟩] }
  getr : h.p0.get? r = some { level := lr, isData := false, hist := [] }
  getz : h.p0.get? z = some { level := lz, isData := false, hist := [⟨0, .rootKey r⟩] }
  obj : h.s0.obj r = some (.key { level := lr, leaf := true, ks := [.time 0] })
  none : ∀ x, x ≠ r → h.s0.obj x = none
  roots : h.s0.roots = [(0, r)]

theorem StartB.facts {h : BHist} (hs : StartB h) : ∃ r z lr lz l0, StartFacts h r z lr lz l0 := by
  obtain ⟨r, z, lr, lz, l0, hr, hz, hzr, hlr, hlrz, hlz0, hlz, hnew, hadds, hobj, hnone, hroots⟩ := hs
  have hp0 := p0_eq hr hz hzr hnew hadds
  have hr' : ¬ (0 = r) := fun h => hr h.symm
  have hz' : ¬ (0 = z) := fun h => hz h.symm
  have hrz : ¬ (r = z) := fun h => hzr h.symm
  refine ⟨r, z, lr, lz, l0, hr, hz, hzr, hlr, hlrz, hlz0, hp0, ?_, ?_, ?_, ?_, hobj, hnone, hroots⟩
  · show SIS.Check.topLevelOf h.p0 = lz
    rw [hp0]
    simp [SIS.Check.topLevelOf]
    omega
  · rw [hp0]; simp [SIS.get?_cons]
  · rw [hp0]; simp [SIS.get?_cons, hr]
  · rw [hp0]; simp [SIS.get?_cons, hz, hzr]

section Start

variable {h : BHist} {r z lr lz l0 : Nat}

theorem StartFacts.mem (f : StartFacts h r z lr lz l0) {q : NodeId × Node BVal} (hq : q ∈ h.p0) :
    q = (0, { level := l0, isData := false, hist := [⟨0, .top z⟩] }) ∨
    q = (r, { level := lr, isData := false, hist := [] }) ∨
    q = (z, { level := lz, isData := false, hist := [⟨0, .rootKey r⟩] }) := by
  rw [f.p0] at hq
  simpa using hq

theorem StartFacts.reach0 (f : StartFacts h r z lr lz l0) : Reach h.spec h.p0 0 SIS.root :=
  Reach.root _ f.get0

theorem StartFacts.reachz (f : StartFacts h r z lr lz l0) : Reach h.spec h.p0 0 z :=
  Reach.child f.reach0 f.get0 (by
    show z ∈ blive (History.upTo [(⟨0, .top z⟩ : Entry BVal)] 0)
    simp [History.upTo, blive_top]) f.getz f.hlz0

theorem StartFacts.reachr (f : StartFacts h r z lr lz l0) : Reach h.spec h.p0 0 r :=
  Reach.child f.reachz f.getz (by
    show r ∈ blive (History.upTo [(⟨0, .rootKey r⟩ : Entry BVal)] 0)
    simp [History.upTo, blive_rootKey]) f.getr f.hlrz

/-- The model's assumptions on the structure, for the start. -/
theorem StartFacts.specOK (f : StartFacts h r z lr lz l0) : SIS.SpecOK h.spec := by
  have hinit : h.spec.init = h.p0 := rfl
  have hr' : ¬ (0 = r) := fun h => f.hr h.symm
  have hz' : ¬ (0 = z) := fun h => f.hz h.symm
  have hrz : ¬ (r = z) := fun h => f.hzr h.symm
  refine { liveSub := SIS.Check.blive_sub, initDistinct := ?_, initRoot := ?_, initTime := ?_,
           initData := ?_, initLevels := ?_, initReachable := ?_, virtInit := ?_ }
  · rw [hinit, f.p0]
    simp [hr', hz', hrz]
  · rw [hinit]
    show (h.p0.get? 0).isSome = true
    rw [f.get0]; rfl
  · intro q hq e he
    rw [hinit] at hq
    rcases f.mem hq with rfl | rfl | rfl
    · simp only [List.mem_singleton] at he; rw [he]
    · simp at he
    · simp only [List.mem_singleton] at he; rw [he]
  · intro q hq hd
    rw [hinit] at hq
    rcases f.mem hq with rfl | rfl | rfl <;> simp at hd
  · intro q hq e he y hy
    rw [hinit] at hq ⊢
    rcases f.mem hq with rfl | rfl | rfl
    · simp only [List.mem_singleton] at he
      subst he
      have : y = z := by simpa [BHist.spec, bspec, bptrs] using hy
      subst this
      exact ⟨_, f.getz, f.hlz0⟩
    · simp at he
    · simp only [List.mem_singleton] at he
      subst he
      have : y = r := by simpa [BHist.spec, bspec, bptrs] using hy
      subst this
      exact ⟨_, f.getr, f.hlrz⟩
  · intro q hq
    rw [hinit] at hq ⊢
    rw [SIS.reachable_iff]
    rcases f.mem hq with rfl | rfl | rfl
    · exact f.reach0
    · exact f.reachr
    · exact f.reachz
  · intro _
    refine { rootPtrs := fun _ => rfl, rootIndex := ?_, initTop := ?_, initRootHist := ?_ }
    · intro n hn
      rw [hinit] at hn
      have h0 := f.get0
      change h.p0.get? 0 = _ at hn
      rw [h0] at hn
      injection hn with hn
      rw [← hn]
    · intro q hq hne hlev
      rw [hinit] at hq
      rw [f.top] at hlev
      rcases f.mem hq with rfl | rfl | rfl
      · exact absurd rfl hne
      · simp only at hlev
        have := f.hlrz
        omega
      · refine ⟨rfl, by simp, ?_⟩
        intro q' hq' hne' hlev'
        rw [hinit] at hq'
        rw [f.top] at hlev'
        rcases f.mem hq' with rfl | rfl | rfl
        · exact absurd rfl hne'
        · simp only at hlev'
          have := f.hlrz
          omega
        · rfl
    · intro n hn
      rw [hinit] at hn
      change h.p0.get? 0 = _ at hn
      rw [f.get0] at hn
      injection hn with hn
      rw [← hn, hinit, f.top, f.p0]
      have h1 : ¬ lz ≤ lr := by have := f.hlrz; omega
      simp [SIS.root, f.hz, h1, BHist.spec, bspec]

/-- The invariants at the start. -/
theorem StartFacts.binv (f : StartFacts h r z lr lz l0) : BInv h 0 := by
  have hr0 : (0 : Nat) ≠ r := fun h => f.hr h.symm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x o hx
    change h.s0.obj x = some o at hx
    by_cases hxr : x = r
    · subst hxr
      rw [f.obj] at hx
      injection hx with hx
      subst hx
      exact f.getr
    · rw [f.none x hxr] at hx; cases hx
  · refine ⟨?_, ?_⟩
    · intro x n hx t ht
      change h.s0.obj x = some _ at hx
      by_cases hxr : x = r
      · subst hxr
        rw [f.obj] at hx
        injection hx with hx
        injection hx with hx
        subst hx
        simp only [List.mem_singleton, Klong.time.injEq] at ht
        exact Nat.le_of_eq ht
      · rw [f.none x hxr] at hx; cases hx
    · intro q hq
      change q ∈ h.s0.roots at hq
      rw [f.roots] at hq
      simp only [List.mem_singleton] at hq
      rw [hq]
  · intro x n hx
    change h.s0.obj x = some _ at hx
    by_cases hxr : x = r
    · subst hxr
      rw [f.obj] at hx
      injection hx with hx
      injection hx with hx
      subst hx
      exact ⟨by show klongsWf [Klong.time 0] = true; decide,
        by show fullOk [Klong.time 0] = true; decide⟩
    · rw [f.none x hxr] at hx; cases hx
  · intro x n hx c y hy
    change h.s0.obj x = some _ at hx
    by_cases hxr : x = r
    · subst hxr
      rw [f.obj] at hx
      injection hx with hx
      injection hx with hx
      subst hx
      simp at hy
    · rw [f.none x hxr] at hx; cases hx
  · refine ⟨_, z, _, r, _, f.get0, ?_, f.getz, f.hlz0, ?_, ?_, f.obj, f.hlrz, f.none _ hr0, f.none _ f.hzr⟩
    · show blive (History.upTo [(⟨0, .top z⟩ : Entry BVal)] 0) = [z]
      simp [History.upTo, blive_top]
    · show blive (History.upTo [(⟨0, .rootKey r⟩ : Entry BVal)] 0) = [r]
      simp [History.upTo, blive_rootKey]
    · change h.s0.root = some r
      simp [Tree.root, f.roots]

end Start

/-! ## One transaction -/

section Step

variable {p : Params} {h : BHist} {j : Nat} {hj : j < h.txs.length}

/-- An entry value that the change adds to a node of the tree is one of the
node's new entry values. -/
theorem StepFacts.add_mem (f : StepFacts p h j hj) {a : NodeId × BVal} (ha : a ∈ h.txs[j].c.adds)
    (hs : ((h.tree (j + 1)).obj a.1).isSome = true) :
    a.2 ∈ newVals (h.tree j) (h.tree (j + 1)) a.1 := by
  rw [← f.adds_all a.1 hs]
  exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨ha, by simp⟩, rfl⟩

/-- The model's assumptions on one transaction (`StepOK`), for the change of a
transaction that meets the bridge's clauses, on the model's structure. -/
theorem StepFacts.stepOK (f : StepFacts p h j hj) (hi : BInv h j) (hi' : BInv h (j + 1)) :
    SIS.StepOK h.spec (h.P j) (j + 1) h.txs[j].c := by
  have hP' := h.P_succ hj
  have hnews := f.news
  simp only [newsOk, Bool.and_eq_true, decide_eq_true_eq] at hnews
  have hat' : (h.tree (j + 1)).at (j + 1) = h.tree (j + 1) := hi'.timely.at_eq
  have hat : (h.tree j).at j = h.tree j := hi.timely.at_eq
  have hcur := f.cur
  have hmk := f.mkd
  have hnr := f.nores
  rw [hat'] at hcur hmk hnr
  rw [hat] at hnr
  refine { fresh := ?_, distinct := hnews.1, current := ?_, dataFixed := ?_, dataNoPtrs := ?_,
           levels := ?_, newReachable := ?_, noRes := ?_, virt := fun _ => f.top.virt,
           touchIndex := f.touch.index, touchReach := f.touch.reach, touchUp := ?_ }
  · intro nn hnn
    have h1 := List.all_eq_true.mp hnews.2 nn hnn
    simp only [Bool.and_eq_true] at h1
    exact f.top.fresh nn hnn (by simpa using h1.1)
  · intro a ha
    cases ho : (h.tree (j + 1)).obj a.1 with
    | none => exact f.top.current a ha ho
    | some o =>
      have h1 := List.all_eq_true.mp hcur a ha
      simp only [ho] at h1
      rw [← hP']
      exact hi'.mem_reach_model (by simpa using h1)
  · intro a ha n hn
    cases ho' : (h.tree (j + 1)).obj a.1 with
    | none => exact f.top.dataFixed a ha ho' n hn
    | some o' =>
      have hmem := f.add_mem ha (by rw [ho']; rfl)
      cases ho : (h.tree j).obj a.1 with
      | none =>
        obtain ⟨nn, _, _, hfresh, _⟩ := f.new_of ho (by rw [ho']; rfl)
        rw [hfresh] at hn; cases hn
      | some o =>
        cases o with
        | key n0 =>
          have h1 := hi.rep a.1 _ ho
          simp only at h1
          rw [h1] at hn
          injection hn with hn
          rw [← hn]
        | val v =>
          exfalso
          unfold newVals at hmem
          rw [ho', ho] at hmem
          cases o' with
          | key n' =>
            obtain ⟨n, hn', _⟩ | ⟨hno, _⟩ := f.key_cases ho'
            · rw [ho] at hn'; cases hn'
            · rw [ho] at hno; cases hno
          | val v' => simp at hmem
  · intro a ha nn hnn hid hdata
    have h1 := List.all_eq_true.mp hnews.2 nn hnn
    simp only [Bool.and_eq_true] at h1
    rw [hid] at h1
    cases ho' : (h.tree (j + 1)).obj a.1 with
    | none => rw [ho'] at h1; simp [hdata] at h1
    | some o' =>
      cases o' with
      | key n' => rw [ho'] at h1; simp [hdata] at h1
      | val v =>
        have hmem := f.add_mem ha (by rw [ho']; rfl)
        have hno : (h.tree j).obj a.1 = none := by simpa using h1.1
        unfold newVals at hmem
        rw [ho', hno] at hmem
        simp only [Option.isSome_none, Bool.false_eq_true, ite_false, List.mem_singleton] at hmem
        rw [hmem]
        rfl
  · intro a ha y hy
    cases ho' : (h.tree (j + 1)).obj a.1 with
    | none => exact f.top.levels a ha ho' y hy
    | some o' =>
      have hmem := f.add_mem ha (by rw [ho']; rfl)
      unfold newVals at hmem
      rw [ho'] at hmem
      cases o' with
      | val v =>
        exfalso
        simp only at hmem
        split at hmem
        · simp at hmem
        · simp only [List.mem_singleton] at hmem
          rw [hmem] at hy
          simp [BHist.spec, bspec, bptrs] at hy
      | key n' =>
        simp only [List.mem_map] at hmem
        obtain ⟨e, he, hev⟩ := hmem
        have he' := List.mem_of_mem_drop he
        obtain ⟨c, hc⟩ := entriesFrom_ptr n'.ks [] 0 [] e he' y (by rw [hev]; exact hy)
        obtain ⟨oy, hoy, hlt⟩ := hi'.lev a.1 n' ho' c y hc
        obtain ⟨M, hM, hMl⟩ := hi'.node_of hoy
        have hN := hi'.rep a.1 _ ho'
        simp only at hN
        rw [hP'] at hN hM
        exact ⟨_, M, hN, hM, by rw [hMl]; exact hlt⟩
  · intro nn hnn
    cases ho : (h.tree (j + 1)).obj nn.id with
    | none => exact f.top.newReachable nn hnn ho
    | some o =>
      have h1 := List.all_eq_true.mp hmk nn hnn
      simp only [ho, Option.isNone_some, Bool.false_or] at h1
      rw [← hP']
      exact hi'.mem_reach_model (by simpa using h1)
  · intro y hy
    cases ho : (h.tree (j + 1)).obj y with
    | none => exact f.top.noRes y ho hy
    | some o =>
      rw [← hP'] at hy
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hs0, _⟩ := hi'.link
      rcases hi'.model_reach_cases hy with h1 | h1 | h1
      · rw [h1, hs0] at ho; cases ho
      · rw [h1] at ho; cases ho
      · have h2 := List.all_eq_true.mp hnr y h1
        simp only [Bool.or_eq_true, List.any_eq_true, beq_iff_eq] at h2
        rcases h2 with h2 | ⟨nn, hnn, hid⟩
        · left
          simp only [Nat.add_sub_cancel]
          exact hi.mem_reach_model (by simpa using h2)
        · right
          exact List.mem_map.mpr ⟨nn, hnn, hid⟩
  · intro x hx q nq h1 h2 h3
    exact (f.touch.up x hx q nq h1 h2 h3).imp id (fun h4 => ⟨rfl, h4⟩)

end Step

/-! ## The run -/

section Run

variable {p : Params} {h : BHist}

/-- The invariants after every transaction of a bridged history. -/
theorem MeetsBridge.binv (hm : MeetsBridge p h) : ∀ j, j ≤ h.txs.length → BInv h j
  | 0, _ => by
    obtain ⟨r, z, lr, lz, l0, f⟩ := hm.start.facts
    exact f.binv
  | j + 1, hj => binv_step (hm.facts j hj) (hm.binv j (Nat.le_of_succ_le hj))

theorem run_S_length (sp : Spec BVal Nat) (al : SIS.Algo BVal Nat) (ts : List Nat) :
    (SIS.run sp al ts).S.length = ts.length + 1 := by
  have key : ∀ (ts : List Nat) (db : SIS.DB BVal Nat),
      (ts.foldl (SIS.step sp al) db).S.length = db.S.length + ts.length := by
    intro ts
    induction ts with
    | nil => intro db; rfl
    | cons t ts ih =>
      intro db
      simp only [List.foldl_cons, List.length_cons]
      rw [ih, SIS.step_eq_parts]
      simp only [List.length_append, List.length_singleton]
      omega
  unfold SIS.run
  rw [key]
  have : (SIS.init sp).S.length = 1 := rfl
  omega

theorem BHist.ts_get (h : BHist) {j : Nat} (hj : j < h.txs.length) :
    h.ts[j]'(by simp [BHist.ts, hj]) = j + 1 := by
  simp [BHist.ts]; omega

theorem BHist.exec_eq (h : BHist) {j : Nat} (hj : j < h.txs.length) (i : Nat)
    (v : SIS.View BVal) : h.spec.exec (j + 1) i v = h.txs[j].c := by
  show h.chs.getD (j + 1) { new := [], adds := [] } = h.txs[j].c
  simp [BHist.chs, hj]

/-- The model's run has the history's structures: after the first j
transactions, whatever the algorithm's choices. -/
theorem run_P (h : BHist) (al : SIS.Algo BVal Nat) : ∀ j, j ≤ h.txs.length →
    (SIS.run h.spec al (h.ts.take j)).P = h.P j
  | 0, _ => rfl
  | j + 1, hj => by
    have hjl : j < h.ts.length := by simp [BHist.ts]; omega
    have h1 := SIS.st_succ h.spec al h.ts hjl
    unfold SIS.st at h1
    rw [h1, SIS.step_eq_parts]
    simp only
    rw [SIS.parts_P, SIS.parts_c, run_S_length, run_P h al j (Nat.le_of_succ_le hj), h.P_succ hj]
    have hlen : (h.ts.take j).length = j := by simp [BHist.ts]; omega
    rw [hlen, h.ts_get hj, h.exec_eq hj]

/-- `RunOK` for a bridged history: the model's assumptions on the structure
and on every transaction hold for the model's instance of the history. -/
theorem MeetsBridge.runOK (hm : MeetsBridge p h) (al : SIS.Algo BVal Nat) :
    SIS.RunOK h.spec al h.ts := by
  obtain ⟨r, z, lr, lz, l0, f⟩ := hm.start.facts
  refine ⟨f.specOK, ?_⟩
  intro j hjl
  have hj : j < h.txs.length := by simpa [BHist.ts] using hjl
  simp only
  rw [run_P h al j (Nat.le_of_lt hj), h.ts_get hj, h.exec_eq hj]
  exact (hm.facts j hj).stepOK (hm.binv j (Nat.le_of_lt hj)) (hm.binv (j + 1) hj)

end Run

end Contract
