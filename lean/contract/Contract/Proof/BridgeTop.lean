/-
The contract package (bergdb 030-07): the top's premise of the bridge
(`TopOK`, in the model's words) from the contract's top (bergdb 030-08) and
clause TB (BridgeTop.lean). After every transaction of a history that meets
`MeetsBridgeTop`, the model's root holds one entry for each top node of the
contract's top, each top node of the model holds its root pointer and its
skip pointers, on a level above the earlier ones, and every other node of the
model is a node of the tree (`TopInv`). `top_step` proves the top's clauses
for one more transaction, and `MeetsBridgeTop.meetsBridge` that the history
meets `MeetsBridge`.
-/
import Mathlib.Tactic
import SIS.Proof.VStep
import SIS.Proof.StepFacts
import Contract.BridgeTop
import Contract.TheoremsTop
import Contract.Proof.BridgeStep

namespace Contract

open SIS (Struct Changes Entry History Node NewNode Spec Reach)
open SIS.Check (BVal bptrs blive bspec bstep LState)

/-! ## The entries of the root and of a top node -/

theorem bstep_skips (st : LState) (t : Nat) : ∀ (sk : List (Nat × NodeId × Time)),
    ((sk.map (fun q => BVal.skip q.1 q.2.1)).map (fun v => (⟨t, v⟩ : Entry BVal))).foldl bstep st
      = st
  | [] => rfl
  | _ :: r => by
    simp only [List.map_cons, List.foldl_cons]
    exact bstep_skips st t r

/-- The model's live child of a top node: its root pointer's. -/
theorem blive_topVals (n : TopNode) (t : Nat) :
    blive ((topVals n).map (fun v => (⟨t, v⟩ : Entry BVal))) = [n.root] := by
  rw [SIS.Check.blive_eq]
  simp only [topVals, List.map_cons, List.foldl_cons]
  have h1 : bstep ([], none, none) (⟨t, .rootKey n.root⟩ : Entry BVal) = ([], some n.root, none) :=
    rfl
  rw [h1, bstep_skips]
  rfl

/-- The root's entries for the top nodes of the top. -/
def rootHist (tp : Top) : History BVal := tp.map (fun zm => ⟨zm.2.time, BVal.top zm.1⟩)

/-- The model's live child of the root: the last top node. -/
theorem blive_rootHist {tp : Top} {z : NodeId} {n : TopNode} (hl : tp.getLast? = some (z, n)) :
    blive (rootHist tp) = [z] := by
  rw [SIS.Check.blive_eq, blive_tops]
  · have : (rootHist tp).getLast? = some ⟨n.time, BVal.top z⟩ := by
      unfold rootHist
      rw [List.getLast?_map, hl]
      rfl
    rw [this]
    simp [SIS.Check.bout, bptrs]
    rfl
  · intro e he
    unfold rootHist at he
    obtain ⟨zm, _, rfl⟩ := List.mem_map.mp he
    exact ⟨zm.1, rfl⟩

/-- A pointee of a top node: its root pointer's, or a skip pointer's. -/
theorem mem_ptrs_topVals {n : TopNode} {v : BVal} {y : NodeId} (hv : v ∈ topVals n)
    (hy : y ∈ bptrs v) : y = n.root ∨ ∃ q ∈ n.skips, q.2.1 = y := by
  simp only [topVals, List.mem_cons, List.mem_map] at hv
  rcases hv with rfl | ⟨q, hq, rfl⟩
  · left; simpa [bptrs] using hy
  · right
    simp only [bptrs, List.mem_singleton] at hy
    exact ⟨q, hq, hy.symm⟩

/-- A list of entries for one node, from the values added to it. -/
theorem filter_map_eq {adds : List (NodeId × BVal)} {x : NodeId} {L : List BVal}
    (h : (adds.filter (fun a => a.1 == x)).map (·.2) = L) :
    adds.filter (fun a => a.1 == x) = L.map (fun v => (x, v)) := by
  rw [← h, List.map_map]
  conv_lhs => rw [← List.map_id (adds.filter (fun a => a.1 == x))]
  apply List.map_congr_left
  intro a ha
  have := (List.mem_filter.mp ha).2
  simp only [beq_iff_eq] at this
  obtain ⟨a1, a2⟩ := a
  simp_all

/-! ## The invariant of the top -/

/-- What holds of the model's structure and the contract's top after the first
j transactions. -/
structure TopInv (h : BHist) (top : Nat → Top) (j : Nat) : Prop where
  good : TopGood (top j)
  ne : top j ≠ []
  times : ∀ zm ∈ top j, zm.2.time ≤ j
  roots : (h.tree j).roots = rootsOf (top j)
  rootNode : (h.P j).get? SIS.root =
    some { level := levelIn (h.P j) SIS.root, isData := false, hist := rootHist (top j) }
  topNode : ∀ zm ∈ top j,
    (h.P j).get? zm.1 = some ⟨levelIn (h.P j) zm.1, false,
      (topVals zm.2).map (fun v => ⟨zm.2.time, v⟩)⟩ ∧
    h.topLevel ≤ levelIn (h.P j) zm.1 ∧ levelIn (h.P j) zm.1 < levelIn (h.P j) SIS.root ∧
    zm.1 ≠ SIS.root ∧ (h.tree j).obj zm.1 = none ∧ ((h.tree j).obj zm.2.root).isSome = true
  order : ∀ a ∈ top j, ∀ b ∈ top j, a.2.time < b.2.time →
    levelIn (h.P j) a.1 < levelIn (h.P j) b.1
  other : ∀ x N, (h.P j).get? x = some N → (h.tree j).obj x = none →
    x = SIS.root ∨ ∃ n, (x, n) ∈ top j
  low : ∀ x o, (h.tree j).obj x = some o → lvl o < h.topLevel
  s0 : (h.tree j).obj SIS.root = none
  tpos : 0 < h.topLevel

theorem levelIn_of {P : Struct BVal} {x : NodeId} {N : Node BVal} (h : P.get? x = some N) :
    levelIn P x = N.level := by
  simp [levelIn, h]

section Inv

variable {p : Params} {h : BHist} {top : Nat → Top} {j : Nat}

/-- The last top node, with what the model and the tree hold of it. -/
theorem TopInv.last (ti : TopInv h top j) : ∃ z n, (top j).getLast? = some (z, n) ∧
    (z, n) ∈ top j ∧ (h.tree j).root = some n.root := by
  cases hl : (top j).getLast? with
  | none => exact absurd (List.getLast?_eq_none_iff.mp hl) ti.ne
  | some zn =>
    obtain ⟨z, n⟩ := zn
    refine ⟨z, n, rfl, List.mem_of_getLast? hl, ?_⟩
    unfold Tree.root
    rw [ti.roots]
    unfold rootsOf
    rw [List.getLast?_map, hl]
    rfl

/-- The model reaches the root and the last top node. -/
theorem TopInv.reach_last (ti : TopInv h top j) {z : NodeId} {n : TopNode}
    (hl : (top j).getLast? = some (z, n)) :
    Reach h.spec (h.P j) j SIS.root ∧ Reach h.spec (h.P j) j z ∧
    h.spec.live (History.upTo (rootHist (top j)) j) = [z] ∧
    h.spec.live (History.upTo ((topVals n).map (fun v => (⟨n.time, v⟩ : Entry BVal))) j) =
      [n.root] := by
  have hm := List.mem_of_getLast? hl
  have hup : History.upTo (rootHist (top j)) j = rootHist (top j) := by
    apply SIS.upTo_of_forall
    intro e he
    unfold rootHist at he
    obtain ⟨zm, hzm, rfl⟩ := List.mem_map.mp he
    exact ti.times zm hzm
  have hup2 : History.upTo ((topVals n).map (fun v => (⟨n.time, v⟩ : Entry BVal))) j =
      (topVals n).map (fun v => (⟨n.time, v⟩ : Entry BVal)) := by
    apply SIS.upTo_of_forall
    intro e he
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp he
    exact ti.times _ hm
  have hl0 : h.spec.live (History.upTo (rootHist (top j)) j) = [z] := by
    rw [hup]; exact blive_rootHist hl
  have hr0 : Reach h.spec (h.P j) j SIS.root := Reach.root _ ti.rootNode
  obtain ⟨hz, _, hlt, _⟩ := ti.topNode _ hm
  refine ⟨hr0, ?_, hl0, ?_⟩
  · exact Reach.child hr0 ti.rootNode (by rw [hl0]; exact List.mem_singleton_self z) hz hlt
  · rw [hup2]; exact blive_topVals n n.time

/-- The link of the model's top to the tree's space root, from the invariant
of the top and the tree's invariants. -/
theorem TopInv.link (ti : TopInv h top j) (hinv : invOk p (h.tree j) = true) :
    TopLink h.spec (h.P j) j (h.tree j) := by
  obtain ⟨z, n, hl, hm, hroot⟩ := ti.last
  obtain ⟨_, _, hl0, hly⟩ := ti.reach_last hl
  obtain ⟨hz, hge, hlt, _, hsz, _⟩ := ti.topNode _ hm
  unfold invOk at hinv
  rw [hroot] at hinv
  simp only at hinv
  cases hy : (h.tree j).obj n.root with
  | none => rw [hy] at hinv; simp at hinv
  | some o =>
    cases o with
    | val v => rw [hy] at hinv; simp at hinv
    | key ny =>
      have hlow := ti.low _ _ hy
      exact ⟨_, z, _, n.root, ny, ti.rootNode, hl0, hz, hlt, hly, hroot, hy,
        Nat.lt_of_lt_of_le hlow hge, ti.s0, hsz⟩

end Inv

/-! ## The start -/

theorem topInv_start {h : BHist} {top : Nat → Top} {r z lr lz l0 : Nat}
    (f : StartFacts h r z lr lz l0) (hadds : h.c0.adds = [(0, .top z), (z, .rootKey r)])
    (ht : topStartOk h.c0 (top 0) h.s0 = true) : TopInv h top 0 := by
  unfold topStartOk at ht
  rw [hadds] at ht
  cases htp : top 0 with
  | nil => rw [htp] at ht; simp at ht
  | cons zn rest =>
    cases rest with
    | cons _ _ => rw [htp] at ht; simp at ht
    | nil =>
      obtain ⟨z', n⟩ := zn
      rw [htp] at ht
      simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at ht
      obtain ⟨⟨⟨hz', htime⟩, hsk⟩, hroots⟩ := ht
      subst hz'
      have hroot : n.root = r := by
        rw [f.roots] at hroots
        simp only [rootsOf, List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq,
          and_true] at hroots
        exact hroots.2.symm
      have hP0 : h.P 0 = h.p0 := rfl
      have hlev0 : levelIn (h.P 0) SIS.root = l0 := levelIn_of f.get0
      have hlevz : levelIn (h.P 0) z' = lz := levelIn_of f.getz
      have htl : h.topLevel = lz := f.top
      have hr0 : (0 : Nat) ≠ r := fun h => f.hr h.symm
      have hgood : TopGood [(z', n)] := by
        have hok : skipsOk [] n = true := by simp [skipsOk, hsk, strictUp]
        have hg := TopGood.snoc [] z' n TopGood.nil (by simp [Top.node, List.lookup]) (by simp) hok
        simpa using hg
      refine { good := by rw [htp]; exact hgood, ne := by rw [htp]; simp, times := ?_,
               roots := by rw [htp]; exact hroots, rootNode := ?_, topNode := ?_, order := ?_,
               other := ?_, low := ?_, s0 := f.none _ hr0, tpos := ?_ }
      · intro zm hzm
        rw [htp] at hzm
        simp only [List.mem_singleton] at hzm
        rw [hzm]
        exact Nat.le_of_eq htime
      · rw [hlev0, htp]
        have := f.get0
        simp only [rootHist, List.map_cons, List.map_nil, htime]
        exact this
      · intro zm hzm
        rw [htp] at hzm
        simp only [List.mem_singleton] at hzm
        subst hzm
        refine ⟨?_, ?_, ?_, f.hz, f.none _ f.hzr, ?_⟩
        · rw [hlevz]
          have := f.getz
          simp only [topVals, hsk, List.map_nil, List.map_cons, htime, hroot]
          exact this
        · rw [hlevz, htl]
        · rw [hlevz, hlev0]; exact f.hlz0
        · show (h.s0.obj n.root).isSome = true
          rw [hroot, f.obj]; rfl
      · intro a ha b hb hlt
        rw [htp] at ha hb
        simp only [List.mem_singleton] at ha hb
        rw [ha, hb] at hlt
        exact absurd hlt (Nat.lt_irrefl _)
      · intro x N hx hno
        rw [hP0] at hx
        have hmem := SIS.mem_of_get? hx
        rcases f.mem hmem with h1 | h1 | h1
        · left
          injection h1 with h1
        · exfalso
          injection h1 with h1
          have : h.s0.obj x = none := hno
          rw [h1, f.obj] at this
          cases this
        · right
          injection h1 with h1
          exact ⟨n, by rw [htp, h1]; simp⟩
      · intro x o hx
        have hx' : h.s0.obj x = some o := hx
        by_cases hxr : x = r
        · rw [hxr, f.obj] at hx'
          injection hx' with hx'
          rw [← hx', htl]
          exact f.hlrz
        · rw [f.none x hxr] at hx'; cases hx'
      · rw [htl]
        have := f.hlr
        have := f.hlrz
        omega

/-! ## One transaction -/

/-- The top node that a transaction makes, if any, as a list. -/
def ntTops : Option (NodeId × TopNode × Nat) → Top
  | none => []
  | some (z, n, _) => [(z, n)]

/-- The node of the model that a transaction makes for it. -/
def ntNews : Option (NodeId × TopNode × Nat) → List NewNode
  | none => []
  | some (z, _, lv) => [⟨z, lv, false⟩]

/-- The root's entry values for it. -/
def ntRoot : Option (NodeId × TopNode × Nat) → List BVal
  | none => []
  | some (z, _, _) => [BVal.top z]

/-- What the change does to the nodes that are no nodes of the tree: nothing,
or it makes the top node z with the node n of the contract's top, on the
level lv. -/
structure NonTree (h : BHist) (top : Nat → Top) (j : Nat) (hj : j < h.txs.length)
    (nt : Option (NodeId × TopNode × Nat)) : Prop where
  tops : top (j + 1) = top j ++ ntTops nt
  news : h.txs[j].c.new.filter (fun nn => ((h.tree (j + 1)).obj nn.id).isNone) = ntNews nt
  adds : ∀ a ∈ h.txs[j].c.adds, (h.tree (j + 1)).obj a.1 = none →
    ∃ z n lv, nt = some (z, n, lv) ∧ (a.1 = z ∨ a.1 = SIS.root)
  made : ∀ z n lv, nt = some (z, n, lv) →
    n.time = j + 1 ∧ skipsOk (top j) n = true ∧ (top j).node z = none ∧
    (∀ zm ∈ top j, levelIn (h.P j) zm.1 < lv) ∧ lv < levelIn (h.P j) SIS.root ∧
    (h.txs[j].c.adds.filter (fun a => a.1 == z)).map (·.2) = topVals n ∧
    (h.txs[j].c.adds.filter (fun a => a.1 == SIS.root)).map (·.2) = [.top z]

/-- Clause TB and 030-08's step of the top give the change's part for the
nodes that are no nodes of the tree. -/
theorem nonTree_of {h : BHist} {top : Nat → Top} {j : Nat} (hj : j < h.txs.length)
    (hts : TopStep (j + 1) (top j) (top (j + 1)))
    (htb : (if top (j + 1) == top j then
        h.txs[j].c.new.all (fun nn => ((h.tree (j + 1)).obj nn.id).isSome) &&
          h.txs[j].c.adds.all (fun a => ((h.tree (j + 1)).obj a.1).isSome)
      else
        match (top (j + 1)).getLast?,
          h.txs[j].c.new.filter (fun nn => ((h.tree (j + 1)).obj nn.id).isNone) with
        | some (z, n), [nn] =>
          nn.id == z && (top j).all (fun zm => decide (levelIn (h.P j) zm.1 < nn.level)) &&
          decide (nn.level < levelIn (h.P j) SIS.root) &&
          (h.txs[j].c.adds.filter (fun a => a.1 == z)).map (·.2) == topVals n &&
          (h.txs[j].c.adds.filter (fun a => a.1 == SIS.root)).map (·.2) == [.top z] &&
          h.txs[j].c.adds.all (fun a => ((h.tree (j + 1)).obj a.1).isSome || a.1 == z ||
            a.1 == SIS.root)
        | _, _ => false) = true)
    (hnd : ∀ nn ∈ h.txs[j].c.new, (h.tree (j + 1)).obj nn.id = none → nn.isData = false) :
    ∃ nt, NonTree h top j hj nt := by
  rcases hts with hA | ⟨z, n, hB, hznone, htime, hskips⟩
  · refine ⟨none, ?_⟩
    simp only [hA, beq_self_eq_true, ite_true, Bool.and_eq_true, List.all_eq_true] at htb
    refine { tops := by simp [hA, ntTops], news := ?_, adds := ?_, made := by intro z n lv h; cases h }
    · show _ = []
      rw [List.filter_eq_nil_iff]
      intro nn hnn hno
      have := htb.1 nn hnn
      rw [Option.isNone_iff_eq_none.mp hno] at this
      cases this
    · intro a ha hno
      have := htb.2 a ha
      rw [hno] at this
      cases this
  · have hne : (top (j + 1) == top j) = false := by
      rw [beq_eq_false_iff_ne]
      intro heq
      have := congrArg List.length heq
      rw [hB] at this
      simp at this
    have hlast : (top (j + 1)).getLast? = some (z, n) := by rw [hB]; simp
    simp only [hne, Bool.false_eq_true, ite_false, hlast] at htb
    cases hf : h.txs[j].c.new.filter (fun nn => ((h.tree (j + 1)).obj nn.id).isNone) with
    | nil => rw [hf] at htb; simp at htb
    | cons nn rest =>
      cases rest with
      | cons _ _ => rw [hf] at htb; simp at htb
      | nil =>
        rw [hf] at htb
        simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
          Bool.or_eq_true] at htb
        obtain ⟨⟨⟨⟨⟨hid, hlev⟩, hlt⟩, haz⟩, har⟩, hall⟩ := htb
        have hmem : nn ∈ h.txs[j].c.new.filter (fun nn => ((h.tree (j + 1)).obj nn.id).isNone) := by
          rw [hf]; exact List.mem_singleton_self nn
        have hnn := List.mem_filter.mp hmem
        have hdata := hnd nn hnn.1 (Option.isNone_iff_eq_none.mp hnn.2)
        have hnneq : nn = ⟨z, nn.level, false⟩ := by
          cases nn
          simp_all
        refine ⟨some (z, n, nn.level), ?_⟩
        refine { tops := hB, news := by rw [hf]; show [nn] = [_]; rw [← hnneq], adds := ?_, made := ?_ }
        · intro a ha hno
          refine ⟨z, n, nn.level, rfl, ?_⟩
          rcases hall a ha with (h1 | h1) | h1
          · rw [hno] at h1; cases h1
          · exact Or.inl h1
          · exact Or.inr h1
        · intro z' n' lv' heq
          injection heq with heq
          injection heq with h1 h2
          injection h2 with h2 h3
          subst h1 h2 h3
          exact ⟨htime, hskips, hznone, hlev, hlt, haz, har⟩

section Step

variable {p : Params} {h : BHist} {top : Nat → Top} {j : Nat} {hj : j < h.txs.length}

/-- From a top node, the model's top closure holds every top node that the
skip pointers reach. -/
theorem skipPath_closure (ti : TopInv h top j) {a b : NodeId} (hp : SkipPath (top j) a b) :
    ∀ na, (a, na) ∈ top j → ∀ Na, (h.P j).get? a = some Na →
      b ∈ SIS.topClosure h.spec (h.P j) a Na := by
  induction hp with
  | refl z =>
    intro na _ Na _
    rw [SIS.topClosure_eq]
    exact List.mem_cons_self
  | step z n q y hz hq _ ih =>
    intro na hna Na hNa
    have hna' : n = na := by
      have := hz.symm.trans (ti.good.lookup hna)
      simpa using this
    subst hna'
    obtain ⟨ny, hym, _, hlt⟩ := ti.good.skip hna hq
    obtain ⟨hN, _, _, _⟩ := ti.topNode _ hna
    rw [hN] at hNa
    injection hNa with hNa
    subst hNa
    obtain ⟨hNy, hge, _, _⟩ := ti.topNode _ hym
    rw [SIS.topClosure_eq]
    apply List.mem_cons_of_mem
    rw [List.mem_flatMap]
    refine ⟨q.2.1, ?_, ?_⟩
    · simp only [SIS.pointees, List.mem_eraseDups, List.mem_flatMap]
      refine ⟨⟨n.time, .skip q.1 q.2.1⟩, ?_, by simp [BHist.spec, bspec, bptrs]⟩
      apply List.mem_map.mpr
      exact ⟨.skip q.1 q.2.1, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q, hq, rfl⟩), rfl⟩
    · rw [hNy]
      have hlev := ti.order _ hym _ hna hlt
      have hge' : h.spec.topLevel ≤ levelIn (h.P j) q.2.1 := hge
      simp only [hge', hlev, and_self, ite_true]
      exact ih ny hym _ hNy

/-- The top's clauses of the bridge (`TopOK`) for one more transaction, from
the contract's top and clause TB; with them the invariants after it. -/
theorem top_step (hi : BInv h j) (ti : TopInv h top j)
    (hc : Contract p (j + 1) (h.tree j) h.txs[j].ops h.txs[j].D (h.tree (j + 1)))
    (hb : bridgeOk h.topLevel (j + 1) (h.tree j) (h.tree (j + 1)) h.txs[j].D h.txs[j].c = true)
    (hmade : Made (h.tree j) (h.tree (j + 1)) h.txs[j].c)
    (hts : TopStep (j + 1) (top j) (top (j + 1)))
    (hroots : (h.tree (j + 1)).roots = rootsOf (top (j + 1)))
    (htb : topChangeOk h.topLevel (h.P j) (h.tree (j + 1)) (top j) (top (j + 1)) h.txs[j].c
      = true) :
    TopOK h.spec (h.P j) (j + 1) (h.tree j) (h.tree (j + 1)) h.txs[j].c ∧
    TopInv h top (j + 1) ∧ BInv h (j + 1) := by
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := bridgeOk_parts hb
  simp only [Nat.add_sub_cancel] at b6
  simp only [topChangeOk, Bool.and_eq_true] at htb
  obtain ⟨tb1, tb2⟩ := htb
  have hnews := b1
  simp only [newsOk, Bool.and_eq_true, decide_eq_true_eq] at hnews
  obtain ⟨f1, f2, f3⟩ := hc.2
  have hP' := h.P_succ hj
  -- TB1, for each node made.
  have hnew : ∀ nn ∈ h.txs[j].c.new, nn.id ≠ SIS.root ∧ (top j).node nn.id = none ∧
      (((h.tree (j + 1)).obj nn.id).isSome = true → nn.level < h.topLevel) := by
    intro nn hnn
    have := List.all_eq_true.mp tb1 nn hnn
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Option.isNone_iff_eq_none, Bool.or_eq_true,
      decide_eq_true_eq] at this
    refine ⟨this.1.1, this.1.2, ?_⟩
    intro hs
    rcases this.2 with h1 | h1
    · rw [h1] at hs; cases hs
    · exact h1
  -- Clause N, for each node made.
  have hkind : ∀ nn ∈ h.txs[j].c.new, (h.tree j).obj nn.id = none ∧
      (∀ n, (h.tree (j + 1)).obj nn.id = some (.key n) → nn.level = n.level) ∧
      ((h.tree (j + 1)).obj nn.id = none → h.topLevel ≤ nn.level ∧ nn.isData = false) := by
    intro nn hnn
    have := List.all_eq_true.mp hnews.2 nn hnn
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at this
    refine ⟨this.1, ?_, ?_⟩
    · intro n hn
      have h2 := this.2
      rw [hn] at h2
      simp only [Bool.and_eq_true, beq_iff_eq] at h2
      exact h2.1
    · intro hno
      have h2 := this.2
      rw [hno] at h2
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h2
      exact h2
  -- A node of the model that is no node of the tree stays none.
  have stays : ∀ x, (x = SIS.root ∨ ∃ n, (x, n) ∈ top j) → (h.tree (j + 1)).obj x = none := by
    intro x hx
    by_contra hne
    have hsome : ((h.tree (j + 1)).obj x).isSome = true := by
      cases ho : (h.tree (j + 1)).obj x with
      | none => exact absurd ho hne
      | some _ => rfl
    have hno : (h.tree j).obj x = none := by
      rcases hx with rfl | ⟨n, hm⟩
      · exact ti.s0
      · exact (ti.topNode _ hm).2.2.2.2.1
    obtain ⟨nn, hnn, hid⟩ := List.mem_map.mp (hmade x hno hsome)
    have h1 := hnew nn hnn
    rw [hid] at h1
    rcases hx with rfl | ⟨n, hm⟩
    · exact h1.1 rfl
    · rw [ti.good.lookup hm] at h1
      cases h1.2.1
  -- The ids made are new in the model.
  have fresh : ∀ nn ∈ h.txs[j].c.new, (h.tree j).obj nn.id = none →
      (h.P j).get? nn.id = none := by
    intro nn hnn hno
    by_contra hne
    obtain ⟨N, hN⟩ := Option.ne_none_iff_exists'.mp hne
    have h1 := hnew nn hnn
    rcases ti.other _ N hN hno with h2 | ⟨n, hm⟩
    · exact h1.1 h2
    · rw [ti.good.lookup hm] at h1
      cases h1.2.1
  have tf : TreeFacts p h j hj :=
    { contract := hc, news := b1, adds := b2, loc := b3, cur := b4, mkd := b5, nores := b6,
      made := hmade, fresh := fresh }
  have rep' := tf.rep hi.rep
  have timely' := tf.timely hi.timely
  have wf' := tf.wf hi.wf
  have lev' := tf.lev hi.lev
  have hinv' : invOk p (h.tree (j + 1)) = true := by
    have := hc.1
    simp only [contractOk, Bool.and_eq_true] at this
    rw [← timely'.at_eq]
    exact this.1
  -- A node of the tree is below the top nodes' level.
  have low' : ∀ x o, (h.tree (j + 1)).obj x = some o → lvl o < h.topLevel := by
    intro x o' hx
    cases ho : (h.tree j).obj x with
    | some o =>
      obtain ⟨o'', ho'', hext, _⟩ := f1 x o ho
      rw [hx] at ho''
      injection ho'' with ho''
      subst ho''
      rw [hext.lvl]
      exact ti.low x o ho
    | none =>
      obtain ⟨nn, hnn, hid⟩ := List.mem_map.mp (hmade x ho (by rw [hx]; rfl))
      cases o' with
      | val v => exact ti.tpos
      | key n =>
        have h1 := (hkind nn hnn).2.1 n (by rw [hid]; exact hx)
        have h2 := (hnew nn hnn).2.2 (by rw [hid, hx]; rfl)
        show n.level < h.topLevel
        omega
  obtain ⟨nt, hnt⟩ := nonTree_of hj hts tb2 (fun nn hnn hno => ((hkind nn hnn).2.2 hno).2)
  -- The model's structure after the change, at the root and the top nodes.
  have getOld : ∀ x N, (h.P j).get? x = some N → (h.P (j + 1)).get? x =
      some ⟨N.level, N.isData, N.hist ++
        ((h.txs[j].c.adds.filter (fun a => a.1 == x)).map (·.2)).map
          (fun v => (⟨j + 1, v⟩ : Entry BVal))⟩ := by
    intro x N hN
    rw [hP', SIS.get?_apply_of_get? hN, addsFor_eq]
  have noAdds : ∀ x, (h.tree (j + 1)).obj x = none →
      (∀ z n lv, nt = some (z, n, lv) → x ≠ z ∧ x ≠ SIS.root) →
      h.txs[j].c.adds.filter (fun a => a.1 == x) = [] := by
    intro x hno hx
    rw [List.filter_eq_nil_iff]
    intro a ha hax
    have hax' : a.1 = x := by simpa using hax
    obtain ⟨z, n, lv, hnt', hcase⟩ := hnt.adds a ha (by rw [hax']; exact hno)
    have := hx z n lv hnt'
    rcases hcase with h1 | h1
    · exact this.1 (hax'.symm.trans h1)
    · exact this.2 (hax'.symm.trans h1)
  -- An old top node is as it was.
  have oldTop : ∀ zm ∈ top j, (h.P (j + 1)).get? zm.1 = (h.P j).get? zm.1 := by
    intro zm hzm
    obtain ⟨hN, _, _, hne, _, _⟩ := ti.topNode zm hzm
    rw [getOld _ _ hN, noAdds zm.1 (stays _ (Or.inr ⟨zm.2, hzm⟩)) ?_, hN]
    · simp
    · intro z n lv hnt'
      refine ⟨?_, hne⟩
      rintro rfl
      have := (hnt.made _ n lv hnt').2.2.1
      rw [ti.good.lookup hzm] at this
      cases this
  have oldLev : ∀ zm ∈ top j, levelIn (h.P (j + 1)) zm.1 = levelIn (h.P j) zm.1 := by
    intro zm hzm
    simp only [levelIn, oldTop zm hzm]
  -- The root after the change.
  have rootAdds : (h.txs[j].c.adds.filter (fun a => a.1 == SIS.root)).map (·.2) = ntRoot nt := by
    cases hnt' : nt with
    | none =>
      rw [noAdds SIS.root (stays _ (Or.inl rfl)) (by intro z n lv h1; rw [hnt'] at h1; cases h1)]
      rfl
    | some t =>
      obtain ⟨z, n, lv⟩ := t
      exact (hnt.made z n lv hnt').2.2.2.2.2.2
  have rootNode' : (h.P (j + 1)).get? SIS.root =
      some ⟨levelIn (h.P j) SIS.root, false, rootHist (top (j + 1))⟩ := by
    rw [getOld _ _ ti.rootNode, rootAdds, hnt.tops]
    cases hnt' : nt with
    | none => simp [rootHist, ntRoot, ntTops]
    | some t =>
      obtain ⟨z, n, lv⟩ := t
      have := (hnt.made z n lv hnt').1
      simp [rootHist, ntRoot, ntTops, this]
  have rootLev' : levelIn (h.P (j + 1)) SIS.root = levelIn (h.P j) SIS.root :=
    levelIn_of rootNode'
  -- The top node made.
  have newTop : ∀ z n lv, nt = some (z, n, lv) →
      (⟨z, lv, false⟩ : NewNode) ∈ h.txs[j].c.new ∧ (h.tree (j + 1)).obj z = none ∧
      (h.P j).get? z = none ∧ h.topLevel ≤ lv ∧ z ≠ SIS.root ∧
      (h.P (j + 1)).get? z =
        some ⟨lv, false, (topVals n).map (fun v => (⟨n.time, v⟩ : Entry BVal))⟩ := by
    intro z n lv hnt'
    have hmem : (⟨z, lv, false⟩ : NewNode) ∈ h.txs[j].c.new.filter
        (fun nn => ((h.tree (j + 1)).obj nn.id).isNone) := by
      rw [hnt.news, hnt']; exact List.mem_singleton_self _
    obtain ⟨hin, hno⟩ := List.mem_filter.mp hmem
    have hno' : (h.tree (j + 1)).obj z = none := Option.isNone_iff_eq_none.mp hno
    have hk := hkind _ hin
    have hfr := fresh _ hin hk.1
    have hm := hnt.made z n lv hnt'
    refine ⟨hin, hno', hfr, (hk.2.2 hno').1, (hnew _ hin).1, ?_⟩
    rw [hP', SIS.get?_apply, hfr, newNodeOf_mem hnews.1 hin, addsFor_eq, hm.2.2.2.2.2.1, hm.1]
    simp
  -- The invariant of the top after the transaction.
  have memTop' : ∀ zm, zm ∈ top (j + 1) ↔ zm ∈ top j ∨ ∃ lv, nt = some (zm.1, zm.2, lv) := by
    intro zm
    rw [hnt.tops, List.mem_append]
    cases hnt' : nt with
    | none => simp [ntTops]
    | some t =>
      obtain ⟨z, n, lv⟩ := t
      simp only [ntTops, List.mem_singleton, Option.some.injEq, Prod.mk.injEq]
      constructor
      · rintro (h1 | h1)
        · exact Or.inl h1
        · right
          subst h1
          exact ⟨lv, rfl, rfl, rfl⟩
      · rintro (h1 | ⟨lv', h1, h2, _⟩)
        · exact Or.inl h1
        · right
          obtain ⟨a, b⟩ := zm
          simp_all
  have good' : TopGood (top (j + 1)) := by
    rw [hnt.tops]
    cases hnt' : nt with
    | none => simpa [ntTops] using ti.good
    | some t =>
      obtain ⟨z, n, lv⟩ := t
      have hm := hnt.made z n lv hnt'
      exact TopGood.snoc _ z n ti.good hm.2.2.1
        (fun zm hzm => by have := ti.times zm hzm; rw [hm.1]; exact Nat.lt_succ_of_le this) hm.2.1
  have times' : ∀ zm ∈ top (j + 1), zm.2.time ≤ j + 1 := by
    intro zm hzm
    rcases (memTop' zm).mp hzm with h1 | ⟨lv, h1⟩
    · exact Nat.le_succ_of_le (ti.times zm h1)
    · exact Nat.le_of_eq (hnt.made _ _ lv h1).1
  have rootIn' : ∀ zm ∈ top (j + 1), ((h.tree (j + 1)).obj zm.2.root).isSome = true := by
    intro zm hzm
    rcases (memTop' zm).mp hzm with h1 | ⟨lv, h1⟩
    · have := (ti.topNode zm h1).2.2.2.2.2
      obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp this
      obtain ⟨o', ho', _⟩ := f1 _ o ho
      rw [ho']; rfl
    · -- the top node made names the space root
      have hlast : (top (j + 1)).getLast? = some zm := by
        rw [hnt.tops, h1]; simp [ntTops]
      have hroot : (h.tree (j + 1)).root = some zm.2.root := by
        unfold Tree.root
        rw [hroots]
        unfold rootsOf
        rw [List.getLast?_map, hlast]
        rfl
      unfold invOk at hinv'
      rw [hroot] at hinv'
      simp only at hinv'
      cases hy : (h.tree (j + 1)).obj zm.2.root with
      | none => rw [hy] at hinv'; simp at hinv'
      | some o => rfl
  have ti' : TopInv h top (j + 1) := by
    refine { good := good', ne := ?_, times := times', roots := hroots,
             rootNode := by rw [rootLev']; exact rootNode', topNode := ?_, order := ?_,
             other := ?_, low := low', s0 := stays _ (Or.inl rfl), tpos := ti.tpos }
    · rw [hnt.tops]
      intro hnil
      exact ti.ne (List.append_eq_nil_iff.mp hnil).1
    · intro zm hzm
      rcases (memTop' zm).mp hzm with h1 | ⟨lv, h1⟩
      · obtain ⟨hN, hge, hlt, hne, _, _⟩ := ti.topNode zm h1
        rw [oldTop zm h1, oldLev zm h1, rootLev']
        exact ⟨hN, hge, hlt, hne, stays _ (Or.inr ⟨zm.2, h1⟩), rootIn' zm hzm⟩
      · obtain ⟨_, hno, _, hge, hne, hN⟩ := newTop _ _ lv h1
        have hl : levelIn (h.P (j + 1)) zm.1 = lv := levelIn_of hN
        rw [hl, rootLev']
        exact ⟨hN, hge, (hnt.made _ _ lv h1).2.2.2.2.1, hne, hno, rootIn' zm hzm⟩
    · intro a ha b hb hlt
      rcases (memTop' a).mp ha with h1 | ⟨lva, h1⟩
      · rcases (memTop' b).mp hb with h2 | ⟨lvb, h2⟩
        · rw [oldLev a h1, oldLev b h2]
          exact ti.order a h1 b h2 hlt
        · obtain ⟨_, _, _, _, _, hN⟩ := newTop _ _ lvb h2
          rw [oldLev a h1, levelIn_of hN]
          exact (hnt.made _ _ lvb h2).2.2.2.1 a h1
      · exfalso
        have hta := (hnt.made _ _ lva h1).1
        have := times' b hb
        rw [hta] at hlt
        exact absurd hlt (Nat.not_lt.mpr this)
    · intro x N' hx hno
      rw [hP', SIS.get?_apply] at hx
      cases hPx : (h.P j).get? x with
      | some N =>
        have hsno : (h.tree j).obj x = none := by
          cases ho : (h.tree j).obj x with
          | none => rfl
          | some o =>
            obtain ⟨o', ho', _⟩ := f1 x o ho
            rw [hno] at ho'; cases ho'
        rcases ti.other x N hPx hsno with h1 | ⟨n, hm⟩
        · exact Or.inl h1
        · exact Or.inr ⟨n, (memTop' (x, n)).mpr (Or.inl hm)⟩
      | none =>
        rw [hPx] at hx
        simp only [Option.none_or, Option.map_eq_some_iff] at hx
        obtain ⟨m, hm, _⟩ := hx
        obtain ⟨nn, hnn, hid, _⟩ := SIS.newNodeOf_some hm
        have hmem : nn ∈ h.txs[j].c.new.filter
            (fun nn => ((h.tree (j + 1)).obj nn.id).isNone) :=
          List.mem_filter.mpr ⟨hnn, by rw [hid, hno]; rfl⟩
        rw [hnt.news] at hmem
        cases hnt' : nt with
        | none => rw [hnt'] at hmem; simp [ntNews] at hmem
        | some t =>
          obtain ⟨z, n, lv⟩ := t
          rw [hnt'] at hmem
          simp only [ntNews, List.mem_singleton] at hmem
          right
          refine ⟨n, (memTop' (x, n)).mpr (Or.inr ⟨lv, ?_⟩)⟩
          rw [hnt', ← hid, hmem]
  have link' := ti'.link hinv'
  have hi' : BInv h (j + 1) := ⟨rep', timely', wf', lev', link'⟩
  obtain ⟨zl, nl, hlast', hml', hroot'⟩ := ti'.last
  obtain ⟨hr0', hrz', hl0', hly'⟩ := ti'.reach_last hlast'
  obtain ⟨hzl', _, _, _, _, _⟩ := ti'.topNode _ hml'
  -- What the model reaches after the transaction that is no node of the tree.
  have reachNT : ∀ y, (h.tree (j + 1)).obj y = none →
      SIS.reachable h.spec (h.P (j + 1)) (j + 1) y = true → y = SIS.root ∨ y = zl := by
    intro y hno hy
    rw [SIS.reachable_iff] at hy
    cases hyo : (h.tree (j + 1)).obj nl.root with
    | none =>
      have := rootIn' _ hml'
      rw [hyo] at this; cases this
    | some o =>
      cases o with
      | val v =>
        unfold invOk at hinv'
        rw [hroot'] at hinv'
        simp only at hinv'
        rw [hyo] at hinv'
        simp at hinv'
      | key ny =>
        rcases hi'.reach3 ti'.rootNode hl0' hzl' hly' hroot' hyo hy with h1 | h1 | h1
        · exact Or.inl h1
        · exact Or.inr h1
        · have := hi'.reach_obj h1
          rw [hno] at this; cases this
  -- A node made on the top nodes' level or above is the top node made.
  have isNew : ∀ nn ∈ h.txs[j].c.new, h.topLevel ≤ nn.level →
      ∃ z n lv, nt = some (z, n, lv) ∧ nn = ⟨z, lv, false⟩ := by
    intro nn hnn hl
    have hno : (h.tree (j + 1)).obj nn.id = none := by
      cases ho : (h.tree (j + 1)).obj nn.id with
      | none => rfl
      | some o =>
        have := (hnew nn hnn).2.2 (by rw [ho]; rfl)
        omega
    have hmem : nn ∈ h.txs[j].c.new.filter (fun nn => ((h.tree (j + 1)).obj nn.id).isNone) :=
      List.mem_filter.mpr ⟨hnn, by rw [hno]; rfl⟩
    rw [hnt.news] at hmem
    cases hnt' : nt with
    | none => rw [hnt'] at hmem; simp [ntNews] at hmem
    | some t =>
      obtain ⟨z, n, lv⟩ := t
      rw [hnt'] at hmem
      exact ⟨z, n, lv, rfl, List.mem_singleton.mp hmem⟩
  -- If a top node is made, it is the last one.
  have lastNew : ∀ z n lv, nt = some (z, n, lv) → zl = z := by
    intro z n lv hnt'
    have : (top (j + 1)).getLast? = some (z, n) := by rw [hnt.tops, hnt']; simp [ntTops]
    rw [hlast'] at this
    injection this with this
    injection this
  have hspecTop : h.spec.topLevel = h.topLevel := rfl
  refine ⟨{ virt := ?_, fresh := fresh, current := ?_, dataFixed := ?_, levels := ?_,
            newReachable := ?_, noRes := ?_, link := by rw [← hP']; exact link' }, ti', hi'⟩
  · -- VirtStep
    refine { newTop := ?_, topFixed := ?_, rootAdds := ?_, closure := ?_, dead := ?_ }
    · intro nn hnn hl
      obtain ⟨z, n, lv, hnt', hnneq⟩ := isNew nn hnn hl
      refine ⟨by rw [hnneq], ?_, ?_⟩
      · have hm := (hnt.made z n lv hnt').2.2.2.2.2.1
        have hne : h.txs[j].c.adds.filter (fun a => a.1 == z) ≠ [] := by
          intro hnil
          rw [hnil] at hm
          simp [topVals] at hm
        obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ hne
        obtain ⟨ha1, ha2⟩ := List.mem_filter.mp ha
        exact ⟨a, ha1, by rw [hnneq]; simpa using ha2⟩
      · intro nn' hnn' hl'
        obtain ⟨z', n', lv', hnt'', hnneq'⟩ := isNew nn' hnn' hl'
        rw [hnt'] at hnt''
        injection hnt'' with h1
        injection h1 with h1 h2
        injection h2 with h2 h3
        rw [hnneq, hnneq', h1, h3]
    · intro a ha N hN hne
      rw [hspecTop]
      cases ho' : (h.tree (j + 1)).obj a.1 with
      | none =>
        exfalso
        obtain ⟨z, n, lv, hnt', hcase⟩ := hnt.adds a ha ho'
        rcases hcase with h1 | h1
        · rw [h1, (newTop z n lv hnt').2.2.1] at hN; cases hN
        · exact hne h1
      | some o' =>
        cases ho : (h.tree j).obj a.1 with
        | none =>
          exfalso
          obtain ⟨nn, hnn, hid⟩ := List.mem_map.mp (hmade a.1 ho (by rw [ho']; rfl))
          have := fresh nn hnn (by rw [hid]; exact ho)
          rw [hid, hN] at this; cases this
        | some o =>
          obtain ⟨M, hM, hMl⟩ := hi.node_of ho
          rw [hN] at hM
          injection hM with hM
          rw [hM, hMl]
          exact ti.low _ _ ho
    · -- rootAdds
      have hL := filter_map_eq rootAdds
      rw [hL]
      have hfilter : h.txs[j].c.new.filter (fun nn => decide (h.spec.topLevel ≤ nn.level)) =
          h.txs[j].c.new.filter (fun nn => ((h.tree (j + 1)).obj nn.id).isNone) := by
        apply List.filter_congr
        intro nn hnn
        cases ho : (h.tree (j + 1)).obj nn.id with
        | none =>
          have := ((hkind nn hnn).2.2 ho).1
          simp [hspecTop, this]
        | some o =>
          have := (hnew nn hnn).2.2 (by rw [ho]; rfl)
          simp only [Option.isNone_some, decide_eq_false_iff_not, hspecTop]
          omega
      rw [hfilter, hnt.news]
      cases nt with
      | none => rfl
      | some t =>
        obtain ⟨z, n, lv⟩ := t
        rfl
    · -- closure
      intro nn hnn hl N hN y m hy hne hlm
      obtain ⟨z, n, lv, hnt', hnneq⟩ := isNew nn hnn hl
      have hid : nn.id = z := by rw [hnneq]
      rw [hid] at hN ⊢
      rw [← hP'] at hN ⊢
      have hsno : (h.tree j).obj y = none := by
        cases ho : (h.tree j).obj y with
        | none => rfl
        | some o =>
          obtain ⟨M, hM, hMl⟩ := hi.node_of ho
          rw [hy] at hM
          injection hM with hM
          have := ti.low _ _ ho
          rw [hspecTop] at hlm
          rw [← hMl, ← hM] at this
          omega
      rcases ti.other y m hy hsno with h1 | ⟨ny, hym⟩
      · exact absurd h1 hne
      · have hzm : (z, n) ∈ top (j + 1) := (memTop' (z, n)).mpr (Or.inr ⟨lv, hnt'⟩)
        have hym' : (y, ny) ∈ top (j + 1) := (memTop' (y, ny)).mpr (Or.inl hym)
        have hle : ny.time ≤ n.time := by
          have h3 := ti.times _ hym
          have h4 := (hnt.made z n lv hnt').1
          rw [h4]
          exact Nat.le_succ_of_le h3
        have hpath := good'.skipPath n.time z n rfl hzm y ny hym' hle
        exact skipPath_closure ti' hpath n hzm N hN
    · -- dead
      intro z1 N1 hz1 htop y hy hytop
      rw [← hP'] at hz1 htop hytop ⊢
      simp only [SIS.isTop, hz1, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at htop
      have hno1 : (h.tree (j + 1)).obj z1 = none := by
        cases ho : (h.tree (j + 1)).obj z1 with
        | none => rfl
        | some o =>
          obtain ⟨M, hM, hMl⟩ := hi'.node_of ho
          rw [hz1] at hM
          injection hM with hM
          have := low' _ _ ho
          have h2 := htop.2
          rw [hspecTop] at h2
          rw [← hMl, ← hM] at this
          omega
      rcases ti'.other z1 N1 hz1 hno1 with h1 | ⟨n1, hm1⟩
      · exact absurd h1 htop.1
      · obtain ⟨hN1, _, _, _, _, hrootIn⟩ := ti'.topNode _ hm1
        rw [hz1] at hN1
        injection hN1 with hN1
        rw [hN1] at hy
        simp only [SIS.pointees, List.mem_eraseDups, List.mem_flatMap] at hy
        obtain ⟨e, he, hye⟩ := hy
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp he
        rcases mem_ptrs_topVals hv hye with h2 | ⟨q, hq, h2⟩
        · -- the root pointer names a node of the tree, which is no top node
          exfalso
          subst h2
          obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp hrootIn
          obtain ⟨M, hM, hMl⟩ := hi'.node_of ho
          simp only [SIS.isTop, hM, Bool.and_eq_true, decide_eq_true_eq] at hytop
          have := low' _ _ ho
          have h3 := hytop.2
          rw [hspecTop] at h3
          rw [← hMl] at this
          omega
        · -- a skip pointer names an older top node, which is not reachable
          subst h2
          obtain ⟨ny, hym, _, hlt⟩ := good'.skip hm1 hq
          by_contra hreach
          have hreach' : SIS.reachable h.spec (h.P (j + 1)) (j + 1) q.2.1 = true := by
            cases hr : SIS.reachable h.spec (h.P (j + 1)) (j + 1) q.2.1 with
            | true => rfl
            | false => exact absurd hr hreach
          obtain ⟨_, _, _, hne, hno, _⟩ := ti'.topNode _ hym
          rcases reachNT _ hno hreach' with h3 | h3
          · exact hne h3
          · have hny : ny = nl := by
              have h4 := good'.lookup hym
              rw [h3, good'.lookup hml'] at h4
              injection h4 with h4
              exact h4.symm
            have := good'.last_max hlast' _ hm1
            rw [hny] at hlt
            exact absurd hlt (Nat.not_lt.mpr this)
  · -- current
    intro a ha hno
    obtain ⟨z, n, lv, hnt', hcase⟩ := hnt.adds a ha hno
    rw [← hP', SIS.reachable_iff]
    rcases hcase with h1 | h1
    · rw [h1, ← lastNew z n lv hnt']; exact hrz'
    · rw [h1]; exact hr0'
  · -- dataFixed
    intro a ha hno N hN
    obtain ⟨z, n, lv, hnt', hcase⟩ := hnt.adds a ha hno
    rcases hcase with h1 | h1
    · rw [h1, (newTop z n lv hnt').2.2.1] at hN; cases hN
    · rw [h1, ti.rootNode] at hN
      injection hN with hN
      rw [← hN]
  · -- levels
    intro a ha hno y hy
    obtain ⟨z, n, lv, hnt', hcase⟩ := hnt.adds a ha hno
    obtain ⟨_, _, _, hge, _, hNz⟩ := newTop z n lv hnt'
    have hm := hnt.made z n lv hnt'
    rw [← hP']
    rcases hcase with h1 | h1
    · -- an entry of the top node made
      have hmem : a.2 ∈ topVals n := by
        rw [← hm.2.2.2.2.2.1]
        exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨ha, by simpa using h1⟩, rfl⟩
      rw [h1]
      rcases mem_ptrs_topVals hmem hy with h2 | ⟨q, hq, h2⟩
      · have hzm : (z, n) ∈ top (j + 1) := (memTop' (z, n)).mpr (Or.inr ⟨lv, hnt'⟩)
        obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp (rootIn' _ hzm)
        obtain ⟨M, hM, hMl⟩ := hi'.node_of ho
        refine ⟨_, M, hNz, by rw [h2]; exact hM, ?_⟩
        have := low' _ _ ho
        show M.level < lv
        omega
      · have hq' := (skipsOk_parts hm.2.1).1 q hq
        cases hlk : (top j).node q.2.1 with
        | none => rw [hlk] at hq'; simp at hq'
        | some ny =>
          have hym := mem_of_lookup hlk
          obtain ⟨hNy, _⟩ := ti.topNode _ hym
          refine ⟨_, _, hNz, by rw [← h2, oldTop _ hym]; exact hNy, ?_⟩
          exact hm.2.2.2.1 _ hym
    · -- the root's entry for the top node made
      have hmem : a.2 ∈ [BVal.top z] := by
        rw [← hm.2.2.2.2.2.2]
        exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨ha, by simpa using h1⟩, rfl⟩
      simp only [List.mem_singleton] at hmem
      rw [hmem] at hy
      have hyz : y = z := by simpa [BHist.spec, bspec, bptrs] using hy
      rw [h1, hyz]
      exact ⟨_, _, rootNode', hNz, hm.2.2.2.2.1⟩
  · -- newReachable
    intro nn hnn hno
    have hl := ((hkind nn hnn).2.2 hno).1
    obtain ⟨z, n, lv, hnt', hnneq⟩ := isNew nn hnn hl
    rw [← hP', SIS.reachable_iff]
    have hid : nn.id = z := by rw [hnneq]
    rw [hid, ← lastNew z n lv hnt']
    exact hrz'
  · -- noRes
    intro y hno hy
    rw [← hP'] at hy
    rcases reachNT y hno hy with h1 | h1
    · left
      simp only [Nat.add_sub_cancel]
      rw [h1, SIS.reachable_iff]
      exact Reach.root _ ti.rootNode
    · cases hnt' : nt with
      | none =>
        left
        simp only [Nat.add_sub_cancel]
        have htops : top (j + 1) = top j := by rw [hnt.tops, hnt']; simp [ntTops]
        rw [htops] at hlast'
        rw [h1, SIS.reachable_iff]
        exact (ti.reach_last hlast').2.1
      | some t =>
        obtain ⟨z, n, lv⟩ := t
        right
        rw [h1, lastNew z n lv hnt']
        exact List.mem_map.mpr ⟨_, (newTop z n lv hnt').1, rfl⟩

end Step

/-! ## The history -/

section Hist

variable {p : Params} {h : BHist} {top : Nat → Top}

/-- The invariants of the tree and of the top after every transaction of a
history that meets `MeetsBridgeTop`, and the top's clauses of the bridge for
every transaction. -/
theorem MeetsBridgeTop.inv (hm : MeetsBridgeTop p h top) : ∀ j, j ≤ h.txs.length →
    BInv h j ∧ TopInv h top j
  | 0, _ => by
    obtain ⟨r, z, lr, lz, l0, hr, hz, hzr, hlr, hlrz, hlz0, hlz, hnew, hadds, hobj, hnone,
      hroots⟩ := hm.start
    obtain ⟨r', z', lr', lz', l0', f⟩ := hm.start.facts
    have hadds' : h.c0.adds = [(0, .top z'), (z', .rootKey r')] := by
      have hp0 := p0_eq hr hz hzr hnew hadds
      have hp0' := f.p0
      rw [hp0] at hp0'
      simp only [List.cons.injEq, Prod.mk.injEq, Node.mk.injEq, and_true, true_and] at hp0'
      obtain ⟨⟨_, h1⟩, ⟨h2, _⟩, h3, _⟩ := hp0'
      simp only [Entry.mk.injEq, BVal.top.injEq, true_and] at h1
      rw [hadds, h1, h2]
    exact ⟨f.binv, topInv_start f hadds' hm.startTop⟩
  | j + 1, hj => by
    obtain ⟨hi, ti⟩ := hm.inv j (Nat.le_of_succ_le hj)
    obtain ⟨h1, h2, h3, h4, h5, h6, _⟩ := hm.step j hj
    obtain ⟨_, ti', hi'⟩ := top_step (hj := hj) hi ti h1 h2 h3 h4 h5 h6
    exact ⟨hi', ti'⟩

/-- A history that meets the contract, the bridge's clauses about key nodes
and values, the touch rules, 030-08's top clauses and clause TB meets
`MeetsBridge`: the top's premise in the model's words is proved. -/
theorem MeetsBridgeTop.meetsBridge (hm : MeetsBridgeTop p h top) : MeetsBridge p h where
  start := hm.start
  step := by
    intro j hj
    obtain ⟨hi, ti⟩ := hm.inv j (Nat.le_of_lt hj)
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hm.step j hj
    obtain ⟨htop, _, _⟩ := top_step (hj := hj) hi ti h1 h2 h3 h4 h5 h6
    exact ⟨h1, h2, h3, htop, h7⟩

end Hist

end Contract
