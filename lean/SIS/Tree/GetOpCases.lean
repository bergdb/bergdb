import SIS.Tree.GetOpAssembly
import SIS.Tree.PutInvNewSeg
import SIS.Tree.RangePath
import SIS.Tree.RangeNewSegs

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! The writer's tree, `PutInv` and the walk's ranges of the put's cases, from
the rules (bergdb 024-12, TP10; `GetOpAssembly.lean`): the rules' premises from
`PutInv`, `RangeOrder` and the global parts of `PutInv`, as for the reading
(`GetCaseBridge.lean`).

* (1) a put into its leaf with room: all three (`treeCase_putLeafRoom`,
  `putInvCase_putLeafRoom`, `rangeCase_putLeafRoom`); `PutInv` by the place of
  the leaf: below an inner segment root, the space root, or a segment root
  below a segment leaf.
* (2) a put into a full leaf: all three (`treeCase_putLeafFull`,
  `putInvCase_putLeafFull`, `rangeCase_putLeafFull`), on
  `writerWP_put_accessPathR` (the tree, the taken ids kept, the nodes reached
  after reached before or new) and `rangeOrder_put_accessPath`; `PutInv`'s
  order from the ranges after (`putInv_after_op`).
* (3) a put of a key with no leaf, in four parts (`opCaseOK_putNewSeg_of_parts`):
  the writer fails where no new segment is made; one new segment below a leaf
  with room (all three); more new segments below a leaf with room (the
  ranges); new segments below a full leaf (open). -/

/-! ## (1) A put into its leaf with room -/

theorem segRootR_snoc_some (N : NodeId → Option KNode) (t : Time) (fuel : Nat) (k : Nat) :
    ∀ (pre : List Nat) (r rk : NodeId), segRootR N t fuel (pre ++ [k]) r = some rk →
      ∃ rq, segRootR N t fuel pre r = some rq ∧ getEqR N t k fuel rq = some rk := by
  intro pre
  induction pre with
  | nil =>
    intro r rk h
    simp only [List.nil_append, segRootR] at h
    refine ⟨r, rfl, ?_⟩
    cases hg : getEqR N t k fuel r with
    | none => rw [hg] at h; cases h
    | some y =>
      rw [hg] at h
      simp only at h
      split at h
      · simp only [Option.some.injEq] at h; rw [h]
      · cases h
  | cons a rest ih =>
    intro r rk h
    simp only [List.cons_append, segRootR] at h
    cases hg : getEqR N t a fuel r with
    | none => rw [hg] at h; cases h
    | some y =>
      rw [hg] at h
      simp only at h
      split at h
      · rename_i hy
        obtain ⟨rq, h1, h2⟩ := ih y rk h
        refine ⟨rq, ?_, h2⟩
        simp only [segRootR, hg, hy, ↓reduceIte]
        exact h1
      · cases h

theorem eqVisits_of_leaf (N : NodeId → Option KNode) (t : Time) (cv fuel : Nat) (x L : NodeId)
    (m : KNode) (hx : N x = some m) (hl : m.leaf = true) (hL : (L, cv) ∈ eqVisits N t cv fuel x) :
    L = x := by
  cases fuel with
  | zero => simp [eqVisits] at hL
  | succ f =>
    simp only [eqVisits, hx, hl, ↓reduceIte, List.mem_cons, Prod.mk.injEq, and_true,
      List.not_mem_nil, or_false] at hL
    exact hL

/-- (1), the writer's tree. -/
theorem treeCase_putLeafRoom (p : Params) (R : Struct BVal → Time → Prop) :
    OpCaseOK p R (QTree p) PutLeafRoomCase := by
  intro ts tx _ _ _ _ _ _ _ op _ _ _ w _ hI _ hP
  obtain ⟨pre, cv, h, L, n, hop, hK, hroom⟩ := hP
  subst hop
  obtain ⟨rk, hrk, hn⟩ := keyLeaf_rk hK
  exact writerWP_put_room_seg_tree (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv h rk w hrk
    (hI.pathUntaken _) (keyLeaf_all hK hrk (fun m => klongsWf m.ks = true ∧
      (∀ s, Klong.time s ∈ m.ks → s ≤ (ctxOf p ts).i) ∧ m.size + 1 < (ctxOf p ts).p.M ∧
      deadOver (ctxOf p ts).p (m.add (ctxOf p ts).i (.key cv w.next)) = false)
      ⟨hI.wf L n hn, hI.times L n hn, hroom.1, hroom.2⟩)
    (fun x xn _ hn => hI.wf x xn hn) hI.tree (hI.none_of_ge w.next (Nat.le_refl _))
    (fun u c' hu ⟨un, hun, hl⟩ => by
      have := hI.links u un c' w.next (tReach_reachS _ _ _ _ hu) hun hl
      omega)

/-- (1), `PutInv`: by the place of the leaf. -/
theorem putInvCase_putLeafRoom (p : Params) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) :
    OpCaseOK p R (QPutInv p) PutLeafRoomCase := by
  intro ts tx hw hr z top _ htop ops op _ _ r w hpre hI _ hP
  obtain ⟨pre, cv, h, L, n, hop, hK, hroom⟩ := hP
  subst hop
  obtain ⟨rk, hrk, hvisL, hn, hnl⟩ := id hK
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  have hbk := putBook_reached p ts tx hw (hRL _ _ hr) z top htop ops r w hpre
  have hroomAll := keyLeaf_all hK hrk (fun m => m.size + 1 < (ctxOf p ts).p.M ∧
    deadOver (ctxOf p ts).p (m.add (ctxOf p ts).i (.key cv w.next)) = false) hroom
  cases hrkn : wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w rk with
  | none =>
    have := eqVisits_start_isSome _ _ _ _ _ L n hvisL hn
    rw [hrkn] at this
    cases this
  | some m =>
    cases hml : m.leaf with
    | false =>
      exact putInv_put_room_below (ctxOf p ts) _ tx.base top hB pre cv h rk w hI hbk hrk
        (fun m' hm' => by
          have hm2 : wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w rk = some m' := hm'
          rw [hrkn] at hm2; cases hm2; exact hml) hroomAll
    | true =>
      have hLrk : L = rk := eqVisits_of_leaf _ _ _ _ rk L m hrkn hml hvisL
      subst hLrk
      rw [hrkn] at hn
      cases hn
      rcases List.eq_nil_or_concat pre with hnil | ⟨pre0, k1, hpre0⟩
      · subst hnil
        simp only [segRootR, Option.some.injEq] at hrk
        subst hrk
        exact putInv_put_room_root (ctxOf p ts) _ tx.base top hB cv h w n hI hbk hrkn hml hroom
      · rw [List.concat_eq_append] at hpre0
        subst hpre0
        obtain ⟨rq, hrq, hgk⟩ := segRootR_snoc_some _ _ _ k1 pre0 _ _ hrk
        have hk : pre0 ++ [k1] ++ [cv] = pre0 ++ [k1, cv] := by simp
        rw [hk]
        exact putInv_put_room_segRoot (ctxOf p ts) _ tx.base top hB pre0 k1 cv h rq L n w hI hbk
          hrq hgk hrkn hml hroom

/-- (1), the walk's ranges. -/
theorem rangeCase_putLeafRoom (p : Params) (R : Struct BVal → Time → Prop) :
    OpCaseOK p R (QRange p) PutLeafRoomCase := by
  intro ts tx _ _ _ _ _ _ _ op _ _ _ w _ hI hRO hP
  obtain ⟨pre, cv, h, L, n, hop, hK, hroom⟩ := hP
  subst hop
  obtain ⟨rk, hrk, _⟩ := keyLeaf_rk hK
  refine writerWP_mono (rangeOrder_put_room (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv h rk w hI
    hRO hrk (keyLeaf_all hK hrk (fun m => m.size + 1 < (ctxOf p ts).p.M ∧
      deadOver (ctxOf p ts).p (m.add (ctxOf p ts).i (.key cv w.next)) = false) hroom)) ?_
  intro _ _ h _
  exact h

/-! ## (2) A put into a full leaf: the walk's ranges -/

/-- (2), the walk's ranges, for 2 ≤ splitAbove and runs with their links. -/
theorem rangeCase_putLeafFull (p : Params) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hsa : 2 ≤ p.splitAbove) :
    OpCaseOK p R (QRange p) PutLeafFullCase := by
  intro ts tx hw hr z top _ htop ops op _ _ r w hpre hI hRO hP
  obtain ⟨pre, cv, h, L, n, hop, hK, hfull⟩ := hP
  subst hop
  obtain ⟨rk, hrk, _⟩ := keyLeaf_rk hK
  have hG := putInvG_reached p ts tx hw (hRL _ _ hr) z top htop ops r w hpre
  refine writerWP_mono (rangeOrder_put_accessPath (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv h
    rk w hrk (hI.pathUntaken _) hI.ids hI.fresh hI.wf hI.times hI.tree
    (fun u c' z ⟨un, hun, hl⟩ => hG.links u un c' z hun hl)
    (rangeG_of_rangeOrder (ctxOf p ts) _ _ hRO hI.times)
    (lenG_of_splitAbove (ctxOf p ts) _ _ hsa)
    (keyLeaf_all hK hrk (fun m => ¬ (m.size + 1 < (ctxOf p ts).p.M ∧
      deadOver (ctxOf p ts).p (m.add (ctxOf p ts).i (.key cv w.next)) = false)) hfull) hRO) ?_
  intro _ _ h _
  exact h

/-! ## (2) A put into a full leaf: the writer's tree and `PutInv` -/

/-- `PutInv` after an operation from the writer's tree after it, the taken ids
kept, the nodes reached after it reached before or new, and the walk's ranges
after it: the global parts from the books, the order from the ranges. -/
theorem putInv_after_op (p : Params) (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx]))
    (hRL : RunLinksOK p (treeRun p ts) ts.length) (z : NodeId) (top : Top)
    (htop : topOf p (ctxOf p ts).view z = .ok top) (ops : List Op) (r : List Bool) (w : W)
    (hpre : (ops.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w))
    (hI : PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w) (op : Op) (a : Bool) (w' : W)
    (hrun : putKv op (ctxOf p ts) w = .ok (a, w')) (htaken : w'.taken = w.taken)
    (hreach : ∀ x, TReach (wNode p (viewOf (treeRun p ts)) w') (ts.length + 1) w'.top.rootKey x →
      TReach (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey x ∨ w.next ≤ x)
    (hR' : RangeOrder (wNode p (viewOf (treeRun p ts)) w') (ts.length + 1) w'.top.rootKey)
    (hT' : WriterTreeOK p (treeRun p ts) (ts.length + 1) w') :
    PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w' := by
  have hB := putBase_of_run p ts tx hw hRL
  have hbk := putBook_reached p ts tx hw hRL z top htop ops r w hpre
  have hb' := (putBook_putKv (ctxOf p ts) _ tx.base top op hB w hbk a w' hrun).1
  have hG' := putInvG_of_book (ctxOf p ts) _ tx.base top w' hB hb'
  refine putInv_of_parts (ctxOf p ts) _ w' hG' hT' ?_ ?_
  · intro x hx
    rcases hreach x (reachS_tReach _ _ _ _ hx) with h | h
    · rw [htaken]; exact hI.untaken x (tReach_reachS _ _ _ _ h)
    · rw [htaken]
      cases hc : w.taken.contains x with
      | false => rfl
      | true => have := hI.ids.2.2.1 x hc; omega
  · exact leafOrder_of_rangeOrder _ _ _ hR' hG'.times

/-- (2), the writer's tree, for 2 ≤ splitAbove and runs with their links. -/
theorem treeCase_putLeafFull (p : Params) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hsa : 2 ≤ p.splitAbove) :
    OpCaseOK p R (QTree p) PutLeafFullCase := by
  intro ts tx hw hr z top _ htop ops op post hops r w hpre hI hRO hP
  obtain ⟨pre, cv, h, L, n, hop, hK, hfull⟩ := hP
  subst hop
  have hkey : keyWf (pre ++ [cv]) = true := within_op_keyWf p ts tx hw ops _ post hops
  obtain ⟨rk, hrk, _⟩ := keyLeaf_rk hK
  have hG := putInvG_reached p ts tx hw (hRL _ _ hr) z top htop ops r w hpre
  have hOrd := ordG_of_rangeOrder (ctxOf p ts) _ _ hRO hI.times
  exact writerWP_mono (writerWP_put_accessPathR (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv h
    rk w hkey hrk (hI.pathUntaken _) hI.ids hI.fresh hI.wf hI.times hI.tree
    (fun u c' z ⟨un, hun, hl⟩ => hG.links u un c' z hun hl) hI.keyNoValue
    (rangeG_of_rangeOrder (ctxOf p ts) _ _ hRO hI.times)
    (lenG_of_splitAbove (ctxOf p ts) _ _ hsa)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ => Or.inr hOrd)
    (keyLeaf_all hK hrk (fun m => ¬ (m.size + 1 < (ctxOf p ts).p.M ∧
      deadOver (ctxOf p ts).p (m.add (ctxOf p ts).i (.key cv w.next)) = false)) hfull)
    (hI.keyUniq pre cv rk hkey hrk)) (fun _ _ h => h.1)

/-- (2), `PutInv`, for 2 ≤ splitAbove and runs with their links. -/
theorem putInvCase_putLeafFull (p : Params) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hsa : 2 ≤ p.splitAbove) :
    OpCaseOK p R (QPutInv p) PutLeafFullCase := by
  intro ts tx hw hr z top _ htop ops op post hops r w hpre hI hRO hP
  obtain ⟨pre, cv, h, L, n, hop, hK, hfull⟩ := hP
  subst hop
  have hkey : keyWf (pre ++ [cv]) = true := within_op_keyWf p ts tx hw ops _ post hops
  obtain ⟨rk, hrk, _⟩ := keyLeaf_rk hK
  have hG := putInvG_reached p ts tx hw (hRL _ _ hr) z top htop ops r w hpre
  have hOrd := ordG_of_rangeOrder (ctxOf p ts) _ _ hRO hI.times
  have hfull' := keyLeaf_all hK hrk (fun m => ¬ (m.size + 1 < (ctxOf p ts).p.M ∧
    deadOver (ctxOf p ts).p (m.add (ctxOf p ts).i (.key cv w.next)) = false)) hfull
  have h1 := writerWP_put_accessPathR (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv h
    rk w hkey hrk (hI.pathUntaken _) hI.ids hI.fresh hI.wf hI.times hI.tree
    (fun u c' z ⟨un, hun, hl⟩ => hG.links u un c' z hun hl) hI.keyNoValue
    (rangeG_of_rangeOrder (ctxOf p ts) _ _ hRO hI.times)
    (lenG_of_splitAbove (ctxOf p ts) _ _ hsa)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ => Or.inr hOrd) hfull' (hI.keyUniq pre cv rk hkey hrk)
  have h2 := rangeOrder_put_accessPath (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv h
    rk w hrk (hI.pathUntaken _) hI.ids hI.fresh hI.wf hI.times hI.tree
    (fun u c' z ⟨un, hun, hl⟩ => hG.links u un c' z hun hl)
    (rangeG_of_rangeOrder (ctxOf p ts) _ _ hRO hI.times)
    (lenG_of_splitAbove (ctxOf p ts) _ _ hsa) hfull' hRO
  intro a w' hrun hT'
  have e1 := h1 a w' hrun
  exact putInv_after_op p ts tx hw (hRL _ _ hr) z top htop ops r w hpre hI _ a w' hrun e1.2.1
    e1.2.2.1 (h2 a w' hrun) hT'

/-! ## (3) A put of a key with no leaf, in parts -/

/-- The point where a put makes new segments, in the writer's state. -/
def NewSegAt (c : Ctx) (base : View BVal) (w : W) (pre : List Nat) (c0 : Nat) (tail : List Nat)
    (rk0 L : NodeId) (n : KNode) : Prop :=
  tail ≠ [] ∧ segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk0 ∧
    (L, c0) ∈ eqVisits (wNode c.p base w) c.i c0 c.p.fuel rk0 ∧ wNode c.p base w L = some n ∧
    n.leaf = true ∧ n.searchEq c.i c0 = none

/-- (3a) One new segment, below a leaf with room. -/
def PutNewSeg1RoomCase (c : Ctx) (base : View BVal) (w : W) (op : Op) : Prop :=
  ∃ pre c0 cl h rk0 L n, op = .put (pre ++ [c0, cl]) h ∧ NewSegAt c base w pre c0 [cl] rk0 L n ∧
    n.size + 1 < c.p.M

/-- (3b) Two new segments or more, below a leaf with room. -/
def PutNewSegsRoomCase (c : Ctx) (base : View BVal) (w : W) (op : Op) : Prop :=
  ∃ pre c0 tail h rk0 L n, op = .put (pre ++ c0 :: tail) h ∧ 2 ≤ tail.length ∧
    NewSegAt c base w pre c0 tail rk0 L n ∧ n.size + 1 < c.p.M

/-- (3c) New segments below a full leaf. -/
def PutNewSegFullCase (c : Ctx) (base : View BVal) (w : W) (op : Op) : Prop :=
  ∃ pre c0 tail h rk0 L n, op = .put (pre ++ c0 :: tail) h ∧ NewSegAt c base w pre c0 tail rk0 L n ∧
    ¬ n.size + 1 < c.p.M

/-- (3) from its parts: where the put makes no new segment the writer fails
(`writerWP_putSegs_put_fail`), for every post. -/
theorem opCaseOK_putNewSeg_of_parts (p : Params) (R : Struct BVal → Time → Prop)
    (Q : List Tx → Op → W → W → Prop)
    (a : OpCaseOK p R Q PutNewSeg1RoomCase) (b : OpCaseOK p R Q PutNewSegsRoomCase)
    (cF : OpCaseOK p R Q PutNewSegFullCase) :
    OpCaseOK p R Q PutNewSegCase := by
  intro ts tx hw hr z top hz htop ops op post hops r w hpre hI hRO hP
  obtain ⟨key, h, hop, hno⟩ := id hP
  have hkey : keyWf key = true := by
    have := within_op_keyWf p ts tx hw ops _ post hops
    rw [hop] at this; exact this
  have hne : key ≠ [] := by intro h; subst h; simp [keyWf] at hkey
  have hno' : NoLeafFrom (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) p.fuel key
      w.top.rootKey := by
    rintro ⟨pre, cv, rk, L, n, hsplit, hrk, hvis, hn, hnl⟩
    exact hno ⟨pre, cv, L, n, hsplit, rk, hrk, hvis, hn, hnl⟩
  by_cases hseg : NewSegFrom (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) p.fuel key
      w.top.rootKey
  · obtain ⟨pre, c0, tail, rk0, L, n, hk, htail, hrk0, hL, hn, hnl, hnone⟩ := hseg
    have hat : NewSegAt (ctxOf p ts) (viewOf (treeRun p ts)) w pre c0 tail rk0 L n :=
      ⟨htail, hrk0, hL, hn, hnl, hnone⟩
    by_cases hroom : n.size + 1 < p.M
    · cases tail with
      | nil => exact absurd rfl htail
      | cons cl rest =>
        cases rest with
        | nil =>
          exact a ts tx hw hr z top hz htop ops op post hops r w hpre hI hRO
            ⟨pre, c0, cl, h, rk0, L, n, by rw [hop, hk], hat, hroom⟩
        | cons d rest' =>
          exact b ts tx hw hr z top hz htop ops op post hops r w hpre hI hRO
            ⟨pre, c0, cl :: d :: rest', h, rk0, L, n, by rw [hop, hk], by simp, hat, hroom⟩
    · exact cF ts tx hw hr z top hz htop ops op post hops r w hpre hI hRO
        ⟨pre, c0, tail, h, rk0, L, n, by rw [hop, hk], hat, hroom⟩
  · subst hop
    unfold putKv pathClear findRoot pathAdd
    wpSimplify
    generalize hw2 : ({ ({ w with path := [] } : W) with
      path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w2
    have hr02 : ReadsAs (ctxOf p ts).p (viewOf (treeRun p ts)) w w2 := by
      subst hw2; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    refine writerWP_mono (writerWP_putSegs_put_fail (ctxOf p ts) _ (viewCoherent_ctxOf p ts) key h
      key w.top.rootKey w2 hne ?_ ?_ ?_) (fun _ _ hf => hf.elim)
    · intro q hq
      rw [hr02.2.2.1]
      rw [hr02.1] at hq
      exact hI.pathUntaken key q hq
    · rw [hr02.1]; exact hno'
    · rw [hr02.1]; exact hseg

/-- The leaf of the point is the one leaf of its segment's descent. -/
theorem newSegAt_one {c : Ctx} {base : View BVal} {w : W} {pre : List Nat} {c0 : Nat}
    {tail : List Nat} {rk0 L : NodeId} {n : KNode} (h : NewSegAt c base w pre c0 tail rk0 L n)
    (P : NodeId → KNode → Prop) (hP : P L n) :
    ∀ L' n', (L', c0) ∈ eqVisits (wNode c.p base w) c.i c0 c.p.fuel rk0 →
      wNode c.p base w L' = some n' → n'.leaf = true → P L' n' := by
  obtain ⟨_, _, hL, hn, hnl, _⟩ := h
  intro L' n' hL' hn' hnl'
  have he := eqVisits_leaf_unique _ _ _ _ _ _ _ _ _ hL' hL hn' hnl' hn hnl
  subst he
  rw [hn] at hn'
  cases hn'
  exact hP

/-- (3a), the writer's tree. -/
theorem treeCase_putNewSeg1Room (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M) :
    OpCaseOK p R (QTree p) PutNewSeg1RoomCase := by
  intro ts tx _ _ _ _ _ _ _ op _ _ _ w _ hI _ hP
  obtain ⟨pre, c0, cl, h, rk0, L, n, hop, hat, hroom⟩ := hP
  subst hop
  exact writerWP_put_newSeg_inv_tree (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre c0 cl h rk0 w hI hM
    hat.2.1 (newSegAt_one hat (fun _ m => m.searchEq (ctxOf p ts).i c0 = none ∧
      m.size + 1 < (ctxOf p ts).p.M) ⟨hat.2.2.2.2.2, hroom⟩)

/-- (3a), `PutInv`. -/
theorem putInvCase_putNewSeg1Room (p : Params) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hM : 2 ≤ p.M) :
    OpCaseOK p R (QPutInv p) PutNewSeg1RoomCase := by
  intro ts tx hw hr z top _ htop ops op _ _ r w hpre hI _ hP
  obtain ⟨pre, c0, cl, h, rk0, L, n, hop, hat, hroom⟩ := hP
  subst hop
  exact putInv_put_newSeg (ctxOf p ts) _ tx.base top (putBase_of_run p ts tx hw (hRL _ _ hr)) pre c0
    cl h rk0 w hI (putBook_reached p ts tx hw (hRL _ _ hr) z top htop ops r w hpre) hM hat.2.1
    (newSegAt_one hat (fun _ m => m.searchEq (ctxOf p ts).i c0 = none ∧
      m.size + 1 < (ctxOf p ts).p.M) ⟨hat.2.2.2.2.2, hroom⟩)

/-- The ranges of new segments below a leaf with room. -/
theorem rangeOrder_newSegsRoom (p : Params) (ts : List Tx) (w : W)
    (hI : PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w)
    (hRO : RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey)
    (hM : 2 ≤ p.M) (pre : List Nat) (c0 h : Nat) (tail : List Nat) (rk0 L : NodeId) (n : KNode)
    (hat : NewSegAt (ctxOf p ts) (viewOf (treeRun p ts)) w pre c0 tail rk0 L n)
    (hroom : n.size + 1 < p.M) :
    WriterWP (putKv (.put (pre ++ c0 :: tail) h)) (ctxOf p ts) w (fun _ w' =>
      RangeOrder (wNode p (viewOf (treeRun p ts)) w') (ts.length + 1) w'.top.rootKey) := by
  obtain ⟨hkeys, hnotpre⟩ := newSeg_leaf_keys hI pre c0 rk0 L hat.2.1 hat.2.2.1
  exact rangeOrder_put_newSegs (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre c0 h tail hat.1 rk0 w hM
    hat.2.1 (hI.pathUntaken _) hI.ids hI.fresh
    (newSegAt_one hat (fun L' m => klongsWf m.ks = true ∧
      (∀ s, Klong.time s ∈ m.ks → s ≤ (ctxOf p ts).i) ∧ m.searchEq (ctxOf p ts).i c0 = none ∧
      m.size + 1 < (ctxOf p ts).p.M ∧
      (∀ key', keyWf key' = true →
        (L', c0) ∈ fromVisits (wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w) (ctxOf p ts).i
          (ctxOf p ts).p.fuel key' w.top.rootKey → ∃ rest', key' = pre ++ c0 :: rest') ∧
      ∀ c', (L', c') ∉ fromVisits (wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w) (ctxOf p ts).i
        (ctxOf p ts).p.fuel pre w.top.rootKey)
      ⟨hI.wf L n hat.2.2.2.1, hI.times L n hat.2.2.2.1, hat.2.2.2.2.2, hroom, hkeys, hnotpre⟩)
    hI.links hI.tree hI.wf hRO

/-- (3a), the walk's ranges. -/
theorem rangeCase_putNewSeg1Room (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M) :
    OpCaseOK p R (QRange p) PutNewSeg1RoomCase := by
  intro ts tx _ _ _ _ _ _ _ op _ _ _ w _ hI hRO hP
  obtain ⟨pre, c0, cl, h, rk0, L, n, hop, hat, hroom⟩ := hP
  subst hop
  exact writerWP_mono (rangeOrder_newSegsRoom p ts w hI hRO hM pre c0 h [cl] rk0 L n hat hroom)
    (fun _ _ h _ => h)

/-- (3b), the walk's ranges. -/
theorem rangeCase_putNewSegsRoom (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M) :
    OpCaseOK p R (QRange p) PutNewSegsRoomCase := by
  intro ts tx _ _ _ _ _ _ _ op _ _ _ w _ hI hRO hP
  obtain ⟨pre, c0, tail, h, rk0, L, n, hop, _, hat, hroom⟩ := hP
  subst hop
  exact writerWP_mono (rangeOrder_newSegsRoom p ts w hI hRO hM pre c0 h tail rk0 L n hat hroom)
    (fun _ _ h _ => h)

/-! ## TP10 and TP11 with these cases proved -/

/-- `getOK_scanOK_of_cases_merges` with the cases above proved: for the
parameters of `MergeParamsOK`, left of the cases are the writer's tree and
`PutInv` of (3b) and of (3c), the walk's ranges of (3c), and the writer's tree,
`PutInv`, the ranges and the reading of (4). -/
theorem getOK_scanOK_of_cases_merges_open (p : Params) (hp : MergeParamsOK p)
    (hinv : InvPreserved p)
    (hlinks : ∀ ts, Within p ts → RunLinksOK p (treeRun p ts) ts.length)
    (htree : ∀ ts, Within p ts → TreeAt p (treeRun p ts) ts.length)
    (hfit : TxSegFitsOK p (RunOK p))
    (t3b : OpCaseOK p (RunOK p) (QTree p) PutNewSegsRoomCase)
    (i3b : OpCaseOK p (RunOK p) (QPutInv p) PutNewSegsRoomCase)
    (t3c : OpCaseOK p (RunOK p) (QTree p) PutNewSegFullCase)
    (i3c : OpCaseOK p (RunOK p) (QPutInv p) PutNewSegFullCase)
    (r3c : OpCaseOK p (RunOK p) (QRange p) PutNewSegFullCase)
    (t4 : OpCaseOK p (RunOK p) (QTree p) DelMergeCase)
    (i4 : OpCaseOK p (RunOK p) (QPutInv p) DelMergeCase)
    (r4 : OpCaseOK p (RunOK p) (QRange p) DelMergeCase)
    (c4 : OpGetCaseOK p (RunOK p) DelMergeCase) :
    GetOK p ∧ ScanOK p := by
  have hp' := hp
  unfold MergeParamsOK at hp'
  have hM : 2 ≤ p.M := by omega
  have hsa : 2 ≤ p.splitAbove := by omega
  have hRL : ∀ P t, RunOK p P t → RunLinksOK p P t := fun _ _ h => h.1
  exact getOK_scanOK_of_cases_merges p hp hinv hlinks htree hfit
    (treeCase_putLeafRoom p _) (treeCase_putLeafFull p _ hRL hsa)
    (opCaseOK_putNewSeg_of_parts p _ _ (treeCase_putNewSeg1Room p _ hM) t3b t3c) t4
    (putInvCase_putLeafRoom p _ hRL) (putInvCase_putLeafFull p _ hRL hsa)
    (opCaseOK_putNewSeg_of_parts p _ _ (putInvCase_putNewSeg1Room p _ hRL hM) i3b i3c) i4
    (rangeCase_putLeafRoom p _) (rangeCase_putLeafFull p _ hRL hsa)
    (opCaseOK_putNewSeg_of_parts p _ _ (rangeCase_putNewSeg1Room p _ hM)
      (rangeCase_putNewSegsRoom p _ hM) r3c) r4
    c4

end SIS.Tree
