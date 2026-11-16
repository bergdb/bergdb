/-
The live merge reduced to `mergeParent`'s `full` (bergdb 030-01, step 3's rest):
`MergeLiveFullOK` asked a merge whose parent may lack room for some merge; the
merges whose parent takes `mergeParent`'s branch with room for the merge it
makes are proved (`writerWP_mergeTail_liveRoomR`, LiveMergeRoom.lean), so what
is left is the merge's tail where `mergeParent` goes `full`, stated at the tail
with the round's facts and the two nodes chosen (`MergeTailFullOK`).
-/
import SIS.Tree.LiveSplitRoom2

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The merge's tail where its parent takes `mergeParent`'s `full` (bergdb
030-01, step 3's rest): at a round of the merges' loop with the facts of
`MergeLiveOK`, the merge's tail from a state w3 that reads as v3, with the two
nodes l and r that the merge chose and their facts, where `mergeParent` has no
room or compacts for the merge it makes (`¬ MergeParentRoom`), keeps the hole's
form one height up (a merge into one node), or ends with no hole. -/
def MergeTailFullOK (c : Ctx) (base : View BVal) (B : NodeId) (H : NodeId → Nat → Prop) : Prop :=
  ∀ (key : Key) (g h : Nat) (v v1 v3 : W) (d F : Nat) (w0 : W) (k0 : Key) (KO : KindOracle)
    (top0 : Top) (X : Nat → NodeId) (K : Nat → Nat) (Nn : Nat → KNode) (x p : NodeId)
    (pn xn : KNode),
    descendToHeight key g h c v = .ok (d, v1) → 0 < d →
    ReadsAs c.p base v1 v3 → ObsKept c v1 v3 → v3.path = v1.path →
    LiveHoleW key g h c base v →
    DelInvJ c base w0 k0 F KO B B v3 → PutBook c B top0 v3 → PathOK c v3 d X K Nn →
    Book B c v1 → HtInv H B c v1 → PathFreeTo v1 v1.path.length → HtInv H B c v3 →
    (v3.path[d]?).map (·.2) = some x → (v3.path[d - 1]?).map (·.2) = some p →
    v3.nodes.lookup p = some pn → pn.leaf = false → v3.nodes.lookup x = some xn →
    xn.cnt < c.p.mergeBelow →
    ∀ (leftSome : Bool) (l : NodeId) (ln : KNode) (il : Nat) (r : NodeId) (rn : KNode)
      (ir cL cR : Nat) (w3 : W), ReadsAs c.p base v3 w3 →
    w3.nodes.lookup p = some pn → ObsKept c v3 w3 →
    (∀ z, (w3.nodes.lookup z).isSome = true → (v3.nodes.lookup z).isSome = true ∨
      (c.view z).isSome = true) →
    pn.ks[il]? = some (.key cL l) → LastLive pn.ks pn.lastBitmap il cL →
    pn.ks[ir]? = some (.key cR r) → LastLive pn.ks pn.lastBitmap ir cR → cL < cR →
    (∀ cc z, (cc, z) ∈ pn.liveAt c.i → cc ≤ cL ∨ cR ≤ cc) →
    ln.leaf = xn.leaf → rn.leaf = xn.leaf →
    (x = l ∨ x = r) → wNode c.p base v3 l = some ln → wNode c.p base v3 r = some rn →
    v3.nodes <+: w3.nodes → w3.path = v3.path →
    ¬ MergeParentRoom c pn il cL v3.next ir cR (mergeM2 c xn ln rn cR v3.next) →
    WriterWP (mergeTail c x d p pn xn leftSome l ln il r rn ir) c w3
      (fun res v4 => (res = 1 → LiveHoleW key g (h + 1) c base v4) ∧
        (res ≠ 1 → LiveEdges c.p (wNode c.p base v4) c.i v4.top.rootKey))

set_option maxHeartbeats 4000000 in
/-- The live merge (bergdb 030-01, step 3) from the merge's tail where its
parent goes `full`: every merge whose parent takes `mergeParent`'s branch with
room is proved (`liveHoleW_merge_G`), whatever the parent's room for other
merges (`MergeRoom`). -/
theorem mergeLiveOK_of_tailFull (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (hm : c.p.merges = true) (hMP : MergeParamsOK c.p) {B : NodeId} {H : NodeId → Nat → Prop}
    (hvo : ViewHtOK H B c) (hF : MergeTailFullOK c base B H) : MergeLiveOK c base B H := by
  intro key g h v v1 v3 d F w0 k0 KO top0 X K Nn x p pn xn hS hd hr13 hk13 hp13 hLH hJ3 hpb3 hP3 hb1
    hi1 hpf1 hi3 hx hpath hplk hpleaf hxlk hcnt
  have hI : PutInv c base v3 := hJ3.1.1.1
  have hRO : RangeOrder (wNode c.p base v3) c.i v3.top.rootKey := hJ3.1.1.2.2.1
  obtain ⟨hX, _, hS2, _, _⟩ := id hP3
  -- the path's length
  have hlen : d + 1 = v3.path.length := by
    obtain ⟨_, _, hl, _, _⟩ := descend_exit_shape key g h c v v1 d hS
    rw [hp13]; exact hl
  have hpX : p = X (d - 1) := by
    have := hX (d - 1) (by omega); rw [hpath] at this; exact Option.some.inj this
  have hpn : wNode c.p base v3 p = some pn := by
    obtain ⟨a, b⟩ := hS2 (d - 1) (by omega)
    rw [← hpX] at a b
    rw [hplk] at a
    simp only [wNode, b, Bool.false_eq_true, ↓reduceIte, hplk]
  have hxX : x = X d := by
    have := hX d (by omega); rw [hx] at this; exact Option.some.inj this
  have hxn : wNode c.p base v3 x = some xn := by
    obtain ⟨a, b⟩ := hS2 d (by omega)
    rw [← hxX] at a b
    rw [hxlk] at a
    simp only [wNode, b, Bool.false_eq_true, ↓reduceIte, hxlk]
  have hfree : ∀ z, v3.next ≤ z → wNode c.p base v3 z = none ∧ v3.taken.contains z = false := by
    intro z hz
    have hl : v3.nodes.lookup z = none := by
      cases h' : v3.nodes.lookup z with
      | none => rfl
      | some _ => have := hI.ids.1 z (by rw [h']; rfl); omega
    have ht : v3.taken.contains z = false := by
      cases h' : v3.taken.contains z with
      | false => rfl
      | true => have := hI.ids.2.2.1 z h'; omega
    refine ⟨?_, ht⟩
    simp only [wNode, ht, Bool.false_eq_true, ↓reduceIte, hl, (hI.fresh z hz).1]
  refine liveHoleW_merge_G key g h c base v v1 v3 d hvc hm hMP hS hd hr13 hk13 hp13 hLH hI.tree hRO
    (fun y hy => hI.untaken y (tReach_reachS _ _ _ _ hy)) hI.ids.1 hI.ids.2.1 hfree
    (fun z hz u c' hu hl => by
      obtain ⟨un, hun, hc⟩ := hl
      have := hI.links u un c' z (tReach_reachS _ _ _ _ hu) hun hc
      omega)
    (fun j e he => by
      have hj : j ≤ d := by
        have := (List.getElem?_eq_some_iff.mp he).1; omega
      have hXj := hX j hj
      rw [he] at hXj
      have hej : e.2 = X j := Option.some.inj hXj
      rw [hej]
      exact pathOK_depth c base v3 d X K Nn hP3 j hj)
    (fun e he => by
      obtain ⟨j, hj, hje⟩ := List.mem_iff_getElem.mp he
      have hXj := hX j (by omega)
      rw [List.getElem?_eq_getElem hj, hje] at hXj
      have hej : e.2 = X j := Option.some.inj hXj
      rw [hej]
      exact ⟨Nn j, (hS2 j (by omega)).1⟩)
    x p pn hx hpath hplk hpleaf (hI.wf p pn hpn) (hI.times p pn hpn)
    (fun cc z zn _ hzn => hI.times z zn hzn) hvo.heights hvo.ids hb1 hi1 hpf1 hpb3.book ?_
  intro leftSome l ln il r rn ir cL cR xn' w3 hr3 h3p hk3 hsrc3 hL hLL hR hRL hclt hadj hll hrl hxn'
    hxlr hln hrn hpre3 hpath3 hB
  rw [hxn] at hxn'
  cases hxn'
  exact hF key g h v v1 v3 d F w0 k0 KO top0 X K Nn x p pn xn hS hd hr13 hk13 hp13 hLH hJ3 hpb3 hP3
    hb1 hi1 hpf1 hi3 hx hpath hplk hpleaf hxlk hcnt leftSome l ln il r rn ir cL cR w3 hr3 h3p hk3 hsrc3
    hL hLL hR hRL hclt hadj hll hrl hxlr hln hrn hpre3 hpath3 hB

/-- `MergeLiveFullOK` from the merge's tail where its parent goes `full`. -/
theorem mergeLiveFullOK_of_tailFull (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (hm : c.p.merges = true) (hMP : MergeParamsOK c.p) {B : NodeId} {H : NodeId → Nat → Prop}
    (hvo : ViewHtOK H B c) (hF : MergeTailFullOK c base B H) : MergeLiveFullOK c base B H :=
  fun key g h v v1 v3 d F w0 k0 KO top0 X K Nn x p pn xn hS hd hr13 hk13 hp13 hLH hJ3 hpb3 hP3 hb1
    hi1 hpf1 hi3 hx hpath hplk hpleaf hxlk hcnt _ =>
  mergeLiveOK_of_tailFull c base hvc hm hMP hvo hF key g h v v1 v3 d F w0 k0 KO top0 X K Nn x p pn xn
    hS hd hr13 hk13 hp13 hLH hJ3 hpb3 hP3 hb1 hi1 hpf1 hi3 hx hpath hplk hpleaf hxlk hcnt

/-- `afterDelete` with the hole (bergdb 030-01, steps 3 and 4): from the call's
facts to `LiveEdges`, premises the merge's tail where its parent goes `full`
(`MergeTailFullOK`), `MergeParamsOK` and R3 after the merges' loop. -/
theorem writerWP_afterDelete_liveTF (key : Key) (g : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (hm : c.p.merges = true) (hMP : MergeParamsOK c.p) (KO : KindOracle)
    (B : NodeId) (hv : ViewIdsBelow B c.view) (hk : ViewKinds KO B c)
    (hICEk : ICEFromKinds c base KO B) (hsa2 : 2 ≤ c.p.splitAbove) (hcap : 1 ≤ c.p.mergeMax)
    (hpos : 0 < c.i) {H : NodeId → Nat → Prop} (hvo : ViewHtOK H B c)
    (hkw : ViewKlongsWf c.p c.view) (top0 : Top) (hB : PutBase c base B)
    (hF : MergeTailFullOK c base B H)
    (v : W) (hJ : DelInvJAE c base KO B B v) (hpb : PutBook c B top0 v) (hhi : HtInv H B c v)
    (hLH : LiveHoleW key g 0 c base v)
    (hR3 : WriterWP (mergeUp key g c.p.fuel 0 false) c v
      (fun merged v' => merged = true → R3At key g c v')) :
    WriterWP (afterDelete key g 0) c v
      (fun _ v' => LiveEdges c.p (wNode c.p base v') c.i v'.top.rootKey) :=
  writerWP_afterDelete_liveFR key g c base hvc hm hMP KO B hv hk hICEk hsa2 hcap hpos hvo hkw top0 hB
    (mergeLiveFullOK_of_tailFull c base hvc hm hMP hvo hF) v hJ hpb hhi hLH hR3

end SIS.Tree
