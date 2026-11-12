import SIS.Tree.MergeProtectedNode

namespace SIS.Tree

open SIS SIS.Check

theorem upsert_lookup_same (nodes : List (NodeId × KNode)) (x : NodeId) (n : KNode) :
    (upsert nodes x n).lookup x = some n := by
  unfold upsert
  split
  · rename_i hex
    induction nodes with
    | nil => simp at hex
    | cons q nodes ih =>
      rcases q with ⟨y,m⟩
      by_cases hy : y = x
      · subst y
        simp
      · have hx : x ≠ y := Ne.symm hy
        have hxyb : (x == y) = false := beq_eq_false_iff_ne.mpr hx
        have htail : nodes.any (fun q => q.1 == x) = true := by simpa [hy] using hex
        simpa [List.lookup_cons,hy,hxyb] using ih htail
  · rename_i hnone
    have hlookup : nodes.lookup x = none := by
      apply List.lookup_eq_none_iff.mpr
      intro q hq
      have hfalse : (q.1 == x) = false := by
        have hh := List.any_eq_false.mp (Bool.eq_false_iff.mpr hnone) q hq
        exact Bool.eq_false_iff.mpr hh
      have hne : q.1 ≠ x := by simpa only [beq_eq_false_iff_ne] using hfalse
      simpa only [bne_iff_ne] using Ne.symm hne
    simp [List.lookup_append,hlookup]

private theorem lookup_map_update_other (nodes : List (NodeId × KNode)) (x y : NodeId)
    (n : KNode) (hxy : x ≠ y) :
    (nodes.map (fun q => if q.1 == y then (y,n) else q)).lookup x = nodes.lookup x := by
  induction nodes with
  | nil => rfl
  | cons q nodes ih =>
    rcases q with ⟨z,m⟩
    by_cases hzy : z = y
    · subst z
      simpa [List.lookup_cons,beq_eq_false_iff_ne.mpr hxy] using ih
    · by_cases hzx : z = x
      · subst z
        simp [hzy]
      · simpa [List.lookup_cons,hzy,beq_eq_false_iff_ne.mpr (Ne.symm hzx)] using ih

theorem upsert_lookup_other (nodes : List (NodeId × KNode)) (x y : NodeId)
    (n : KNode) (hxy : x ≠ y) : (upsert nodes y n).lookup x = nodes.lookup x := by
  unfold upsert
  split
  · exact lookup_map_update_other nodes x y n hxy
  · have hl : [(y,n)].lookup x = none := by
      simp only [List.lookup_cons,beq_eq_false_iff_ne.mpr hxy,List.lookup_nil]
    rw [List.lookup_append,hl]
    cases nodes.lookup x <;> rfl

theorem writerWP_ghOf_known (x : NodeId) (n : KNode) (g h : Nat)
    (c : Ctx) (w : W)
    (hn : w.nodes.lookup x = some n) (hg : w.gh.lookup x = some (g,h))
    (post : (Nat × Nat) → W → Prop) :
    WriterWP (ghOf x) c w post ↔ post (g,h) w := by
  unfold ghOf
  simp only [writerWP_bind]
  rw [writerWP_getNode_known x n c w hn]
  simp only [writerWP_get,hg,writerWP_pure]

/-- Splitting a root made by this transaction really leaves the first half
at its old id, with its old height tag. The new ids must be above that id. -/
theorem writerWP_handleFullWith_new_root_first
    (up : NodeId → List (Nat × NodeId) → M Unit) (x : NodeId)
    (ins : List (Nat × NodeId)) (last n : KNode) (g h : Nat) (c : Ctx) (w : W)
    (hn : w.nodes.lookup x = some n) (hg : w.gh.lookup x = some (g,h))
    (ht : n.firstTime = some c.i) (hfresh : x < w.next)
    (hfull : c.p.splitAbove < last.size) :
    WriterWP (handleFullWith up 0 x ins last false) c w (fun _ v =>
      v.nodes.lookup x = some (halves n.leaf c.i last ins).1 ∧
      v.gh.lookup x = some (g,h) ∧ v.taken = w.taken) := by
  have hx : x ≠ w.next := Nat.ne_of_lt hfresh
  have hx2 : x ≠ w.next+2 := by omega
  have hxb : (x == w.next) = false := beq_eq_false_iff_ne.mpr hx
  have hx2b : (x == w.next+2) = false := beq_eq_false_iff_ne.mpr hx2
  unfold handleFullWith
  simp only [writerWP_bind,writerWP_read]
  rw [writerWP_getNode_known x n c w hn]
  rw [writerWP_ghOf_known x n g h c w hn hg]
  simp only [ht,BEq.rfl,parentAt,writerWP_pure,Bool.not_false,Bool.true_and,
    hfull,decide_true,↓reduceIte,Bool.false_eq_true,Bool.not_true]
  unfold newKey fresh setMadeFor replacedBy putNode note newSuperRoot
  repeat' first
    | wpSimplify
    | simp only [note,fresh]
    | contradiction
    | split
  all_goals
    constructor
    · rw [List.lookup_append,upsert_lookup_other _ x w.next _ hx,upsert_lookup_same]
      rfl
    · exact ⟨by simp only [List.lookup_cons,hx2b,hxb,hg],True.intro⟩

/-- The actual retained root half has the live-count barrier proved for
halves; the split also leaves its height tag and take-back status intact. -/
theorem writerWP_handleFullWith_new_root_protected
    (up : NodeId → List (Nat × NodeId) → M Unit) (x : NodeId)
    (ins pairs : List (Nat × NodeId)) (n : KNode) (g h : Nat) (c : Ctx) (w : W)
    (hp : MergeParamsOK c.p)
    (hn : w.nodes.lookup x = some n) (hg : w.gh.lookup x = some (g,h))
    (ht : n.firstTime = some c.i) (hfresh : x < w.next)
    (hs : pairs.Pairwise (fun a b => a.1 < b.1))
    (hfull : c.p.splitAbove < (⟨n.leaf,newKlongs c.i pairs⟩ : KNode).size) :
    WriterWP (handleFullWith up 0 x ins ⟨n.leaf,newKlongs c.i pairs⟩ false) c w
      (fun _ v => ∃ first,
        v.nodes.lookup x = some first ∧ c.p.mergeBelow ≤ first.cnt ∧
        first.onlyLiveKlong = none ∧ v.gh.lookup x = some (g,h) ∧ v.taken = w.taken) := by
  refine writerWP_mono
    (writerWP_handleFullWith_new_root_first up x ins _ n g h c w hn hg ht hfresh hfull) ?_
  rintro _ v ⟨hv,hgh,htaken⟩
  exact ⟨_,hv,halves_first_protected_fill c.p hp n.leaf c.i pairs ins hs hfull,
    halves_first_protected_not_unary c.p hp n.leaf c.i pairs ins hs hfull,hgh,htaken⟩

/-- The retained-half state theorem also holds for a segment root below a
segment leaf. The leaf's pointer to the new root is repointed in place. -/
theorem writerWP_handleFullWith_new_segment_root_first
    (up : NodeId → List (Nat × NodeId) → M Unit) (d : Nat) (x q : NodeId)
    (parentCv : Option Nat) (cv : Nat) (ins : List (Nat × NodeId))
    (last n pn : KNode) (g h : Nat) (c : Ctx) (w : W)
    (hn : w.nodes.lookup x = some n) (hg : w.gh.lookup x = some (g,h))
    (hpn : w.nodes.lookup q = some pn) (hpleaf : pn.leaf = true)
    (hpath : w.path[d]? = some (parentCv,q)) (hxPath : w.path[d+1]? = some (some cv,x))
    (ht : n.firstTime = some c.i) (hfresh : x < w.next) (hqfresh : q < w.next)
    (hxq : x ≠ q) (hfull : c.p.splitAbove < last.size) :
    WriterWP (handleFullWith up (d+1) x ins last false) c w (fun _ v =>
      v.nodes.lookup x = some (halves n.leaf c.i last ins).1 ∧
      v.gh.lookup x = some (g,h) ∧ v.taken = w.taken) := by
  have hx : x ≠ w.next := Nat.ne_of_lt hfresh
  have hx2 : x ≠ w.next+2 := by omega
  have hxb : (x == w.next) = false := beq_eq_false_iff_ne.mpr hx
  have hx2b : (x == w.next+2) = false := beq_eq_false_iff_ne.mpr hx2
  have hqn : q ≠ w.next := Nat.ne_of_lt hqfresh
  have hqx : q ≠ x := Ne.symm hxq
  unfold handleFullWith
  simp only [writerWP_bind,writerWP_read]
  rw [writerWP_getNode_known x n c w hn]
  rw [writerWP_ghOf_known x n g h c w hn hg]
  simp only [parentAt,pathNode,writerWP_bind,writerWP_get,hpath,writerWP_pure]
  rw [writerWP_getNode_known q pn c w hpn]
  simp only [ht,BEq.rfl,hpleaf,Bool.not_false,Bool.true_and,
    hfull,decide_true,↓reduceIte,Bool.false_eq_true,Bool.not_true]
  unfold newKey fresh setMadeFor replacedBy putNode note klongAt
  repeat' first
    | wpSimplify
    | simp only [hxPath]
    | (with_unfolding_none refine
        (writerWP_getNode_known q pn _ _ ?segmentCache _).mpr ?_
       case segmentCache =>
         rw [List.lookup_append,upsert_lookup_other _ q w.next _ hqn,
           upsert_lookup_other _ q x _ hqx,List.lookup_append,hpn]
         rfl)
    | exact writerWP_throw _ _ _ _
    | contradiction
    | split
  all_goals
    constructor
    · rw [upsert_lookup_other _ x q _ hxq,List.lookup_append,
        upsert_lookup_other _ x w.next _ hx,upsert_lookup_same]
      rfl
    · exact ⟨by simp only [List.lookup_cons,hx2b,hxb,hg],True.intro⟩

/-- A delete with room and without dead compaction keeps the earlier live
keys in the actual cached node, for both appended and in-place bitmaps. -/
theorem writerWP_appendDeleteKlong_room_earlier (x : NodeId) (depth cv cut : Nat)
    (n : KNode) (keys : List Nat) (c : Ctx) (w : W)
    (hn : w.nodes.lookup x = some n) (hkeys : keys.Nodup)
    (hcut : ∀ a ∈ keys, a < cut) (hcv : cut ≤ cv)
    (hk : ∀ a ∈ keys, ∃ y i, (.key a y,i) ∈ n.ks.zipIdx ∧ i ∉ n.lastBitmap)
    (hroom : n.size+1 < c.p.M)
    (hdeadAdd : deadOver c.p (n.add c.i (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))) = false)
    (hdeadSet : deadOver c.p
      (n.setAt (n.size-1) (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))) = false) :
    WriterWP (appendDeleteKlong x depth cv) c w (fun _ v =>
      ∃ after, v.nodes.lookup x = some after ∧ keys.length ≤ after.cnt) := by
  have hold := n.cnt_ge_protected_keys keys hkeys hk
  have hadd := n.add_delete_cnt_ge_earlier_prefix c.i cut cv keys hkeys hcut hcv hk
  have hset := n.setAt_delete_cnt_ge_earlier_prefix cut cv keys hkeys hcut hcv hk
  unfold appendDeleteKlong
  simp only [writerWP_bind,writerWP_read]
  rw [writerWP_getNode_known x n c w hn]
  repeat' first
    | wpSimplify
    | simp only [note,putNode,hroom,hdeadAdd,hdeadSet,Bool.false_eq_true,↓reduceIte]
    | exact writerWP_throw _ _ _ _
    | (exact ⟨n,hn,hold⟩)
    | (exact ⟨_,upsert_lookup_same _ _ _,hadd⟩)
    | (exact ⟨_,upsert_lookup_same _ _ _,hset _ (by assumption)⟩)
    | (solve | simp_all only [Bool.false_and,Bool.false_eq_true])
    | split

/-- A full delete at a root made in this transaction retains an actual
cached prefix of m earlier live values, with the old height and take-back
status. The earlier values are a structural premise of this local rule. -/
theorem writerWP_handleFullWith_new_root_earlier_prefix
    (up : NodeId → List (Nat × NodeId) → M Unit) (x : NodeId)
    (n : KNode) (g h cut cv : Nat) (keys : List Nat) (ins : List (Nat × NodeId))
    (c : Ctx) (w : W) (hp : MergeParamsOK c.p)
    (hn : w.nodes.lookup x = some n) (hg : w.gh.lookup x = some (g,h))
    (ht : n.firstTime = some c.i) (hfresh : x < w.next)
    (hlen : keys.length = c.p.mergeBelow) (hkeys : keys.Nodup)
    (hcut : ∀ a ∈ keys, a < cut) (hcv : cut ≤ cv)
    (hk : ∀ a ∈ keys, ∃ y i, (.key a y,i) ∈ n.ks.zipIdx ∧ i ∉ n.lastBitmap)
    (hfull : c.p.splitAbove <
      (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))).size) :
    WriterWP (handleFullWith up 0 x ins
      (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))) false) c w
      (fun _ v => ∃ first kept,
        v.nodes.lookup x = some first ∧ kept.length = c.p.mergeBelow ∧
        kept.Pairwise (fun a b => a.1 < b.1) ∧ (∀ q ∈ kept, q.1 < cut) ∧
        (newKlongs c.i kept).IsPrefix first.ks ∧ c.p.mergeBelow ≤ first.cnt ∧
        first.onlyLiveKlong = none ∧ v.gh.lookup x = some (g,h) ∧ v.taken = w.taken) := by
  obtain ⟨kept,hkeepLen,hkeepOrder,hkeepCut,hkeepPrefix,hcount⟩ :=
    n.halves_delete_earlier_prefix c.i c.p hp cut cv keys hlen hkeys hcut hcv hk ins hfull
  refine writerWP_mono
    (writerWP_handleFullWith_new_root_first up x ins _ n g h c w hn hg ht hfresh hfull) ?_
  rintro _ v ⟨hnode,hgh,htaken⟩
  exact ⟨_,kept,hnode,hkeepLen,hkeepOrder,hkeepCut,hkeepPrefix,hcount,
    KNode.onlyLiveKlong_none_of_cnt_ge_two _ (Nat.le_trans hp.1 hcount),hgh,htaken⟩

end SIS.Tree
