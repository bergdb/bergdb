import SIS.Tree.MergeFrozenPrefix

namespace SIS.Tree

open SIS SIS.Check

private def onlyKeyStep (del : List Nat) (acc : Option (Option (Nat × Nat)))
    (q : Klong × Nat) : Option (Option (Nat × Nat)) :=
  match acc with
  | none => none
  | some cur => match q.1 with
    | .key c _ =>
      if del.contains q.2 then acc else match cur with
        | some (_,cv) => if c != cv then none else some (some (q.2,c))
        | none => some (some (q.2,c))
    | _ => acc

private def onlyKeyAllows (c : Nat) : Option (Option (Nat × Nat)) → Prop
  | none => False
  | some none => True
  | some (some (_,a)) => a = c

private theorem onlyKeyStep_back (del : List Nat) (acc : Option (Option (Nat × Nat)))
    (q : Klong × Nat) (c : Nat) (ha : onlyKeyAllows c (onlyKeyStep del acc q)) :
    onlyKeyAllows c acc ∧ ∀ a y i, q = (.key a y,i) → i ∉ del → a = c := by
  rcases q with ⟨k,i⟩
  cases acc with
  | none => exact ha.elim
  | some cur =>
    cases k with
    | time t => exact ⟨ha,by intro a y j he; cases he⟩
    | del bits => exact ⟨ha,by intro a y j he; cases he⟩
    | key a y =>
      by_cases hi : i ∈ del
      · have hh : onlyKeyAllows c (some cur) := by simpa [onlyKeyStep,hi] using ha
        refine ⟨hh,?_⟩
        intro b z j he hj
        cases he
        exact (hj hi).elim
      · cases cur with
        | none =>
          have hac : a = c := by simpa [onlyKeyStep,onlyKeyAllows,hi] using ha
          exact ⟨trivial,by intro b z j he _; cases he; exact hac⟩
        | some jc =>
          rcases jc with ⟨j,b⟩
          have hab : a = b := by
            by_cases he : a = b
            · exact he
            · simp [onlyKeyStep,onlyKeyAllows,hi,he] at ha
          have hac : a = c := by simpa [onlyKeyStep,onlyKeyAllows,hi,hab] using ha
          exact ⟨by simpa [onlyKeyAllows,← hab] using hac,
            by intro d z e he _; cases he; exact hac⟩

private theorem onlyKeyFold_back (del : List Nat) (ks : List (Klong × Nat))
    (acc : Option (Option (Nat × Nat))) (c : Nat)
    (ha : onlyKeyAllows c (ks.foldl (onlyKeyStep del) acc)) :
    onlyKeyAllows c acc ∧
      ∀ a y i, (.key a y,i) ∈ ks → i ∉ del → a = c := by
  induction ks generalizing acc with
  | nil => exact ⟨ha,by simp⟩
  | cons q ks ih =>
    obtain ⟨hstep,htail⟩ := ih _ ha
    obtain ⟨hacc,hhead⟩ := onlyKeyStep_back del acc q c hstep
    refine ⟨hacc,?_⟩
    intro a y i hm hi
    simp only [List.mem_cons] at hm
    rcases hm with he | hm
    · exact hhead a y i he.symm hi
    · exact htail a y i hm hi

/-- A successful only-live-klong test permits at most one live compare
value, even when a physical node contains shadowed versions. -/
theorem KNode.onlyLiveKlong_some_cnt_le_one (n : KNode) (i : Nat)
    (hi : n.onlyLiveKlong = some i) : n.cnt ≤ 1 := by
  unfold KNode.onlyLiveKlong at hi
  change (match n.ks.zipIdx.foldl (onlyKeyStep n.lastBitmap) (some none) with
    | some (some (j,_)) => some j | _ => none) = some i at hi
  cases hr : n.ks.zipIdx.foldl (onlyKeyStep n.lastBitmap) (some none) with
  | none => simp only [hr] at hi; cases hi
  | some cur =>
    cases cur with
    | none => simp only [hr] at hi; cases hi
    | some jc =>
      rcases jc with ⟨j,c⟩
      have hall := (onlyKeyFold_back n.lastBitmap n.ks.zipIdx (some none) c
        (by rw [hr]; exact rfl)).2
      have hsub : ∀ a ∈ n.live.map Prod.fst, a ∈ [c] := by
        intro a ha
        obtain ⟨y,k,hm,hk⟩ := (n.live_has_key a).mp ha
        exact List.mem_singleton.mpr (hall a y k hm hk)
      have hlen := n.live_keys_nodup.length_le_of_subset hsub
      simpa only [List.length_map,List.length_singleton,KNode.cnt] using hlen

theorem KNode.onlyLiveKlong_none_of_cnt_ge_two (n : KNode) (hn : 2 ≤ n.cnt) :
    n.onlyLiveKlong = none := by
  cases hi : n.onlyLiveKlong with
  | none => rfl
  | some i => have := n.onlyLiveKlong_some_cnt_le_one i hi; omega

/-- The retained prefix of a split prevents the first half from passing
the root-collapse test. This concerns its actual live count. -/
theorem halves_first_protected_not_unary (p : Params) (hp : MergeParamsOK p)
    (leaf : Bool) (t : Time) (pairs ins : List (Nat × NodeId))
    (hs : pairs.Pairwise (fun a b => a.1 < b.1))
    (hfull : p.splitAbove < (⟨leaf,newKlongs t pairs⟩ : KNode).size) :
    (halves leaf t ⟨leaf,newKlongs t pairs⟩ ins).1.onlyLiveKlong = none := by
  apply KNode.onlyLiveKlong_none_of_cnt_ge_two
  exact Nat.le_trans hp.1 (halves_first_protected_fill p hp leaf t pairs ins hs hfull)

/-- The same barrier survives a merge into one node or into two: the first
output keeps enough distinct compare values from its left input. -/
theorem mergeKlongs_first_protected_not_unary (p : Params) (hp : MergeParamsOK p)
    (inner : Bool) (t : Time) (cR : Nat) (left right : List (Nat × NodeId))
    (hn : (left.map Prod.fst).Nodup) (hleft : p.mergeBelow ≤ left.length) :
    (⟨!inner,newKlongs t (mergeKlongs inner p.mergeMax cR left right).1⟩ : KNode).onlyLiveKlong = none := by
  apply KNode.onlyLiveKlong_none_of_cnt_ge_two
  exact Nat.le_trans hp.1
    (mergeKlongs_first_protected_fill p hp inner t cR left right hn hleft)

/-- Root collapse stops immediately after a descent to a cached node with
at least two live compare values. -/
theorem writerWP_collapseRoot_of_cnt_ge_two (key : Key) (g fuel : Nat)
    (c : Ctx) (w : W) (post : Unit → W → Prop)
    (hd : WriterWP (descendToSegmentRoot key g) c w (fun root v =>
      ∃ n, v.nodes.lookup root = some n ∧ 2 ≤ n.cnt ∧ post () v)) :
    WriterWP (collapseRoot key g (fuel+1)) c w post := by
  rw [collapseRoot]
  simp only [writerWP_bind,writerWP_read]
  refine writerWP_mono hd ?_
  rintro root v ⟨n,hn,hcnt,hpost⟩
  rw [writerWP_getNode_known root n c v hn]
  have honly := n.onlyLiveKlong_none_of_cnt_ge_two hcnt
  repeat' first
    | simp only [writerWP_bind,writerWP_pure,writerWP_get,replacedBy,honly]
    | exact hpost
    | split

/-- The merge loop stops on a cached non-root node whose live count meets
the threshold. The descent may also stop at depth zero. -/
theorem writerWP_mergeUp_of_full_node (key : Key) (g fuel h : Nat) (merged : Bool)
    (c : Ctx) (w : W) (post : Bool → W → Prop)
    (hd : WriterWP (descendToHeight key g h) c w (fun d v =>
      post merged v ∧ (d = 0 ∨
        ∃ (e q : Option Nat × NodeId) (n pn : KNode),
          v.path[d]? = some e ∧ v.path[d-1]? = some q ∧
          v.nodes.lookup e.2 = some n ∧ v.nodes.lookup q.2 = some pn ∧
          c.p.mergeBelow ≤ n.cnt))) :
    WriterWP (mergeUp key g (fuel+1) h merged) c w post := by
  rw [mergeUp]
  simp only [writerWP_bind,writerWP_read]
  refine writerWP_mono hd ?_
  rintro d v ⟨hpost,hnode⟩
  by_cases hd0 : d = 0
  · simp only [hd0,BEq.rfl,↓reduceIte,writerWP_pure]
    exact hpost
  · have hbeq : (d == 0) = false := by simp [hd0]
    simp only [hbeq,Bool.false_eq_true,↓reduceIte]
    rcases hnode with hd0' | ⟨e,q,n,pn,he,hq,hn,hpn,hcnt⟩
    · exact (hd0 hd0').elim
    · simp only [pathNode,he,hq,writerWP_bind,writerWP_pure,writerWP_get]
      rw [writerWP_getNode_known q.2 pn c v hpn]
      cases hleaf : pn.leaf
      · simp only [Bool.false_eq_true,↓reduceIte,writerWP_bind]
        rw [writerWP_getNode_known e.2 n c v hn]
        simpa only [hcnt,↓reduceIte,writerWP_pure] using hpost
      · simpa only [↓reduceIte,writerWP_pure] using hpost

/-- A retained physical prefix with no deleted indices supplies the merge
loop's live-count test. -/
theorem writerWP_mergeUp_of_protected_prefix (key : Key) (g fuel h : Nat) (merged : Bool)
    (c : Ctx) (w : W) (post : Bool → W → Prop)
    (hd : WriterWP (descendToHeight key g h) c w (fun d v =>
      post merged v ∧ (d = 0 ∨
        ∃ (e q : Option Nat × NodeId) (n pn : KNode) (t : Time)
            (pairs : List (Nat × NodeId)),
          v.path[d]? = some e ∧ v.path[d-1]? = some q ∧
          v.nodes.lookup e.2 = some n ∧ v.nodes.lookup q.2 = some pn ∧
          c.p.mergeBelow ≤ pairs.length ∧ (pairs.map Prod.fst).Nodup ∧
          (newKlongs t pairs).IsPrefix n.ks ∧ n.lastBitmap = []))) :
    WriterWP (mergeUp key g (fuel+1) h merged) c w post := by
  apply writerWP_mergeUp_of_full_node key g fuel h merged c w post
  refine writerWP_mono hd ?_
  rintro d v ⟨hpost,hnode⟩
  refine ⟨hpost,?_⟩
  rcases hnode with hd0 | ⟨e,q,n,pn,t,pairs,he,hq,hn,hpn,hlen,hnd,hprefix,hbitmap⟩
  · exact Or.inl hd0
  · exact Or.inr ⟨e,q,n,pn,he,hq,hn,hpn,
      Nat.le_trans hlen (n.cnt_ge_key_prefix t pairs hnd hprefix hbitmap)⟩

end SIS.Tree
