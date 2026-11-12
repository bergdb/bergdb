import SIS.Tree.DeleteCount

namespace SIS.Tree

open SIS SIS.Check

/-- The information in a klong other than the pointer of a key klong. -/
def klongShape : Klong → Klong
  | .key c _ => .key c 0
  | .time t => .time t
  | .del bits => .del bits

theorem cvAt_map_shape (ks : List Klong) (i : Nat) :
    cvAt (ks.map klongShape) i = cvAt ks i := by
  unfold cvAt
  rw [List.getElem?_map]
  cases hk : ks[i]? with
  | none => rfl
  | some k => cases k <;> rfl

theorem cvAt_map_shape_fun (ks : List Klong) : cvAt (ks.map klongShape) = cvAt ks := by
  funext i
  exact cvAt_map_shape ks i

theorem lastBitmapOf_map_shape (ks : List Klong) :
    lastBitmapOf (ks.map klongShape) = lastBitmapOf ks := by
  unfold lastBitmapOf
  rw [List.foldl_map]
  congr 1
  funext bits k
  cases k <;> rfl

theorem klongsWfStep_shape (ks : List Klong) (acc : Bool × Option Time × List Nat)
    (k : Klong) (i : Nat) :
    klongsWfStep (ks.map klongShape) acc (klongShape k,i) = klongsWfStep ks acc (k,i) := by
  unfold klongsWfStep
  rw [cvAt_map_shape_fun]
  cases k <;> rfl

theorem klongsWf_map_shape (ks : List Klong) : klongsWf (ks.map klongShape) = klongsWf ks := by
  rw [klongsWf_eq_fold,klongsWf_eq_fold,List.zipIdx_map,List.foldl_map]
  have he : (fun acc q => klongsWfStep (ks.map klongShape) acc (Prod.map klongShape id q)) =
      klongsWfStep ks := by
    funext acc q
    rcases q with ⟨k,i⟩
    exact klongsWfStep_shape ks acc k i
  simp only [he]

theorem klongsWf_of_shape_eq (a b : List Klong) (h : a.map klongShape = b.map klongShape) :
    klongsWf a = klongsWf b := by
  rw [← klongsWf_map_shape a,h,klongsWf_map_shape]

theorem KNode.live_has_cvAt (n : KNode) (c : Nat) :
    c ∈ n.live.map Prod.fst ↔ ∃ i, cvAt n.ks i = some c ∧ i ∉ n.lastBitmap := by
  rw [n.live_has_key]
  constructor
  · rintro ⟨y,i,hi,hdel⟩
    exact ⟨i,(cvAt_eq_some_iff n.ks i c).mpr ⟨y,List.mem_zipIdx_iff_getElem?.mp hi⟩,hdel⟩
  · rintro ⟨i,hcv,hdel⟩
    obtain ⟨y,hy⟩ := (cvAt_eq_some_iff n.ks i c).mp hcv
    exact ⟨y,i,List.mem_zipIdx_iff_getElem?.mpr hy,hdel⟩

theorem KNode.cnt_eq_of_shape (a b : KNode) (h : a.ks.map klongShape = b.ks.map klongShape) :
    a.cnt = b.cnt := by
  have hcv : cvAt a.ks = cvAt b.ks := by
    rw [← cvAt_map_shape_fun a.ks,h,cvAt_map_shape_fun]
  have hdel : a.lastBitmap = b.lastBitmap := by
    change lastBitmapOf a.ks = lastBitmapOf b.ks
    rw [← lastBitmapOf_map_shape a.ks,h,lastBitmapOf_map_shape]
  have hm : ∀ c, c ∈ a.live.map Prod.fst ↔ c ∈ b.live.map Prod.fst := by
    intro c
    rw [a.live_has_cvAt,b.live_has_cvAt,hcv,hdel]
  have hl := a.live_keys_nodup.length_le_of_subset (fun c hc => (hm c).mp hc)
  have hr := b.live_keys_nodup.length_le_of_subset (fun c hc => (hm c).mpr hc)
  simp only [List.length_map] at hl hr
  exact Nat.le_antisymm hl hr

theorem replaceKlong_go_shape (pre rest : List Klong) (cur : Option Time)
    (t c : Nat) (y : NodeId) (out : List Klong)
    (h : replaceKlong.go t c y pre rest cur = .ok (some out)) :
    out.map klongShape = (pre ++ rest).map klongShape := by
  induction rest generalizing pre cur with
  | nil => simp [replaceKlong.go] at h
  | cons k rest ih =>
    cases k with
    | time x =>
      simp only [replaceKlong.go] at h
      have hh := ih (pre ++ [.time x]) (some x) h
      simpa only [List.append_assoc,List.singleton_append] using hh
    | del bits => simp [replaceKlong.go] at h
    | key a z =>
      simp only [replaceKlong.go] at h
      split at h
      · rename_i hc
        have hac : a = c := by
          have hh : a = c ∧ cur = some t := by simpa only [Bool.and_eq_true,beq_iff_eq] using hc
          exact hh.1
        have hout : pre ++ Klong.key c y :: rest = out := by simpa using h
        rw [← hout]
        simp [klongShape,hac]
      · have hh := ih (pre ++ [.key a z]) cur h
        simpa only [List.append_assoc,List.singleton_append] using hh

theorem replaceKlong_shape (ks : List Klong) (t c : Nat) (y : NodeId) (out : List Klong)
    (h : replaceKlong ks t c y = .ok (some out)) :
    out.map klongShape = ks.map klongShape := by
  exact replaceKlong_go_shape [] ks none t c y out h

theorem KNode.add_key_lastBitmap (n : KNode) (t : Time) (c : Nat) (y : NodeId) :
    (n.add t (.key c y)).lastBitmap = n.lastBitmap := by
  unfold KNode.add
  split
  · split <;> simp only [KNode.lastBitmap,lastBitmapOf,List.foldl_append,List.foldl_cons,List.foldl_nil]
  · simp only [KNode.lastBitmap,lastBitmapOf,List.foldl_append,List.foldl_cons,List.foldl_nil]

theorem KNode.add_key_cnt_ge (n : KNode) (t : Time) (c : Nat) (y : NodeId) :
    n.cnt ≤ (n.add t (.key c y)).cnt := by
  have hh := (n.add t (.key c y)).cnt_ge_protected_keys (n.live.map Prod.fst) n.live_keys_nodup (by
    intro a ha
    obtain ⟨z,i,hi,hdel⟩ := (n.live_has_key a).mp ha
    refine ⟨z,i,prefix_mem_zipIdx (n.add_prefix t _) a z i hi,?_⟩
    rwa [n.add_key_lastBitmap])
  simpa only [List.length_map,KNode.cnt] using hh

theorem KNode.add_leaf (n : KNode) (t : Time) (k : Klong) : (n.add t k).leaf = n.leaf := by
  unfold KNode.add
  split
  · split <;> rfl
  · rfl

theorem KNode.cnt_with_leaf (n : KNode) (leaf : Bool) :
    ({n with leaf := leaf} : KNode).cnt = n.cnt := rfl

theorem KNode.repoint_shape (n : KNode) (i : Nat) (y : NodeId) :
    (n.repoint i y).ks.map klongShape = n.ks.map klongShape := by
  unfold KNode.repoint
  cases hk : n.ks[i]? with
  | none => rfl
  | some k =>
    cases k with
    | time t => rfl
    | del bits => rfl
    | key c z =>
      obtain ⟨hi,hget⟩ := List.getElem?_eq_some_iff.mp hk
      have hi' : i < (n.ks.map klongShape).length := by simpa using hi
      have he : (n.ks.map klongShape)[i] = Klong.key c 0 := by
        simp only [List.getElem_map,hget,klongShape]
      simp only [KNode.setAt,List.map_set,klongShape]
      rw [← he,List.set_getElem_self]

theorem KNode.repoint_cnt (n : KNode) (i : Nat) (y : NodeId) : (n.repoint i y).cnt = n.cnt :=
  KNode.cnt_eq_of_shape _ _ (n.repoint_shape i y)

theorem KNode.repoint_klongsWf (n : KNode) (i : Nat) (y : NodeId) :
    klongsWf (n.repoint i y).ks = klongsWf n.ks :=
  klongsWf_of_shape_eq _ _ (n.repoint_shape i y)

def retargetKlongs (ks : List Klong) (ti : Nat) (src dst : NodeId) : List Klong :=
  ks.zipIdx.map (fun (k,i) => match k with
    | .key cv y => if ti < i && y == src then Klong.key cv dst else k
    | _ => k)

theorem retargetKlongs_shape (ks : List Klong) (ti : Nat) (src dst : NodeId) :
    (retargetKlongs ks ti src dst).map klongShape = ks.map klongShape := by
  unfold retargetKlongs
  rw [List.map_map]
  calc
    _ = ks.zipIdx.map (fun q => klongShape q.1) := by
      congr 1
      funext q
      rcases q with ⟨k,i⟩
      cases k with
      | time t => rfl
      | del bits => rfl
      | key c y =>
        dsimp only [Function.comp_def]
        by_cases hc : (decide (ti < i) && y == src) = true <;>
          simp only [hc,Bool.false_eq_true,↓reduceIte,klongShape]
    _ = ks.map klongShape := by
      simpa only [List.map_map,Function.comp_def] using congrArg (List.map klongShape)
        (show ks.zipIdx.map Prod.fst = ks from by simp)

theorem klongsWf_retargetKlongs (ks : List Klong) (ti : Nat) (src dst : NodeId) :
    klongsWf (retargetKlongs ks ti src dst) = klongsWf ks :=
  klongsWf_of_shape_eq _ _ (retargetKlongs_shape ks ti src dst)

end SIS.Tree
