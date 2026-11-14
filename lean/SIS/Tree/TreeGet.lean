import SIS.Tree.TreeReadModel

namespace SIS.Tree

open SIS SIS.Check

theorem keyTreeSound_node (p : Params) (v : View BVal) (t f x lo : Nat)
    (hi : Option Nat) (hs : KeyTreeSound p v t f x lo hi) :
    ∃ n, knodeOf p v x = some n := by
  cases f with
  | zero => exact hs.elim
  | succ f => exact ⟨hs.choose,hs.choose_spec.1⟩

/-- Restarting the segment search with the model's full fuel at an already
selected child changes no result. -/
theorem getFrom_inner_child (p : Params) (v : View BVal) (t f x lo : Nat)
    (hi : Option Nat) (hs : KeyTreeSound p v t (f+1) x lo hi) (hf : f+1 ≤ p.fuel)
    (n : KNode) (hn : knodeOf p v x = some n) (hleaf : n.leaf = false)
    (cv : Nat) (rest : Key) (fd : Found) (hfd : n.searchLte t cv = some fd) :
    getFrom p v t (cv::rest) x = getFrom p v t (cv::rest) fd.y := by
  have hseg := keyTreeSound_segmentSound p v t (f+1) x lo hi hs
  obtain ⟨n',hn',hwf,hr,hc⟩ := hs
  rw [hn] at hn'
  cases Option.some.inj hn'
  have hmem := (n.searchLte_spec t cv).1 fd hfd |>.1
  obtain ⟨b,hb⟩ := childBounds_exists (n.liveAt t) hi (fd.c,fd.y) hmem
  have hchild := hc ((fd.c,fd.y),b) hb (by simp [hleaf])
  simp only [hleaf,Bool.false_eq_true,↓reduceIte] at hchild
  have hchildseg := keyTreeSound_segmentSound p v t f fd.y _ b hchild
  have hget : getEq p v t cv p.fuel x = getEq p v t cv p.fuel fd.y := by
    calc
      getEq p v t cv p.fuel x = getEq p v t cv (f+1) x :=
        getEq_fuel_stable p v t (f+1) x lo hi hseg p.fuel hf cv
      _ = getEq p v t cv f fd.y := by simp only [getEq,hn,hleaf,Bool.false_eq_true,↓reduceIte,hfd]
      _ = getEq p v t cv p.fuel fd.y :=
        (getEq_fuel_stable p v t f fd.y _ b hchildseg p.fuel (by omega) cv).symm
  cases rest <;> simp only [getFrom,hget]

/-- The full multisegment get returns exactly the key/value pairs obtained
by enumerating the sound tree. This includes the historical time parameter. -/
theorem getFrom_treeContents (p : Params) (v : View BVal) (t f x lo : Nat)
    (hi : Option Nat) (hs : KeyTreeSound p v t f x lo hi) (hf : f ≤ p.fuel)
    (key : Key) (hkey : keyWf key = true) (value : Nat) :
    getFrom p v t key x = some value ↔ (key,value) ∈ treeContents p v t f x := by
  induction f generalizing x lo hi key with
  | zero => exact hs.elim
  | succ f ih =>
    have hwhole := hs
    have hseg := keyTreeSound_segmentSound p v t (f+1) x lo hi hs
    obtain ⟨n,hn,hwf,hr,hc⟩ := hs
    cases key with
    | nil => simp [keyWf] at hkey
    | cons cv rest =>
      simp only [treeContents,hn]
      cases hleaf : n.leaf with
      | false =>
        simp only [hleaf,Bool.false_eq_true,↓reduceIte]
        constructor
        · intro hget
          cases hfd : n.searchLte t cv with
          | none =>
            have heq : getEq p v t cv p.fuel x = none := by
              rw [getEq_fuel_stable p v t (f+1) x lo hi hseg p.fuel hf cv]
              simp only [getEq,hn,hleaf,Bool.false_eq_true,↓reduceIte,hfd]
            cases rest <;> simp [getFrom,heq] at hget
          | some fd =>
            have hmem := (n.searchLte_spec t cv).1 fd hfd |>.1
            obtain ⟨b,hb⟩ := childBounds_exists (n.liveAt t) hi (fd.c,fd.y) hmem
            have hchild := hc ((fd.c,fd.y),b) hb (by simp [hleaf])
            simp only [hleaf,Bool.false_eq_true,↓reduceIte] at hchild
            rw [getFrom_inner_child p v t f x lo hi hwhole hf n hn hleaf cv rest fd hfd] at hget
            exact List.mem_flatMap.mpr ⟨(fd.c,fd.y),hmem,
              (ih fd.y _ b hchild (by omega) (cv::rest) hkey).mp hget⟩
        · intro hmem
          obtain ⟨q,hq,hmem⟩ := List.mem_flatMap.mp hmem
          obtain ⟨b,hb⟩ := childBounds_exists (n.liveAt t) hi q hq
          have hchild := hc (q,b) hb (by simp [hleaf])
          simp only [hleaf,Bool.false_eq_true,↓reduceIte] at hchild
          obtain ⟨hlow,hhigh⟩ := treeContents_first_range p v t f q.2 _ b hchild cv rest value hmem
          have hsep : q.1 ≤ cv := by
            split at hlow
            · rename_i hz
              have hzero : q.1 = 0 := by simpa using hz
              omega
            · exact hlow
          obtain ⟨fd,hfd,_,hptr⟩ := n.searchLte_child t hi q b hb cv hsep hhigh
          rw [getFrom_inner_child p v t f x lo hi hwhole hf n hn hleaf cv rest fd hfd,hptr]
          exact (ih q.2 _ b hchild (by omega) (cv::rest) hkey).mpr hmem
      | true =>
        simp only [hleaf,↓reduceIte]
        have heq : getEq p v t cv p.fuel x = (n.liveAt t).lookup cv := by
          rw [getEq_fuel_stable p v t (f+1) x lo hi hseg p.fuel hf cv]
          simpa only [getEq,hn,hleaf,↓reduceIte] using searchEqSpec n t cv hwf
        cases rest with
        | nil =>
          have hterminal : segLen cv ≠ 7 := ((keyWf_singleton cv).mp hkey).2.2
          change ((getEq p v t cv p.fuel x).bind (valueOf v) = some value) ↔ _
          rw [heq]
          constructor
          · intro hget
            cases hy : (n.liveAt t).lookup cv with
            | none => simp [hy] at hget
            | some y =>
              have hv : valueOf v y = some value := by simpa only [hy,Option.bind_some] using hget
              refine List.mem_flatMap.mpr ⟨(cv,y),lookup_some_mem hy,?_⟩
              simp [hterminal,hv]
          · intro hmem
            obtain ⟨q,hq,hmem⟩ := List.mem_flatMap.mp hmem
            by_cases hlong : segLen q.1 = 7
            · simp only [hlong,beq_self_eq_true,↓reduceIte] at hmem
              obtain ⟨child,hchild,he⟩ := List.mem_map.mp hmem
              have hshape : q.1 = cv ∧ child.1 = [] := List.cons.inj (congrArg Prod.fst he)
              have hw := treeContents_keyShape p v t f q.2 child hchild
              simp [hshape.2,keyShape] at hw
            · simp only [show (segLen q.1 == 7) = false by simp [hlong],Bool.false_eq_true,↓reduceIte] at hmem
              cases hv : valueOf v q.2 with
              | none => simp [hv] at hmem
              | some val =>
                have he : ([cv],value) = ([q.1],val) := by simpa [hv] using hmem
                have hcv : cv = q.1 := (List.cons.inj (congrArg Prod.fst he)).1
                have hval : value = val := congrArg Prod.snd he
                have hy := lookup_some_of_mem (n.liveAt_keys_nodup t) hq
                simp [hcv,hy,hv,hval]
        | cons a rest =>
          have hlong : segLen cv = 7 ∧ keyWf (a::rest) = true :=
            ((keyWf_cons_cons cv a rest).mp hkey).2.2
          change (match getEq p v t cv p.fuel x with
            | some y => if (knodeOf p v y).isSome then getFrom p v t (a::rest) y else none
            | none => none) = some value ↔ _
          rw [heq]
          constructor
          · intro hget
            cases hy : (n.liveAt t).lookup cv with
            | none => simp [hy] at hget
            | some y =>
              have hmem := lookup_some_mem hy
              obtain ⟨b,hb⟩ := childBounds_exists (n.liveAt t) hi (cv,y) hmem
              have hchild := hc ((cv,y),b) hb (by simp [hleaf,hlong.1])
              simp only [hleaf,↓reduceIte] at hchild
              obtain ⟨child,hnode⟩ := keyTreeSound_node p v t f y 0 none hchild
              have hget' : getFrom p v t (a::rest) y = some value := by
                simpa only [hy,hnode,Option.isSome_some,↓reduceIte] using hget
              have hkv := (ih y 0 none hchild (by omega) (a::rest) hlong.2).mp hget'
              refine List.mem_flatMap.mpr ⟨(cv,y),hmem,?_⟩
              simp only [hlong.1,beq_self_eq_true,↓reduceIte]
              exact List.mem_map.mpr ⟨(a::rest,value),hkv,rfl⟩
          · intro hmem
            obtain ⟨q,hq,hmem⟩ := List.mem_flatMap.mp hmem
            by_cases hqLong : segLen q.1 = 7
            · simp only [hqLong,beq_self_eq_true,↓reduceIte] at hmem
              obtain ⟨child,hchildmem,he⟩ := List.mem_map.mp hmem
              have hkeys : q.1 = cv ∧ child.1 = a::rest := List.cons.inj (congrArg Prod.fst he)
              have hvals : child.2 = value := congrArg Prod.snd he
              obtain ⟨b,hb⟩ := childBounds_exists (n.liveAt t) hi q hq
              have hchild := hc (q,b) hb (by simp [hleaf,hqLong])
              simp only [hleaf,↓reduceIte] at hchild
              have hkv : (a::rest,value) ∈ treeContents p v t f q.2 := by
                simpa only [← hkeys.2,← hvals] using hchildmem
              have hget := (ih q.2 0 none hchild (by omega) (a::rest) hlong.2).mpr hkv
              obtain ⟨childNode,hnode⟩ := keyTreeSound_node p v t f q.2 0 none hchild
              have hy := lookup_some_of_mem (n.liveAt_keys_nodup t) hq
              simp only [← hkeys.1,hy,hnode,Option.isSome_some,↓reduceIte]
              exact hget
            · simp only [show (segLen q.1 == 7) = false by simp [hqLong],Bool.false_eq_true,↓reduceIte] at hmem
              cases hv : valueOf v q.2 with
              | none => simp [hv] at hmem
              | some val =>
                have he : (cv::a::rest,value) = ([q.1],val) := by simpa [hv] using hmem
                have he' := (List.cons.inj (congrArg Prod.fst he)).2
                cases he'

/-- The logical contents at a time, from that time's space root. -/
def rootContents (p : Params) (P : Struct BVal) (t : Time) : List (Key × Nat) :=
  match rootAt (viewOf P) t with
  | none => []
  | some r => treeContents p (viewOf P) t p.fuel r

theorem get_mem_rootContents (p : Params) (P : Struct BVal) (t : Time)
    (hP : HighKindsOK p P) (hi : InvOK p P t) (key : Key)
    (hkey : keyWf key = true) (value : Nat) :
    get p (viewOf P) t key = some value ↔ (key,value) ∈ rootContents p P t := by
  unfold InvOK faultsAt at hi
  unfold get rootContents
  cases hr : rootAt (viewOf P) t with
  | none => simp [hr] at hi
  | some r =>
    simp only [hr,Option.bind_some] at hi ⊢
    exact getFrom_treeContents p _ t p.fuel r 0 none
      (keyTreeSound_of_walk p P t p.fuel hP r 0 none true true hi)
      (Nat.le_refl _) key hkey value

theorem get_lookup_rootContents (p : Params) (P : Struct BVal) (t : Time)
    (hP : HighKindsOK p P) (hi : InvOK p P t) (key : Key) (hkey : keyWf key = true) :
    get p (viewOf P) t key = (rootContents p P t).lookup key := by
  cases he : (rootContents p P t).lookup key with
  | some value =>
    apply (get_mem_rootContents p P t hP hi key hkey value).mpr
    obtain ⟨pre,post,hm,_⟩ := List.lookup_eq_some_iff.mp he
    rw [hm]
    simp
  | none =>
    cases hg : get p (viewOf P) t key with
    | none => rfl
    | some value =>
      have hm := (get_mem_rootContents p P t hP hi key hkey value).mp hg
      have hn := List.lookup_eq_none_iff.mp he (key,value) hm
      simp at hn

end SIS.Tree
