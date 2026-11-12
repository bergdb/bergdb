import SIS.Tree.SegmentGet

namespace SIS.Tree

open SIS SIS.Check

/-- A reader's structural tree invariant: ordered ranges, well-formed
klongs and a complete recursive walk through inner and long-segment links. -/
def KeyTreeSound (p : Params) (v : View BVal) (t : Time) :
    Nat → NodeId → Nat → Option Nat → Prop
  | 0, _, _, _ => False
  | f+1, x, lo, hi => ∃ n, knodeOf p v x = some n ∧ klongsWf n.ks = true ∧
      NodeRange n t lo hi ∧ ∀ q ∈ childBounds (n.liveAt t) hi,
        (n.leaf && segLen q.1.1 != 7) = false →
        KeyTreeSound p v t f q.1.2
          (if n.leaf then 0 else if q.1.1 == 0 then lo else q.1.1)
          (if n.leaf then none else q.2)

theorem keyTreeSound_segmentSound (p : Params) (v : View BVal) (t f x lo : Nat)
    (hi : Option Nat) (hs : KeyTreeSound p v t f x lo hi) :
    SegmentSound p v t f x lo hi := by
  induction f generalizing x lo hi with
  | zero => exact hs.elim
  | succ f ih =>
    obtain ⟨n,hn,hwf,hr,hc⟩ := hs
    refine ⟨n,hn,hwf,hr,?_⟩
    intro hleaf q hq
    have hh := hc q hq (by simp [hleaf])
    simp only [hleaf,Bool.false_eq_true,↓reduceIte] at hh
    exact ih _ _ _ hh

theorem keyTreeSound_of_walk (p : Params) (P : Struct BVal) (t f : Nat)
    (hP : HighKindsOK p P) (x lo : Nat) (hi : Option Nat) (isRoot space : Bool)
    (hw : walk p (viewOf P) t f x lo hi isRoot space = []) :
    KeyTreeSound p (viewOf P) t f x lo hi := by
  induction f generalizing x lo hi isRoot space with
  | zero => simp only [walk,List.cons_ne_nil] at hw
  | succ f ih =>
    cases hv : P.get? x with
    | none => simp only [walk,viewOf,hv,List.cons_ne_nil] at hw
    | some nd =>
      cases hd : nd.isData with
      | true => simp only [walk,viewOf,hv,hd,↓reduceIte,List.cons_ne_nil] at hw
      | false =>
        have hl := highKindsOK_walk_level p P t f x lo hi isRoot space nd hP hv hd hw
        let n : KNode := ⟨p.heightOf nd.level == 0,klongsOf nd.hist⟩
        have hn : knodeOf p (viewOf P) x = some n := by
          simp [knodeOf,viewOf,hv,hd,Nat.not_lt_of_ge hl,n]
        refine ⟨n,hn,walk_current_wf p _ t f x lo hi isRoot space nd hv hd hw,
          walk_current_range p _ t f x lo hi isRoot space nd hv hd hw,?_⟩
        intro ⟨⟨c,y⟩,hi'⟩ hzip hterminal
        have hcy := childBounds_fst _ _ _ _ hzip
        have hp := walk_current_pointer p (viewOf P) t f x lo hi isRoot space nd hv hd hw
          c y (n.liveAt_key_mem t c y hcy)
        cases hvy : P.get? y with
        | none => simp [viewOf,hvy] at hp
        | some ny =>
          have hchild := List.flatMap_eq_nil_iff.mp
            (walk_child_faults_nil p (viewOf P) t f x lo hi isRoot space nd hv hd hw)
            ((c,y),hi') hzip
          change walkChildFaults p (viewOf P) t f x n (p.segOf nd.level)
            (p.heightOf nd.level) lo space ((c,y),hi') = [] at hchild
          cases hleaf : n.leaf with
          | true =>
            have hc : segLen c = 7 := by simpa [hleaf] using hterminal
            simp only [walkChildFaults,hleaf,hc,beq_self_eq_true,↓reduceIte,viewOf,hvy] at hchild
            simp only [hleaf,↓reduceIte]
            split at hchild
            · cases hchild
            · split at hchild
              · cases hchild
              · exact ih y 0 none true false hchild
          | false =>
            simp only [walkChildFaults,hleaf,Bool.false_eq_true,↓reduceIte,viewOf,hvy] at hchild
            simp only [hleaf,Bool.false_eq_true,↓reduceIte]
            split at hchild
            · cases hchild
            · split at hchild
              · cases hchild
              · exact ih y (if c == 0 then lo else c) hi' false space hchild

/-- Once a segment's structural depth fits, additional search fuel changes
no result. -/
theorem getEq_fuel_stable (p : Params) (v : View BVal) (t f x lo : Nat)
    (hi : Option Nat) (hs : SegmentSound p v t f x lo hi)
    (g : Nat) (hg : f ≤ g) (cv : Nat) :
    getEq p v t cv g x = getEq p v t cv f x := by
  induction f generalizing x lo hi g with
  | zero => exact hs.elim
  | succ f ih =>
    cases g with
    | zero => omega
    | succ g =>
      obtain ⟨n,hn,hwf,hr,hc⟩ := hs
      simp only [getEq,hn]
      cases hleaf : n.leaf with
      | true => simp only [hleaf,↓reduceIte]
      | false =>
        simp only [hleaf,Bool.false_eq_true,↓reduceIte]
        cases hf : n.searchLte t cv with
        | none => rfl
        | some fd =>
          have hmem := (n.searchLte_spec t cv).1 fd hf |>.1
          obtain ⟨b,hb⟩ := childBounds_exists (n.liveAt t) hi (fd.c,fd.y) hmem
          exact ih fd.y _ b (hc hleaf ((fd.c,fd.y),b) hb) g (by omega)

/-- The multisegment map obtained by enumerating every tree edge. Inner
links keep the key; a long segment prefixes it; a short segment names a value. -/
def treeContents (p : Params) (v : View BVal) (t : Time) :
    Nat → NodeId → List (Key × Nat)
  | 0, _ => []
  | f+1, x => match knodeOf p v x with
    | none => []
    | some n =>
      (n.liveAt t).flatMap (fun q =>
        if n.leaf then
          if segLen q.1 == 7 then
            (treeContents p v t f q.2).map (fun kv => (q.1::kv.1,kv.2))
          else match valueOf v q.2 with
            | none => []
            | some h => [([q.1],h)]
        else treeContents p v t f q.2)

theorem treeContents_keyWf (p : Params) (v : View BVal) (t f x : Nat) :
    ∀ q ∈ treeContents p v t f x, keyWf q.1 = true := by
  induction f generalizing x with
  | zero => simp [treeContents]
  | succ f ih =>
    intro kv hkv
    simp only [treeContents] at hkv
    cases hn : knodeOf p v x with
    | none => simp [hn] at hkv
    | some n =>
      simp only [hn] at hkv
      obtain ⟨q,hq,hkv⟩ := List.mem_flatMap.mp hkv
      cases hleaf : n.leaf with
      | false =>
        simp only [hleaf,Bool.false_eq_true,↓reduceIte] at hkv
        exact ih q.2 kv hkv
      | true =>
        simp only [hleaf,↓reduceIte] at hkv
        by_cases hlen : segLen q.1 = 7
        · simp only [hlen,beq_self_eq_true,↓reduceIte] at hkv
          obtain ⟨child,hchild,rfl⟩ := List.mem_map.mp hkv
          have hchildwf := ih q.2 child hchild
          cases hkey : child.1 with
          | nil => simp [hkey,keyWf] at hchildwf
          | cons c rest => simpa [keyWf,hlen,hkey] using hchildwf
        · simp only [show (segLen q.1 == 7) = false by simp [hlen],Bool.false_eq_true,↓reduceIte] at hkv
          cases hv : valueOf v q.2 with
          | none => simp [hv] at hkv
          | some h =>
            have he : kv = ([q.1],h) := by simpa [hv] using hkv
            simp [he,keyWf,hlen]

theorem treeContents_first_range (p : Params) (v : View BVal) (t f x lo : Nat)
    (hi : Option Nat) (hs : KeyTreeSound p v t f x lo hi) :
    ∀ cv rest h, (cv::rest,h) ∈ treeContents p v t f x → lo ≤ cv ∧ UpperBound hi cv := by
  induction f generalizing x lo hi with
  | zero => exact hs.elim
  | succ f ih =>
    obtain ⟨n,hn,hwf,hr,hc⟩ := hs
    intro cv rest h hkv
    simp only [treeContents,hn] at hkv
    obtain ⟨q,hq,hkv⟩ := List.mem_flatMap.mp hkv
    obtain ⟨b,hb⟩ := childBounds_exists (n.liveAt t) hi q hq
    have hqr := hr q hq
    cases hleaf : n.leaf with
    | true =>
      simp only [hleaf,↓reduceIte] at hkv hqr
      have hcv : cv = q.1 := by
        split at hkv
        · obtain ⟨child,_,heq⟩ := List.mem_map.mp hkv
          exact (List.cons.inj (congrArg Prod.fst heq)).1.symm
        · cases hv : valueOf v q.2 with
          | none => simp [hv] at hkv
          | some val =>
            have heq : (cv::rest,h) = ([q.1],val) := by simpa [hv] using hkv
            exact (List.cons.inj (congrArg Prod.fst heq)).1
      rwa [hcv]
    | false =>
      simp only [hleaf,Bool.false_eq_true,↓reduceIte] at hkv hqr
      have hchild := hc (q,b) hb (by simp [hleaf])
      simp only [hleaf,Bool.false_eq_true,↓reduceIte] at hchild
      obtain ⟨hlow,hhigh⟩ := ih q.2 _ b hchild cv rest h hkv
      constructor
      · split at hlow
        · exact hlow
        · rcases hqr.1 with hz | hlt
          · simp [hz] at *
          · omega
      · rcases childBounds_high (n.liveAt t) hi q b hb with he | ⟨s,hsm,he⟩
        · rwa [he] at hhigh
        · rw [he] at hhigh
          have hsbound := (hr s hsm).2
          cases hi with
          | none => trivial
          | some upper =>
            dsimp only [UpperBound] at hhigh hsbound ⊢
            omega

end SIS.Tree
