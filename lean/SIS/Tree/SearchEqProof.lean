import SIS.Tree.KlongBitmap

namespace SIS.Tree

open SIS SIS.Check

def eraseDeleted (bits : List Nat) : Option (Nat × NodeId) → Option (Nat × NodeId)
  | none => none
  | some q => if bits.contains q.1 then none else some q

def keyMatchStep (c : Nat) (v : Option (Nat × NodeId)) (q : Klong × Nat) :
    Option (Nat × NodeId) :=
  match q.1 with
  | .key a y => if a == c then some (q.2,y) else v
  | _ => v

def lastMatch (ks : List Klong) (c : Nat) : Option (Nat × NodeId) :=
  ks.zipIdx.foldl (keyMatchStep c) none

def eqBitmapStep (c : Nat) (acc : List Nat × Option (Nat × NodeId))
    (q : Klong × Nat) : List Nat × Option (Nat × NodeId) :=
  if acc.1.contains q.2 then acc else
    match q.1 with
    | .time _ => acc
    | .key a y => if a == c then (acc.1,some (q.2,y)) else acc
    | .del bits => (bits,eraseDeleted bits acc.2)

theorem eraseDeleted_absorb (old bits : List Nat)
    (hm : ∀ i ∈ old, i ∈ bits) (v : Option (Nat × NodeId)) :
    eraseDeleted bits (eraseDeleted old v) = eraseDeleted bits v := by
  cases v with
  | none => rfl
  | some q =>
    by_cases ho : q.1 ∈ old
    · have hb := hm q.1 ho
      simp [eraseDeleted,ho,hb]
    · simp [eraseDeleted,ho]

theorem zipIdx_fold_take_step {α : Type} (ks : List Klong)
    (f : α → Klong × Nat → α) (init : α) (i : Nat) (k : Klong)
    (hk : ks[i]? = some k) :
    (ks.take (i+1)).zipIdx.foldl f init = f ((ks.take i).zipIdx.foldl f init) (k,i) := by
  have hi : i < ks.length := (List.getElem?_eq_some_iff.mp hk).1
  simp only [List.take_add_one,hk,Option.toList_some,List.zipIdx_append,
    List.length_take,Nat.min_eq_left (Nat.le_of_lt hi),Nat.zero_add,
    List.zipIdx_cons,List.zipIdx_nil,List.foldl_append,List.foldl_cons,List.foldl_nil]

/-- The online search's index and pointer are determined by its latest
physical match and its current bitmap. -/
theorem eqBitmapFold_spec (ks : List Klong) (hr : BitmapRules ks)
    (c j : Nat) (hj : j ≤ ks.length) :
    let s := (ks.take j).zipIdx.foldl (eqBitmapStep c) ([],none)
    s.1 = lastBitmapOf (ks.take j) ∧
      s.2 = eraseDeleted (lastBitmapOf (ks.take j)) (lastMatch (ks.take j) c) := by
  induction j with
  | zero => exact ⟨rfl,rfl⟩
  | succ j ih =>
    have hj' : j < ks.length := by omega
    have hk : ks[j]? = some ks[j] := List.getElem?_eq_getElem hj'
    obtain ⟨hs1,hs2⟩ := ih (by omega)
    have hnot : (lastBitmapOf (ks.take j)).contains j = false := by
      simp only [List.contains_eq_mem,decide_eq_false_iff_not]
      intro hmem
      have := (bitmapRules_bounds ks hr j (by omega) j hmem).1
      omega
    have hmatch : lastMatch (ks.take (j+1)) c =
        keyMatchStep c (lastMatch (ks.take j) c) (ks[j],j) := by
      exact zipIdx_fold_take_step ks (keyMatchStep c) none j ks[j] hk
    change _ ∧ _
    rw [zipIdx_fold_take_step ks (eqBitmapStep c) ([],none) j ks[j] hk,
      lastBitmap_take_step ks j ks[j] hk,hmatch]
    cases he : ks[j] with
    | time t =>
      simpa only [eqBitmapStep,hs1,hnot,Bool.false_eq_true,↓reduceIte,
        bitmapNext,keyMatchStep] using And.intro hs1 hs2
    | key a y =>
      by_cases hac : a = c
      · simp only [eqBitmapStep,hs1,hnot,Bool.false_eq_true,↓reduceIte,
          bitmapNext,keyMatchStep,hac,beq_self_eq_true,eraseDeleted]
        trivial
      · simpa only [eqBitmapStep,hs1,hnot,Bool.false_eq_true,↓reduceIte,
          bitmapNext,keyMatchStep,show (a == c) = false from beq_eq_false_iff_ne.mpr hac]
          using And.intro hs1 hs2
    | del bits =>
      rw [he] at hk
      have hm := (hr j bits hk).2.1
      simp only [eqBitmapStep,hs1,hnot,Bool.false_eq_true,↓reduceIte,
        bitmapNext,keyMatchStep,hs2,eraseDeleted_absorb _ _ hm]
      trivial

theorem keyLookup_fold_none (xs : List (Klong × Nat)) (del : List Nat) (c : Nat)
    (hd : ∀ y i, (.key c y,i) ∈ xs → i ∈ del) :
    xs.foldl (keyLookupStep del c) none = none := by
  induction xs with
  | nil => rfl
  | cons q qs ih =>
    have ht : ∀ y i, (.key c y,i) ∈ qs → i ∈ del := by
      intro y i hi
      exact hd y i (List.mem_cons_of_mem _ hi)
    rcases q with ⟨k,i⟩
    cases k with
    | time t => exact ih ht
    | del bits => exact ih ht
    | key a y =>
      by_cases hac : a = c
      · subst a
        have hi := hd y i List.mem_cons_self
        simpa [List.foldl_cons,keyLookupStep,hi] using ih ht
      · simpa [List.foldl_cons,keyLookupStep,hac] using ih ht

theorem keyLookup_lastMatch (ks : List Klong) (del : List Nat)
    (hd : BitmapDownward ks del) (c : Nat) :
    keyLookup ks del c = (eraseDeleted del (lastMatch ks c)).map Prod.snd := by
  have hh : ∀ j, j ≤ ks.length →
      keyLookup (ks.take j) del c =
        (eraseDeleted del (lastMatch (ks.take j) c)).map Prod.snd := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      have hj' : j < ks.length := by omega
      have hk : ks[j]? = some ks[j] := List.getElem?_eq_getElem hj'
      have hlook : keyLookup (ks.take (j+1)) del c =
          keyLookupStep del c (keyLookup (ks.take j) del c) (ks[j],j) :=
        zipIdx_fold_take_step ks (keyLookupStep del c) none j ks[j] hk
      have hmatch : lastMatch (ks.take (j+1)) c =
          keyMatchStep c (lastMatch (ks.take j) c) (ks[j],j) :=
        zipIdx_fold_take_step ks (keyMatchStep c) none j ks[j] hk
      rw [hlook,hmatch]
      cases he : ks[j] with
      | time t => exact ih (by omega)
      | del bits => exact ih (by omega)
      | key a y =>
        by_cases hac : a = c
        · subst a
          by_cases hjd : j ∈ del
          · have hnone : keyLookup (ks.take j) del c = none := by
              apply keyLookup_fold_none
              intro z i hi
              have hi' : i < j := by
                have := (List.mem_zipIdx hi).2.1
                simp only [List.length_take] at this
                omega
              have hget := List.mem_zipIdx_iff_getElem?.mp hi
              have hkey : ks[i]? = some (.key c z) := by
                simpa only [List.getElem?_take,hi',↓reduceIte] using hget
              apply hd i j c (by omega)
              · simp only [cvAt,hkey]
              · simp only [cvAt,hk,he]
              · exact hjd
            simp [keyLookupStep,keyMatchStep,eraseDeleted,hjd,hnone]
          · simp [keyLookupStep,keyMatchStep,eraseDeleted,hjd]
        · simpa [keyLookupStep,keyMatchStep,hac] using ih (by omega)
  simpa only [List.take_length] using hh ks.length (Nat.le_refl _)

theorem searchEq_bitmap_projection (n : KNode) (t : Time) (c : Nat) :
    ((prefixAt n.ks t).zipIdx.foldl (eqBitmapStep c) ([],none)).2 =
      (n.searchEq t c).map (fun f => (f.idx,f.y)) := by
  have hh := List.foldl_hom
    (fun acc : Option Time × List Nat × Option Found =>
      (acc.2.1,acc.2.2.map (fun f => (f.idx,f.y))))
    (g₁ := fun (acc : Option Time × List Nat × Option Found) (q : Klong × Nat) =>
      if acc.2.1.contains q.2 then acc else
        match q.1 with
        | .time x => (some x,acc.2.1,acc.2.2)
        | .key a y => if a == c then (acc.1,acc.2.1,some ⟨c,q.2,acc.1.getD 0,y⟩) else acc
        | .del b => (acc.1,b,match acc.2.2 with
          | some f => if b.contains f.idx then none else some f
          | none => none))
    (g₂ := eqBitmapStep c) (l := (prefixAt n.ks t).zipIdx) (init := (none,[],none)) (by
      intro acc q
      rcases q with ⟨k,i⟩
      by_cases hskip : acc.2.1.contains i = true
      · simp only [eqBitmapStep,hskip,↓reduceIte]
      · cases k with
        | time x => simp only [eqBitmapStep,Bool.false_eq_true,hskip,↓reduceIte]
        | key a y =>
          by_cases hac : (a == c) = true <;>
            simp only [eqBitmapStep,Bool.false_eq_true,hskip,hac,↓reduceIte,Option.map_some]
        | del bits =>
          cases hf : acc.2.2 with
          | none => simp only [eqBitmapStep,Bool.false_eq_true,hskip,↓reduceIte,Option.map_none,eraseDeleted]
          | some f =>
            by_cases hb : bits.contains f.idx = true <;>
              simp only [eqBitmapStep,Bool.false_eq_true,hskip,hb,↓reduceIte,Option.map_some,
                Option.map_none,eraseDeleted])
  exact congrArg Prod.snd hh

theorem searchEqSpec : SearchEqSpec := by
  intro n t c hw
  let pre := prefixAt n.ks t
  have hp : pre.IsPrefix n.ks := List.takeWhile_prefix _
  have hr := bitmapRules_prefix hp (klongsWf_bitmapRules n.ks hw)
  have hs := (eqBitmapFold_spec pre hr c pre.length (Nat.le_refl _)).2
  simp only [List.take_length] at hs
  have hl := keyLookup_lastMatch pre (lastBitmapOf pre)
    (by simpa only [List.take_length] using
      bitmapRules_downward pre hr pre.length (Nat.le_refl _)) c
  have he := congrArg (Option.map Prod.snd) (searchEq_bitmap_projection n t c)
  simp only [Option.map_map,Function.comp_def] at he
  rw [KNode.liveAt_lookup]
  change (n.searchEq t c).map (fun f => f.y) = keyLookup pre (lastBitmapOf pre) c
  rw [← he,hs,hl]

end SIS.Tree
