/-
Dead klong counts of single nodes (bergdb 024-12, option 2's bound, 024-23):
the bitmap names only klongs of the node (`lastBitmapOf_lt`); a prefix of a
node's klongs, so its version before the transaction, holds no more dead
klongs than the node (`KNode.deadCount_take_le`, `KNode.deadCount_toPrev_le`);
pointing a key klong elsewhere keeps the count (`KNode.deadCount_repoint`).
Below the cascade's shapes (`ChainShape.lean`).
-/
import SIS.Tree.SpaceSplitDeadBound
import SIS.Tree.KlongDeleteAppend
import SIS.Tree.KlongRoundTripBits
import SIS.Tree.DeadProps
import SIS.Tree.WriterTreeMergeLive

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- Every bit of a node's last bitmap names a klong of the node. -/
theorem lastBitmapOf_lt (ks : List Klong) (hw : klongsWf ks = true) :
    ∀ b ∈ lastBitmapOf ks, b < ks.length := by
  intro b hb
  rcases lastBitmapFold_origin ks [] with he | hm
  · change lastBitmapOf ks = [] at he
    rw [he] at hb; cases hb
  · change .del (lastBitmapOf ks) ∈ ks at hm
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
    have hil : i < ks.length := (List.getElem?_eq_some_iff.mp hi).1
    have hs := klongsWfState_ok ks hw (i+1)
    rw [klongsWfState_succ ks i (.del (lastBitmapOf ks)) hi] at hs
    simp only [klongsWfStep, Bool.and_eq_true] at hs
    have hall := hs.1.2
    have hb' := List.all_eq_true.mp hall b hb
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb'
    omega

/-- The predicate of `KNode.deadCount`. -/
def deadP (ks : List Klong) (del : List Nat) : Klong × Nat → Bool := fun (k, i) => match k with
  | .key c _ => del.contains i || (ks.drop (i + 1)).any (fun k' => match k' with
      | .key c' _ => c' == c
      | _ => false)
  | _ => false

theorem KNode.deadCount_eq (n : KNode) :
    n.deadCount = (n.ks.zipIdx.filter (deadP n.ks n.lastBitmap)).length := rfl

/-- A key klong of a compare value that has no live klong in the node adds no
dead klong. -/
theorem KNode.deadCount_add_key_new (n : KNode) (t : Time) (c : Nat) (v : NodeId)
    (hw : klongsWf n.ks = true) (hnone : n.live.lookup c = none) :
    (n.add t (.key c v)).deadCount ≤ n.deadCount := by
  have hlb := KNode.add_key_lastBitmap n t c v
  have hlt := lastBitmapOf_lt n.ks hw
  obtain ⟨E, hE, hEk⟩ : ∃ E : List Klong, (n.add t (.key c v)).ks = n.ks ++ E ∧
      (E = [.time t, .key c v] ∨ E = [.key c v]) := by
    unfold KNode.add
    split
    · split
      · exact ⟨_, rfl, Or.inl rfl⟩
      · exact ⟨_, rfl, Or.inr rfl⟩
    · exact ⟨_, rfl, Or.inl rfl⟩
  rw [KNode.deadCount_eq, KNode.deadCount_eq, hlb, hE]
  generalize hdel : n.lastBitmap = del at hlt
  have hdel' : lastBitmapOf n.ks = del := hdel
  rw [hdel'] at hlt
  have hA : (n.ks.zipIdx.filter (deadP (n.ks ++ E) del)) = n.ks.zipIdx.filter (deadP n.ks del) := by
    apply List.filter_congr
    intro x hx
    obtain ⟨k, i⟩ := x
    have hki : n.ks[i]? = some k := by
      have := List.mem_zipIdx_iff_getElem?.mp hx
      simpa using this
    have hil : i < n.ks.length := (List.getElem?_eq_some_iff.mp hki).1
    cases k with
    | time _ => rfl
    | del _ => rfl
    | key c' y =>
      simp only [deadP]
      rw [List.drop_append_of_le_length (by omega), List.any_append]
      have hEany : E.any (fun k' => match k' with
          | .key c'' _ => c'' == c'
          | _ => false) = (c == c') := by
        rcases hEk with h | h <;> subst h <;> simp
      rw [hEany]
      cases hcc : (c == c') with
      | false => simp
      | true =>
        have hcc' : c = c' := by simpa using hcc
        subst hcc'
        cases hA : (del.contains i || (List.drop (i + 1) n.ks).any (fun k' => match k' with
            | .key c'' _ => c'' == c
            | _ => false)) with
        | true => simp
        | false =>
          exfalso
          simp only [Bool.or_eq_false_iff] at hA
          obtain ⟨h1, h2⟩ := hA
          have hl : LastLive n.ks n.lastBitmap i c := by
            refine ⟨⟨y, hki⟩, ?_, ?_⟩
            · intro hm
              rw [hdel] at hm
              have : del.contains i = true := List.elem_eq_true_of_mem hm
              rw [this] at h1; cases h1
            · intro j y' hij hj
              exfalso
              have hmem : Klong.key c y' ∈ List.drop (i + 1) n.ks := by
                have hj' : (List.drop (i + 1) n.ks)[j - (i + 1)]? = some (.key c y') := by
                  rw [List.getElem?_drop]
                  have : i + 1 + (j - (i + 1)) = j := by omega
                  rw [this]; exact hj
                exact List.mem_of_getElem? hj'
              have : (List.drop (i + 1) n.ks).any (fun k' => match k' with
                  | .key c'' _ => c'' == c
                  | _ => false) = true := List.any_eq_true.mpr ⟨_, hmem, by simp⟩
              rw [this] at h2; cases h2
          have hk := keyLookup_of_last n.lastBitmap c n.ks i y hki hl
          rw [← KNode.live_lookup, hnone] at hk
          cases hk
  rw [List.zipIdx_append, List.filter_append, List.length_append, hA]
  have hB : ((E.zipIdx (0 + n.ks.length)).filter (deadP (n.ks ++ E) del)).length = 0 := by
    have hm1 : n.ks.length ∉ del := fun h => by have := hlt _ h; omega
    have hm2 : n.ks.length + 1 ∉ del := fun h => by have := hlt _ h; omega
    rcases hEk with h | h <;> subst h
    · have hd : List.drop (n.ks.length + 1 + 1) (n.ks ++ [Klong.time t, Klong.key c v]) = [] :=
        List.drop_eq_nil_of_le (by simp)
      simp [deadP, hm2, hd, List.zipIdx_cons]
    · have hd : List.drop (n.ks.length + 1) (n.ks ++ [Klong.key c v]) = [] :=
        List.drop_eq_nil_of_le (by simp)
      simp [deadP, hm1, hd, List.zipIdx_cons]
  omega

/-! ## A prefix holds no more dead klongs -/

/-- A later bitmap holds every bit of an earlier one (`klongsWf`). -/
theorem lastBitmapOf_take_mono (ks : List Klong) (hw : klongsWf ks = true) (m : Nat) :
    ∀ j, m ≤ j → ∀ b ∈ lastBitmapOf (ks.take m), b ∈ lastBitmapOf (ks.take j) := by
  intro j hj
  induction j with
  | zero => intro b hb; have : m = 0 := by omega
            subst this; exact hb
  | succ j ih =>
    intro b hb
    rcases Nat.eq_or_lt_of_le hj with h | h
    · subst h; exact hb
    · have hb' := ih (by omega) b hb
      rcases Nat.lt_or_ge j ks.length with hl | hl
      · obtain ⟨k, hk⟩ : ∃ k, ks[j]? = some k := ⟨ks[j], List.getElem?_eq_getElem hl⟩
        have hs := klongsWfState_ok ks hw (j+1)
        rw [klongsWfState_succ ks j k hk] at hs
        rw [← klongsWfState_bitmap] at hb' ⊢
        rw [klongsWfState_succ ks j k hk]
        cases k with
        | time x => simpa [klongsWfStep] using hb'
        | key c y => simpa [klongsWfStep] using hb'
        | del bits =>
          simp only [klongsWfStep, Bool.and_eq_true] at hs
          have hall := hs.1.1.1.1.2
          have := List.all_eq_true.mp hall b hb'
          simp only [klongsWfStep]
          exact List.mem_of_elem_eq_true this
      · have h1 : ks.take (j+1) = ks.take j := by
          rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
        rw [h1]; exact hb'

theorem length_filter_mono {α : Type} (l : List α) (p q : α → Bool)
    (h : ∀ x ∈ l, p x = true → q x = true) : (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ih' := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.filter_cons]
    cases hp : p a <;> cases hq : q a <;> simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons]
    · omega
    · omega
    · have := h a List.mem_cons_self hp; rw [hq] at this; cases this
    · omega

/-- A prefix of a node's klongs holds no more dead klongs than the node. -/
theorem KNode.deadCount_take_le (leaf : Bool) (ks : List Klong) (hw : klongsWf ks = true) (m : Nat) :
    (⟨leaf, ks.take m⟩ : KNode).deadCount ≤ (⟨leaf, ks⟩ : KNode).deadCount := by
  rw [KNode.deadCount_eq, KNode.deadCount_eq]
  simp only [KNode.lastBitmap]
  have hsub : (ks.take m).zipIdx.Sublist ks.zipIdx := by
    have he : ks.zipIdx = (ks.take m).zipIdx ++ (ks.drop m).zipIdx (0 + (ks.take m).length) := by
      have := List.zipIdx_append (xs := ks.take m) (ys := ks.drop m) (k := 0)
      rw [List.take_append_drop] at this
      exact this
    rw [he]
    exact List.sublist_append_left _ _
  refine Nat.le_trans (length_filter_mono _ _ (deadP ks (lastBitmapOf ks)) ?_)
    (hsub.filter _).length_le
  intro x hx hpx
  obtain ⟨k, i⟩ := x
  cases k with
  | time _ => cases hpx
  | del _ => cases hpx
  | key c y =>
    simp only [deadP, Bool.or_eq_true] at hpx ⊢
    rcases hpx with h1 | h1
    · left
      have hb := List.mem_of_elem_eq_true h1
      have hlen : m ≤ ks.length ∨ ks.length ≤ m := Nat.le_total _ _
      have hmono := lastBitmapOf_take_mono ks hw m (max m ks.length) (Nat.le_max_left _ _) i hb
      have htk : ks.take (max m ks.length) = ks := List.take_of_length_le (Nat.le_max_right _ _)
      rw [htk] at hmono
      exact List.elem_eq_true_of_mem hmono
    · right
      obtain ⟨k', hk', hk2⟩ := List.any_eq_true.mp h1
      refine List.any_eq_true.mpr ⟨k', ?_, hk2⟩
      rw [List.drop_take] at hk'
      exact List.mem_of_mem_take hk'

/-- `toPrev` holds no more dead klongs than the node. -/
theorem KNode.deadCount_toPrev_le (n : KNode) (t : Time) (hw : klongsWf n.ks = true) :
    (n.toPrev t).deadCount ≤ n.deadCount := by
  have hp : (prefixAt n.ks t).IsPrefix n.ks := List.takeWhile_prefix _
  obtain ⟨hpe⟩ : ∃ _ : prefixAt n.ks t = n.ks.take (prefixAt n.ks t).length, True :=
    ⟨List.prefix_iff_eq_take.mp hp, trivial⟩
  have h := KNode.deadCount_take_le n.leaf n.ks hw (prefixAt n.ks t).length
  have e1 : n.toPrev t = ⟨n.leaf, n.ks.take (prefixAt n.ks t).length⟩ := by
    unfold KNode.toPrev; rw [← hpe]
  have e2 : n = ⟨n.leaf, n.ks⟩ := rfl
  rw [e1]
  exact Nat.le_trans h (Nat.le_of_eq (by rw [← e2]))


/-! ## Pointers do not count -/

theorem KNode.deadCount_map_shape (leaf : Bool) (ks : List Klong) :
    (⟨leaf, ks.map klongShape⟩ : KNode).deadCount = (⟨leaf, ks⟩ : KNode).deadCount := by
  unfold KNode.deadCount
  have hb : (⟨leaf, ks.map klongShape⟩ : KNode).lastBitmap = (⟨leaf, ks⟩ : KNode).lastBitmap :=
    lastBitmapOf_map_shape ks
  rw [hb]
  simp only [List.zipIdx_map, List.filter_map, List.length_map]
  congr 2
  funext q
  rcases q with ⟨k, i⟩
  cases k with
  | key c y =>
    simp only [Function.comp_def, Prod.map, id, klongShape, ← List.map_drop, List.any_map]
    congr 2
    funext k'
    cases k' <;> rfl
  | time t => rfl
  | del b => rfl

/-- Pointing a key klong elsewhere keeps the dead count. -/
theorem KNode.deadCount_repoint (n : KNode) (i : Nat) (y : NodeId) :
    (n.repoint i y).deadCount = n.deadCount := by
  unfold KNode.repoint
  cases hk : n.ks[i]? with
  | none => rfl
  | some k =>
    cases k with
    | time _ => rfl
    | del _ => rfl
    | key c y0 =>
      simp only [KNode.setAt]
      have hs : (n.ks.set i (Klong.key c y)).map klongShape = n.ks.map klongShape := by
        rw [List.map_set]
        apply List.ext_getElem?
        intro j
        rw [List.getElem?_set]
        split
        · rename_i hj
          subst hj
          rw [List.getElem?_map, hk]
          have hil : i < n.ks.length := (List.getElem?_eq_some_iff.mp hk).1
          simp [klongShape, hil]
        · rfl
      have e1 := KNode.deadCount_map_shape n.leaf (n.ks.set i (Klong.key c y))
      have e2 := KNode.deadCount_map_shape n.leaf n.ks
      rw [hs] at e1
      have e3 : ({ n with ks := n.ks.set i (Klong.key c y) } : KNode) =
          ⟨n.leaf, n.ks.set i (Klong.key c y)⟩ := rfl
      have e4 : n = ⟨n.leaf, n.ks⟩ := rfl
      rw [e3, ← e1, e2, ← e4]

/-- A new root with the empty key's klong and one more holds no dead klong. -/
theorem KNode.deadCount_newRoot (t : Time) (a b : NodeId) (sc : Nat) (hsc : 0 < sc) :
    (⟨false, [Klong.time t, .key 0 a, .key sc b]⟩ : KNode).deadCount = 0 := by
  have h := KNode.newKlongs_deadCount false t [(0, a), (sc, b)] (by simp; omega)
  exact h

end SIS.Tree
