import SIS.Tree.GetInPlace

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! A put into the space root when it is a full leaf (bergdb 024-12, TP10;
`OpGetOK`'s rules): the split makes a new space root, and the writer's super
root names it (`newSuperRoot`). A space split gives the new root two klongs,
at compare value 0 to the first half and at the second half's first compare
value to the second; a time split makes the root's last version with the put
the new root. -/

/-! ## Readings that avoid some nodes -/

/-- Two readers that agree on the nodes reached from r0 outside D, whose links
avoid D, descend alike from those nodes. -/
theorem getEqR_avoid (N1 N2 : NodeId → Option KNode) (t : Time) (r0 : NodeId)
    (D : NodeId → Prop)
    (hsame : ∀ x, ReachS N1 t r0 x → ¬ D x → N2 x = N1 x)
    (hlinks : ∀ x xn c z, ReachS N1 t r0 x → N1 x = some xn → (c, z) ∈ xn.liveAt t → ¬ D z)
    (c : Nat) :
    ∀ (fu : Nat) (x : NodeId), ReachS N1 t r0 x → ¬ D x →
      getEqR N2 t c fu x = getEqR N1 t c fu x := by
  intro fu
  induction fu with
  | zero => intro x _ _; rfl
  | succ fu ih =>
    intro x hx hD
    simp only [getEqR, hsame x hx hD]
    cases hn : N1 x with
    | none => rfl
    | some xn =>
      simp only
      split
      · rfl
      · cases h1 : xn.searchLte t c with
        | none => rfl
        | some fd =>
          simp only
          have hmem := KNode.searchLte_mem xn t c fd h1
          exact ih fd.y (ReachS.step x xn fd.c fd.y hx hn hmem) (hlinks x xn fd.c fd.y hx hn hmem)

theorem getFromR_avoid (N1 N2 : NodeId → Option KNode) (V : NodeId → Option Nat) (t : Time)
    (fuel : Nat) (r0 : NodeId) (D : NodeId → Prop)
    (hwf : ∀ x xn, ReachS N1 t r0 x → N1 x = some xn → klongsWf xn.ks = true)
    (hsame : ∀ x, ReachS N1 t r0 x → ¬ D x → N2 x = N1 x)
    (hlinks : ∀ x xn c z, ReachS N1 t r0 x → N1 x = some xn → (c, z) ∈ xn.liveAt t → ¬ D z) :
    ∀ (key : List Nat) (r : NodeId), ReachS N1 t r0 r → ¬ D r →
      getFromR N2 V t fuel key r = getFromR N1 V t fuel key r := by
  intro key
  induction key with
  | nil => intro r _ _; rfl
  | cons cv rest ih =>
    intro r hr hD
    have he := getEqR_avoid N1 N2 t r0 D hsame hlinks cv fuel r hr hD
    cases rest with
    | nil => simp only [getFromR]; rw [he]
    | cons d rest' =>
      simp only [getFromR]
      rw [he]
      cases hg : getEqR N1 t cv fuel r with
      | none => rfl
      | some z =>
        simp only
        have hz : ReachS N1 t r0 z := getEqR_reach N1 t r0 cv hwf fuel r z hr hg
        obtain ⟨x, xn, cz, hx, hxn, _, hzm⟩ := getEqR_leaf_link N1 t r0 cv hwf fuel r z hr hg
        have hzD := hlinks x xn cz z hx hxn hzm
        rw [hsame z hz hzD]
        split
        · exact ih z hz hzD
        · rfl

/-! ## The new space root of a space split -/

theorem KNode.rootPair_live_lookup (t : Time) (F S : NodeId) (sc c' : Nat) :
    (⟨false, newKlongs t [(0, F), (sc, S)]⟩ : KNode).live.lookup c' =
      if sc = c' then some S else if 0 = c' then some F else none := by
  rw [KNode.newKlongs_live_lookup_fold]
  simp only [List.foldl_cons, List.foldl_nil, pairLookupStep]
  by_cases h1 : sc = c'
  · simp [h1]
  · by_cases h2 : 0 = c'
    · subst h2; simp [h1]
    · have h1' : (sc == c') = false := by simpa using h1
      have h2' : (0 == c') = false := by simpa using h2
      simp [h1', h2', h1, h2]

/-- The new root's search: the first half below sc, the second from it. -/
theorem KNode.rootPair_searchLte (t : Time) (F S : NodeId) (sc c : Nat) :
    ((⟨false, newKlongs t [(0, F), (sc, S)]⟩ : KNode).searchLte t c).map (·.y) =
      some (if c < sc then F else S) := by
  let rn : KNode := ⟨false, newKlongs t [(0, F), (sc, S)]⟩
  have hnd := KNode.live_keys_nodup rn
  have hmem : ∀ a y, (a, y) ∈ rn.live ↔ rn.live.lookup a = some y :=
    fun a y => mem_iff_lookup _ hnd a y
  have hcv : ∀ q ∈ rn.live, q.1 = sc ∨ q.1 = 0 := by
    intro q hq
    have := (hmem q.1 q.2).mp hq
    rw [KNode.rootPair_live_lookup] at this
    by_cases h1 : sc = q.1
    · exact Or.inl h1.symm
    · by_cases h2 : 0 = q.1
      · exact Or.inr h2.symm
      · simp [h1, h2] at this
  have ht : ∀ s, Klong.time s ∈ rn.ks → s ≤ t := newKlongs_times t _
  by_cases hc : c < sc
  · simp only [hc, ↓reduceIte]
    apply KNode.searchLte_of_max rn t ht c 0 F
    · rw [hmem, KNode.rootPair_live_lookup]
      have : ¬ sc = 0 := by omega
      simp [this]
    · omega
    · intro q hq hqc
      rcases hcv q hq with h | h
      · rw [h] at hqc; omega
      · omega
  · simp only [hc, ↓reduceIte]
    apply KNode.searchLte_of_max rn t ht c sc S
    · rw [hmem, KNode.rootPair_live_lookup]; simp
    · omega
    · intro q hq _
      rcases hcv q hq with h | h <;> omega

/-! ## The writer's space split of the space root -/

/-! ## The time split of the space root -/

/-! ## The space split in place of the space root -/

end SIS.Tree
