import SIS.Tree.GetSplit
import SIS.Tree.GetUnder
import SIS.Tree.WriterTreeVisits
import SIS.Tree.WriterTreeSpace

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! A put into a full leaf below an inner parent with room, by a space split
(bergdb 024-12, TP10; `OpGetOK`'s rules): the leaf's last version and the
put's klong go to two new leaves, the parent's klong to the leaf names the
first and a new klong at the second half's first compare value names the
second. Reading a key through the parent gives what reading the leaf with the
put gave (`halves_leaf_lookup`), if the leaf's compare values lie between the
parent's klong to it and the parent's next one (the search tree's order). -/

/-! ## The parent's search after the split -/

theorem KNode.searchLte_of_max (m : KNode) (t : Time) (ht : ∀ s, Klong.time s ∈ m.ks → s ≤ t)
    (c : Int) (ec : Nat) (ey : NodeId) (hm : (ec, ey) ∈ m.live) (hle : (ec : Int) ≤ c)
    (hmax : ∀ q ∈ m.live, (q.1 : Int) ≤ c → q.1 ≤ ec) :
    (m.searchLte t c).map (·.y) = some ey := by
  have hs := m.searchLte_spec t c
  unfold NodeSearchSpec at hs
  rw [KNode.liveAt_of_times m t ht] at hs
  cases h : m.searchLte t c with
  | none =>
    have := hs.2.mp h (ec, ey) hm
    simp only [decide_eq_false_iff_not] at this
    exact absurd hle this
  | some f =>
    obtain ⟨hfm, hfa, hfmax⟩ := hs.1 f h
    simp only [decide_eq_true_eq] at hfa
    have h1 := hfmax (ec, ey) hm (by simpa using hle)
    have h2 := hmax (f.c, f.y) hfm hfa
    simp only [decide_eq_true_eq] at h1
    have hc : f.c = ec := by omega
    have hnd := KNode.live_keys_nodup m
    have hm' : (f.c, ey) ∈ m.live := by rw [hc]; exact hm
    have := (lookup_some_of_mem hnd hfm).symm.trans (lookup_some_of_mem hnd hm')
    simp only [Option.map_some, Option.some.injEq]
    exact Option.some.inj this

theorem KNode.searchLte_none_of (m : KNode) (t : Time) (ht : ∀ s, Klong.time s ∈ m.ks → s ≤ t)
    (c : Int) (hall : ∀ q ∈ m.live, c < (q.1 : Int)) : m.searchLte t c = none := by
  have hs := m.searchLte_spec t c
  unfold NodeSearchSpec at hs
  rw [KNode.liveAt_of_times m t ht] at hs
  apply hs.2.mpr
  intro q hq
  have := hall q hq
  simp only [decide_eq_false_iff_not]
  omega

/-- The parent after a space split of its child L: its klong k1 to L names the
first half F, and a klong at sc names the second half S. A search that found
k1 finds F below sc and S from sc on; any other search finds what it found. -/
theorem KNode.splitParent_searchLte (n : KNode) (t : Time) (k1 sc : Nat) (L F S : NodeId)
    (hw : klongsWf n.ks = true) (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t)
    (hk1 : (k1, L) ∈ n.live) (hle : k1 ≤ sc)
    (hgap : ∀ c' z, (c', z) ∈ n.live → c' ≤ k1 ∨ sc < c') (c : Int) :
    (((n.add t (.key k1 F)).add t (.key sc S)).searchLte t c).map (·.y) =
      (n.searchLte t c).map (fun fd => if fd.c = k1 then (if c < sc then F else S) else fd.y) := by
  have hw1 := KNode.add_key_wf n t k1 F hw
  have ht1 := KNode.add_times n t (.key k1 F) (fun s h => by cases h) ht
  have ht2 := KNode.add_times _ t (.key sc S) (fun s h => by cases h) ht1
  have hlk : ∀ c', ((n.add t (.key k1 F)).add t (.key sc S)).live.lookup c' =
      if sc == c' then some S else if k1 == c' then some F else n.live.lookup c' := by
    intro c'
    rw [KNode.add_key_live_lookup_of_wf _ t sc c' S hw1, KNode.add_key_live_lookup_of_wf n t k1 c' F hw]
  have hnd := KNode.live_keys_nodup n
  have hnd2 := KNode.live_keys_nodup ((n.add t (.key k1 F)).add t (.key sc S))
  have hmem2 : ∀ c' z, (c', z) ∈ ((n.add t (.key k1 F)).add t (.key sc S)).live ↔
      (if sc = c' then z = S else if k1 = c' then z = F else (c', z) ∈ n.live) := by
    intro c' z
    rw [mem_iff_lookup _ hnd2, hlk]
    by_cases h1 : sc = c'
    · subst h1; simp [eq_comm]
    · have h1' : (sc == c') = false := by simpa using h1
      simp only [h1', Bool.false_eq_true, ↓reduceIte, h1]
      by_cases h2 : k1 = c'
      · subst h2; simp [eq_comm]
      · have h2' : (k1 == c') = false := by simpa using h2
        simp only [h2', Bool.false_eq_true, ↓reduceIte, h2]
        rw [mem_iff_lookup _ hnd]
  -- every compare value of the new node: sc, k1 or one of n's
  have hcv2 : ∀ q ∈ ((n.add t (.key k1 F)).add t (.key sc S)).live,
      q.1 = sc ∨ q.1 = k1 ∨ q ∈ n.live := by
    intro q hq
    have := (hmem2 q.1 q.2).mp hq
    by_cases h1 : sc = q.1
    · exact Or.inl h1.symm
    · simp only [h1, ↓reduceIte] at this
      by_cases h2 : k1 = q.1
      · exact Or.inr (Or.inl h2.symm)
      · simp only [h2, ↓reduceIte] at this
        exact Or.inr (Or.inr this)
  have hs1 := n.searchLte_spec t c
  unfold NodeSearchSpec at hs1
  rw [KNode.liveAt_of_times n t ht] at hs1
  have hk1live : ((k1, F) ∈ ((n.add t (.key k1 F)).add t (.key sc S)).live) ∨ sc = k1 := by
    by_cases h : sc = k1
    · exact Or.inr h
    · left; rw [hmem2]; simp [h]
  have hsclive : (sc, S) ∈ ((n.add t (.key k1 F)).add t (.key sc S)).live := by
    rw [hmem2]; simp
  cases h1 : n.searchLte t c with
  | none =>
    have hall := hs1.2.mp h1
    have hk1c : c < (k1 : Int) := by
      have := hall (k1, L) hk1
      simp only [decide_eq_false_iff_not] at this
      omega
    rw [KNode.searchLte_none_of _ t ht2 c (fun q hq => by
      rcases hcv2 q hq with h | h | h
      · rw [h]; omega
      · rw [h]; exact hk1c
      · have := hall q h
        simp only [decide_eq_false_iff_not] at this
        omega)]
    rfl
  | some fd =>
    obtain ⟨hfm, hfa, hfmax⟩ := hs1.1 fd h1
    simp only [decide_eq_true_eq] at hfa
    simp only [Option.map_some]
    by_cases hfk : fd.c = k1
    · simp only [hfk, ↓reduceIte]
      by_cases hcs : c < (sc : Int)
      · simp only [hcs, ↓reduceIte]
        have hsk : sc ≠ k1 := by
          intro he; rw [hfk] at hfa; omega
        rcases hk1live with hk | hk
        · apply KNode.searchLte_of_max _ t ht2 c k1 F hk (by rw [← hfk]; exact hfa)
          intro q hq hqc
          rcases hcv2 q hq with h | h | h
          · rw [h] at hqc; omega
          · omega
          · have := hfmax q h (by simpa using hqc)
            simp only [decide_eq_true_eq] at this
            omega
        · exact absurd hk hsk
      · simp only [hcs, ↓reduceIte]
        apply KNode.searchLte_of_max _ t ht2 c sc S hsclive (by omega)
        intro q hq hqc
        rcases hcv2 q hq with h | h | h
        · omega
        · omega
        · have := hfmax q h (by simpa using hqc)
          simp only [decide_eq_true_eq] at this
          omega
    · simp only [hfk, ↓reduceIte]
      have hfsc : fd.c ≠ sc := by
        intro he
        rcases hgap fd.c fd.y hfm with h | h
        · omega
        · omega
      have hmem : (fd.c, fd.y) ∈ ((n.add t (.key k1 F)).add t (.key sc S)).live := by
        rw [hmem2]
        simp only [show ¬ sc = fd.c from fun h => hfsc h.symm, show ¬ k1 = fd.c from fun h => hfk h.symm,
          ↓reduceIte]
        exact hfm
      apply KNode.searchLte_of_max _ t ht2 c fd.c fd.y hmem hfa
      intro q hq hqc
      rcases hcv2 q hq with h | h | h
      · -- sc ≤ c: then k1 ≤ c, k1 ≤ fd.c, so sc < fd.c
        have hk := hfmax (k1, L) hk1 (by simp; omega)
        simp only [decide_eq_true_eq] at hk
        rcases hgap fd.c fd.y hfm with h' | h'
        · omega
        · omega
      · rw [h] at hqc ⊢
        have hk := hfmax (k1, L) hk1 (by simpa using hqc)
        simpa using hk
      · have := hfmax q h (by simpa using hqc)
        simpa using this

/-! ## The writer's space split below an inner parent with room -/

theorem writerWP_klongAt (d k1 : Nat) (L : NodeId) (c : Ctx) (w : W)
    (h : w.path[d]? = some (some k1, L)) (post : Nat → W → Prop) :
    WriterWP (klongAt d) c w post ↔ post k1 w := by
  unfold klongAt
  simp only [writerWP_bind, writerWP_get, h, writerWP_pure]

/-! ## The reading after the split -/

/-- The descents of reader N2, in which q's klong to the leaf L names F below
compare value sc and S from it, and F and S read as L for those compare values,
are those of reader Nm, on the nodes that Nm reaches but L, F and S. -/
theorem getEqR_split (Nm N2 : NodeId → Option KNode) (t : Time) (r0 L q F S : NodeId)
    (qn qn2 m f s : KNode) (sc : Nat)
    (hNq : Nm q = some qn) (hql : qn.leaf = false) (hN2q : N2 q = some qn2)
    (hq2l : qn2.leaf = false)
    (hqsearch : ∀ c : Nat, (qn2.searchLte t c).map (·.y) =
      (qn.searchLte t c).map (fun fd => if fd.y = L then (if c < sc then F else S) else fd.y))
    (hNmL : Nm L = some m) (hml : m.leaf = true)
    (hN2F : N2 F = some f) (hfl : f.leaf = true) (hN2S : N2 S = some s) (hsl : s.leaf = true)
    (hleafF : ∀ c, c < sc → (f.searchEq t c).map (·.y) = (m.searchEq t c).map (·.y))
    (hleafS : ∀ c, sc ≤ c → (s.searchEq t c).map (·.y) = (m.searchEq t c).map (·.y))
    (hsame : ∀ x, x ≠ L → x ≠ q → x ≠ F → x ≠ S → N2 x = Nm x)
    (hnotL : ∀ x xn c z, ReachS Nm t r0 x → x ≠ q → Nm x = some xn → (c, z) ∈ xn.liveAt t → z ≠ L)
    (hnotFS : ∀ x xn c z, ReachS Nm t r0 x → Nm x = some xn → (c, z) ∈ xn.liveAt t →
      (z ≠ L → z ≠ F) ∧ z ≠ S) (c : Nat) :
    ∀ (fu : Nat) (x : NodeId), ReachS Nm t r0 x → x ≠ L → x ≠ F → x ≠ S →
      getEqR N2 t c fu x = getEqR Nm t c fu x := by
  -- reading a leaf the split made, or L, for a compare value routed to it
  have hleafRead : ∀ fu, getEqR N2 t c fu (if c < sc then F else S) = getEqR Nm t c fu L := by
    intro fu
    cases fu with
    | zero => rfl
    | succ fu =>
      by_cases hcs : c < sc
      · simp only [hcs, ↓reduceIte, getEqR, hN2F, hfl, hNmL, hml]
        exact hleafF c hcs
      · simp only [hcs, ↓reduceIte, getEqR, hN2S, hsl, hNmL, hml]
        exact hleafS c (by omega)
  intro fu
  induction fu with
  | zero => intro x _ _ _ _; rfl
  | succ fu ih =>
    intro x hx hxL hxF hxS
    by_cases hxq : x = q
    · subst hxq
      simp only [getEqR, hNq, hN2q, hql, hq2l, Bool.false_eq_true, ↓reduceIte]
      have hs := hqsearch c
      cases h1 : qn.searchLte t c with
      | none =>
        rw [h1] at hs
        cases h2 : qn2.searchLte t c with
        | none => rfl
        | some _ => rw [h2] at hs; cases hs
      | some fd =>
        rw [h1] at hs
        cases h2 : qn2.searchLte t c with
        | none => rw [h2] at hs; cases hs
        | some fd2 =>
          rw [h2] at hs
          simp only [Option.map_some, Option.some.injEq] at hs
          simp only
          have hmem := KNode.searchLte_mem qn t c fd h1
          have hrfd : ReachS Nm t r0 fd.y := ReachS.step x qn fd.c fd.y hx hNq hmem
          by_cases hL : fd.y = L
          · rw [hL] at hs
            simp only [↓reduceIte] at hs
            rw [hs, hL]
            exact hleafRead fu
          · simp only [hL, ↓reduceIte] at hs
            rw [hs]
            have hfs := hnotFS x qn fd.c fd.y hx hNq hmem
            exact ih fd.y hrfd hL (hfs.1 hL) hfs.2
    · have he := hsame x hxL hxq hxF hxS
      simp only [getEqR, he]
      cases hn : Nm x with
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
            have hrfd : ReachS Nm t r0 fd.y := ReachS.step x xn fd.c fd.y hx hn hmem
            have hfs := hnotFS x xn fd.c fd.y hx hn hmem
            have hnL := hnotL x xn fd.c fd.y hx hxq hn hmem
            exact ih fd.y hrfd hnL (hfs.1 hnL) hfs.2

/-- What a descent finds is named by a live klong of a leaf that it reaches. -/
theorem getEqR_leaf_link (N : NodeId → Option KNode) (t : Time) (r0 : NodeId) (cv : Nat)
    (hwf : ∀ x xn, ReachS N t r0 x → N x = some xn → klongsWf xn.ks = true) :
    ∀ (f : Nat) (x y : NodeId), ReachS N t r0 x → getEqR N t cv f x = some y →
      ∃ x' xn c, ReachS N t r0 x' ∧ N x' = some xn ∧ xn.leaf = true ∧ (c, y) ∈ xn.liveAt t := by
  intro f
  induction f with
  | zero => intro x y _ h; simp [getEqR] at h
  | succ f ih =>
    intro x y hx h
    simp only [getEqR] at h
    cases hn : N x with
    | none => rw [hn] at h; cases h
    | some n =>
      rw [hn] at h
      simp only at h
      split at h
      · rename_i hl
        cases hf : n.searchEq t cv with
        | none => rw [hf] at h; cases h
        | some fd =>
          rw [hf] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          exact ⟨x, n, cv, hx, hn, hl, KNode.searchEq_mem n t cv fd (hwf x n hx hn) hf⟩
      · cases hf : n.searchLte t cv with
        | none => rw [hf] at h; cases h
        | some fd =>
          rw [hf] at h
          exact ih fd.y y (ReachS.step x n fd.c fd.y hx hn (KNode.searchLte_mem n t cv fd hf)) h

/-- `getEqR_split` for the reading of keys. -/
theorem getFromR_split (Nm N2 : NodeId → Option KNode) (V : NodeId → Option Nat) (t : Time)
    (fuel : Nat) (r0 L q F S : NodeId)
    (hwf : ∀ x xn, ReachS Nm t r0 x → Nm x = some xn → klongsWf xn.ks = true)
    (hget : ∀ c (x : NodeId), ReachS Nm t r0 x → x ≠ L → x ≠ F → x ≠ S →
      getEqR N2 t c fuel x = getEqR Nm t c fuel x)
    (hsame : ∀ x, x ≠ L → x ≠ q → x ≠ F → x ≠ S → N2 x = Nm x)
    (hq : (N2 q).isSome = (Nm q).isSome)
    (hnotL : ∀ x xn c z, ReachS Nm t r0 x → x ≠ q → Nm x = some xn → (c, z) ∈ xn.liveAt t → z ≠ L)
    (hqL : ∀ xn c z, Nm q = some xn → (c, z) ∈ xn.liveAt t → xn.leaf = true → z ≠ L)
    (hnotFS : ∀ x xn c z, ReachS Nm t r0 x → Nm x = some xn → (c, z) ∈ xn.liveAt t →
      (z ≠ L → z ≠ F) ∧ z ≠ S) :
    ∀ (key : List Nat) (r : NodeId), ReachS Nm t r0 r → r ≠ L → r ≠ F → r ≠ S →
      getFromR N2 V t fuel key r = getFromR Nm V t fuel key r := by
  intro key
  induction key with
  | nil => intro r _ _ _ _; rfl
  | cons cv rest ih =>
    intro r hr hrL hrF hrS
    have he := hget cv r hr hrL hrF hrS
    cases rest with
    | nil => simp only [getFromR]; rw [he]
    | cons d rest' =>
      simp only [getFromR]
      rw [he]
      cases hg : getEqR Nm t cv fuel r with
      | none => rfl
      | some z =>
        simp only
        have hz : ReachS Nm t r0 z := getEqR_reach Nm t r0 cv hwf fuel r z hr hg
        -- z is a leaf's target: neither L, F nor S
        obtain ⟨x, xn, cz, hx, hxn, hxl, hzm⟩ : ∃ x xn cz, ReachS Nm t r0 x ∧ Nm x = some xn ∧
            xn.leaf = true ∧ (cz, z) ∈ xn.liveAt t :=
          getEqR_leaf_link Nm t r0 cv hwf fuel r z hr hg
        have hzL : z ≠ L := by
          by_cases hxq : x = q
          · subst hxq; exact hqL xn cz z hxn hzm hxl
          · exact hnotL x xn cz z hx hxq hxn hzm
        have hfs := hnotFS x xn cz z hx hxn hzm
        have hsome : (N2 z).isSome = (Nm z).isSome := by
          by_cases hzq : z = q
          · rw [hzq]; exact hq
          · rw [hsame z hzL hzq (hfs.1 hzL) hfs.2]
        rw [hsome]
        split
        · exact ih z hz hzL (hfs.1 hzL) hfs.2
        · rfl

theorem newKlongs_times (t : Time) (l : List (Nat × NodeId)) :
    ∀ s, Klong.time s ∈ newKlongs t l → s ≤ t := by
  intro s hs
  simp only [newKlongs, List.mem_cons, List.mem_map] at hs
  rcases hs with hs | ⟨q, _, hq⟩
  · cases hs; exact Nat.le_refl _
  · cases hq

theorem KNode.lastVersion_eq_newKlongs (n : KNode) (t : Time) :
    n.lastVersion t = ⟨n.leaf, newKlongs t n.live⟩ := by
  have hk := KNode.lastVersion_keys n t
  have hl : (n.lastVersion t).leaf = n.leaf := rfl
  cases hv : n.lastVersion t with
  | mk leaf ks =>
    rw [hv] at hk hl
    simp only at hk hl
    subst hl hk
    simp only [newKlongs]

end SIS.Tree
