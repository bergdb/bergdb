import SIS.Tree.GetSegRoot

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! A put of a key whose last segment has no tree yet (bergdb 024-12, TP10;
`OpGetOK`'s rules): the leaf of the segment before, with room, gets a klong to a
new segment leaf, which gets the put's klong (`setNode`'s creation). Every key
reads what it read but the put's key: a key through the new klong read nothing
before and reads nothing after, but the put's. -/

theorem getFromR_append_gen (N : NodeId → Option KNode) (V : NodeId → Option Nat) (t : Time)
    (fuel : Nat) (s : List Nat) (hs : s ≠ []) :
    ∀ (pre : List Nat) (r : NodeId), getFromR N V t fuel (pre ++ s) r =
      (segRootR N t fuel pre r).bind (fun rk => getFromR N V t fuel s rk) := by
  intro pre
  induction pre with
  | nil => intro r; rfl
  | cons c rest ih =>
    intro r
    have hne : rest ++ s ≠ [] := by simp [hs]
    obtain ⟨d, rest', he⟩ : ∃ d rest', rest ++ s = d :: rest' := by
      cases h : rest ++ s with
      | nil => exact absurd h hne
      | cons d rest' => exact ⟨d, rest', rfl⟩
    simp only [List.cons_append]
    rw [he]
    simp only [getFromR, segRootR]
    rw [← he]
    cases getEqR N t c fuel r with
    | none => rfl
    | some y =>
      simp only
      split
      · exact ih y
      · rfl

/-- The walk down a prefix is the same in two readers that agree at its visits
and on which reached nodes are key nodes. -/
theorem segRootR_frame_reach (N1 N2 : NodeId → Option KNode) (t : Time) (fuel : Nat)
    (r0 : NodeId) (hwf : ∀ x xn, ReachS N1 t r0 x → N1 x = some xn → klongsWf xn.ks = true)
    (hsome : ∀ y, ReachS N1 t r0 y → (N1 y).isSome = (N2 y).isSome) :
    ∀ (pre : List Nat) (r : NodeId), ReachS N1 t r0 r →
      (∀ q ∈ fromVisits N1 t fuel pre r, AgreeAt N1 N2 t q.1 q.2) →
      segRootR N1 t fuel pre r = segRootR N2 t fuel pre r := by
  intro pre
  induction pre with
  | nil => intro r _ _; rfl
  | cons c rest ih =>
    intro r hr h
    have hev : ∀ q ∈ eqVisits N1 t c fuel r, AgreeAt N1 N2 t q.1 q.2 := by
      intro q hq
      apply h q
      cases rest with
      | nil => exact hq
      | cons d rest' => simp only [fromVisits]; exact List.mem_append_left _ hq
    obtain ⟨he, _⟩ := getEqR_frame N1 N2 t c fuel r hev
    simp only [segRootR]
    rw [← he]
    cases hg : getEqR N1 t c fuel r with
    | none => rfl
    | some y =>
      simp only
      have hy : ReachS N1 t r0 y := getEqR_reach N1 t r0 c hwf fuel r y hr hg
      rw [← hsome y hy]
      split
      · apply ih y hy
        intro q hq
        apply h q
        cases rest with
        | nil => simp [fromVisits] at hq
        | cons d rest' =>
          simp only [fromVisits, hg]
          exact List.mem_append_right _ hq
      · rfl

/-- After the leaf cur of the key's segment before got a klong at c0 to the new
segment leaf ch, which holds the put's klong at cl to the new value v, every
key reads what it read but the key, which reads the put's value. -/
theorem getFromR_newSeg (N N2 : NodeId → Option KNode) (V V2 : NodeId → Option Nat)
    (t : Time) (fuel : Nat) (hfuel : 1 ≤ fuel) (root rk0 cur ch v : NodeId) (n cn : KNode)
    (pre : List Nat) (c0 cl h : Nat)
    (hrk : segRootR N t fuel pre root = some rk0)
    (hcurv : (cur, c0) ∈ eqVisits N t c0 fuel rk0) (hNcur : N cur = some n) (hnl : n.leaf = true)
    (hnwf : klongsWf n.ks = true) (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ t)
    (hnone : (n.searchEq t c0).map (·.y) = none)
    (hN2cur : N2 cur = some (n.add t (.key c0 ch)))
    (hN2ch : N2 ch = some cn) (hcnl : cn.leaf = true)
    (hcns : ∀ c', (cn.searchEq t c').map (·.y) = if cl == c' then some v else none)
    (hN2 : ∀ x, x ≠ cur → x ≠ ch → N2 x = N x) (hN2v : N2 v = none)
    (hV2v : V2 v = some h) (hV2 : ∀ a, a ≠ v → V2 a = V a) (hV2ch : V2 ch = none)
    (hcurch : cur ≠ ch) (hrootch : root ≠ ch)
    (hwf : ∀ x xn, ReachS N t root x → N x = some xn → klongsWf xn.ks = true)
    (hfr : ∀ x xn c z, ReachS N t root x → N x = some xn → (c, z) ∈ xn.liveAt t →
      z ≠ ch ∧ z ≠ v)
    (huniq : ∀ key', keyWf key' = true → (cur, c0) ∈ fromVisits N t fuel key' root →
      ∃ rest', key' = pre ++ c0 :: rest')
    (hpre : ∀ c', (cur, c') ∉ fromVisits N t fuel pre root) :
    ∀ key', keyWf key' = true → getFromR N2 V2 t fuel key' root =
      if pre ++ [c0, cl] == key' then some h else getFromR N V t fuel key' root := by
  -- nodes reached are not the new leaf
  have hreach_ne : ∀ x, ReachS N t root x → x ≠ ch := by
    intro x hx
    cases hx with
    | root => exact hrootch
    | step x' n' c _ hx' hn' hz => exact (hfr x' n' c _ hx' hn' hz).1
  have hagree : ∀ x c, ReachS N t root x → (x = cur → c ≠ c0) → AgreeAt N N2 t x c := by
    intro x c hx hc
    by_cases hxc : x = cur
    · subst hxc
      right
      refine ⟨n, n.add t (.key c0 ch), hNcur, hN2cur, hnl, by rw [KNode.add_leaf]; exact hnl, ?_⟩
      rw [KNode.add_key_searchEq n t c0 ch hnwf hnt c]
      have : (c0 == c) = false := by
        cases hb : (c0 == c) with
        | false => rfl
        | true => exact absurd (beq_iff_eq.mp hb).symm (hc rfl)
      rw [this]; rfl
    · left; exact (hN2 x hxc (hreach_ne x hx)).symm
  have hsome : ∀ y, ReachS N t root y → (N y).isSome = (N2 y).isSome := by
    intro y hy
    by_cases hyc : y = cur
    · rw [hyc, hNcur, hN2cur]; rfl
    · rw [hN2 y hyc (hreach_ne y hy)]
  have hrrk : ReachS N t root rk0 := segRootR_reach N t fuel root hwf pre root rk0 ReachS.root hrk
  have hkeyv : (cur, c0) ∈ fromVisits N t fuel (pre ++ [c0, cl]) root :=
    fromVisits_append_gen N t fuel c0 [cl] pre root rk0 hrk _ hcurv
  intro key' hkey'
  by_cases hv : (cur, c0) ∈ fromVisits N t fuel key' root
  · obtain ⟨rest', hk⟩ := huniq key' hkey' hv
    subst hk
    have hs : c0 :: rest' ≠ [] := by simp
    rw [getFromR_append_gen N2 V2 t fuel _ hs, getFromR_append_gen N V t fuel _ hs, hrk]
    rw [← segRootR_frame_reach N N2 t fuel root hwf hsome pre root ReachS.root (by
      intro q hq
      exact hagree q.1 q.2 (fromVisits_reach N t fuel root hwf pre root q.1 q.2 ReachS.root hq)
        (fun he => absurd (he ▸ hq) (hpre q.2))), hrk]
    simp only [Option.bind_some]
    -- the descents of c0 from rk0: none before, the new leaf after
    have hg1 : getEqR N t c0 fuel rk0 = none := by
      rw [getEqR_change_leaf N N t c0 cur n hNcur hnl fuel rk0 (fun _ _ _ => rfl) hcurv
        (fun n1 h1 => by rw [hNcur] at h1; cases h1; exact hnl)]
      exact hnone
    have hg2 : getEqR N2 t c0 fuel rk0 = some ch := by
      rw [getEqR_change_leaf N N2 t c0 cur _ hN2cur (by rw [KNode.add_leaf]; exact hnl) fuel rk0
        (fun q hq hqc => (hN2 q.1 hqc (hreach_ne q.1
          (eqVisits_reach N t root c0 fuel rk0 q.1 q.2 hrrk hq))).symm) hcurv
        (fun n1 h1 => by rw [hNcur] at h1; cases h1; exact hnl)]
      rw [KNode.add_key_searchEq n t c0 ch hnwf hnt c0]
      simp
    have hN : getFromR N V t fuel (c0 :: rest') rk0 = none := by
      cases rest' with
      | nil => simp only [getFromR, hg1]; rfl
      | cons d more => simp only [getFromR, hg1]
    rw [hN]
    cases rest' with
    | nil =>
      simp only [getFromR, hg2, Option.bind_some, hV2ch]
      have : (pre ++ [c0, cl] == pre ++ [c0]) = false := by simp
      simp [this]
    | cons d more =>
      simp only [getFromR, hg2, hN2ch, Option.isSome_some, ↓reduceIte]
      obtain ⟨f2, hf2⟩ : ∃ f2, fuel = f2 + 1 := ⟨fuel - 1, by omega⟩
      have hgd : getEqR N2 t d fuel ch = if cl == d then some v else none := by
        rw [hf2]; simp only [getEqR, hN2ch, hcnl, ↓reduceIte]; exact hcns d
      cases more with
      | nil =>
        simp only [getFromR, hgd]
        by_cases hd : cl = d
        · subst hd; simp [hV2v]
        · have hb : (cl == d) = false := by simpa using hd
          have hne : (pre ++ [c0, cl] == pre ++ [c0, d]) = false := by simp [hd]
          simp [hb, hne]
      | cons e more' =>
        simp only [getFromR, hgd]
        have hne : (pre ++ [c0, cl] == pre ++ c0 :: d :: e :: more') = false := by simp
        by_cases hd : cl = d
        · subst hd; simp [hN2v, hne]
        · have hb : (cl == d) = false := by simpa using hd
          simp [hb, hne]
  · have hne : (pre ++ [c0, cl] == key') = false := by
      cases hb : (pre ++ [c0, cl] == key') with
      | false => rfl
      | true => rw [beq_iff_eq.mp hb] at hkeyv; exact absurd hkeyv hv
    rw [hne]
    simp only [Bool.false_eq_true, ↓reduceIte]
    symm
    apply getFromR_frame N N2 V V2 t fuel hfuel key' root
    · intro q hq
      exact hagree q.1 q.2 (fromVisits_reach N t fuel root hwf key' root q.1 q.2 ReachS.root hq)
        (fun he hc => hv (by rw [← he, ← hc]; exact hq))
    · intro x c m y hx hm _ hs
      have hrx := fromVisits_reach N t fuel root hwf key' root x c ReachS.root hx
      cases hfd : m.searchEq t c with
      | none => rw [hfd] at hs; cases hs
      | some fd =>
        rw [hfd] at hs
        simp only [Option.map_some, Option.some.injEq] at hs
        subst hs
        exact (hV2 fd.y (hfr x m c fd.y hrx hm (KNode.searchEq_mem m t c fd (hwf x m hrx hm) hfd)).2).symm

end SIS.Tree
