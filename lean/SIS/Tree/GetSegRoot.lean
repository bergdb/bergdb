import SIS.Tree.GetPutInv

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! A put into the root of a key's last segment when it is a full leaf below a
segment leaf q (bergdb 024-12, TP10; `OpGetOK`'s rules): the split replaces the
segment's tree by one from a new root R, and q's klong k1 to the old root L
names R. Reading through q: what the new tree reads from R for the rest of a
key is what L's tree with the put read (`getFromR_graft`). -/

/-! ## A link moved to a new tree -/

/-- Reader N2 is reader N1 but q's klong k1 to L names R (q a leaf in both)
and the nodes of D: the descents from the nodes outside D that N1 reaches find
what N1's find, L renamed R. -/
theorem getEqR_graft (N1 N2 : NodeId → Option KNode) (t : Time) (r0 q L R : NodeId)
    (D : NodeId → Prop) (qn1 qn2 : KNode)
    (hq1 : N1 q = some qn1) (hq2 : N2 q = some qn2) (hql1 : qn1.leaf = true) (hql2 : qn2.leaf = true)
    (hqs : ∀ c, (qn2.searchEq t c).map (·.y) =
      ((qn1.searchEq t c).map (·.y)).map (fun z => if z = L then R else z))
    (hLD : D L) (hwf : ∀ x xn, ReachS N1 t r0 x → N1 x = some xn → klongsWf xn.ks = true)
    (hsame : ∀ x, ReachS N1 t r0 x → ¬ D x → x ≠ q → N2 x = N1 x)
    (hlinks : ∀ x xn c z, ReachS N1 t r0 x → ¬ D x → x ≠ q → N1 x = some xn →
      (c, z) ∈ xn.liveAt t → ¬ D z)
    (c : Nat) :
    ∀ (f : Nat) (x : NodeId), ReachS N1 t r0 x → ¬ D x →
      getEqR N2 t c f x = (getEqR N1 t c f x).map (fun z => if z = L then R else z) := by
  intro f
  induction f with
  | zero => intro x _ _; rfl
  | succ f ih =>
    intro x hx hD
    by_cases hxq : x = q
    · subst hxq
      simp only [getEqR, hq1, hq2, hql1, hql2, ↓reduceIte]
      exact hqs c
    · simp only [getEqR, hsame x hx hD hxq]
      cases hn : N1 x with
      | none => rfl
      | some xn =>
        simp only
        by_cases hl : xn.leaf = true
        · simp only [hl, ↓reduceIte]
          cases hs : xn.searchEq t c with
          | none => rfl
          | some fd =>
            simp only [Option.map_some, Option.some.injEq]
            have hm : (c, fd.y) ∈ xn.liveAt t := KNode.searchEq_mem xn t c fd (hwf x xn hx hn) hs
            have hzL : fd.y ≠ L := fun he => hlinks x xn c fd.y hx hD hxq hn hm (he ▸ hLD)
            simp [hzL]
        · simp only [hl, Bool.false_eq_true, ↓reduceIte]
          cases hs : xn.searchLte t c with
          | none => rfl
          | some fd =>
            simp only
            have hmem := KNode.searchLte_mem xn t c fd hs
            exact ih fd.y (ReachS.step x xn fd.c fd.y hx hn hmem) (hlinks x xn fd.c fd.y hx hD hxq hn hmem)

/-- What a descent from a node outside D finds is L or outside D. -/
theorem getEqR_res_notD (N1 : NodeId → Option KNode) (t : Time) (r0 q L : NodeId)
    (D : NodeId → Prop) (qn1 : KNode) (hq1 : N1 q = some qn1) (hql1 : qn1.leaf = true)
    (hwf : ∀ x xn, ReachS N1 t r0 x → N1 x = some xn → klongsWf xn.ks = true)
    (hlinks : ∀ x xn c z, ReachS N1 t r0 x → ¬ D x → x ≠ q → N1 x = some xn →
      (c, z) ∈ xn.liveAt t → ¬ D z)
    (hqlinks : ∀ c z, (c, z) ∈ qn1.liveAt t → D z → z = L) (c : Nat) :
    ∀ (f : Nat) (x z : NodeId), ReachS N1 t r0 x → ¬ D x → getEqR N1 t c f x = some z →
      z = L ∨ ¬ D z := by
  intro f
  induction f with
  | zero => intro x z _ _ h; simp [getEqR] at h
  | succ f ih =>
    intro x z hx hD h
    simp only [getEqR] at h
    cases hn : N1 x with
    | none => rw [hn] at h; cases h
    | some xn =>
      rw [hn] at h
      simp only at h
      by_cases hl : xn.leaf = true
      · simp only [hl, ↓reduceIte] at h
        cases hs : xn.searchEq t c with
        | none => rw [hs] at h; cases h
        | some fd =>
          rw [hs] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          have hm := KNode.searchEq_mem xn t c fd (hwf x xn hx hn) hs
          by_cases hxq : x = q
          · subst hxq
            rw [hq1] at hn; cases hn
            by_cases hz : D fd.y
            · exact Or.inl (hqlinks c fd.y hm hz)
            · exact Or.inr hz
          · exact Or.inr (hlinks x xn c fd.y hx hD hxq hn hm)
      · simp only [hl, Bool.false_eq_true, ↓reduceIte] at h
        cases hs : xn.searchLte t c with
        | none => rw [hs] at h; cases h
        | some fd =>
          rw [hs] at h
          have hmem := KNode.searchLte_mem xn t c fd hs
          have hxq : x ≠ q := by
            intro he; subst he; rw [hq1] at hn; cases hn; exact hl hql1
          exact ih fd.y z (ReachS.step x xn fd.c fd.y hx hn hmem)
            (hlinks x xn fd.c fd.y hx hD hxq hn hmem) h

/-- The reading from the nodes outside D that N1 reaches is N2's, when the tree
from R reads in N2 as the tree from L in N1. -/
theorem getFromR_graft (N1 N2 : NodeId → Option KNode) (V : NodeId → Option Nat) (t : Time)
    (fuel : Nat) (r0 q L R : NodeId) (D : NodeId → Prop) (qn1 qn2 : KNode)
    (hq1 : N1 q = some qn1) (hq2 : N2 q = some qn2) (hql1 : qn1.leaf = true) (hql2 : qn2.leaf = true)
    (hqs : ∀ c, (qn2.searchEq t c).map (·.y) =
      ((qn1.searchEq t c).map (·.y)).map (fun z => if z = L then R else z))
    (hLD : D L)
    (hwf : ∀ x xn, ReachS N1 t r0 x → N1 x = some xn → klongsWf xn.ks = true)
    (hsame : ∀ x, ReachS N1 t r0 x → ¬ D x → x ≠ q → N2 x = N1 x)
    (hlinks : ∀ x xn c z, ReachS N1 t r0 x → ¬ D x → x ≠ q → N1 x = some xn →
      (c, z) ∈ xn.liveAt t → ¬ D z)
    (hqlinks : ∀ c z, (c, z) ∈ qn1.liveAt t → D z → z = L)
    (hsub : ∀ key, key ≠ [] → getFromR N2 V t fuel key R = getFromR N1 V t fuel key L)
    (hRL : (N2 R).isSome = (N1 L).isSome) (hVL : V R = V L) :
    ∀ (key : List Nat) (x : NodeId), ReachS N1 t r0 x → ¬ D x →
      getFromR N2 V t fuel key x = getFromR N1 V t fuel key x := by
  intro key
  induction key with
  | nil => intro x _ _; rfl
  | cons c rest ih =>
    intro x hx hD
    have he := getEqR_graft N1 N2 t r0 q L R D qn1 qn2 hq1 hq2 hql1 hql2 hqs hLD hwf hsame hlinks
      c fuel x hx hD
    cases rest with
    | nil =>
      simp only [getFromR]
      rw [he]
      cases hg : getEqR N1 t c fuel x with
      | none => rfl
      | some z =>
        simp only [Option.map_some, Option.bind_some]
        by_cases hz : z = L
        · simp [hz, hVL]
        · simp [hz]
    | cons d rest' =>
      simp only [getFromR]
      rw [he]
      cases hg : getEqR N1 t c fuel x with
      | none => rfl
      | some z =>
        simp only [Option.map_some]
        by_cases hz : z = L
        · simp only [hz, ↓reduceIte]
          rw [hRL]
          split
          · exact hsub (d :: rest') (by simp)
          · rfl
        · simp only [hz, ↓reduceIte]
          have hzr : ReachS N1 t r0 z := getEqR_reach N1 t r0 c hwf fuel x z hx hg
          have hzD : ¬ D z := by
            rcases getEqR_res_notD N1 t r0 q L D qn1 hq1 hql1 hwf hlinks hqlinks c fuel x z hx hD hg with
              h | h
            · exact absurd h hz
            · exact h
          have hsome : (N2 z).isSome = (N1 z).isSome := by
            by_cases hzq : z = q
            · rw [hzq, hq1, hq2]; rfl
            · rw [hsame z hzr hzD hzq]
          rw [hsome]
          split
          · exact ih z hzr hzD
          · rfl

/-- A tree from a new root R reads in N2 as the tree from L in Nm, if their
first descents find alike and they agree below on what Nm reaches from L
outside D. -/
theorem getFromR_newRoot_sim (Nm N2 : NodeId → Option KNode) (V : NodeId → Option Nat)
    (t : Time) (fuel : Nat) (L R : NodeId) (D : NodeId → Prop)
    (hfirst : ∀ c, getEqR N2 t c fuel R = getEqR Nm t c fuel L)
    (hwf : ∀ x xn, ReachS Nm t L x → Nm x = some xn → klongsWf xn.ks = true)
    (hsame : ∀ x, ReachS Nm t L x → ¬ D x → N2 x = Nm x)
    (hlinks : ∀ x xn c z, ReachS Nm t L x → Nm x = some xn → (c, z) ∈ xn.liveAt t → ¬ D z) :
    ∀ key, getFromR N2 V t fuel key R = getFromR Nm V t fuel key L := by
  intro key
  cases key with
  | nil => rfl
  | cons c rest =>
    cases rest with
    | nil => simp only [getFromR]; rw [hfirst c]
    | cons d rest' =>
      simp only [getFromR]
      rw [hfirst c]
      cases hg : getEqR Nm t c fuel L with
      | none => rfl
      | some z =>
        simp only
        have hz : ReachS Nm t L z := getEqR_reach Nm t L c hwf fuel L z ReachS.root hg
        obtain ⟨x, xn, cz, hx, hxn, _, hzm⟩ := getEqR_leaf_link Nm t L c hwf fuel L z ReachS.root hg
        have hzD := hlinks x xn cz z hx hxn hzm
        rw [hsame z hz hzD]
        split
        · exact getFromR_avoid Nm N2 V t fuel L D hwf hsame hlinks _ z hz hzD
        · rfl

theorem reachS_trans (N : NodeId → Option KNode) (t : Time) (r a : NodeId) (ha : ReachS N t r a) :
    ∀ b, ReachS N t a b → ReachS N t r b := by
  intro b hb
  induction hb with
  | root => exact ha
  | step x n c z _ hn hz ih => exact ReachS.step x n c z ih hn hz

/-- After a time split of the root L of a key's last segment, a leaf below the
segment leaf q (q's klong k1 names the new root Y, which holds L's last version
with the put's klong to the new value v), every key reads what it read but the
key, which reads the put's value. -/
theorem getFromR_segTimeSplit (N N2 : NodeId → Option KNode) (V V2 : NodeId → Option Nat)
    (i : Time) (fuel : Nat) (hfuel : 1 ≤ fuel) (root q L Y v : NodeId) (n qn ln : KNode)
    (k1 : Nat) (pre : List Nat) (cv h : Nat)
    (hNL : N L = some n) (hnl : n.leaf = true) (hnwf : klongsWf n.ks = true)
    (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ i)
    (hNq : N q = some qn) (hql : qn.leaf = true) (hqwf : klongsWf qn.ks = true)
    (hqt : ∀ s, Klong.time s ∈ qn.ks → s ≤ i) (hk1 : (k1, L) ∈ qn.live)
    (hN2q : N2 q = some (qn.add i (.key k1 Y)))
    (hN2Y : N2 Y = some ln) (hlnl : ln.leaf = true) (hlnwf : klongsWf ln.ks = true)
    (hlnt : ∀ s, Klong.time s ∈ ln.ks → s ≤ i)
    (hlnlook : ∀ q', ln.live.lookup q' = if cv == q' then some v else n.live.lookup q')
    (hN2 : ∀ x, x ≠ L → x ≠ q → x ≠ Y → N2 x = N x)
    (hV2v : V2 v = some h) (hV2 : ∀ a, a ≠ v → V2 a = V a) (hV2L : V2 L = none)
    (hV2Y : V2 Y = none)
    (hqL : q ≠ L) (hYq : Y ≠ q) (hYL : Y ≠ L) (hvL : v ≠ L) (hvY : v ≠ Y) (hvq : v ≠ q)
    (hNv : N v = none)
    (hrootL : root ≠ L) (hrootY : root ≠ Y) (hrq : ReachS N i root q)
    (hrk : segRootR N i fuel pre root = some L) (hcv : cv ∉ pre)
    (huniq : ∀ key' x m', keyWf key' = true → (x, cv) ∈ fromVisits N i fuel key' root →
      (x, cv) ∈ eqVisits N i cv fuel L → N x = some m' → m'.leaf = true → key' = pre ++ [cv])
    (hwf : ∀ x xn, ReachS N i root x → N x = some xn → klongsWf xn.ks = true)
    (honlyL : ∀ x xn c, ReachS N i root x → N x = some xn → (c, L) ∈ xn.liveAt i →
      x = q ∧ c = k1)
    (hnotq : ∀ x, ReachS N i L x → x ≠ q)
    (hfr : ∀ x xn c z, ReachS N i root x → N x = some xn → (c, z) ∈ xn.liveAt i →
      z ≠ v ∧ z ≠ Y) :
    ∀ key', keyWf key' = true → getFromR N2 V2 i fuel key' root =
      if pre ++ [cv] == key' then some h else getFromR N V i fuel key' root := by
  let m := n.add i (.key cv v)
  have hml : m.leaf = true := by simp only [m, KNode.add_leaf]; exact hnl
  have hmwf : klongsWf m.ks = true := KNode.add_key_wf n i cv v hnwf
  have hmt : ∀ s, Klong.time s ∈ m.ks → s ≤ i := KNode.add_times n i (.key cv v) (fun s h => by cases h) hnt
  have hmlook : ∀ c, m.live.lookup c = if cv == c then some v else n.live.lookup c :=
    fun c => KNode.add_key_live_lookup_of_wf n i cv c v hnwf
  let Nm : NodeId → Option KNode := fun x => if x = L then some m else N x
  have hNmL : Nm L = some m := by simp [Nm]
  have hNm : ∀ x, x ≠ L → Nm x = N x := fun x hx => by simp [Nm, hx]
  have hNmq : Nm q = some qn := by rw [hNm q hqL, hNq]
  have hL1 := KNode.liveAt_of_times n i hnt
  have hLm := KNode.liveAt_of_times m i hmt
  have hmem : ∀ c z, (c, z) ∈ m.liveAt i → (c, z) ∈ n.liveAt i ∨ z = v := by
    intro c z hz
    rw [hLm] at hz
    have := lookup_some_of_mem (KNode.live_keys_nodup m) hz
    rw [hmlook] at this
    by_cases hc : cv = c
    · subst hc
      rw [beq_self_eq_true] at this
      simp only [↓reduceIte, Option.some.injEq] at this
      exact Or.inr this.symm
    · have hc' : (cv == c) = false := by simpa using hc
      rw [hc'] at this
      simp only [Bool.false_eq_true, ↓reduceIte] at this
      left; rw [hL1]; exact lookup_some_mem this
  have hrL : ReachS N i root L := ReachS.step q qn k1 L hrq hNq (by
    rw [KNode.liveAt_of_times qn i hqt]; exact hk1)
  have hreach := reach_change N i root L v n m hNL hmem hNv hvL
  have hreachL := reach_change N i L L v n m hNL hmem hNv hvL
  have hwfm : ∀ x xn, ReachS Nm i root x → Nm x = some xn → klongsWf xn.ks = true := by
    intro x xn hx hn
    by_cases hxL : x = L
    · subst hxL; rw [hNmL] at hn; cases hn; exact hmwf
    · rw [hNm x hxL] at hn
      rcases hreach x hx with hx' | hxv
      · exact hwf x xn hx' hn
      · subst hxv; rw [hNv] at hn; cases hn
  -- the reading from root through Nm: the leaf with the put
  have hs : ∀ c', c' ≠ cv → (n.searchEq i c').map (·.y) = (m.searchEq i c').map (·.y) := by
    intro c' hc'
    rw [KNode.searchEq_live n i hnwf hnt, KNode.searchEq_live m i hmwf hmt, hmlook]
    have : (cv == c') = false := by
      cases hb : (cv == c') with
      | false => rfl
      | true => exact absurd (beq_iff_eq.mp hb).symm hc'
    rw [this]; rfl
  have hvisL : (L, cv) ∈ eqVisits N i cv fuel L := by
    obtain ⟨f2, hf2⟩ : ∃ f2, fuel = f2 + 1 := ⟨fuel - 1, by omega⟩
    rw [hf2]; simp [eqVisits]
  have hA := getFromR_leaf_change_seg N Nm V V2 i fuel hfuel L pre cv root L n m
    (fun x hx => (hNm x hx).symm) hNL hNmL hnl hml hs hrk hcv hvisL huniq
    (fun key' x c' m' y' _ hx hm' hml' hs' => by
      have hrx : ReachS N i root x := fromVisits_reach N i fuel root hwf key' root x c' ReachS.root hx
      have hy' : y' ≠ v := by
        cases hfd : m'.searchEq i c' with
        | none => rw [hfd] at hs'; cases hs'
        | some fd =>
          rw [hfd] at hs'
          simp only [Option.map_some, Option.some.injEq] at hs'
          subst hs'
          exact (hfr x m' c' fd.y hrx hm' (KNode.searchEq_mem m' i c' fd (hwf x m' hrx hm') hfd)).1
      exact (hV2 y' hy').symm)
  -- the tree from Y reads in N2 as the tree from L in Nm
  let D' : NodeId → Prop := fun z => z = L ∨ z = Y ∨ z = q
  have hlinksL : ∀ x xn c z, ReachS Nm i L x → Nm x = some xn → (c, z) ∈ xn.liveAt i → ¬ D' z := by
    intro x xn c z hx hn hz
    -- x is reached from L in N (or is v, no key node)
    have hxN : ReachS N i L x ∨ x = v := hreachL x hx
    have hlink : ∀ x' xn', ReachS N i L x' → N x' = some xn' → (c, z) ∈ xn'.liveAt i → ¬ D' z := by
      intro x' xn' hx' hn' hz' hD
      have hx'r : ReachS N i root x' := reachS_trans N i root L hrL x' hx'
      rcases hD with h1 | h1 | h1
      · subst h1
        exact hnotq x' hx' (honlyL x' xn' c hx'r hn' hz').1
      · exact (hfr x' xn' c z hx'r hn' hz').2 h1
      · subst h1
        exact hnotq z (ReachS.step x' xn' c z hx' hn' hz') rfl
    by_cases hxL : x = L
    · subst hxL; rw [hNmL] at hn; cases hn
      rcases hmem c z hz with h1 | h1
      · exact hlink x n ReachS.root hNL h1
      · subst h1
        rintro (h | h | h)
        · exact hvL h
        · exact hvY h
        · exact hvq h
    · rw [hNm x hxL] at hn
      rcases hxN with hx' | hxv
      · exact hlink x xn hx' hn hz
      · subst hxv; rw [hNv] at hn; cases hn
  have hwfL : ∀ x xn, ReachS Nm i L x → Nm x = some xn → klongsWf xn.ks = true := by
    intro x xn hx hn
    by_cases hxL : x = L
    · subst hxL; rw [hNmL] at hn; cases hn; exact hmwf
    · rw [hNm x hxL] at hn
      rcases hreachL x hx with hx' | hxv
      · exact hwf x xn (reachS_trans N i root L hrL x hx') hn
      · subst hxv; rw [hNv] at hn; cases hn
  have hfirst : ∀ c, getEqR N2 i c fuel Y = getEqR Nm i c fuel L := by
    intro c
    obtain ⟨f2, hf2⟩ : ∃ f2, fuel = f2 + 1 := ⟨fuel - 1, by omega⟩
    rw [hf2]
    simp only [getEqR, hN2Y, hNmL, hml, hlnl, ↓reduceIte]
    rw [KNode.searchEq_live ln i hlnwf hlnt, KNode.searchEq_live m i hmwf hmt, hlnlook, hmlook]
  have hsameL : ∀ x, ReachS Nm i L x → ¬ D' x → N2 x = Nm x := by
    intro x _ hD
    have h1 : x ≠ L := fun h => hD (Or.inl h)
    have h2 : x ≠ Y := fun h => hD (Or.inr (Or.inl h))
    have h3 : x ≠ q := fun h => hD (Or.inr (Or.inr h))
    rw [hN2 x h1 h3 h2, hNm x h1]
  have hsub := getFromR_newRoot_sim Nm N2 V2 i fuel L Y D' hfirst hwfL hsameL hlinksL
  -- the graft at q
  let D : NodeId → Prop := fun z => z = L ∨ z = Y
  have hqs : ∀ c, ((qn.add i (.key k1 Y)).searchEq i c).map (·.y) =
      ((qn.searchEq i c).map (·.y)).map (fun z => if z = L then Y else z) := by
    intro c
    rw [KNode.add_key_searchEq qn i k1 Y hqwf hqt c]
    have hqL1 := KNode.liveAt_of_times qn i hqt
    by_cases hc : k1 = c
    · subst hc
      have : (qn.searchEq i k1).map (·.y) = some L := by
        rw [KNode.searchEq_live qn i hqwf hqt]
        exact lookup_some_of_mem (KNode.live_keys_nodup qn) hk1
      rw [this]; simp
    · have hc' : (k1 == c) = false := by simpa using hc
      simp only [hc', Bool.false_eq_true, ↓reduceIte]
      cases hfd : qn.searchEq i c with
      | none => rfl
      | some fd =>
        simp only [Option.map_some, Option.some.injEq]
        have hm := KNode.searchEq_mem qn i c fd hqwf hfd
        have hyL : fd.y ≠ L := by
          intro he
          rw [he] at hm
          exact hc (honlyL q qn c hrq hNq hm).2.symm
        simp [hyL]
  have hgr := getFromR_graft Nm N2 V2 i fuel root q L Y D qn (qn.add i (.key k1 Y)) hNmq hN2q hql
    (by rw [KNode.add_leaf]; exact hql) hqs (Or.inl rfl) hwfm
    (by
      intro x _ hD hxq
      have h1 : x ≠ L := fun h => hD (Or.inl h)
      have h2 : x ≠ Y := fun h => hD (Or.inr h)
      rw [hN2 x h1 hxq h2, hNm x h1])
    (by
      intro x xn c z hx hD hxq hn hz hDz
      have hxL : x ≠ L := fun h => hD (Or.inl h)
      rw [hNm x hxL] at hn
      rcases hreach x hx with hx' | hxv
      · rcases hDz with h1 | h1
        · subst h1; exact hxq (honlyL x xn c hx' hn hz).1
        · exact (hfr x xn c z hx' hn hz).2 h1
      · subst hxv; rw [hNv] at hn; cases hn)
    (by
      intro c z hz hDz
      rcases hDz with h1 | h1
      · exact h1
      · exact absurd h1 (hfr q qn c z hrq hNq hz).2)
    (fun key _ => hsub key) (by rw [hN2Y, hNmL]; rfl) (by rw [hV2Y, hV2L])
  intro key' hkey'
  rw [hgr key' root ReachS.root (by rintro (h | h); exact hrootL h; exact hrootY h)]
  by_cases hk : pre ++ [cv] = key'
  · subst hk
    simp only [beq_self_eq_true, ↓reduceIte]
    rw [hA.1, KNode.searchEq_live m i hmwf hmt, hmlook]
    simp [hV2v]
  · have hk' : (pre ++ [cv] == key') = false := by simpa using hk
    simp only [hk', Bool.false_eq_true, ↓reduceIte]
    exact hA.2 key' hkey' (fun h' => hk h'.symm)

/-! ## The writer: the walk down a key's prefix to any suffix -/

/-- `writerWP_putSegs_prefix_src` to any nonempty suffix of segments. -/
theorem writerWP_putSegs_walk_src (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (key : Key) (value : Option Nat) (sfx : List Nat) (hsfx : sfx ≠ []) (post : Bool → W → Prop) :
    ∀ (pre : List Nat) (r rk : NodeId) (w : W),
      (∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ sfx) r,
        w.taken.contains q.1 = false) →
      segRootR (wNode c.p base w) c.i c.p.fuel pre r = some rk →
      w.path.getLast?.map (·.2) = some r →
      (∀ w', ReadsAs c.p base w w' → w'.path.getLast?.map (·.2) = some rk →
        (∀ z, (w'.nodes.lookup z).isSome = true →
          (w.nodes.lookup z).isSome = true ∨ (c.view z).isSome = true) →
        WriterWP (putSegs key value sfx rk) c w' post) →
      WriterWP (putSegs key value (pre ++ sfx) r) c w post := by
  intro pre
  induction pre with
  | nil =>
    intro r rk w _ hrk hp hcont
    simp only [segRootR, Option.some.injEq] at hrk
    subst hrk
    rw [List.nil_append]
    exact hcont w (ReadsAs.refl _ _ _) hp (fun z hz => Or.inl hz)
  | cons s rest ih =>
    intro r rk w ht hrk hp hcont
    have hne : rest ++ sfx ≠ [] := by simp [hsfx]
    rw [List.cons_append, putSegs.eq_3 key value r s (rest ++ sfx) hne]
    simp only [segRootR] at hrk
    cases hg : getEqR (wNode c.p base w) c.i s c.p.fuel r with
    | none => rw [hg] at hrk; cases hrk
    | some y =>
      rw [hg] at hrk
      simp only at hrk
      split at hrk
      · rename_i hysome
        obtain ⟨d, rest', he⟩ : ∃ d rest', rest ++ sfx = d :: rest' := by
          cases h' : rest ++ sfx with
          | nil => exact absurd h' hne
          | cons d rest' => exact ⟨d, rest', rfl⟩
        have hvis : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (s :: d :: rest') r,
            w.taken.contains q.1 = false := by
          intro q hq; apply ht q; rw [List.cons_append, he]; exact hq
        simp only [fromVisits] at hvis
        have ht1 : ∀ q ∈ eqVisits (wNode c.p base w) c.i s c.p.fuel r,
            w.taken.contains q.1 = false := fun q hq => hvis q (List.mem_append_left _ hq)
        unfold setNode
        wpSimplify
        refine writerWP_mono (writerWP_and (writerWP_descendLte_reads s c base hvc c.p.fuel r w ht1)
          (writerWP_descendLte_cache s c base hvc c.p.fuel r w ht1)) ?_
        intro L w3 ⟨⟨hr3, n, hn, hnl, hlk3, _, hget⟩, ⟨_, hsrc3, _⟩⟩
        rw [writerWP_getNode_known L n c _ hlk3]
        rw [hg] at hget
        cases hfd : n.searchEq c.i s with
        | none => rw [hfd] at hget; cases hget
        | some fd =>
          rw [hfd] at hget
          simp only [Option.map_some, Option.some.injEq] at hget
          simp only [pathAdd, writerWP_bind, writerWP_modify, writerWP_pure]
          rw [← hget]
          generalize hw4 : ({ w3 with path := w3.path ++ [(some fd.c, y)] } : W) = w4
          have hr04 : ReadsAs c.p base w w4 := by
            subst hw4
            exact ReadsAs.trans _ _ _ _ _ hr3 ⟨rfl, rfl, rfl, rfl, rfl⟩
          refine ih y rk w4 ?_ ?_ (by subst hw4; simp) ?_
          · intro q hq
            rw [hr04.2.2.1]
            rw [hr04.1] at hq
            apply hvis q
            apply List.mem_append_right
            rw [hg]
            simp only
            rw [← he]
            exact hq
          · rw [hr04.1]; exact hrk
          · intro w' hr' hp' hsrc'
            refine hcont w' (ReadsAs.trans _ _ _ _ _ hr04 hr') hp' (fun z hz => ?_)
            rcases hsrc' z hz with h1 | h1
            · subst hw4
              exact hsrc3 z h1
            · exact Or.inr h1
      · cases hrk

/-! ## The writer: a time split below a segment leaf -/

set_option linter.unusedSimpArgs false in
theorem writerWP_handleFullWith_timeSplitLeafParent (d' : Nat) (L q : NodeId) (n qn : KNode)
    (k1 cv v : Nat) (compact : Bool) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hlq : w.nodes.lookup q = some qn)
    (hqL : q ≠ L) (hql : qn.leaf = true) (hfirst : n.firstTime ≠ some c.i)
    (hcs : (!compact && decide ((n.lastVersion c.i).size > c.p.splitAbove)) = false)
    (hpq : (w.path[d']?).map (·.2) = some q) (hpk : w.path[d' + 1]? = some (some k1, L))
    (hroomq : qn.size + 1 + 1 ≤ c.p.M) (hdeadq : ∀ y, deadOver c.p (qn.add c.i (.key k1 y)) = false)
    (hny : w.nodes.lookup w.next = none) :
    WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) L [(cv, v)]
      (n.lastVersion c.i) compact) c w
      (fun _ w' => TimeSplitAfter c w w' L q n qn k1 cv v) := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w hlk]
  refine writerWP_ghOf_cached L n c w hlk _ (fun gh => ?_)
  have hnew : (n.firstTime == some c.i) = false := by simpa using hfirst
  simp only [hnew]
  unfold parentAt pathNode
  simp only [writerWP_bind, writerWP_get]
  cases hp : w.path[d']? with
  | none => rw [hp] at hpq; cases hpq
  | some e =>
    rw [hp] at hpq
    simp only [Option.map_some, Option.some.injEq] at hpq
    simp only [writerWP_pure]
    rw [hpq]
    simp only [writerWP_bind]
    rw [writerWP_getNode_known q qn c w hlq]
    simp only [writerWP_pure, hql, hcs, Bool.false_eq_true, ↓reduceIte]
    have hfinal : ∀ (l : KNode), l.leaf = n.leaf → klongsWf l.ks = true →
        (∀ s, Klong.time s ∈ l.ks → s ≤ c.i) →
        (∀ q', l.live.lookup q' = [(cv, v)].foldl (pairLookupStep q') (n.live.lookup q')) →
        ∀ w2 : W, w2.taken = w.taken → w2.top = w.top → w2.vals = w.vals →
        w2.nodes = upsert (w.nodes ++ [(w.next, { leaf := n.leaf, ks := l.ks })]) q
          (qn.add c.i (.key k1 w.next)) →
        WriterWP (do let n ← getNode L; putNode L (n.toPrev (c.i - 1))) c w2
          (fun _ w' => TimeSplitAfter c w w' L q n qn k1 cv v) := by
      intro l hl_leaf hl_wf hl_times hl_look w2 h2t h2top h2v h2n
      have hlk2 : w2.nodes.lookup L = some n := by
        rw [h2n, lookup_upsert]
        simp only [show L ≠ q from fun h => hqL h.symm, ↓reduceIte, List.lookup_append, hlk]
        rfl
      simp only [writerWP_bind]
      rw [writerWP_getNode_known L n c w2 hlk2]
      simp only [putNode, writerWP_modify]
      refine ⟨l, hl_leaf, hl_wf, hl_times, ?_, h2t, h2top, h2v, ?_⟩
      · intro q'
        rw [hl_look q']
        simp [pairLookupStep]
      · intro x
        simp only
        rw [lookup_upsert, h2n, lookup_upsert]
        by_cases hxL : x = L
        · simp [hxL]
        · simp only [hxL, ↓reduceIte]
          by_cases hxq : x = q
          · simp [hxq]
          · simp only [hxq, ↓reduceIte, List.lookup_append]
            by_cases hxy : x = w.next
            · subst hxy; rw [hny]; simp [List.lookup]
            · simp only [hxy, ↓reduceIte]
              cases h : w.nodes.lookup x with
              | some m => rfl
              | none =>
                show (none : Option KNode).or ([(w.next, { leaf := n.leaf, ks := l.ks })].lookup x) = none
                rw [lookup_cons_ne _ _ _ _ hxy]; rfl
    split
    · simp only [note, writerWP_bind, writerWP_modify]
      refine writerWP_mono (writerWP_replaceOrAdd_last n [(cv, v)] c _) ?_
      rintro l w1 ⟨hw1, hl_leaf, hl_wf, hl_times, hl_look⟩
      subst w1
      split <;>
      · simp only [newKey, fresh, setMadeFor, klongAt, note, writerWP_bind, writerWP_modify,
          writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
        split <;>
        · simp only [writerWP_bind, writerWP_modify, writerWP_pure, hpk]
          refine writerWP_mono (writerWP_appendKlongs_room d' q qn k1 w.next c _
            (by simp [List.lookup_append, hlq]) hroomq (hdeadq _)) ?_
          intro _ w2 hw2
          subst hw2
          exact hfinal l hl_leaf hl_wf hl_times hl_look _ rfl rfl rfl rfl
    · simp only [writerWP_bind]
      refine writerWP_mono (writerWP_replaceOrAdd_last n [(cv, v)] c _) ?_
      rintro l w1 ⟨hw1, hl_leaf, hl_wf, hl_times, hl_look⟩
      subst w1
      split <;>
      · simp only [newKey, fresh, setMadeFor, klongAt, note, writerWP_bind, writerWP_modify,
          writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
        split <;>
        · simp only [writerWP_bind, writerWP_modify, writerWP_pure, hpk]
          refine writerWP_mono (writerWP_appendKlongs_room d' q qn k1 w.next c _
            (by simp [List.lookup_append, hlq]) hroomq (hdeadq _)) ?_
          intro _ w2 hw2
          subst hw2
          exact hfinal l hl_leaf hl_wf hl_times hl_look _ rfl rfl rfl rfl

theorem writerWP_appendKlongs_timeSplitLeafParent (d' : Nat) (L q : NodeId) (n qn : KNode)
    (k1 cv v : Nat) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hlq : w.nodes.lookup q = some qn)
    (hqL : q ≠ L) (hql : qn.leaf = true) (hfirst : n.firstTime ≠ some c.i)
    (hfull : ¬ (n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv v)) = false))
    (hsplit : c.p.M ≤ n.size + 1 → (n.lastVersion c.i).size ≤ c.p.splitAbove)
    (hpq : (w.path[d']?).map (·.2) = some q) (hpk : w.path[d' + 1]? = some (some k1, L))
    (hroomq : qn.size + 1 + 1 ≤ c.p.M) (hdeadq : ∀ y, deadOver c.p (qn.add c.i (.key k1 y)) = false)
    (hny : w.nodes.lookup w.next = none) :
    WriterWP (appendKlongs (d' + 1) L [(cv, v)]) c w
      (fun _ w' => TimeSplitAfter c w w' L q n qn k1 cv v) := by
  rw [appendKlongs_step_dead]
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w hlk]
  have hts := fun compact hcs => writerWP_handleFullWith_timeSplitLeafParent d' L q n qn k1 cv v compact c w
    hlk hlq hqL hql hfirst hcs hpq hpk hroomq hdeadq hny
  split
  · rename_i hsize
    apply hts false
    have h1 : c.p.M ≤ n.size + 1 := by simp at hsize; omega
    simp only [Bool.not_false, Bool.true_and, decide_eq_false_iff_not, gt_iff_lt, Nat.not_lt]
    exact hsplit h1
  · rename_i hsize
    have hlt : n.size + 1 < c.p.M := by simp at hsize; omega
    have hd : deadOver c.p (n.add c.i (.key cv v)) = true := by
      cases h : deadOver c.p (n.add c.i (.key cv v)) with
      | true => rfl
      | false => exact absurd ⟨hlt, h⟩ hfull
    simp only [List.foldl_cons, List.foldl_nil, hd, ↓reduceIte]
    exact hts true (by simp)

/-- A search for compare value c finds a klong of c. -/
theorem KNode.searchEq_c (n : KNode) (t : Time) (c : Nat) (fd : Found)
    (h : n.searchEq t c = some fd) : fd.c = c := by
  unfold KNode.searchEq at h
  generalize (prefixAt n.ks t).zipIdx = l at h
  suffices hs : ∀ (l : List (Klong × Nat)) (acc : Option Time × List Nat × Option Found),
      (∀ f, acc.2.2 = some f → f.c = c) → ∀ f, (l.foldl (fun (acc : Option Time × List Nat × Option Found) (k, i) =>
      if acc.2.1.contains i then acc else
        match k with
        | .time x => (some x, acc.2.1, acc.2.2)
        | .key c' y => if c' == c then (acc.1, acc.2.1, some ⟨c, i, acc.1.getD 0, y⟩) else acc
        | .del b => (acc.1, b, match acc.2.2 with
          | some f => if b.contains f.idx then none else some f
          | none => none)) acc).2.2 = some f → f.c = c from
    hs l _ (fun f hf => by simp at hf) fd h
  intro l
  induction l with
  | nil => intro acc hacc f hf; exact hacc f hf
  | cons e rest ih =>
    intro acc hacc f hf
    rw [List.foldl_cons] at hf
    apply ih _ _ f hf
    intro f' hf'
    rcases e with ⟨k, i⟩
    simp only at hf'
    split at hf'
    · exact hacc f' hf'
    · split at hf'
      · exact hacc f' hf'
      · split at hf'
        · simp only [Option.some.injEq] at hf'; rw [← hf']
        · exact hacc f' hf'
      · simp only at hf'
        split at hf'
        · rename_i f0 hf0
          split at hf'
          · cases hf'
          · simp only [Option.some.injEq] at hf'; rw [← hf']; exact hacc f0 hf0
        · cases hf'

theorem fromVisits_append_gen (N : NodeId → Option KNode) (t : Time) (fuel : Nat)
    (k : Nat) (rest : List Nat) :
    ∀ (pre : List Nat) (r rk : NodeId), segRootR N t fuel pre r = some rk →
      ∀ q ∈ eqVisits N t k fuel rk, q ∈ fromVisits N t fuel (pre ++ k :: rest) r := by
  intro pre
  induction pre with
  | nil =>
    intro r rk hrk q hq
    simp only [segRootR, Option.some.injEq] at hrk
    subst hrk
    cases rest with
    | nil => exact hq
    | cons d rest' => simp only [List.nil_append, fromVisits]; exact List.mem_append_left _ hq
  | cons c pre ih =>
    intro r rk hrk q hq
    have hne : pre ++ k :: rest ≠ [] := by simp
    obtain ⟨d, rest', he⟩ : ∃ d rest', pre ++ k :: rest = d :: rest' := by
      cases h : pre ++ k :: rest with
      | nil => exact absurd h hne
      | cons d rest' => exact ⟨d, rest', rfl⟩
    simp only [segRootR] at hrk
    simp only [List.cons_append]
    rw [he]
    simp only [fromVisits]
    apply List.mem_append_right
    cases hg : getEqR N t c fuel r with
    | none => rw [hg] at hrk; cases hrk
    | some y =>
      rw [hg] at hrk
      simp only at hrk ⊢
      split at hrk
      · rw [← he]; exact ih y rk hrk q hq
      · cases hrk

theorem segRootR_snoc (N : NodeId → Option KNode) (t : Time) (fuel : Nat) (k : Nat) :
    ∀ (pre : List Nat) (r : NodeId), segRootR N t fuel (pre ++ [k]) r =
      (segRootR N t fuel pre r).bind (fun rk => match getEqR N t k fuel rk with
        | some y => if (N y).isSome then some y else none
        | none => none) := by
  intro pre
  induction pre with
  | nil =>
    intro r
    simp only [List.nil_append, segRootR, Option.bind_some]
    cases getEqR N t k fuel r <;> rfl
  | cons c pre ih =>
    intro r
    simp only [List.cons_append, segRootR]
    cases getEqR N t c fuel r with
    | none => rfl
    | some y =>
      simp only
      split
      · exact ih y
      · rfl

/-! ## The rule: a time split of a segment root below a segment leaf -/

/-- A put of a key whose last segment's tree is one leaf L that existed before
the transaction, full, with at most h klongs in its last version or full by
its dead klongs only, below the segment leaf q of the key's segment before,
which has room: the time split of L changes the reading by the put alone. The
premises are those of the time split rule (`writerWP_put_timeSplit_key`), with
q not reached from L. -/
theorem writerWP_put_segTimeSplit (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre0 : List Nat) (k1 cv h : Nat) (rq L : NodeId) (n : KNode) (w : W)
    (hkey : keyWf (pre0 ++ [k1, cv]) = true)
    (hrq : segRootR (wNode c.p base w) c.i c.p.fuel pre0 w.top.rootKey = some rq)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre0 ++ [k1, cv]) w.top.rootKey,
      w.taken.contains q.1 = false)
    (hids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
      (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next) ∧
      (∀ q ∈ w.vals, q.1 < w.next) ∧ w.top.rootKey < w.next)
    (hbase : knodeOf c.p base w.next = none ∧ valueOf base (w.next + 2) = none ∧
      knodeOf c.p base (w.next + 2) = none)
    (hL : getEqR (wNode c.p base w) c.i k1 c.p.fuel rq = some L)
    (hNL : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (hleaf : (∀ s, Klong.time s ∈ n.ks → s ≤ c.i) ∧
      ¬ (n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv w.next)) = false) ∧
      n.firstTime ≠ some c.i ∧ (c.p.M ≤ n.size + 1 → (n.lastVersion c.i).size ≤ c.p.splitAbove) ∧
      wValue base w L = none ∧ L ≠ w.top.rootKey)
    (hseg : ∀ q qn, (q, k1) ∈ eqVisits (wNode c.p base w) c.i k1 c.p.fuel rq →
      wNode c.p base w q = some qn → qn.leaf = true →
      (∀ s, Klong.time s ∈ qn.ks → s ≤ c.i) ∧ qn.size + 1 + 1 ≤ c.p.M ∧
      ∀ y, deadOver c.p (qn.add c.i (.key k1 y)) = false)
    (huniq : ∀ key' x n', keyWf key' = true →
      (x, cv) ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
      (x, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel L →
      wNode c.p base w x = some n' → n'.leaf = true → key' = pre0 ++ [k1, cv])
    (hwf : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → klongsWf xn.ks = true)
    (htreeK : ∀ x xn cc z, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → (cc, z) ∈ xn.liveAt c.i → (wNode c.p base w z).isSome = true →
      ∀ x' xn' cc', ReachS (wNode c.p base w) c.i w.top.rootKey x' →
        wNode c.p base w x' = some xn' → (cc', z) ∈ xn'.liveAt c.i → x = x' ∧ cc = cc')
    (hnotq : ∀ q, (q, k1) ∈ eqVisits (wNode c.p base w) c.i k1 c.p.fuel rq →
      ∀ x, ReachS (wNode c.p base w) c.i L x → x ≠ q)
    (hfr : ∀ x xn cc z, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → (cc, z) ∈ xn.liveAt c.i → z ≠ w.next ∧ z ≠ w.next + 2) :
    WriterWP (putKv (.put (pre0 ++ [k1, cv]) h)) c w (fun _ w' => ∀ key', keyWf key' = true →
      wGet c.p c.i base w' key' =
        if Op.key (.put (pre0 ++ [k1, cv]) h) == key' then Op.value (.put (pre0 ++ [k1, cv]) h)
        else wGet c.p c.i base w key') := by
  obtain ⟨hidn, hidv, hidt, hidvals, hidr⟩ := hids
  obtain ⟨htimes, hfull, hfirst, hsplit, hLval, hLroot⟩ := hleaf
  have hfuel : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  have hkey' : pre0 ++ [k1, cv] = (pre0 ++ [k1]) ++ [cv] := by simp
  -- the key's visits
  have hvk1 : ∀ q ∈ eqVisits (wNode c.p base w) c.i k1 c.p.fuel rq,
      q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre0 ++ [k1, cv]) w.top.rootKey :=
    fromVisits_append_gen _ _ _ k1 [cv] pre0 _ rq hrq
  have hsegL : segRootR (wNode c.p base w) c.i c.p.fuel (pre0 ++ [k1]) w.top.rootKey = some L := by
    rw [segRootR_snoc, hrq]
    simp only [Option.bind_some, hL, hNL, Option.isSome_some, ↓reduceIte]
  have hvcv : ∀ q ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel L,
      q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre0 ++ [k1, cv]) w.top.rootKey := by
    rw [hkey']; exact fromVisits_append _ _ _ (pre0 ++ [k1]) cv _ L hsegL
  unfold putKv pathClear findRoot pathAdd
  wpSimplify
  generalize hw2 : ({ ({ w with path := [] } : W) with
    path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w2
  have hr02 : ReadsAs c.p base w w2 := by subst hw2; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hw2n : w2.nodes = w.nodes := by subst hw2; rfl
  refine writerWP_putSegs_walk_src c base hvc (pre0 ++ [k1, cv]) (some h) [k1, cv] (by simp) _ pre0
    w.top.rootKey rq w2 (by rw [hr02.1, hr02.2.2.1]; exact ht) (by rw [hr02.1]; exact hrq)
    (by subst hw2; simp) ?_
  intro w2' hr2' hp2' hsrc2'
  have hr0 := ReadsAs.trans _ _ _ _ _ hr02 hr2'
  rw [putSegs.eq_3 _ _ rq k1 [cv] (by simp)]
  unfold setNode
  wpSimplify
  have ht1 : ∀ q ∈ eqVisits (wNode c.p base w2') c.i k1 c.p.fuel rq,
      w2'.taken.contains q.1 = false := by
    rw [hr0.1, hr0.2.2.1]
    exact fun q hq => ht q (hvk1 q hq)
  refine writerWP_mono (writerWP_and
    (writerWP_descendLte_path k1 c base hvc c.p.fuel rq w2' ht1 hp2')
    (writerWP_descendLte_cache k1 c base hvc c.p.fuel rq w2' ht1)) ?_
  intro q w3 ⟨⟨hr23, qn, hq, hql, hlkq3, hvisq, hgetq, hdpq⟩, ⟨hcache3, hsrc3, _⟩⟩
  rw [hr0.1] at hq hvisq hgetq hcache3
  have hr03 := ReadsAs.trans _ _ _ _ _ hr0 hr23
  rw [writerWP_getNode_known q qn c _ (by simpa using hlkq3)]
  rw [hL] at hgetq
  cases hfd : qn.searchEq c.i k1 with
  | none => rw [hfd] at hgetq; cases hgetq
  | some fd =>
    rw [hfd] at hgetq
    simp only [Option.map_some, Option.some.injEq] at hgetq
    have hfdc : fd.c = k1 := KNode.searchEq_c qn c.i k1 fd hfd
    simp only [pathAdd, writerWP_bind, writerWP_modify, writerWP_pure]
    rw [← hgetq, putSegs.eq_2]
    generalize hw4 : ({ w3 with path := w3.path ++ [(some fd.c, L)] } : W) = w4
    have hr34 : ReadsAs c.p base w3 w4 := by subst hw4; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    have hr04 := ReadsAs.trans _ _ _ _ _ hr03 hr34
    have hp4 : w4.path.getLast?.map (·.2) = some L := by subst hw4; simp
    unfold setValue
    wpSimplify
    have ht2 : ∀ q ∈ eqVisits (wNode c.p base w4) c.i cv c.p.fuel L,
        w4.taken.contains q.1 = false := by
      rw [hr04.1, hr04.2.2.1]
      exact fun q hq => ht q (hvcv q hq)
    refine writerWP_mono (writerWP_and
      (writerWP_descendLte_path cv c base hvc c.p.fuel L w4 ht2 hp4)
      (writerWP_descendLte_cache cv c base hvc c.p.fuel L w4 ht2)) ?_
    intro L' w5 ⟨⟨hr45, n', hn', hnl', hlk5, hvisL, _, hdp⟩, ⟨_, hsrc5, hpre5⟩⟩
    rw [hr04.1] at hn' hvisL
    have hr05 := ReadsAs.trans _ _ _ _ _ hr04 hr45
    have hnext5 : w5.next = w.next := hr05.2.2.2.2
    have hevL : eqVisits (wNode c.p base w) c.i cv c.p.fuel L = [(L, cv)] := by
      obtain ⟨f2, hf2⟩ : ∃ f2, c.p.fuel = f2 + 1 := ⟨c.p.fuel - 1, by omega⟩
      rw [hf2]
      simp [eqVisits, hNL, hnl]
    obtain ⟨hLL, hp5⟩ : L' = L ∧ w5.path = w4.path := by
      rcases hdp with hd | ⟨pre', q', k1', qn', fd', _, _, hq', hql', _, _, _, hqv'⟩
      · exact hd
      · rw [hr04.1, hevL] at hqv'
        simp only [List.mem_singleton, Prod.mk.injEq] at hqv'
        rw [hr04.1, hqv'.1, hNL] at hq'
        cases hq'
        rw [hnl] at hql'
        cases hql'
    subst L'
    rw [hNL] at hn'
    cases hn'
    unfold newValue fresh
    wpSimplify
    rw [writerWP_getNode_known _ n c _ (by simpa using hlk5)]
    have hcond : (decide (n.size + 1 < c.p.M) && !deadOver c.p (n.add c.i (.key cv w5.next))) = false := by
      rw [hnext5]
      cases hd : deadOver c.p (n.add c.i (.key cv w.next)) with
      | true => simp
      | false =>
        have : ¬ n.size + 1 < c.p.M := fun hlt => hfull ⟨hlt, hd⟩
        simp [this]
    simp only [hcond, Bool.false_eq_true, ↓reduceIte, pathSize, writerWP_bind, writerWP_get,
      writerWP_pure]
    -- the path: q, then L by the klong k1
    have hlast3 : w3.path.getLast?.map (·.2) = some q := by
      rcases hdpq with ⟨hqr, hp3⟩ | ⟨pre', q', k1', qn', fd', hp3, _, _, _, _, _, _, _⟩
      · rw [hp3, hp2', hqr]
      · rw [hp3]; simp
    have hne3 : w3.path ≠ [] := by intro he; rw [he] at hlast3; simp at hlast3
    obtain ⟨d', hd'⟩ : ∃ d', w3.path.length = d' + 1 := by
      cases h' : w3.path.length with
      | zero => exact absurd (List.eq_nil_of_length_eq_zero h') hne3
      | succ k => exact ⟨k, rfl⟩
    have hlen : w5.path.length - 1 = d' + 1 := by
      rw [hp5, ← hw4]; simp only [List.length_append, List.length_singleton]; omega
    have hpq : (w5.path[d']?).map (·.2) = some q := by
      rw [hp5, ← hw4]
      simp only
      rw [List.getElem?_append_left (by omega)]
      rw [List.getLast?_eq_getElem?, hd'] at hlast3
      simpa using hlast3
    have hpk : w5.path[d' + 1]? = some (some fd.c, L) := by
      rw [hp5, ← hw4]
      simp only
      rw [List.getElem?_append_right (by omega), hd']
      simp
    have hlq5 : w5.nodes.lookup q = some qn := by
      have h3 := hcache3 q qn hvisq hq
      have h4 : w4.nodes = w3.nodes := by rw [← hw4]
      obtain ⟨tl, htl⟩ := hpre5
      rw [← htl, List.lookup_append, h4, h3]; rfl
    have hsrcw5 : ∀ z, (w5.nodes.lookup z).isSome = true → z < w.next := by
      intro z hz
      have h4 : w4.nodes = w3.nodes := by rw [← hw4]
      rcases hsrc5 z hz with h1 | h1
      · rw [h4] at h1
        rcases hsrc3 z h1 with h2 | h2
        · rcases hsrc2' z h2 with h3 | h3
          · rw [hw2n] at h3; exact hidn z h3
          · exact hidv z h3
        · exact hidv z h2
      · exact hidv z h1
    have hrrq : ReachS (wNode c.p base w) c.i w.top.rootKey rq :=
      segRootR_reach _ _ _ _ hwf pre0 _ rq ReachS.root hrq
    have hrq' : ReachS (wNode c.p base w) c.i w.top.rootKey q :=
      eqVisits_reach _ _ _ k1 c.p.fuel rq q k1 hrrq hvisq
    have hqL : q ≠ L := fun he => hnotq q hvisq L ReachS.root he.symm
    obtain ⟨hqt, hroomq, hdeadq⟩ := hseg q qn hvisq hq hql
    have hny : w5.nodes.lookup (w5.next + 2) = none := by
      cases h' : w5.nodes.lookup (w5.next + 2) with
      | none => rfl
      | some _ => have := hsrcw5 _ (by rw [h']; rfl); omega
    rw [hlen]
    refine writerWP_mono (writerWP_appendKlongs_timeSplitLeafParent d' L q n qn fd.c cv w5.next c _
      (by simpa using hlk5) (by simpa using hlq5) hqL hql hfirst (by rw [hnext5]; exact hfull) hsplit
      (by simpa using hpq) (by simpa using hpk) hroomq (by rw [hfdc]; exact hdeadq)
      (by simpa using hny)) ?_
    intro _ wf hTS
    obtain ⟨l, hl_leaf, hl_wf, hl_times, hl_look, hft, hftop, hfv, hfn⟩ := hTS
    simp only at hft hftop hfv hfn
    rw [hr05.2.2.1] at hft
    rw [hr05.2.1] at hftop
    rw [hr05.2.2.2.1, hnext5] at hfv
    rw [hnext5, hfdc] at hfn
    rw [hnext5] at hl_look
    have hLlt : L < w.next := hsrcw5 L (by rw [hlk5]; rfl)
    have hqlt : q < w.next := hsrcw5 q (by rw [hlq5]; rfl)
    have hntake : ∀ z, w.next ≤ z → w.taken.contains z = false := by
      intro z hz
      cases h' : w.taken.contains z with
      | false => rfl
      | true => have := hidt z h'; omega
    have hvalnone : ∀ z, w.next ≤ z → w.vals.lookup z = none := by
      intro z hz
      apply List.lookup_eq_none_iff.mpr
      intro q' hq'
      have := hidvals q' hq'
      simp only [bne_iff_ne, ne_eq]
      omega
    have hnodenone : ∀ z, w.next ≤ z → w.nodes.lookup z = none := by
      intro z hz
      cases h' : w.nodes.lookup z with
      | none => rfl
      | some _ => have := hidn z (by rw [h']; rfl); omega
    have hk1 : (k1, L) ∈ qn.live := by
      have := KNode.searchEq_mem qn c.i k1 fd (hwf q qn hrq' hq) hfd
      rw [KNode.liveAt_of_times qn c.i hqt, ← hgetq] at this
      exact this
    have hm : ({ leaf := n.leaf, ks := l.ks } : KNode) = l := by
      cases l; simp only at hl_leaf ⊢; rw [hl_leaf]
    have hLt : wf.taken.contains L = false := by
      rw [hft]; exact ht (L, cv) (hvcv _ (by rw [hevL]; simp))
    have hres := getFromR_segTimeSplit (wNode c.p base w) (wNode c.p base wf) (wValue base w)
      (wValue base wf) c.i c.p.fuel hfuel w.top.rootKey q L (w.next + 2) w.next n qn
      ⟨n.leaf, l.ks⟩ k1 (pre0 ++ [k1]) cv h hNL hnl (hwf L n (by
        have := segRootR_reach _ _ _ _ hwf (pre0 ++ [k1]) _ L ReachS.root hsegL; exact this) hNL)
      htimes hq hql (hwf q qn hrq' hq) hqt hk1
      (by
        have hqt' : wf.taken.contains q = false := by
          rw [hft]; exact ht (q, k1) (hvk1 _ hvisq)
        simp only [wNode, hqt', Bool.false_eq_true, ↓reduceIte, hfn, hqL])
      (by
        have hyt : wf.taken.contains (w.next + 2) = false := by rw [hft]; exact hntake _ (by omega)
        have h1 : w.next + 2 ≠ L := by omega
        have h2 : w.next + 2 ≠ q := by omega
        simp only [wNode, hyt, Bool.false_eq_true, ↓reduceIte, hfn, h1, h2])
      hnl hl_wf hl_times
      (by
        intro q'
        rw [hm, hl_look q'])
      (by
        intro x hxL hxq hxY
        rw [← hr05.1]
        simp only [wNode, hft, hfn, hxL, hxq, hxY, ↓reduceIte, hr05.2.2.1])
      (by
        have hvt : wf.taken.contains w.next = false := by rw [hft]; exact hntake _ (Nat.le_refl _)
        simp only [wValue, hvt, Bool.false_eq_true, ↓reduceIte, hfv,
          lookup_append_single_self _ _ _ (hvalnone _ (Nat.le_refl _))])
      (by
        intro a ha
        simp only [wValue, hft, hfv, lookup_append_single_ne _ _ _ _ ha])
      (by
        rw [← hLval]
        have hl' : (w.vals ++ [(w.next, h)]).lookup L = w.vals.lookup L :=
          lookup_append_single_ne _ _ _ _ (by omega)
        simp only [wValue, hft, hfv, hl'])
      (by
        have hyt : wf.taken.contains (w.next + 2) = false := by rw [hft]; exact hntake _ (by omega)
        simp only [wValue, hyt, Bool.false_eq_true, ↓reduceIte, hfv,
          lookup_append_single_ne _ _ _ _ (by omega : w.next + 2 ≠ w.next),
          hvalnone _ (by omega : w.next ≤ w.next + 2), hbase.2.1])
      hqL (by omega) (by omega) (by omega) (by omega) (by omega)
      (by
        simp only [wNode, hntake _ (Nat.le_refl _), Bool.false_eq_true, ↓reduceIte,
          hnodenone _ (Nat.le_refl _), hbase.1])
      hLroot.symm (by omega) hrq' hsegL
      (keyWf_last_notin (pre0 ++ [k1]) cv (by rw [← hkey']; exact hkey))
      (fun key' x n' hk' h1 h2 h3 h4 => by rw [← hkey']; exact huniq key' x n' hk' h1 h2 h3 h4)
      hwf
      (fun x xn c' hx hxn hz => htreeK x xn c' L hx hxn hz (by simp [hNL]) q qn k1 hrq' hq
        (by rw [KNode.liveAt_of_times qn c.i hqt]; exact hk1))
      (hnotq q hvisq)
      hfr
    intro key' hkey2
    unfold wGet
    rw [hftop, hres key' hkey2, ← hkey']
    simp only [Op.key, Op.value]
    rfl

end SIS.Tree
