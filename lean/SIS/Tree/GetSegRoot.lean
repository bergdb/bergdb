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

end SIS.Tree
