import SIS.Tree.GetNewSeg
import SIS.Tree.WriterTreeRepoint

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! A put into a segment's root L, a full leaf that the transaction made, below
the segment leaf q of the key's segment before (bergdb 024-12, TP10; `OpGetOK`'s
rules): the space split in place keeps the first half at L, makes the second
and a new segment root, and repoints q's klong to L in place
(`split.space2.inplace`). -/

theorem KNode.linkIndex_split (n : KNode) (x : NodeId) (c0 j : Nat)
    (hj : n.linkIndex x c0 = some j) :
    ∃ pre post, n.ks = pre ++ Klong.key c0 x :: post ∧ pre.length = j ∧
      (∀ k ∈ post, ∀ y, k ≠ Klong.key c0 y) ∧ n.lastBitmap.contains j = false := by
  unfold KNode.linkIndex at hj
  dsimp only at hj
  split at hj
  · rename_i c' y' i hf
    split at hj
    · rename_i hc
      have hij : i = j := Option.some.inj hj
      subst hij
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, beq_iff_eq] at hc
      obtain ⟨hdel, hy⟩ := hc
      subst hy
      obtain ⟨hp, as, bs, hrev, has⟩ := List.find?_eq_some_iff_append.mp hf
      simp only [beq_iff_eq] at hp
      subst hp
      have hz : n.ks.zipIdx = bs.reverse ++ (Klong.key c' y', i) :: as.reverse := by
        have := congrArg List.reverse hrev
        simpa using this
      obtain ⟨l1, l2, hks, h1, h2⟩ := List.zipIdx_eq_append_iff.mp hz
      obtain ⟨a, rest, hl2, ha, hrest⟩ := List.zipIdx_eq_cons_iff.mp h2.symm
      simp only [Prod.mk.injEq, Nat.zero_add] at ha
      obtain ⟨ha1, ha2⟩ := ha
      subst hl2
      refine ⟨l1, rest, by rw [hks, ha1], ha2.symm, ?_, hdel⟩
      intro k hk y hky
      subst hky
      obtain ⟨m, hm⟩ : ∃ m, (Klong.key c' y, m) ∈ rest.zipIdx (l1.length + 1) := by
        obtain ⟨m, hm⟩ := List.mem_iff_getElem.mp hk
        refine ⟨l1.length + 1 + m, ?_⟩
        apply List.mem_iff_getElem.mpr
        refine ⟨m, by simpa using hm.1, ?_⟩
        simp [hm.2]
      have hm' : (Klong.key c' y, m) ∈ as.reverse := by
        rw [hrest]; simpa using hm
      have := has (Klong.key c' y, m) (by simpa using hm')
      simp at this
    · cases hj
  · cases hj

theorem keyLookupFold_no_key (del : List Nat) (c0 : Nat) :
    ∀ (post : List Klong) (k : Nat) (v : Option NodeId), (∀ q ∈ post, ∀ y, q ≠ Klong.key c0 y) →
      (post.zipIdx k).foldl (keyLookupStep del c0) v = v := by
  intro post
  induction post with
  | nil => intro k v _; rfl
  | cons q rest ih =>
    intro k v h
    simp only [List.zipIdx_cons, List.foldl_cons]
    have hq : keyLookupStep del c0 v (q, k) = v := by
      unfold keyLookupStep
      cases q with
      | key a z =>
        simp only
        have : (a == c0) = false := by
          cases hb : (a == c0) with
          | false => rfl
          | true => exact absurd (by rw [beq_iff_eq.mp hb]) (h (Klong.key a z) List.mem_cons_self z)
        simp [this]
      | time t => rfl
      | del b => rfl
    rw [hq]
    exact ih (k + 1) v (fun q' hq' => h q' (List.mem_cons_of_mem _ hq'))

/-- A klong repointed in place at the index that `linkIndex` gives for c0: the
live klong of c0 names the new node, every other is the node's. -/
theorem KNode.repoint_live_lookup (n : KNode) (x y : NodeId) (c0 j : Nat)
    (hj : n.linkIndex x c0 = some j) (c : Nat) :
    (n.repoint j y).live.lookup c = if c0 == c then some y else n.live.lookup c := by
  obtain ⟨pre, post, hks, hlen, hpost, hdel⟩ := KNode.linkIndex_split n x c0 j hj
  have hget : n.ks[j]? = some (Klong.key c0 x) := by
    rw [hks, ← hlen]; simp
  have hrep : n.repoint j y = { n with ks := pre ++ Klong.key c0 y :: post } := by
    unfold KNode.repoint
    rw [hget]
    simp only [KNode.setAt, hks, ← hlen]
    congr 1
    simp
  have hbm : (n.repoint j y).lastBitmap = n.lastBitmap := by
    unfold KNode.lastBitmap
    rw [hrep]
    simp only
    have := lastBitmapOf_set_key n.ks j c0 y ⟨x, hget⟩
    rw [← this, hks, ← hlen]
    simp
  rw [KNode.live_lookup, KNode.live_lookup, hbm]
  unfold keyLookup
  rw [hrep]
  simp only
  rw [hks]
  simp only [List.zipIdx_append, List.zipIdx_cons, List.foldl_append, List.foldl_cons,
    Nat.zero_add, hlen]
  by_cases hc : c0 = c
  · subst hc
    simp only [beq_self_eq_true, ↓reduceIte]
    have hs : keyLookupStep n.lastBitmap c0 ((pre.zipIdx).foldl (keyLookupStep n.lastBitmap c0) none)
        (Klong.key c0 y, j) = some y := by
      have hdel' : j ∉ n.lastBitmap := by simpa using hdel
      unfold keyLookupStep
      simp [hdel']
    rw [hs]
    exact keyLookupFold_no_key _ _ post (j + 1) (some y) hpost
  · have hb : (c0 == c) = false := by simpa using hc
    simp only [hb, Bool.false_eq_true, ↓reduceIte]
    congr 1
    unfold keyLookupStep
    simp [hb]

/-- After a space split in place of the root L of a key's last segment, a leaf
below the segment leaf q (L holds the first half, S the second, q's klong k1
names the new root Y in place, whose klongs (0, L) and (sc, S) name them), every
key reads what it read but the key, which reads the put's value. -/
theorem getFromR_segSpaceSplitInPlace (N N2 : NodeId → Option KNode) (V V2 : NodeId → Option Nat)
    (i : Time) (fuel : Nat) (hfuel : 2 ≤ fuel) (root q L S Y v : NodeId) (n qn qn2 : KNode)
    (k1 : Nat) (pre : List Nat) (cv h : Nat)
    (hNL : N L = some n) (hnl : n.leaf = true) (hnwf : klongsWf n.ks = true)
    (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ i) (hlive : n.live ≠ [])
    (hNq : N q = some qn) (hql : qn.leaf = true) (hqwf : klongsWf qn.ks = true)
    (hqt : ∀ s, Klong.time s ∈ qn.ks → s ≤ i) (hk1 : (k1, L) ∈ qn.live)
    (hN2q : N2 q = some qn2) (hq2l : qn2.leaf = true) (hq2wf : klongsWf qn2.ks = true)
    (hq2t : ∀ s, Klong.time s ∈ qn2.ks → s ≤ i)
    (hq2look : ∀ c, qn2.live.lookup c = if k1 == c then some Y else qn.live.lookup c)
    (hN2R : N2 Y = some ⟨false, newKlongs i
      [(0, L), ((halves n.leaf i (n.lastVersion i) [(cv, v)]).2.2, S)]⟩)
    (hN2F : N2 L = some (halves n.leaf i (n.lastVersion i) [(cv, v)]).1)
    (hN2S : N2 S = some (halves n.leaf i (n.lastVersion i) [(cv, v)]).2.1)
    (hN2 : ∀ x, x ≠ L → x ≠ q → x ≠ S → x ≠ Y → N2 x = N x)
    (hV2v : V2 v = some h) (hV2 : ∀ a, a ≠ v → V2 a = V a) (hV2L : V2 L = none)
    (hV2Y : V2 Y = none)
    (hqL : q ≠ L) (hYq : Y ≠ q) (hYL : Y ≠ L) (hSL : S ≠ L)
    (hSq : S ≠ q) (hvL : v ≠ L) (hvY : v ≠ Y) (hvq : v ≠ q) (hvS : v ≠ S)
    (hNv : N v = none)
    (hrootL : root ≠ L) (hrootY : root ≠ Y) (hrootS : root ≠ S)
    (hrq : ReachS N i root q)
    (hrk : segRootR N i fuel pre root = some L) (hcv : cv ∉ pre)
    (huniq : ∀ key' x m', keyWf key' = true → (x, cv) ∈ fromVisits N i fuel key' root →
      (x, cv) ∈ eqVisits N i cv fuel L → N x = some m' → m'.leaf = true → key' = pre ++ [cv])
    (hwf : ∀ x xn, ReachS N i root x → N x = some xn → klongsWf xn.ks = true)
    (honlyL : ∀ x xn c, ReachS N i root x → N x = some xn → (c, L) ∈ xn.liveAt i →
      x = q ∧ c = k1)
    (hnotq : ∀ x, ReachS N i L x → x ≠ q)
    (hfr : ∀ x xn c z, ReachS N i root x → N x = some xn → (c, z) ∈ xn.liveAt i →
      z ≠ v ∧ z ≠ Y ∧ z ≠ S) :
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
  have hA := getFromR_leaf_change_seg N Nm V V2 i fuel (by omega) L pre cv root L n m
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
  let D' : NodeId → Prop := fun z => z = L ∨ z = Y ∨ z = q ∨ z = S
  have hlinksL : ∀ x xn c z, ReachS Nm i L x → Nm x = some xn → (c, z) ∈ xn.liveAt i → ¬ D' z := by
    intro x xn c z hx hn hz
    -- x is reached from L in N (or is v, no key node)
    have hxN : ReachS N i L x ∨ x = v := hreachL x hx
    have hlink : ∀ x' xn', ReachS N i L x' → N x' = some xn' → (c, z) ∈ xn'.liveAt i → ¬ D' z := by
      intro x' xn' hx' hn' hz' hD
      have hx'r : ReachS N i root x' := reachS_trans N i root L hrL x' hx'
      rcases hD with h1 | h1 | h1 | h1
      · subst h1
        exact hnotq x' hx' (honlyL x' xn' c hx'r hn' hz').1
      · exact (hfr x' xn' c z hx'r hn' hz').2.1 h1
      · subst h1
        exact hnotq z (ReachS.step x' xn' c z hx' hn' hz') rfl
      · exact (hfr x' xn' c z hx'r hn' hz').2.2 h1
    by_cases hxL : x = L
    · subst hxL; rw [hNmL] at hn; cases hn
      rcases hmem c z hz with h1 | h1
      · exact hlink x n ReachS.root hNL h1
      · subst h1
        rintro (h | h | h | h)
        · exact hvL h
        · exact hvY h
        · exact hvq h
        · exact hvS h
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
  -- the halves
  have hlv := KNode.lastVersion_eq_newKlongs n i
  rw [hnl] at hlv
  rw [hnl, hlv] at hN2R hN2F hN2S
  obtain ⟨r, hr⟩ : ∃ r, (n.live.drop (n.live.length / 2)).head? = some r := by
    cases hd : (n.live.drop (n.live.length / 2)) with
    | nil =>
      have : n.live.length ≤ n.live.length / 2 := List.drop_eq_nil_iff.mp hd
      have : n.live.length = 0 := by omega
      exact absurd (List.eq_nil_of_length_eq_zero this) hlive
    | cons a _ => exact ⟨a, rfl⟩
  have hshape := halves_leaf_shape i n.live [(cv, v)] r hr
  simp only [List.head?_cons] at hshape
  have hwfh := halves_newKlongs_wf true i n.live [(cv, v)]
  generalize hout : halves true i ⟨true, newKlongs i n.live⟩ [(cv, v)] = out at hN2R hN2F hN2S hN2q hwfh hshape
  obtain ⟨f, s, sc⟩ := out
  simp only at hN2R hN2F hN2S hN2q hwfh
  have hfs : f.leaf = true ∧ s.leaf = true ∧ (∀ t', Klong.time t' ∈ f.ks → t' ≤ i) ∧
      (∀ t', Klong.time t' ∈ s.ks → t' ≤ i) := by
    by_cases hd : r.1 ≤ cv <;>
    · simp only [hd, decide_true, decide_false, ↓reduceIte, Bool.false_eq_true,
        Prod.mk.injEq] at hshape
      obtain ⟨hf, hs', _⟩ := hshape
      subst hf hs'
      exact ⟨rfl, rfl, newKlongs_times i _, newKlongs_times i _⟩
  obtain ⟨hfl, hsl, hft, hst⟩ := hfs
  have hlook := halves_leaf_lookup i n.live [(cv, v)] n.live_order r hr (by simp)
  rw [hout] at hlook
  simp only at hlook
  have hleaf : ∀ c, ((if c < sc then f else s).searchEq i c).map (·.y) = (m.searchEq i c).map (·.y) := by
    intro c
    by_cases hc : c < sc
    · simp only [hc, ↓reduceIte]
      rw [KNode.searchEq_live f i hwfh.1 hft, KNode.searchEq_live m i hmwf hmt, hmlook]
      have := hlook c
      simp only [hc, ↓reduceIte] at this
      rw [this]
      simp [pairLookupStep]
    · simp only [hc, ↓reduceIte]
      rw [KNode.searchEq_live s i hwfh.2 hst, KNode.searchEq_live m i hmwf hmt, hmlook]
      have := hlook c
      simp only [hc, ↓reduceIte] at this
      rw [this]
      simp [pairLookupStep]
  have hfirst : ∀ c, getEqR N2 i c fuel Y = getEqR Nm i c fuel L := by
    intro c
    obtain ⟨f2, hf2⟩ : ∃ f2, fuel = f2 + 2 := ⟨fuel - 2, by omega⟩
    rw [hf2]
    have hsr := KNode.rootPair_searchLte i L S sc c
    simp only [getEqR, hN2R, hNmL, hml, Bool.false_eq_true, ↓reduceIte]
    cases hs : (⟨false, newKlongs i [(0, L), (sc, S)]⟩ : KNode).searchLte i ↑c with
    | none => rw [hs] at hsr; cases hsr
    | some fd =>
      rw [hs] at hsr
      simp only [Option.map_some, Option.some.injEq] at hsr
      simp only
      rw [hsr]
      by_cases hc : c < sc
      · simp only [hc, ↓reduceIte, hN2F, hfl]
        have := hleaf c
        simp only [hc, ↓reduceIte] at this
        exact this
      · simp only [hc, ↓reduceIte, hN2S, hsl]
        have := hleaf c
        simp only [hc, ↓reduceIte] at this
        exact this
  have hsameL : ∀ x, ReachS Nm i L x → ¬ D' x → N2 x = Nm x := by
    intro x _ hD
    have h1 : x ≠ L := fun h => hD (Or.inl h)
    have h2 : x ≠ Y := fun h => hD (Or.inr (Or.inl h))
    have h3 : x ≠ q := fun h => hD (Or.inr (Or.inr (Or.inl h)))
    have h5 : x ≠ S := fun h => hD (Or.inr (Or.inr (Or.inr h)))
    rw [hN2 x h1 h3 h5 h2, hNm x h1]
  have hsub := getFromR_newRoot_sim Nm N2 V2 i fuel L Y D' hfirst hwfL hsameL hlinksL
  -- the graft at q
  let D : NodeId → Prop := fun z => z = L ∨ z = Y ∨ z = S
  have hqs : ∀ c, (qn2.searchEq i c).map (·.y) =
      ((qn.searchEq i c).map (·.y)).map (fun z => if z = L then Y else z) := by
    intro c
    rw [KNode.searchEq_live qn2 i hq2wf hq2t, hq2look, ← KNode.searchEq_live qn i hqwf hqt]
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
  have hgr := getFromR_graft Nm N2 V2 i fuel root q L Y D qn qn2 hNmq hN2q hql
    hq2l hqs (Or.inl rfl) hwfm
    (by
      intro x _ hD hxq
      have h1 : x ≠ L := fun h => hD (Or.inl h)
      have h2 : x ≠ Y := fun h => hD (Or.inr (Or.inl h))
      have h5 : x ≠ S := fun h => hD (Or.inr (Or.inr h))
      rw [hN2 x h1 hxq h5 h2, hNm x h1])
    (by
      intro x xn c z hx hD hxq hn hz hDz
      have hxL : x ≠ L := fun h => hD (Or.inl h)
      rw [hNm x hxL] at hn
      rcases hreach x hx with hx' | hxv
      · rcases hDz with h1 | h1 | h1
        · subst h1; exact hxq (honlyL x xn c hx' hn hz).1
        · exact (hfr x xn c z hx' hn hz).2.1 h1
        · exact (hfr x xn c z hx' hn hz).2.2 h1
      · subst hxv; rw [hNv] at hn; cases hn)
    (by
      intro c z hz hDz
      rcases hDz with h1 | h1 | h1
      · exact h1
      · exact absurd h1 (hfr q qn c z hrq hNq hz).2.1
      · exact absurd h1 (hfr q qn c z hrq hNq hz).2.2)
    (fun key _ => hsub key) (by rw [hN2R, hNmL]; rfl) (by rw [hV2Y, hV2L])
  intro key' hkey'
  rw [hgr key' root ReachS.root (by
    rintro (h | h | h)
    · exact hrootL h
    · exact hrootY h
    · exact hrootS h)]
  by_cases hk : pre ++ [cv] = key'
  · subst hk
    simp only [beq_self_eq_true, ↓reduceIte]
    rw [hA.1, KNode.searchEq_live m i hmwf hmt, hmlook]
    simp [hV2v]
  · have hk' : (pre ++ [cv] == key') = false := by simpa using hk
    simp only [hk', Bool.false_eq_true, ↓reduceIte]
    exact hA.2 key' hkey' (fun h' => hk h'.symm)

/-! ## The writer -/

/-- The state after a space split in place of the segment root L, a leaf that
the transaction made, below the segment leaf q: L holds the first half, the next
id the second, the id after it the new segment root, and q's klong k1 to L,
found by `linkIndex`, names it in place. -/
def SegSpaceSplitInPlaceAfter (c : Ctx) (w w' : W) (L q : NodeId) (n qn : KNode) (k1 cv v : Nat) :
    Prop :=
  ∃ j, qn.linkIndex L k1 = some j ∧
    w'.taken = w.taken ∧ w'.top = w.top ∧ w'.vals = w.vals ∧
    ∀ x, w'.nodes.lookup x =
      if x = L then some (halves n.leaf c.i (n.lastVersion c.i) [(cv, v)]).1
      else if x = q then some (qn.repoint j (w.next + 2))
      else if x = w.next then some (halves n.leaf c.i (n.lastVersion c.i) [(cv, v)]).2.1
      else if x = w.next + 2 then some ⟨false, [.time c.i, .key 0 L,
        .key (halves n.leaf c.i (n.lastVersion c.i) [(cv, v)]).2.2 w.next]⟩
      else w.nodes.lookup x

set_option linter.unusedSimpArgs false in
theorem writerWP_handleFullWith_segSpaceSplitInPlace (d' : Nat) (L q : NodeId) (n qn : KNode)
    (k1 cv v : Nat) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hlq : w.nodes.lookup q = some qn)
    (hqL : q ≠ L) (hql : qn.leaf = true) (hfirst : n.firstTime = some c.i)
    (hsplit : c.p.splitAbove < (n.lastVersion c.i).size)
    (hpq : (w.path[d']?).map (·.2) = some q) (hpk : w.path[d' + 1]? = some (some k1, L))
    (hLn : L < w.next) (hqn : q < w.next)
    (hny : w.nodes.lookup (w.next + 2) = none) :
    WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) L [(cv, v)]
      (n.lastVersion c.i) false) c w
      (fun _ w' => SegSpaceSplitInPlaceAfter c w w' L q n qn k1 cv v) := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w hlk]
  refine writerWP_ghOf_cached L n c w hlk _ (fun gh => ?_)
  have hnew : (n.firstTime == some c.i) = true := by simp [hfirst]
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
    have hsz : decide ((n.lastVersion c.i).size > c.p.splitAbove) = true := by
      simp only [decide_eq_true_eq, gt_iff_lt]; exact hsplit
    simp only [writerWP_pure, hql, hsz, Bool.not_false, Bool.true_and, Bool.false_eq_true,
      ↓reduceIte]
    have hq1 : q ≠ w.next := by omega
    have hq2 : q ≠ w.next + 2 := by omega
    have hL1 : L ≠ w.next := by omega
    have hL2 : L ≠ w.next + 2 := by omega
    simp only [newKey, fresh, setMadeFor, replacedBy, note, putNode, writerWP_bind, writerWP_modify,
      writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
    split <;>
    · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
      split <;>
      · simp only [writerWP_bind, writerWP_modify, writerWP_pure, writerWP_get, writerWP_set]
        split <;>
        · simp only [writerWP_bind, writerWP_modify, writerWP_pure, writerWP_get, writerWP_set]
          split <;>
          · simp only [writerWP_bind, writerWP_modify, writerWP_pure, writerWP_get, writerWP_set]
            refine (writerWP_klongAt (d' + 1) k1 L c _ ?_ _).mpr ?_
            · exact hpk
            refine (writerWP_getNode_known q qn c _ ?_ _).mpr ?_
            · simp only [lookup_upsert, List.lookup_append, hq1, hq2, hqL, ↓reduceIte, hlq]
              rfl
            split
            · rename_i j hj
              split
              · simp only [writerWP_bind]
                exact writerWP_throw _ _ _ _
              · simp only [writerWP_bind, writerWP_modify, Bool.not_true, Bool.false_eq_true,
                  ↓reduceIte, writerWP_pure]
                refine ⟨j, hj, rfl, rfl, rfl, ?_⟩
                intro x
                simp only [lookup_upsert, List.lookup_append]
                by_cases hxL : x = L
                · subst hxL; simp [hqL.symm, hL1, hL2]
                · simp only [hxL, ↓reduceIte]
                  by_cases hxq : x = q
                  · simp [hxq]
                  · simp only [hxq, ↓reduceIte]
                    by_cases h1 : x = w.next
                    · subst h1; simp
                    · simp only [h1, ↓reduceIte]
                      by_cases h2 : x = w.next + 2
                      · subst h2
                        rw [hny]
                        have hb : (w.next + 2 == w.next) = false := by simp
                        simp [List.lookup, hb]
                      · simp only [h2, ↓reduceIte]
                        cases h : w.nodes.lookup x with
                        | some m => rfl
                        | none =>
                          show (((none : Option KNode).or ([(w.next, { leaf := n.leaf, ks := [] })].lookup x)).or
                            ([(w.next + 2, _)].lookup x)) = none
                          rw [lookup_cons_ne _ _ _ _ h1, lookup_cons_ne _ _ _ _ h2]; rfl
            · exact writerWP_throw _ _ _ _

theorem writerWP_appendKlongs_segSpaceSplitInPlace (d' : Nat) (L q : NodeId) (n qn : KNode)
    (k1 cv v : Nat) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hlq : w.nodes.lookup q = some qn)
    (hqL : q ≠ L) (hql : qn.leaf = true) (hfirst : n.firstTime = some c.i)
    (hfull : c.p.M ≤ n.size + 1)
    (hsplit : c.p.splitAbove < (n.lastVersion c.i).size)
    (hpq : (w.path[d']?).map (·.2) = some q) (hpk : w.path[d' + 1]? = some (some k1, L))
    (hLn : L < w.next) (hqn : q < w.next) (hny : w.nodes.lookup (w.next + 2) = none) :
    WriterWP (appendKlongs (d' + 1) L [(cv, v)]) c w
      (fun _ w' => SegSpaceSplitInPlaceAfter c w w' L q n qn k1 cv v) := by
  rw [appendKlongs_step_dead]
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w hlk]
  have h1 : n.size + [(cv, v)].length + 1 > c.p.M := by simp; omega
  simp only [h1, ↓reduceIte]
  exact writerWP_handleFullWith_segSpaceSplitInPlace d' L q n qn k1 cv v c w hlk hlq hqL hql hfirst
    hsplit hpq hpk hLn hqn hny

/-- A put of a key whose last segment's tree is one leaf L that the transaction
made, full by its size, with more than h klongs in its last version, below the
segment leaf q of the key's segment before: the space split in place of L into
a new segment root, q's klong repointed in place, changes the reading by the put
alone. -/
theorem writerWP_put_segSpaceSplitInPlace (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre0 : List Nat) (k1 cv h : Nat) (rq L : NodeId) (n : KNode) (w : W)
    (hkey : keyWf (pre0 ++ [k1, cv]) = true)
    (hrq : segRootR (wNode c.p base w) c.i c.p.fuel pre0 w.top.rootKey = some rq)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre0 ++ [k1, cv]) w.top.rootKey,
      w.taken.contains q.1 = false)
    (hids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
      (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next) ∧
      (∀ q ∈ w.vals, q.1 < w.next) ∧ w.top.rootKey < w.next)
    (hbase : ∀ z, w.next ≤ z → knodeOf c.p base z = none ∧ valueOf base z = none)
    (hL : getEqR (wNode c.p base w) c.i k1 c.p.fuel rq = some L)
    (hNL : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (hleaf : (∀ s, Klong.time s ∈ n.ks → s ≤ c.i) ∧ c.p.M ≤ n.size + 1 ∧
      n.firstTime = some c.i ∧ c.p.splitAbove < (n.lastVersion c.i).size ∧ n.live ≠ [] ∧
      wValue base w L = none ∧ L ≠ w.top.rootKey)
    (hseg : ∀ q qn, (q, k1) ∈ eqVisits (wNode c.p base w) c.i k1 c.p.fuel rq →
      wNode c.p base w q = some qn → qn.leaf = true →
      ∀ s, Klong.time s ∈ qn.ks → s ≤ c.i)
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
      wNode c.p base w x = some xn → (cc, z) ∈ xn.liveAt c.i →
        z ≠ w.next ∧ z ≠ w.next + 2 ∧ z ≠ w.next + 2 + 2) :
    WriterWP (putKv (.put (pre0 ++ [k1, cv]) h)) c w (fun _ w' => ∀ key', keyWf key' = true →
      wGet c.p c.i base w' key' =
        if Op.key (.put (pre0 ++ [k1, cv]) h) == key' then Op.value (.put (pre0 ++ [k1, cv]) h)
        else wGet c.p c.i base w key') := by
  obtain ⟨hidn, hidv, hidt, hidvals, hidr⟩ := hids
  obtain ⟨htimes, hfull, hfirst, hsplit, hlive, hLval, hLroot⟩ := hleaf
  have hfuel : 2 ≤ c.p.fuel := by unfold Params.fuel; omega
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
      have : ¬ n.size + 1 < c.p.M := by omega
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
    have hqt := hseg q qn hvisq hq hql
    rw [hlen]
    have hny : w5.nodes.lookup (w5.next + 2 + 2) = none := by
      cases h' : w5.nodes.lookup (w5.next + 2 + 2) with
      | none => rfl
      | some _ => have := hsrcw5 _ (by rw [h']; rfl); omega
    refine writerWP_mono (writerWP_appendKlongs_segSpaceSplitInPlace d' L q n qn fd.c cv w5.next c _
      (by simpa using hlk5) (by simpa using hlq5) hqL hql hfirst hfull hsplit
      (by simpa using hpq) (by simpa using hpk)
      (by have := hsrcw5 L (by rw [hlk5]; rfl); simp only; omega)
      (by have := hsrcw5 q (by rw [hlq5]; rfl); simp only; omega) (by simpa using hny)) ?_
    intro _ wf hSS
    obtain ⟨j, hj, hft, hftop, hfv, hfn⟩ := hSS
    simp only at hft hftop hfv hfn
    rw [hr05.2.2.1] at hft
    rw [hr05.2.1] at hftop
    rw [hr05.2.2.2.1, hnext5] at hfv
    rw [hnext5] at hfn
    rw [hfdc] at hj
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
    have hqt5 : ∀ s, Klong.time s ∈ (qn.repoint j (w.next + 2 + 2)).ks → s ≤ c.i := by
      intro s hs
      apply hqt s
      have hsh := KNode.repoint_shape qn j (w.next + 2 + 2)
      have : klongShape (Klong.time s) ∈ (qn.repoint j (w.next + 2 + 2)).ks.map klongShape :=
        List.mem_map_of_mem hs
      rw [hsh] at this
      obtain ⟨k, hk, hke⟩ := List.mem_map.mp this
      cases k with
      | time t' => simp only [klongShape, Klong.time.injEq] at hke; subst hke; exact hk
      | key a b => simp [klongShape] at hke
      | del b => simp [klongShape] at hke
    have hres := getFromR_segSpaceSplitInPlace (wNode c.p base w) (wNode c.p base wf) (wValue base w)
      (wValue base wf) c.i c.p.fuel hfuel w.top.rootKey q L (w.next + 2) (w.next + 2 + 2) w.next n qn
      (qn.repoint j (w.next + 2 + 2)) k1 (pre0 ++ [k1]) cv h hNL hnl (hwf L n (by
        have := segRootR_reach _ _ _ _ hwf (pre0 ++ [k1]) _ L ReachS.root hsegL; exact this) hNL)
      htimes hlive hq hql (hwf q qn hrq' hq) hqt hk1
      (by
        have hqt' : wf.taken.contains q = false := by
          rw [hft]; exact ht (q, k1) (hvk1 _ hvisq)
        simp only [wNode, hqt', Bool.false_eq_true, ↓reduceIte, hfn, hqL, hfdc])
      (by unfold KNode.repoint; split <;> simp [KNode.setAt, hql])
      (by rw [KNode.repoint_klongsWf]; exact hwf q qn hrq' hq)
      hqt5
      (fun c' => KNode.repoint_live_lookup qn L (w.next + 2 + 2) k1 j hj c')
      (by
        have hyt : wf.taken.contains (w.next + 2 + 2) = false := by
          rw [hft]; exact hntake _ (by omega)
        simp only [wNode, hyt, Bool.false_eq_true, ↓reduceIte, hfn,
          show w.next + 2 + 2 ≠ L by omega, show w.next + 2 + 2 ≠ q by omega,
          show w.next + 2 + 2 ≠ w.next + 2 by omega]
        rfl)
      (by
        have hLt : wf.taken.contains L = false := by
          rw [hft]; exact ht (L, cv) (hvcv _ (by rw [hevL]; simp))
        simp only [wNode, hLt, Bool.false_eq_true, ↓reduceIte, hfn])
      (by
        have hyt : wf.taken.contains (w.next + 2) = false := by rw [hft]; exact hntake _ (by omega)
        simp only [wNode, hyt, Bool.false_eq_true, ↓reduceIte, hfn,
          show w.next + 2 ≠ L by omega, show w.next + 2 ≠ q by omega])
      (by
        intro x hxL hxq hxS hxY
        rw [← hr05.1]
        simp only [wNode, hft, hfn, hxL, hxq, hxS, hxY, ↓reduceIte, hr05.2.2.1])
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
        have hyt : wf.taken.contains (w.next + 2 + 2) = false := by
          rw [hft]; exact hntake _ (by omega)
        simp only [wValue, hyt, Bool.false_eq_true, ↓reduceIte, hfv,
          lookup_append_single_ne _ _ _ _ (by omega : w.next + 2 + 2 ≠ w.next),
          hvalnone _ (by omega : w.next ≤ w.next + 2 + 2), (hbase (w.next + 2 + 2) (by omega)).2])
      hqL (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by
        simp only [wNode, hntake _ (Nat.le_refl _), Bool.false_eq_true, ↓reduceIte,
          hnodenone _ (Nat.le_refl _), (hbase _ (Nat.le_refl _)).1])
      hLroot.symm (by omega) (by omega) hrq' hsegL
      (keyWf_last_notin (pre0 ++ [k1]) cv (by rw [← hkey']; exact hkey))
      (fun key' x n' hk' h1 h2 h3 h4 => by rw [← hkey']; exact huniq key' x n' hk' h1 h2 h3 h4)
      hwf
      (fun x xn c' hx hxn hz => htreeK x xn c' L hx hxn hz (by simp [hNL]) q qn k1 hrq' hq
        (by rw [KNode.liveAt_of_times qn c.i hqt]; exact hk1))
      (hnotq q hvisq)
      (fun x xn cc z hx hxn hz => by
        have := hfr x xn cc z hx hxn hz
        exact ⟨this.1, this.2.2, this.2.1⟩)
    intro key' hkey2
    unfold wGet
    rw [hftop, hres key' hkey2, ← hkey']
    simp only [Op.key, Op.value]
    rfl

end SIS.Tree
