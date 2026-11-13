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

end SIS.Tree
