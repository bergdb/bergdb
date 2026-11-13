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

/-- After a space split of the space root L, a leaf, every key reads what it
read but the put's key [cv], which reads the put's value. The new root R has
the klongs (0, F) and (sc, S) to the halves of L's last version with the put's
klong to the new value v. -/
theorem getFromR_rootSpaceSplit (N N2 : NodeId → Option KNode) (V V2 : NodeId → Option Nat)
    (i : Time) (fuel : Nat) (hfuel : 2 ≤ fuel) (L F S R v : NodeId) (n : KNode) (cv h : Nat)
    (hNL : N L = some n) (hnl : n.leaf = true) (hnwf : klongsWf n.ks = true)
    (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ i) (hlive : n.live ≠ [])
    (hN2R : N2 R = some ⟨false, newKlongs i
      [(0, F), ((halves n.leaf i (n.lastVersion i) [(cv, v)]).2.2, S)]⟩)
    (hN2F : N2 F = some (halves n.leaf i (n.lastVersion i) [(cv, v)]).1)
    (hN2S : N2 S = some (halves n.leaf i (n.lastVersion i) [(cv, v)]).2.1)
    (hN2 : ∀ x, x ≠ L → x ≠ F → x ≠ S → x ≠ R → N2 x = N x)
    (hV2v : V2 v = some h) (hV2 : ∀ a, a ≠ v → V2 a = V a)
    (hvL : v ≠ L) (hvF : v ≠ F) (hvS : v ≠ S) (hvR : v ≠ R) (hNv : N v = none)
    (huniq : ∀ key' x m', keyWf key' = true → (x, cv) ∈ fromVisits N i fuel key' L →
      (x, cv) ∈ eqVisits N i cv fuel L → N x = some m' → m'.leaf = true → key' = [cv])
    (hwf : ∀ x xn, ReachS N i L x → N x = some xn → klongsWf xn.ks = true)
    (hfr : ∀ x xn c z, ReachS N i L x → N x = some xn → (c, z) ∈ xn.liveAt i →
      z ≠ v ∧ z ≠ F ∧ z ≠ S ∧ z ≠ R ∧ z ≠ L) :
    ∀ key', keyWf key' = true → getFromR N2 V2 i fuel key' R =
      if [cv] == key' then some h else getFromR N V i fuel key' L := by
  let m := n.add i (.key cv v)
  have hml : m.leaf = true := by simp only [m, KNode.add_leaf]; exact hnl
  have hmwf : klongsWf m.ks = true := KNode.add_key_wf n i cv v hnwf
  have hmt : ∀ s, Klong.time s ∈ m.ks → s ≤ i := KNode.add_times n i (.key cv v) (fun s h => by cases h) hnt
  have hmlook : ∀ c, m.live.lookup c = if cv == c then some v else n.live.lookup c :=
    fun c => KNode.add_key_live_lookup_of_wf n i cv c v hnwf
  let Nm : NodeId → Option KNode := fun x => if x = L then some m else N x
  have hNmL : Nm L = some m := by simp [Nm]
  have hNm : ∀ x, x ≠ L → Nm x = N x := fun x hx => by simp [Nm, hx]
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
  have hreach := reach_change N i L L v n m hNL hmem hNv hvL
  have hwfm : ∀ x xn, ReachS Nm i L x → Nm x = some xn → klongsWf xn.ks = true := by
    intro x xn hx hn
    by_cases hxL : x = L
    · subst hxL; rw [hNmL] at hn; cases hn; exact hmwf
    · rw [hNm x hxL] at hn
      rcases hreach x hx with hx' | hxv
      · exact hwf x xn hx' hn
      · subst hxv; rw [hNv] at hn; cases hn
  -- the links of the nodes Nm reaches avoid L and the new nodes
  let D : NodeId → Prop := fun z => z = L ∨ z = F ∨ z = S ∨ z = R
  have hlinks : ∀ x xn c z, ReachS Nm i L x → Nm x = some xn → (c, z) ∈ xn.liveAt i → ¬ D z := by
    intro x xn c z hx hn hz
    have hfr' : ∀ x' xn', ReachS N i L x' → N x' = some xn' → (c, z) ∈ xn'.liveAt i → ¬ D z := by
      intro x' xn' hx' hn' hz' hD
      obtain ⟨_, h1, h2, h3, h4⟩ := hfr x' xn' c z hx' hn' hz'
      rcases hD with h | h | h | h
      · exact h4 h
      · exact h1 h
      · exact h2 h
      · exact h3 h
    by_cases hxL : x = L
    · subst hxL; rw [hNmL] at hn; cases hn
      rcases hmem c z hz with h1 | h1
      · exact hfr' x n ReachS.root hNL h1
      · subst h1
        rintro (h | h | h | h)
        · exact hvL h
        · exact hvF h
        · exact hvS h
        · exact hvR h
    · rw [hNm x hxL] at hn
      rcases hreach x hx with hx' | hxv
      · exact hfr' x xn hx' hn hz
      · subst hxv; rw [hNv] at hn; cases hn
  have hsame : ∀ x, ReachS Nm i L x → ¬ D x → N2 x = Nm x := by
    intro x _ hD
    have h1 : x ≠ L := fun h => hD (Or.inl h)
    have h2 : x ≠ F := fun h => hD (Or.inr (Or.inl h))
    have h3 : x ≠ S := fun h => hD (Or.inr (Or.inr (Or.inl h)))
    have h4 : x ≠ R := fun h => hD (Or.inr (Or.inr (Or.inr h)))
    rw [hN2 x h1 h2 h3 h4, hNm x h1]
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
  generalize hout : halves true i ⟨true, newKlongs i n.live⟩ [(cv, v)] = out at hN2R hN2F hN2S hwfh hshape
  obtain ⟨f, s, sc⟩ := out
  simp only at hN2R hN2F hN2S hwfh
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
  -- the first segment's descent from the new root reads as L with the put
  have hfirst : ∀ c, getEqR N2 i c fuel R = getEqR Nm i c fuel L := by
    intro c
    obtain ⟨f2, hf2⟩ : ∃ f2, fuel = f2 + 2 := ⟨fuel - 2, by omega⟩
    rw [hf2]
    have hsr := KNode.rootPair_searchLte i F S sc c
    simp only [getEqR, hN2R, hNmL, hml, Bool.false_eq_true, ↓reduceIte]
    cases hs : (⟨false, newKlongs i [(0, F), (sc, S)]⟩ : KNode).searchLte i ↑c with
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
  have hsim : ∀ key', getFromR N2 V2 i fuel key' R = getFromR Nm V2 i fuel key' L := by
    intro key'
    cases key' with
    | nil => rfl
    | cons c rest =>
      cases rest with
      | nil => simp only [getFromR]; rw [hfirst c]
      | cons d rest' =>
        simp only [getFromR]
        rw [hfirst c]
        cases hg : getEqR Nm i c fuel L with
        | none => rfl
        | some z =>
          simp only
          have hz : ReachS Nm i L z := getEqR_reach Nm i L c hwfm fuel L z ReachS.root hg
          obtain ⟨x, xn, cz, hx, hxn, _, hzm⟩ := getEqR_leaf_link Nm i L c hwfm fuel L z ReachS.root hg
          have hzD := hlinks x xn cz z hx hxn hzm
          rw [hsame z hz hzD]
          split
          · exact getFromR_avoid Nm N2 V2 i fuel L D hwfm hsame hlinks _ z hz hzD
          · rfl
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
  have hA := getFromR_leaf_change_seg N Nm V V2 i fuel (by omega) L [] cv L L n m
    (fun x hx => (hNm x hx).symm) hNL hNmL hnl hml hs rfl (by simp) hvisL huniq
    (fun key' x c' m' y' _ hx hm' hml' hs' => by
      have hrx : ReachS N i L x := fromVisits_reach N i fuel L hwf key' L x c' ReachS.root hx
      have hy' : y' ≠ v := by
        cases hfd : m'.searchEq i c' with
        | none => rw [hfd] at hs'; cases hs'
        | some fd =>
          rw [hfd] at hs'
          simp only [Option.map_some, Option.some.injEq] at hs'
          subst hs'
          exact (hfr x m' c' fd.y hrx hm' (KNode.searchEq_mem m' i c' fd (hwf x m' hrx hm') hfd)).1
      exact (hV2 y' hy').symm)
  intro key' hkey'
  rw [hsim key']
  by_cases hk : [cv] = key'
  · subst hk
    simp only [beq_self_eq_true, ↓reduceIte]
    have := hA.1
    simp only [List.nil_append] at this
    rw [this, KNode.searchEq_live m i hmwf hmt, hmlook]
    simp [hV2v]
  · have hk' : ([cv] == key') = false := by simpa using hk
    simp only [hk', Bool.false_eq_true, ↓reduceIte]
    exact hA.2 key' hkey' (fun h' => hk (by simpa using h'.symm))

/-! ## The writer's space split of the space root -/

/-- The state after a space split of the space root L, a leaf that existed
before the transaction: the halves at the next two ids, the new root at the id
after them, which the super root names; L keeps its klongs before the
transaction. -/
def RootSpaceSplitAfter (c : Ctx) (w w' : W) (L : NodeId) (n : KNode) (cv v : Nat) : Prop :=
  w'.taken = w.taken ∧ w'.top.rootKey = w.next + 2 + 2 ∧ w'.vals = w.vals ∧
    ∀ x, w'.nodes.lookup x =
      if x = L then some (n.toPrev (c.i - 1))
      else if x = w.next then some (halves n.leaf c.i (n.lastVersion c.i) [(cv, v)]).1
      else if x = w.next + 2 then some (halves n.leaf c.i (n.lastVersion c.i) [(cv, v)]).2.1
      else if x = w.next + 2 + 2 then some ⟨false, [.time c.i, .key 0 w.next,
        .key (halves n.leaf c.i (n.lastVersion c.i) [(cv, v)]).2.2 (w.next + 2)]⟩
      else w.nodes.lookup x

theorem writerWP_handleFullWith_rootSpaceSplit (up : NodeId → List (Nat × NodeId) → M Unit)
    (L : NodeId) (n : KNode) (cv v : Nat) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hfirst : n.firstTime ≠ some c.i)
    (hsplit : c.p.splitAbove < (n.lastVersion c.i).size) (hLn : L < w.next) :
    WriterWP (handleFullWith up 0 L [(cv, v)] (n.lastVersion c.i) false) c w
      (fun _ w' => RootSpaceSplitAfter c w w' L n cv v) := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w hlk]
  refine writerWP_ghOf_cached L n c w hlk _ (fun gh => ?_)
  have hnew : (n.firstTime == some c.i) = false := by simpa using hfirst
  have hsz : decide ((n.lastVersion c.i).size > c.p.splitAbove) = true := by
    simp only [decide_eq_true_eq, gt_iff_lt]; exact hsplit
  simp only [hnew, parentAt, writerWP_pure, hsz, Bool.not_false, Bool.true_and,
    Bool.false_eq_true, ↓reduceIte]
  have hL1 : L ≠ w.next := by omega
  have hL2 : L ≠ w.next + 2 := by omega
  have hL3 : L ≠ w.next + 2 + 2 := by omega
  simp only [newKey, fresh, setMadeFor, note, putNode, newSuperRoot, writerWP_bind,
    writerWP_modify, writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
  split <;>
  · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
    split <;>
    · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
      split <;>
      · simp only [writerWP_bind, writerWP_modify, writerWP_pure, writerWP_get, writerWP_set]
        refine (writerWP_getNode_known L n c _ ?_ _).mpr ?_
        · simp only [lookup_upsert, List.lookup_append, hL1, hL2, hL3, ↓reduceIte, hlk]
          rfl
        refine ⟨rfl, rfl, rfl, ?_⟩
        intro x
        simp only [lookup_upsert, List.lookup_append]
        by_cases hxL : x = L
        · subst hxL; simp
        · simp only [hxL, ↓reduceIte]
          by_cases h3 : x = w.next + 2 + 2
          · subst h3
            simp [show w.next + 2 + 2 ≠ w.next by omega]
          · simp only [h3, ↓reduceIte]
            by_cases h2 : x = w.next + 2
            · subst h2; simp
            · simp only [h2, ↓reduceIte]
              by_cases h1 : x = w.next
              · subst h1; simp
              · simp only [h1, ↓reduceIte]
                cases h : w.nodes.lookup x with
                | some m => rfl
                | none =>
                  show (((none : Option KNode).or ([(w.next, { leaf := n.leaf, ks := [] })].lookup x)).or
                    ([(w.next + 2, { leaf := n.leaf, ks := [] })].lookup x)).or
                    ([(w.next + 2 + 2, { leaf := false, ks := [] })].lookup x) = none
                  rw [lookup_cons_ne _ _ _ _ h1, lookup_cons_ne _ _ _ _ h2, lookup_cons_ne _ _ _ _ h3]; rfl

theorem writerWP_appendKlongs_rootSpaceSplit (L : NodeId) (n : KNode) (cv v : Nat) (c : Ctx)
    (w : W) (hlk : w.nodes.lookup L = some n) (hfirst : n.firstTime ≠ some c.i)
    (hfull : c.p.M ≤ n.size + 1)
    (hsplit : c.p.splitAbove < (n.lastVersion c.i).size) (hLn : L < w.next) :
    WriterWP (appendKlongs 0 L [(cv, v)]) c w
      (fun _ w' => RootSpaceSplitAfter c w w' L n cv v) := by
  rw [appendKlongs_step_dead]
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w hlk]
  have h1 : n.size + [(cv, v)].length + 1 > c.p.M := by simp; omega
  simp only [h1, ↓reduceIte]
  exact writerWP_handleFullWith_rootSpaceSplit _ L n cv v c w hlk hfirst hsplit hLn

/-- A put of a key of one segment when the space root is a leaf that existed
before the transaction, full by its size, with more than h klongs in its last
version: the space split of the root changes the reading by the put alone. The
premises are those of the other split rules: ids below the next one, the root
not taken back, the reachable nodes' klongs well formed, no reachable klong to
the root or to the fresh ids, and the uniqueness of the key's search at the
root. -/
theorem writerWP_put_rootSpaceSplit (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (cv h : Nat) (w : W) (n : KNode)
    (hroot : wNode c.p base w w.top.rootKey = some n) (hnl : n.leaf = true)
    (hrt : w.taken.contains w.top.rootKey = false)
    (hleaf : klongsWf n.ks = true ∧ (∀ s, Klong.time s ∈ n.ks → s ≤ c.i) ∧
      c.p.M ≤ n.size + 1 ∧ n.firstTime ≠ some c.i ∧ c.p.splitAbove < (n.lastVersion c.i).size ∧
      n.live ≠ [])
    (hids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
      (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next) ∧
      (∀ q ∈ w.vals, q.1 < w.next) ∧ w.top.rootKey < w.next)
    (hbase : knodeOf c.p base w.next = none)
    (huniq : ∀ key' x n', keyWf key' = true →
      (x, cv) ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
      (x, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel w.top.rootKey →
      wNode c.p base w x = some n' → n'.leaf = true → key' = [cv])
    (hwf : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → klongsWf xn.ks = true)
    (hfr : ∀ x xn cc z, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → (cc, z) ∈ xn.liveAt c.i →
        z ≠ w.next ∧ z ≠ w.next + 2 ∧ z ≠ w.next + 2 + 2 ∧ z ≠ w.next + 2 + 2 + 2 ∧
        z ≠ w.top.rootKey) :
    WriterWP (putKv (.put [cv] h)) c w (fun _ w' => ∀ key', keyWf key' = true →
      wGet c.p c.i base w' key' =
        if Op.key (.put [cv] h) == key' then Op.value (.put [cv] h)
        else wGet c.p c.i base w key') := by
  obtain ⟨hidn, hidv, hidt, hidvals, hidr⟩ := hids
  obtain ⟨hnwf, htimes, hfull, hfirst, hsplit, hlive⟩ := hleaf
  have hfuel : 2 ≤ c.p.fuel := by unfold Params.fuel; omega
  unfold putKv pathClear findRoot pathAdd
  wpSimplify
  generalize hw2 : ({ ({ w with path := [] } : W) with
    path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w2
  have hr02 : ReadsAs c.p base w w2 := by subst hw2; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hw2n : w2.nodes = w.nodes := by subst hw2; rfl
  have hp2 : w2.path = [(none, w.top.rootKey)] := by subst hw2; rfl
  rw [putSegs.eq_2]
  unfold setValue
  wpSimplify
  have hev : eqVisits (wNode c.p base w2) c.i cv c.p.fuel w.top.rootKey = [(w.top.rootKey, cv)] := by
    obtain ⟨f2, hf2⟩ : ∃ f2, c.p.fuel = f2 + 1 := ⟨c.p.fuel - 1, by omega⟩
    rw [hf2, hr02.1]
    simp [eqVisits, hroot, hnl]
  have ht2 : ∀ q ∈ eqVisits (wNode c.p base w2) c.i cv c.p.fuel w.top.rootKey,
      w2.taken.contains q.1 = false := by
    rw [hev, hr02.2.2.1]
    intro q hq
    simp only [List.mem_singleton] at hq
    subst hq
    exact hrt
  refine writerWP_mono (writerWP_and
    (writerWP_descendLte_path cv c base hvc c.p.fuel w.top.rootKey w2 ht2 (by rw [hp2]; rfl))
    (writerWP_descendLte_cache cv c base hvc c.p.fuel w.top.rootKey w2 ht2)) ?_
  intro L w3 ⟨⟨hr23, n', hn', hnl', hlk3, hvisL, _, hdp⟩, ⟨_, hsrc3, _⟩⟩
  rw [hr02.1] at hn' hvisL
  have hr03 := ReadsAs.trans _ _ _ _ _ hr02 hr23
  have hnext3 : w3.next = w.next := hr03.2.2.2.2
  -- the descent stops at the root, a leaf
  obtain ⟨hLr, hp3⟩ : L = w.top.rootKey ∧ w3.path = w2.path := by
    rcases hdp with h | ⟨pre', q, k1, qn, fd, _, _, hq, hql, _, _, _, hqv⟩
    · exact h
    · rw [hev] at hqv
      simp only [List.mem_singleton, Prod.mk.injEq] at hqv
      rw [hqv.1, hr02.1, hroot] at hq
      cases hq
      rw [hnl] at hql
      cases hql
  subst hLr
  rw [hroot] at hn'
  cases hn'
  unfold newValue fresh
  wpSimplify
  rw [writerWP_getNode_known _ n c _ (by simpa using hlk3)]
  have hcond : (decide (n.size + 1 < c.p.M) && !deadOver c.p (n.add c.i (.key cv w3.next))) = false := by
    have : ¬ n.size + 1 < c.p.M := by omega
    simp [this]
  simp only [hcond, Bool.false_eq_true, ↓reduceIte, pathSize, writerWP_bind, writerWP_get,
    writerWP_pure]
  have hsrcw3 : ∀ z, (w3.nodes.lookup z).isSome = true → z < w.next := by
    intro z hz
    rcases hsrc3 z hz with h1 | h1
    · rw [hw2n] at h1; exact hidn z h1
    · exact hidv z h1
  have hlen : w3.path.length - 1 = 0 := by rw [hp3, hp2]; rfl
  rw [hlen]
  refine writerWP_mono (writerWP_appendKlongs_rootSpaceSplit w.top.rootKey n cv w3.next c _
    (by simpa using hlk3) hfirst hfull hsplit (by simp only; omega)) ?_
  intro _ wf hRS
  obtain ⟨hft, hftop, hfv, hfn⟩ := hRS
  simp only at hft hftop hfv hfn
  rw [hr03.2.2.1] at hft
  rw [hr03.2.2.2.1, hnext3] at hfv
  rw [hnext3] at hfn hftop
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
  have hres := getFromR_rootSpaceSplit (wNode c.p base w) (wNode c.p base wf) (wValue base w)
    (wValue base wf) c.i c.p.fuel hfuel w.top.rootKey (w.next + 2) (w.next + 2 + 2)
    (w.next + 2 + 2 + 2) w.next n cv h hroot hnl hnwf htimes hlive
    (by
      have hyt : wf.taken.contains (w.next + 2 + 2 + 2) = false := by
        rw [hft]; exact hntake _ (by omega)
      simp only [wNode, hyt, Bool.false_eq_true, ↓reduceIte, hfn,
        show w.next + 2 + 2 + 2 ≠ w.top.rootKey by omega, show w.next + 2 + 2 + 2 ≠ w.next + 2 by omega,
        show w.next + 2 + 2 + 2 ≠ w.next + 2 + 2 by omega]
      rfl)
    (by
      have hyt : wf.taken.contains (w.next + 2) = false := by rw [hft]; exact hntake _ (by omega)
      simp only [wNode, hyt, Bool.false_eq_true, ↓reduceIte, hfn,
        show w.next + 2 ≠ w.top.rootKey by omega])
    (by
      have hyt : wf.taken.contains (w.next + 2 + 2) = false := by
        rw [hft]; exact hntake _ (by omega)
      simp only [wNode, hyt, Bool.false_eq_true, ↓reduceIte, hfn,
        show w.next + 2 + 2 ≠ w.top.rootKey by omega, show w.next + 2 + 2 ≠ w.next + 2 by omega])
    (by
      intro x hxL hxF hxS hxR
      rw [← hr03.1]
      simp only [wNode, hft, hfn, hxL, hxF, hxS, hxR, ↓reduceIte, hr03.2.2.1])
    (by
      have hvt : wf.taken.contains w.next = false := by rw [hft]; exact hntake _ (Nat.le_refl _)
      simp only [wValue, hvt, Bool.false_eq_true, ↓reduceIte, hfv,
        lookup_append_single_self _ _ _ (hvalnone _ (Nat.le_refl _))])
    (by
      intro a ha
      simp only [wValue, hft, hfv, lookup_append_single_ne _ _ _ _ ha])
    (by omega) (by omega) (by omega) (by omega)
    (by
      simp only [wNode, hntake _ (Nat.le_refl _), Bool.false_eq_true, ↓reduceIte,
        hnodenone _ (Nat.le_refl _), hbase])
    huniq hwf hfr
  intro key' hkey'
  unfold wGet
  rw [hftop, hres key' hkey']
  simp only [Op.key, Op.value]
  rfl

/-! ## The time split of the space root -/

theorem writerWP_handleFullWith_rootTimeSplit (up : NodeId → List (Nat × NodeId) → M Unit)
    (L : NodeId) (n : KNode) (cv v : Nat) (compact : Bool) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hfirst : n.firstTime ≠ some c.i)
    (hcs : (!compact && decide ((n.lastVersion c.i).size > c.p.splitAbove)) = false)
    (hLn : L < w.next) (hny : w.nodes.lookup w.next = none) :
    WriterWP (handleFullWith up 0 L [(cv, v)] (n.lastVersion c.i) compact) c w (fun _ w' =>
      ∃ l : KNode, l.leaf = n.leaf ∧ klongsWf l.ks = true ∧ (∀ s, Klong.time s ∈ l.ks → s ≤ c.i) ∧
        (∀ q', l.live.lookup q' = [(cv, v)].foldl (pairLookupStep q') (n.live.lookup q')) ∧
        w'.taken = w.taken ∧ w'.top.rootKey = w.next ∧ w'.vals = w.vals ∧
        ∀ x, w'.nodes.lookup x =
          if x = L then some (n.toPrev (c.i - 1))
          else if x = w.next then some ⟨n.leaf, l.ks⟩ else w.nodes.lookup x) := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w hlk]
  refine writerWP_ghOf_cached L n c w hlk _ (fun gh => ?_)
  have hnew : (n.firstTime == some c.i) = false := by simpa using hfirst
  simp only [hnew, parentAt, writerWP_pure, hcs, Bool.false_eq_true, ↓reduceIte, Bool.not_false]
  have hL1 : L ≠ w.next := by omega
  split <;>
  · simp only [note, writerWP_bind, writerWP_modify, writerWP_pure]
    refine writerWP_mono (writerWP_replaceOrAdd_last n [(cv, v)] c _) ?_
    rintro l w1 ⟨hw1, hl_leaf, hl_wf, hl_times, hl_look⟩
    subst w1
    split <;>
    · simp only [newKey, fresh, setMadeFor, note, newSuperRoot, writerWP_bind, writerWP_modify,
        writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
      split <;>
      · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
        split <;>
        · simp only [writerWP_bind, writerWP_modify, writerWP_pure, writerWP_get, writerWP_set]
          refine (writerWP_getNode_known L n c _ ?_ _).mpr ?_
          · simp only [List.lookup_append, hlk]; rfl
          rw [putNode, writerWP_modify]
          refine ⟨l, hl_leaf, hl_wf, hl_times, hl_look, rfl, rfl, rfl, ?_⟩
          intro x
          show (upsert _ L _).lookup x = _
          rw [lookup_upsert]
          by_cases hxL : x = L
          · simp [hxL]
          · simp only [hxL, ↓reduceIte, List.lookup_append]
            by_cases hxy : x = w.next
            · subst hxy; rw [hny]; simp [List.lookup]
            · simp only [hxy, ↓reduceIte]
              cases h : w.nodes.lookup x with
              | some m => rfl
              | none =>
                show (none : Option KNode).or ([(w.next, { leaf := n.leaf, ks := l.ks })].lookup x) = none
                rw [lookup_cons_ne _ _ _ _ hxy]; rfl

/-- After a time split of the space root L, a leaf, every key reads what it
read but the put's key [cv], which reads the put's value. The new root Y holds
L's last version with the put's klong to the new value v. -/
theorem getFromR_rootTimeSplit (N N2 : NodeId → Option KNode) (V V2 : NodeId → Option Nat)
    (i : Time) (fuel : Nat) (hfuel : 1 ≤ fuel) (L Y v : NodeId) (n ln : KNode) (cv h : Nat)
    (hNL : N L = some n) (hnl : n.leaf = true) (hnwf : klongsWf n.ks = true)
    (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ i)
    (hN2Y : N2 Y = some ln) (hlnl : ln.leaf = true) (hlnwf : klongsWf ln.ks = true)
    (hlnt : ∀ s, Klong.time s ∈ ln.ks → s ≤ i)
    (hlnlook : ∀ q', ln.live.lookup q' = if cv == q' then some v else n.live.lookup q')
    (hN2 : ∀ x, x ≠ L → x ≠ Y → N2 x = N x)
    (hV2v : V2 v = some h) (hV2 : ∀ a, a ≠ v → V2 a = V a)
    (hvL : v ≠ L) (hvY : v ≠ Y) (hNv : N v = none)
    (huniq : ∀ key' x m', keyWf key' = true → (x, cv) ∈ fromVisits N i fuel key' L →
      (x, cv) ∈ eqVisits N i cv fuel L → N x = some m' → m'.leaf = true → key' = [cv])
    (hwf : ∀ x xn, ReachS N i L x → N x = some xn → klongsWf xn.ks = true)
    (hfr : ∀ x xn c z, ReachS N i L x → N x = some xn → (c, z) ∈ xn.liveAt i →
      z ≠ v ∧ z ≠ Y ∧ z ≠ L) :
    ∀ key', keyWf key' = true → getFromR N2 V2 i fuel key' Y =
      if [cv] == key' then some h else getFromR N V i fuel key' L := by
  let m := n.add i (.key cv v)
  have hml : m.leaf = true := by simp only [m, KNode.add_leaf]; exact hnl
  have hmwf : klongsWf m.ks = true := KNode.add_key_wf n i cv v hnwf
  have hmt : ∀ s, Klong.time s ∈ m.ks → s ≤ i := KNode.add_times n i (.key cv v) (fun s h => by cases h) hnt
  have hmlook : ∀ c, m.live.lookup c = if cv == c then some v else n.live.lookup c :=
    fun c => KNode.add_key_live_lookup_of_wf n i cv c v hnwf
  let Nm : NodeId → Option KNode := fun x => if x = L then some m else N x
  have hNmL : Nm L = some m := by simp [Nm]
  have hNm : ∀ x, x ≠ L → Nm x = N x := fun x hx => by simp [Nm, hx]
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
  have hreach := reach_change N i L L v n m hNL hmem hNv hvL
  have hwfm : ∀ x xn, ReachS Nm i L x → Nm x = some xn → klongsWf xn.ks = true := by
    intro x xn hx hn
    by_cases hxL : x = L
    · subst hxL; rw [hNmL] at hn; cases hn; exact hmwf
    · rw [hNm x hxL] at hn
      rcases hreach x hx with hx' | hxv
      · exact hwf x xn hx' hn
      · subst hxv; rw [hNv] at hn; cases hn
  -- the links of the nodes Nm reaches avoid L and the new nodes
  let D : NodeId → Prop := fun z => z = L ∨ z = Y
  have hlinks : ∀ x xn c z, ReachS Nm i L x → Nm x = some xn → (c, z) ∈ xn.liveAt i → ¬ D z := by
    intro x xn c z hx hn hz
    have hfr' : ∀ x' xn', ReachS N i L x' → N x' = some xn' → (c, z) ∈ xn'.liveAt i → ¬ D z := by
      intro x' xn' hx' hn' hz' hD
      obtain ⟨_, h1, h2⟩ := hfr x' xn' c z hx' hn' hz'
      rcases hD with h | h
      · exact h2 h
      · exact h1 h
    by_cases hxL : x = L
    · subst hxL; rw [hNmL] at hn; cases hn
      rcases hmem c z hz with h1 | h1
      · exact hfr' x n ReachS.root hNL h1
      · subst h1
        rintro (h | h)
        · exact hvL h
        · exact hvY h
    · rw [hNm x hxL] at hn
      rcases hreach x hx with hx' | hxv
      · exact hfr' x xn hx' hn hz
      · subst hxv; rw [hNv] at hn; cases hn
  have hsame : ∀ x, ReachS Nm i L x → ¬ D x → N2 x = Nm x := by
    intro x _ hD
    have h1 : x ≠ L := fun h => hD (Or.inl h)
    have h2 : x ≠ Y := fun h => hD (Or.inr h)
    rw [hN2 x h1 h2, hNm x h1]
  have hfirst : ∀ c, getEqR N2 i c fuel Y = getEqR Nm i c fuel L := by
    intro c
    obtain ⟨f2, hf2⟩ : ∃ f2, fuel = f2 + 1 := ⟨fuel - 1, by omega⟩
    rw [hf2]
    simp only [getEqR, hN2Y, hNmL, hml, hlnl, ↓reduceIte]
    rw [KNode.searchEq_live ln i hlnwf hlnt, KNode.searchEq_live m i hmwf hmt, hlnlook, hmlook]
  have hsim : ∀ key', getFromR N2 V2 i fuel key' Y = getFromR Nm V2 i fuel key' L := by
    intro key'
    cases key' with
    | nil => rfl
    | cons c rest =>
      cases rest with
      | nil => simp only [getFromR]; rw [hfirst c]
      | cons d rest' =>
        simp only [getFromR]
        rw [hfirst c]
        cases hg : getEqR Nm i c fuel L with
        | none => rfl
        | some z =>
          simp only
          have hz : ReachS Nm i L z := getEqR_reach Nm i L c hwfm fuel L z ReachS.root hg
          obtain ⟨x, xn, cz, hx, hxn, _, hzm⟩ := getEqR_leaf_link Nm i L c hwfm fuel L z ReachS.root hg
          have hzD := hlinks x xn cz z hx hxn hzm
          rw [hsame z hz hzD]
          split
          · exact getFromR_avoid Nm N2 V2 i fuel L D hwfm hsame hlinks _ z hz hzD
          · rfl
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
  have hA := getFromR_leaf_change_seg N Nm V V2 i fuel (by omega) L [] cv L L n m
    (fun x hx => (hNm x hx).symm) hNL hNmL hnl hml hs rfl (by simp) hvisL huniq
    (fun key' x c' m' y' _ hx hm' hml' hs' => by
      have hrx : ReachS N i L x := fromVisits_reach N i fuel L hwf key' L x c' ReachS.root hx
      have hy' : y' ≠ v := by
        cases hfd : m'.searchEq i c' with
        | none => rw [hfd] at hs'; cases hs'
        | some fd =>
          rw [hfd] at hs'
          simp only [Option.map_some, Option.some.injEq] at hs'
          subst hs'
          exact (hfr x m' c' fd.y hrx hm' (KNode.searchEq_mem m' i c' fd (hwf x m' hrx hm') hfd)).1
      exact (hV2 y' hy').symm)
  intro key' hkey'
  rw [hsim key']
  by_cases hk : [cv] = key'
  · subst hk
    simp only [beq_self_eq_true, ↓reduceIte]
    have := hA.1
    simp only [List.nil_append] at this
    rw [this, KNode.searchEq_live m i hmwf hmt, hmlook]
    simp [hV2v]
  · have hk' : ([cv] == key') = false := by simpa using hk
    simp only [hk', Bool.false_eq_true, ↓reduceIte]
    exact hA.2 key' hkey' (fun h' => hk (by simpa using h'.symm))

theorem writerWP_appendKlongs_rootTimeSplit (L : NodeId) (n : KNode) (cv v : Nat) (c : Ctx)
    (w : W) (hlk : w.nodes.lookup L = some n) (hfirst : n.firstTime ≠ some c.i)
    (hfull : ¬ (n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv v)) = false))
    (hsplit : c.p.M ≤ n.size + 1 → (n.lastVersion c.i).size ≤ c.p.splitAbove) (hLn : L < w.next)
    (hny : w.nodes.lookup w.next = none) :
    WriterWP (appendKlongs 0 L [(cv, v)]) c w (fun _ w' =>
      ∃ l : KNode, l.leaf = n.leaf ∧ klongsWf l.ks = true ∧ (∀ s, Klong.time s ∈ l.ks → s ≤ c.i) ∧
        (∀ q', l.live.lookup q' = [(cv, v)].foldl (pairLookupStep q') (n.live.lookup q')) ∧
        w'.taken = w.taken ∧ w'.top.rootKey = w.next ∧ w'.vals = w.vals ∧
        ∀ x, w'.nodes.lookup x =
          if x = L then some (n.toPrev (c.i - 1))
          else if x = w.next then some ⟨n.leaf, l.ks⟩ else w.nodes.lookup x) := by
  rw [appendKlongs_step_dead]
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w hlk]
  split
  · rename_i hsize
    exact writerWP_handleFullWith_rootTimeSplit _ L n cv v false c w hlk hfirst
      (by
        have h1 : c.p.M ≤ n.size + 1 := by simp at hsize; omega
        simp only [Bool.not_false, Bool.true_and, decide_eq_false_iff_not, gt_iff_lt, Nat.not_lt]
        exact hsplit h1) hLn hny
  · rename_i hsize
    have hlt : n.size + 1 < c.p.M := by simp at hsize; omega
    have hd : deadOver c.p (n.add c.i (.key cv v)) = true := by
      cases h : deadOver c.p (n.add c.i (.key cv v)) with
      | true => rfl
      | false => exact absurd ⟨hlt, h⟩ hfull
    simp only [List.foldl_cons, List.foldl_nil, hd, ↓reduceIte]
    exact writerWP_handleFullWith_rootTimeSplit _ L n cv v true c w hlk hfirst (by simp) hLn hny

/-- A put of a key of one segment when the space root is a full leaf that existed
before the transaction, with at most h klongs in its last version or full by
its dead klongs only: the time split of the root changes the reading by the put
alone. The
premises are those of the other split rules: ids below the next one, the root
not taken back, the reachable nodes' klongs well formed, no reachable klong to
the root or to the fresh ids, and the uniqueness of the key's search at the
root. -/
theorem writerWP_put_rootTimeSplit (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (cv h : Nat) (w : W) (n : KNode)
    (hroot : wNode c.p base w w.top.rootKey = some n) (hnl : n.leaf = true)
    (hrt : w.taken.contains w.top.rootKey = false)
    (hleaf : klongsWf n.ks = true ∧ (∀ s, Klong.time s ∈ n.ks → s ≤ c.i) ∧
      ¬ (n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv w.next)) = false) ∧
      n.firstTime ≠ some c.i ∧ (c.p.M ≤ n.size + 1 → (n.lastVersion c.i).size ≤ c.p.splitAbove))
    (hids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
      (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next) ∧
      (∀ q ∈ w.vals, q.1 < w.next) ∧ w.top.rootKey < w.next)
    (hbase : knodeOf c.p base w.next = none)
    (huniq : ∀ key' x n', keyWf key' = true →
      (x, cv) ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
      (x, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel w.top.rootKey →
      wNode c.p base w x = some n' → n'.leaf = true → key' = [cv])
    (hwf : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → klongsWf xn.ks = true)
    (hfr : ∀ x xn cc z, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → (cc, z) ∈ xn.liveAt c.i →
        z ≠ w.next ∧ z ≠ w.next + 2 ∧ z ≠ w.top.rootKey) :
    WriterWP (putKv (.put [cv] h)) c w (fun _ w' => ∀ key', keyWf key' = true →
      wGet c.p c.i base w' key' =
        if Op.key (.put [cv] h) == key' then Op.value (.put [cv] h)
        else wGet c.p c.i base w key') := by
  obtain ⟨hidn, hidv, hidt, hidvals, hidr⟩ := hids
  obtain ⟨hnwf, htimes, hfull, hfirst, hsplit⟩ := hleaf
  have hfuel : 2 ≤ c.p.fuel := by unfold Params.fuel; omega
  unfold putKv pathClear findRoot pathAdd
  wpSimplify
  generalize hw2 : ({ ({ w with path := [] } : W) with
    path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w2
  have hr02 : ReadsAs c.p base w w2 := by subst hw2; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hw2n : w2.nodes = w.nodes := by subst hw2; rfl
  have hp2 : w2.path = [(none, w.top.rootKey)] := by subst hw2; rfl
  rw [putSegs.eq_2]
  unfold setValue
  wpSimplify
  have hev : eqVisits (wNode c.p base w2) c.i cv c.p.fuel w.top.rootKey = [(w.top.rootKey, cv)] := by
    obtain ⟨f2, hf2⟩ : ∃ f2, c.p.fuel = f2 + 1 := ⟨c.p.fuel - 1, by omega⟩
    rw [hf2, hr02.1]
    simp [eqVisits, hroot, hnl]
  have ht2 : ∀ q ∈ eqVisits (wNode c.p base w2) c.i cv c.p.fuel w.top.rootKey,
      w2.taken.contains q.1 = false := by
    rw [hev, hr02.2.2.1]
    intro q hq
    simp only [List.mem_singleton] at hq
    subst hq
    exact hrt
  refine writerWP_mono (writerWP_and
    (writerWP_descendLte_path cv c base hvc c.p.fuel w.top.rootKey w2 ht2 (by rw [hp2]; rfl))
    (writerWP_descendLte_cache cv c base hvc c.p.fuel w.top.rootKey w2 ht2)) ?_
  intro L w3 ⟨⟨hr23, n', hn', hnl', hlk3, hvisL, _, hdp⟩, ⟨_, hsrc3, _⟩⟩
  rw [hr02.1] at hn' hvisL
  have hr03 := ReadsAs.trans _ _ _ _ _ hr02 hr23
  have hnext3 : w3.next = w.next := hr03.2.2.2.2
  -- the descent stops at the root, a leaf
  obtain ⟨hLr, hp3⟩ : L = w.top.rootKey ∧ w3.path = w2.path := by
    rcases hdp with h | ⟨pre', q, k1, qn, fd, _, _, hq, hql, _, _, _, hqv⟩
    · exact h
    · rw [hev] at hqv
      simp only [List.mem_singleton, Prod.mk.injEq] at hqv
      rw [hqv.1, hr02.1, hroot] at hq
      cases hq
      rw [hnl] at hql
      cases hql
  subst hLr
  rw [hroot] at hn'
  cases hn'
  unfold newValue fresh
  wpSimplify
  rw [writerWP_getNode_known _ n c _ (by simpa using hlk3)]
  have hcond : (decide (n.size + 1 < c.p.M) && !deadOver c.p (n.add c.i (.key cv w3.next))) = false := by
    rw [hnext3]
    cases hd : deadOver c.p (n.add c.i (.key cv w.next)) with
    | true => simp
    | false =>
      have : ¬ n.size + 1 < c.p.M := fun hlt => hfull ⟨hlt, hd⟩
      simp [this]
  simp only [hcond, Bool.false_eq_true, ↓reduceIte, pathSize, writerWP_bind, writerWP_get,
    writerWP_pure]
  have hsrcw3 : ∀ z, (w3.nodes.lookup z).isSome = true → z < w.next := by
    intro z hz
    rcases hsrc3 z hz with h1 | h1
    · rw [hw2n] at h1; exact hidn z h1
    · exact hidv z h1
  have hlen : w3.path.length - 1 = 0 := by rw [hp3, hp2]; rfl
  rw [hlen]
  have hny : w3.nodes.lookup (w3.next + 2) = none := by
    cases h' : w3.nodes.lookup (w3.next + 2) with
    | none => rfl
    | some _ => have := hsrcw3 _ (by rw [h']; rfl); omega
  refine writerWP_mono (writerWP_appendKlongs_rootTimeSplit w.top.rootKey n cv w3.next c _
    (by simpa using hlk3) hfirst (by rw [hnext3]; exact hfull) hsplit (by simp only; omega)
    (by simpa using hny)) ?_
  intro _ wf ⟨l, hl_leaf, hl_wf, hl_times, hl_look, hft, hftop, hfv, hfn⟩
  simp only at hft hftop hfv hfn
  rw [hr03.2.2.1] at hft
  rw [hr03.2.2.2.1, hnext3] at hfv
  rw [hnext3] at hfn hftop hl_look
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
  have hres := getFromR_rootTimeSplit (wNode c.p base w) (wNode c.p base wf) (wValue base w)
    (wValue base wf) c.i c.p.fuel (by omega) w.top.rootKey (w.next + 2) w.next n ⟨n.leaf, l.ks⟩ cv h
    hroot hnl hnwf htimes
    (by
      have hyt : wf.taken.contains (w.next + 2) = false := by rw [hft]; exact hntake _ (by omega)
      simp only [wNode, hyt, Bool.false_eq_true, ↓reduceIte, hfn,
        show w.next + 2 ≠ w.top.rootKey by omega])
    hnl hl_wf hl_times
    (by
      have hm : ({ leaf := n.leaf, ks := l.ks } : KNode) = l := by
        cases l; simp only at hl_leaf ⊢; rw [hl_leaf]
      intro q'
      rw [hm, hl_look q']
      simp [pairLookupStep])
    (by
      intro x hxL hxY
      rw [← hr03.1]
      simp only [wNode, hft, hfn, hxL, hxY, ↓reduceIte, hr03.2.2.1])
    (by
      have hvt : wf.taken.contains w.next = false := by rw [hft]; exact hntake _ (Nat.le_refl _)
      simp only [wValue, hvt, Bool.false_eq_true, ↓reduceIte, hfv,
        lookup_append_single_self _ _ _ (hvalnone _ (Nat.le_refl _))])
    (by
      intro a ha
      simp only [wValue, hft, hfv, lookup_append_single_ne _ _ _ _ ha])
    (by omega) (by omega)
    (by
      simp only [wNode, hntake _ (Nat.le_refl _), Bool.false_eq_true, ↓reduceIte,
        hnodenone _ (Nat.le_refl _), hbase])
    huniq hwf hfr
  intro key' hkey'
  unfold wGet
  rw [hftop, hres key' hkey']
  simp only [Op.key, Op.value]
  rfl

end SIS.Tree
