import SIS.Tree.GetChain

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! The space split of an inner node (bergdb 024-12, TP10; the cascades): the
halves of an inner node's last version with a klong put find, for compare values
below the second half's first one, what the first half finds, and from it on,
what the second finds, the second half's first klong renamed to the empty key
(`halves_inner_searchLte`). -/

theorem halves_inner_searchLte (qn : KNode) (t : Time) (k1 : Nat) (Y : NodeId)
    (hql : qn.leaf = false) (hw : klongsWf qn.ks = true) (hqt : ∀ s, Klong.time s ∈ qn.ks → s ≤ t)
    (r : Nat × NodeId) (hr : (qn.live.drop (qn.live.length / 2)).head? = some r) (hsc : 0 < r.1) :
    let out := halves qn.leaf t (qn.lastVersion t) [(k1, Y)]
    out.2.2 = r.1 ∧ out.1.leaf = false ∧ out.2.1.leaf = false ∧
      klongsWf out.1.ks = true ∧ klongsWf out.2.1.ks = true ∧
      (∀ s, Klong.time s ∈ out.1.ks → s ≤ t) ∧ (∀ s, Klong.time s ∈ out.2.1.ks → s ≤ t) ∧
      (∀ c : Nat, c < r.1 → (out.1.searchLte t c).map (·.y) =
        ((qn.add t (.key k1 Y)).searchLte t c).map (·.y)) ∧
      (∀ c : Nat, r.1 ≤ c → (out.2.1.searchLte t c).map (·.y) =
        ((qn.add t (.key k1 Y)).searchLte t c).map (·.y)) := by
  intro out
  have hlv := KNode.lastVersion_eq_newKlongs qn t
  rw [hql] at hlv
  have hout : out = halves false t ⟨false, newKlongs t qn.live⟩ [(k1, Y)] := by
    simp only [out, hql, hlv]
  have hs : CvSorted qn.live := qn.live_order
  have hshape := halves_shape false t qn.live [(k1, Y)] r hr
  simp only [List.head?_cons] at hshape
  have hlook := halves_lookup false t qn.live [(k1, Y)] hs r hr hsc (by simp)
  rw [← hout] at hlook hshape
  simp only at hlook
  have hleft := halves_left_lt_divider qn.live (qn.live.length / 2) hs r hr
  have hright := halves_right_ge_divider qn.live (qn.live.length / 2) hs r hr
  -- the first half's and the second half's live klongs
  have hdrop : ∀ q ∈ (qn.live.drop (qn.live.length / 2)).tail, r.1 < q.1 := by
    have hd := hs.sublist (List.drop_sublist (qn.live.length / 2) qn.live)
    cases he : qn.live.drop (qn.live.length / 2) with
    | nil => rw [he] at hr; cases hr
    | cons a rest =>
      rw [he] at hr hd
      simp only [List.head?_cons, Option.some.injEq] at hr
      subst hr
      intro q hq
      simp only [List.tail_cons] at hq
      exact (List.pairwise_cons.mp hd).1 q hq
  have hsec : ∀ c z, (c, z) ∈ secondSplitPairs false qn.live → c = 0 ∨ r.1 < c := by
    intro c z hcz
    simp only [secondSplitPairs, Bool.false_eq_true, ↓reduceIte] at hcz
    cases he : qn.live.drop (qn.live.length / 2) with
    | nil => rw [he] at hr; cases hr
    | cons a rest =>
      rw [he] at hcz hdrop
      simp only [renameHead, List.mem_cons, Prod.mk.injEq] at hcz
      rcases hcz with ⟨h1, _⟩ | h1
      · exact Or.inl h1
      · exact Or.inr (hdrop (c, z) (by simpa using h1))
  have htimesNK : ∀ (l : List (Nat × NodeId)), ∀ s, Klong.time s ∈ (⟨false, newKlongs t l⟩ : KNode).ks → s ≤ t :=
    fun l => newKlongs_times t l
  obtain ⟨hsc', hl1, hl2, hw1, hw2, ht1, ht2, hF, hS⟩ : out.2.2 = r.1 ∧ out.1.leaf = false ∧
      out.2.1.leaf = false ∧ klongsWf out.1.ks = true ∧ klongsWf out.2.1.ks = true ∧
      (∀ s, Klong.time s ∈ out.1.ks → s ≤ t) ∧ (∀ s, Klong.time s ∈ out.2.1.ks → s ≤ t) ∧
      (∀ c z, (c, z) ∈ out.1.live → c < r.1) ∧
      (∀ c z, (c, z) ∈ out.2.1.live → c = 0 ∨ r.1 < c) := by
    by_cases hc : r.1 ≤ k1
    · simp only [hc, decide_true, ↓reduceIte] at hshape
      rw [hshape]
      refine ⟨rfl, rfl, rfl, klongsWf_newKlongs _ _, klongsWf_newKlongs _ _, htimesNK _, htimesNK _,
        ?_, ?_⟩
      · intro c z hcz
        exact hleft (c, z) (newKlongs_live_mem false t _ c z hcz)
      · intro c z hcz
        have := newKlongs_live_mem false t _ c z hcz
        rcases List.mem_append.mp this with h1 | h1
        · exact hsec c z h1
        · simp only [List.map_cons, List.map_nil, List.mem_singleton, Prod.mk.injEq] at h1
          obtain ⟨h1, _⟩ := h1
          subst h1
          simp only [splitLocalCv, Bool.not_false, Bool.true_and]
          by_cases hk : k1 = r.1
          · simp [hk]
          · have hk' : (k1 == r.1) = false := by simpa using hk
            simp only [hk', Bool.false_eq_true, ↓reduceIte]
            right; omega
    · simp only [hc, decide_false, Bool.false_eq_true, ↓reduceIte] at hshape
      rw [hshape]
      refine ⟨rfl, rfl, rfl, klongsWf_newKlongs _ _, klongsWf_newKlongs _ _, htimesNK _, htimesNK _,
        ?_, ?_⟩
      · intro c z hcz
        have := newKlongs_live_mem false t _ c z hcz
        rcases List.mem_append.mp this with h1 | h1
        · exact hleft (c, z) h1
        · simp only [List.mem_singleton, Prod.mk.injEq] at h1
          rw [h1.1]; omega
      · intro c z hcz
        exact hsec c z (newKlongs_live_mem false t _ c z hcz)
  rw [hsc'] at hlook
  -- the parent with the klong, as a lookup
  have hQw := KNode.add_key_wf qn t k1 Y hw
  have hQt := KNode.add_times qn t (.key k1 Y) (fun s h => by cases h) hqt
  have hQlook : ∀ c, (qn.add t (.key k1 Y)).live.lookup c =
      [(k1, Y)].foldl (pairLookupStep c) (qn.live.lookup c) := by
    intro c
    rw [KNode.add_key_live_lookup_of_wf qn t k1 c Y hw]
    simp [pairLookupStep]
  have hmemQ : ∀ a z, (a, z) ∈ (qn.add t (.key k1 Y)).live ↔
      (qn.add t (.key k1 Y)).live.lookup a = some z :=
    fun a z => mem_iff_lookup _ (KNode.live_keys_nodup _) a z
  have hmem1 : ∀ a z, (a, z) ∈ out.1.live ↔ out.1.live.lookup a = some z :=
    fun a z => mem_iff_lookup _ (KNode.live_keys_nodup _) a z
  have hmem2 : ∀ a z, (a, z) ∈ out.2.1.live ↔ out.2.1.live.lookup a = some z :=
    fun a z => mem_iff_lookup _ (KNode.live_keys_nodup _) a z
  -- below r.1 the first half and the parent agree
  have hlow : ∀ a z, a < r.1 → ((a, z) ∈ out.1.live ↔ (a, z) ∈ (qn.add t (.key k1 Y)).live) := by
    intro a z ha
    rw [hmem1, hmemQ, hQlook, ← hlook a]
    simp [ha]
  -- from r.1 on the second half and the parent agree, r.1 named the empty key
  have hspl : ∀ a, r.1 ≤ a → splitLocalCv false r.1 a = if a = r.1 then 0 else a := by
    intro a _
    simp only [splitLocalCv, Bool.not_false, Bool.true_and]
    by_cases h : a = r.1
    · simp [h]
    · have h' : (a == r.1) = false := by simpa using h
      simp [h', h]
  have hhigh : ∀ a z, r.1 < a → ((a, z) ∈ out.2.1.live ↔ (a, z) ∈ (qn.add t (.key k1 Y)).live) := by
    intro a z ha
    rw [hmem2, hmemQ, hQlook, ← hlook a, hspl a (by omega)]
    simp [show ¬ a < r.1 by omega, show a ≠ r.1 by omega]
  have hzero : ∀ z, (0, z) ∈ out.2.1.live ↔ (r.1, z) ∈ (qn.add t (.key k1 Y)).live := by
    intro z
    rw [hmem2, hmemQ, hQlook, ← hlook r.1, hspl r.1 (Nat.le_refl _)]
    simp
  have hsQ := (qn.add t (.key k1 Y)).searchLte_spec t
  refine ⟨hsc', hl1, hl2, hw1, hw2, ht1, ht2, ?_, ?_⟩
  · intro c hc
    have hs := hsQ c
    unfold NodeSearchSpec at hs
    rw [KNode.liveAt_of_times _ t hQt] at hs
    cases hq : (qn.add t (.key k1 Y)).searchLte t c with
    | none =>
      have hall := hs.2.mp hq
      rw [KNode.searchLte_none_of out.1 t ht1 c (fun q hq1 => by
        have hqr := hF q.1 q.2 hq1
        have := hall q ((hlow q.1 q.2 hqr).mp hq1)
        simp only [decide_eq_false_iff_not] at this
        omega)]
    | some f =>
      obtain ⟨hfm, hfa, hfmax⟩ := hs.1 f hq
      simp only [decide_eq_true_eq] at hfa
      have hfr : f.c < r.1 := by omega
      rw [KNode.searchLte_of_max out.1 t ht1 c f.c f.y ((hlow f.c f.y hfr).mpr hfm) hfa
        (fun q hq1 hqc => by
          have := hfmax q ((hlow q.1 q.2 (hF q.1 q.2 hq1)).mp hq1) (by simpa using hqc)
          simpa using this)]
      rfl
  · intro c hc
    have hs := hsQ c
    unfold NodeSearchSpec at hs
    rw [KNode.liveAt_of_times _ t hQt] at hs
    -- the parent has a klong of r.1
    obtain ⟨zr, hzr⟩ : ∃ z, (r.1, z) ∈ (qn.add t (.key k1 Y)).live := by
      have hrm : r ∈ qn.live := by
        have : r ∈ qn.live.drop (qn.live.length / 2) := by
          cases he : qn.live.drop (qn.live.length / 2) with
          | nil => rw [he] at hr; cases hr
          | cons a rest =>
            rw [he] at hr; simp only [List.head?_cons, Option.some.injEq] at hr; subst hr; simp
        exact List.mem_of_mem_drop this
      have hl := lookup_some_of_mem (KNode.live_keys_nodup qn) hrm
      by_cases hk : k1 = r.1
      · exact ⟨Y, by rw [hmemQ, KNode.add_key_live_lookup_of_wf qn t k1 r.1 Y hw]; simp [hk]⟩
      · refine ⟨r.2, ?_⟩
        rw [hmemQ, KNode.add_key_live_lookup_of_wf qn t k1 r.1 Y hw]
        have hk' : (k1 == r.1) = false := by simpa using hk
        simp only [hk', Bool.false_eq_true, ↓reduceIte]; exact hl
    cases hq : (qn.add t (.key k1 Y)).searchLte t c with
    | none =>
      have := hs.2.mp hq (r.1, zr) hzr
      simp only [decide_eq_false_iff_not] at this
      omega
    | some f =>
      obtain ⟨hfm, hfa, hfmax⟩ := hs.1 f hq
      simp only [decide_eq_true_eq] at hfa
      have hfr : r.1 ≤ f.c := by
        have := hfmax (r.1, zr) hzr (by simp only [decide_eq_true_eq]; omega)
        simpa using this
      by_cases hfe : f.c = r.1
      · have hm0 : (0, f.y) ∈ out.2.1.live := (hzero f.y).mpr (by rw [← hfe]; exact hfm)
        rw [KNode.searchLte_of_max out.2.1 t ht2 c 0 f.y hm0 (by omega) (fun q hq2 hqc => by
          rcases hS q.1 q.2 hq2 with h0 | hgt
          · omega
          · have := hfmax q ((hhigh q.1 q.2 hgt).mp hq2) (by simpa using hqc)
            simp only [decide_eq_true_eq] at this
            omega)]
        rfl
      · have hfgt : r.1 < f.c := by omega
        rw [KNode.searchLte_of_max out.2.1 t ht2 c f.c f.y ((hhigh f.c f.y hfgt).mpr hfm) hfa
          (fun q hq2 hqc => by
            rcases hS q.1 q.2 hq2 with h0 | hgt
            · omega
            · have := hfmax q ((hhigh q.1 q.2 hgt).mp hq2) (by simpa using hqc)
              simpa using this)]
        rfl

/-- `getEqR_split` for an inner node L split into the inner halves F and S: the
descents of N2 are those of Nm on the nodes that Nm reaches but L, F and S, and
from F (below sc) or S (from sc on) as from L. -/
theorem getEqR_split_inner (Nm N2 : NodeId → Option KNode) (t : Time) (r0 L q F S : NodeId)
    (qn qn2 m f s : KNode) (sc : Nat)
    (hNq : Nm q = some qn) (hql : qn.leaf = false) (hN2q : N2 q = some qn2)
    (hq2l : qn2.leaf = false)
    (hqsearch : ∀ c : Nat, (qn2.searchLte t c).map (·.y) =
      (qn.searchLte t c).map (fun fd => if fd.y = L then (if c < sc then F else S) else fd.y))
    (hNmL : Nm L = some m) (hml : m.leaf = false) (hrL : ReachS Nm t r0 L)
    (hN2F : N2 F = some f) (hfl : f.leaf = false) (hN2S : N2 S = some s) (hsl : s.leaf = false)
    (hsF : ∀ c : Nat, c < sc → (f.searchLte t c).map (·.y) = (m.searchLte t c).map (·.y))
    (hsS : ∀ c : Nat, sc ≤ c → (s.searchLte t c).map (·.y) = (m.searchLte t c).map (·.y))
    (hsame : ∀ x, x ≠ L → x ≠ q → x ≠ F → x ≠ S → N2 x = Nm x)
    (hnotL : ∀ x xn c z, ReachS Nm t r0 x → x ≠ q → Nm x = some xn → (c, z) ∈ xn.liveAt t → z ≠ L)
    (hnotFS : ∀ x xn c z, ReachS Nm t r0 x → Nm x = some xn → (c, z) ∈ xn.liveAt t →
      z ≠ F ∧ z ≠ S) (hLq : L ≠ q) (c : Nat) :
    ∀ (fu : Nat), (∀ (x : NodeId), ReachS Nm t r0 x → x ≠ L → x ≠ F → x ≠ S →
      getEqR N2 t c fu x = getEqR Nm t c fu x) ∧
      getEqR N2 t c fu (if c < sc then F else S) = getEqR Nm t c fu L := by
  intro fu
  induction fu with
  | zero => exact ⟨fun _ _ _ _ _ => rfl, rfl⟩
  | succ fu ih =>
    obtain ⟨ihP, ihQ⟩ := ih
    refine ⟨?_, ?_⟩
    · intro x hx hxL hxF hxS
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
              exact ihQ
            · simp only [hL, ↓reduceIte] at hs
              rw [hs]
              have hfs := hnotFS x qn fd.c fd.y hx hNq hmem
              exact ihP fd.y hrfd hL hfs.1 hfs.2
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
              exact ihP fd.y hrfd (hnotL x xn fd.c fd.y hx hxq hn hmem) hfs.1 hfs.2
    · -- the halves search as L does, then the same child
      have hchild : ∀ fd : Found, m.searchLte t c = some fd →
          getEqR N2 t c fu fd.y = getEqR Nm t c fu fd.y := by
        intro fd hfd
        have hmem := KNode.searchLte_mem m t c fd hfd
        have hfs := hnotFS L m fd.c fd.y hrL hNmL hmem
        exact ihP fd.y (ReachS.step L m fd.c fd.y hrL hNmL hmem)
          (hnotL L m fd.c fd.y hrL hLq hNmL hmem) hfs.1 hfs.2
      by_cases hc : c < sc
      · simp only [hc, ↓reduceIte, getEqR, hN2F, hfl, hNmL, hml, Bool.false_eq_true]
        have he := hsF c hc
        cases h1 : m.searchLte t c with
        | none =>
          rw [h1] at he
          cases h2 : f.searchLte t c with
          | none => rfl
          | some _ => rw [h2] at he; cases he
        | some fd =>
          rw [h1] at he
          cases h2 : f.searchLte t c with
          | none => rw [h2] at he; cases he
          | some fd2 =>
            rw [h2] at he
            simp only [Option.map_some, Option.some.injEq] at he
            simp only
            rw [he]
            exact hchild fd h1
      · simp only [hc, ↓reduceIte, getEqR, hN2S, hsl, hNmL, hml, Bool.false_eq_true]
        have he := hsS c (by omega)
        cases h1 : m.searchLte t c with
        | none =>
          rw [h1] at he
          cases h2 : s.searchLte t c with
          | none => rfl
          | some _ => rw [h2] at he; cases he
        | some fd =>
          rw [h1] at he
          cases h2 : s.searchLte t c with
          | none => rw [h2] at he; cases he
          | some fd2 =>
            rw [h2] at he
            simp only [Option.map_some, Option.some.injEq] at he
            simp only
            rw [he]
            exact hchild fd h1

/-! ## The writer: a time split of a leaf whose inner parent is full and space split -/

/-- The state after a time split of the leaf L whose parent q, full, is space
split, below the grandparent g with room: L's last version with the put at the
next id, the halves of q's last version with the klong to it at the two ids
after, g's klong kq names the first and a klong at the second half's first
compare value the second; L and q keep their klongs before the transaction. -/
def TimeSpaceAfter (c : Ctx) (w w' : W) (L q g : NodeId) (n qn gn : KNode)
    (kq k1 cv v : Nat) : Prop :=
  ∃ l : KNode, l.leaf = n.leaf ∧ klongsWf l.ks = true ∧ (∀ s, Klong.time s ∈ l.ks → s ≤ c.i) ∧
    (∀ q', l.live.lookup q' = if cv == q' then some v else n.live.lookup q') ∧
    w'.taken = w.taken ∧ w'.top = w.top ∧ w'.vals = w.vals ∧
    ∀ x, w'.nodes.lookup x =
      if x = L then some (n.toPrev (c.i - 1))
      else if x = q then some (qn.toPrev (c.i - 1))
      else if x = g then some ((gn.add c.i (.key kq (w.next + 2))).add c.i
        (.key (halves qn.leaf c.i (qn.lastVersion c.i) [(k1, w.next)]).2.2 (w.next + 2 + 2)))
      else if x = w.next then some ⟨n.leaf, l.ks⟩
      else if x = w.next + 2 then some (halves qn.leaf c.i (qn.lastVersion c.i) [(k1, w.next)]).1
      else if x = w.next + 2 + 2 then
        some (halves qn.leaf c.i (qn.lastVersion c.i) [(k1, w.next)]).2.1
      else w.nodes.lookup x

set_option linter.unusedSimpArgs false in
theorem writerWP_handleFullWith_timeSpace (d'' : Nat) (L q g : NodeId) (n qn gn : KNode)
    (kq k1 cv v : Nat) (compact : Bool) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hlq : w.nodes.lookup q = some qn)
    (hlg : w.nodes.lookup g = some gn)
    (hqL : q ≠ L) (hgq : g ≠ q) (hgL : g ≠ L) (hql : qn.leaf = false) (hgl : gn.leaf = false)
    (hfirst : n.firstTime ≠ some c.i) (hqfirst : qn.firstTime ≠ some c.i)
    (hcs : (!compact && decide ((n.lastVersion c.i).size > c.p.splitAbove)) = false)
    (hqfull : c.p.M < qn.size + 1 + 1)
    (hqsplit : c.p.splitAbove < (qn.lastVersion c.i).size)
    (hpg : (w.path[d'']?).map (·.2) = some g) (hpq : w.path[d'' + 1]? = some (some kq, q))
    (hpk : w.path[d'' + 1 + 1]? = some (some k1, L))
    (hroomg : gn.size + 2 + 1 ≤ c.p.M)
    (hdeadg : ∀ y1 sc y2, deadOver c.p ((gn.add c.i (.key kq y1)).add c.i (.key sc y2)) = false)
    (hny : w.nodes.lookup w.next = none) (hny2 : w.nodes.lookup (w.next + 2) = none)
    (hny3 : w.nodes.lookup (w.next + 2 + 2) = none)
    (hLn : L < w.next) :
    WriterWP (handleFullWith (fun q more => appendKlongs (d'' + 1) q more) (d'' + 1 + 1) L [(cv, v)]
      (n.lastVersion c.i) compact) c w
      (fun _ w' => TimeSpaceAfter c w w' L q g n qn gn kq k1 cv v) := by
  have hpq' : (w.path[d'' + 1]?).map (·.2) = some q := by rw [hpq]; rfl
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w hlk]
  refine writerWP_ghOf_cached L n c w hlk _ (fun gh => ?_)
  have hnew : (n.firstTime == some c.i) = false := by simpa using hfirst
  simp only [hnew]
  unfold parentAt pathNode
  simp only [writerWP_bind, writerWP_get]
  cases hp : w.path[d'' + 1]? with
  | none => rw [hp] at hpq'; cases hpq'
  | some e =>
    rw [hp] at hpq'
    simp only [Option.map_some, Option.some.injEq] at hpq'
    simp only [writerWP_pure]
    rw [hpq']
    simp only [writerWP_bind]
    rw [writerWP_getNode_known q qn c w hlq]
    simp only [writerWP_pure, hql, hcs, Bool.false_eq_true, ↓reduceIte]
    have hfinal : ∀ (l : KNode), l.leaf = n.leaf → klongsWf l.ks = true →
        (∀ s, Klong.time s ∈ l.ks → s ≤ c.i) →
        (∀ q', l.live.lookup q' = [(cv, v)].foldl (pairLookupStep q') (n.live.lookup q')) →
        ∀ w2 : W, w2.taken = w.taken → w2.top = w.top → w2.vals = w.vals →
        (∀ x, w2.nodes.lookup x =
          if x = q then some (qn.toPrev (c.i - 1))
          else if x = g then some ((gn.add c.i (.key kq (w.next + 2))).add c.i
            (.key (halves qn.leaf c.i (qn.lastVersion c.i) [(k1, w.next)]).2.2 (w.next + 2 + 2)))
          else if x = w.next + 2 then some (halves qn.leaf c.i (qn.lastVersion c.i) [(k1, w.next)]).1
          else if x = w.next + 2 + 2 then
            some (halves qn.leaf c.i (qn.lastVersion c.i) [(k1, w.next)]).2.1
          else (w.nodes ++ [(w.next, ({ leaf := n.leaf, ks := l.ks } : KNode))]).lookup x) →
        WriterWP (do let n ← getNode L; putNode L (n.toPrev (c.i - 1))) c w2
          (fun _ w' => TimeSpaceAfter c w w' L q g n qn gn kq k1 cv v) := by
      intro l hl_leaf hl_wf hl_times hl_look w2 h2t h2top h2v h2n
      have hlk2 : w2.nodes.lookup L = some n := by
        rw [h2n]
        simp only [show L ≠ q from fun h => hqL h.symm, show L ≠ g from fun h => hgL h.symm,
          show L ≠ w.next + 2 by omega, show L ≠ w.next + 2 + 2 by omega, ↓reduceIte,
          List.lookup_append, hlk]
        rfl
      simp only [writerWP_bind]
      rw [writerWP_getNode_known L n c w2 hlk2]
      simp only [putNode, writerWP_modify]
      refine ⟨l, hl_leaf, hl_wf, hl_times, ?_, h2t, h2top, h2v, ?_⟩
      · intro q'
        rw [hl_look q']
        simp [pairLookupStep]
      · intro x
        show (upsert _ L _).lookup x = _
        rw [lookup_upsert, h2n]
        by_cases hxL : x = L
        · simp [hxL]
        · simp only [hxL, ↓reduceIte]
          by_cases hxq : x = q
          · simp [hxq]
          · simp only [hxq, ↓reduceIte]
            by_cases hxg : x = g
            · simp [hxg]
            · simp only [hxg, ↓reduceIte, List.lookup_append]
              by_cases hx3 : x = w.next + 2 + 2
              · simp [hx3, show w.next + 2 + 2 ≠ w.next by omega,
                  show w.next + 2 + 2 ≠ w.next + 2 by omega]
              · by_cases hx2 : x = w.next + 2
                · simp [hx2, show w.next + 2 ≠ w.next by omega]
                · simp only [hx2, hx3, ↓reduceIte]
                  by_cases hxy : x = w.next
                  · subst hxy; rw [hny]; simp [List.lookup]
                  · simp only [hxy, ↓reduceIte]
                    cases h : w.nodes.lookup x with
                    | some m => rfl
                    | none =>
                      show (none : Option KNode).or ([(w.next, { leaf := n.leaf, ks := l.ks })].lookup x) = none
                      rw [lookup_cons_ne _ _ _ _ hxy]; rfl
    have hup : ∀ (l : KNode), l.leaf = n.leaf → klongsWf l.ks = true →
        (∀ s, Klong.time s ∈ l.ks → s ≤ c.i) →
        (∀ q', l.live.lookup q' = [(cv, v)].foldl (pairLookupStep q') (n.live.lookup q')) →
        ∀ w1 : W, w1.nodes = w.nodes ++ [(w.next, ({ leaf := n.leaf, ks := l.ks } : KNode))] →
        w1.next = w.next + 2 → w1.path = w.path → w1.taken = w.taken → w1.top = w.top →
        w1.vals = w.vals →
        WriterWP (appendKlongs (d'' + 1) q [(k1, w.next)]) c w1 (fun _ w' =>
          WriterWP (do let n ← getNode L; putNode L (n.toPrev (c.i - 1))) c w'
            (fun _ w'' => TimeSpaceAfter c w w'' L q g n qn gn kq k1 cv v)) := by
      intro l hl_leaf hl_wf hl_times hl_look w1 h1n h1x h1p h1t h1top h1v
      refine writerWP_mono (writerWP_appendKlongs_spaceSplit d'' q g qn gn kq k1 w.next c w1
        (by rw [h1n, List.lookup_append, hlq]; rfl) (by rw [h1n, List.lookup_append, hlg]; rfl)
        hgq hgl hqfirst hqfull hqsplit (by rw [h1p]; exact hpg) (by rw [h1p]; exact hpq)
        hroomg (fun y1 sc y2 => hdeadg y1 sc y2)
        (by
          rw [h1n, h1x, List.lookup_append, hny2]
          show ([(w.next, ({ leaf := n.leaf, ks := l.ks } : KNode))].lookup (w.next + 2)) = none
          rw [lookup_cons_ne _ _ _ _ (by omega)]; rfl)
        (by
          rw [h1n, h1x, List.lookup_append, hny3]
          show ([(w.next, ({ leaf := n.leaf, ks := l.ks } : KNode))].lookup (w.next + 2 + 2)) = none
          rw [lookup_cons_ne _ _ _ _ (by omega)]; rfl)) ?_
      intro _ w2 ⟨h2t, h2top, h2v, h2n⟩
      refine hfinal l hl_leaf hl_wf hl_times hl_look w2
        (by rw [h2t, h1t]) (by rw [h2top, h1top]) (by rw [h2v, h1v]) ?_
      intro x; rw [h2n x, h1x, h1n]
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
          exact hup l hl_leaf hl_wf hl_times hl_look _ rfl rfl rfl rfl rfl rfl
    · simp only [writerWP_bind]
      refine writerWP_mono (writerWP_replaceOrAdd_last n [(cv, v)] c _) ?_
      rintro l w1 ⟨hw1, hl_leaf, hl_wf, hl_times, hl_look⟩
      subst w1
      split <;>
      · simp only [newKey, fresh, setMadeFor, klongAt, note, writerWP_bind, writerWP_modify,
          writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
        split <;>
        · simp only [writerWP_bind, writerWP_modify, writerWP_pure, hpk]
          exact hup l hl_leaf hl_wf hl_times hl_look _ rfl rfl rfl rfl rfl rfl

end SIS.Tree
