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

/-! ## The reading after a leaf's time split and its parent's space split -/

theorem getFromR_timeSpace (N N2 : NodeId → Option KNode) (V V2 : NodeId → Option Nat)
    (i : Time) (fuel : Nat) (hfuel : 1 ≤ fuel) (root L q g Y Fq Sq v : NodeId)
    (n qn gn ln : KNode) (k1 kq : Nat) (pre : List Nat) (cv h : Nat) (rk : NodeId)
    (r : Nat × NodeId) (hr : (qn.live.drop (qn.live.length / 2)).head? = some r) (hsc : 0 < r.1)
    (hwfG : ∀ x xn, N x = some xn → klongsWf xn.ks = true)
    (hNL : N L = some n) (hnl : n.leaf = true) (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ i)
    (hNq : N q = some qn) (hql : qn.leaf = false) (hqt : ∀ s, Klong.time s ∈ qn.ks → s ≤ i)
    (hk1 : (k1, L) ∈ qn.live)
    (hNg : N g = some gn) (hgl : gn.leaf = false) (hgt : ∀ s, Klong.time s ∈ gn.ks → s ≤ i)
    (hkq : (kq, q) ∈ gn.live) (hkqr : kq ≤ r.1)
    (hgap : ∀ c' z, (c', z) ∈ gn.live → c' ≤ kq ∨ r.1 < c')
    (hN2Y : N2 Y = some ln) (hlnl : ln.leaf = true) (hlnwf : klongsWf ln.ks = true)
    (hlnt : ∀ s, Klong.time s ∈ ln.ks → s ≤ i)
    (hlnlook : ∀ c, ln.live.lookup c = if cv == c then some v else n.live.lookup c)
    (hN2g : N2 g = some ((gn.add i (.key kq Fq)).add i
      (.key (halves qn.leaf i (qn.lastVersion i) [(k1, Y)]).2.2 Sq)))
    (hN2F : N2 Fq = some (halves qn.leaf i (qn.lastVersion i) [(k1, Y)]).1)
    (hN2S : N2 Sq = some (halves qn.leaf i (qn.lastVersion i) [(k1, Y)]).2.1)
    (hN2L : ∀ m, N2 L = some m → klongsWf m.ks = true)
    (hN2 : ∀ x, x ≠ L → x ≠ q → x ≠ g → x ≠ Y → x ≠ Fq → x ≠ Sq → N2 x = N x)
    (hV2v : V2 v = some h) (hV2 : ∀ a, a ≠ v → V2 a = V a) (hV2L : V2 L = none)
    (hV2Y : V2 Y = none)
    (hqL : q ≠ L) (hYL : Y ≠ L) (hYq : Y ≠ q) (hgq : g ≠ q) (hgL : g ≠ L) (hgY : g ≠ Y)
    (hFL : Fq ≠ L) (hFq : Fq ≠ q) (hFg : Fq ≠ g) (hFY : Fq ≠ Y)
    (hSL : Sq ≠ L) (hSq : Sq ≠ q) (hSg : Sq ≠ g) (hSY : Sq ≠ Y) (hFS : Fq ≠ Sq)
    (hvL : v ≠ L) (hvY : v ≠ Y) (hvq : v ≠ q) (hvF : v ≠ Fq) (hvS : v ≠ Sq)
    (hNv : N v = none) (hNY : N Y = none) (hNF : N Fq = none) (hNS : N Sq = none)
    (hrootL : root ≠ L) (hrootY : root ≠ Y) (hrootq : root ≠ q) (hrootF : root ≠ Fq)
    (hrootS : root ≠ Sq) (hrootv : root ≠ v)
    (hrq : ReachS N i root q) (hrg : ReachS N i root g)
    (hnoq : ¬ ReachS N i q g) (hnoL : ¬ ReachS N i L g)
    (hrk : segRootR N i fuel pre root = some rk) (hcv : cv ∉ pre)
    (hvisL : (L, cv) ∈ eqVisits N i cv fuel rk)
    (huniq : ∀ key' x m', keyWf key' = true → (x, cv) ∈ fromVisits N i fuel key' root →
      (x, cv) ∈ eqVisits N i cv fuel rk → N x = some m' → m'.leaf = true → key' = pre ++ [cv])
    (honlyL : ∀ x xn c, ReachS N i root x → N x = some xn → (c, L) ∈ xn.liveAt i →
      x = q ∧ c = k1)
    (honlyq : ∀ x xn c, ReachS N i root x → N x = some xn → (c, q) ∈ xn.liveAt i →
      x = g ∧ c = kq)
    (hfr : ∀ x xn c z, ReachS N i root x → N x = some xn → (c, z) ∈ xn.liveAt i →
      z ≠ v ∧ z ≠ Y ∧ z ≠ Fq ∧ z ≠ Sq) :
    ∀ key', keyWf key' = true → getFromR N2 V2 i fuel key' root =
      if pre ++ [cv] == key' then some h else getFromR N V i fuel key' root := by
  have hwfR : ∀ x xn, ReachS N i root x → N x = some xn → klongsWf xn.ks = true :=
    fun x xn _ hn => hwfG x xn hn
  have hnwf := hwfG L n hNL
  have hqwf := hwfG q qn hNq
  have hgwf := hwfG g gn hNg
  let q1 : KNode := qn.add i (.key k1 Y)
  let N1 : NodeId → Option KNode := fun x =>
    if x = q then some q1 else if x = g then some gn
    else if x = Fq then none else if x = Sq then none else N2 x
  have hN1q : N1 q = some q1 := by simp [N1]
  have hN1g : N1 g = some gn := by simp [N1, hgq]
  have hN1Y : N1 Y = some ln := by simp [N1, hYq, hgY.symm, hFY.symm, hSY.symm, hN2Y]
  have hN1F : N1 Fq = none := by simp [N1, hFq, hFg]
  have hN1S : N1 Sq = none := by simp [N1, hSq, hSg]
  have hN1 : ∀ x, x ≠ L → x ≠ q → x ≠ Y → N1 x = N x := by
    intro x h1 h2 h3
    by_cases hxg : x = g
    · subst hxg; simp [N1, h2, hNg]
    · by_cases hxF : x = Fq
      · subst hxF; simp [N1, h2, hxg, hNF]
      · by_cases hxS : x = Sq
        · subst hxS; simp [N1, h2, hxg, hxF, hNS]
        · simp only [N1, h2, hxg, hxF, hxS, ↓reduceIte]
          exact hN2 x h1 h2 hxg h3 hxF hxS
  -- step A: N1 reads as the put
  have hA := getFromR_timeSplit_only N N1 V V2 i fuel hfuel root L q Y v n qn ln k1 pre cv h rk
    hNL hnl hnwf hnt hNq hql hqwf hqt hk1 hlnl hlnwf hlnt hlnlook hN1Y hN1q hN1 hV2v hV2 hV2L hV2Y
    hqL hYL hYq hvL hvY hNv hrootL hrootY hrq hrk hcv hvisL huniq hwfR honlyL
    (fun x xn c z hx hn hz => ⟨(hfr x xn c z hx hn hz).1, (hfr x xn c z hx hn hz).2.1⟩)
  -- the nodes N1 reaches
  have hqk1 : (k1, L) ∈ qn.liveAt i := by rw [KNode.liveAt_of_times qn i hqt]; exact hk1
  have hrL : ReachS N i root L := ReachS.step q qn k1 L hrq hNq hqk1
  have hqadd : ∀ c z, (c, z) ∈ q1.liveAt i → ((c, z) ∈ qn.liveAt i ∧ c ≠ k1) ∨ z = Y := by
    intro c z hz
    have ht2 := KNode.add_times qn i (.key k1 Y) (fun s h => by cases h) hqt
    rw [KNode.liveAt_of_times _ i ht2] at hz
    have := lookup_some_of_mem (KNode.live_keys_nodup _) hz
    rw [KNode.add_key_live_lookup_of_wf qn i k1 c Y hqwf] at this
    by_cases hc : k1 = c
    · subst hc; simp at this; exact Or.inr this.symm
    · have hc' : (k1 == c) = false := by simpa using hc
      simp only [hc', Bool.false_eq_true, ↓reduceIte] at this
      left; rw [KNode.liveAt_of_times qn i hqt]
      exact ⟨lookup_some_mem this, fun h => hc h.symm⟩
  have hlnmem : ∀ c z, (c, z) ∈ ln.liveAt i → (c, z) ∈ n.liveAt i ∨ z = v := by
    intro c z hz
    rw [KNode.liveAt_of_times ln i hlnt] at hz
    have := lookup_some_of_mem (KNode.live_keys_nodup ln) hz
    rw [hlnlook] at this
    by_cases hc : cv = c
    · subst hc; simp at this; exact Or.inr this.symm
    · have hc' : (cv == c) = false := by simpa using hc
      simp only [hc', Bool.false_eq_true, ↓reduceIte] at this
      left; rw [KNode.liveAt_of_times n i hnt]; exact lookup_some_mem this
  have hreachNe : ∀ x, ReachS N i root x → x ≠ Y ∧ x ≠ Fq ∧ x ≠ Sq ∧ x ≠ v := by
    intro x hx
    cases hx with
    | root => exact ⟨hrootY, hrootF, hrootS, hrootv⟩
    | step x' xn c _ hx' hn hz =>
      have := hfr x' xn c _ hx' hn hz
      exact ⟨this.2.1, this.2.2.1, this.2.2.2, this.1⟩
  have hreach1 : ∀ x, ReachS N1 i root x → (ReachS N i root x ∧ x ≠ L) ∨ x = Y ∨ x = v := by
    intro x hx
    induction hx with
    | root => exact Or.inl ⟨ReachS.root, hrootL⟩
    | step x' xn c z _ hn hz ih =>
      rcases ih with ⟨hx', hx'L⟩ | hx' | hx'
      · by_cases hxq : x' = q
        · subst hxq
          rw [hN1q] at hn; cases hn
          rcases hqadd c z hz with ⟨hz', hck⟩ | hzY
          · left
            refine ⟨ReachS.step x' qn c z hx' hNq hz', fun hzL => ?_⟩
            subst hzL
            exact hck (honlyL x' qn c hx' hNq hz').2
          · exact Or.inr (Or.inl hzY)
        · rw [hN1 x' hx'L hxq (hreachNe x' hx').1] at hn
          left
          refine ⟨ReachS.step x' xn c z hx' hn hz, fun hzL => ?_⟩
          subst hzL
          exact hxq (honlyL x' xn c hx' hn hz).1
      · subst x'
        rw [hN1Y] at hn; cases hn
        rcases hlnmem c z hz with hz' | hzv
        · left
          refine ⟨ReachS.step L n c z hrL hNL hz', fun hzL => ?_⟩
          subst hzL
          exact hqL (honlyL _ n c hrL hNL hz').1.symm
        · exact Or.inr (Or.inr hzv)
      · subst x'
        have : N1 v = none := by rw [hN1 v hvL hvq hvY, hNv]
        rw [this] at hn; cases hn
  -- step B: q split at g into Fq and Sq
  have hq1wf : klongsWf q1.ks = true := KNode.add_key_wf qn i k1 Y hqwf
  have hwf1 : ∀ x xn, ReachS N1 i root x → N1 x = some xn → klongsWf xn.ks = true := by
    intro x xn hx hn
    rcases hreach1 x hx with ⟨hx', hxL⟩ | hxY | hxv
    · by_cases hxq : x = q
      · subst hxq; rw [hN1q] at hn; cases hn; exact hq1wf
      · rw [hN1 x hxL hxq (hreachNe x hx').1] at hn; exact hwfG x xn hn
    · subst hxY; rw [hN1Y] at hn; cases hn; exact hlnwf
    · subst hxv; rw [hN1 x hvL hvq hvY, hNv] at hn; cases hn
  have hnotq1 : ∀ x xn c z, ReachS N1 i root x → x ≠ g → N1 x = some xn →
      (c, z) ∈ xn.liveAt i → z ≠ q := by
    intro x xn c z hx hxg hn hz hzq
    subst hzq
    rcases hreach1 x hx with ⟨hx', hxL⟩ | hxY | hxv
    · by_cases hxq : x = z
      · subst hxq
        rw [hN1q] at hn; cases hn
        rcases hqadd c x hz with ⟨hz', _⟩ | hzY
        · exact hgq (honlyq x qn c hx' hNq hz').1.symm
        · exact hYq hzY.symm
      · rw [hN1 x hxL hxq (hreachNe x hx').1] at hn
        exact hxg (honlyq x xn c hx' hn hz).1
    · subst hxY
      rw [hN1Y] at hn; cases hn
      rcases hlnmem c z hz with hz' | hzv
      · exact hgL (honlyq L n c hrL hNL hz').1.symm
      · exact hvq hzv.symm
    · subst hxv
      rw [hN1 x hvL hvq hvY, hNv] at hn; cases hn
  have hnotFS1 : ∀ x xn c z, ReachS N1 i root x → N1 x = some xn → (c, z) ∈ xn.liveAt i →
      z ≠ Fq ∧ z ≠ Sq := by
    intro x xn c z hx hn hz
    rcases hreach1 x hx with ⟨hx', hxL⟩ | hxY | hxv
    · by_cases hxq : x = q
      · subst hxq
        rw [hN1q] at hn; cases hn
        rcases hqadd c z hz with ⟨hz', _⟩ | hzY
        · exact ⟨(hfr x qn c z hx' hNq hz').2.2.1, (hfr x qn c z hx' hNq hz').2.2.2⟩
        · rw [hzY]; exact ⟨hFY.symm, hSY.symm⟩
      · rw [hN1 x hxL hxq (hreachNe x hx').1] at hn
        exact ⟨(hfr x xn c z hx' hn hz).2.2.1, (hfr x xn c z hx' hn hz).2.2.2⟩
    · subst hxY
      rw [hN1Y] at hn; cases hn
      rcases hlnmem c z hz with hz' | hzv
      · exact ⟨(hfr L n c z hrL hNL hz').2.2.1, (hfr L n c z hrL hNL hz').2.2.2⟩
      · rw [hzv]; exact ⟨hvF, hvS⟩
    · subst hxv
      rw [hN1 x hvL hvq hvY, hNv] at hn; cases hn
  -- the halves of q with the klong put
  obtain ⟨hscq, hFl, hSl, hFwf, hSwf, hFt, hSt, hsF, hsS⟩ :=
    halves_inner_searchLte qn i k1 Y hql hqwf hqt r hr hsc
  have hg2 : (((gn.add i (.key kq Fq)).add i
      (.key (halves qn.leaf i (qn.lastVersion i) [(k1, Y)]).2.2 Sq))).leaf = false := by
    rw [KNode.add_leaf, KNode.add_leaf]; exact hgl
  have hgsearch : ∀ c : Nat, ((((gn.add i (.key kq Fq)).add i
      (.key (halves qn.leaf i (qn.lastVersion i) [(k1, Y)]).2.2 Sq))).searchLte i c).map (·.y) =
      (gn.searchLte i c).map (fun fd => if fd.y = q then
        (if c < (halves qn.leaf i (qn.lastVersion i) [(k1, Y)]).2.2 then Fq else Sq) else fd.y) := by
    intro c
    rw [hscq]
    have hA := KNode.splitParent_searchLte gn i kq r.1 q Fq Sq hgwf hgt hkq hkqr hgap c
    rw [hA]
    cases hs : gn.searchLte i c with
    | none => rfl
    | some fd =>
      simp only [Option.map_some, Option.some.injEq]
      have hmemfd := KNode.searchLte_mem gn i c fd hs
      have hyq : fd.y = q ↔ fd.c = kq := by
        constructor
        · intro hy
          rw [hy] at hmemfd
          exact (honlyq g gn fd.c hrg hNg hmemfd).2
        · intro hc
          rw [KNode.liveAt_of_times gn i hgt, hc] at hmemfd
          exact Option.some.inj ((lookup_some_of_mem (KNode.live_keys_nodup gn) hmemfd).symm.trans
            (lookup_some_of_mem (KNode.live_keys_nodup gn) hkq))
      by_cases hc : fd.c = kq
      · simp only [hc, ↓reduceIte, hyq.mpr hc, Int.ofNat_lt]
      · have hy : ¬ fd.y = q := fun h => hc (hyq.mp h)
        simp only [hc, ↓reduceIte, hy]
  have hrq1 : ReachS N1 i root q := by
    have htr : ∀ x, ReachS N i root x → ¬ ReachS N i q x → ¬ ReachS N i L x →
        ReachS N1 i root x := by
      intro x hx
      induction hx with
      | root => intro _ _; exact ReachS.root
      | step x' xn c z hx' hn hz ih =>
        intro hq hL
        have hq' : ¬ ReachS N i q x' := fun h => hq (ReachS.step x' xn c z h hn hz)
        have hL' : ¬ ReachS N i L x' := fun h => hL (ReachS.step x' xn c z h hn hz)
        have hx'q : x' ≠ q := by intro he; subst he; exact hq' ReachS.root
        have hx'L : x' ≠ L := by intro he; subst he; exact hL' ReachS.root
        have hn1 : N1 x' = some xn := by rw [hN1 x' hx'L hx'q (hreachNe x' hx').1]; exact hn
        exact ReachS.step x' xn c z (ih hq' hL') hn1 hz
    have hrg1 : ReachS N1 i root g := htr g hrg hnoq hnoL
    exact ReachS.step g gn kq q hrg1 hN1g (by rw [KNode.liveAt_of_times gn i hgt]; exact hkq)
  have hsame1 : ∀ x, x ≠ q → x ≠ g → x ≠ Fq → x ≠ Sq → N2 x = N1 x := by
    intro x h1 h2 h3 h4
    simp only [N1, h1, h2, h3, h4, ↓reduceIte]
  have hget := fun c => getEqR_split_inner N1 N2 i root q g Fq Sq gn _ q1 _ _ _ hN1g hgl hN2g hg2
    hgsearch hN1q (by simp only [q1, KNode.add_leaf]; exact hql) hrq1 hN2F hFl hN2S hSl
    (fun c hc => by rw [hscq] at hc; exact hsF c hc) (fun c hc => by rw [hscq] at hc; exact hsS c hc)
    (fun x h1 h2 h3 h4 => hsame1 x h1 h2 h3 h4)
    (fun x xn c z hx hxg hn hz => hnotq1 x xn c z hx hxg hn hz)
    hnotFS1 hgq.symm c
  have hsim := getFromR_split N1 N2 V2 i fuel root q g Fq Sq hwf1
    (fun c x hx hxq hxF hxS => (hget c fuel).1 x hx hxq hxF hxS)
    (fun x h1 h2 h3 h4 => hsame1 x h1 h2 h3 h4) (by rw [hN2g, hN1g]; rfl)
    (fun x xn c z hx hxg hn hz => hnotq1 x xn c z hx hxg hn hz)
    (fun xn c z hxn _ hxl => by rw [hN1g] at hxn; cases hxn; rw [hgl] at hxl; cases hxl)
    (fun x xn c z hx hn hz => ⟨fun _ => (hnotFS1 x xn c z hx hn hz).1, (hnotFS1 x xn c z hx hn hz).2⟩)
  intro key' hkey'
  rw [hsim key' root ReachS.root hrootq hrootF hrootS]
  exact hA key' hkey'

theorem writerWP_appendKlongs_timeSpace (d'' : Nat) (L q g : NodeId) (n qn gn : KNode)
    (kq k1 cv v : Nat) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hlq : w.nodes.lookup q = some qn)
    (hlg : w.nodes.lookup g = some gn)
    (hqL : q ≠ L) (hgq : g ≠ q) (hgL : g ≠ L) (hql : qn.leaf = false) (hgl : gn.leaf = false)
    (hfirst : n.firstTime ≠ some c.i) (hqfirst : qn.firstTime ≠ some c.i)
    (hfull : ¬ (n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv v)) = false))
    (hsplit : c.p.M ≤ n.size + 1 → (n.lastVersion c.i).size ≤ c.p.splitAbove)
    (hqfull : c.p.M < qn.size + 1 + 1)
    (hqsplit : c.p.splitAbove < (qn.lastVersion c.i).size)
    (hpg : (w.path[d'']?).map (·.2) = some g) (hpq : w.path[d'' + 1]? = some (some kq, q))
    (hpk : w.path[d'' + 1 + 1]? = some (some k1, L))
    (hroomg : gn.size + 2 + 1 ≤ c.p.M)
    (hdeadg : ∀ y1 sc y2, deadOver c.p ((gn.add c.i (.key kq y1)).add c.i (.key sc y2)) = false)
    (hny : w.nodes.lookup w.next = none) (hny2 : w.nodes.lookup (w.next + 2) = none)
    (hny3 : w.nodes.lookup (w.next + 2 + 2) = none)
    (hLn : L < w.next) :
    WriterWP (appendKlongs (d'' + 1 + 1) L [(cv, v)]) c w
      (fun _ w' => TimeSpaceAfter c w w' L q g n qn gn kq k1 cv v) := by
  rw [appendKlongs_step_dead]
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w hlk]
  have hts := fun compact hcs => writerWP_handleFullWith_timeSpace d'' L q g n qn gn kq k1 cv v
    compact c w hlk hlq hlg hqL hgq hgL hql hgl hfirst hqfirst hcs hqfull hqsplit hpg hpq hpk hroomg
    hdeadg hny hny2 hny3 hLn
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

/-! ## The rule: a time split of a leaf and a space split of its full parent -/

/-- A put of a key whose last segment's leaf L existed before the transaction
and is full, with at most h klongs in its last version or full by dead klongs
only, below the parent q, an inner node that existed before the transaction and
is full by its size, with more than h klongs in its last version, at least two
of them live, below the grandparent g with room for two klongs: the time split
of L and the space split of q change the reading by the put alone. The keys of
q's live klongs lie between kq and g's next key (`hrange`), and neither q nor L
reaches g. -/
theorem writerWP_put_timeSpace (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv h : Nat) (rk : NodeId) (w : W)
    (S0 : List (Option Nat × NodeId)) (kq k1 : Nat) (q L : NodeId) (n qn gn : KNode)
    (hkey : keyWf (pre ++ [cv]) = true)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false)
    (hids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
      (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next) ∧
      (∀ q ∈ w.vals, q.1 < w.next) ∧ w.top.rootKey < w.next)
    (hbase : ∀ z, w.next ≤ z → knodeOf c.p base z = none ∧ valueOf base z = none)
    (hwfG : ∀ x xn, wNode c.p base w x = some xn → klongsWf xn.ks = true)
    (hpath : PathFrom (wNode c.p base w) c.i cv rk (S0 ++ [(some kq, q), (some k1, L)]))
    (hNL : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (hNq : wNode c.p base w q = some qn) (hNg : wNode c.p base w (pathEnd rk S0) = some gn)
    (hleaf : (∀ s, Klong.time s ∈ n.ks → s ≤ c.i) ∧
      ¬ (n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv w.next)) = false) ∧
      n.firstTime ≠ some c.i ∧ (c.p.M ≤ n.size + 1 → (n.lastVersion c.i).size ≤ c.p.splitAbove) ∧
      wValue base w L = none ∧ L ≠ w.top.rootKey)
    (hparent : (∀ s, Klong.time s ∈ qn.ks → s ≤ c.i) ∧ c.p.M < qn.size + 1 + 1 ∧
      qn.firstTime ≠ some c.i ∧ c.p.splitAbove < (qn.lastVersion c.i).size ∧
      2 ≤ qn.live.length ∧ wValue base w q = none ∧ q ≠ w.top.rootKey)
    (hrange : ∀ c' z, (c', z) ∈ qn.live →
      kq ≤ c' ∧ ∀ c'' z', (c'', z') ∈ gn.live → kq < c'' → c' < c'')
    (hgp : (∀ s, Klong.time s ∈ gn.ks → s ≤ c.i) ∧ gn.size + 2 + 1 ≤ c.p.M ∧
      ∀ y1 sc y2, deadOver c.p ((gn.add c.i (.key kq y1)).add c.i (.key sc y2)) = false)
    (hacyc : ¬ ReachS (wNode c.p base w) c.i q (pathEnd rk S0) ∧
      ¬ ReachS (wNode c.p base w) c.i L (pathEnd rk S0))
    (huniq : ∀ key' x n', keyWf key' = true →
      (x, cv) ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
      (x, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w x = some n' → n'.leaf = true → key' = pre ++ [cv])
    (htreeK : ∀ x xn cc z, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → (cc, z) ∈ xn.liveAt c.i → (wNode c.p base w z).isSome = true →
      ∀ x' xn' cc', ReachS (wNode c.p base w) c.i w.top.rootKey x' →
        wNode c.p base w x' = some xn' → (cc', z) ∈ xn'.liveAt c.i → x = x' ∧ cc = cc')
    (hlinks : ∀ x xn cc z, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → (cc, z) ∈ xn.liveAt c.i → z < w.next) :
    WriterWP (putKv (.put (pre ++ [cv]) h)) c w (fun _ w' => ∀ key', keyWf key' = true →
      wGet c.p c.i base w' key' =
        if Op.key (.put (pre ++ [cv]) h) == key' then Op.value (.put (pre ++ [cv]) h)
        else wGet c.p c.i base w key') := by
  obtain ⟨hidn, hidv, hidt, hidvals, hidr⟩ := hids
  obtain ⟨htimes, hfull, hfirst, hsplit, hLval, hLroot⟩ := hleaf
  obtain ⟨hqt, hqfull, hqfirst, hqsplit, hq2, hqval, hqroot⟩ := hparent
  obtain ⟨hgt, hroomg, hdeadg⟩ := hgp
  have hfuel : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  have hwfR : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → klongsWf xn.ks = true := fun x xn _ hn => hwfG x xn hn
  -- the path's last two steps
  obtain ⟨gn', qn', fdg, fdq, hg', hgl, hgs, hkq, hgy, hq', hql, hqs, hk1, hqy⟩ :=
    PathFrom.last_two _ _ _ S0 rk _ _ q L hpath
  rw [hNg] at hg'; cases hg'
  rw [hNq] at hq'; cases hq'
  obtain ⟨g, hgdef⟩ : ∃ g, g = pathEnd rk S0 := ⟨_, rfl⟩
  rw [← hgdef] at hNg hacyc
  have hqL : q ≠ L := by intro he; subst he; rw [hNq] at hNL; cases hNL; rw [hql] at hnl; cases hnl
  have hgL : g ≠ L := by intro he; rw [he] at hNg; rw [hNL] at hNg; cases hNg; rw [hgl] at hnl; cases hnl
  have hgq : g ≠ q := by
    intro he
    rw [he] at hNg; rw [hNq] at hNg; cases hNg
    rw [hqs] at hgs; cases hgs
    exact hqL (hgy.symm.trans hqy)
  have hrrk : ReachS (wNode c.p base w) c.i w.top.rootKey rk :=
    segRootR_reach _ _ _ _ hwfR pre _ rk ReachS.root hrk
  unfold putKv pathClear findRoot pathAdd
  wpSimplify
  generalize hw2 : ({ ({ w with path := [] } : W) with
    path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w2
  have hr02 : ReadsAs c.p base w w2 := by subst hw2; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hw2n : w2.nodes = w.nodes := by subst hw2; rfl
  refine writerWP_putSegs_prefix_src c base hvc (pre ++ [cv]) (some h) cv _ pre w.top.rootKey rk w2
    (by rw [hr02.1, hr02.2.2.1]; exact ht) (by rw [hr02.1]; exact hrk) (by subst hw2; simp) ?_
  intro w2' hr2' hp2' hsrc2'
  have hr0 := ReadsAs.trans _ _ _ _ _ hr02 hr2'
  unfold setValue
  wpSimplify
  have ht2 : ∀ q ∈ eqVisits (wNode c.p base w2') c.i cv c.p.fuel rk,
      w2'.taken.contains q.1 = false := by
    rw [hr0.1, hr0.2.2.1]
    exact fun q hq => ht q (fromVisits_append _ _ _ pre cv _ rk hrk q hq)
  refine writerWP_mono (writerWP_and (writerWP_and
    (writerWP_descendLte_reads cv c base hvc c.p.fuel rk w2' ht2)
    (writerWP_descendLte_steps cv c base hvc c.p.fuel rk w2' ht2))
    (writerWP_descendLte_cache cv c base hvc c.p.fuel rk w2' ht2)) ?_
  intro L' w3 ⟨⟨⟨hr23, n', hn', hnl', hlk3, hvisL, _⟩, ⟨steps, hpf, hp3, hLe⟩⟩, ⟨hcache3, hsrc3, _⟩⟩
  rw [hr0.1] at hn' hvisL hpf hcache3
  have hr03 := ReadsAs.trans _ _ _ _ _ hr0 hr23
  have hnext3 : w3.next = w.next := hr03.2.2.2.2
  -- the descent is the path g, q, L
  have hend : pathEnd rk (S0 ++ [(some kq, q), (some k1, L)]) = L := by
    rw [show S0 ++ [(some kq, q), (some k1, L)] = (S0 ++ [(some kq, q)]) ++ [(some k1, L)] by simp,
      pathEnd_append]
  have hsteps : steps = S0 ++ [(some kq, q), (some k1, L)] := by
    apply PathFrom.unique_leaf _ _ _ steps rk _ hpf hpath
    · intro m hm; rw [← hLe, hn'] at hm; cases hm; exact hnl'
    · exact ⟨n', by rw [← hLe]; exact hn'⟩
    · intro m hm; rw [hend, hNL] at hm; cases hm; exact hnl
    · exact ⟨n, by rw [hend]; exact hNL⟩
  have hLL : L' = L := by rw [hLe, hsteps, hend]
  clear hLe
  subst L'
  rw [hNL] at hn'; cases hn'
  -- q and g are visited
  have hvis := PathFrom.mem_eqVisits _ _ _ c.p.fuel rk _ hpath
    (fun m hm => by rw [hend, hNL] at hm; cases hm; exact hnl) (by rw [hend]; exact hvisL)
  have hqv : (q, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk :=
    hvis.2 (some kq, q) (by simp)
  have hgv : (g, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk := by
    rw [hgdef]
    cases hS0 : S0.getLast? with
    | none =>
      have : S0 = [] := List.getLast?_eq_none_iff.mp hS0
      subst this; simpa [pathEnd] using hvis.1
    | some e =>
      have hmem : e ∈ S0 := List.mem_of_getLast? hS0
      have := hvis.2 e (by simp [hmem])
      simpa [pathEnd, hS0] using this
  have hlq3 : w3.nodes.lookup q = some qn := hcache3 q qn hqv hNq
  have hlg3 : w3.nodes.lookup g = some gn := hcache3 g gn hgv hNg
  unfold newValue fresh
  wpSimplify
  rw [writerWP_getNode_known L n c _ (by simpa using hlk3)]
  have hcond : (decide (n.size + 1 < c.p.M) && !deadOver c.p (n.add c.i (.key cv w3.next))) = false := by
    rw [hnext3]
    cases hd : deadOver c.p (n.add c.i (.key cv w.next)) with
    | true => simp
    | false =>
      have : ¬ n.size + 1 < c.p.M := fun hlt => hfull ⟨hlt, hd⟩
      simp [this]
  simp only [hcond, Bool.false_eq_true, ↓reduceIte, pathSize, writerWP_bind, writerWP_get,
    writerWP_pure]
  -- ids in the writer's nodes are below the next id
  have hsrcw3 : ∀ z, (w3.nodes.lookup z).isSome = true → z < w.next := by
    intro z hz
    rcases hsrc3 z hz with h1 | h1
    · rcases hsrc2' z h1 with h2 | h2
      · rw [hw2n] at h2; exact hidn z h2
      · exact hidv z h2
    · exact hidv z h1
  -- the access path: ..., g, q, L
  rw [hsteps] at hp3
  have hlastP : (w2'.path ++ S0).getLast?.map (·.2) = some g := by
    rw [hgdef]
    cases hS0 : S0.getLast? with
    | none =>
      have : S0 = [] := List.getLast?_eq_none_iff.mp hS0
      subst this; simpa [pathEnd] using hp2'
    | some e =>
      rw [List.getLast?_append, hS0]
      simp [pathEnd, hS0]
  have hneP : w2'.path ++ S0 ≠ [] := by
    intro he
    have : w2'.path = [] := (List.append_eq_nil_iff.mp he).1
    rw [this] at hp2'; simp at hp2'
  obtain ⟨d'', hd''⟩ : ∃ d'', (w2'.path ++ S0).length = d'' + 1 := by
    cases h' : (w2'.path ++ S0).length with
    | zero => exact absurd (List.eq_nil_of_length_eq_zero h') hneP
    | succ k => exact ⟨k, rfl⟩
  have hp3' : w3.path = (w2'.path ++ S0) ++ [(some kq, q), (some k1, L)] := by
    rw [hp3]; simp
  have hlen : w3.path.length - 1 = d'' + 1 + 1 := by
    rw [hp3']; simp only [List.length_append, List.length_cons, List.length_nil] at hd'' ⊢; omega
  have hpg : (w3.path[d'']?).map (·.2) = some g := by
    rw [hp3', List.getElem?_append_left (by omega)]
    rw [List.getLast?_eq_getElem?, hd''] at hlastP
    simpa using hlastP
  have hpq : w3.path[d'' + 1]? = some (some kq, q) := by
    rw [hp3', List.getElem?_append_right (by omega), hd'']; simp
  have hpk : w3.path[d'' + 1 + 1]? = some (some k1, L) := by
    rw [hp3', List.getElem?_append_right (by omega), hd'']; simp
  have hkqc : fdg.c = kq := by simpa using hkq.symm
  have hk1c : fdq.c = k1 := by simpa using hk1.symm
  have hk1L : (k1, L) ∈ qn.live := by
    have := KNode.searchLte_mem qn c.i cv fdq hqs
    rw [KNode.liveAt_of_times qn c.i hqt, hk1c, hqy] at this; exact this
  have hkqg : (kq, q) ∈ gn.live := by
    have := KNode.searchLte_mem gn c.i cv fdg hgs
    rw [KNode.liveAt_of_times gn c.i hgt, hkqc, hgy] at this; exact this
  have hLlt : L < w.next := hsrcw3 L (by rw [hlk3]; rfl)
  have hny : w3.nodes.lookup (w3.next + 2) = none := by
    cases h' : w3.nodes.lookup (w3.next + 2) with
    | none => rfl
    | some _ => have := hsrcw3 _ (by rw [h']; rfl); omega
  have hny2 : w3.nodes.lookup (w3.next + 2 + 2) = none := by
    cases h' : w3.nodes.lookup (w3.next + 2 + 2) with
    | none => rfl
    | some _ => have := hsrcw3 _ (by rw [h']; rfl); omega
  have hny3 : w3.nodes.lookup (w3.next + 2 + 2 + 2) = none := by
    cases h' : w3.nodes.lookup (w3.next + 2 + 2 + 2) with
    | none => rfl
    | some _ => have := hsrcw3 _ (by rw [h']; rfl); omega
  rw [hlen]
  refine writerWP_mono (writerWP_appendKlongs_timeSpace d'' L q g n qn gn kq k1 cv w3.next c _
    (by simpa using hlk3) (by simpa using hlq3) (by simpa using hlg3) hqL hgq hgL hql hgl hfirst
    hqfirst (by rw [hnext3]; exact hfull) hsplit hqfull hqsplit
    (by simpa using hpg) (by simpa using hpq) (by simpa using hpk) hroomg hdeadg
    (by simpa using hny) (by simpa using hny2) (by simpa using hny3) (by simp only; omega)) ?_
  intro _ wf hTS
  obtain ⟨l, hl_leaf, hl_wf, hl_times, hl_look, hft, hftop, hfv, hfn⟩ := hTS
  simp only at hft hftop hfv hfn
  rw [hr03.2.2.1] at hft
  rw [hr03.2.1] at hftop
  rw [hr03.2.2.2.1, hnext3] at hfv
  rw [hnext3] at hfn hl_look
  -- facts on ids
  have hqlt : q < w.next := hsrcw3 q (by rw [hlq3]; rfl)
  have hglt : g < w.next := hsrcw3 g (by rw [hlg3]; rfl)
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
  have hfreshN : ∀ z, w.next ≤ z → wNode c.p base w z = none := by
    intro z hz
    simp only [wNode, hntake z hz, Bool.false_eq_true, ↓reduceIte, hnodenone z hz,
      (hbase z hz).1]
  have hrq : ReachS (wNode c.p base w) c.i w.top.rootKey q :=
    eqVisits_reach _ _ _ cv c.p.fuel rk q cv hrrk hqv
  have hrg : ReachS (wNode c.p base w) c.i w.top.rootKey g :=
    eqVisits_reach _ _ _ cv c.p.fuel rk g cv hrrk hgv
  have hLt : wf.taken.contains L = false := by
    rw [hft]; exact ht (L, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hvisL)
  have hqtk : wf.taken.contains q = false := by
    rw [hft]; exact ht (q, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hqv)
  have hgtk : wf.taken.contains g = false := by
    rw [hft]; exact ht (g, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hgv)
  have hlm : ({ leaf := n.leaf, ks := l.ks } : KNode) = l := by
    cases l; simp only at hl_leaf ⊢; rw [hl_leaf]
  -- the divider of q's halves
  obtain ⟨r, hr⟩ : ∃ r, (qn.live.drop (qn.live.length / 2)).head? = some r := by
    cases h' : qn.live.drop (qn.live.length / 2) with
    | nil => have := congrArg List.length h'; simp at this; omega
    | cons a _ => exact ⟨a, rfl⟩
  have hsc : 0 < r.1 := by
    obtain ⟨a, ha⟩ : ∃ a, a ∈ qn.live.take (qn.live.length / 2) := by
      cases h' : qn.live.take (qn.live.length / 2) with
      | nil =>
        have := congrArg List.length h'
        rw [List.length_take] at this; simp only [List.length_nil] at this; omega
      | cons a _ => exact ⟨a, by simp⟩
    have := halves_left_lt_divider qn.live _ qn.live_order r hr a ha
    omega
  have hrmem : r ∈ qn.live := List.mem_of_mem_drop (List.mem_of_head? hr)
  have hkqr : kq ≤ r.1 := (hrange r.1 r.2 hrmem).1
  have hgap : ∀ c' z, (c', z) ∈ gn.live → c' ≤ kq ∨ r.1 < c' := by
    intro c' z hcz
    by_cases hle : c' ≤ kq
    · exact Or.inl hle
    · exact Or.inr ((hrange r.1 r.2 hrmem).2 c' z hcz (by omega))
  have hres := getFromR_timeSpace (wNode c.p base w) (wNode c.p base wf) (wValue base w)
    (wValue base wf) c.i c.p.fuel hfuel w.top.rootKey L q g (w.next + 2) (w.next + 2 + 2)
    (w.next + 2 + 2 + 2) w.next n qn gn ⟨n.leaf, l.ks⟩ k1 kq pre cv h rk r hr hsc hwfG hNL hnl
    htimes hNq hql hqt hk1L hNg hgl hgt hkqg hkqr hgap
    (by
      have hyt : wf.taken.contains (w.next + 2) = false := by rw [hft]; exact hntake _ (by omega)
      simp only [wNode, hyt, Bool.false_eq_true, ↓reduceIte, hfn,
        show w.next + 2 ≠ L by omega, show w.next + 2 ≠ q by omega, show w.next + 2 ≠ g by omega])
    hnl (by rw [hlm]; exact hl_wf) (by rw [hlm]; exact hl_times)
    (by intro c'; rw [hlm, hl_look c'])
    (by simp only [wNode, hgtk, Bool.false_eq_true, ↓reduceIte, hfn, hgL, hgq])
    (by
      have hyt : wf.taken.contains (w.next + 2 + 2) = false := by
        rw [hft]; exact hntake _ (by omega)
      simp only [wNode, hyt, Bool.false_eq_true, ↓reduceIte, hfn,
        show w.next + 2 + 2 ≠ L by omega, show w.next + 2 + 2 ≠ q by omega,
        show w.next + 2 + 2 ≠ g by omega, show w.next + 2 + 2 ≠ w.next + 2 by omega])
    (by
      have hyt : wf.taken.contains (w.next + 2 + 2 + 2) = false := by
        rw [hft]; exact hntake _ (by omega)
      simp only [wNode, hyt, Bool.false_eq_true, ↓reduceIte, hfn,
        show w.next + 2 + 2 + 2 ≠ L by omega, show w.next + 2 + 2 + 2 ≠ q by omega,
        show w.next + 2 + 2 + 2 ≠ g by omega, show w.next + 2 + 2 + 2 ≠ w.next + 2 by omega,
        show w.next + 2 + 2 + 2 ≠ w.next + 2 + 2 by omega])
    (by
      intro m hm
      simp only [wNode, hLt, Bool.false_eq_true, ↓reduceIte, hfn, Option.some.injEq] at hm
      rw [← hm]; exact KNode.toPrev_wf n _ (hwfG L n hNL))
    (by
      intro x hxL hxq hxg hxY hxF hxS
      rw [← hr03.1]
      simp only [wNode, hft, hfn, hxL, hxq, hxg, hxY, hxF, hxS, ↓reduceIte, hr03.2.2.1])
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
        hvalnone _ (by omega : w.next ≤ w.next + 2), (hbase (w.next + 2) (by omega)).2])
    hqL (by omega) (by omega) hgq hgL (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (hfreshN _ (Nat.le_refl _)) (hfreshN _ (by omega)) (hfreshN _ (by omega)) (hfreshN _ (by omega))
    hLroot.symm (by omega) hqroot.symm (by omega) (by omega) (by omega)
    hrq hrg hacyc.1 hacyc.2 hrk (keyWf_last_notin pre cv hkey) hvisL huniq
    (fun x xn c' hx hxn hz => htreeK x xn c' L hx hxn hz (by simp [hNL]) q qn k1 hrq hNq
      (by rw [KNode.liveAt_of_times qn c.i hqt]; exact hk1L))
    (fun x xn c' hx hxn hz => htreeK x xn c' q hx hxn hz (by simp [hNq]) g gn kq hrg hNg
      (by rw [KNode.liveAt_of_times gn c.i hgt]; exact hkqg))
    (fun x xn cc z hx hxn hz => by
      have := hlinks x xn cc z hx hxn hz
      exact ⟨by omega, by omega, by omega, by omega⟩)
  intro key' hkey'
  unfold wGet
  rw [hftop, hres key' hkey']
  simp only [Op.key, Op.value]
  rfl

end SIS.Tree
