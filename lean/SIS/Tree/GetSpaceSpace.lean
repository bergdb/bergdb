import SIS.Tree.GetInnerSplit

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! The space split of an inner node after a space split below it (bergdb
024-12, TP10; the cascades): the halves of an inner node's last version with
klongs put on one side of its divider find what the node with the klongs
found, by compare value (`halves_inner_searchLte_ins`). -/

theorem halves_inner_searchLte_ins (qn Q : KNode) (t : Time) (ins : List (Nat × NodeId))
    (hql : qn.leaf = false)
    (r : Nat × NodeId) (hr : (qn.live.drop (qn.live.length / 2)).head? = some r) (hsc : 0 < r.1)
    (hside : (∀ q ∈ ins, r.1 ≤ q.1) ∨ (∀ q ∈ ins, q.1 < r.1))
    (hQt : ∀ s, Klong.time s ∈ Q.ks → s ≤ t)
    (hQlook : ∀ c, Q.live.lookup c = ins.foldl (pairLookupStep c) (qn.live.lookup c)) :
    let out := halves qn.leaf t (qn.lastVersion t) ins
    out.2.2 = r.1 ∧ out.1.leaf = false ∧ out.2.1.leaf = false ∧
      klongsWf out.1.ks = true ∧ klongsWf out.2.1.ks = true ∧
      (∀ s, Klong.time s ∈ out.1.ks → s ≤ t) ∧ (∀ s, Klong.time s ∈ out.2.1.ks → s ≤ t) ∧
      (∀ c : Nat, c < r.1 → (out.1.searchLte t c).map (·.y) =
        (Q.searchLte t c).map (·.y)) ∧
      (∀ c : Nat, r.1 ≤ c → (out.2.1.searchLte t c).map (·.y) =
        (Q.searchLte t c).map (·.y)) := by
  intro out
  have hlv := KNode.lastVersion_eq_newKlongs qn t
  rw [hql] at hlv
  have hout : out = halves false t ⟨false, newKlongs t qn.live⟩ ins := by
    simp only [out, hql, hlv]
  have hs : CvSorted qn.live := qn.live_order
  have hshape := halves_shape false t qn.live ins r hr
  have hside' : ∀ q ∈ ins, decide (r.1 ≤ q.1) =
      (match ins.head? with | some a => decide (r.1 ≤ a.1) | none => false) := by
    intro q hq
    cases hins : ins with
    | nil => rw [hins] at hq; cases hq
    | cons a rest =>
      rw [hins] at hq hside
      simp only [List.head?_cons]
      rcases hside with h | h
      · simp [h q hq, h a List.mem_cons_self]
      · have h1 := h q hq
        have h2 := h a List.mem_cons_self
        simp only [decide_eq_decide]
        omega
  have hlook := halves_lookup false t qn.live ins hs r hr hsc hside'
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
    have htrue : (∀ a ∈ ins, r.1 ≤ a.1) →
        ∀ (A : KNode × KNode × Nat), A = (⟨false, newKlongs t (qn.live.take (qn.live.length / 2))⟩,
          ⟨false, newKlongs t (secondSplitPairs false qn.live ++
            ins.map (fun q => (splitLocalCv false r.1 q.1, q.2)))⟩, r.1) →
        A.2.2 = r.1 ∧ A.1.leaf = false ∧
        A.2.1.leaf = false ∧ klongsWf A.1.ks = true ∧ klongsWf A.2.1.ks = true ∧
        (∀ s, Klong.time s ∈ A.1.ks → s ≤ t) ∧ (∀ s, Klong.time s ∈ A.2.1.ks → s ≤ t) ∧
        (∀ c z, (c, z) ∈ A.1.live → c < r.1) ∧
        (∀ c z, (c, z) ∈ A.2.1.live → c = 0 ∨ r.1 < c) := by
      intro hin A hA
      subst hA
      refine ⟨rfl, rfl, rfl, klongsWf_newKlongs _ _, klongsWf_newKlongs _ _, htimesNK _, htimesNK _,
        ?_, ?_⟩
      · intro c z hcz
        exact hleft (c, z) (newKlongs_live_mem false t _ c z hcz)
      · intro c z hcz
        have := newKlongs_live_mem false t _ c z hcz
        rcases List.mem_append.mp this with h1 | h1
        · exact hsec c z h1
        · obtain ⟨a, ha, hae⟩ := List.mem_map.mp h1
          have hra : r.1 ≤ a.1 := hin a ha
          simp only [Prod.mk.injEq] at hae
          rw [← hae.1]
          simp only [splitLocalCv, Bool.not_false, Bool.true_and]
          by_cases hk : a.1 = r.1
          · simp [hk]
          · have hk' : (a.1 == r.1) = false := by simpa using hk
            simp only [hk', Bool.false_eq_true, ↓reduceIte]
            right; omega
    have hfalse : (∀ a ∈ ins, a.1 < r.1) →
        ∀ (A : KNode × KNode × Nat), A = (⟨false, newKlongs t (qn.live.take (qn.live.length / 2) ++ ins)⟩,
          ⟨false, newKlongs t (secondSplitPairs false qn.live)⟩, r.1) →
        A.2.2 = r.1 ∧ A.1.leaf = false ∧
        A.2.1.leaf = false ∧ klongsWf A.1.ks = true ∧ klongsWf A.2.1.ks = true ∧
        (∀ s, Klong.time s ∈ A.1.ks → s ≤ t) ∧ (∀ s, Klong.time s ∈ A.2.1.ks → s ≤ t) ∧
        (∀ c z, (c, z) ∈ A.1.live → c < r.1) ∧
        (∀ c z, (c, z) ∈ A.2.1.live → c = 0 ∨ r.1 < c) := by
      intro hin A hA
      subst hA
      refine ⟨rfl, rfl, rfl, klongsWf_newKlongs _ _, klongsWf_newKlongs _ _, htimesNK _, htimesNK _,
        ?_, ?_⟩
      · intro c z hcz
        have := newKlongs_live_mem false t _ c z hcz
        rcases List.mem_append.mp this with h1 | h1
        · exact hleft (c, z) h1
        · exact hin (c, z) h1
      · intro c z hcz
        exact hsec c z (newKlongs_live_mem false t _ c z hcz)
    rw [hshape]
    split
    · rename_i a hhead
      have ha : a ∈ ins := List.mem_of_head? hhead
      split
      · rename_i hc
        simp only [decide_eq_true_eq] at hc
        refine htrue ?_ _ rfl
        intro b hb
        rcases hside with h | h
        · exact h b hb
        · have := h a ha; omega
      · rename_i hc
        simp only [decide_eq_true_eq] at hc
        refine hfalse ?_ _ rfl
        intro b hb
        rcases hside with h | h
        · have := h a ha; omega
        · exact h b hb
    · rename_i hhead
      have hnil : ins = [] := List.head?_eq_none_iff.mp hhead
      exact hfalse (by rw [hnil]; intro b hb; cases hb) _ rfl
  rw [hsc'] at hlook
  -- the parent with the klongs, as a lookup
  have hQlook' := hQlook
  have hmemQ : ∀ a z, (a, z) ∈ Q.live ↔ Q.live.lookup a = some z :=
    fun a z => mem_iff_lookup _ (KNode.live_keys_nodup _) a z
  have hmem1 : ∀ a z, (a, z) ∈ out.1.live ↔ out.1.live.lookup a = some z :=
    fun a z => mem_iff_lookup _ (KNode.live_keys_nodup _) a z
  have hmem2 : ∀ a z, (a, z) ∈ out.2.1.live ↔ out.2.1.live.lookup a = some z :=
    fun a z => mem_iff_lookup _ (KNode.live_keys_nodup _) a z
  -- below r.1 the first half and the parent agree
  have hlow : ∀ a z, a < r.1 → ((a, z) ∈ out.1.live ↔ (a, z) ∈ Q.live) := by
    intro a z ha
    rw [hmem1, hmemQ, hQlook', ← hlook a]
    simp [ha]
  -- from r.1 on the second half and the parent agree, r.1 named the empty key
  have hspl : ∀ a, r.1 ≤ a → splitLocalCv false r.1 a = if a = r.1 then 0 else a := by
    intro a _
    simp only [splitLocalCv, Bool.not_false, Bool.true_and]
    by_cases h : a = r.1
    · simp [h]
    · have h' : (a == r.1) = false := by simpa using h
      simp [h', h]
  have hhigh : ∀ a z, r.1 < a → ((a, z) ∈ out.2.1.live ↔ (a, z) ∈ Q.live) := by
    intro a z ha
    rw [hmem2, hmemQ, hQlook', ← hlook a, hspl a (by omega)]
    simp [show ¬ a < r.1 by omega, show a ≠ r.1 by omega]
  have hzero : ∀ z, (0, z) ∈ out.2.1.live ↔ (r.1, z) ∈ Q.live := by
    intro z
    rw [hmem2, hmemQ, hQlook', ← hlook r.1, hspl r.1 (Nat.le_refl _)]
    simp
  have hsQ := Q.searchLte_spec t
  refine ⟨hsc', hl1, hl2, hw1, hw2, ht1, ht2, ?_, ?_⟩
  · intro c hc
    have hs := hsQ c
    unfold NodeSearchSpec at hs
    rw [KNode.liveAt_of_times _ t hQt] at hs
    cases hq : Q.searchLte t c with
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
    obtain ⟨zr, hzr⟩ : ∃ z, (r.1, z) ∈ Q.live := by
      have hrm : r ∈ qn.live := List.mem_of_mem_drop (List.mem_of_head? hr)
      have hl := lookup_some_of_mem (KNode.live_keys_nodup qn) hrm
      have hq := hQlook r.1
      rw [hl, pairLookupFold_reverse] at hq
      cases hx : ins.reverse.lookup r.1 with
      | none => rw [hx] at hq; exact ⟨r.2, (hmemQ _ _).mpr hq⟩
      | some y => rw [hx] at hq; exact ⟨y, (hmemQ _ _).mpr hq⟩
    cases hq : Q.searchLte t c with
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

/-! ## The writer: a space split of a node with any klongs to put -/

/-- `SpaceSplitAfter` for any klongs to put. -/
def SpaceSplitAfterIns (c : Ctx) (w w' : W) (L q : NodeId) (n qn : KNode) (k1 : Nat)
    (ins : List (Nat × NodeId)) : Prop :=
  w'.taken = w.taken ∧ w'.top = w.top ∧ w'.vals = w.vals ∧
    ∀ x, w'.nodes.lookup x =
      if x = L then some (n.toPrev (c.i - 1))
      else if x = q then some ((qn.add c.i (.key k1 w.next)).add c.i
        (.key (halves n.leaf c.i (n.lastVersion c.i) ins).2.2 (w.next + 2)))
      else if x = w.next then some (halves n.leaf c.i (n.lastVersion c.i) ins).1
      else if x = w.next + 2 then some (halves n.leaf c.i (n.lastVersion c.i) ins).2.1
      else w.nodes.lookup x

set_option linter.unusedSimpArgs false in
theorem writerWP_handleFullWith_spaceSplitIns (d' : Nat) (L q : NodeId) (n qn : KNode)
    (k1 : Nat) (ins : List (Nat × NodeId)) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hlq : w.nodes.lookup q = some qn)
    (hqL : q ≠ L) (hql : qn.leaf = false) (hfirst : n.firstTime ≠ some c.i)
    (hsplit : c.p.splitAbove < (n.lastVersion c.i).size)
    (hpq : (w.path[d']?).map (·.2) = some q) (hpk : w.path[d' + 1]? = some (some k1, L))
    (hroomq : qn.size + 2 + 1 ≤ c.p.M)
    (hdeadq : ∀ y1 sc y2, deadOver c.p ((qn.add c.i (.key k1 y1)).add c.i (.key sc y2)) = false)
    (hn1 : w.nodes.lookup w.next = none) (hn2 : w.nodes.lookup (w.next + 2) = none) :
    WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) L ins
      (n.lastVersion c.i) false) c w
      (fun _ w' => SpaceSplitAfterIns c w w' L q n qn k1 ins) := by
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
    have hsz : decide ((n.lastVersion c.i).size > c.p.splitAbove) = true := by
      simpa using hsplit
    simp only [writerWP_pure, hql, hsz, Bool.not_false, Bool.true_and, ↓reduceIte,
      Bool.false_eq_true]
    simp only [newKey, fresh, setMadeFor, klongAt, note, writerWP_bind, writerWP_modify,
      writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
    split
    all_goals (try split)
    all_goals (
      simp only [writerWP_bind, writerWP_modify, writerWP_pure, hpk, putNode]
      refine writerWP_mono (writerWP_appendKlongs_room2 d' q qn k1 w.next _ (w.next + 2) c _
        (by
          simp only [lookup_upsert]
          have h1 : q ≠ w.next + 2 := fun h => by rw [h, hn2] at hlq; cases hlq
          have h2 : q ≠ w.next := fun h => by rw [h, hn1] at hlq; cases hlq
          simp [h1, h2, List.lookup_append, hlq]) hroomq (hdeadq _ _ _)) ?_
      intro _ w2 hw2
      subst hw2
      rw [writerWP_getNode_known L n c _ (by
        simp only [lookup_upsert]
        have h1 : L ≠ w.next + 2 := fun h => by rw [h, hn2] at hlk; cases hlk
        have h2 : L ≠ w.next := fun h => by rw [h, hn1] at hlk; cases hlk
        simp [hqL.symm, h1, h2, List.lookup_append, hlk])]
      simp only [putNode, writerWP_modify]
      refine ⟨rfl, rfl, rfl, ?_⟩
      intro x
      simp only [lookup_upsert, List.lookup_append]
      by_cases hxL : x = L
      · simp [hxL]
      · simp only [hxL, ↓reduceIte]
        by_cases hxq : x = q
        · simp [hxq]
        · simp only [hxq, ↓reduceIte]
          by_cases hx2 : x = w.next + 2
          · have hx1 : x ≠ w.next := by omega
            simp [hx2]
          · simp only [hx2, ↓reduceIte]
            by_cases hx1 : x = w.next
            · simp [hx1]
            · simp only [hx1, ↓reduceIte]
              cases h : w.nodes.lookup x with
              | some m => rfl
              | none =>
                have hb1 : (x == w.next) = false := by simpa using hx1
                have hb2 : (x == w.next + 2) = false := by simpa using hx2
                simp [List.lookup, hb1, hb2])

theorem writerWP_appendKlongs_spaceSplitIns (d' : Nat) (L q : NodeId) (n qn : KNode)
    (k1 : Nat) (ins : List (Nat × NodeId)) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hlq : w.nodes.lookup q = some qn)
    (hqL : q ≠ L) (hql : qn.leaf = false) (hfirst : n.firstTime ≠ some c.i)
    (hfull : c.p.M < n.size + ins.length + 1)
    (hsplit : c.p.splitAbove < (n.lastVersion c.i).size)
    (hpq : (w.path[d']?).map (·.2) = some q) (hpk : w.path[d' + 1]? = some (some k1, L))
    (hroomq : qn.size + 2 + 1 ≤ c.p.M)
    (hdeadq : ∀ y1 sc y2, deadOver c.p ((qn.add c.i (.key k1 y1)).add c.i (.key sc y2)) = false)
    (hn1 : w.nodes.lookup w.next = none) (hn2 : w.nodes.lookup (w.next + 2) = none) :
    WriterWP (appendKlongs (d' + 1) L ins) c w
      (fun _ w' => SpaceSplitAfterIns c w w' L q n qn k1 ins) := by
  rw [appendKlongs_step_dead]
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w hlk]
  have hf : (n.size + ins.length + 1 > c.p.M) := by omega
  simp only [hf, ↓reduceIte]
  exact writerWP_handleFullWith_spaceSplitIns d' L q n qn k1 ins c w hlk hlq hqL hql hfirst hsplit
    hpq hpk hroomq hdeadq hn1 hn2

/-! ## The writer: a space split of a leaf whose inner parent is full and space split -/

/-- The state after a space split of the leaf L whose parent q, full, is space
split too, below the grandparent g with room: L's halves at the next two ids,
q's halves with the klongs to L's at the two ids after, g's klong kq names q's
first half and a new klong its second; L and q keep their klongs before the
transaction. -/
def SpaceSpaceAfter (c : Ctx) (w w' : W) (L q g : NodeId) (n qn gn : KNode)
    (kq k1 cv v : Nat) : Prop :=
  w'.taken = w.taken ∧ w'.top = w.top ∧ w'.vals = w.vals ∧
    ∀ x, w'.nodes.lookup x =
      if x = L then some (n.toPrev (c.i - 1))
      else if x = q then some (qn.toPrev (c.i - 1))
      else if x = g then some ((gn.add c.i (.key kq (w.next + 2 + 2))).add c.i
        (.key (halves qn.leaf c.i (qn.lastVersion c.i) [(k1, w.next),
          ((halves n.leaf c.i (n.lastVersion c.i) [(cv, v)]).2.2, w.next + 2)]).2.2
          (w.next + 2 + 2 + 2)))
      else if x = w.next then some (halves n.leaf c.i (n.lastVersion c.i) [(cv, v)]).1
      else if x = w.next + 2 then some (halves n.leaf c.i (n.lastVersion c.i) [(cv, v)]).2.1
      else if x = w.next + 2 + 2 then some (halves qn.leaf c.i (qn.lastVersion c.i) [(k1, w.next),
          ((halves n.leaf c.i (n.lastVersion c.i) [(cv, v)]).2.2, w.next + 2)]).1
      else if x = w.next + 2 + 2 + 2 then some (halves qn.leaf c.i (qn.lastVersion c.i)
          [(k1, w.next), ((halves n.leaf c.i (n.lastVersion c.i) [(cv, v)]).2.2, w.next + 2)]).2.1
      else w.nodes.lookup x

set_option linter.unusedSimpArgs false in
theorem writerWP_handleFullWith_spaceSpace (d'' : Nat) (L q g : NodeId) (n qn gn : KNode)
    (kq k1 cv v : Nat) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hlq : w.nodes.lookup q = some qn)
    (hlg : w.nodes.lookup g = some gn)
    (hqL : q ≠ L) (hgq : g ≠ q) (hgL : g ≠ L) (hql : qn.leaf = false) (hgl : gn.leaf = false)
    (hfirst : n.firstTime ≠ some c.i) (hqfirst : qn.firstTime ≠ some c.i)
    (hsplit : c.p.splitAbove < (n.lastVersion c.i).size)
    (hqfull : c.p.M < qn.size + 2 + 1)
    (hqsplit : c.p.splitAbove < (qn.lastVersion c.i).size)
    (hpg : (w.path[d'']?).map (·.2) = some g) (hpq : w.path[d'' + 1]? = some (some kq, q))
    (hpk : w.path[d'' + 1 + 1]? = some (some k1, L))
    (hroomg : gn.size + 2 + 1 ≤ c.p.M)
    (hdeadg : ∀ y1 sc y2, deadOver c.p ((gn.add c.i (.key kq y1)).add c.i (.key sc y2)) = false)
    (hn1 : w.nodes.lookup w.next = none) (hn2 : w.nodes.lookup (w.next + 2) = none)
    (hn3 : w.nodes.lookup (w.next + 2 + 2) = none)
    (hn4 : w.nodes.lookup (w.next + 2 + 2 + 2) = none) :
    WriterWP (handleFullWith (fun q more => appendKlongs (d'' + 1) q more) (d'' + 1 + 1) L [(cv, v)]
      (n.lastVersion c.i) false) c w
      (fun _ w' => SpaceSpaceAfter c w w' L q g n qn gn kq k1 cv v) := by
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
    have hsz : decide ((n.lastVersion c.i).size > c.p.splitAbove) = true := by
      simpa using hsplit
    simp only [writerWP_pure, hql, hsz, Bool.not_false, Bool.true_and, ↓reduceIte,
      Bool.false_eq_true]
    have hq1 : q ≠ w.next := fun h => by rw [h, hn1] at hlq; cases hlq
    have hq2 : q ≠ w.next + 2 := fun h => by rw [h, hn2] at hlq; cases hlq
    have hq3 : q ≠ w.next + 2 + 2 := fun h => by rw [h, hn3] at hlq; cases hlq
    have hg1 : g ≠ w.next := fun h => by rw [h, hn1] at hlg; cases hlg
    have hg2 : g ≠ w.next + 2 := fun h => by rw [h, hn2] at hlg; cases hlg
    have hg3 : g ≠ w.next + 2 + 2 := fun h => by rw [h, hn3] at hlg; cases hlg
    have hL1 : L ≠ w.next := fun h => by rw [h, hn1] at hlk; cases hlk
    have hL2 : L ≠ w.next + 2 := fun h => by rw [h, hn2] at hlk; cases hlk
    have hL3 : L ≠ w.next + 2 + 2 := fun h => by rw [h, hn3] at hlk; cases hlk
    have hq4 : q ≠ w.next + 2 + 2 + 2 := fun h => by rw [h, hn4] at hlq; cases hlq
    have hg4 : g ≠ w.next + 2 + 2 + 2 := fun h => by rw [h, hn4] at hlg; cases hlg
    have hL4 : L ≠ w.next + 2 + 2 + 2 := fun h => by rw [h, hn4] at hlk; cases hlk
    have hb41 : (w.next + 2 + 2 + 2 == w.next) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; omega
    have hb42 : (w.next + 2 + 2 + 2 == w.next + 2) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; omega
    have hb31 : (w.next + 2 + 2 == w.next) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; omega
    have hb32 : (w.next + 2 + 2 == w.next + 2) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; omega
    simp only [newKey, fresh, setMadeFor, klongAt, note, writerWP_bind, writerWP_modify,
      writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
    split
    all_goals (try split)
    all_goals (
      simp only [writerWP_bind, writerWP_modify, writerWP_pure, hpk, putNode]
      refine writerWP_mono (writerWP_appendKlongs_spaceSplitIns d'' q g qn gn kq
        [(k1, w.next), ((halves n.leaf c.i (n.lastVersion c.i) [(cv, v)]).2.2, w.next + 2)] c _
        (by simp [lookup_upsert, hq1, hq2, List.lookup_append, hlq])
        (by simp [lookup_upsert, hg1, hg2, List.lookup_append, hlg])
        hgq hgl hqfirst (by simpa using hqfull) hqsplit hpg hpq hroomg hdeadg
        (by
          simp only [lookup_upsert, show w.next + 2 + 2 ≠ w.next + 2 by omega,
            show w.next + 2 + 2 ≠ w.next by omega, ↓reduceIte, List.lookup_append, hn3]
          simp [List.lookup, hb31, hb32])
        (by
          simp only [lookup_upsert, show w.next + 2 + 2 + 2 ≠ w.next + 2 by omega,
            show w.next + 2 + 2 + 2 ≠ w.next by omega, ↓reduceIte, List.lookup_append, hn4]
          simp [List.lookup, hb41, hb42])) ?_
      intro _ w2 ⟨h2t, h2top, h2v, h2n⟩
      rw [writerWP_getNode_known L n c _ (by
        rw [h2n]
        simp [hqL.symm, hgL.symm, hL1, hL2, hL3, hL4, lookup_upsert, List.lookup_append, hlk])]
      try simp only [putNode, writerWP_modify]
      refine ⟨h2t, h2top, h2v, ?_⟩
      intro x
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
          · simp only [hxg, ↓reduceIte]
            by_cases hx4 : x = w.next + 2 + 2 + 2
            · simp [hx4, show w.next + 2 + 2 + 2 ≠ w.next by omega,
                show w.next + 2 + 2 + 2 ≠ w.next + 2 by omega,
                show w.next + 2 + 2 + 2 ≠ w.next + 2 + 2 by omega,
                show w.next + 2 + 2 ≠ w.next by omega]
            · simp only [hx4, ↓reduceIte]
              by_cases hx3 : x = w.next + 2 + 2
              · simp [hx3, show w.next + 2 + 2 ≠ w.next by omega,
                  show w.next + 2 + 2 ≠ w.next + 2 by omega]
              · simp only [hx3, ↓reduceIte, lookup_upsert, List.lookup_append]
                by_cases hx2 : x = w.next + 2
                · have hx1 : x ≠ w.next := by omega
                  simp [hx2]
                · simp only [hx2, ↓reduceIte]
                  by_cases hx1 : x = w.next
                  · simp [hx1]
                  · simp only [hx1, ↓reduceIte]
                    cases h : w.nodes.lookup x with
                    | some m => rfl
                    | none =>
                      have hb1 : (x == w.next) = false := by simpa using hx1
                      have hb2 : (x == w.next + 2) = false := by simpa using hx2
                      simp [List.lookup, hb1, hb2])

theorem writerWP_appendKlongs_spaceSpace (d'' : Nat) (L q g : NodeId) (n qn gn : KNode)
    (kq k1 cv v : Nat) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hlq : w.nodes.lookup q = some qn)
    (hlg : w.nodes.lookup g = some gn)
    (hqL : q ≠ L) (hgq : g ≠ q) (hgL : g ≠ L) (hql : qn.leaf = false) (hgl : gn.leaf = false)
    (hfirst : n.firstTime ≠ some c.i) (hqfirst : qn.firstTime ≠ some c.i)
    (hfull : c.p.M ≤ n.size + 1)
    (hsplit : c.p.splitAbove < (n.lastVersion c.i).size)
    (hqfull : c.p.M < qn.size + 2 + 1)
    (hqsplit : c.p.splitAbove < (qn.lastVersion c.i).size)
    (hpg : (w.path[d'']?).map (·.2) = some g) (hpq : w.path[d'' + 1]? = some (some kq, q))
    (hpk : w.path[d'' + 1 + 1]? = some (some k1, L))
    (hroomg : gn.size + 2 + 1 ≤ c.p.M)
    (hdeadg : ∀ y1 sc y2, deadOver c.p ((gn.add c.i (.key kq y1)).add c.i (.key sc y2)) = false)
    (hny : w.nodes.lookup w.next = none) (hny2 : w.nodes.lookup (w.next + 2) = none)
    (hny3 : w.nodes.lookup (w.next + 2 + 2) = none)
    (hny4 : w.nodes.lookup (w.next + 2 + 2 + 2) = none) :
    WriterWP (appendKlongs (d'' + 1 + 1) L [(cv, v)]) c w
      (fun _ w' => SpaceSpaceAfter c w w' L q g n qn gn kq k1 cv v) := by
  rw [appendKlongs_step_dead]
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w hlk]
  have h1 : n.size + [(cv, v)].length + 1 > c.p.M := by simp; omega
  simp only [h1, ↓reduceIte]
  exact writerWP_handleFullWith_spaceSpace d'' L q g n qn gn kq k1 cv v c w hlk hlq hlg hqL hgq
    hgL hql hgl hfirst hqfirst hsplit hqfull hqsplit hpg hpq hpk hroomg hdeadg hny hny2 hny3 hny4

/-- The reading after a space split of a leaf L whose parent q is full and space
split too, below the grandparent g with room (the halves F, S of L, Fq, Sq of
q with the klongs to F and S): the put alone. -/
theorem getFromR_spaceSpace (N N2 : NodeId → Option KNode) (V V2 : NodeId → Option Nat)
    (i : Time) (fuel : Nat) (hfuel : 1 ≤ fuel) (root L q g F S Fq Sq v : NodeId)
    (n qn gn : KNode) (k1 kq : Nat) (pre : List Nat) (cv h : Nat) (rk : NodeId)
    (r : Nat × NodeId) (hr : (qn.live.drop (qn.live.length / 2)).head? = some r) (hsc : 0 < r.1)
    (hwfG : ∀ x xn, N x = some xn → klongsWf xn.ks = true)
    (hNL : N L = some n) (hnl : n.leaf = true) (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ i)
    (hlive : n.live ≠ [])
    (hNq : N q = some qn) (hql : qn.leaf = false) (hqt : ∀ s, Klong.time s ∈ qn.ks → s ≤ i)
    (hk1 : (k1, L) ∈ qn.live)
    (hrange : ∀ c' z, (c', z) ∈ n.live →
      k1 ≤ c' ∧ ∀ c'' z', (c'', z') ∈ qn.live → k1 < c'' → c' < c'')
    (hNg : N g = some gn) (hgl : gn.leaf = false) (hgt : ∀ s, Klong.time s ∈ gn.ks → s ≤ i)
    (hkq : (kq, q) ∈ gn.live) (hkqr : kq ≤ r.1)
    (hgap : ∀ c' z, (c', z) ∈ gn.live → c' ≤ kq ∨ r.1 < c')
    (hside : (∀ a ∈ [(k1, F), ((halves n.leaf i (n.lastVersion i) [(cv, v)]).2.2, S)], r.1 ≤ a.1) ∨
      (∀ a ∈ [(k1, F), ((halves n.leaf i (n.lastVersion i) [(cv, v)]).2.2, S)], a.1 < r.1))
    (hN2F : N2 F = some (halves n.leaf i (n.lastVersion i) [(cv, v)]).1)
    (hN2S : N2 S = some (halves n.leaf i (n.lastVersion i) [(cv, v)]).2.1)
    (hN2g : N2 g = some ((gn.add i (.key kq Fq)).add i
      (.key (halves qn.leaf i (qn.lastVersion i)
        [(k1, F), ((halves n.leaf i (n.lastVersion i) [(cv, v)]).2.2, S)]).2.2 Sq)))
    (hN2Fq : N2 Fq = some (halves qn.leaf i (qn.lastVersion i)
      [(k1, F), ((halves n.leaf i (n.lastVersion i) [(cv, v)]).2.2, S)]).1)
    (hN2Sq : N2 Sq = some (halves qn.leaf i (qn.lastVersion i)
      [(k1, F), ((halves n.leaf i (n.lastVersion i) [(cv, v)]).2.2, S)]).2.1)
    (hN2 : ∀ x, x ≠ L → x ≠ q → x ≠ g → x ≠ F → x ≠ S → x ≠ Fq → x ≠ Sq → N2 x = N x)
    (hV2v : V2 v = some h) (hV2 : ∀ a, a ≠ v → V2 a = V a)
    (hqL : q ≠ L) (hgq : g ≠ q) (hgL : g ≠ L) (hgF : g ≠ F) (hgS : g ≠ S)
    (hFL : F ≠ L) (hSL : S ≠ L) (hFq : F ≠ q) (hSq : S ≠ q) (hFS : F ≠ S)
    (hFqq : Fq ≠ q) (hFqg : Fq ≠ g) (hFqF : Fq ≠ F) (hFqS : Fq ≠ S)
    (hSqq : Sq ≠ q) (hSqg : Sq ≠ g) (hSqF : Sq ≠ F) (hSqS : Sq ≠ S) (hFqSq : Fq ≠ Sq)
    (hvL : v ≠ L) (hvq : v ≠ q) (hvF : v ≠ F) (hvS : v ≠ S) (hvFq : v ≠ Fq) (hvSq : v ≠ Sq)
    (hNv : N v = none) (hNF : N F = none) (hNS : N S = none) (hNFq : N Fq = none)
    (hNSq : N Sq = none)
    (hrootL : root ≠ L) (hrootF : root ≠ F) (hrootS : root ≠ S) (hrootq : root ≠ q)
    (hrootFq : root ≠ Fq) (hrootSq : root ≠ Sq) (hrootv : root ≠ v)
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
      z ≠ v ∧ z ≠ F ∧ z ≠ S ∧ z ≠ Fq ∧ z ≠ Sq) :
    ∀ key', keyWf key' = true → getFromR N2 V2 i fuel key' root =
      if pre ++ [cv] == key' then some h else getFromR N V i fuel key' root := by
  have hwfR : ∀ x xn, ReachS N i root x → N x = some xn → klongsWf xn.ks = true :=
    fun x xn _ hn => hwfG x xn hn
  have hnwf := hwfG L n hNL
  have hqwf := hwfG q qn hNq
  have hgwf := hwfG g gn hNg
  let sc := (halves n.leaf i (n.lastVersion i) [(cv, v)]).2.2
  let q2 : KNode := (qn.add i (.key k1 F)).add i (.key sc S)
  let N1 : NodeId → Option KNode := fun x =>
    if x = q then some q2 else if x = g then some gn
    else if x = Fq then none else if x = Sq then none else N2 x
  have hN1q : N1 q = some q2 := by simp [N1]
  have hN1g : N1 g = some gn := by simp [N1, hgq]
  have hN1F : N1 F = some (halves n.leaf i (n.lastVersion i) [(cv, v)]).1 := by
    simp [N1, hFq, hgF.symm, hFqF.symm, hSqF.symm, hN2F]
  have hN1S : N1 S = some (halves n.leaf i (n.lastVersion i) [(cv, v)]).2.1 := by
    simp [N1, hSq, hgS.symm, hFqS.symm, hSqS.symm, hN2S]
  have hN1Fq : N1 Fq = none := by simp [N1, hFqq, hFqg]
  have hN1Sq : N1 Sq = none := by simp [N1, hSqq, hSqg]
  have hN1 : ∀ x, x ≠ L → x ≠ q → x ≠ F → x ≠ S → N1 x = N x := by
    intro x h1 h2 h3 h4
    by_cases hxg : x = g
    · subst hxg; simp [N1, h2, hNg]
    · by_cases hxF : x = Fq
      · subst hxF; simp [N1, h2, hxg, hNFq]
      · by_cases hxS : x = Sq
        · subst hxS; simp [N1, h2, hxg, hxF, hNSq]
        · simp only [N1, h2, hxg, hxF, hxS, ↓reduceIte]
          exact hN2 x h1 h2 hxg h3 h4 hxF hxS
  -- step A: N1 reads as the put
  have hA := getFromR_spaceSplit N N1 V V2 i fuel hfuel root L q F S v n qn k1 pre cv h rk
    hNL hnl hnwf hnt hlive hNq hql hqwf hqt hk1 hrange hN1q hN1F hN1S hN1 hV2v hV2
    hqL hvL hvF hvS hNv hrootL hrootF hrootS hrq hrk hcv hvisL huniq hwfR honlyL
    (fun x xn c z hx hn hz => ⟨(hfr x xn c z hx hn hz).1, (hfr x xn c z hx hn hz).2.1,
      (hfr x xn c z hx hn hz).2.2.1⟩)
  -- the nodes N1 reaches: N's but L, and F, S and v
  have hqk1 : (k1, L) ∈ qn.liveAt i := by rw [KNode.liveAt_of_times qn i hqt]; exact hk1
  have hrL : ReachS N i root L := ReachS.step q qn k1 L hrq hNq hqk1
  have hq2wf : klongsWf q2.ks = true :=
    KNode.add_key_wf _ i sc S (KNode.add_key_wf qn i k1 F hqwf)
  have hq2t : ∀ s, Klong.time s ∈ q2.ks → s ≤ i :=
    KNode.add_times _ i (.key sc S) (fun s h => by cases h)
      (KNode.add_times qn i (.key k1 F) (fun s h => by cases h) hqt)
  have hq2look : ∀ c, q2.live.lookup c =
      if sc == c then some S else if k1 == c then some F else qn.live.lookup c := by
    intro c
    rw [KNode.add_key_live_lookup_of_wf _ i sc c S (KNode.add_key_wf qn i k1 F hqwf),
      KNode.add_key_live_lookup_of_wf qn i k1 c F hqwf]
  have hq2mem : ∀ c z, (c, z) ∈ q2.liveAt i →
      ((c, z) ∈ qn.liveAt i ∧ c ≠ k1) ∨ z = F ∨ z = S := by
    intro c z hz
    rw [KNode.liveAt_of_times _ i hq2t] at hz
    have := lookup_some_of_mem (KNode.live_keys_nodup _) hz
    rw [hq2look] at this
    by_cases h1 : sc = c
    · subst h1; simp at this; exact Or.inr (Or.inr this.symm)
    · have h1' : (sc == c) = false := by simpa using h1
      simp only [h1', Bool.false_eq_true, ↓reduceIte] at this
      by_cases h2 : k1 = c
      · subst h2; simp at this; exact Or.inr (Or.inl this.symm)
      · have h2' : (k1 == c) = false := by simpa using h2
        simp only [h2', Bool.false_eq_true, ↓reduceIte] at this
        left; rw [KNode.liveAt_of_times qn i hqt]
        exact ⟨lookup_some_mem this, fun h => h2 h.symm⟩
  have hhalf : ∀ x xn c z, (x = F ∨ x = S) → N1 x = some xn → (c, z) ∈ xn.liveAt i →
      (c, z) ∈ n.liveAt i ∨ z = v := by
    intro x xn c z hx hn hz
    rw [KNode.liveAt_of_times n i hnt]
    rcases hx with hx | hx
    · subst hx; rw [hN1F] at hn; cases hn
      exact halves_leaf_live_mem i n cv v hnl hlive c z (Or.inl hz)
    · subst hx; rw [hN1S] at hn; cases hn
      exact halves_leaf_live_mem i n cv v hnl hlive c z (Or.inr hz)
  have hreachNe : ∀ x, ReachS N i root x → x ≠ F ∧ x ≠ S ∧ x ≠ Fq ∧ x ≠ Sq ∧ x ≠ v := by
    intro x hx
    cases hx with
    | root => exact ⟨hrootF, hrootS, hrootFq, hrootSq, hrootv⟩
    | step x' xn c _ hx' hn hz =>
      have := hfr x' xn c _ hx' hn hz
      exact ⟨this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2, this.1⟩
  have hreach1 : ∀ x, ReachS N1 i root x →
      (ReachS N i root x ∧ x ≠ L) ∨ x = F ∨ x = S ∨ x = v := by
    intro x hx
    induction hx with
    | root => exact Or.inl ⟨ReachS.root, hrootL⟩
    | step x' xn c z _ hn hz ih =>
      rcases ih with ⟨hx', hx'L⟩ | hx' | hx' | hx'
      · by_cases hxq : x' = q
        · subst hxq
          rw [hN1q] at hn; cases hn
          rcases hq2mem c z hz with ⟨hz', hck⟩ | hzF | hzS
          · left
            refine ⟨ReachS.step x' qn c z hx' hNq hz', fun hzL => ?_⟩
            subst hzL
            exact hck (honlyL x' qn c hx' hNq hz').2
          · exact Or.inr (Or.inl hzF)
          · exact Or.inr (Or.inr (Or.inl hzS))
        · obtain ⟨hxF, hxS, _, _, _⟩ := hreachNe x' hx'
          rw [hN1 x' hx'L hxq hxF hxS] at hn
          left
          refine ⟨ReachS.step x' xn c z hx' hn hz, fun hzL => ?_⟩
          subst hzL
          exact hxq (honlyL x' xn c hx' hn hz).1
      · rcases hhalf x' xn c z (Or.inl hx') hn hz with hz' | hzv
        · left
          refine ⟨ReachS.step L n c z hrL hNL hz', fun hzL => ?_⟩
          subst hzL
          exact hqL (honlyL _ n c hrL hNL hz').1.symm
        · exact Or.inr (Or.inr (Or.inr hzv))
      · rcases hhalf x' xn c z (Or.inr hx') hn hz with hz' | hzv
        · left
          refine ⟨ReachS.step L n c z hrL hNL hz', fun hzL => ?_⟩
          subst hzL
          exact hqL (honlyL _ n c hrL hNL hz').1.symm
        · exact Or.inr (Or.inr (Or.inr hzv))
      · subst x'
        have : N1 v = none := by rw [hN1 v hvL hvq hvF hvS, hNv]
        rw [this] at hn; cases hn
  -- step B: q split at g into Fq and Sq
  have hwfh := halves_newKlongs_wf true i n.live [(cv, v)]
  have hlvq := KNode.lastVersion_eq_newKlongs n i
  rw [hnl] at hlvq
  have hwf1 : ∀ x xn, ReachS N1 i root x → N1 x = some xn → klongsWf xn.ks = true := by
    intro x xn hx hn
    rcases hreach1 x hx with ⟨hx', hxL⟩ | hxF | hxS | hxv
    · by_cases hxq : x = q
      · subst hxq; rw [hN1q] at hn; cases hn; exact hq2wf
      · obtain ⟨hxF, hxS, _, _, _⟩ := hreachNe x hx'
        rw [hN1 x hxL hxq hxF hxS] at hn; exact hwfG x xn hn
    · subst hxF; rw [hN1F] at hn; cases hn; rw [hnl, hlvq]; exact hwfh.1
    · subst hxS; rw [hN1S] at hn; cases hn; rw [hnl, hlvq]; exact hwfh.2
    · subst hxv; rw [hN1 x hvL hvq hvF hvS, hNv] at hn; cases hn
  have hnotq1 : ∀ x xn c z, ReachS N1 i root x → x ≠ g → N1 x = some xn →
      (c, z) ∈ xn.liveAt i → z ≠ q := by
    intro x xn c z hx hxg hn hz hzq
    subst hzq
    rcases hreach1 x hx with ⟨hx', hxL⟩ | hxF | hxS | hxv
    · by_cases hxq : x = z
      · subst hxq
        rw [hN1q] at hn; cases hn
        rcases hq2mem c x hz with ⟨hz', _⟩ | hzF | hzS
        · exact hgq (honlyq x qn c hx' hNq hz').1.symm
        · exact hFq hzF.symm
        · exact hSq hzS.symm
      · obtain ⟨hxF, hxS, _, _, _⟩ := hreachNe x hx'
        rw [hN1 x hxL hxq hxF hxS] at hn
        exact hxg (honlyq x xn c hx' hn hz).1
    · rcases hhalf x xn c z (Or.inl hxF) hn hz with hz' | hzv
      · exact hgL (honlyq L n c hrL hNL hz').1.symm
      · exact hvq hzv.symm
    · rcases hhalf x xn c z (Or.inr hxS) hn hz with hz' | hzv
      · exact hgL (honlyq L n c hrL hNL hz').1.symm
      · exact hvq hzv.symm
    · subst hxv
      rw [hN1 x hvL hvq hvF hvS, hNv] at hn; cases hn
  have hnotFS1 : ∀ x xn c z, ReachS N1 i root x → N1 x = some xn → (c, z) ∈ xn.liveAt i →
      z ≠ Fq ∧ z ≠ Sq := by
    intro x xn c z hx hn hz
    rcases hreach1 x hx with ⟨hx', hxL⟩ | hxF | hxS | hxv
    · by_cases hxq : x = q
      · subst hxq
        rw [hN1q] at hn; cases hn
        rcases hq2mem c z hz with ⟨hz', _⟩ | hzF | hzS
        · exact ⟨(hfr x qn c z hx' hNq hz').2.2.2.1, (hfr x qn c z hx' hNq hz').2.2.2.2⟩
        · rw [hzF]; exact ⟨hFqF.symm, hSqF.symm⟩
        · rw [hzS]; exact ⟨hFqS.symm, hSqS.symm⟩
      · obtain ⟨hxF, hxS, _, _, _⟩ := hreachNe x hx'
        rw [hN1 x hxL hxq hxF hxS] at hn
        exact ⟨(hfr x xn c z hx' hn hz).2.2.2.1, (hfr x xn c z hx' hn hz).2.2.2.2⟩
    · rcases hhalf x xn c z (Or.inl hxF) hn hz with hz' | hzv
      · exact ⟨(hfr L n c z hrL hNL hz').2.2.2.1, (hfr L n c z hrL hNL hz').2.2.2.2⟩
      · rw [hzv]; exact ⟨hvFq, hvSq⟩
    · rcases hhalf x xn c z (Or.inr hxS) hn hz with hz' | hzv
      · exact ⟨(hfr L n c z hrL hNL hz').2.2.2.1, (hfr L n c z hrL hNL hz').2.2.2.2⟩
      · rw [hzv]; exact ⟨hvFq, hvSq⟩
    · subst hxv
      rw [hN1 x hvL hvq hvF hvS, hNv] at hn; cases hn
  -- the halves of q with the klongs put
  have hq2look' : ∀ c, q2.live.lookup c =
      [(k1, F), (sc, S)].foldl (pairLookupStep c) (qn.live.lookup c) := by
    intro c
    rw [hq2look c]
    simp only [List.foldl_cons, List.foldl_nil, pairLookupStep]
  obtain ⟨hscq, hFl, hSl, hFwf, hSwf, hFt, hSt, hsF, hsS⟩ :=
    halves_inner_searchLte_ins qn q2 i [(k1, F), (sc, S)] hql r hr hsc hside hq2t hq2look'
  have hg2 : (((gn.add i (.key kq Fq)).add i
      (.key (halves qn.leaf i (qn.lastVersion i) [(k1, F), (sc, S)]).2.2 Sq))).leaf = false := by
    rw [KNode.add_leaf, KNode.add_leaf]; exact hgl
  have hgsearch : ∀ c : Nat, ((((gn.add i (.key kq Fq)).add i
      (.key (halves qn.leaf i (qn.lastVersion i) [(k1, F), (sc, S)]).2.2 Sq))).searchLte i c).map
        (·.y) =
      (gn.searchLte i c).map (fun fd => if fd.y = q then
        (if c < (halves qn.leaf i (qn.lastVersion i) [(k1, F), (sc, S)]).2.2 then Fq else Sq)
        else fd.y) := by
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
        obtain ⟨hxF, hxS, _, _, _⟩ := hreachNe x' hx'
        have hn1 : N1 x' = some xn := by rw [hN1 x' hx'L hx'q hxF hxS]; exact hn
        exact ReachS.step x' xn c z (ih hq' hL') hn1 hz
    have hrg1 : ReachS N1 i root g := htr g hrg hnoq hnoL
    exact ReachS.step g gn kq q hrg1 hN1g (by rw [KNode.liveAt_of_times gn i hgt]; exact hkq)
  have hsame1 : ∀ x, x ≠ q → x ≠ g → x ≠ Fq → x ≠ Sq → N2 x = N1 x := by
    intro x h1 h2 h3 h4
    simp only [N1, h1, h2, h3, h4, ↓reduceIte]
  have hget := fun c => getEqR_split_inner N1 N2 i root q g Fq Sq gn _ q2 _ _ _ hN1g hgl hN2g hg2
    hgsearch hN1q (by simp only [q2, KNode.add_leaf]; exact hql) hrq1 hN2Fq hFl hN2Sq hSl
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
  rw [hsim key' root ReachS.root hrootq hrootFq hrootSq]
  exact hA key' hkey'

/-! ## The rule: a space split of a leaf and a space split of its full parent -/

/-- A put of a key whose last segment's leaf L existed before the transaction
and is full by its size, with more than h klongs in its last version, below the
parent q, an inner node that existed before the transaction and is full by its
size with the two klongs to L's halves, with more than h klongs in its last
version, at least two of them live, below the grandparent g with room for two
klongs: the space splits of L and of q change the reading by the put alone. The
keys of L's and of q's live klongs lie between their parents' klongs to them and
the next ones (`hrange`, `hrangeq`), and neither q nor L reaches g. -/
theorem writerWP_put_spaceSpace (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
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
    (hleaf : (∀ s, Klong.time s ∈ n.ks → s ≤ c.i) ∧ c.p.M ≤ n.size + 1 ∧
      n.firstTime ≠ some c.i ∧ c.p.splitAbove < (n.lastVersion c.i).size ∧ n.live ≠ [] ∧
      wValue base w L = none ∧ L ≠ w.top.rootKey)
    (hparent : (∀ s, Klong.time s ∈ qn.ks → s ≤ c.i) ∧ c.p.M < qn.size + 2 + 1 ∧
      qn.firstTime ≠ some c.i ∧ c.p.splitAbove < (qn.lastVersion c.i).size ∧
      2 ≤ qn.live.length ∧ wValue base w q = none ∧ q ≠ w.top.rootKey)
    (hrange : ∀ c' z, (c', z) ∈ n.live →
      k1 ≤ c' ∧ ∀ c'' z', (c'', z') ∈ qn.live → k1 < c'' → c' < c'')
    (hrangeq : ∀ c' z, (c', z) ∈ qn.live →
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
  obtain ⟨htimes, hfull, hfirst, hsplit, hlive, hLval, hLroot⟩ := hleaf
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
    have : ¬ n.size + 1 < c.p.M := by omega
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
  have hny4 : w3.nodes.lookup (w3.next + 2 + 2 + 2 + 2) = none := by
    cases h' : w3.nodes.lookup (w3.next + 2 + 2 + 2 + 2) with
    | none => rfl
    | some _ => have := hsrcw3 _ (by rw [h']; rfl); omega
  rw [hlen]
  refine writerWP_mono (writerWP_appendKlongs_spaceSpace d'' L q g n qn gn kq k1 cv w3.next c _
    (by simpa using hlk3) (by simpa using hlq3) (by simpa using hlg3) hqL hgq hgL hql hgl hfirst
    hqfirst hfull hsplit hqfull hqsplit
    (by simpa using hpg) (by simpa using hpq) (by simpa using hpk) hroomg hdeadg
    (by simpa using hny) (by simpa using hny2) (by simpa using hny3) (by simpa using hny4)) ?_
  intro _ wf hTS
  obtain ⟨hft, hftop, hfv, hfn⟩ := hTS
  simp only at hft hftop hfv hfn
  rw [hr03.2.2.1] at hft
  rw [hr03.2.1] at hftop
  rw [hr03.2.2.2.1, hnext3] at hfv
  rw [hnext3] at hfn
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
  have hkqr : kq ≤ r.1 := (hrangeq r.1 r.2 hrmem).1
  have hgap : ∀ c' z, (c', z) ∈ gn.live → c' ≤ kq ∨ r.1 < c' := by
    intro c' z hcz
    by_cases hle : c' ≤ kq
    · exact Or.inl hle
    · exact Or.inr ((hrangeq r.1 r.2 hrmem).2 c' z hcz (by omega))
  -- the divider of L's halves, between k1 and q's next key
  obtain ⟨rL, hrL⟩ : ∃ rL, (n.live.drop (n.live.length / 2)).head? = some rL := by
    cases h' : n.live.drop (n.live.length / 2) with
    | nil =>
      have := congrArg List.length h'
      simp only [List.length_drop, List.length_nil] at this
      have : n.live.length = 0 := by omega
      exact absurd (List.eq_nil_of_length_eq_zero this) hlive
    | cons a _ => exact ⟨a, rfl⟩
  have hscL : (halves n.leaf c.i (n.lastVersion c.i) [(cv, w.next)]).2.2 = rL.1 := by
    have hlv := KNode.lastVersion_eq_newKlongs n c.i
    rw [hnl] at hlv
    simp only [hnl, hlv]
    rw [halves_shape true c.i n.live [(cv, w.next)] rL hrL]
    split <;> (try split) <;> rfl
  have hrLmem : rL ∈ n.live := List.mem_of_mem_drop (List.mem_of_head? hrL)
  have hside : (∀ a ∈ [(k1, w.next + 2), ((halves n.leaf c.i (n.lastVersion c.i)
        [(cv, w.next)]).2.2, w.next + 2 + 2)], r.1 ≤ a.1) ∨
      (∀ a ∈ [(k1, w.next + 2), ((halves n.leaf c.i (n.lastVersion c.i)
        [(cv, w.next)]).2.2, w.next + 2 + 2)], a.1 < r.1) := by
    rw [hscL]
    have hL1 := (hrange rL.1 rL.2 hrLmem).1
    by_cases hrk1 : r.1 ≤ k1
    · left
      intro a ha
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
      rcases ha with ha | ha <;> (subst ha; simp only; omega)
    · right
      have hL2 := (hrange rL.1 rL.2 hrLmem).2 r.1 r.2 hrmem (by omega)
      intro a ha
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
      rcases ha with ha | ha <;> (subst ha; simp only; omega)
  have hres := getFromR_spaceSpace (wNode c.p base w) (wNode c.p base wf) (wValue base w)
    (wValue base wf) c.i c.p.fuel hfuel w.top.rootKey L q g (w.next + 2) (w.next + 2 + 2)
    (w.next + 2 + 2 + 2) (w.next + 2 + 2 + 2 + 2) w.next n qn gn k1 kq pre cv h rk r hr hsc hwfG
    hNL hnl htimes hlive hNq hql hqt hk1L hrange hNg hgl hgt hkqg hkqr hgap hside
    (by
      have hyt : wf.taken.contains (w.next + 2) = false := by rw [hft]; exact hntake _ (by omega)
      simp only [wNode, hyt, Bool.false_eq_true, ↓reduceIte, hfn,
        show w.next + 2 ≠ L by omega, show w.next + 2 ≠ q by omega, show w.next + 2 ≠ g by omega])
    (by
      have hyt : wf.taken.contains (w.next + 2 + 2) = false := by
        rw [hft]; exact hntake _ (by omega)
      simp only [wNode, hyt, Bool.false_eq_true, ↓reduceIte, hfn,
        show w.next + 2 + 2 ≠ L by omega, show w.next + 2 + 2 ≠ q by omega,
        show w.next + 2 + 2 ≠ g by omega, show w.next + 2 + 2 ≠ w.next + 2 by omega])
    (by simp only [wNode, hgtk, Bool.false_eq_true, ↓reduceIte, hfn, hgL, hgq])
    (by
      have hyt : wf.taken.contains (w.next + 2 + 2 + 2) = false := by
        rw [hft]; exact hntake _ (by omega)
      simp only [wNode, hyt, Bool.false_eq_true, ↓reduceIte, hfn,
        show w.next + 2 + 2 + 2 ≠ L by omega, show w.next + 2 + 2 + 2 ≠ q by omega,
        show w.next + 2 + 2 + 2 ≠ g by omega, show w.next + 2 + 2 + 2 ≠ w.next + 2 by omega,
        show w.next + 2 + 2 + 2 ≠ w.next + 2 + 2 by omega])
    (by
      have hyt : wf.taken.contains (w.next + 2 + 2 + 2 + 2) = false := by
        rw [hft]; exact hntake _ (by omega)
      simp only [wNode, hyt, Bool.false_eq_true, ↓reduceIte, hfn,
        show w.next + 2 + 2 + 2 + 2 ≠ L by omega, show w.next + 2 + 2 + 2 + 2 ≠ q by omega,
        show w.next + 2 + 2 + 2 + 2 ≠ g by omega, show w.next + 2 + 2 + 2 + 2 ≠ w.next + 2 by omega,
        show w.next + 2 + 2 + 2 + 2 ≠ w.next + 2 + 2 by omega,
        show w.next + 2 + 2 + 2 + 2 ≠ w.next + 2 + 2 + 2 by omega])
    (by
      intro x hxL hxq hxg hxF hxS hxFq hxSq
      rw [← hr03.1]
      simp only [wNode, hft, hfn, hxL, hxq, hxg, hxF, hxS, hxFq, hxSq, ↓reduceIte, hr03.2.2.1])
    (by
      have hvt : wf.taken.contains w.next = false := by rw [hft]; exact hntake _ (Nat.le_refl _)
      simp only [wValue, hvt, Bool.false_eq_true, ↓reduceIte, hfv,
        lookup_append_single_self _ _ _ (hvalnone _ (Nat.le_refl _))])
    (by
      intro a ha
      simp only [wValue, hft, hfv, lookup_append_single_ne _ _ _ _ ha])
    hqL hgq hgL (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (hfreshN _ (Nat.le_refl _)) (hfreshN _ (by omega)) (hfreshN _ (by omega)) (hfreshN _ (by omega))
    (hfreshN _ (by omega))
    hLroot.symm (by omega) (by omega) hqroot.symm (by omega) (by omega) (by omega)
    hrq hrg hacyc.1 hacyc.2 hrk (keyWf_last_notin pre cv hkey) hvisL huniq
    (fun x xn c' hx hxn hz => htreeK x xn c' L hx hxn hz (by simp [hNL]) q qn k1 hrq hNq
      (by rw [KNode.liveAt_of_times qn c.i hqt]; exact hk1L))
    (fun x xn c' hx hxn hz => htreeK x xn c' q hx hxn hz (by simp [hNq]) g gn kq hrg hNg
      (by rw [KNode.liveAt_of_times gn c.i hgt]; exact hkqg))
    (fun x xn cc z hx hxn hz => by
      have := hlinks x xn cc z hx hxn hz
      exact ⟨by omega, by omega, by omega, by omega, by omega⟩)
  intro key' hkey'
  unfold wGet
  rw [hftop, hres key' hkey']
  simp only [Op.key, Op.value]
  rfl

end SIS.Tree
