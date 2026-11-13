import SIS.Tree.GetInnerSplit

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! The space split of an inner node after a space split below it (bergdb
024-12, TP10; the cascades): the halves of an inner node's last version with
klongs put on one side of its divider find what the node with the klongs
found, by compare value (`halves_inner_searchLte_ins`). -/

theorem halves_inner_searchLte_ins (qn Q : KNode) (t : Time) (ins : List (Nat × NodeId))
    (hql : qn.leaf = false) (hqt : ∀ s, Klong.time s ∈ qn.ks → s ≤ t)
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
  simp only [hf, decide_true, ↓reduceIte]
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

end SIS.Tree
