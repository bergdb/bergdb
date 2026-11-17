/-
The contract package (bergdb 030-16): the merge (`Dag.merge`, bergdb 024-11,
M1 to M5) as a statement about two trees, A before and B after.

Two siblings l and r, adjacent live klongs (cL, l) and (cR, r) of the inner
node q, of one level and one kind, each with a live klong. Their live klongs
in order, the right one's first renamed cR in an inner node (`mergeList`),
make one new node m1 (`Sound.mergeOne`): q's klong of cL names m1 and cR is
gone. Or they are cut in two (`Sound.mergeTwo`): the first part in m1, the
rest in m2 (in an inner node its first renamed to the empty key), and q gets
(cL, m1) and (g, m2), g the rest's first compare value, in place of the two.
The tree holds the same keys; l and r are no longer reached; the nodes
reached are those of A and the new ones.

Both ask (`hnames`) that a klong of another node reached that names l or r
names a node of B: B may drop l and r (the writer takes back a node made in
the transaction), and a dead klong that names one of them in a node that the
merge leaves as it is would then name nothing (PointersOK).

The helpers: `trm_kids`, the merged klongs in B meet what `Good` asks of a
node's klongs for the range of the two nodes, in order, and hold and reach
what the two nodes did; `trm_split`, a sorted list of such klongs cut in two
nodes; `trm_lo`, a compare value after the first is above the lower bound.
-/
import Contract.Proof.TreeRulesUp
import SIS.Tree.Exec

namespace Contract

theorem trm_belowNext {post : List (Nat × NodeId)} {c : Nat} {hi : Option Nat}
    (hpost : ∀ b ∈ post, c < b.1) (h : belowHi c hi = true) :
    belowHi c (nextHi post hi) = true := by
  cases post with
  | nil => exact h
  | cons b post =>
    simp only [nextHi, belowHi, decide_eq_true_eq]
    exact hpost b List.mem_cons_self

/-- The rules of one node, in B: every klong names a node of B. -/
theorem trm_nodeOk {A B : Tree} {b b' : Nat} {m : KNode} (h : nodeOk ⟨b⟩ A m = true)
    (hb : b ≤ b') (hs : ∀ c y, Klong.key c y ∈ m.ks → (B.obj y).isSome = true) :
    nodeOk ⟨b'⟩ B m = true := by
  simp only [nodeOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h ⊢
  refine ⟨⟨by omega, h.1.2⟩, ?_⟩
  intro k hk
  cases k with
  | key c y => exact hs c y hk
  | _ => rfl

theorem trm_ptr {A : Tree} {b : Nat} {m : KNode} (h : nodeOk ⟨b⟩ A m = true) {c : Nat}
    {y : NodeId} (hk : Klong.key c y ∈ m.ks) : (A.obj y).isSome = true := by
  simp only [nodeOk, Bool.and_eq_true, List.all_eq_true] at h
  exact h.2 _ hk

/-- A live compare value after the first is above the lower bound, from what
`Good` asks of each klong of a sorted list. -/
theorem trm_lo {s : Tree} {lev : Nat} {leaf : Bool} {lo : Nat} {H : Option Nat}
    {e l1 rest : List (Nat × NodeId)} {sc : Nat} {y0 : NodeId}
    (hk : ∀ t ∈ bounds e H, KidOk s lev leaf lo H t.1 t.2.1 t.2.2) (hsort : e.Pairwise CvLt)
    (hsplit : e = l1 ++ (sc, y0) :: rest) (hl1 : l1 ≠ []) : lo < sc := by
  rcases List.eq_nil_or_concat' l1 with h | ⟨l0, ⟨c0, z0⟩, rfl⟩
  · exact absurd h hl1
  have he : e = l0 ++ (c0, z0) :: ((sc, y0) :: rest) := by rw [hsplit]; simp
  have hc0 : c0 < sc := by
    rw [he, List.pairwise_append] at hsort
    exact (List.pairwise_cons.mp hsort.2.1).1 (sc, y0) List.mem_cons_self
  have hkk : KidOk s lev leaf lo H c0 z0 (some sc) := hk _ (bounds_mem H he)
  cases hlf : leaf with
  | true =>
    have : lo ≤ c0 := hkk.2.1 hlf
    omega
  | false =>
    obtain ⟨m, hm1, _, hm3, hg⟩ := hkk.2.2.2 (by simp [hlf])
    simp only [hlf, Bool.false_eq_true, ite_false] at hg
    obtain ⟨⟨k, v⟩, hkv⟩ := List.exists_mem_of_ne_nil _ (hg.nonempty m hm1 hm3)
    obtain ⟨d, r, _, hd1, hd2⟩ := hg.range k v hkv
    simp only [belowHi, decide_eq_true_eq] at hd2
    omega

/-- The klongs of a merge (`mergeList`) in B: what `Good` asks of each, in
order, for the range of the two nodes merged; they are sorted; they hold what
the two nodes held; they reach what the two nodes' klongs reached. -/
theorem trm_kids {A B : Tree} {l rr : NodeId} {nl nr : KNode} {lo cR : Nat} {H : Option Nat}
    (hGl : Good A l lo (some cR)) (hGr : Good A rr (max lo cR) H)
    (hAl : A.obj l = some (.key nl)) (hAr : A.obj rr = some (.key nr))
    (hlev : nl.level = nr.level) (hkind : nl.leaf = nr.leaf) (hnr : live nr.ks ≠ [])
    (hcR : belowHi cR H = true)
    (hal : ∀ z ∈ reachAt A (A.fuel l) l, z ≠ l → B.obj z = A.obj z)
    (har : ∀ z ∈ reachAt A (A.fuel rr) rr, z ≠ rr → B.obj z = A.obj z) :
    (∀ t ∈ bounds (SIS.Tree.mergeList (!nl.leaf) cR (live nl.ks) (live nr.ks)) H,
      KidOk B nl.level nl.leaf lo H t.1 t.2.1 t.2.2) ∧
    (SIS.Tree.mergeList (!nl.leaf) cR (live nl.ks) (live nr.ks)).Pairwise CvLt ∧
    (SIS.Tree.mergeList (!nl.leaf) cR (live nl.ks) (live nr.ks)).flatMap
      (fun cy => klongList B nl.leaf (L B) cy.1 cy.2) = L A l ++ L A rr ∧
    (SIS.Tree.mergeList (!nl.leaf) cR (live nl.ks) (live nr.ks)).flatMap
      (fun cy => reachAt B nl.level cy.2) =
      (live nl.ks).flatMap (fun cy => reachAt A nl.level cy.2) ++
        (live nr.ks).flatMap (fun cy => reachAt A nl.level cy.2) := by
  have hkl := fun c z (hm : (c, z) ∈ live nl.ks) => hGl.tr_kids_agree hAl hal hm
  have hkr := fun c z (hm : (c, z) ∈ live nr.ks) => hGr.tr_kids_agree hAr har hm
  have hREl : ∀ c z, (c, z) ∈ live nl.ks → reachAt B nl.level z = reachAt A nl.level z := by
    intro c z hm
    refine reachAt_agree _ _ (fun z' hz' => ?_)
    rw [hGl.tc_kid_eq hAl hm] at hz'
    exact hkl c z hm z' hz'
  have hREr : ∀ c z, (c, z) ∈ live nr.ks → reachAt B nl.level z = reachAt A nl.level z := by
    intro c z hm
    refine reachAt_agree _ _ (fun z' hz' => ?_)
    rw [hlev, hGr.tc_kid_eq hAr hm] at hz'
    exact hkr c z hm z' hz'
  have hKEl : ∀ c z, (c, z) ∈ live nl.ks →
      klongList B nl.leaf (L B) c z = klongList A nl.leaf (L A) c z :=
    fun c z hm => tc_klongList (hkl c z hm z (tc_self _ _ _)) (L_agree (hkl c z hm))
  have hKEr : ∀ c z, (c, z) ∈ live nr.ks →
      klongList B nl.leaf (L B) c z = klongList A nl.leaf (L A) c z :=
    fun c z hm => tc_klongList (hkr c z hm z (tc_self _ _ _)) (L_agree (hkr c z hm))
  have hLl : L A l = (live nl.ks).flatMap (fun cy => klongList A nl.leaf (L A) cy.1 cy.2) :=
    hGl.L_eq hAl
  have hLr : L A rr = (live nr.ks).flatMap (fun cy => klongList A nl.leaf (L A) cy.1 cy.2) := by
    rw [hkind]
    exact hGr.L_eq hAr
  have hlt : ∀ a ∈ live nl.ks, a.1 < cR := by
    intro a ha
    have := hGl.tr_hi hAl (c := a.1) (y := a.2) ha
    simpa [belowHi] using this
  have hAL := hGl.tr_kids hAl
  have hAR := hGr.tr_kids hAr
  rw [← hlev, ← hkind] at hAR
  have hRl : (live nl.ks).flatMap (fun cy => reachAt B nl.level cy.2) =
      (live nl.ks).flatMap (fun cy => reachAt A nl.level cy.2) := by
    apply List.flatMap_congr
    rintro ⟨c, z⟩ hm
    exact hREl c z hm
  have hKl : (live nl.ks).flatMap (fun cy => klongList B nl.leaf (L B) cy.1 cy.2) = L A l := by
    rw [hLl]
    apply List.flatMap_congr
    rintro ⟨c, z⟩ hm
    exact hKEl c z hm
  rcases Bool.eq_false_or_eq_true nl.leaf with hlf | hlf
  · -- segment leaves: the klongs of both, in order
    have hm : SIS.Tree.mergeList (!nl.leaf) cR (live nl.ks) (live nr.ks) =
        live nl.ks ++ live nr.ks := by
      simp [SIS.Tree.mergeList, hlf]
    rw [hm]
    have hge : ∀ b ∈ live nr.ks, max lo cR ≤ b.1 := by
      intro b hb
      obtain ⟨p1, p2, he1⟩ := List.append_of_mem hb
      exact (hAR _ (bounds_mem H he1)).2.1 hlf
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [bounds_append]
      intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · have hmem := bounds_mem_live ht
        obtain ⟨p1, p2, he1⟩ := List.append_of_mem hmem
        have hA' := hAL _ (bounds_mem (some cR) he1)
        have h1 : t.1 < cR := hlt _ hmem
        exact hA'.tr_move (hkl _ _ hmem) (tr_belowHi_le (le_of_lt h1) hcR)
          (fun hl => ⟨rfl, hA'.2.1 hl⟩) (fun h' => by rw [hlf] at h'; cases h')
      · have hA' := hAR t ht
        exact hA'.tr_move (hkr _ _ (bounds_mem_live ht)) hA'.1
          (fun hl => ⟨rfl, le_trans (le_max_left _ _) (hA'.2.1 hl)⟩)
          (fun h' => by rw [hlf] at h'; cases h')
    · rw [List.pairwise_append]
      exact ⟨live_sorted _, live_sorted _, fun a ha b hb =>
        lt_of_lt_of_le (hlt a ha) (le_trans (le_max_right lo cR) (hge b hb))⟩
    · rw [List.flatMap_append, hKl, hLr]
      congr 1
      apply List.flatMap_congr
      rintro ⟨c, z⟩ hm
      exact hKEr c z hm
    · rw [List.flatMap_append, hRl]
      congr 1
      apply List.flatMap_congr
      rintro ⟨c, z⟩ hm
      exact hREr c z hm
  · -- inner nodes: the right one's first klong gets cR
    obtain ⟨⟨c0, y0⟩, restR, hR⟩ := List.exists_cons_of_ne_nil hnr
    have hm : SIS.Tree.mergeList (!nl.leaf) cR (live nl.ks) (live nr.ks) =
        live nl.ks ++ (cR, y0) :: restR := by
      simp [SIS.Tree.mergeList, hlf, hR, SIS.Tree.renameHead]
    rw [hm]
    have hm0 : (c0, y0) ∈ live nr.ks := by rw [hR]; simp
    have hmr : ∀ a ∈ restR, a ∈ live nr.ks := fun a ha => by rw [hR]; simp [ha]
    have hgt : ∀ b ∈ restR, max lo cR < b.1 := by
      intro b hb
      obtain ⟨p1, p2, he1⟩ := List.append_of_mem hb
      exact hGr.tr_split_lo hAr (l1 := (c0, y0) :: p1) (sc := b.1) (y0 := b.2) (rest := p2)
        (by rw [hR, he1]; simp) (by simp)
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [bounds_append]
      intro t ht
      simp only [nextHi, bounds, List.mem_append, List.mem_cons] at ht
      rcases ht with ht | rfl | ht
      · have hA' := hAL t ht
        have h1 : t.1 < cR := hlt _ (bounds_mem_live ht)
        exact hA'.tr_move (hkl _ _ (bounds_mem_live ht)) (tr_belowHi_le (le_of_lt h1) hcR)
          (fun h' => by rw [hlf] at h'; cases h') (fun _ => ⟨rfl, rfl⟩)
      · have hA' := hAR (c0, y0, nextHi restR H) (by rw [hR]; simp [bounds])
        obtain ⟨m, hm1, hm2, hm3, hg⟩ := hA'.2.2.2 (fun h' => by rw [hlf] at h'; cases h')
        simp only [hlf, Bool.false_eq_true, ite_false] at hg
        refine ⟨hcR, (fun h' => by rw [hlf] at h'; cases h'),
          (fun h' => by rw [hlf] at h'; cases h'),
          fun _ => ⟨m, (hkr c0 y0 hm0 y0 (tc_self _ _ _)).trans hm1, hm2, hm3, ?_⟩⟩
        simp only [hlf, Bool.false_eq_true, ite_false]
        exact (hg.agree (hkr c0 y0 hm0)).widen (le_max_left _ _) (fun _ h' => h')
      · have hA' := hAR t (by rw [hR]; simp [bounds, ht])
        have h1 : max lo cR < t.1 := hgt _ (bounds_mem_live ht)
        exact hA'.tr_move (hkr _ _ (hmr _ (bounds_mem_live ht))) hA'.1
          (fun h' => by rw [hlf] at h'; cases h') (fun _ => ⟨by omega, rfl⟩)
    · have hs := live_sorted nr.ks
      rw [hR, List.pairwise_cons] at hs
      rw [List.pairwise_append, List.pairwise_cons]
      refine ⟨live_sorted _, ⟨fun b hb => lt_of_le_of_lt (le_max_right lo cR) (hgt b hb), hs.2⟩,
        fun a ha b hb => ?_⟩
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hlt a ha
      · exact lt_trans (hlt a ha) (lt_of_le_of_lt (le_max_right lo cR) (hgt b hb))
    · rw [List.flatMap_append, hKl, hLr, hR, List.flatMap_cons, List.flatMap_cons]
      congr 1
      congr 1
      · simp only [klongList, hlf, Bool.false_eq_true, ite_false]
        exact L_agree (hkr c0 y0 hm0)
      · apply List.flatMap_congr
        rintro ⟨c, z⟩ hm
        exact hKEr c z (hmr _ hm)
    · rw [List.flatMap_append, hRl, hR, List.flatMap_cons, List.flatMap_cons]
      congr 1
      congr 1
      · exact hREr c0 y0 hm0
      · apply List.flatMap_congr
        rintro ⟨c, z⟩ hm
        exact hREr c z (hmr _ hm)

/-- A split of a sorted list of klongs that meet what `Good` asks of them for
the range [lo, H): the first part in one node, for [lo, sc); the rest in
another, its first compare value 0 in an inner node, for [max lo sc, H). -/
theorem trm_split {B : Tree} {first second : NodeId} {lev : Nat} {leaf : Bool} {lo : Nat}
    {H : Option Nat} {e l1 rest : List (Nat × NodeId)} {sc : Nat} {y0 : NodeId} {b1 b2 : Nat}
    (hk : ∀ t ∈ bounds e H, KidOk B lev leaf lo H t.1 t.2.1 t.2.2) (hsort : e.Pairwise CvLt)
    (hsplit : e = l1 ++ (sc, y0) :: rest) (hBf : NodeIs B first lev leaf l1 b1)
    (hBs : NodeIs B second lev leaf (if leaf then (sc, y0) :: rest else (0, y0) :: rest) b2) :
    Good B first lo (some sc) ∧ Good B second (max lo sc) H := by
  obtain ⟨nf, hf1, hf2, hf3, hf4, hf5⟩ := hBf
  obtain ⟨ns, hs1, hs2, hs3, hs4, hs5⟩ := hBs
  have hag : ∀ y : NodeId, ∀ z ∈ reachAt B (B.fuel y) y, B.obj z = B.obj z :=
    fun _ _ _ => rfl
  rw [hsplit, bounds_append] at hk
  rw [hsplit, List.pairwise_append] at hsort
  have hl1lt : ∀ a ∈ l1, a.1 < sc := fun a ha => hsort.2.2 a ha (sc, y0) List.mem_cons_self
  have hrestgt : ∀ b ∈ rest, sc < b.1 := (List.pairwise_cons.mp hsort.2.1).1
  have hwf1 : klongsWf nf.ks = true := by
    simp only [nodeOk, Bool.and_eq_true] at hf5
    exact hf5.1.2
  have hwf2 : klongsWf ns.ks = true := by
    simp only [nodeOk, Bool.and_eq_true] at hs5
    exact hs5.1.2
  refine ⟨?_, ?_⟩
  · refine tr_good_of hf1 hwf1 ?_
    rw [hf4, hf2, hf3]
    intro t ht
    have hA' := hk t (List.mem_append_left _ ht)
    have hlt : t.1 < sc := hl1lt _ (bounds_mem_live ht)
    exact hA'.tr_move (hag _) (by simp [belowHi, hlt]) (fun hl => ⟨rfl, hA'.2.1 hl⟩)
      (fun _ => ⟨rfl, rfl⟩)
  · refine tr_good_of hs1 hwf2 ?_
    rw [hs2, hs3]
    cases leaf with
    | true =>
      simp only [ite_true] at hs4
      rw [hs4]
      intro t ht
      have hA' := hk t (List.mem_append_right _ ht)
      have hmem := bounds_mem_live ht
      have hge : sc ≤ t.1 := by
        rcases List.mem_cons.mp hmem with h' | h'
        · rw [← (Prod.mk.inj h').1]
        · exact le_of_lt (hrestgt _ h')
      exact hA'.tr_move (hag _) hA'.1 (fun _ => ⟨rfl, max_le (hA'.2.1 rfl) hge⟩)
        (fun h' => by cases h')
    | false =>
      simp only [Bool.false_eq_true, ite_false] at hs4
      rw [hs4]
      intro t ht
      simp only [bounds, List.mem_cons] at ht
      rcases ht with rfl | ht
      · have hA' := hk (sc, y0, nextHi rest H) (List.mem_append_right _ (by simp [bounds]))
        exact hA'.tr_move (hag _) (tr_belowHi_le (Nat.zero_le _) hA'.1)
          (fun h' => by cases h') (fun _ => ⟨by omega, rfl⟩)
      · have hA' := hk t (List.mem_append_right _ (by simp [bounds, ht]))
        have hgt : sc < t.1 := hrestgt _ (bounds_mem_live ht)
        exact hA'.tr_move (hag _) hA'.1 (fun h' => by cases h') (fun _ => ⟨by omega, rfl⟩)

theorem trm_nodup_drop {α : Type} {X Y Z : List α} {a b : α}
    (h : (X ++ a :: (Y ++ b :: Z)).Nodup) :
    (X ++ (Y ++ Z)).Nodup ∧ a ∉ X ++ (Y ++ Z) ∧ b ∉ X ++ (Y ++ Z) := by
  rw [List.nodup_middle, List.nodup_cons] at h
  obtain ⟨ha, h⟩ := h
  have e1 : X ++ (Y ++ b :: Z) = (X ++ Y) ++ b :: Z := by simp
  rw [e1, List.nodup_middle, List.nodup_cons] at h
  refine ⟨by simpa using h.2, fun hm => ha ?_, fun hm => h.1 (by simpa using hm)⟩
  simp only [List.mem_append, List.mem_cons] at hm ⊢
  tauto

theorem trm_mem_drop {α : Type} {X Y Z : List α} {a b z : α} (h : z ∈ X ++ (Y ++ Z)) :
    z ∈ X ++ a :: (Y ++ b :: Z) := by
  simp only [List.mem_append, List.mem_cons] at h ⊢
  tauto

theorem trm_mem_snoc {α : Type} {P S : List α} {a b : α} (h : a ∈ P ++ S) :
    a ∈ (P ++ [b]) ++ S := by
  simp only [List.mem_append, List.mem_singleton] at h ⊢
  tauto

theorem trm_mem_add {α : Type} {X R : List α} {c z : α} (h : z ∈ X ++ c :: R) :
    z = c ∨ z ∈ X ++ R := by
  simp only [List.mem_append, List.mem_cons] at h ⊢
  tauto

theorem trm_nodup_add {α : Type} {X R : List α} {c : α} (h : (X ++ R).Nodup) (hc : c ∉ X ++ R) :
    (X ++ c :: R).Nodup := by
  rw [List.nodup_middle, List.nodup_cons]
  exact ⟨hc, h⟩


/-- The merge into one node. `hnames`: a klong of another node reached that
names l or rr names a node of B (l and rr stay in B, or no such klong). -/
theorem Sound.mergeOne {M : Nat} {ex' : Option NodeId} {A B : Tree} {r q l rr m1 : NodeId}
    {C : List (Key × Nat)} {nq nl nr : KNode} {cL cR : Nat} {pre post : List (Nat × NodeId)}
    (h : Sound M none A r C) (hq : q ∈ reachAt A (A.fuel r) r)
    (hAq : A.obj q = some (.key nq)) (hql : nq.leaf = false)
    (hlive : live nq.ks = pre ++ (cL, l) :: (cR, rr) :: post)
    (hAl : A.obj l = some (.key nl)) (hAr : A.obj rr = some (.key nr))
    (hlev : nl.level = nr.level) (hkind : nl.leaf = nr.leaf)
    (hnl : live nl.ks ≠ []) (hnr : live nr.ks ≠ [])
    (hm1 : A.obj m1 = none)
    (hBm : NodeIs B m1 nl.level nl.leaf
      (SIS.Tree.mergeList (!nl.leaf) cR (live nl.ks) (live nr.ks)) M)
    (hBq : NodeIs B q nq.level false (pre ++ (cL, m1) :: post) (bnd M ex' q))
    (hsame : ∀ z, z ≠ m1 → z ≠ q → z ≠ l → z ≠ rr → B.obj z = A.obj z)
    (hnames : ∀ z ∈ reachAt A (A.fuel r) r, z ≠ q → z ≠ l → z ≠ rr → ∀ m,
      A.obj z = some (.key m) → ∀ c y, Klong.key c y ∈ m.ks → (y = l ∨ y = rr) →
        (B.obj y).isSome = true) :
    Sound M ex' B r C ∧ l ∉ reachAt B (B.fuel r) r ∧ rr ∉ reachAt B (B.fuel r) r ∧
      ∀ z ∈ reachAt B (B.fuel r) r, z ∈ reachAt A (A.fuel r) r ∨ z = m1 := by
  obtain ⟨nqb, hq1, hq2, hq3, hq4, hq5⟩ := hBq
  obtain ⟨nm, hn1, hn2, hn3, hn4, hn5⟩ := id hBm
  have hG := h.good
  obtain ⟨loq, hiq, hgq⟩ := hG.tr_reach_good _ q hq nq hAq
  have hTq := hG.tr_nodup h.tree hq
  have hnotA : ∀ z, A.obj z = none → z ∉ reachAt A (A.fuel r) r := by
    intro z hz hm
    have := hG.tr_exists _ z hm
    simp [hz] at this
  have hmA := hnotA m1 hm1
  have he : live nq.ks = pre ++ (cL, l) :: ((cR, rr) :: post) := hlive
  have he2 : live nq.ks = (pre ++ [(cL, l)]) ++ (cR, rr) :: post := by rw [hlive]; simp
  obtain ⟨_, hpostL, _⟩ := live_split he
  obtain ⟨_, hpost2, _⟩ := live_split he2
  have hcLR : cL < cR := hpostL _ List.mem_cons_self
  have hlk : (cL, l) ∈ live nq.ks := by rw [he]; simp
  have hrk : (cR, rr) ∈ live nq.ks := by rw [he]; simp
  have hlvl : nl.level < nq.level := by
    obtain ⟨m, _, _, hm1', hm2, _, _⟩ := hgq.child hAq hlk (by simp [hql])
    rw [hAl] at hm1'
    cases hm1'
    exact hm2
  have hql' : q ≠ l := by
    intro e
    rw [e, hAl] at hAq
    cases hAq
    omega
  have hqr' : q ≠ rr := by
    intro e
    rw [e, hAr] at hAq
    cases hAq
    omega
  have hfq : A.fuel q = nq.level + 1 := by simp [Tree.fuel, hAq]
  have hlq : l ∈ reachAt A (A.fuel q) q := by
    rw [hfq]
    exact tc_kid hAq hlk (tc_self _ _ _)
  have hrq : rr ∈ reachAt A (A.fuel q) q := by
    rw [hfq]
    exact tc_kid hAq hrk (tc_self _ _ _)
  have hlr : l ∈ reachAt A (A.fuel r) r := hG.tr_closed hq hlq
  have hrr : rr ∈ reachAt A (A.fuel r) r := hG.tr_closed hq hrq
  have hqnl : ∀ f, q ∉ reachAt A f l := fun f => hgq.tc_no_cycle hlq (Ne.symm hql') f
  have hqnr : ∀ f, q ∉ reachAt A f rr := fun f => hgq.tc_no_cycle hrq (Ne.symm hqr') f
  have hqA : ∀ z, z ∈ reachAt A (A.fuel q) q → z ∈ reachAt A (A.fuel r) r :=
    fun z hz => hG.tr_closed hq hz
  have hapart : ∀ z ∈ reachAt A nq.level rr, z ∉ reachAt A nq.level l :=
    fun z hz => (hgq.tr_side hAq hTq he (c := cR) (z := rr) (by simp) hz).2.1
  have hlA : reachAt A nq.level l = reachAt A (A.fuel l) l := hgq.tc_kid_eq hAq hlk
  have hrA : reachAt A nq.level rr = reachAt A (A.fuel rr) rr := hgq.tc_kid_eq hAq hrk
  have hal : ∀ z ∈ reachAt A (A.fuel l) l, z ≠ l → B.obj z = A.obj z := by
    intro z hz hzl
    refine hsame z (fun e => hmA (e ▸ hG.tr_closed hlr hz)) (fun e => hqnl _ (e ▸ hz)) hzl
      (fun e => ?_)
    rw [← hlA] at hz
    exact hapart rr (tc_self _ _ _) (e ▸ hz)
  have har : ∀ z ∈ reachAt A (A.fuel rr) rr, z ≠ rr → B.obj z = A.obj z := by
    intro z hz hzr
    refine hsame z (fun e => hmA (e ▸ hG.tr_closed hrr hz)) (fun e => hqnr _ (e ▸ hz))
      (fun e => ?_) hzr
    rw [← hrA] at hz
    exact hapart z hz (e ▸ tc_self _ _ _)
  have hmpp : ∀ a ∈ pre ++ post, a ∈ live nq.ks := by
    intro a h'
    rw [he]
    rcases List.mem_append.mp h' with h' | h' <;> simp [h']
  have hside : ∀ c' z, (c', z) ∈ pre ++ post → ∀ z' ∈ reachAt A nq.level z,
      B.obj z' = A.obj z' := by
    intro c' z hb z' hz'
    obtain ⟨h1, h2, h3⟩ := hgq.tr_side hAq hTq he (c := c') (z := z) (tr_mem_mid hb) hz'
    obtain ⟨_, h4, _⟩ := hgq.tr_side hAq hTq he2 (c := c') (z := z) (trm_mem_snoc hb) hz'
    refine hsame z' (fun e => ?_) h1 (fun e => h2 (e ▸ tc_self _ _ _))
      (fun e => h4 (e ▸ tc_self _ _ _))
    rw [e, hm1] at h3
    cases h3
  have hside' : ∀ c' z, (c', z) ∈ pre ++ post → ∀ z' ∈ reachAt A (A.fuel z) z,
      B.obj z' = A.obj z' := by
    intro c' z hb z' hz'
    rw [← hgq.tc_kid_eq hAq (hmpp _ hb)] at hz'
    exact hside c' z hb z' hz'
  have hwf : klongsWf nqb.ks = true := by
    simp only [nodeOk, Bool.and_eq_true] at hq5
    exact hq5.1.2
  have hwfm : klongsWf nm.ks = true := by
    simp only [nodeOk, Bool.and_eq_true] at hn5
    exact hn5.1.2
  have hmne : SIS.Tree.mergeList (!nl.leaf) cR (live nl.ks) (live nr.ks) ≠ [] := by
    simp [SIS.Tree.mergeList, hnl]
  have hmerge : ∀ lo' hi', Good A q lo' hi' →
      Good B m1 (max lo' cL) (nextHi post hi') ∧ L B m1 = L A l ++ L A rr ∧
      reachAt B (B.fuel m1) m1 =
        m1 :: ((live nl.ks).flatMap (fun cy => reachAt A nl.level cy.2) ++
          (live nr.ks).flatMap (fun cy => reachAt A nl.level cy.2)) := by
    intro lo' hi' hg
    have hgl : Good A l (max lo' cL) (some cR) := hg.tr_kid hAq hql he
    have hgr : Good A rr (max (max lo' cL) cR) (nextHi post hi') := by
      have := hg.tr_kid hAq hql he2
      rwa [show max lo' cR = max (max lo' cL) cR by omega] at this
    have hcR : belowHi cR (nextHi post hi') = true := trm_belowNext hpost2 (hg.tr_hi hAq hrk)
    obtain ⟨hK, _, hLm, hRm⟩ := trm_kids hgl hgr hAl hAr hlev hkind hnr hcR hal har
    have hGm : Good B m1 (max lo' cL) (nextHi post hi') := by
      refine tr_good_of hn1 hwfm ?_
      rw [hn4, hn2, hn3]
      exact hK
    refine ⟨hGm, ?_, ?_⟩
    · rw [hGm.L_eq hn1, hn4, hn3]
      exact hLm
    · rw [show B.fuel m1 = nl.level + 1 by simp [Tree.fuel, hn1, hn2], tc_key hn1, hn4, hRm]
  have hloc : ∀ lo' hi', Good A q lo' hi' → Good B q lo' hi' := by
    intro lo' hi' hg
    have hGm := (hmerge lo' hi' hg).1
    have hA := hg.tr_kids hAq
    rw [he, bounds_append] at hA
    refine tr_good_of hq1 hwf ?_
    rw [hq4, hq2, hq3, bounds_append]
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · have hA' := hA t (List.mem_append_left _ ht)
      rw [hql] at hA'
      exact hA'.tr_move (hside' _ _ (List.mem_append_left _ (bounds_mem_live ht))) hA'.1
        (fun h' => (by cases h')) (fun _ => ⟨rfl, rfl⟩)
    · simp only [bounds, List.mem_cons] at ht
      rcases ht with rfl | ht
      · have hA' := hg.tr_kids hAq _ (bounds_mem hi' he)
        refine ⟨hA'.1, fun h' => (by cases h'), fun h' => (by cases h'), fun _ => ?_⟩
        exact ⟨nm, hn1, by omega, by rw [hn4]; exact hmne, by simpa using hGm⟩
      · have hA' := hA t (List.mem_append_right _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ ht)))
        rw [hql] at hA'
        exact hA'.tr_move (hside' _ _ (List.mem_append_right _ (bounds_mem_live ht))) hA'.1
          (fun h' => (by cases h')) (fun _ => ⟨rfl, rfl⟩)
  obtain ⟨hGm0, hLm0, hRm0⟩ := hmerge loq hiq hgq
  have hgqB := hloc loq hiq hgq
  have hL : L B q = L A q := by
    rw [hgqB.L_eq hq1, hgq.L_eq hAq, hq4, he, hq3, hql]
    have hE : ∀ l' : List (Nat × NodeId), (∀ a ∈ l', a ∈ pre ++ post) →
        l'.flatMap (fun cy => klongList B false (L B) cy.1 cy.2) =
          l'.flatMap (fun cy => klongList A false (L A) cy.1 cy.2) := by
      intro l' hl'
      apply List.flatMap_congr
      rintro ⟨c, z⟩ hm
      exact tc_klongList (hside c z (hl' _ hm) z (tc_self _ _ _))
        (L_agree (hside' c z (hl' _ hm)))
    simp only [List.flatMap_append, List.flatMap_cons]
    rw [hE pre (fun a h' => List.mem_append_left _ h'),
      hE post (fun a h' => List.mem_append_right _ h')]
    simp only [klongList, Bool.false_eq_true, ite_false]
    rw [hLm0]
    simp
  have hRE : ∀ l' : List (Nat × NodeId), (∀ a ∈ l', a ∈ pre ++ post) →
      l'.flatMap (fun cy => reachAt B nq.level cy.2) =
        l'.flatMap (fun cy => reachAt A nq.level cy.2) := by
    intro l' hl'
    apply List.flatMap_congr
    rintro ⟨c, z⟩ hm
    exact reachAt_agree _ _ (hside c z (hl' _ hm))
  have hmB : reachAt B nq.level m1 =
      m1 :: ((live nl.ks).flatMap (fun cy => reachAt A nl.level cy.2) ++
        (live nr.ks).flatMap (fun cy => reachAt A nl.level cy.2)) := by
    rw [hGm0.reachAt_eq nq.level (by simp [Tree.fuel, hn1, hn2]; omega)]
    exact hRm0
  have hlA' : reachAt A nq.level l =
      l :: (live nl.ks).flatMap (fun cy => reachAt A nl.level cy.2) := by
    rw [hlA, show A.fuel l = nl.level + 1 by simp [Tree.fuel, hAl], tc_key hAl]
  have hrA' : reachAt A nq.level rr =
      rr :: (live nr.ks).flatMap (fun cy => reachAt A nl.level cy.2) := by
    rw [hrA, show A.fuel rr = nr.level + 1 by simp [Tree.fuel, hAr], tc_key hAr, hlev]
  have hRqA : reachAt A (A.fuel q) q = (q :: pre.flatMap (fun cy => reachAt A nq.level cy.2)) ++
      l :: ((live nl.ks).flatMap (fun cy => reachAt A nl.level cy.2) ++
        rr :: ((live nr.ks).flatMap (fun cy => reachAt A nl.level cy.2) ++
          post.flatMap (fun cy => reachAt A nq.level cy.2))) := by
    rw [hfq, tc_key hAq, he, List.flatMap_append, List.flatMap_cons, List.flatMap_cons, hlA', hrA']
    simp
  have hRqB : reachAt B (B.fuel q) q = (q :: pre.flatMap (fun cy => reachAt A nq.level cy.2)) ++
      m1 :: ((live nl.ks).flatMap (fun cy => reachAt A nl.level cy.2) ++
        ((live nr.ks).flatMap (fun cy => reachAt A nl.level cy.2) ++
          post.flatMap (fun cy => reachAt A nq.level cy.2))) := by
    rw [show B.fuel q = nq.level + 1 by simp [Tree.fuel, hq1, hq2], tc_key hq1, hq4,
      List.flatMap_append, List.flatMap_cons, hmB, hRE pre (fun a h' => List.mem_append_left _ h'),
      hRE post (fun a h' => List.mem_append_right _ h')]
    simp
  have hTq' := hTq
  rw [hRqA] at hTq'
  obtain ⟨hK, hlK, hrK⟩ := trm_nodup_drop hTq'
  have hR : (reachAt B (B.fuel q) q).Nodup := by
    rw [hRqB]
    refine trm_nodup_add hK (fun hm => hmA (hqA m1 ?_))
    rw [hRqA]
    exact trm_mem_drop hm
  have hmemq : ∀ z ∈ reachAt B (B.fuel q) q, z ∈ reachAt A (A.fuel q) q ∨ z = m1 := by
    intro z hz
    rw [hRqB] at hz
    rw [hRqA]
    rcases trm_mem_add hz with e | e
    · exact Or.inr e
    · exact Or.inl (trm_mem_drop e)
  have hnew : ∀ z ∈ reachAt B (B.fuel q) q,
      z ∈ reachAt A (A.fuel q) q ∨ z ∉ reachAt A (A.fuel r) r := by
    intro z hz
    rcases hmemq z hz with h' | rfl
    · exact Or.inl h'
    · exact Or.inr hmA
  have ha : Agree A B r q := by
    intro z hz hzq
    exact hsame z (fun e => hmA (e ▸ hz)) (fun e => hzq (e ▸ tc_self _ _ _))
      (fun e => hzq (e ▸ hlq)) (fun e => hzq (e ▸ hrq))
  have hk : KeepsKind A B q := by
    intro n hn
    rw [hAq] at hn
    cases hn
    exact ⟨nqb, hq1, by omega, fun _ => by rw [hq4]; simp⟩
  have hqk : ∃ n, A.obj q = some (.key n) := ⟨nq, hAq⟩
  obtain ⟨hTB, hmemB⟩ := ctx_reach hG h.tree hq ha hk hloc hqk hR hnew
  have hgone : ∀ x, x ∈ reachAt A (A.fuel q) q → x ≠ m1 →
      x ∉ (q :: pre.flatMap (fun cy => reachAt A nq.level cy.2)) ++
        ((live nl.ks).flatMap (fun cy => reachAt A nl.level cy.2) ++
          ((live nr.ks).flatMap (fun cy => reachAt A nl.level cy.2) ++
            post.flatMap (fun cy => reachAt A nq.level cy.2))) →
      x ∉ reachAt B (B.fuel r) r := by
    intro x hxq hxm hxK hx
    rcases hmemB x hx with ⟨_, h2⟩ | h2
    · exact h2 hxq
    · rw [hRqB] at h2
      rcases trm_mem_add h2 with h3 | h3
      · exact hxm h3
      · exact hxK h3
  have hlB : l ∉ reachAt B (B.fuel r) r := hgone l hlq (tr_ne_of_obj hAl hm1) hlK
  have hrB : rr ∉ reachAt B (B.fuel r) r := hgone rr hrq (tr_ne_of_obj hAr hm1) hrK
  have hmem : ∀ z ∈ reachAt B (B.fuel r) r, z ∈ reachAt A (A.fuel r) r ∨ z = m1 := by
    intro z hz
    rcases hmemB z hz with ⟨h1, _⟩ | h1
    · exact Or.inl h1
    · rcases hmemq z h1 with h2 | h2
      · exact Or.inl (hqA z h2)
      · exact Or.inr h2
  refine ⟨⟨?_, Good.ctx hG h.tree hq ha hk hloc hqk, ?_, ?_, hTB⟩, hlB, hrB, hmem⟩
  · obtain ⟨n, ho, hne⟩ := h.key
    by_cases hrq' : r = q
    · rw [hrq']
      exact ⟨nqb, hq1, Or.inr (by rw [hq4]; simp)⟩
    · have hrl : r ≠ l := fun e => hqnl _ (e ▸ hq)
      have hrr' : r ≠ rr := fun e => hqnr _ (e ▸ hq)
      exact ⟨n, (hsame r (tr_ne_of_obj ho hm1) hrq' hrl hrr').trans ho, hne⟩
  · intro z hz m hm
    by_cases hzq : z = q
    · rw [hzq, hq1] at hm
      cases hm
      rw [hzq]
      exact hq5
    by_cases hzm : z = m1
    · rw [hzm, hn1] at hm
      cases hm
      exact tr_nodeOk hn5 (by split <;> omega) (fun _ h' => h')
    have hzl : z ≠ l := fun e => hlB (e ▸ hz)
    have hzr : z ≠ rr := fun e => hrB (e ▸ hz)
    have hzA : z ∈ reachAt A (A.fuel r) r := by
      rcases hmem z hz with h' | h'
      · exact h'
      · exact absurd h' hzm
    have hAm : A.obj z = some (.key m) := by rw [← hsame z hzm hzq hzl hzr]; exact hm
    have hnA := h.nodes z hzA m hAm
    simp only [reduceCtorEq, ite_false] at hnA
    refine trm_nodeOk hnA (by split <;> omega) (fun c y hky => ?_)
    by_cases hy : y = l ∨ y = rr
    · exact hnames z hzA hzq hzl hzr m hAm c y hky hy
    by_cases hym : y = m1
    · simp [hym, hn1]
    by_cases hyq : y = q
    · simp [hyq, hq1]
    rw [hsame y hym hyq (fun e => hy (Or.inl e)) (fun e => hy (Or.inr e))]
    exact trm_ptr hnA hky
  · rw [ctx_L hG h.tree hq ha hk hloc hqk hL]
    exact h.holds

/-- The merge into two nodes: `mergeList`'s klongs are `first ++ rest`, both
not empty; m1 holds `first`, m2 holds `rest` (in an inner node with its first
compare value renamed 0), and q's klong of the rest's first compare value g
names m2. `hnames` as for `Sound.mergeOne`. -/
theorem Sound.mergeTwo {M : Nat} {ex' : Option NodeId} {A B : Tree}
    {r q l rr m1 m2 : NodeId} {C : List (Key × Nat)} {nq nl nr : KNode} {cL cR g : Nat}
    {pre post first rest : List (Nat × NodeId)} {y0 : NodeId}
    (h : Sound M none A r C) (hq : q ∈ reachAt A (A.fuel r) r)
    (hAq : A.obj q = some (.key nq)) (hql : nq.leaf = false)
    (hlive : live nq.ks = pre ++ (cL, l) :: (cR, rr) :: post)
    (hAl : A.obj l = some (.key nl)) (hAr : A.obj rr = some (.key nr))
    (hlev : nl.level = nr.level) (hkind : nl.leaf = nr.leaf)
    (hnr : live nr.ks ≠ [])
    (hsplit : SIS.Tree.mergeList (!nl.leaf) cR (live nl.ks) (live nr.ks) =
      first ++ (g, y0) :: rest)
    (hfirst : first ≠ [])
    (hm1 : A.obj m1 = none) (hm2 : A.obj m2 = none) (hne : m1 ≠ m2)
    (hBm1 : NodeIs B m1 nl.level nl.leaf first M)
    (hBm2 : NodeIs B m2 nl.level nl.leaf
      (if nl.leaf then (g, y0) :: rest else (0, y0) :: rest) M)
    (hBq : NodeIs B q nq.level false (pre ++ (cL, m1) :: (g, m2) :: post) (bnd M ex' q))
    (hsame : ∀ z, z ≠ m1 → z ≠ m2 → z ≠ q → z ≠ l → z ≠ rr → B.obj z = A.obj z)
    (hnames : ∀ z ∈ reachAt A (A.fuel r) r, z ≠ q → z ≠ l → z ≠ rr → ∀ m,
      A.obj z = some (.key m) → ∀ c y, Klong.key c y ∈ m.ks → (y = l ∨ y = rr) →
        (B.obj y).isSome = true) :
    Sound M ex' B r C ∧ l ∉ reachAt B (B.fuel r) r ∧ rr ∉ reachAt B (B.fuel r) r ∧
      ∀ z ∈ reachAt B (B.fuel r) r, z ∈ reachAt A (A.fuel r) r ∨ z = m1 ∨ z = m2 := by
  obtain ⟨nqb, hq1, hq2, hq3, hq4, hq5⟩ := hBq
  obtain ⟨nf, hf1, hf2, hf3, hf4, hf5⟩ := id hBm1
  obtain ⟨ns, hs1, hs2, hs3, hs4, hs5⟩ := id hBm2
  have hG := h.good
  obtain ⟨loq, hiq, hgq⟩ := hG.tr_reach_good _ q hq nq hAq
  have hTq := hG.tr_nodup h.tree hq
  have hnotA : ∀ z, A.obj z = none → z ∉ reachAt A (A.fuel r) r := by
    intro z hz hm
    have := hG.tr_exists _ z hm
    simp [hz] at this
  have hmA := hnotA m1 hm1
  have hmA2 := hnotA m2 hm2
  have he : live nq.ks = pre ++ (cL, l) :: ((cR, rr) :: post) := hlive
  have he2 : live nq.ks = (pre ++ [(cL, l)]) ++ (cR, rr) :: post := by rw [hlive]; simp
  obtain ⟨_, hpostL, _⟩ := live_split he
  obtain ⟨_, hpost2, hpp2⟩ := live_split he2
  have hcLR : cL < cR := hpostL _ List.mem_cons_self
  have hlk : (cL, l) ∈ live nq.ks := by rw [he]; simp
  have hrk : (cR, rr) ∈ live nq.ks := by rw [he]; simp
  have hlvl : nl.level < nq.level := by
    obtain ⟨m, _, _, hm1', hm2', _, _⟩ := hgq.child hAq hlk (by simp [hql])
    rw [hAl] at hm1'
    cases hm1'
    exact hm2'
  have hql' : q ≠ l := by
    intro e
    rw [e, hAl] at hAq
    cases hAq
    omega
  have hqr' : q ≠ rr := by
    intro e
    rw [e, hAr] at hAq
    cases hAq
    omega
  have hfq : A.fuel q = nq.level + 1 := by simp [Tree.fuel, hAq]
  have hlq : l ∈ reachAt A (A.fuel q) q := by
    rw [hfq]
    exact tc_kid hAq hlk (tc_self _ _ _)
  have hrq : rr ∈ reachAt A (A.fuel q) q := by
    rw [hfq]
    exact tc_kid hAq hrk (tc_self _ _ _)
  have hlr : l ∈ reachAt A (A.fuel r) r := hG.tr_closed hq hlq
  have hrr : rr ∈ reachAt A (A.fuel r) r := hG.tr_closed hq hrq
  have hqnl : ∀ f, q ∉ reachAt A f l := fun f => hgq.tc_no_cycle hlq (Ne.symm hql') f
  have hqnr : ∀ f, q ∉ reachAt A f rr := fun f => hgq.tc_no_cycle hrq (Ne.symm hqr') f
  have hqA : ∀ z, z ∈ reachAt A (A.fuel q) q → z ∈ reachAt A (A.fuel r) r :=
    fun z hz => hG.tr_closed hq hz
  have hapart : ∀ z ∈ reachAt A nq.level rr, z ∉ reachAt A nq.level l :=
    fun z hz => (hgq.tr_side hAq hTq he (c := cR) (z := rr) (by simp) hz).2.1
  have hlA : reachAt A nq.level l = reachAt A (A.fuel l) l := hgq.tc_kid_eq hAq hlk
  have hrA : reachAt A nq.level rr = reachAt A (A.fuel rr) rr := hgq.tc_kid_eq hAq hrk
  have hal : ∀ z ∈ reachAt A (A.fuel l) l, z ≠ l → B.obj z = A.obj z := by
    intro z hz hzl
    have hzr := hG.tr_closed hlr hz
    refine hsame z (fun e => hmA (e ▸ hzr)) (fun e => hmA2 (e ▸ hzr))
      (fun e => hqnl _ (e ▸ hz)) hzl (fun e => ?_)
    rw [← hlA] at hz
    exact hapart rr (tc_self _ _ _) (e ▸ hz)
  have har : ∀ z ∈ reachAt A (A.fuel rr) rr, z ≠ rr → B.obj z = A.obj z := by
    intro z hz hzr
    have hzr' := hG.tr_closed hrr hz
    refine hsame z (fun e => hmA (e ▸ hzr')) (fun e => hmA2 (e ▸ hzr'))
      (fun e => hqnr _ (e ▸ hz)) (fun e => ?_) hzr
    rw [← hrA] at hz
    exact hapart z hz (e ▸ tc_self _ _ _)
  have hmpp : ∀ a ∈ pre ++ post, a ∈ live nq.ks := by
    intro a h'
    rw [he]
    rcases List.mem_append.mp h' with h' | h' <;> simp [h']
  have hside : ∀ c' z, (c', z) ∈ pre ++ post → ∀ z' ∈ reachAt A nq.level z,
      B.obj z' = A.obj z' := by
    intro c' z hb z' hz'
    obtain ⟨h1, h2, h3⟩ := hgq.tr_side hAq hTq he (c := c') (z := z) (tr_mem_mid hb) hz'
    obtain ⟨_, h4, _⟩ := hgq.tr_side hAq hTq he2 (c := c') (z := z) (trm_mem_snoc hb) hz'
    refine hsame z' (fun e => ?_) (fun e => ?_) h1 (fun e => h2 (e ▸ tc_self _ _ _))
      (fun e => h4 (e ▸ tc_self _ _ _))
    · rw [e, hm1] at h3
      cases h3
    · rw [e, hm2] at h3
      cases h3
  have hside' : ∀ c' z, (c', z) ∈ pre ++ post → ∀ z' ∈ reachAt A (A.fuel z) z,
      B.obj z' = A.obj z' := by
    intro c' z hb z' hz'
    rw [← hgq.tc_kid_eq hAq (hmpp _ hb)] at hz'
    exact hside c' z hb z' hz'
  have hwf : klongsWf nqb.ks = true := by
    simp only [nodeOk, Bool.and_eq_true] at hq5
    exact hq5.1.2
  have hkids : ∀ lo' hi', Good A q lo' hi' →
      (∀ t ∈ bounds (first ++ (g, y0) :: rest) (nextHi post hi'),
        KidOk B nl.level nl.leaf (max lo' cL) (nextHi post hi') t.1 t.2.1 t.2.2) ∧
      (first ++ (g, y0) :: rest).Pairwise CvLt ∧
      (first ++ (g, y0) :: rest).flatMap (fun cy => klongList B nl.leaf (L B) cy.1 cy.2) =
        L A l ++ L A rr ∧
      (first ++ (g, y0) :: rest).flatMap (fun cy => reachAt B nl.level cy.2) =
        (live nl.ks).flatMap (fun cy => reachAt A nl.level cy.2) ++
          (live nr.ks).flatMap (fun cy => reachAt A nl.level cy.2) := by
    intro lo' hi' hg
    have hgl : Good A l (max lo' cL) (some cR) := hg.tr_kid hAq hql he
    have hgr : Good A rr (max (max lo' cL) cR) (nextHi post hi') := by
      have := hg.tr_kid hAq hql he2
      rwa [show max lo' cR = max (max lo' cL) cR by omega] at this
    have hcR : belowHi cR (nextHi post hi') = true := trm_belowNext hpost2 (hg.tr_hi hAq hrk)
    rw [← hsplit]
    exact trm_kids hgl hgr hAl hAr hlev hkind hnr hcR hal har
  have hmerge : ∀ lo' hi', Good A q lo' hi' →
      Good B m1 (max lo' cL) (some g) ∧ Good B m2 (max lo' g) (nextHi post hi') ∧ cL < g ∧
        belowHi g (nextHi post hi') = true := by
    intro lo' hi' hg
    obtain ⟨hK, hS, _, _⟩ := hkids lo' hi' hg
    have hlo := trm_lo hK hS rfl hfirst
    obtain ⟨hGf, hGs⟩ := trm_split hK hS rfl hBm1 hBm2
    have hgb : belowHi g (nextHi post hi') = true :=
      (hK (g, y0, nextHi rest (nextHi post hi')) (by rw [bounds_append]; simp [bounds])).1
    refine ⟨hGf, ?_, by omega, hgb⟩
    rwa [show max (max lo' cL) g = max lo' g by omega] at hGs
  have hloc : ∀ lo' hi', Good A q lo' hi' → Good B q lo' hi' := by
    intro lo' hi' hg
    obtain ⟨hGf, hGs, _, hgb⟩ := hmerge lo' hi' hg
    have hA := hg.tr_kids hAq
    rw [he, bounds_append] at hA
    refine tr_good_of hq1 hwf ?_
    rw [hq4, hq2, hq3, bounds_append]
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · have hA' := hA t (List.mem_append_left _ ht)
      rw [hql] at hA'
      exact hA'.tr_move (hside' _ _ (List.mem_append_left _ (bounds_mem_live ht))) hA'.1
        (fun h' => (by cases h')) (fun _ => ⟨rfl, rfl⟩)
    · simp only [bounds, List.mem_cons] at ht
      rcases ht with rfl | rfl | ht
      · have hA' := hg.tr_kids hAq _ (bounds_mem hi' he)
        refine ⟨hA'.1, fun h' => (by cases h'), fun h' => (by cases h'), fun _ => ?_⟩
        exact ⟨nf, hf1, by omega, by rw [hf4]; exact hfirst, by simpa [nextHi] using hGf⟩
      · have hh : ∀ b ∈ post, belowHi b.1 hi' = true :=
          fun b hb => hg.tr_hi hAq (hmpp _ (List.mem_append_right _ hb))
        refine ⟨(below_nextHi hpp2 hh hgb).1, fun h' => (by cases h'), fun h' => (by cases h'),
          fun _ => ?_⟩
        exact ⟨ns, hs1, by omega, by rw [hs4]; split <;> simp, by simpa using hGs⟩
      · have hA' := hA t (List.mem_append_right _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ ht)))
        rw [hql] at hA'
        exact hA'.tr_move (hside' _ _ (List.mem_append_right _ (bounds_mem_live ht))) hA'.1
          (fun h' => (by cases h')) (fun _ => ⟨rfl, rfl⟩)
  obtain ⟨_, _, hLm0, hRm0⟩ := hkids loq hiq hgq
  obtain ⟨hGf0, hGs0, _, _⟩ := hmerge loq hiq hgq
  have hgqB := hloc loq hiq hgq
  have hLm : L B m1 ++ L B m2 = L A l ++ L A rr := by
    rw [← hLm0, List.flatMap_append, hGf0.L_eq hf1, hGs0.L_eq hs1, hf4, hf3, hs4, hs3]
    congr 1
    cases nl.leaf <;> simp [klongList]
  have hL : L B q = L A q := by
    rw [hgqB.L_eq hq1, hgq.L_eq hAq, hq4, he, hq3, hql]
    have hE : ∀ l' : List (Nat × NodeId), (∀ a ∈ l', a ∈ pre ++ post) →
        l'.flatMap (fun cy => klongList B false (L B) cy.1 cy.2) =
          l'.flatMap (fun cy => klongList A false (L A) cy.1 cy.2) := by
      intro l' hl'
      apply List.flatMap_congr
      rintro ⟨c, z⟩ hm
      exact tc_klongList (hside c z (hl' _ hm) z (tc_self _ _ _))
        (L_agree (hside' c z (hl' _ hm)))
    simp only [List.flatMap_append, List.flatMap_cons]
    rw [hE pre (fun a h' => List.mem_append_left _ h'),
      hE post (fun a h' => List.mem_append_right _ h')]
    simp only [klongList, Bool.false_eq_true, ite_false]
    rw [← List.append_assoc (L B m1), hLm]
    simp
  have hRE : ∀ l' : List (Nat × NodeId), (∀ a ∈ l', a ∈ pre ++ post) →
      l'.flatMap (fun cy => reachAt B nq.level cy.2) =
        l'.flatMap (fun cy => reachAt A nq.level cy.2) := by
    intro l' hl'
    apply List.flatMap_congr
    rintro ⟨c, z⟩ hm
    exact reachAt_agree _ _ (hside c z (hl' _ hm))
  have hm1B : reachAt B nq.level m1 =
      m1 :: first.flatMap (fun cy => reachAt B nl.level cy.2) := by
    rw [hGf0.reachAt_eq nq.level (by simp [Tree.fuel, hf1, hf2]; omega),
      show B.fuel m1 = nl.level + 1 by simp [Tree.fuel, hf1, hf2], tc_key hf1, hf4]
  have hm2B : reachAt B nq.level m2 =
      m2 :: ((g, y0) :: rest).flatMap (fun cy => reachAt B nl.level cy.2) := by
    rw [hGs0.reachAt_eq nq.level (by simp [Tree.fuel, hs1, hs2]; omega),
      show B.fuel m2 = nl.level + 1 by simp [Tree.fuel, hs1, hs2], tc_key hs1, hs4]
    congr 1
    cases nl.leaf <;> simp
  have hlA' : reachAt A nq.level l =
      l :: (live nl.ks).flatMap (fun cy => reachAt A nl.level cy.2) := by
    rw [hlA, show A.fuel l = nl.level + 1 by simp [Tree.fuel, hAl], tc_key hAl]
  have hrA' : reachAt A nq.level rr =
      rr :: (live nr.ks).flatMap (fun cy => reachAt A nl.level cy.2) := by
    rw [hrA, show A.fuel rr = nr.level + 1 by simp [Tree.fuel, hAr], tc_key hAr, hlev]
  have hRqA : reachAt A (A.fuel q) q = (q :: pre.flatMap (fun cy => reachAt A nq.level cy.2)) ++
      l :: ((live nl.ks).flatMap (fun cy => reachAt A nl.level cy.2) ++
        rr :: ((live nr.ks).flatMap (fun cy => reachAt A nl.level cy.2) ++
          post.flatMap (fun cy => reachAt A nq.level cy.2))) := by
    rw [hfq, tc_key hAq, he, List.flatMap_append, List.flatMap_cons, List.flatMap_cons, hlA',
      hrA']
    simp
  have hRqB : reachAt B (B.fuel q) q = (q :: pre.flatMap (fun cy => reachAt A nq.level cy.2)) ++
      m1 :: (first.flatMap (fun cy => reachAt B nl.level cy.2) ++
        m2 :: (((g, y0) :: rest).flatMap (fun cy => reachAt B nl.level cy.2) ++
          post.flatMap (fun cy => reachAt A nq.level cy.2))) := by
    rw [show B.fuel q = nq.level + 1 by simp [Tree.fuel, hq1, hq2], tc_key hq1, hq4,
      List.flatMap_append, List.flatMap_cons, List.flatMap_cons, hm1B, hm2B,
      hRE pre (fun a h' => List.mem_append_left _ h'),
      hRE post (fun a h' => List.mem_append_right _ h')]
    simp
  have hFGS : first.flatMap (fun cy => reachAt B nl.level cy.2) ++
      (((g, y0) :: rest).flatMap (fun cy => reachAt B nl.level cy.2) ++
        post.flatMap (fun cy => reachAt A nq.level cy.2)) =
      (live nl.ks).flatMap (fun cy => reachAt A nl.level cy.2) ++
        ((live nr.ks).flatMap (fun cy => reachAt A nl.level cy.2) ++
          post.flatMap (fun cy => reachAt A nq.level cy.2)) := by
    rw [← List.append_assoc, ← List.flatMap_append, hRm0, List.append_assoc]
  have hTq' := hTq
  rw [hRqA] at hTq'
  obtain ⟨hK, hlK, hrK⟩ := trm_nodup_drop hTq'
  have hR : (reachAt B (B.fuel q) q).Nodup := by
    rw [hRqB]
    refine tr_nodup_insert2 (trm_nodup_add (by rw [hFGS]; exact hK) (fun hm => ?_)) (fun hm => ?_)
    · rw [hFGS] at hm
      exact hmA (hqA m1 (by rw [hRqA]; exact trm_mem_drop hm))
    · rcases trm_mem_add hm with e | e
      · exact hne e.symm
      · rw [hFGS] at e
        exact hmA2 (hqA m2 (by rw [hRqA]; exact trm_mem_drop e))
  have hmemq : ∀ z ∈ reachAt B (B.fuel q) q,
      z ∈ reachAt A (A.fuel q) q ∨ z = m1 ∨ z = m2 := by
    intro z hz
    rw [hRqB] at hz
    rcases tr_mem_two hz with e | e | e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr e)
    · rw [hFGS] at e
      rw [hRqA]
      exact Or.inl (trm_mem_drop e)
  have hnew : ∀ z ∈ reachAt B (B.fuel q) q,
      z ∈ reachAt A (A.fuel q) q ∨ z ∉ reachAt A (A.fuel r) r := by
    intro z hz
    rcases hmemq z hz with h' | rfl | rfl
    · exact Or.inl h'
    · exact Or.inr hmA
    · exact Or.inr hmA2
  have ha : Agree A B r q := by
    intro z hz hzq
    exact hsame z (fun e => hmA (e ▸ hz)) (fun e => hmA2 (e ▸ hz))
      (fun e => hzq (e ▸ tc_self _ _ _)) (fun e => hzq (e ▸ hlq)) (fun e => hzq (e ▸ hrq))
  have hk : KeepsKind A B q := by
    intro n hn
    rw [hAq] at hn
    cases hn
    exact ⟨nqb, hq1, by omega, fun _ => by rw [hq4]; simp⟩
  have hqk : ∃ n, A.obj q = some (.key n) := ⟨nq, hAq⟩
  obtain ⟨hTB, hmemB⟩ := ctx_reach hG h.tree hq ha hk hloc hqk hR hnew
  have hgone : ∀ x, x ∈ reachAt A (A.fuel q) q → x ≠ m1 → x ≠ m2 →
      x ∉ (q :: pre.flatMap (fun cy => reachAt A nq.level cy.2)) ++
        ((live nl.ks).flatMap (fun cy => reachAt A nl.level cy.2) ++
          ((live nr.ks).flatMap (fun cy => reachAt A nl.level cy.2) ++
            post.flatMap (fun cy => reachAt A nq.level cy.2))) →
      x ∉ reachAt B (B.fuel r) r := by
    intro x hxq hxm hxm2 hxK hx
    rcases hmemB x hx with ⟨_, h2⟩ | h2
    · exact h2 hxq
    · rw [hRqB] at h2
      rcases tr_mem_two h2 with h3 | h3 | h3
      · exact hxm h3
      · exact hxm2 h3
      · rw [hFGS] at h3
        exact hxK h3
  have hlB : l ∉ reachAt B (B.fuel r) r :=
    hgone l hlq (tr_ne_of_obj hAl hm1) (tr_ne_of_obj hAl hm2) hlK
  have hrB : rr ∉ reachAt B (B.fuel r) r :=
    hgone rr hrq (tr_ne_of_obj hAr hm1) (tr_ne_of_obj hAr hm2) hrK
  have hmem : ∀ z ∈ reachAt B (B.fuel r) r,
      z ∈ reachAt A (A.fuel r) r ∨ z = m1 ∨ z = m2 := by
    intro z hz
    rcases hmemB z hz with ⟨h1, _⟩ | h1
    · exact Or.inl h1
    · rcases hmemq z h1 with h2 | h2 | h2
      · exact Or.inl (hqA z h2)
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr h2)
  refine ⟨⟨?_, Good.ctx hG h.tree hq ha hk hloc hqk, ?_, ?_, hTB⟩, hlB, hrB, hmem⟩
  · obtain ⟨n, ho, hne'⟩ := h.key
    by_cases hrq' : r = q
    · rw [hrq']
      exact ⟨nqb, hq1, Or.inr (by rw [hq4]; simp)⟩
    · have hrl : r ≠ l := fun e => hqnl _ (e ▸ hq)
      have hrr' : r ≠ rr := fun e => hqnr _ (e ▸ hq)
      exact ⟨n, (hsame r (tr_ne_of_obj ho hm1) (tr_ne_of_obj ho hm2) hrq' hrl hrr').trans ho,
        hne'⟩
  · intro z hz m hm
    by_cases hzq : z = q
    · rw [hzq, hq1] at hm
      cases hm
      rw [hzq]
      exact hq5
    by_cases hzm : z = m1
    · rw [hzm, hf1] at hm
      cases hm
      exact tr_nodeOk hf5 (by split <;> omega) (fun _ h' => h')
    by_cases hzm2 : z = m2
    · rw [hzm2, hs1] at hm
      cases hm
      exact tr_nodeOk hs5 (by split <;> omega) (fun _ h' => h')
    have hzl : z ≠ l := fun e => hlB (e ▸ hz)
    have hzr : z ≠ rr := fun e => hrB (e ▸ hz)
    have hzA : z ∈ reachAt A (A.fuel r) r := by
      rcases hmem z hz with h' | h' | h'
      · exact h'
      · exact absurd h' hzm
      · exact absurd h' hzm2
    have hAm : A.obj z = some (.key m) := by
      rw [← hsame z hzm hzm2 hzq hzl hzr]
      exact hm
    have hnA := h.nodes z hzA m hAm
    simp only [reduceCtorEq, ite_false] at hnA
    refine trm_nodeOk hnA (by split <;> omega) (fun c y hky => ?_)
    by_cases hy : y = l ∨ y = rr
    · exact hnames z hzA hzq hzl hzr m hAm c y hky hy
    by_cases hym : y = m1
    · simp [hym, hf1]
    by_cases hym2 : y = m2
    · simp [hym2, hs1]
    by_cases hyq : y = q
    · simp [hyq, hq1]
    rw [hsame y hym hym2 hyq (fun e => hy (Or.inl e)) (fun e => hy (Or.inr e))]
    exact trm_ptr hnA hky
  · rw [ctx_L hG h.tree hq ha hk hloc hqk hL]
    exact h.holds

end Contract
