/-
The contract package (bergdb 030-10): a put that makes a new segment leaf, as
a statement about two trees. The key is routed to the segment leaf x with the
segments cv :: rest left, and x has no live klong of cv: the tree of the next
segment does not exist. In B, x has the klong (cv, c1), and c1 is the head of
a chain of new segment leaves, one for each segment of `rest`, each with one
live klong: the next segment's leaf, and at the end the new value
(`NewChain`). Then B holds the keys with the put applied.
-/
import Contract.Proof.TreeRules

namespace Contract

/-- A chain of new nodes in B (no nodes of A) that holds the one key `key`
with the value hash `hval`: node y, a segment leaf on level lv within the
node size M, has one live klong, of the key's first segment: for the last
segment a short one that names a new value; else a long one that names the
next node of the chain, on a lower level. The ids of the chain's nodes, the
value last: all distinct. -/
inductive NewChain (M : Nat) (A B : Tree) (hval : Nat) : NodeId → Nat → Key → List NodeId → Prop
    where
  | last (y v : NodeId) (lv c : Nat) : A.obj y = none → A.obj v = none → y ≠ v →
      NodeIs B y lv true [(c, v)] M → isLong c = false → B.obj v = some (.val hval) →
      NewChain M A B hval y lv [c] [y, v]
  | step (y y' : NodeId) (lv lv' c : Nat) (rest : Key) (ids : List NodeId) : A.obj y = none →
      y ∉ ids → NodeIs B y lv true [(c, y')] M → isLong c = true → lv' < lv →
      NewChain M A B hval y' lv' rest ids → NewChain M A B hval y lv (c :: rest) (y :: ids)

/-- What a new chain is in B: its head is a sound segment root that holds the
one key, reaches exactly the chain's nodes, all distinct and new, each within
the node size. -/
theorem NewChain.tr_props {M : Nat} {A B : Tree} {hval : Nat} {y : NodeId} {lv : Nat}
    {key : Key} {ids : List NodeId} (h : NewChain M A B hval y lv key ids) :
    (∃ n, B.obj y = some (.key n) ∧ n.level = lv ∧ live n.ks ≠ []) ∧ Good B y 0 none ∧
      L B y = [(key, hval)] ∧ reachAt B (B.fuel y) y = ids ∧ ids.Nodup ∧
      (∀ z ∈ ids, A.obj z = none) ∧
      (∀ z ∈ ids, ∀ m, B.obj z = some (.key m) → nodeOk ⟨M⟩ B m = true) := by
  induction h with
  | last y v lv c hy hv hyv hB hc hBv =>
    obtain ⟨n, h1, h2, h3, h4, h5⟩ := hB
    have hwf : klongsWf n.ks = true := by
      simp only [nodeOk, Bool.and_eq_true] at h5
      exact h5.1.2
    have hG : Good B y 0 none := by
      refine tr_good_of h1 hwf ?_
      rw [h4, h3]
      intro t ht
      simp only [bounds, nextHi, List.mem_cons, List.not_mem_nil, or_false] at ht
      subst ht
      refine ⟨rfl, fun _ => Nat.zero_le _, fun _ _ => ⟨hval, hBv⟩, fun hk => ?_⟩
      have := hk rfl
      rw [hc] at this
      cases this
    refine ⟨⟨n, h1, h2, by rw [h4]; simp⟩, hG, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hG.L_eq h1, h4, h3]
      simp [klongList, hc, hBv]
    · rw [show B.fuel y = lv + 1 by simp [Tree.fuel, h1, h2], tc_key h1, h4]
      simp [tc_val hBv]
    · simp [hyv]
    · intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · exact hy
      · exact hv
    · intro z hz m hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · rw [h1] at hm
        cases hm
        exact h5
      · rw [hBv] at hm
        cases hm
  | step y y' lv lv' c rest ids hy hyids hB hc hlt _ ih =>
    obtain ⟨n, h1, h2, h3, h4, h5⟩ := hB
    obtain ⟨⟨m, hm1, hm2, hm3⟩, hG', hL', hR', hN', hA', hO'⟩ := ih
    have hwf : klongsWf n.ks = true := by
      simp only [nodeOk, Bool.and_eq_true] at h5
      exact h5.1.2
    have hG : Good B y 0 none := by
      refine tr_good_of h1 hwf ?_
      rw [h4, h3]
      intro t ht
      simp only [bounds, nextHi, List.mem_cons, List.not_mem_nil, or_false] at ht
      subst ht
      refine ⟨rfl, fun _ => Nat.zero_le _, fun _ hs => ?_, fun _ => ?_⟩
      · rw [hc] at hs
        cases hs
      · exact ⟨m, hm1, by omega, hm3, by simpa using hG'⟩
    refine ⟨⟨n, h1, h2, by rw [h4]; simp⟩, hG, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hG.L_eq h1, h4, h3]
      simp [klongList, hc, hL']
    · rw [show B.fuel y = lv + 1 by simp [Tree.fuel, h1, h2], tc_key h1, h4]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [hG'.reachAt_eq lv (by simp [Tree.fuel, hm1]; omega), hR']
    · exact List.nodup_cons.mpr ⟨hyids, hN'⟩
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hy
      · exact hA' z hz
    · intro z hz m' hm'
      rcases List.mem_cons.mp hz with rfl | hz
      · rw [h1] at hm'
        cases hm'
        exact h5
      · exact hO' z hz m' hm'

theorem Sound.putSeg {M : Nat} {ex' : Option NodeId} {A B : Tree} {r x c1 : NodeId}
    {C : List (Key × Nat)} {nx : KNode} {key rest : Key} {cv hval lv : Nat} {ids : List NodeId}
    (h : Sound M none A r C) (hr : Route A r key x (cv :: rest))
    (hAx : A.obj x = some (.key nx)) (hleaf : nx.leaf = true) (hcv : isLong cv = true)
    (hno : ∀ y, (cv, y) ∉ live nx.ks) (hch : NewChain M A B hval c1 lv rest ids)
    (hlev : lv < nx.level)
    (hBx : NodeIs B x nx.level true (insertCv cv c1 (live nx.ks)) (bnd M ex' x))
    (hsame : ∀ z, z ≠ x → z ∉ ids → B.obj z = A.obj z) :
    Sound M ex' B r (mapPut key hval C) ∧
      ∀ z ∈ reachAt B (B.fuel r) r, z ∈ reachAt A (A.fuel r) r ∨ z ∈ ids := by
  obtain ⟨nb, hb1, hb2, hb3, hb4, hb5⟩ := hBx
  obtain ⟨⟨mc, hc1, hc2, hc3⟩, hGc, hLc, hRc, hNc, hAc, hOc⟩ := hch.tr_props
  have hG := h.good
  have hK0 : KeyIn key 0 none := fun _ _ _ => ⟨Nat.zero_le _, rfl⟩
  have hxr := (hr.tc_target hG).2
  obtain ⟨lox, hix, hgx, hKx⟩ := hr.tr_target hG hK0
  have hidsA : ∀ z ∈ ids, z ∉ reachAt A (A.fuel r) r := by
    intro z hz hm
    have := hG.tr_exists _ z hm
    simp [hAc z hz] at this
  have hidsx : ∀ z ∈ reachAt A (A.fuel x) x, z ∉ ids :=
    fun z hz hzi => hidsA z hzi (hG.tr_closed hxr hz)
  have hxA : ∀ z ∈ reachAt A (A.fuel x) x, z ≠ x → B.obj z = A.obj z :=
    fun z hz hzx => hsame z hzx (hidsx z hz)
  have hka := fun c z (hm : (c, z) ∈ live nx.ks) => hgx.tr_kids_agree hAx hxA hm
  obtain ⟨pre, old, post, hlv, hold, hins, hpre, hpost⟩ := tr_insertCv cv c1 (live_sorted nx.ks)
  have hold0 : old = [] := by
    rcases hold with e | ⟨y0, e⟩
    · exact e
    · exfalso
      apply hno y0
      rw [hlv, e]
      simp
  rw [hold0, List.append_nil] at hlv
  rw [hins] at hb4
  have hmpre : ∀ a ∈ pre, a ∈ live nx.ks := fun a ha => by rw [hlv]; simp [ha]
  have hmpost : ∀ a ∈ post, a ∈ live nx.ks := fun a ha => by rw [hlv]; simp [ha]
  have hwf : klongsWf nb.ks = true := by
    simp only [nodeOk, Bool.and_eq_true] at hb5
    exact hb5.1.2
  have hloc : ∀ lo' hi', Good A x lo' hi' → KeyIn (cv :: rest) lo' hi' → Good B x lo' hi' := by
    intro lo' hi' hg hK
    obtain ⟨hK1, hK2⟩ := hK cv rest rfl
    have hold' : ∀ t : Nat × NodeId × Option Nat, (t.1, t.2.1) ∈ live nx.ks →
        KidOk B nx.level true lo' hi' t.1 t.2.1 t.2.2 := by
      rintro ⟨c, z, H⟩ hm
      obtain ⟨p1, p2, he⟩ := List.append_of_mem hm
      have hA := hg.tr_kids hAx _ (bounds_mem hi' he)
      rw [hleaf] at hA
      exact hA.tr_move (hka _ _ hm) hA.1 (fun _ => ⟨rfl, hA.2.1 rfl⟩) (fun h' => (by cases h'))
    refine tr_good_of hb1 hwf ?_
    rw [hb4, hb2, hb3, bounds_append]
    intro t ht
    simp only [bounds, List.mem_append, List.mem_cons] at ht
    rcases ht with ht | rfl | ht
    · exact hold' t (hmpre _ (bounds_mem_live ht))
    · refine ⟨hK2, fun _ => hK1, fun _ hs => ?_, fun _ => ?_⟩
      · rw [hcv] at hs
        cases hs
      · exact ⟨mc, hc1, by omega, hc3, by simpa using hGc⟩
    · exact hold' t (hmpost _ (bounds_mem_live ht))
  have hk : KeepsKind A B x := by
    intro n hn
    rw [hAx] at hn
    cases hn
    exact ⟨nb, hb1, by omega, fun _ => by rw [hb4]; simp⟩
  have ha : Agree A B r x :=
    fun z hz hzx => hsame z (fun h => hzx (h ▸ tc_self _ _ _)) (fun hi => hidsA z hi hz)
  have hGB := tr_route_good hk hloc hr hG hK0 h.tree ha
  have hgBx := hloc lox hix hgx hKx
  have hL : L B x = mapPut (cv :: rest) hval (L A x) := by
    rw [hgBx.L_eq hb1, hgx.L_eq hAx, hb4, hb3, hlv, hleaf]
    simp only [List.flatMap_append, List.flatMap_cons]
    have hE : ∀ l : List (Nat × NodeId), (∀ a ∈ l, a ∈ live nx.ks) →
        l.flatMap (fun cy => klongList B true (L B) cy.1 cy.2) =
          l.flatMap (fun cy => klongList A true (L A) cy.1 cy.2) := by
      intro l hl
      apply List.flatMap_congr
      rintro ⟨c, z⟩ hm
      exact tc_klongList (hka c z (hl _ hm) z (tc_self _ _ _)) (L_agree (hka c z (hl _ hm)))
    have hv' : klongList B true (L B) cv c1 = [(cv :: rest, hval)] := by
      simp [klongList, hcv, hLc]
    rw [hE pre hmpre, hE post hmpost, hv']
    have hmid := (mapPut_local hval).mid (cv :: rest)
      (pre.flatMap (fun cy => klongList A true (L A) cy.1 cy.2)) []
      (post.flatMap (fun cy => klongList A true (L A) cy.1 cy.2)) ?_ ?_
    · simp only [List.append_assoc, List.nil_append] at hmid ⊢
      rw [hmid]
      rfl
    · rintro ⟨k0, v0⟩ h0
      obtain ⟨⟨c0, z0⟩, h0, hkv⟩ := List.mem_flatMap.mp h0
      have hc0 : c0 < cv := hpre (c0, z0) h0
      rcases mem_klongList.mp hkv with ⟨_, _, k1, rfl, _⟩ | ⟨_, _, rfl, _⟩ | ⟨hl', _⟩
      · exact cons_lt_cons_of_lt hc0 _ _
      · exact cons_lt_cons_of_lt hc0 _ _
      · cases hl'
    · rintro ⟨k2, v2⟩ h2
      obtain ⟨⟨c2, z2⟩, h2, hkv⟩ := List.mem_flatMap.mp h2
      have hc2 : cv < c2 := hpost (c2, z2) h2
      rcases mem_klongList.mp hkv with ⟨_, _, k1, rfl, _⟩ | ⟨_, _, rfl, _⟩ | ⟨hl', _⟩
      · exact cons_lt_cons_of_lt hc2 _ _
      · exact cons_lt_cons_of_lt hc2 _ _
      · cases hl'
  have hRE : ∀ l : List (Nat × NodeId), (∀ a ∈ l, a ∈ live nx.ks) →
      l.flatMap (fun cy => reachAt B nx.level cy.2) =
        l.flatMap (fun cy => reachAt A nx.level cy.2) := by
    intro l hl
    apply List.flatMap_congr
    rintro ⟨c, z⟩ hm
    refine reachAt_agree _ _ (fun z' hz' => ?_)
    rw [hgx.tc_kid_eq hAx (hl _ hm)] at hz'
    exact hka c z (hl _ hm) z' hz'
  have hRB : reachAt B (B.fuel x) x = x :: (pre.flatMap (fun cy => reachAt A nx.level cy.2) ++
      (ids ++ post.flatMap (fun cy => reachAt A nx.level cy.2))) := by
    rw [show B.fuel x = nx.level + 1 by simp [Tree.fuel, hb1, hb2], tc_key hb1, hb4,
      List.flatMap_append, List.flatMap_cons, hRE pre hmpre, hRE post hmpost,
      hGc.reachAt_eq nx.level (by simp [Tree.fuel, hc1]; omega), hRc]
  have hRA : reachAt A (A.fuel x) x = x :: (pre.flatMap (fun cy => reachAt A nx.level cy.2) ++
      post.flatMap (fun cy => reachAt A nx.level cy.2)) := by
    rw [show A.fuel x = nx.level + 1 by simp [Tree.fuel, hAx], tc_key hAx, hlv,
      List.flatMap_append]
  have hTx := hG.tr_nodup h.tree hxr
  have hR : (reachAt B (B.fuel x) x).Nodup := by
    rw [hRA, List.nodup_cons] at hTx
    rw [hRB, List.nodup_cons, (List.perm_append_comm_assoc _ _ _).nodup_iff, List.nodup_append]
    have hxi : x ∉ ids := hidsx x (tc_self _ _ _)
    refine ⟨fun hm => ?_, hNc, hTx.2, fun a ha b hb e => ?_⟩
    · rcases List.mem_append.mp hm with hm | hm
      · exact hTx.1 (List.mem_append_left _ hm)
      rcases List.mem_append.mp hm with hm | hm
      · exact hxi hm
      · exact hTx.1 (List.mem_append_right _ hm)
    · subst e
      refine hidsx a ?_ ha
      rw [hRA]
      exact List.mem_cons_of_mem _ hb
  have hxmem : ∀ z ∈ reachAt B (B.fuel x) x, z ∈ reachAt A (A.fuel x) x ∨ z ∈ ids := by
    intro z hz
    rw [hRB] at hz
    rw [hRA]
    simp only [List.mem_cons, List.mem_append] at hz ⊢
    tauto
  have hnew : ∀ z ∈ reachAt B (B.fuel x) x,
      z ∈ reachAt A (A.fuel x) x ∨ z ∉ reachAt A (A.fuel r) r := by
    intro z hz
    rcases hxmem z hz with h' | h'
    · exact Or.inl h'
    · exact Or.inr (hidsA z h')
  obtain ⟨P, S, hPA, hPB⟩ := tr_route_split hk hloc hr hG hK0 h.tree ha
  obtain ⟨hTB, hmemB⟩ := tr_split_concl hPA hPB h.tree hR hnew
  have hmem : ∀ z ∈ reachAt B (B.fuel r) r, z ∈ reachAt A (A.fuel r) r ∨ z ∈ ids := by
    intro z hz
    rcases hmemB z hz with ⟨h1, _⟩ | h1
    · exact Or.inl h1
    · rcases hxmem z h1 with h2 | h2
      · exact Or.inl (hG.tr_closed hxr h2)
      · exact Or.inr h2
  have hs : ∀ z, (A.obj z).isSome = true → (B.obj z).isSome = true := by
    intro z hz
    by_cases hzx : z = x
    · simp [hzx, hb1]
    · by_cases hzi : z ∈ ids
      · rw [hAc z hzi] at hz
        cases hz
      · rw [hsame z hzx hzi]
        exact hz
  refine ⟨⟨?_, hGB, ?_, ?_, hTB⟩, hmem⟩
  · obtain ⟨n, ho, hne⟩ := h.key
    by_cases hrx : r = x
    · rw [hrx]
      exact ⟨nb, hb1, Or.inl hb3⟩
    · have hri : r ∉ ids := by
        intro hi
        rw [hAc r hi] at ho
        cases ho
      exact ⟨n, (hsame r hrx hri).trans ho, hne⟩
  · intro z hz m hm
    by_cases hzx : z = x
    · rw [hzx, hb1] at hm
      cases hm
      rw [hzx]
      exact hb5
    · rcases hmem z hz with hzA | hzi
      · have hzi : z ∉ ids := fun hi => hidsA z hi hzA
        exact h.tr_old hs hzA (fun e => by cases e) (hsame z hzx hzi) hm (by split <;> omega)
      · exact tr_nodeOk (hOc z hzi m hm) (by split <;> omega) (fun _ h' => h')
  · rw [tr_route_L hk hloc (mapPut_local hval) hL hr hG hK0 h.tree ha, h.holds]

end Contract
