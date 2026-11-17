/-
The contract package (bergdb 030-10): the delete's first rule as a statement
about two trees: the segment leaf that the key is routed to loses the live
klong of the key's last segment (a bitmap, `Dag.appendDeleteKlong`), and
keeps a live klong, or is the space root. Then the tree holds the keys with
the delete applied; no node is made, and the nodes reached are among those
reached before.
-/
import Contract.Proof.TreeRules

namespace Contract

/-- A route that ends where it starts leaves the key as it is. -/
theorem Route.tr_self {A : Tree} {u q : NodeId} {k k' : Key} (hr : Route A u k q k')
    {lo : Nat} {hi : Option Nat} (hG : Good A u lo hi) (huq : u = q) : k = k' := by
  cases hr with
  | here => rfl
  | inner _ n c y _ _ _ _ hobj hl hm _ _ hry =>
    exfalso
    obtain ⟨m, lo', hi', _, _, _, hg⟩ := hG.child hobj hm (by simp [hl])
    have h1 := (hry.tc_target hg).2
    rw [← hG.tc_kid_eq hobj hm, ← huq] at h1
    exact hG.not_below hobj hm _ h1
  | leaf _ n c y _ _ _ hobj _ hm hlong hry =>
    exfalso
    obtain ⟨m, lo', hi', _, _, _, hg⟩ := hG.child hobj hm (fun _ => hlong)
    have h1 := (hry.tc_target hg).2
    rw [← hG.tc_kid_eq hobj hm, ← huq] at h1
    exact hG.not_below hobj hm _ h1

theorem Sound.del {M : Nat} {ex' : Option NodeId} {A B : Tree} {r x : NodeId}
    {C : List (Key × Nat)} {nx : KNode} {k : Key} {cv : Nat}
    (h : Sound M none A r C) (hr : Route A r k x [cv]) (hAx : A.obj x = some (.key nx))
    (hleaf : nx.leaf = true) (hcv : isLong cv = false)
    (hkeep : (live nx.ks).filter (fun a => a.1 != cv) ≠ [] ∨ x = r)
    (hBx : NodeIs B x nx.level true ((live nx.ks).filter (fun a => a.1 != cv)) (bnd M ex' x))
    (hsame : ∀ z, z ≠ x → B.obj z = A.obj z) :
    Sound M ex' B r (mapDel k C) ∧
      ∀ z ∈ reachAt B (B.fuel r) r, z ∈ reachAt A (A.fuel r) r := by
  obtain ⟨nb, hb1, hb2, hb3, hb4, hb5⟩ := hBx
  have hG := h.good
  have hK0 : KeyIn k 0 none := fun _ _ _ => ⟨Nat.zero_le _, rfl⟩
  have hxr := (hr.tc_target hG).2
  obtain ⟨lox, hix, hgx, _⟩ := hr.tr_target hG hK0
  have hxA : ∀ z ∈ reachAt A (A.fuel x) x, z ≠ x → B.obj z = A.obj z :=
    fun z _ hz => hsame z hz
  have hka := fun c z (hm : (c, z) ∈ live nx.ks) => hgx.tr_kids_agree hAx hxA hm
  have hfm : ∀ a ∈ (live nx.ks).filter (fun a => a.1 != cv), a ∈ live nx.ks :=
    fun a ha => List.mem_of_mem_filter ha
  have hwf : klongsWf nb.ks = true := by
    simp only [nodeOk, Bool.and_eq_true] at hb5
    exact hb5.1.2
  have hloc : ∀ lo' hi', Good A x lo' hi' → Good B x lo' hi' := by
    intro lo' hi' hg
    refine tr_good_of hb1 hwf ?_
    rw [hb4, hb2, hb3]
    rintro ⟨c, z, H⟩ ht
    have hm := hfm _ (bounds_mem_live ht)
    obtain ⟨p1, p2, he⟩ := List.append_of_mem hm
    have hA := hg.tr_kids hAx _ (bounds_mem hi' he)
    rw [hleaf] at hA
    exact hA.tr_move (hka _ _ hm) hA.1 (fun _ => ⟨rfl, hA.2.1 rfl⟩) (fun h' => (by cases h'))
  have hgBx := hloc lox hix hgx
  have hL : L B x = mapDel [cv] (L A x) := by
    rw [hgBx.L_eq hb1, hgx.L_eq hAx, hb4, hb3, hleaf]
    have main : ∀ l : List (Nat × NodeId), (∀ a ∈ l, a ∈ live nx.ks) →
        (l.filter (fun a => a.1 != cv)).flatMap (fun cy => klongList B true (L B) cy.1 cy.2) =
          mapDel [cv] (l.flatMap (fun cy => klongList A true (L A) cy.1 cy.2)) := by
      intro l
      induction l with
      | nil => intro _; rfl
      | cons a l ih =>
        intro hl
        obtain ⟨c, z⟩ := a
        have hm : (c, z) ∈ live nx.ks := hl _ List.mem_cons_self
        have ih' := ih (fun b hb => hl b (List.mem_cons_of_mem _ hb))
        unfold mapDel at ih' ⊢
        rw [List.flatMap_cons, List.filter_append, ← ih']
        by_cases hc : c = cv
        · subst hc
          rw [List.filter_cons_of_neg (p := fun a : Nat × NodeId => a.1 != c) (by simp)]
          have h0 : (klongList A true (L A) c z).filter (fun kv => kv.1 != [c]) = [] := by
            unfold klongList
            simp only [hcv, ite_true, Bool.false_eq_true, ite_false]
            split <;> simp
          simp [h0]
        · have hne : ((c, z).1 != cv) = true := by simpa using hc
          rw [List.filter_cons_of_pos (p := fun a : Nat × NodeId => a.1 != cv) hne,
            List.flatMap_cons, tc_klongList (hka c z hm z (tc_self _ _ _)) (L_agree (hka c z hm))]
          congr 1
          symm
          rw [List.filter_eq_self]
          rintro ⟨k0, v0⟩ hkv
          rcases mem_klongList.mp hkv with ⟨_, _, k1, rfl, _⟩ | ⟨_, _, rfl, _⟩ | ⟨hl', _⟩
          · simp [hc]
          · simp [hc]
          · cases hl'
    exact main _ (fun a h' => h')
  have hRB : reachAt B (B.fuel x) x = x :: ((live nx.ks).filter (fun a => a.1 != cv)).flatMap
      (fun cy => reachAt A nx.level cy.2) := by
    rw [show B.fuel x = nx.level + 1 by simp [Tree.fuel, hb1, hb2], tc_key hb1, hb4]
    congr 1
    apply List.flatMap_congr
    rintro ⟨c, z⟩ hm
    refine reachAt_agree _ _ (fun z' hz' => ?_)
    rw [hgx.tc_kid_eq hAx (hfm _ hm)] at hz'
    exact hka c z (hfm _ hm) z' hz'
  have hRA : reachAt A (A.fuel x) x =
      x :: (live nx.ks).flatMap (fun cy => reachAt A nx.level cy.2) := by
    rw [show A.fuel x = nx.level + 1 by simp [Tree.fuel, hAx], tc_key hAx]
  have hsub : (reachAt B (B.fuel x) x).Sublist (reachAt A (A.fuel x) x) := by
    rw [hRB, hRA]
    exact (List.filter_sublist.flatMap _).cons_cons x
  have hR : (reachAt B (B.fuel x) x).Nodup := (hG.tr_nodup h.tree hxr).sublist hsub
  have hs : ∀ w, (A.obj w).isSome = true → (B.obj w).isSome = true := by
    intro w hw
    by_cases hwx : w = x
    · simp [hwx, hb1]
    · rw [hsame w hwx]
      exact hw
  have hnodes : ∀ z, z ∈ reachAt A (A.fuel r) r → ∀ m, B.obj z = some (.key m) →
      nodeOk ⟨if ex' = some z then M + 3 else M⟩ B m = true := by
    intro z hzA m hm
    by_cases hzx : z = x
    · rw [hzx, hb1] at hm
      cases hm
      rw [hzx]
      exact hb5
    · exact h.tr_old hs hzA (fun e => by cases e) (hsame z hzx) hm (by split <;> omega)
  by_cases hxr' : x = r
  · subst hxr'
    have hk : k = [cv] := hr.tr_self hG rfl
    refine ⟨⟨⟨nb, hb1, Or.inl hb3⟩, hloc 0 none hG, ?_, ?_, hR⟩, fun z hz => hsub.subset hz⟩
    · intro z hz m hm
      exact hnodes z (hsub.subset hz) m hm
    · rw [hL, h.holds, hk]
  · have hkeep' := hkeep.resolve_right hxr'
    have hk : KeepsKind A B x := by
      intro n hn
      rw [hAx] at hn
      cases hn
      exact ⟨nb, hb1, by omega, fun _ => by rw [hb4]; exact hkeep'⟩
    have ha : Agree A B r x := fun z _ hzx => hsame z (fun e => hzx (e ▸ tc_self _ _ _))
    have hqk : ∃ n, A.obj x = some (.key n) := ⟨nx, hAx⟩
    obtain ⟨hTB, hmemB⟩ := ctx_reach hG h.tree hxr ha hk hloc hqk hR
      (fun z hz => Or.inl (hsub.subset hz))
    have hmem : ∀ z ∈ reachAt B (B.fuel r) r, z ∈ reachAt A (A.fuel r) r := by
      intro z hz
      rcases hmemB z hz with ⟨h1, _⟩ | h1
      · exact h1
      · exact hG.tr_closed hxr (hsub.subset h1)
    refine ⟨⟨?_, Good.ctx hG h.tree hxr ha hk hloc hqk, ?_, ?_, hTB⟩, hmem⟩
    · obtain ⟨n, ho, hne⟩ := h.key
      exact ⟨n, (hsame r (Ne.symm hxr')).trans ho, hne⟩
    · intro z hz m hm
      exact hnodes z (hmem z hz) m hm
    · rw [ctx_route hG h.tree ha hk hloc mapDel_local hr hL, h.holds]

end Contract
