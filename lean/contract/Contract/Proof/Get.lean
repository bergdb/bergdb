/-
The contract package (bergdb 030-04): a get is right. On a tree that meets
the invariants, `get` gives for every key what the tree's contents hold for
it (`get_contents`).
-/
import Contract.Proof.Good

namespace Contract

theorem ite_pos' {α : Type} {c : Prop} [Decidable c] (h : c) (a b : α) :
    (if c then a else b) = a := by simp [h]

theorem ite_neg' {α : Type} {c : Prop} [Decidable c] (h : ¬ c) (a b : α) :
    (if c then a else b) = b := by simp [h]

variable {s : Tree}

/-- A get from a sound node finds exactly what the node holds. -/
theorem Good.getGo_iff {x : NodeId} {lo : Nat} {hi : Option Nat} (h : Good s x lo hi) :
    ∀ f, s.fuel x ≤ f → ∀ k v, getGo s f k x = some v ↔ (k, v) ∈ L s x := by
  induction h with
  | mk x lo hi n hobj hwf hhi hlo hval hkey hseg hkid ihseg ihkid =>
    intro f hf k v
    have hG : Good s x lo hi := Good.mk x lo hi n hobj hwf hhi hlo hval hkey hseg hkid
    have hfuel : s.fuel x = n.level + 1 := by simp [Tree.fuel, hobj]
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    rw [hG.L_eq hobj, List.mem_flatMap]
    -- a key that a klong of a segment leaf holds starts with the klong's compare value
    have hhead : ∀ c c' y' rest, n.leaf = true →
        (c :: rest, v) ∈ klongList s n.leaf (L s) c' y' → c' = c := by
      intro c c' y' rest hl hkv
      rcases mem_klongList.mp hkv with ⟨_, _, k', hk', _⟩ | ⟨_, _, hk', _⟩ | ⟨h1, _⟩
      · injection hk' with h1 _; exact h1.symm
      · injection hk' with h1 _; exact h1.symm
      · rw [hl] at h1; simp at h1
    cases k with
    | nil =>
      simp only [getGo]
      constructor
      · intro h; simp at h
      · rintro ⟨⟨c, y⟩, hm, hkv⟩
        rcases mem_klongList.mp hkv with ⟨_, _, k', hk', _⟩ | ⟨_, _, hk', _⟩ | ⟨hl, hkv⟩
        · simp at hk'
        · simp at hk'
        · obtain ⟨m, lo', hi', hm1, _, _, hg⟩ := hG.child hobj hm (by simp [hl])
          obtain ⟨d, r, hd, _⟩ := hg.range [] v hkv
          simp at hd
    | cons c rest =>
      simp only [getGo, hobj]
      by_cases hl : n.leaf = true
      · rw [ite_pos' hl]
        rw [searchEq_spec n.ks hwf c]
        cases hlk : (live n.ks).lookup c with
        | none =>
          dsimp only
          constructor
          · intro h; simp at h
          · rintro ⟨⟨c', y'⟩, hm, hkv⟩
            have hc : c' = c := hhead c c' y' rest hl hkv
            subst hc
            have := (lookup_iff_mem (live_sorted n.ks) c' y').mpr hm
            rw [hlk] at this; simp at this
        | some y =>
          have hm : (c, y) ∈ live n.ks := (lookup_iff_mem (live_sorted n.ks) c y).mp hlk
          dsimp only
          have hR : (∃ a ∈ live n.ks, (c :: rest, v) ∈ klongList s n.leaf (L s) a.1 a.2) ↔
              (c :: rest, v) ∈ klongList s n.leaf (L s) c y := by
            constructor
            · rintro ⟨⟨c', y'⟩, hm', hkv⟩
              have hc : c' = c := hhead c c' y' rest hl hkv
              subst hc
              rw [live_unique hm hm']; exact hkv
            · intro hkv; exact ⟨(c, y), hm, hkv⟩
          rw [hR, mem_klongList]
          by_cases hlong : isLong c = true
          · obtain ⟨m, hm1, hm2, hm3⟩ := hkey c y hm (fun _ => hlong)
            have hfy : s.fuel y = m.level + 1 := by simp [Tree.fuel, hm1]
            cases rest with
            | nil =>
              rw [show s.val y = none by simp [Tree.val, hm1]]
              constructor
              · intro h; simp at h
              · rintro (⟨_, _, k', hk', hkv⟩ | ⟨_, h2, _⟩ | ⟨h1, _⟩)
                · injection hk' with _ h2
                  subst h2
                  obtain ⟨d, r, hd, _⟩ := (hseg hl c y hm hlong).range [] v hkv
                  simp at hd
                · rw [hlong] at h2; simp at h2
                · rw [hl] at h1; simp at h1
            | cons r0 rs =>
              dsimp only
              rw [ihseg hl c y hm hlong f' (by omega) (r0 :: rs) v]
              constructor
              · intro hkv; exact Or.inl ⟨hl, hlong, r0 :: rs, rfl, hkv⟩
              · rintro (⟨_, _, k', hk', hkv⟩ | ⟨_, h2, _⟩ | ⟨h1, _⟩)
                · injection hk' with _ h2; rw [h2]; exact hkv
                · rw [hlong] at h2; simp at h2
                · rw [hl] at h1; simp at h1
          · have hlong' : isLong c = false := by simpa using hlong
            obtain ⟨w, hw⟩ := hval hl c y hm hlong'
            cases rest with
            | nil =>
              rw [show s.val y = some w by simp [Tree.val, hw]]
              constructor
              · intro h
                injection h with h
                subst h
                exact Or.inr (Or.inl ⟨hl, hlong', rfl, hw⟩)
              · rintro (⟨_, h2, _⟩ | ⟨_, _, _, h4⟩ | ⟨h1, _⟩)
                · rw [hlong'] at h2; simp at h2
                · rw [hw] at h4; injection h4 with h4; injection h4 with h4; rw [h4]
                · rw [hl] at h1; simp at h1
            | cons r0 rs =>
              dsimp only
              have hnone : getGo s f' (r0 :: rs) y = none := by
                cases f' with
                | zero => rfl
                | succ f'' => simp [getGo, hw]
              rw [hnone]
              constructor
              · intro h; simp at h
              · rintro (⟨_, h2, _⟩ | ⟨_, _, h3, _⟩ | ⟨h1, _⟩)
                · rw [hlong'] at h2; simp at h2
                · simp at h3
                · rw [hl] at h1; simp at h1
      · have hl' : n.leaf = false := by simpa using hl
        rw [ite_neg' hl]
        rw [searchLte_spec]
        cases hs : ((live n.ks).filter (fun cy => !(Pos.at c).below cy.1)).getLast? with
        | none =>
          dsimp only
          constructor
          · intro h; simp at h
          · rintro ⟨⟨c', y'⟩, hm, hkv⟩
            have hkv' : (c :: rest, v) ∈ L s y' := by simpa [klongList, hl'] using hkv
            obtain ⟨pre, post, he⟩ := List.append_of_mem hm
            obtain ⟨d, r, hd, hd1, _⟩ := (hkid hl' pre c' y' post he).range _ _ hkv'
            injection hd with hd _
            subst hd
            have hmf : (c', y') ∈ (live n.ks).filter (fun cy => !(Pos.at c).below cy.1) := by
              rw [List.mem_filter]
              refine ⟨hm, ?_⟩
              have : c' ≤ c := le_trans (le_max_right _ _) hd1
              simp [Pos.below]; omega
            rw [List.getLast?_eq_none_iff] at hs
            rw [hs] at hmf
            simp at hmf
        | some a =>
          obtain ⟨c', y⟩ := a
          dsimp only
          obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hs
          have hmf : (c', y) ∈ (live n.ks).filter (fun cy => !(Pos.at c).below cy.1) := by
            rw [hys]; simp
          have hm : (c', y) ∈ live n.ks := (List.mem_filter.mp hmf).1
          have hc' : c' ≤ c := by
            have := (List.mem_filter.mp hmf).2
            simp [Pos.below] at this
            omega
          have hmax : ∀ c'' y'', (c'', y'') ∈ live n.ks → c'' ≤ c → c'' ≤ c' := by
            intro c'' y'' hm'' hle
            have h1 : (c'', y'') ∈ (live n.ks).filter (fun cy => !(Pos.at c).below cy.1) := by
              rw [List.mem_filter]
              refine ⟨hm'', ?_⟩
              simp [Pos.below]; omega
            have hsorted := (live_sorted n.ks).filter (fun cy => !(Pos.at c).below cy.1)
            rw [hys] at h1 hsorted
            rw [List.pairwise_append] at hsorted
            rcases List.mem_append.mp h1 with h2 | h2
            · exact le_of_lt (hsorted.2.2 _ h2 (c', y) (by simp))
            · simp at h2; omega
          obtain ⟨pre, post, he⟩ := List.append_of_mem hm
          obtain ⟨m, hm1, hm2, _⟩ := hkey c' y hm (by simp [hl'])
          have hfy : s.fuel y = m.level + 1 := by simp [Tree.fuel, hm1]
          rw [ihkid hl' pre c' y post he f' (by omega) (c :: rest) v]
          constructor
          · intro hkv; exact ⟨(c', y), hm, by simpa [klongList, hl'] using hkv⟩
          · rintro ⟨⟨c'', y''⟩, hm'', hkv⟩
            have hkv' : (c :: rest, v) ∈ L s y'' := by simpa [klongList, hl'] using hkv
            obtain ⟨pre', post', he'⟩ := List.append_of_mem hm''
            obtain ⟨d, r, hd, hd1, hd2⟩ := (hkid hl' pre' c'' y'' post' he').range _ _ hkv'
            injection hd with hd _
            subst hd
            obtain ⟨hpre', _, hpp'⟩ := live_split he'
            have hbn := below_nextHi hpp' (fun b hb => hhi b.1 b.2 (by rw [he']; simp [hb])) hd2
            have h1 : c'' ≤ c' := hmax c'' y'' hm'' (le_trans (le_max_right _ _) hd1)
            have h2 : c'' = c' := by
              by_contra hne
              have hlt : c'' < c' := lt_of_le_of_ne h1 hne
              have h3 : (c', y) ∈ post' := by
                have hm0 := hm
                rw [he'] at hm0
                rcases List.mem_append.mp hm0 with h3 | h3
                · have := hpre' _ h3
                  simp at this; omega
                · rcases List.mem_cons.mp h3 with h3 | h3
                  · injection h3 with h3 _; omega
                  · exact h3
              have := hbn.2 _ h3
              simp at this; omega
            subst h2
            rw [live_unique hm hm'']; exact hkv'

/-- TP10 for one tree: on a tree that meets the invariants, a get gives what
the contents hold for the key. -/
theorem get_contents {p : Params} (h : invOk p s = true) (k : Key) :
    get s k = (contents s).lookup k := by
  unfold invOk at h
  unfold get contents
  cases hr : s.root with
  | none => simp [hr] at h
  | some r =>
    simp only [hr] at h ⊢
    cases ho : s.obj r with
    | none => simp [ho] at h
    | some o =>
      rw [ho] at h
      cases o with
      | val v => simp at h
      | key n =>
        simp only [Bool.and_eq_true] at h
        have hG : Good s r 0 none := walk_good _ _ _ _ h.2
        apply Option.ext
        intro v
        rw [hG.getGo_iff _ (le_refl _)]
        show (k, v) ∈ L s r ↔ List.lookup k (L s r) = some v
        rw [lookup_iff_mem hG.sorted]

end Contract
