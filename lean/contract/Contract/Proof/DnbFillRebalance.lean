/-
bergdb 030-37: virtual fill conditions through arbitrary-height joins
and their recursive rebalances. This is structural fill accounting, not
the unrestricted dirty-node cost bound.
-/
import Contract.Proof.DnbFillVirtual

namespace Contract.PE

open DNB PeProof

variable {cf : Cfg} {i : Time} {s : Tree}

theorem joinLoop_ne_nil {g h : Nat} {down : List (Nat × VN) → Option (List (Nat × VN))} :
    ∀ (n : Nat) {es es' : List (Nat × VN)}, es ≠ [] →
      joinLoop cf i s g h down n es = some es' → es' ≠ []
  | 0, es, es', hne, hj => by
    simp only [joinLoop, Option.some.injEq] at hj
    cases hj
    exact hne
  | n + 1, es, es', hne, hj => by
    rw [joinLoop] at hj
    split at hj
    · cases hj; exact hne
    · rename_i hlen
      cases hs : findSmall cf es with
      | none => rw [hs] at hj; cases hj; exact hne
      | some ix =>
        rw [hs] at hj
        simp only at hj
        cases hstep : joinAt cf i s g h down es ix with
        | none => rw [hstep] at hj; cases hj
        | some es1 =>
          rw [hstep] at hj
          have hl := joinAt_length hstep
          have hne1 : es1 ≠ [] := by intro hz; rw [hz, List.length_nil] at hl; omega
          exact joinLoop_ne_nil n hne1 hj

theorem rebalance_ne_nil {f g h : Nat} {es es' : List (Nat × VN)}
    (hne : ∀ e ∈ es, e.2.isEmpty = false) (hes : es ≠ [])
    (hr : rebalance cf i s f g h es = some es') : es' ≠ [] := by
  cases f with
  | zero => simp [rebalance] at hr
  | succ f =>
    have hk : kept es = es := filter_head hne
    change (if !cf.merges then some (kept es) else
      joinLoop cf i s g h (fun J => rebalance cf i s f g (h - 1) J)
        ((kept es).length + 1) (kept es)) = some es' at hr
    rw [hk] at hr
    split at hr
    · cases hr; exact hes
    · exact joinLoop_ne_nil _ hes hr

theorem joinAt_vfill {g h ix : Nat} {down : List (Nat × VN) → Option (List (Nat × VN))}
    {es es' : List (Nat × VN)} (hm2 : 2 ≤ cf.m)
    (hdown : ∀ J J', down J = some J' →
      (∀ e ∈ J, VFill cf i s g false (h - 1) e.2) → (∀ e ∈ J, e.2.isEmpty = false) →
      (∀ e ∈ J', VFill cf i s g false (h - 1) e.2) ∧ (∀ e ∈ J', e.2.isEmpty = false) ∧
        (J'.length < 2 ∨ findSmall cf J' = none) ∧ (J ≠ [] → J' ≠ []))
    (hv : ∀ e ∈ es, VFill cf i s g false h e.2)
    (hne : ∀ e ∈ es, e.2.isEmpty = false)
    (hj : joinAt cf i s g h down es ix = some es') :
    (∀ e ∈ es', VFill cf i s g false h e.2) ∧ (∀ e ∈ es', e.2.isEmpty = false) := by
  rw [joinAt_eq] at hj
  unfold joinAtIl at hj
  split at hj
  · rename_i l r hl hr
    have hvl := hv l (List.mem_of_getElem? hl)
    have hvr := hv r (List.mem_of_getElem? hr)
    have hnl := hne l (List.mem_of_getElem? hl)
    split at hj
    · rename_i L R hoL hoR
      cases h with
      | zero =>
        simp only [beq_self_eq_true, ↓reduceIte] at hj
        cases hm : mkNode cf i s none g 0 true (L ++ R) with
        | none => rw [hm] at hj; cases hj
        | some v =>
          rw [hm] at hj
          simp only [Option.some.injEq] at hj
          subst hj
          obtain ⟨L', hL, hpL, hnL⟩ := hvl.open_leaf
          obtain ⟨R', hR, hpR, _⟩ := hvr.open_leaf
          rw [hoL] at hL; cases hL
          rw [hoR] at hR; cases hR
          have hp : ∀ e ∈ L ++ R, ∃ y, e.2 = .old y := by
            intro e he
            exact (List.mem_append.mp he).elim (hpL e) (hpR e)
          have hv' := mkNode_vfill_leaf (isRoot := false) hp (by simp) hm
          have hLne : L ≠ [] := by
            have hc := hvl.cnt_pos hm2 hnl
            intro hz; rw [hz] at hnL; simp [entries] at hnL; omega
          have hform := mkNode_form hm
          obtain ⟨F, d, hform⟩ := hform
          have hvne : v.isEmpty = false := hv'.open_ne (by rw [hform]; rfl)
            (by simpa using (List.append_ne_nil_of_left_ne_nil hLne R))
          constructor <;> intro e he <;>
            simp only [List.mem_append, List.mem_singleton] at he
          · rcases he with (he | rfl) | he
            · exact hv e (List.mem_of_mem_take he)
            · exact hv'
            · exact hv e (List.mem_of_mem_drop he)
          · rcases he with (he | rfl) | he
            · exact hne e (List.mem_of_mem_take he)
            · exact hvne
            · exact hne e (List.mem_of_mem_drop he)
      | succ h =>
        simp only [Nat.add_one_ne_zero, beq_iff_eq, ↓reduceIte] at hj
        cases hd : down (L ++ renameHead r.1 R) with
        | none => rw [hd] at hj; cases hj
        | some J =>
          rw [hd] at hj
          simp only at hj
          cases hm : mkNode cf i s none g (h + 1) true J with
          | none => rw [hm] at hj; cases hj
          | some v =>
            rw [hm] at hj
            simp only [Option.some.injEq] at hj
            subst hj
            obtain ⟨L', hL, hcL, hnL, _, hlenL⟩ := hvl.open_inner
            obtain ⟨R', hR, hcR, hnR, _, _⟩ := hvr.open_inner
            rw [hoL] at hL; cases hL
            rw [hoR] at hR; cases hR
            have hc : ∀ e ∈ L ++ renameHead r.1 R, VFill cf i s g false h e.2 := by
              intro e he
              rcases List.mem_append.mp he with he | he
              · exact hcL e he
              · obtain ⟨e', he', h2⟩ := renameHead_mem he
                rw [← h2]; exact hcR e' he'
            have hn : ∀ e ∈ L ++ renameHead r.1 R, e.2.isEmpty = false := by
              intro e he
              rcases List.mem_append.mp he with he | he
              · exact hnL e he
              · obtain ⟨e', he', h2⟩ := renameHead_mem he
                rw [← h2]; exact hnR e' he'
            obtain ⟨hcJ, hnJ, heJ, hJne⟩ := hdown _ _ hd hc hn
            have hv' := mkNode_vfill_inner (isRoot := false) hcJ hnJ heJ (by simp) hm
            have hLne : L ≠ [] := by
              have hp := hvl.cnt_pos hm2 hnl
              intro hz; rw [hz] at hlenL; simp [entries] at hlenL; omega
            have hJ : J ≠ [] := hJne (List.append_ne_nil_of_left_ne_nil hLne _)
            obtain ⟨F, d, hform⟩ := mkNode_form hm
            have hvne : v.isEmpty = false := hv'.open_ne (by rw [hform]; rfl) (by
              simpa only [Nat.add_one_ne_zero, beq_iff_eq, ↓reduceIte] using renameHead_ne 0 hJ)
            constructor <;> intro e he <;>
              simp only [List.mem_append, List.mem_singleton] at he
            · rcases he with (he | rfl) | he
              · exact hv e (List.mem_of_mem_take he)
              · exact hv'
              · exact hv e (List.mem_of_mem_drop he)
            · rcases he with (he | rfl) | he
              · exact hne e (List.mem_of_mem_take he)
              · exact hvne
              · exact hne e (List.mem_of_mem_drop he)
    · cases hj
  · cases hj

theorem joinLoop_vfill {g h : Nat} {down : List (Nat × VN) → Option (List (Nat × VN))}
    (hjoin : ∀ es ix es', joinAt cf i s g h down es ix = some es' →
      (∀ e ∈ es, VFill cf i s g false h e.2) → (∀ e ∈ es, e.2.isEmpty = false) →
      (∀ e ∈ es', VFill cf i s g false h e.2) ∧ (∀ e ∈ es', e.2.isEmpty = false)) :
    ∀ (n : Nat) {es es' : List (Nat × VN)}, joinLoop cf i s g h down n es = some es' →
      (∀ e ∈ es, VFill cf i s g false h e.2) → (∀ e ∈ es, e.2.isEmpty = false) →
      (∀ e ∈ es', VFill cf i s g false h e.2) ∧ (∀ e ∈ es', e.2.isEmpty = false)
  | 0, es, es', hj, hv, hn => by simp only [joinLoop, Option.some.injEq] at hj; cases hj; exact ⟨hv, hn⟩
  | n + 1, es, es', hj, hv, hn => by
    rw [joinLoop] at hj
    split at hj
    · cases hj; exact ⟨hv, hn⟩
    · cases hs : findSmall cf es with
      | none => rw [hs] at hj; cases hj; exact ⟨hv, hn⟩
      | some ix =>
        rw [hs] at hj
        simp only at hj
        cases ht : joinAt cf i s g h down es ix with
        | none => rw [ht] at hj; cases hj
        | some es1 =>
          rw [ht] at hj
          obtain ⟨h1, h2⟩ := hjoin _ _ _ ht hv hn
          exact joinLoop_vfill hjoin n hj h1 h2

/-- Structural fill conditions survive the entire recursive rebalance,
at every height, including arbitrary higher inner joins. -/
theorem rebalance_vfill (hm2 : 2 ≤ cf.m) : ∀ (f g h : Nat) (es es' : List (Nat × VN)),
    rebalance cf i s f g h es = some es' → (∀ e ∈ es, VFill cf i s g false h e.2) →
    (∀ e ∈ es', VFill cf i s g false h e.2) ∧ (∀ e ∈ es', e.2.isEmpty = false) ∧
      (es'.length < 2 ∨ findSmall cf es' = none)
  | 0, _, _, _, _, hr, _ => by simp [rebalance] at hr
  | f + 1, g, h, es, es', hr, hv => by
    have hm : cf.merges = true := by simp [Cfg.merges, hm2]
    have hr' := hr
    change (if !cf.merges then some (kept es) else
      joinLoop cf i s g h (fun J => rebalance cf i s f g (h - 1) J)
        ((kept es).length + 1) (kept es)) = some es' at hr'
    simp only [hm, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hr'
    have hkv : ∀ e ∈ kept es, VFill cf i s g false h e.2 := fun e he => hv e (List.mem_of_mem_filter he)
    have hkn : ∀ e ∈ kept es, e.2.isEmpty = false := by
      intro e he; simpa using (List.mem_filter.mp he).2
    have hjoin : ∀ A ix B, joinAt cf i s g h (fun J => rebalance cf i s f g (h - 1) J) A ix = some B →
        (∀ e ∈ A, VFill cf i s g false h e.2) → (∀ e ∈ A, e.2.isEmpty = false) →
        (∀ e ∈ B, VFill cf i s g false h e.2) ∧ (∀ e ∈ B, e.2.isEmpty = false) := by
      intro A ix B hj hv hn
      apply joinAt_vfill hm2 ?_ hv hn hj
      intro J J' hd hc hn
      obtain ⟨a1, a2, a3⟩ := rebalance_vfill hm2 f g (h - 1) J J' hd hc
      exact ⟨a1, a2, a3, fun he => rebalance_ne_nil hn he hd⟩
    obtain ⟨hv', hn'⟩ := joinLoop_vfill hjoin _ hr' hkv hkn
    exact ⟨hv', hn', rebalance_exit hr hm⟩

end Contract.PE
