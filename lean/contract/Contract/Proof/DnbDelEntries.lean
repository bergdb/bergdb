/-
bergdb 030-36: the parent list when empty children are removed. Renaming
its head changes the added count by at most one and the removed count by
at most one. At least one delete pays for these changes; without deletes
the head is already zero.
-/
import Contract.Proof.DnbDelDrop

namespace Contract.PE

open DNB PeProof

variable {cf : Cfg} {i : Time} {s : Tree}

theorem filter_length_union_le {α : Type} (p q r : α → Bool) : ∀ (l : List α),
    (∀ a ∈ l, p a = true → q a = true ∨ r a = true) →
    (l.filter p).length ≤ (l.filter q).length + (l.filter r).length
  | [], _ => by simp
  | a :: l, hh => by
    have ih := filter_length_union_le p q r l (fun x hx => hh x (List.mem_cons_of_mem _ hx))
    have ha := hh a List.mem_cons_self
    cases hp : p a <;> cases hq : q a <;> cases hr : r a <;> simp_all <;> omega

theorem filter_cv_length_le_one {α : Type} {l : List (Nat × α)} (hs : l.Pairwise CvLtA) (c : Nat) :
    (l.filter (fun e => e.1 == c)).length ≤ 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨ha, hl⟩ := List.pairwise_cons.mp hs
    by_cases hc : a.1 = c
    · have hf : l.filter (fun e => e.1 == c) = [] := by
        rw [List.filter_eq_nil_iff]
        intro e he
        have := ha e he
        simp only [beq_iff_eq]
        omega
      simp [hc, hf]
    · simpa [hc] using ih hl

theorem added_renameHead_le {lb : List (Nat × NodeId)} (c : Nat)
    (F : List (Nat × Option NodeId)) :
    ((renameHead c F).filter (isAdded lb)).length ≤ (F.filter (isAdded lb)).length + 1 := by
  cases F with
  | nil => simp [renameHead]
  | cons e F =>
    simp only [renameHead, List.filter_cons]
    split <;> split <;> simp_all
    all_goals omega

theorem added_renameHead_ge {lb : List (Nat × NodeId)} (c : Nat)
    (F : List (Nat × Option NodeId))
    (ho : ∀ e ∈ F, isAdded lb e = true → e.2 = none) :
    (F.filter (isAdded lb)).length ≤ ((renameHead c F).filter (isAdded lb)).length := by
  cases F with
  | nil => simp [renameHead]
  | cons e F =>
    by_cases ha : isAdded lb e = true
    · have he := ho e List.mem_cons_self ha
      have he' : isAdded lb (c, e.2) = true := by simp [isAdded, he]
      simp only [renameHead, List.filter_cons, ha, he', ↓reduceIte, List.length_cons]
      exact le_rfl
    · have ha0 : isAdded lb e = false := by simpa using ha
      simp only [renameHead, List.filter_cons, ha0, Bool.false_eq_true, ↓reduceIte]
      split <;> simp

theorem removed_renameHead_le {α : Type} {lb : List (Nat × NodeId)}
    (hs : lb.Pairwise CvLtA) (c : Nat) (F : List (Nat × α)) :
    (removedCvs lb (renameHead c F)).length ≤ (removedCvs lb F).length + 1 := by
  cases F with
  | nil => simp [renameHead]
  | cons e F =>
    have hh := filter_length_union_le
      (fun q : Nat × NodeId => !((renameHead c (e :: F)).any (fun e' => e'.1 == q.1)))
      (fun q => !((e :: F).any (fun e' => e'.1 == q.1)))
      (fun q => q.1 == e.1) lb (by
        intro q _ hq
        simp only [renameHead, List.any_cons, Bool.not_or, Bool.and_eq_true] at hq ⊢
        by_cases he : e.1 = q.1
        · exact Or.inr (by simp [he])
        · exact Or.inl ⟨by simp [he], hq.2⟩)
    have hh1 := filter_cv_length_le_one hs e.1
    simp only [removedCvs, List.length_map]
    omega

theorem entries_renameHead (c : Nat) (es : List (Nat × VN)) :
    entries (renameHead c es) = renameHead c (entries es) := by
  cases es with
  | nil => rfl
  | cons e es =>
    change ents c e.2 ++ entries es = renameHead c (ents e.1 e.2 ++ entries es)
    rw [renameHead_append _ (ents_ne e.1 e.2), ents_rename c e.2, ents_rename e.1 e.2,
      renameHead_renameHead]

theorem rebalance_filter_only {f g h : Nat} {es es2 : List (Nat × VN)}
    (hs : (kept es).length < 2 ∨ findSmall cf (kept es) = none)
    (hr : rebalance cf i s (f + 1) g h es = some es2) : es2 = kept es := by
  have hstop (down : List (Nat × VN) → Option (List (Nat × VN))) :
      joinLoop cf i s g h down ((kept es).length + 1) (kept es) = some (kept es) := by
    rw [joinLoop]
    rcases hs with hs | hs
    · simp [hs]
    · split
      · rfl
      · rw [hs]
  change (if !cf.merges then some (kept es) else
    joinLoop cf i s g h (fun J => rebalance cf i s f g (h - 1) J)
      ((kept es).length + 1) (kept es)) = some es2 at hr
  split at hr
  · exact (Option.some.inj hr).symm
  · rw [hstop] at hr
    exact (Option.some.inj hr).symm

/-- The decision lemma only needs the final list to be unchanged when its
entire klong allowance is zero. -/
theorem dec_parts_ov_of_zero {b G H : Nat} {i : Time} {n : KNode} {F : List (Nat × Option NodeId)}
    {K : Nat} {merged : Bool} {k : Nat} (hwf : klongsWf n.ks = true)
    (hA : (removedCvs (live n.ks) F).length + (F.filter (isAdded (live n.ks))).length ≤ K)
    (hsame : K = 0 → (live n.ks).map (fun q => (q.1, some q.2)) = F)
    (hF : F.length ≤ n.ks.length + K)
    (hdec : decideNode (Cfg.java b G H) i (some n) false F = .parts k) :
    0 < overflowsD b K n.ks.length merged (some (deadCount n.ks)) ∧
      k ≤ max (overflowsD b K n.ks.length merged (some (deadCount n.ks)) + 1)
        (cutPartsBound b (n.ks.length + K)) := by
  set R := (removedCvs (live n.ks) F).length
  set A := (F.filter (isAdded (live n.ks))).length
  unfold decideNode at hdec
  simp only at hdec
  split at hdec
  · cases hdec
  · rename_i hne
    have hK : 0 < K := by
      by_contra hh
      exact absurd (hsame (by omega)) (by simpa using hne)
    have hcut : cutParts (Cfg.java b G H) F.length ≤ cutPartsBound b (n.ks.length + K) := by
      rw [cutParts_java]; exact cutPartsBound_mono b hF
    have hlen := appendKsO_length i n.ks F
    have hRe : (if (removedCvs (live n.ks) F).isEmpty then 1 else 2) ≤ 1 + R := by
      split
      · omega
      · rename_i h
        have : 0 < R := by
          simp only [R]
          cases hr : removedCvs (live n.ks) F with
          | nil => rw [hr] at h; simp at h
          | cons _ _ => simp
        omega
    split at hdec
    · rename_i hfit
      split at hdec
      · rename_i hdo
        unfold deadOver at hdo
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hdo
        have hd := deadCount_emit i hwf F
        have hth : 0 < theta b := by
          have := hdo.1; simp only [Cfg.java] at this; omega
        have hpos : 0 < overflowsD b K n.ks.length merged (some (deadCount n.ks)) := by
          apply ov_pos_of_dead hK hth
          have := hdo.2; simp only [Cfg.java] at this; omega
        refine ⟨hpos, ?_⟩
        split at hdec
        · cases hdec; omega
        · cases hdec; exact le_max_of_le_right hcut
      · cases hdec
    · rename_i hfit
      cases hdec
      have hpos : 0 < overflowsD b K n.ks.length merged (some (deadCount n.ks)) := by
        apply ov_pos_of_size hK
        simp only [Cfg.java] at hfit
        omega
      exact ⟨hpos, le_max_of_le_right hcut⟩

end Contract.PE
