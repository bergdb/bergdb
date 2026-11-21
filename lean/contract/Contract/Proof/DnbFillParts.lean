/-
bergdb 030-37: minimum fill of every part emitted by a cut, at Java's
parameters. This is a local ingredient for fill preservation, independent
of the restriction on higher joins in the dirty-bound theorem.
-/
import Contract.Proof.DnbDelFacts
import Contract.Proof.DnbDelTree

namespace Contract.PE

open DNB PeProof

theorem java_fill_params {b G H : Nat} (hb : 8 ≤ b) :
    (Cfg.java b G H).m ≤ (Cfg.java b G H).cap ∧
      2 * (Cfg.java b G H).m ≤ (Cfg.java b G H).h + 1 ∧
      3 * (Cfg.java b G H).m ≤ 2 * (Cfg.java b G H).cap + 1 ∧
      2 * (Cfg.java b G H).m ≤ (Cfg.java b G H).c + 1 := by
  have h8 : ¬b < 8 := by omega
  simp only [Cfg.java, DNB.minFill, DNB.cutSize, DNB.splitAbove, DNB.mergeCap, h8, ite_false]
  omega

theorem nParts_mul_min {c m n : Nat} (hc : 1 ≤ c) (hm : m ≤ c)
    (hcm : 2 * m ≤ c + 1) (hn : m ≤ n) : nParts c n * m ≤ n := by
  rw [nParts_of_pos hc]
  split
  · simpa using hn
  · rename_i hbig
    let k := (n + c - 1) / c
    have hk : 2 ≤ k := by
      apply (Nat.le_div_iff_mul_le (by omega)).mpr
      omega
    have hlt : (k - 1) * c < n := by
      have hdiv := Nat.div_mul_le_self (n + c - 1) c
      change k * c ≤ _ at hdiv
      have he : k * c = (k - 1) * c + c := by
        calc k * c = (k - 1 + 1) * c := by congr 1; omega
             _ = (k - 1) * c + c := by ring
      omega
    have hprod := Nat.mul_le_mul_left (k - 2) hm
    have he1 : (k - 1) * c = (k - 2) * c + c := by
      calc (k - 1) * c = (k - 2 + 1) * c := by congr 1; omega
           _ = (k - 2) * c + c := by ring
    have he2 : k * m = (k - 2) * m + 2 * m := by
      calc k * m = (k - 2 + 2) * m := by congr 1; omega
           _ = (k - 2) * m + 2 * m := by ring
    change k * m ≤ n
    omega

theorem cutParts_mul_min {cf : Cfg} {m n : Nat}
    (hc : 1 ≤ cf.cap) (hm : m ≤ cf.cap) (hh : 2 * m ≤ cf.h + 1)
    (hcap : 3 * m ≤ 2 * cf.cap + 1) (hn : m ≤ n) : cutParts cf n * m ≤ n := by
  unfold cutParts
  split
  · simpa using hn
  · rename_i hbig
    rw [nParts_of_pos hc]
    split
    · simp only [Nat.max_eq_left (by omega : 1 ≤ 2)]
      omega
    · rename_i hnc
      let k := (n + cf.cap - 1) / cf.cap
      by_cases hk : k ≤ 2
      · rw [Nat.max_eq_left hk]
        omega
      · rw [Nat.max_eq_right (by omega : 2 ≤ k)]
        have hdiv := Nat.div_mul_le_self (n + cf.cap - 1) cf.cap
        change k * cf.cap ≤ _ at hdiv
        have he1 : k * cf.cap = (k - 1) * cf.cap + cf.cap := by
          calc k * cf.cap = (k - 1 + 1) * cf.cap := by congr 1; omega
               _ = (k - 1) * cf.cap + cf.cap := by ring
        have hlt : (k - 1) * cf.cap < n := by omega
        have hprod := Nat.mul_le_mul_left (k - 3) hm
        have he2 : (k - 1) * cf.cap = (k - 3) * cf.cap + 2 * cf.cap := by
          calc (k - 1) * cf.cap = (k - 3 + 2) * cf.cap := by congr 1; omega
               _ = (k - 3) * cf.cap + 2 * cf.cap := by ring
        have he3 : k * m = (k - 3) * m + 3 * m := by
          calc k * m = (k - 3 + 3) * m := by congr 1; omega
               _ = (k - 3) * m + 3 * m := by ring
        change k * m ≤ n
        omega

/-- The sizes requested by cutList are exact when they fit in the input. -/
theorem cutList_lengths {α : Type} : ∀ (l : List α) (sz : List Nat), sz.sum ≤ l.length →
    (cutList l sz).map List.length = sz
  | l, [], _ => rfl
  | l, n :: ns, hfit => by
    have hn : n ≤ l.length := by simp only [List.sum_cons] at hfit; omega
    simp only [cutList, List.map_cons, List.length_take, Nat.min_eq_left hn]
    rw [cutList_lengths (l.drop n) ns (by
      simp only [List.sum_cons] at hfit
      simp only [List.length_drop]
      omega)]

theorem cutList_min_length {α : Type} {l : List α} {sz : List Nat} {m : Nat}
    (hfit : sz.sum ≤ l.length) (hmin : ∀ n ∈ sz, m ≤ n) :
    ∀ Q ∈ cutList l sz, m ≤ Q.length := by
  intro Q hQ
  have hm := List.mem_map_of_mem (f := List.length) hQ
  rw [cutList_lengths l sz hfit] at hm
  exact hmin _ hm

/-- Every part of a full-sized virtual node meets the non-root fill rule,
for both an ordinary space cut and a joined node's cut by c. -/
theorem java_parts_minFill {b G H n : Nat} (hb : 8 ≤ b)
    (hn : (Cfg.java b G H).m ≤ n) (join : Bool) :
    ∀ p ∈ partSizes n (if join then nParts (Cfg.java b G H).c n
      else cutParts (Cfg.java b G H) n) join, (Cfg.java b G H).m ≤ p := by
  obtain ⟨hmcap, hmh, hmcap2, hmc⟩ := java_fill_params (G := G) (H := H) hb
  obtain ⟨_, hmc', _, _, _, hcap1, _⟩ := java_params (G := G) (H := H) hb
  have hc1 : 1 ≤ (Cfg.java b G H).c := by omega
  have hparts : (if join then nParts (Cfg.java b G H).c n else cutParts (Cfg.java b G H) n) *
      (Cfg.java b G H).m ≤ n := by
    cases join
    · exact cutParts_mul_min hcap1 hmcap hmh hmcap2 hn
    · exact nParts_mul_min hc1 hmc' hmc hn
  have hk : 0 < (if join then nParts (Cfg.java b G H).c n else cutParts (Cfg.java b G H) n) := by
    cases join
    · exact cutParts_one_le _ _
    · exact nParts_pos _ _
  intro p hp
  have hlow := (partSizes_bounds p hp).1
  have hdiv := (Nat.le_div_iff_mul_le hk).mpr (by
    simpa only [Nat.mul_comm] using hparts)
  omega

/-- The same minimum for every actual decision, including a dead-klong
replacement into one part. The direction of the balanced sizes is free. -/
theorem java_dec_parts_minFill {b G H : Nat} (hb : 8 ≤ b) {i : Time}
    {base : Option KNode} {join : Bool} {F : List (Nat × Option NodeId)} {k : Nat}
    (hn : (Cfg.java b G H).m ≤ F.length)
    (hd : decideNode (Cfg.java b G H) i base join F = .parts k) (ceilFirst : Bool) :
    ∀ p ∈ partSizes F.length k ceilFirst, (Cfg.java b G H).m ≤ p := by
  obtain ⟨hmcap, hmh, hmcap2, hmc⟩ := java_fill_params (G := G) (H := H) hb
  obtain ⟨_, hmc', _, _, _, hcap1, _⟩ := java_params (G := G) (H := H) hb
  have hc1 : 1 ≤ (Cfg.java b G H).c := by omega
  have hcut := cutParts_mul_min hcap1 hmcap hmh hmcap2 hn
  have hjoin := nParts_mul_min hc1 hmc' hmc hn
  have hmul : k * (Cfg.java b G H).m ≤ F.length := by
    cases base with
    | none =>
      cases join <;> simp only [decideNode, Bool.false_eq_true, ↓reduceIte, Dec.parts.injEq] at hd
      · subst k; exact hcut
      · subst k; exact hjoin
    | some n =>
      unfold decideNode at hd
      simp only at hd
      split at hd
      · cases hd
      · split at hd
        · split at hd
          · split at hd
            · cases hd; simpa using hn
            · cases hd; exact hcut
          · cases hd
        · cases hd; exact hcut
  have hk := (dec_parts (cfgOk_java8 hb) hd).1
  intro p hp
  have hl := (partSizes_bounds p hp).1
  have hdiv := (Nat.le_div_iff_mul_le (by omega : 0 < k)).mpr (by
    simpa only [Nat.mul_comm] using hmul)
  omega

end Contract.PE
