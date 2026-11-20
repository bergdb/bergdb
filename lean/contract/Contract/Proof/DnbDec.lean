/-
bergdb 030-29: PE's decision for a node against Java's count of the node.

* Dead klongs (`deadCount`, Dag.deadCount): appending klongs to a node makes
  at most one more dead klong for each key klong appended and, with a new
  bitmap of the last bitmap and the klongs of the compare values R, at most
  one for each compare value of R (`deadCount_emit`).
* Java's parameters (`Cfg.java`): PE's cut (`cutParts`) is Java's
  `cutPartsBound`, which grows with n.
* `dec_parts_ov`: if PE cuts or replaces a node (`decideNode` gives `parts
  k`), and Java counts for it at least as many klongs K as the entries PE
  adds and the compare values it removes, and the final list is no longer
  than the node's size and K, then Java's count has the node overflow and k is
  at most Java's parts.
-/
import Contract.Proof.DnbSpec
import Contract.Proof.Node

namespace Contract.PE

open DNB

/-! ## Dead klongs -/

/-- Klong k with index j is dead in L (`deadCount`'s test). -/
def isDead (L : List Klong) (k : Klong) (j : Nat) : Bool :=
  match k with
  | .key c _ => (lastBitmap L).contains j || (L.drop (j + 1)).any (fun k' => match k' with
      | .key c' _ => c' == c
      | _ => false)
  | _ => false

theorem deadCount_eq (L : List Klong) :
    deadCount L = (L.zipIdx.filter (fun p => isDead L p.1 p.2)).length := by
  unfold deadCount isDead
  congr 1

/-- The compare value of a key klong. -/
def kcv : Klong → Option Nat
  | .key c _ => some c
  | _ => none

theorem mem_zipIdx_get {α : Type} {L : List α} {k : α} {j : Nat} (h : (k, j) ∈ L.zipIdx) :
    j < L.length ∧ L[j]? = some k := by
  rw [List.mem_zipIdx_iff_getElem?] at h
  exact ⟨(List.getElem?_eq_some_iff.mp h).1, h⟩

/-- The key klongs of L that are not dead and whose compare value is in S
have distinct compare values, so there are at most |S| of them. -/
theorem live_in_le (L : List Klong) (S : List Nat) :
    (L.zipIdx.filter (fun p => !isDead L p.1 p.2 && (match kcv p.1 with
      | some c => S.contains c
      | none => false))).length ≤ S.length := by
  set P := L.zipIdx.filter (fun p => !isDead L p.1 p.2 && (match kcv p.1 with
      | some c => S.contains c
      | none => false)) with hP
  have hsorted : P.Pairwise (fun a b => a.2 < b.2) := (zipIdx_sorted L 0).filter _
  have hmem : ∀ p ∈ P, p ∈ L.zipIdx ∧ isDead L p.1 p.2 = false ∧
      ∃ c, kcv p.1 = some c ∧ c ∈ S := by
    intro p hp
    rw [hP, List.mem_filter] at hp
    obtain ⟨h1, h2⟩ := hp
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h2
    refine ⟨h1, h2.1, ?_⟩
    revert h2
    cases kcv p.1 with
    | none => simp
    | some c => intro h2; exact ⟨c, rfl, by simpa using h2.2⟩
  have hpw : P.Pairwise (fun a b => (kcv a.1).getD 0 ≠ (kcv b.1).getD 0) := by
    refine List.Pairwise.imp_of_mem ?_ hsorted
    intro a b ha hb hlt heq
    obtain ⟨ha1, ha2, c, hca, _⟩ := hmem a ha
    obtain ⟨hb1, _, c', hcb, _⟩ := hmem b hb
    rw [hca, hcb] at heq
    simp only [Option.getD_some] at heq
    subst heq
    obtain ⟨hbl, hbget⟩ := mem_zipIdx_get hb1
    have hin : b.1 ∈ L.drop (a.2 + 1) := by
      rw [List.mem_iff_getElem?]
      refine ⟨b.2 - (a.2 + 1), ?_⟩
      rw [List.getElem?_drop, show a.2 + 1 + (b.2 - (a.2 + 1)) = b.2 by omega]
      exact hbget
    revert ha2
    unfold isDead
    cases hk : a.1 with
    | key c0 y0 =>
      simp only [hk, kcv, Option.some.injEq] at hca
      subst hca
      intro ha2
      simp only [Bool.or_eq_false_iff] at ha2
      have := ha2.2
      rw [List.any_eq_false] at this
      have := this b.1 hin
      cases hk' : b.1 with
      | key c1 y1 =>
        rw [hk'] at hcb
        simp only [kcv, Option.some.injEq] at hcb
        subst hcb
        rw [hk'] at this
        simp at this
      | _ => rw [hk'] at hcb; simp [kcv] at hcb
    | _ => simp [hk, kcv] at hca
  have hnd : (P.map (fun p => (kcv p.1).getD 0)).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    exact hpw
  have hsub : P.map (fun p => (kcv p.1).getD 0) ⊆ S := by
    intro c hc
    rw [List.mem_map] at hc
    obtain ⟨p, hp, rfl⟩ := hc
    obtain ⟨_, _, c', hc', hcs⟩ := hmem p hp
    rw [hc']
    exact hcs
  have := (List.subperm_of_subset hnd hsub).length_le
  simpa using this

theorem len_filter_le_add {α : Type} (P Q R : α → Bool) :
    ∀ (l : List α), (∀ x ∈ l, P x = true → Q x = true ∨ R x = true) →
      (l.filter P).length ≤ (l.filter Q).length + (l.filter R).length
  | [], _ => by simp
  | a :: l, h => by
    have ih := len_filter_le_add P Q R l (fun x hx => h x (List.mem_cons_of_mem a hx))
    have ha := h a (List.mem_cons_self)
    simp only [List.filter_cons]
    cases hP : P a <;> cases hQ : Q a <;> cases hR : R a <;> simp_all <;> omega

theorem deadCount_snoc (L : List Klong) (k : Klong) :
    deadCount (L ++ [k]) = (L.zipIdx.filter (fun p => isDead (L ++ [k]) p.1 p.2)).length +
      (if isDead (L ++ [k]) k L.length then 1 else 0) := by
  rw [deadCount_eq, List.zipIdx_append, List.filter_append, List.length_append]
  congr 1
  simp only [List.zipIdx_singleton, zero_add]
  rw [List.filter_cons, List.filter_nil]
  split <;> simp_all

theorem drop_snoc_of_lt {α : Type} (L : List α) (k : α) {j : Nat} (hj : j < L.length) :
    (L ++ [k]).drop (j + 1) = L.drop (j + 1) ++ [k] := by
  rw [List.drop_append_of_le_length (by omega)]

/-- The old klongs after one more: dead before, or the compare value of the
new key klong, or in the new bitmap. -/
theorem isDead_snoc_old {L : List Klong} {k kj : Klong} {j : Nat} (hj : j < L.length) :
    isDead (L ++ [k]) kj j = (match kj with
      | .key c _ => (lastBitmap (L ++ [k])).contains j ||
          (L.drop (j + 1)).any (fun k' => match k' with
            | .key c' _ => c' == c
            | _ => false) ||
          (match k with
            | .key c' _ => c' == c
            | _ => false)
      | _ => false) := by
  unfold isDead
  cases kj with
  | key c y =>
    simp only
    rw [drop_snoc_of_lt L k hj, List.any_append]
    simp [Bool.or_assoc]
  | _ => rfl

theorem deadCount_snoc_time (L : List Klong) (t : Time) :
    deadCount (L ++ [.time t]) = deadCount L := by
  rw [deadCount_snoc, deadCount_eq]
  have hnew : isDead (L ++ [.time t]) (.time t) L.length = false := rfl
  rw [hnew]
  simp only [Bool.false_eq_true, ite_false, add_zero]
  congr 1
  apply List.filter_congr
  intro p hp
  have hj := (mem_zipIdx_get (k := p.1) (j := p.2) (by simpa using hp)).1
  rw [isDead_snoc_old hj, lastBitmap_snoc]
  unfold isDead
  cases p.1 <;> simp

theorem deadCount_snoc_key (L : List Klong) (c : Nat) (y : NodeId)
    (hbm : ∀ j ∈ lastBitmap L, j < L.length) :
    deadCount (L ++ [.key c y]) ≤ deadCount L + 1 := by
  rw [deadCount_snoc]
  have hnew : isDead (L ++ [.key c y]) (.key c y) L.length = false := by
    unfold isDead
    rw [lastBitmap_snoc]
    simp only [Bool.or_eq_false_iff, List.contains_eq_mem, decide_eq_false_iff_not]
    refine ⟨fun h => absurd (hbm _ h) (by omega), ?_⟩
    simp
  rw [hnew]
  simp only [Bool.false_eq_true, ite_false, add_zero]
  have h1 := len_filter_le_add (fun p : Klong × Nat => isDead (L ++ [.key c y]) p.1 p.2)
    (fun p => isDead L p.1 p.2) (fun p => !isDead L p.1 p.2 && (match kcv p.1 with
      | some c' => [c].contains c'
      | none => false)) L.zipIdx (by
      intro p hp hd
      have hj := (mem_zipIdx_get (k := p.1) (j := p.2) (by simpa using hp)).1
      rw [isDead_snoc_old hj, lastBitmap_snoc] at hd
      cases hq : isDead L p.1 p.2
      · right
        revert hd hq
        unfold isDead
        cases p.1 with
        | key c0 y0 =>
          simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
            Bool.not_true, kcv, List.contains_cons, List.contains_nil, Bool.or_false]
          intro hd hq
          rcases hd with (hd | hd) | hd
          · simp_all
          · simp_all
          · exact ⟨by simp_all, by simp [hd]⟩
        | _ => simp
      · left; rfl)
  have h2 := live_in_le L [c]
  rw [← deadCount_eq] at h1
  simp only [List.length_singleton] at h2
  omega

theorem deadCount_snoc_del (L : List Klong) (X S : List Nat)
    (hX : ∀ j ∈ X, ∀ k, L[j]? = some k → ∃ c, kcv k = some c ∧ c ∈ S) :
    deadCount (L ++ [.del (lastBitmap L ++ X)]) ≤ deadCount L + S.length := by
  rw [deadCount_snoc]
  have hnew : isDead (L ++ [.del (lastBitmap L ++ X)]) (.del (lastBitmap L ++ X)) L.length = false := rfl
  rw [hnew]
  simp only [Bool.false_eq_true, ite_false, add_zero]
  have h1 := len_filter_le_add (fun p : Klong × Nat => isDead (L ++ [.del (lastBitmap L ++ X)]) p.1 p.2)
    (fun p => isDead L p.1 p.2) (fun p => !isDead L p.1 p.2 && (match kcv p.1 with
      | some c' => S.contains c'
      | none => false)) L.zipIdx (by
      intro p hp hd
      have hmem := mem_zipIdx_get (k := p.1) (j := p.2) (by simpa using hp)
      rw [isDead_snoc_old hmem.1, lastBitmap_snoc] at hd
      cases hq : isDead L p.1 p.2
      · right
        revert hd hq
        unfold isDead
        cases hk : p.1 with
        | key c0 y0 =>
          intro hd hq
          simp only [Bool.or_eq_false_iff] at hq
          by_cases hx : p.2 ∈ X
          · obtain ⟨c1, hc1, hc1S⟩ := hX p.2 hx p.1 hmem.2
            rw [hk] at hc1
            simp only [kcv, Option.some.injEq] at hc1
            subst hc1
            simp [hc1S, kcv]
          · exfalso
            have hx' : X.contains p.2 = false := by simpa using hx
            simp only [List.contains_append, hq.1, hq.2, hx', Bool.or_false] at hd
            exact absurd hd (by simp)
        | _ => simp
      · left; rfl)
  have h2 := live_in_le L S
  rw [← deadCount_eq] at h1
  omega

theorem deadCount_keys : ∀ (keys L : List Klong), (∀ k ∈ keys, ∃ c y, k = Klong.key c y) →
    (∀ j ∈ lastBitmap L, j < L.length) → deadCount (L ++ keys) ≤ deadCount L + keys.length
  | [], L, _, _ => by simp
  | k :: rest, L, hk, hbm => by
    obtain ⟨c, y, rfl⟩ := hk k (List.mem_cons_self)
    have h1 := deadCount_snoc_key L c y hbm
    have hbm' : ∀ j ∈ lastBitmap (L ++ [Klong.key c y]), j < (L ++ [Klong.key c y]).length := by
      rw [lastBitmap_snoc]
      intro j hj
      have := hbm j hj
      simp; omega
    have h2 := deadCount_keys rest (L ++ [Klong.key c y]) (fun k hk' => hk k (List.mem_cons_of_mem _ hk'))
      hbm'
    rw [List.append_assoc] at h2
    simp only [List.singleton_append] at h2
    simp only [List.length_cons]
    omega

/-- The bitmaps of well-formed klongs name earlier klongs. -/
theorem bm_lt_of_wf {ks : List Klong} (h : klongsWf ks = true) :
    ∀ j ∈ lastBitmap ks, j < ks.length := by
  simp only [klongsWf, Bool.and_eq_true] at h
  have hb := (bmFold_spec ks ks).2 h.2
  have hw : BmW ks := by
    intro l1 b l2 he
    have := bitmapOk_iff (hb l1 b l2 he)
    exact ⟨this.1, this.2.1⟩
  exact BmW.lt_length hw

theorem mem_bitsIn {ks : List Klong} {R : List Nat} {j : Nat} (h : j ∈ bitsIn ks R) :
    ∃ c y, ks[j]? = some (.key c y) ∧ c ∈ R := by
  unfold bitsIn at h
  rw [List.mem_filterMap] at h
  obtain ⟨⟨k, j'⟩, hm, hk⟩ := h
  cases k with
  | key c y =>
    simp only at hk
    split at hk
    · rename_i hc
      simp only [Option.some.injEq] at hk
      subst hk
      exact ⟨c, y, (mem_zipIdx_get hm).2, by simpa using hc⟩
    · simp at hk
  | _ => simp at hk

/-- **Dead klongs after an append.** The klongs PE appends to a node of
well-formed klongs make at most one more dead klong for each compare value
removed and each entry added. -/
theorem deadCount_emit (i : Time) {ks : List Klong} (hwf : klongsWf ks = true)
    (F : List (Nat × Option NodeId)) :
    deadCount (ks ++ appendKsO i ks F) ≤
      deadCount ks + (removedCvs (live ks) F).length + (F.filter (isAdded (live ks))).length := by
  have hbm := bm_lt_of_wf hwf
  set R := removedCvs (live ks) F
  set keys : List Klong := (F.filter (isAdded (live ks))).map (fun e => Klong.key e.1 (e.2.getD 0))
  have hkeys : ∀ k ∈ keys, ∃ c y, k = Klong.key c y := by
    intro k hk
    simp only [keys, List.mem_map] at hk
    obtain ⟨e, _, rfl⟩ := hk
    exact ⟨_, _, rfl⟩
  have hklen : keys.length = (F.filter (isAdded (live ks))).length := by simp [keys]
  unfold appendKsO emitHead
  split
  · rename_i hR
    have h0 := deadCount_snoc_time ks i
    have hbm1 : ∀ j ∈ lastBitmap (ks ++ [Klong.time i]), j < (ks ++ [Klong.time i]).length := by
      rw [lastBitmap_snoc]; intro j hj; have := hbm j hj; simp; omega
    have h1 := deadCount_keys keys (ks ++ [Klong.time i]) hkeys hbm1
    rw [List.append_assoc, List.singleton_append] at h1
    show deadCount (ks ++ (Klong.time i :: keys)) ≤ _
    omega
  · rename_i hR
    have h0 := deadCount_snoc_time ks i
    have hlb1 : lastBitmap (ks ++ [Klong.time i]) = lastBitmap ks := by rw [lastBitmap_snoc]
    have h1 := deadCount_snoc_del (ks ++ [Klong.time i]) (bitsIn ks R) R (by
      intro j hj k hk
      obtain ⟨c, y, hget, hc⟩ := mem_bitsIn hj
      have hjl : j < ks.length := (List.getElem?_eq_some_iff.mp hget).1
      rw [List.getElem?_append_left hjl, hget] at hk
      simp only [Option.some.injEq] at hk
      subst hk
      exact ⟨c, rfl, hc⟩)
    rw [hlb1] at h1
    have hbm2 : ∀ j ∈ lastBitmap (ks ++ [Klong.time i] ++ [Klong.del (lastBitmap ks ++ bitsIn ks R)]),
        j < (ks ++ [Klong.time i] ++ [Klong.del (lastBitmap ks ++ bitsIn ks R)]).length := by
      rw [lastBitmap_snoc]
      intro j hj
      rw [List.mem_append] at hj
      simp only [List.length_append, List.length_singleton]
      rcases hj with hj | hj
      · have := hbm j hj; omega
      · obtain ⟨c, y, hget, _⟩ := mem_bitsIn hj
        have := (List.getElem?_eq_some_iff.mp hget).1; omega
    have h2 := deadCount_keys keys _ hkeys hbm2
    simp only [List.append_assoc, List.cons_append, List.nil_append] at h1 h2
    show deadCount (ks ++ (Klong.time i :: Klong.del (emitBits ks R) :: keys)) ≤ _
    unfold emitBits
    omega

/-! ## Java's parameters -/

theorem cutParts_java (b G H n : Nat) : cutParts (Cfg.java b G H) n = cutPartsBound b n := by
  unfold cutParts cutPartsBound nParts Cfg.java
  simp only
  rw [Nat.max_comm (cutSize b) 1]
  generalize hc : max 1 (cutSize b) = cap
  have hcap : 1 ≤ cap := by rw [← hc]; exact le_max_left _ _
  split
  · rfl
  · split
    · rename_i hnc
      have : (n + cap - 1) / cap < 2 := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
      omega
    · rfl

theorem cutPartsBound_mono (b : Nat) {n n' : Nat} (h : n ≤ n') : cutPartsBound b n ≤ cutPartsBound b n' := by
  unfold cutPartsBound
  simp only
  split <;> split
  · exact le_refl _
  · omega
  · omega
  · exact max_le_max (le_refl 2) (Nat.div_le_div_right (by omega))

/-- Java's room of a node of `size` klongs in `overflowsD`. -/
def roomOf (b size : Nat) (merged : Bool) : Nat :=
  if merged then min (b - 2 - size) (roomAfterReplacement b) else b - 2 - size

/-- Java's `least` in `overflowsD`. -/
def leastOf (b K : Nat) (dead : Option Nat) : Nat :=
  match dead with
  | some d => if 0 < theta b ∧ theta b < d + K then 1 else 0
  | none => 0

theorem overflowsD_eq {b K size : Nat} {merged : Bool} {dead : Option Nat} (hK : K ≠ 0) :
    overflowsD b K size merged dead =
      if K + 1 ≤ roomOf b size merged then leastOf b K dead
      else 1 + (K + 1 - roomOf b size merged - 1) / roomAfterReplacement b := by
  unfold overflowsD roomOf leastOf
  simp only [hK, ite_false]
  rfl

theorem roomOf_le (b size : Nat) (merged : Bool) : roomOf b size merged ≤ b - 2 - size := by
  unfold roomOf; split <;> omega

theorem ov_pos_of_size {b K size : Nat} {merged : Bool} {dead : Option Nat} (hK : 0 < K)
    (h : b ≤ size + K) : 0 < overflowsD b K size merged dead := by
  rw [overflowsD_eq (by omega)]
  have := roomOf_le b size merged
  split
  · omega
  · exact Nat.add_pos_left Nat.one_pos _

theorem ov_pos_of_dead {b K size d : Nat} {merged : Bool} (hK : 0 < K) (hth : 0 < theta b)
    (h : theta b < d + K) : 0 < overflowsD b K size merged (some d) := by
  rw [overflowsD_eq (by omega)]
  split
  · simp only [leastOf]
    split
    · exact Nat.one_pos
    · rename_i hn; exact absurd ⟨hth, h⟩ hn
  · exact Nat.add_pos_left Nat.one_pos _

theorem appendKsO_length (i : Time) (ks : List Klong) (F : List (Nat × Option NodeId)) :
    (appendKsO i ks F).length =
      (if (removedCvs (live ks) F).isEmpty then 1 else 2) + (F.filter (isAdded (live ks))).length := by
  unfold appendKsO emitHead
  split <;> simp <;> omega

/-- **PE replaces a node only where Java's count has it overflow.** If PE's
decision for a node of the tree before is `parts k`, and Java counts for it at
least as many klongs K as the compare values PE removes and the entries it
adds (and the list is the node's own when it removes and adds none), and the
final list holds at most the node's klongs and K, then Java's overflows are
positive, and k is at most Java's parts. -/
theorem dec_parts_ov {b G H : Nat} {i : Time} {n : KNode} {F : List (Nat × Option NodeId)}
    {K : Nat} {merged : Bool} {k : Nat} (hwf : klongsWf n.ks = true)
    (hA : (removedCvs (live n.ks) F).length + (F.filter (isAdded (live n.ks))).length ≤ K)
    (hsame : (removedCvs (live n.ks) F).length + (F.filter (isAdded (live n.ks))).length = 0 →
      (live n.ks).map (fun q => (q.1, some q.2)) = F)
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
    have hRA : 0 < R + A := by
      rcases Nat.eq_zero_or_pos (R + A) with h0 | h0
      · exact absurd (hsame h0) (by simpa using hne)
      · exact h0
    have hK : 0 < K := by omega
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
