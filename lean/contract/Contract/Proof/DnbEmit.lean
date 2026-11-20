/-
bergdb 030-29: the key nodes PE's emit writes, and the new roots its settle
makes.

* `emit_kw`: emit writes exactly `vcost v` key nodes for a planned virtual
  node v (its decision's: none, one appended base, or k new nodes; and its
  children's).
* `settle_puts`: a root whose list is long enough not to collapse is
  settled into itself, or, if it is cut into k ≥ 2 parts, into a chain of new
  roots above it, `raPE k` key nodes more, which is at most Java's
  `rootsAbove` of any parts count from k on (`raPE_le`).
-/
import Contract.Proof.DnbDec
import Contract.Proof.PeAccept

namespace Contract.PE

open DNB PeProof

variable {cf : Cfg} {i : Time} {s : Tree}

/-! ## Key writes -/

theorem kw_write_key (acc : Acc) (x : NodeId) (n : KNode) :
    kw (acc.write x (.key n)) = kw acc + 1 := by
  simp [kw, Acc.write, keyWrites]

theorem kw_write_val (acc : Acc) (x : NodeId) (h : Nat) :
    kw (acc.write x (.val h)) = kw acc := by
  simp [kw, Acc.write, keyWrites]

theorem kw_fresh (acc : Acc) : kw acc.fresh.2 = kw acc := rfl

theorem newParts_kw (g h : Nat) : ∀ (Ps : List (List (Nat × NodeId))) (acc : Acc),
    kw (newParts cf i g h Ps acc).2 = kw acc + Ps.length
  | [], acc => by simp [newParts]
  | P :: Ps, acc => by
    simp only [newParts]
    rw [newParts_kw g h Ps, kw_write_key, kw_fresh]
    simp only [List.length_cons]
    omega

mutual

/-- **emit writes `vcost v` key nodes.** -/
theorem emit_kw : ∀ (v : VN) (acc : Acc) (E : List (Nat × NodeId)) (acc' : Acc),
    emit cf i s v acc = some (E, acc') → kw acc' = kw acc + vcost v
  | .old y, acc, E, acc', h => by
    rw [emit.eq_1] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    simp [vcost]
  | .node base g h join es F dec, acc, E, acc', hem => by
    rw [emit.eq_2] at hem
    simp only at hem
    split at hem
    · cases hem
    · rename_i F0 acc1 hk
      have h1 := emitKids_kw es acc F0 acc1 hk
      simp only [vcost]
      split at hem
      · simp only [Option.some.injEq, Prod.mk.injEq] at hem
        obtain ⟨_, rfl⟩ := hem
        simp [dcost, h1]
      · split at hem
        · simp only [Option.some.injEq, Prod.mk.injEq] at hem
          obtain ⟨_, rfl⟩ := hem
          rw [kw_write_key, h1]
          simp [dcost]; omega
        · cases hem
      · simp only [Option.some.injEq] at hem
        have h2 := congrArg Prod.snd hem
        simp only at h2
        rw [← h2, newParts_kw, h1, cutList_length, partSizes_length]
        simp [dcost]; omega
      · cases hem

/-- `emit_kw` of a list of entries. -/
theorem emitKids_kw : ∀ (es : List (Nat × VN)) (acc : Acc) (E : List (Nat × NodeId)) (acc' : Acc),
    emitKids cf i s es acc = some (E, acc') → kw acc' = kw acc + vcostL es
  | [], acc, E, acc', h => by
    rw [emitKids.eq_1] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    simp [vcostL]
  | (c, v) :: rest, acc, E, acc', h => by
    rw [emitKids.eq_2] at h
    split at h
    · cases h
    · rename_i E1 acc1 he1
      split at h
      · cases h
      · rename_i F2 acc2 he2
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl⟩ := h
        rw [emitKids_kw rest acc1 F2 acc2 he2, emit_kw v acc E1 acc1 he1]
        simp [vcostL]; omega

end

/-! ## Java's rootsAbove -/

/-- From node size 8, a cut of p ≥ 2 parts' entries gives fewer parts. -/
theorem cutPartsBound_lt {b p : Nat} (hb : 8 ≤ b) (hp : 2 ≤ p) : cutPartsBound b p ≤ p - 1 := by
  unfold cutPartsBound
  simp only
  have hh : 4 ≤ splitAbove b := by unfold splitAbove; omega
  have hc : 4 ≤ cutSize b := by unfold cutSize; omega
  split
  · omega
  · rename_i hn
    have hcap : max 1 (cutSize b) = cutSize b := by omega
    rw [hcap]
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 5 := ⟨p - 5, by omega⟩
    obtain ⟨c, hc'⟩ : ∃ c, cutSize b = c + 4 := ⟨cutSize b - 4, by omega⟩
    rw [hc']
    have : (q + 5 + (c + 4) - 1) / (c + 4) ≤ q + 4 := by
      apply Nat.div_le_of_le_mul
      rw [show q + 5 + (c + 4) - 1 = q + c + 8 by omega]
      nlinarith
    omega

theorem rootsAboveLoop_stable (b : Nat) (hb : 8 ≤ b) :
    ∀ (f f' p : Nat), p ≤ f → p ≤ f' → rootsAboveLoop b f p = rootsAboveLoop b f' p
  | 0, f', p, hf, _ => by
    obtain rfl : p = 0 := by omega
    cases f' <;> simp [rootsAboveLoop]
  | f + 1, 0, p, _, hf' => by
    obtain rfl : p = 0 := by omega
    simp [rootsAboveLoop]
  | f + 1, f' + 1, p, hf, hf' => by
    simp only [rootsAboveLoop]
    split
    · rfl
    · rename_i hp
      have hlt := cutPartsBound_lt hb (p := p) (by omega)
      congr 1
      exact rootsAboveLoop_stable b hb f f' _ (by omega) (by omega)

theorem rootsAbove_step {b k : Nat} (hb : 8 ≤ b) (hk : 2 ≤ k) :
    rootsAbove b k = cutPartsBound b k + rootsAbove b (cutPartsBound b k) := by
  have hlt := cutPartsBound_lt hb hk
  unfold rootsAbove
  obtain ⟨f, rfl⟩ : ∃ f, k = f + 1 := ⟨k - 1, by omega⟩
  simp only [rootsAboveLoop]
  rw [ite_eq_right (by omega), show min (f + 1 - 1) (cutPartsBound b (f + 1)) = cutPartsBound b (f + 1) by omega]
  congr 1
  exact rootsAboveLoop_stable b hb f _ _ (by omega) le_rfl

theorem rootsAboveLoop_mono (b : Nat) (hb : 8 ≤ b) :
    ∀ (f f' p q : Nat), p ≤ q → p ≤ f → q ≤ f' → rootsAboveLoop b f p ≤ rootsAboveLoop b f' q
  | 0, _, _, _, _, _, _ => by simp [rootsAboveLoop]
  | f + 1, f', p, q, hpq, hf, hf' => by
    simp only [rootsAboveLoop]
    split
    · exact Nat.zero_le _
    · rename_i hp
      obtain ⟨f'', rfl⟩ : ∃ f'', f' = f'' + 1 := ⟨f' - 1, by omega⟩
      simp only [rootsAboveLoop]
      rw [ite_eq_right (by omega)]
      have h1 := cutPartsBound_lt hb (p := p) (by omega)
      have h2 := cutPartsBound_lt hb (p := q) (by omega)
      have hm := cutPartsBound_mono b hpq
      rw [show min (p - 1) (cutPartsBound b p) = cutPartsBound b p by omega,
        show min (q - 1) (cutPartsBound b q) = cutPartsBound b q by omega]
      have := rootsAboveLoop_mono b hb f f'' _ _ hm (by omega) (by omega)
      omega

theorem rootsAbove_mono {b p q : Nat} (hb : 8 ≤ b) (h : p ≤ q) : rootsAbove b p ≤ rootsAbove b q :=
  rootsAboveLoop_mono b hb p q p q h le_rfl le_rfl

/-! ## Settle -/

/-- What settle adds above a root decided `dec`: Java's new roots for a cut
into k ≥ 2 parts. -/
def raOf (b : Nat) : Dec → Nat
  | .parts k => if 2 ≤ k then rootsAbove b k else 0
  | _ => 0

/-- **Settle of a root that does not collapse.** A planned root whose final
list is not empty and, for an inner node, not of one entry, is settled into
itself, or into new roots above its parts: at most `raOf b dec` key nodes
more, the new roots, and itself unless it was cut into two parts or more. -/
theorem settle_chain {b G H : Nat} (hb : 8 ≤ b) {g : Nat} {space : Bool} :
    ∀ (f : Nat) (base : Option NodeId) (h : Nat) (j : Bool) (es : List (Nat × VN))
      (F : List (Nat × Option NodeId)) (dec : Dec) (r : Option VN),
    F ≠ [] → (h ≠ 0 → F.length ≠ 1) →
    settleRoot (Cfg.java b G H) i s f g (.node base g h j es F dec) space = some r →
    ∃ v', r = some v' ∧ vcost v' ≤ vcost (.node base g h j es F dec) + raOf b dec ∧
      ((∀ k, 2 ≤ k → dec ≠ .parts k) → v' = .node base g h j es F dec)
  | 0, _, _, _, _, _, _, _, _, _, hs => by simp [settleRoot] at hs
  | f + 1, base, h, j, es, F, dec, r, hF, hF1, hs => by
    rw [settleRoot.eq_def] at hs
    simp only at hs
    have hFe : F.isEmpty = false := by cases F <;> simp_all
    rw [hFe] at hs
    simp only [Bool.false_eq_true, ↓reduceIte] at hs
    have hc : (h != 0 && F.length == 1) = false := by
      by_cases h0 : h = 0
      · simp [h0]
      · simp [h0, hF1 h0]
    rw [ite_eq_right (by simp [hc])] at hs
    cases dec with
    | parts k =>
      simp only at hs
      split at hs
      · rename_i hk
        split at hs
        · rename_i r0 hr
          unfold mkNode at hr
          simp only [beq_iff_eq, Nat.add_one_ne_zero, ↓reduceIte] at hr
          split at hr
          · cases hr
          · simp only [Option.some.injEq] at hr
            subst hr
            have hlen : (renameHead 0 (List.flatMap (fun e => ents e.1 e.2)
                (renameHead 0 [(0, VN.node base g h j es F (.parts k))]))).length = k := by
              have h1 : renameHead 0 [(0, VN.node base g h j es F (.parts k))] =
                  [(0, VN.node base g h j es F (.parts k))] := rfl
              rw [h1, renameHead_length]
              simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
              exact ents_parts_length hk
            have hdec : decideNode (Cfg.java b G H) i none false (renameHead 0 (List.flatMap
                (fun e => ents e.1 e.2) (renameHead 0 [(0, VN.node base g h j es F (.parts k))]))) =
                .parts (cutPartsBound b k) := by
              simp only [decideNode, Bool.false_eq_true, ↓reduceIte, hlen, cutParts_java]
            rw [hdec] at hs
            have hne : renameHead 0 (List.flatMap (fun e => ents e.1 e.2)
                (renameHead 0 [(0, VN.node base g h j es F (.parts k))])) ≠ [] := by
              intro he; rw [he] at hlen; simp at hlen; omega
            obtain ⟨v', hr, ih1, _⟩ := settle_chain hb f none (h + 1) false _ _ _ r hne
              (fun _ => by rw [hlen]; omega) hs
            refine ⟨v', hr, ?_, fun hn => absurd rfl (hn k hk)⟩
            have hstep := rootsAbove_step hb hk
            simp only [vcost, vcostL, dcost, raOf, hk, ↓reduceIte, renameHead] at ih1 ⊢
            have hlt := cutPartsBound_lt hb hk
            split at ih1
            · omega
            · omega
        · cases hs
      · simp only [Option.some.injEq] at hs
        subst hs
        exact ⟨_, rfl, by simp, fun _ => rfl⟩
    | same =>
      simp only [Option.some.injEq] at hs
      subst hs
      exact ⟨_, rfl, by simp [raOf], fun _ => rfl⟩
    | append =>
      simp only [Option.some.injEq] at hs
      subst hs
      exact ⟨_, rfl, by simp [raOf], fun _ => rfl⟩

theorem vcostL_old : ∀ (es : List (Nat × NodeId)), vcostL (es.map (fun e => (e.1, VN.old e.2))) = 0
  | [] => rfl
  | e :: es => by simp [vcostL, vcost, vcostL_old es]

theorem raOf_le (b k : Nat) : raOf b (.parts k) ≤ rootsAbove b k := by
  simp only [raOf]; split <;> omega

end Contract.PE
