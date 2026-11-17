/-
The contract package (bergdb 030-16): the merge, `Dag.merge` (bergdb 024-11,
M1 to M5; the model's `SIS.Tree.merge`). Node x at depth d of the key access
path, not the root, is merged with a sibling under its parent p: the left one
if it exists and the two fit one node or there is no right one, else the right
one. Their live klongs make one new node m1, or two, m1 and m2 (`mergeKlongs`);
the parent's klongs are set (`mergeParent`, WriterMergeParent.lean); the two
nodes merged are left out: one of before is cut back (`unlink`), one the
transaction made is taken back, its klongs of the transaction in p pointed to
m1 first (`retarget`). The tree rules: `Sound.mergeOne`, `Sound.mergeTwo`
(TreeRulesMerge.lean).

A node taken back is no node of the map. The link book `WcrLink`
(WriterCollapse.lean: a node reached that the transaction made is named by one
node at most) and `SNamed s` (the klongs of before name nodes of before) say
that only p names it, by klongs of the transaction, which `retarget` points to
m1. The merge keeps the keys, `PInv` and the link book.

Status (prover C, 17 November): `merge_spec` itself is not proved (left out). As stated last,
it had two premises more than first, `WmgSplitLink` (the link book through a full parent's splits) and `WmgFresh`
(no klong names an id not yet given out; without it the statement is false, see its doc), and
`WmgFresh` after. Proved: `mergeIdx` against the live klongs (`wmg_idx_inv`), the choice of the
sibling and the reads (`wmg_pick_spec`, `merge_spec_of_rest`: the merge from `WmgRestOk`),
and the end, the loop over the two nodes merged (`wmg_loop`: cut back, retarget, take-back,
with `WcrLinkX` and `WmgFresh`). Also proved, for what is open: the parent's live klongs split
at the two (`wmg_split2`), the two named once and not by the target (`wmg_kid_once`,
`wmg_target_not`), the shapes of `mergeKlongs` (`wmg_mk_one`, `wmg_mk_two`), and in the room
case the parent's klongs naming a node merged after its last time klong (`wmg_after_n3`).
Open: `WmgRestOk`, the merge's klongs, new nodes and the parent (`mergeParent` with
`Sound.mergeOne`, `Sound.mergeTwo`), up to the loop's invariant `WmgLoop`; with it,
`merge_spec_of_rest` is the merge.
-/
import Contract.Proof.WriterMergeParent
import Contract.Proof.TreeRulesMerge
import Contract.Proof.WriterCollapse

namespace Contract

open SIS (View)
open SIS.Check (BVal)
open SIS.Tree (Ctx)

/-! ## 1. `mergeIdx` -/

/-- The step of `mergeIdx`'s loop. -/
def wmg_idxStep (D : List Nat) (cx : Nat) (acc : Option Nat × Option (Nat × Nat) × Option
    (Nat × Nat))
    (ki : MKlong × Nat) : Option Nat × Option (Nat × Nat) × Option (Nat × Nat) :=
  match ki.1 with
  | .key cv _ =>
    if D.contains ki.2 then acc
    else if cv == cx then (some ki.2, acc.2.1, acc.2.2)
    else if cx < cv then
      (acc.1, (match acc.2.1 with
        | none => some (ki.2, cv)
        | some (_, cva) => if cv ≤ cva then some (ki.2, cv) else acc.2.1), acc.2.2)
    else
      (acc.1, acc.2.1, (match acc.2.2 with
        | none => some (ki.2, cv)
        | some (_, cvb) => if cvb ≤ cv then some (ki.2, cv) else acc.2.2))
  | _ => acc

theorem wmg_mergeIdx_eq (n : MNode) (cx : Nat) :
    SIS.Tree.mergeIdx n cx =
      n.ks.zipIdx.foldl (wmg_idxStep n.lastBitmap cx) (none, none, none) := by
  unfold SIS.Tree.mergeIdx
  congr 1

/-- What `mergeIdx`'s loop has found after the klongs l: the last klong of cx
not deleted; the last klong of the smallest compare value above cx not deleted;
of the largest below. -/
structure WmgIdx (D : List Nat) (cx : Nat) (l : List MKlong)
    (acc : Option Nat × Option (Nat × Nat) × Option (Nat × Nat)) : Prop where
  ix : ∀ ix, acc.1 = some ix → (∃ y, l[ix]? = some (.key cx y)) ∧ ix ∉ D ∧
    ∀ j y', ix < j → l[j]? = some (.key cx y') → j ∈ D
  ia : ∀ ia ca, acc.2.1 = some (ia, ca) → cx < ca ∧ (∃ y, l[ia]? = some (.key ca y)) ∧
    ia ∉ D ∧ (∀ j c y', l[j]? = some (.key c y') → j ∉ D → cx < c → ca ≤ c) ∧
    ∀ j y', ia < j → l[j]? = some (.key ca y') → j ∈ D
  ia0 : acc.2.1 = none → ∀ j c y', l[j]? = some (.key c y') → j ∉ D → ¬ cx < c
  ib : ∀ ib cb, acc.2.2 = some (ib, cb) → cb < cx ∧ (∃ y, l[ib]? = some (.key cb y)) ∧
    ib ∉ D ∧ (∀ j c y', l[j]? = some (.key c y') → j ∉ D → c < cx → c ≤ cb) ∧
    ∀ j y', ib < j → l[j]? = some (.key cb y') → j ∈ D
  ib0 : acc.2.2 = none → ∀ j c y', l[j]? = some (.key c y') → j ∉ D → ¬ c < cx

/-- A klong appended that is no key klong not deleted keeps what the loop found. -/
theorem wmg_idx_keep {D : List Nat} {cx : Nat} {l : List MKlong} {k : MKlong}
    {acc : Option Nat × Option (Nat × Nat) × Option (Nat × Nat)} (h : WmgIdx D cx l acc)
    (hk : ∀ c y, k = .key c y → l.length ∈ D) : WmgIdx D cx (l ++ [k]) acc := by
  have hcase : ∀ j (kk : MKlong), (l ++ [k])[j]? = some kk →
      (j < l.length ∧ l[j]? = some kk) ∨ (j = l.length ∧ kk = k) := by
    intro j kk hj
    rcases Nat.lt_or_ge j l.length with h1 | h1
    · left; rw [List.getElem?_append_left h1] at hj; exact ⟨h1, hj⟩
    · right
      rw [List.getElem?_append_right h1] at hj
      have h2 : j - l.length = 0 := by
        by_contra hne
        rw [List.getElem?_eq_none (by simp; omega)] at hj
        cases hj
      rw [h2] at hj
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      exact ⟨by omega, hj.symm⟩
  have hlt : ∀ j y, l[j]? = some y → j < l.length := fun j y h =>
    (List.getElem?_eq_some_iff.mp h).1
  have hold : ∀ j c y', (l ++ [k])[j]? = some (.key c y') → j ∉ D → l[j]? = some (.key c y') := by
    intro j c y' hj hD
    rcases hcase j _ hj with ⟨-, h1⟩ | ⟨rfl, h1⟩
    · exact h1
    · exact absurd (hk c y' h1.symm) hD
  refine ⟨fun ix hix => ?_, fun ia ca hia => ?_, fun h0 j c y' hj hD => h.ia0 h0 j c y'
    (hold j c y' hj hD) hD, fun ib cb hib => ?_, fun h0 j c y' hj hD => h.ib0 h0 j c y'
    (hold j c y' hj hD) hD⟩
  · obtain ⟨⟨y, hy⟩, h2, h3⟩ := h.ix ix hix
    refine ⟨⟨y, by rw [List.getElem?_append_left (hlt _ _ hy)]; exact hy⟩, h2,
      fun j y' hj hj' => ?_⟩
    rcases hcase j _ hj' with ⟨-, h1⟩ | ⟨rfl, h1⟩
    · exact h3 j y' hj h1
    · exact hk _ _ h1.symm
  · obtain ⟨h1, ⟨y, hy⟩, h2, h3, h4⟩ := h.ia ia ca hia
    refine ⟨h1, ⟨y, by rw [List.getElem?_append_left (hlt _ _ hy)]; exact hy⟩, h2,
      fun j c y' hj hD => h3 j c y' (hold j c y' hj hD) hD, fun j y' hj hj' => ?_⟩
    rcases hcase j _ hj' with ⟨-, h5⟩ | ⟨rfl, h5⟩
    · exact h4 j y' hj h5
    · exact hk _ _ h5.symm
  · obtain ⟨h1, ⟨y, hy⟩, h2, h3, h4⟩ := h.ib ib cb hib
    refine ⟨h1, ⟨y, by rw [List.getElem?_append_left (hlt _ _ hy)]; exact hy⟩, h2,
      fun j c y' hj hD => h3 j c y' (hold j c y' hj hD) hD, fun j y' hj hj' => ?_⟩
    rcases hcase j _ hj' with ⟨-, h5⟩ | ⟨rfl, h5⟩
    · exact h4 j y' hj h5
    · exact hk _ _ h5.symm

theorem wmg_idx_add {D : List Nat} {cx : Nat} {l : List MKlong} {cv : Nat} {yv : NodeId}
    {acc : Option Nat × Option (Nat × Nat) × Option (Nat × Nat)} (h : WmgIdx D cx l acc)
    (hD : l.length ∉ D) :
    WmgIdx D cx (l ++ [.key cv yv]) (wmg_idxStep D cx acc (.key cv yv, l.length)) := by
  have hcase : ∀ j (kk : MKlong), (l ++ [.key cv yv])[j]? = some kk →
      (j < l.length ∧ l[j]? = some kk) ∨ (j = l.length ∧ kk = .key cv yv) := by
    intro j kk hj
    rcases Nat.lt_or_ge j l.length with h1 | h1
    · left; rw [List.getElem?_append_left h1] at hj; exact ⟨h1, hj⟩
    · right
      rw [List.getElem?_append_right h1] at hj
      have h2 : j - l.length = 0 := by
        by_contra hne
        rw [List.getElem?_eq_none (by simp; omega)] at hj
        cases hj
      rw [h2] at hj
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      exact ⟨by omega, hj.symm⟩
  have hlt : ∀ j y, l[j]? = some y → j < l.length := fun j y h =>
    (List.getElem?_eq_some_iff.mp h).1
  have hnew : (l ++ [.key cv yv])[l.length]? = some (.key cv yv) := by simp
  have hold : ∀ j y, l[j]? = some y → (l ++ [.key cv yv])[j]? = some y := fun j y hj => by
    rw [List.getElem?_append_left (hlt _ _ hj)]; exact hj
  have hDc : D.contains l.length = false := by simpa using hD
  unfold wmg_idxStep
  simp only [hDc, Bool.false_eq_true, ↓reduceIte]
  by_cases hc : cv = cx
  · subst hc
    simp only [beq_self_eq_true, ↓reduceIte]
    refine ⟨fun ix hix => ?_, fun ia ca hia => ?_, fun h0 j c y' hj hD' => ?_,
      fun ib cb hib => ?_, fun h0 j c y' hj hD' => ?_⟩
    · cases hix
      refine ⟨⟨yv, hnew⟩, hD, fun j y' hj hj' => ?_⟩
      rcases hcase j _ hj' with ⟨h1, -⟩ | ⟨rfl, -⟩ <;> omega
    · obtain ⟨h1, ⟨y, hy⟩, h2, h3, h4⟩ := h.ia ia ca hia
      refine ⟨h1, ⟨y, hold _ _ hy⟩, h2, fun j c y' hj hD' hc' => ?_, fun j y' hj hj' => ?_⟩
      · rcases hcase j _ hj with ⟨-, h5⟩ | ⟨rfl, h5⟩
        · exact h3 j c y' h5 hD' hc'
        · cases h5; omega
      · rcases hcase j _ hj' with ⟨-, h5⟩ | ⟨rfl, h5⟩
        · exact h4 j y' hj h5
        · cases h5; omega
    · rcases hcase j _ hj with ⟨-, h5⟩ | ⟨rfl, h5⟩
      · exact h.ia0 h0 j c y' h5 hD'
      · cases h5; omega
    · obtain ⟨h1, ⟨y, hy⟩, h2, h3, h4⟩ := h.ib ib cb hib
      refine ⟨h1, ⟨y, hold _ _ hy⟩, h2, fun j c y' hj hD' hc' => ?_, fun j y' hj hj' => ?_⟩
      · rcases hcase j _ hj with ⟨-, h5⟩ | ⟨rfl, h5⟩
        · exact h3 j c y' h5 hD' hc'
        · cases h5; omega
      · rcases hcase j _ hj' with ⟨-, h5⟩ | ⟨rfl, h5⟩
        · exact h4 j y' hj h5
        · cases h5; omega
    · rcases hcase j _ hj with ⟨-, h5⟩ | ⟨rfl, h5⟩
      · exact h.ib0 h0 j c y' h5 hD'
      · cases h5; omega
  · have hc' : (cv == cx) = false := by simpa using hc
    simp only [hc', Bool.false_eq_true, ↓reduceIte]
    -- the klong of ix is kept
    have hix : ∀ ix, acc.1 = some ix → (∃ y, (l ++ [.key cv yv])[ix]? = some (.key cx y)) ∧
        ix ∉ D ∧ ∀ j y', ix < j → (l ++ [.key cv yv])[j]? = some (.key cx y') → j ∈ D := by
      intro ix h1
      obtain ⟨⟨y, hy⟩, h2, h3⟩ := h.ix ix h1
      refine ⟨⟨y, hold _ _ hy⟩, h2, fun j y' hj hj' => ?_⟩
      rcases hcase j _ hj' with ⟨-, h5⟩ | ⟨rfl, h5⟩
      · exact h3 j y' hj h5
      · cases h5; exact absurd rfl hc
    by_cases hlt' : cx < cv
    · simp only [hlt', ↓reduceIte]
      refine ⟨hix, fun ia ca hia => ?_, fun h0 j c y' hj hD' => ?_, fun ib cb hib => ?_,
        fun h0 j c y' hj hD' => ?_⟩
      · cases ho : acc.2.1 with
        | none =>
          rw [ho] at hia
          cases hia
          refine ⟨hlt', ⟨yv, hnew⟩, hD, fun j c y' hj hD' hc'' => ?_, fun j y' hj hj' => ?_⟩
          · rcases hcase j _ hj with ⟨-, h5⟩ | ⟨rfl, h5⟩
            · exact absurd hc'' (h.ia0 ho j c y' h5 hD')
            · cases h5; omega
          · rcases hcase j _ hj' with ⟨h1, -⟩ | ⟨rfl, -⟩ <;> omega
        | some old =>
          obtain ⟨io, co⟩ := old
          rw [ho] at hia
          obtain ⟨h1, ⟨y, hy⟩, h2, h3, h4⟩ := h.ia io co ho
          by_cases hle : cv ≤ co
          · simp only [hle, ↓reduceIte] at hia
            cases hia
            refine ⟨hlt', ⟨yv, hnew⟩, hD, fun j c y' hj hD' hc'' => ?_, fun j y' hj hj' => ?_⟩
            · rcases hcase j _ hj with ⟨-, h5⟩ | ⟨rfl, h5⟩
              · have := h3 j c y' h5 hD' hc''
                omega
              · cases h5; omega
            · rcases hcase j _ hj' with ⟨h6, -⟩ | ⟨rfl, -⟩ <;> omega
          · simp only [hle, ↓reduceIte] at hia
            cases hia
            refine ⟨h1, ⟨y, hold _ _ hy⟩, h2, fun j c y' hj hD' hc'' => ?_,
              fun j y' hj hj' => ?_⟩
            · rcases hcase j _ hj with ⟨-, h5⟩ | ⟨rfl, h5⟩
              · exact h3 j c y' h5 hD' hc''
              · cases h5; omega
            · rcases hcase j _ hj' with ⟨-, h5⟩ | ⟨rfl, h5⟩
              · exact h4 j y' hj h5
              · cases h5; omega
      · exfalso
        cases ho : acc.2.1 with
        | none => rw [ho] at h0; cases h0
        | some old =>
          obtain ⟨io, co⟩ := old
          rw [ho] at h0
          by_cases hle : cv ≤ co <;> simp [hle] at h0
      · obtain ⟨h1, ⟨y, hy⟩, h2, h3, h4⟩ := h.ib ib cb hib
        refine ⟨h1, ⟨y, hold _ _ hy⟩, h2, fun j c y' hj hD' hc'' => ?_, fun j y' hj hj' => ?_⟩
        · rcases hcase j _ hj with ⟨-, h5⟩ | ⟨rfl, h5⟩
          · exact h3 j c y' h5 hD' hc''
          · cases h5; omega
        · rcases hcase j _ hj' with ⟨-, h5⟩ | ⟨rfl, h5⟩
          · exact h4 j y' hj h5
          · cases h5; omega
      · rcases hcase j _ hj with ⟨-, h5⟩ | ⟨rfl, h5⟩
        · exact h.ib0 h0 j c y' h5 hD'
        · cases h5; omega
    · simp only [hlt', ↓reduceIte]
      have hgt : cv < cx := by omega
      refine ⟨hix, fun ia ca hia => ?_, fun h0 j c y' hj hD' => ?_, fun ib cb hib => ?_,
        fun h0 j c y' hj hD' => ?_⟩
      · obtain ⟨h1, ⟨y, hy⟩, h2, h3, h4⟩ := h.ia ia ca hia
        refine ⟨h1, ⟨y, hold _ _ hy⟩, h2, fun j c y' hj hD' hc'' => ?_, fun j y' hj hj' => ?_⟩
        · rcases hcase j _ hj with ⟨-, h5⟩ | ⟨rfl, h5⟩
          · exact h3 j c y' h5 hD' hc''
          · cases h5; omega
        · rcases hcase j _ hj' with ⟨-, h5⟩ | ⟨rfl, h5⟩
          · exact h4 j y' hj h5
          · cases h5; omega
      · rcases hcase j _ hj with ⟨-, h5⟩ | ⟨rfl, h5⟩
        · exact h.ia0 h0 j c y' h5 hD'
        · cases h5; omega
      · cases ho : acc.2.2 with
        | none =>
          rw [ho] at hib
          cases hib
          refine ⟨hgt, ⟨yv, hnew⟩, hD, fun j c y' hj hD' hc'' => ?_, fun j y' hj hj' => ?_⟩
          · rcases hcase j _ hj with ⟨-, h5⟩ | ⟨rfl, h5⟩
            · exact absurd hc'' (h.ib0 ho j c y' h5 hD')
            · cases h5; omega
          · rcases hcase j _ hj' with ⟨h1, -⟩ | ⟨rfl, -⟩ <;> omega
        | some old =>
          obtain ⟨io, co⟩ := old
          rw [ho] at hib
          obtain ⟨h1, ⟨y, hy⟩, h2, h3, h4⟩ := h.ib io co ho
          by_cases hle : co ≤ cv
          · simp only [hle, ↓reduceIte] at hib
            cases hib
            refine ⟨hgt, ⟨yv, hnew⟩, hD, fun j c y' hj hD' hc'' => ?_, fun j y' hj hj' => ?_⟩
            · rcases hcase j _ hj with ⟨-, h5⟩ | ⟨rfl, h5⟩
              · have := h3 j c y' h5 hD' hc''
                omega
              · cases h5; omega
            · rcases hcase j _ hj' with ⟨h6, -⟩ | ⟨rfl, -⟩ <;> omega
          · simp only [hle, ↓reduceIte] at hib
            cases hib
            refine ⟨h1, ⟨y, hold _ _ hy⟩, h2, fun j c y' hj hD' hc'' => ?_,
              fun j y' hj hj' => ?_⟩
            · rcases hcase j _ hj with ⟨-, h5⟩ | ⟨rfl, h5⟩
              · exact h3 j c y' h5 hD' hc''
              · cases h5; omega
            · rcases hcase j _ hj' with ⟨-, h5⟩ | ⟨rfl, h5⟩
              · exact h4 j y' hj h5
              · cases h5; omega
      · exfalso
        cases ho : acc.2.2 with
        | none => rw [ho] at h0; cases h0
        | some old =>
          obtain ⟨io, co⟩ := old
          rw [ho] at h0
          by_cases hle : co ≤ cv <;> simp [hle] at h0

theorem wmg_idx_inv (D : List Nat) (cx : Nat) (l : List MKlong) :
    WmgIdx D cx l (l.zipIdx.foldl (wmg_idxStep D cx) (none, none, none)) := by
  induction l using List.reverseRecOn with
  | nil =>
    refine ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ j _ _ h => (by simp at h),
      fun _ _ h => (by cases h), fun _ j _ _ h => (by simp at h)⟩
  | append_singleton l k ih =>
    rw [foldl_zipIdx_snoc]
    cases k with
    | time t => exact wmg_idx_keep ih (fun c y h => by cases h)
    | del b => exact wmg_idx_keep ih (fun c y h => by cases h)
    | key cv yv =>
      by_cases hD : l.length ∈ D
      · have e : wmg_idxStep D cx (l.zipIdx.foldl (wmg_idxStep D cx) (none, none, none))
            (.key cv yv, l.length) = l.zipIdx.foldl (wmg_idxStep D cx) (none, none, none) := by
          simp [wmg_idxStep, hD]
        rw [e]
        exact wmg_idx_keep ih (fun c y h => hD)
      · exact wmg_idx_add ih hD

/-- The model's klong j as the contract's. -/
theorem wmg_ks_model {n : MNode} {j c : Nat} {y : NodeId} :
    (ksOf n)[j]? = some (Klong.key c y) ↔ n.ks[j]? = some (.key c y) := by
  rw [ksOf_getElem?]
  constructor
  · intro h
    obtain ⟨k, hk, hkk⟩ := Option.map_eq_some_iff.mp h
    cases k with
    | key c' y' =>
      simp only [kOf, Klong.key.injEq] at hkk
      rw [hk, hkk.1, hkk.2]
    | time _ => simp [kOf] at hkk
    | del _ => simp [kOf] at hkk
  · intro h
    rw [h]
    rfl

/-- The last klong of c not deleted is its live klong, in a well formed node. -/
theorem wmg_liveAt_of {n : MNode} (hwf : klongsWf (ksOf n) = true) {j c : Nat} {y : NodeId}
    (hj : n.ks[j]? = some (.key c y)) (hD : j ∉ n.lastBitmap)
    (hlast : ∀ j' y', j < j' → n.ks[j']? = some (.key c y') → j' ∈ n.lastBitmap) :
    LiveAt n j c y := by
  have hD' : j ∉ lastBitmap (ksOf n) := by rw [lastBitmap_ksOf]; exact hD
  refine ⟨wmg_ks_model.mpr hj, hD', fun j' hj' hc => ?_⟩
  unfold cvAt at hc
  split at hc
  · rename_i c' y' hk
    simp only [Option.some.injEq] at hc
    subst hc
    have h1 := hlast j' y' hj' (wmg_ks_model.mp hk)
    have h1' : j' ∈ lastBitmap (ksOf n) := by rw [lastBitmap_ksOf]; exact h1
    obtain ⟨-, -, h3⟩ := lastBitmap_facts hwf j' h1'
    refine hD' (h3 j hj' ?_)
    unfold cvAt
    rw [wmg_ks_model.mpr hj, hk]
  · simp at hc

theorem wmg_liveWith_mem (del : List Nat) : ∀ (l : List (Klong × Nat)) (m : List (Nat × NodeId))
    (a : Nat × NodeId),
    a ∈ l.foldl (fun m (ki : Klong × Nat) => match ki with
      | (k, i) => match k with
        | .key c y => if del.contains i then m else insertCv c y m
        | _ => m) m →
    a ∈ m ∨ ∃ i, (Klong.key a.1 a.2, i) ∈ l ∧ i ∉ del
  | [], m, a, h => Or.inl h
  | (k, i) :: r, m, a, h => by
    simp only [List.foldl_cons] at h
    rcases wmg_liveWith_mem del r _ a h with h1 | ⟨i', h1, h2⟩
    · cases k with
      | time t => exact Or.inl h1
      | del b => exact Or.inl h1
      | key c y =>
        simp only at h1
        split at h1
        · exact Or.inl h1
        · rename_i hd
          rcases mem_insertCv h1 with h2 | h2
          · right
            refine ⟨i, ?_, by simpa using hd⟩
            rw [h2]
            exact List.mem_cons_self
          · exact Or.inl h2
    · exact Or.inr ⟨i', List.mem_cons_of_mem _ h1, h2⟩

/-- A live klong has a klong of the node that the last bitmap does not delete. -/
theorem wmg_live_idx {n : MNode} {c : Nat} {y : NodeId} (h : (c, y) ∈ live (ksOf n)) :
    ∃ j, n.ks[j]? = some (.key c y) ∧ j ∉ n.lastBitmap := by
  unfold live liveWith at h
  rcases wmg_liveWith_mem (lastBitmap (ksOf n)) (ksOf n).zipIdx [] (c, y) h with h1 | ⟨j, h1, h2⟩
  · simp at h1
  · refine ⟨j, wmg_ks_model.mp ?_, by rw [lastBitmap_ksOf] at h2; exact h2⟩
    exact (List.mem_zipIdx_iff_getElem?.mp h1)

/-- The merge's end: the parent's klongs set, then the two nodes merged left out. -/
def wmg_tail (p : NodeId) (d il cL : Nat) (m1 : NodeId) (ir cR : Nat)
    (m2 : Option (NodeId × Nat)) (l r : NodeId) (lMade rMade two : Bool) : SIS.Tree.M Nat := do
  SIS.Tree.mergeParent p (d - 1) il cL m1 ir cR m2
  for (o, made) in [(l, lMade), (r, rMade)] do
    if made then
      SIS.Tree.retarget p o m1
      SIS.Tree.takenBack o
      SIS.Tree.note "merge.takeback"
    else SIS.Tree.unlink o
  pure (if two then 2 else 1)

/-- The merge's new nodes. -/
def wmg_new (c : Ctx) (p : NodeId) (d : Nat) (l : NodeId) (ln : MNode) (il : Nat) (r : NodeId)
    (rn : MNode) (ir cL cR : Nat) (inner : Bool) (first : List (Nat × NodeId))
    (second : Option (List (Nat × NodeId) × Nat)) (g h : Nat) : SIS.Tree.M Nat := do
  let tt := c.i
  let lMade := ln.firstTime == some tt
  let rMade := rn.firstTime == some tt
  if lMade then SIS.Tree.note "merge.made.left"
  if rMade then SIS.Tree.note "merge.made.right"
  let m1 ← SIS.Tree.newKey g h (!inner) (SIS.Tree.newKlongs tt first)
  SIS.Tree.setMadeFor m1 (← if lMade then SIS.Tree.replacedBy l else pure (some l))
  let m2 ← match second with
    | some (ks2, g2) => do
      let y ← SIS.Tree.newKey g h (!inner) (SIS.Tree.newKlongs tt ks2)
      SIS.Tree.setMadeFor y (← if rMade then SIS.Tree.replacedBy r else pure (some r))
      pure (some (y, g2))
    | none => pure none
  wmg_tail p d il cL m1 ir cR m2 l r lMade rMade second.isSome

/-- The merge after the two nodes are chosen: l (klong il of p) and r (klong ir). -/
def wmg_rest (c : Ctx) (p x : NodeId) (pn xn : MNode) (d : Nat) (isLeft : Bool) (l : NodeId)
    (ln : MNode) (il : Nat) (r : NodeId) (rn : MNode) (ir : Nat) : SIS.Tree.M Nat := do
  let tt := c.i
  let inner := !xn.leaf
  SIS.Tree.note (if isLeft then "merge.left" else "merge.right")
  let cL ← match pn.cv? il with
    | some v => pure v
    | none => throw s!"Bug: merge at {tt}: no klong {il} in {p}"
  let cR ← match pn.cv? ir with
    | some v => pure v
    | none => throw s!"Bug: merge at {tt}: no klong {ir} in {p}"
  let lvL := ln.live
  let lvR := rn.live
  if lvL.isEmpty || lvR.isEmpty then
    throw s!"Bug: merge at {tt}: key node {l} or {r} has no live klong"
  if inner && ((lvL.head?.map (·.1)) != some 0 || (lvR.head?.map (·.1)) != some 0) then
    throw s!"Bug: merge at {tt}: inner node {l} or {r} has no live klong of the empty key first"
  let (first, second) := SIS.Tree.mergeKlongs inner c.p.mergeMax cR lvL lvR
  modify (fun w => { w with merges := w.merges + 1 })
  SIS.Tree.note (if second.isSome then "merge.two" else "merge.one")
  SIS.Tree.note (if inner then "merge.inner" else "merge.leaf")
  let (g, h) ← SIS.Tree.ghOf x
  wmg_new c p d l ln il r rn ir cL cR inner first second g h

/-- The choice of the sibling. -/
def wmg_pick (c : Ctx) (p x : NodeId) (pn xn : MNode) (d : Nat) (cx : Nat) : SIS.Tree.M Nat := do
  let tt := c.i
  let inner := !xn.leaf
  let (ix?, ia, ib) := SIS.Tree.mergeIdx pn cx
  let ix ← match ix? with
    | some ix => pure ix
    | none => throw s!"Bug: merge at {tt}: key node {x} has no live klong {cx} in {p}"
  if pn.ptr? ix != some x then
    throw s!"Bug: merge at {tt}: key node {x} is not the live child of its klong in {p}"
  let left ← match ib with
    | some (ib, _) => do
      let (ls, lsn) ← SIS.Tree.sibling p pn ib inner
      if ia.isNone || lsn.cnt + xn.cnt ≤ c.p.mergeMax then pure (some (ib, ls, lsn))
      else pure none
    | none => pure none
  let (l, ln, il, r, rn, ir) ← match left with
    | some (ib, ls, lsn) => pure (ls, lsn, ib, x, xn, ix)
    | none =>
      match ia with
      | some (ia, _) => do
        let (rs, rsn) ← SIS.Tree.sibling p pn ia inner
        pure (x, xn, ix, rs, rsn, ia)
      | none => throw s!"Bug: merge at {tt}: key node {x} has no sibling in {p}"
  wmg_rest c p x pn xn d left.isSome l ln il r rn ir

theorem wmg_eq (x : NodeId) (d : Nat) :
    SIS.Tree.merge x d = (do
      let c ← read
      let p ← SIS.Tree.pathNode (d - 1)
      let pn ← SIS.Tree.getNode p
      let xn ← SIS.Tree.getNode x
      let cx ← SIS.Tree.klongAt d
      wmg_pick c p x pn xn d cx) := by
  rfl


/-! ## 3. The link book with some namers left out, and the open piece -/

/-- `WcrLink` with the nodes of X not counted as namers. -/
def WcrLinkX (X : List NodeId) (i : Time) (s : Tree) (w : MW) : Prop :=
  ∀ m ∈ reachOf i s w, ∀ mn, (treeOf i s w).obj m = some (.key mn) → s.obj m = none →
    ∀ u nu c, (treeOf i s w).obj u = some (.key nu) → Klong.key c m ∈ nu.ks → u ≠ m → u ∉ X →
      m ≠ w.top.rootKey ∧ ∀ u' nu' c', (treeOf i s w).obj u' = some (.key nu') →
        Klong.key c' m ∈ nu'.ks → u' ≠ m → u' ∉ X → u' = u

/-- Every key klong of every key node of the map names an id below the next id. A premise of
the merge (bergdb 030-16, prover C): without it `merge_spec` is false. Nothing else bounds the
pointee of a klong of a node not reached: a segment leaf of the overlay, not reached, with a
dead klong of the transaction that names the id `w.next` meets the frame, BalancedOK (which
asks nothing of a leaf's klongs), `WcrLink` and `SNamed`; the merge's `newKey` makes m1 that
id, a node reached that the transaction made, named by q and by that leaf: `WcrLink` fails. -/
def WmgFresh (i : Time) (s : Tree) (w : MW) : Prop :=
  ∀ u nu c y, (treeOf i s w).obj u = some (.key nu) → Klong.key c y ∈ nu.ks → y < w.next

/-- The open piece (bergdb 030-16): the link book through the splits. A merge's parent
that is full is replaced by its last version with the pointers set (`handleFull`, a time
or a space split, and the parent's parent gets klongs in turn, up the path). The link
book holds after it, not counting namers X off the path, if it held so for the state with
x set to its last version; so do the fresh ids (`WmgFresh`); x stays a node of the overlay
of its kind; the nodes off the path are left as they are; and a node made before the
step, off the path and no live klong of a node of the path in that state, is named after
it only by nodes other than x that named it before. -/
def WmgSplitLink (p : MParams) (i : Time) (base : NodeId) (s : Tree) (tp : Top)
    (v : View BVal) : Prop :=
  ParamsOK p → Books i base s tp → SNamed s →
  ∀ (w : MW) (depth : Nat) (x : NodeId) (n V : MNode) (C : List (Key × Nat)) (compact : Bool)
    (X : List NodeId),
    CasPreD p i base s tp w depth x n V V C →
    (compact = true → (live (ksOf V)).length + 1 ≤ p.M) →
    (∀ y ∈ X, ∀ e c, e ≤ depth → w.path[e]? ≠ some (c, y)) →
    WcrLinkX X i s (w.withNode x V) → WmgFresh i s (w.withNode x V) →
    WP (SIS.Tree.handleFull depth x V compact) { p := p, i := i, view := v } w
      (fun _ w' => w'.outside = [] →
        PInv p i base s tp none C w' ∧ CascadePost i s w (w.withNode x V) w' depth ∧
        WcrLinkX X i s w' ∧ WmgFresh i s w' ∧
        (∃ n', w'.nodes.lookup x = some n' ∧ w'.taken.contains x = false ∧ n'.leaf = n.leaf) ∧
        (∀ y, y < w.next → (∀ e c, e ≤ depth → w.path[e]? ≠ some (c, y)) →
          (treeOf i s w').obj y = (treeOf i s w).obj y) ∧
        ∀ y, s.obj y = none → y < w.next → (∀ e c, e ≤ depth → w.path[e]? ≠ some (c, y)) →
          (∀ e c0 a na, e ≤ depth → w.path[e]? = some (c0, a) →
            (treeOf i s (w.withNode x V)).obj a = some (.key na) → ∀ c', (c', y) ∉ live na.ks) →
          ∀ u nu c, (treeOf i s w').obj u = some (.key nu) → Klong.key c y ∈ nu.ks →
            u ≠ x ∧ ∃ nu0, (treeOf i s w).obj u = some (.key nu0) ∧ Klong.key c y ∈ nu0.ks)

/-! ## 4. Reads -/

theorem wmg_ptr {n : MNode} {j c : Nat} {y : NodeId} (h : n.ks[j]? = some (.key c y)) :
    n.ptr? j = some y := by
  simp [SIS.Tree.KNode.ptr?, h]

theorem wmg_cv {n : MNode} {j c : Nat} {y : NodeId} (h : n.ks[j]? = some (.key c y)) :
    n.cv? j = some c := by
  simp [SIS.Tree.KNode.cv?, h]

/-- `sibling`: the node that klong j of q names, read; a node of the other kind than
`inner` says. (The klong is live: BalancedOK speaks of live klongs.) -/
theorem wmg_sibling {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {z : NodeId} (hs : Shows p v z s tp) (hb : Books i base s tp)
    {u : MW} {C : List (Key × Nat)} (hI : PInv p i base s tp none C u) (ho : OldReach i s u)
    {q : NodeId}
    {pn : MNode} (hlq : u.nodes.lookup q = some pn) (htq : u.taken.contains q = false)
    (hq : q ∈ reachOf i s u) (hql : pn.leaf = false) {j c : Nat} {y : NodeId}
    (hj : pn.ks[j]? = some (.key c y)) (hlv : (c, y) ∈ live (ksOf pn)) (inner : Bool) :
    WP (SIS.Tree.sibling q pn j inner) { p := p, i := i, view := v } u
      (fun r u' => r.1 = y ∧ u'.nodes.lookup y = some r.2 ∧ r.2.leaf = !inner ∧
        treeOf i s u' = treeOf i s u ∧ PInv p i base s tp none C u' ∧ u'.path = u.path ∧
        u'.top = u.top ∧ u'.taken = u.taken ∧ u'.next = u.next ∧
        (∀ z n, u.nodes.lookup z = some n → u'.nodes.lookup z = some n) ∧
        (∀ d, PathOk i s u d → PathOk i s u' d)) := by
  have hAq := treeOf_obj_overlay i s hlq htq
  have hqr : q ∈ reach (treeOf i s u) := by rw [reach_of_root hI.root]; exact hq
  obtain ⟨m, hm, -⟩ := (hI.balanced q hqr _ hAq).2.2 hql c y hlv
  have hyr : y ∈ reach (treeOf i s u) := by
    rw [reach_of_root hI.root]
    exact ts_reach_kid hI.sound.good hq hAq hlv
  unfold SIS.Tree.sibling
  refine wput_read ?_
  rw [wmg_ptr hj]
  obtain ⟨n, w', hget, -, hleaf, hlk, hT, hI', hw', hP⟩ := getNode_spec hs hb hI hm hyr ho
  refine wput_ok hget ?_
  refine wp_ite _ _ _ _ _ _ (fun _ => wp_throw _ _ _ _) (fun hne => ?_)
  rw [wp_pure]
  have hfields : w'.path = u.path ∧ w'.top = u.top ∧ w'.taken = u.taken ∧ w'.next = u.next ∧
      ∀ z n, u.nodes.lookup z = some n → w'.nodes.lookup z = some n := by
    rcases hw' with rfl | ⟨-, gh, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl, fun _ _ h => h⟩
    · exact ⟨rfl, rfl, rfl, rfl, fun _ _ h => prim_lookup_append_some _ h⟩
  refine ⟨rfl, hlk, ?_, hT, hI', hfields.1, hfields.2.1, hfields.2.2.1, hfields.2.2.2.1,
    hfields.2.2.2.2, hP⟩
  cases inner <;> cases hn : n.leaf <;> simp_all


/-! ## 5. Node algebra and steps of the end -/

theorem wmg_mem_kc {c : Nat} {l : List Klong} {j : Nat} {y : NodeId}
    (h : (j, y) ∈ kc c l.zipIdx) : l[j]? = some (Klong.key c y) := by
  simp only [kc, List.mem_filterMap] at h
  obtain ⟨⟨k, i⟩, hm, hk⟩ := h
  have hi := List.mem_zipIdx_iff_getElem?.mp hm
  simp only at hi hk
  cases k with
  | key c' y' =>
    by_cases hc : c' = c
    · simp only [hc, ite_true, Option.some.injEq, Prod.mk.injEq] at hk
      rw [← hk.1, hi, hc, hk.2]
    · simp [hc] at hk
  | time t => simp at hk
  | del b => simp at hk

theorem wmg_kc_of {c : Nat} {l : List Klong} {j : Nat} {y : NodeId}
    (h : l[j]? = some (Klong.key c y)) : (j, y) ∈ kc c l.zipIdx := by
  simp only [kc, List.mem_filterMap]
  exact ⟨(Klong.key c y, j), List.mem_zipIdx_iff_getElem?.mpr h, by simp⟩

/-- A live klong is the live klong (`LiveAt`) of its compare value, in a well formed node. -/
theorem wmg_live_liveAt {n : MNode} (hwf : klongsWf (ksOf n) = true) {c : Nat} {y : NodeId}
    (h : (c, y) ∈ live (ksOf n)) : ∃ j, LiveAt n j c y := by
  have hs := live_sorted (ksOf n)
  have hlk : (live (ksOf n)).lookup c = some y := (lookup_iff_mem hs c y).mpr h
  unfold live liveWith at hlk
  have hlk2 := (lookup_liveWith (lastBitmap (ksOf n)) c
      (ksOf n).zipIdx [] List.Pairwise.nil).symm.trans
    hlk
  have hsort := (kc_sorted c (ksOf n)).filter (fun a => !(lastBitmap (ksOf n)).contains a.1)
  cases hg : ((kc c (ksOf n).zipIdx).filter
      (fun a => !(lastBitmap (ksOf n)).contains a.1)).getLast? with
  | none => rw [hg] at hlk2; simp at hlk2
  | some a =>
    rw [hg] at hlk2
    obtain ⟨j, y'⟩ := a
    simp only [Option.some.injEq] at hlk2
    subst hlk2
    obtain ⟨l', hl'⟩ := List.getLast?_eq_some_iff.mp hg
    have hm : (j, y') ∈ (kc c (ksOf n).zipIdx).filter
        (fun a => !(lastBitmap (ksOf n)).contains a.1) := by rw [hl']; simp
    rw [List.mem_filter] at hm
    have hj := wmg_mem_kc hm.1
    have hjD : j ∉ lastBitmap (ksOf n) := by simpa using hm.2
    refine ⟨j, hj, hjD, fun j' hj' hc => ?_⟩
    unfold cvAt at hc
    split at hc
    · rename_i c'' y'' hk
      simp only [Option.some.injEq] at hc
      subst hc
      by_cases hD : j' ∈ lastBitmap (ksOf n)
      · obtain ⟨-, -, h3⟩ := lastBitmap_facts hwf j' hD
        refine hjD (h3 j hj' ?_)
        unfold cvAt
        rw [hj, hk]
      · have hm' : (j', y'') ∈ (kc c'' (ksOf n).zipIdx).filter
            (fun a => !(lastBitmap (ksOf n)).contains a.1) :=
          List.mem_filter.mpr ⟨wmg_kc_of hk, by simpa using hD⟩
        rw [hl'] at hm' hsort
        rcases List.mem_append.mp hm' with h1 | h1
        · have := (List.pairwise_append.mp hsort).2.2 _ h1 _ (List.mem_singleton_self _)
          simp only at this
          omega
        · simp at h1
          omega
    · simp at hc

/-! ## Klongs with pointees changed -/

/-- A klong with its pointee forgotten. -/
def wmgShape (k : Klong) : Klong :=
  match k with
  | .key c _ => .key c 0
  | k => k

theorem wmg_shape_cvAt {ks ks' : List Klong} (h : ks.map wmgShape = ks'.map wmgShape) :
    cvAt ks = cvAt ks' := by
  funext j
  have h1 : (ks.map wmgShape)[j]? = (ks'.map wmgShape)[j]? := by rw [h]
  rw [List.getElem?_map, List.getElem?_map] at h1
  unfold cvAt
  cases e1 : ks[j]? with
  | none =>
    rw [e1] at h1
    cases e2 : ks'[j]? with
    | none => rfl
    | some k' => rw [e2] at h1; cases h1
  | some k =>
    rw [e1] at h1
    cases e2 : ks'[j]? with
    | none => rw [e2] at h1; cases h1
    | some k' =>
      rw [e2] at h1
      simp only [Option.map_some, Option.some.injEq] at h1
      cases k <;> cases k' <;> simp_all [wmgShape]

theorem wmg_shape_lastBitmap {ks ks' : List Klong} (h : ks.map wmgShape = ks'.map wmgShape) :
    lastBitmap ks = lastBitmap ks' := by
  have e : ∀ l : List Klong, lastBitmap l = lastBitmap (l.map wmgShape) := by
    intro l
    unfold lastBitmap
    rw [List.foldl_map]
    congr 1
    funext d k
    cases k <;> rfl
  rw [e ks, e ks', h]

theorem wmg_shape_timesOk {ks ks' : List Klong} (h : ks.map wmgShape = ks'.map wmgShape) :
    timesOk ks = timesOk ks' := by
  have e : ∀ l : List Klong, timesOk l = timesOk (l.map wmgShape) := by
    intro l
    rw [timesOk_eq, timesOk_eq, List.foldl_map]
    congr 1
    · cases l with
      | nil => rfl
      | cons k l => cases k <;> rfl
    · congr 2
      funext acc k
      cases k <;> rfl
  rw [e ks, e ks', h]

theorem wmg_shape_wf {ks ks' : List Klong} (h : ks.map wmgShape = ks'.map wmgShape) :
    klongsWf ks = klongsWf ks' := by
  have hcv := wmg_shape_cvAt h
  have hbo : bitmapOk ks = bitmapOk ks' := by
    funext i before bits
    unfold bitmapOk
    rw [hcv]
  have hbs : bmStep ks = bmStep ks' := by
    funext acc k i
    unfold bmStep
    rw [hbo]
  have e : ∀ l : List Klong, (l.zipIdx.foldl (fun acc ki => bmStep ks' acc ki.1 ki.2) (true, [])) =
      ((l.map wmgShape).zipIdx.foldl (fun acc ki => bmStep ks' acc ki.1 ki.2) (true, [])) := by
    intro l
    rw [List.zipIdx_map, List.foldl_map]
    congr 1
    funext acc ki
    obtain ⟨k, i⟩ := ki
    cases k <;> rfl
  unfold klongsWf bitmapsOk
  rw [wmg_shape_timesOk h, hbs, e ks, e ks', h]

/-- A klong of the model pointed from src to dst. -/
def wmgSwap (src dst : NodeId) (k : MKlong) : MKlong :=
  match k with
  | .key c y => if y = src then .key c dst else k
  | k => k

/-- A klong pointed from src to dst. -/
def wmgSwapK (src dst : NodeId) (k : Klong) : Klong :=
  match k with
  | .key c y => if y = src then .key c dst else k
  | k => k

theorem wmg_ksOf_swap (n : MNode) (src dst : NodeId) :
    ksOf { n with ks := n.ks.map (wmgSwap src dst) } = (ksOf n).map (wmgSwapK src dst) := by
  simp only [ksOf, List.map_map]
  congr 1
  funext k
  cases k with
  | key c y => by_cases h : y = src <;> simp [wmgSwap, wmgSwapK, kOf, h]
  | time _ => rfl
  | del _ => rfl

theorem wmg_swap_shape (ks : List Klong) (src dst : NodeId) :
    (ks.map (wmgSwapK src dst)).map wmgShape = ks.map wmgShape := by
  rw [List.map_map]
  congr 1
  funext k
  cases k with
  | key c y => by_cases h : y = src <;> simp [wmgSwapK, wmgShape, h]
  | time _ => rfl
  | del _ => rfl

/-- The index-dependent map of `retarget` is the plain one when every klong naming src is
after index ti. -/
theorem wmg_zip_swap (ks : List MKlong) (ti : Nat) (src dst : NodeId)
    (h : ∀ j c, ks[j]? = some (.key c src) → ti < j) (F : MKlong × Nat → MKlong)
    (hF : ∀ k j, F (k, j) = match k with
      | .key cv y => if ti < j && y == src then .key cv dst else k
      | _ => k) :
    ks.zipIdx.map F = ks.map (wmgSwap src dst) := by
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_map, List.getElem?_map, List.getElem?_zipIdx]
  cases hk : ks[j]? with
  | none => rfl
  | some k =>
    simp only [Option.map_some, Option.some.injEq, Nat.zero_add]
    rw [hF]
    cases k with
    | key c y =>
      by_cases hy : y = src
      · subst hy
        have := h j c hk
        simp [this, wmgSwap]
      · simp [hy, wmgSwap]
    | time _ => rfl
    | del _ => rfl

/-- The live klongs are kept when no live klong names src. -/
theorem wmg_swap_live {n : MNode} (hwf : klongsWf (ksOf n) = true) {src dst : NodeId}
    (hns : ∀ c, (c, src) ∉ live (ksOf n)) :
    live (ksOf { n with ks := n.ks.map (wmgSwap src dst) }) = live (ksOf n) := by
  set n' : MNode := { n with ks := n.ks.map (wmgSwap src dst) }
  have hks : ksOf n' = (ksOf n).map (wmgSwapK src dst) := wmg_ksOf_swap n src dst
  have hsh : (ksOf n').map wmgShape = (ksOf n).map wmgShape := by
    rw [hks]; exact wmg_swap_shape _ _ _
  have hwf' : klongsWf (ksOf n') = true := by rw [wmg_shape_wf hsh]; exact hwf
  have hcv := wmg_shape_cvAt hsh
  have hlb := wmg_shape_lastBitmap hsh
  refine cvSorted_ext (live_sorted _) (live_sorted _) (fun ⟨c, y⟩ => ⟨fun h => ?_, fun h => ?_⟩)
  · obtain ⟨j, h1, h2, h3⟩ := wmg_live_liveAt hwf' h
    rw [hks, List.getElem?_map] at h1
    obtain ⟨k, hk, hkk⟩ := Option.map_eq_some_iff.mp h1
    have hk' : k = Klong.key c y ∧ y ≠ src ∨ k = Klong.key c src ∧ y = dst := by
      cases k with
      | key c0 y0 =>
        by_cases hy : y0 = src
        · subst hy
          simp only [wmgSwapK, ite_true, Klong.key.injEq] at hkk
          exact Or.inr ⟨by rw [hkk.1], hkk.2.symm⟩
        · simp only [wmgSwapK, hy, ite_false, Klong.key.injEq] at hkk
          exact Or.inl ⟨by rw [hkk.1, hkk.2], by rw [← hkk.2]; exact hy⟩
      | time _ => simp [wmgSwapK] at hkk
      | del _ => simp [wmgSwapK] at hkk
    have hL : ∀ y0, (ksOf n)[j]? = some (Klong.key c y0) → (c, y0) ∈ live (ksOf n) := by
      intro y0 hy0
      refine (linkIndex_some hwf (wmp_linkIndex (n := n) (j := j) ⟨hy0, ?_, fun j' hj' => ?_⟩)).2.1
      · rw [← hlb]; exact h2
      · rw [← hcv]; exact h3 j' hj'
    rcases hk' with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact hL y hk
    · exact absurd (hL src hk) (hns c)
  · obtain ⟨j, h1, h2, h3⟩ := wmg_live_liveAt hwf h
    have hy : y ≠ src := fun e => hns c (e ▸ h)
    refine (linkIndex_some hwf' (wmp_linkIndex (n := n') (j := j) ⟨?_, ?_, fun j' hj' => ?_⟩)).2.1
    · rw [hks, List.getElem?_map, h1]
      simp [wmgSwapK, hy]
    · rw [hlb]; exact h2
    · rw [hcv]; exact h3 j' hj'


/-! ## Time klongs -/

theorem wmg_lti_fold (F : Option Nat → MKlong × Nat → Option Nat)
    (hF : ∀ acc k i, F acc (k, i) = match k with
      | .time _ => some i
      | _ => acc) : ∀ (l : List MKlong) (s : Nat) (acc : Option Nat) (ti : Nat),
    (l.zipIdx s).foldl F acc = some ti →
      acc = some ti ∨ (s ≤ ti ∧ ∃ t, l[ti - s]? = some (.time t))
  | [], _, _, _, h => Or.inl h
  | k :: l, s, acc, ti, h => by
    rw [List.zipIdx_cons, List.foldl_cons] at h
    rcases wmg_lti_fold F hF l (s + 1) _ ti h with h1 | ⟨h1, t, h2⟩
    · rw [hF] at h1
      cases k with
      | time t =>
        simp only [Option.some.injEq] at h1
        subst h1
        exact Or.inr ⟨Nat.le_refl _, t, by simp⟩
      | key c y => exact Or.inl h1
      | del b => exact Or.inl h1
    · refine Or.inr ⟨by omega, t, ?_⟩
      rw [show ti - s = (ti - (s + 1)) + 1 by omega]
      simpa using h2

/-- The last time index names a time klong. -/
theorem wmg_lti_time {n : MNode} {ti : Nat} (h : n.lastTimeIndex = some ti) :
    ∃ t, n.ks[ti]? = some (.time t) := by
  unfold SIS.Tree.KNode.lastTimeIndex at h
  rcases wmg_lti_fold _ (fun acc k i => by cases k <;> rfl) n.ks 0 none ti h with h1 | ⟨-, t, h2⟩
  · cases h1
  · exact ⟨t, by simpa using h2⟩

theorem wmg_tfold_no_time : ∀ (l : List Klong) (b : Bool) (t0 : Time),
    (∀ t, Klong.time t ∈ l → t ≤ t0) → (l.foldl tStep (b, some t0)).1 = true →
      ∀ t, Klong.time t ∉ l
  | [], _, _, _, _, _, h => by simp at h
  | k :: l, b, t0, hle, h, t, hm => by
    rw [List.foldl_cons] at h
    have hle' : ∀ t, Klong.time t ∈ l → t ≤ t0 := fun t ht => hle t (List.mem_cons_of_mem _ ht)
    cases k with
    | key c y =>
      refine wmg_tfold_no_time l b t0 hle' h t ?_
      rcases List.mem_cons.mp hm with e | e
      · cases e
      · exact e
    | del bs =>
      refine wmg_tfold_no_time l b t0 hle' h t ?_
      rcases List.mem_cons.mp hm with e | e
      · cases e
      · exact e
    | time t' =>
      have ht := hle t' List.mem_cons_self
      have e : tStep (b, some t0) (.time t') = (false, some t') := by
        simp only [tStep, Bool.and_eq_false_iff, decide_eq_false_iff_not, Prod.mk.injEq, and_true]
        exact Or.inr (Nat.not_lt.mpr ht)
      rw [e, wcr_tfold_false] at h
      cases h

/-- With times increasing and none after i, no time klong comes after a time klong of i. -/
theorem wmg_no_time_after {ks : List Klong} {i : Time} (hw : timesOk ks = true)
    (hle : ∀ t, Klong.time t ∈ ks → t ≤ i) {a : Nat} (ha : ks[a]? = some (Klong.time i))
    {b : Nat} (hab : a < b) (t : Time) : ks[b]? ≠ some (Klong.time t) := by
  intro hb
  have hlt : a < ks.length := (List.getElem?_eq_some_iff.mp ha).1
  have hsplit : ks = ks.take (a + 1) ++ ks.drop (a + 1) := (List.take_append_drop _ _).symm
  have htake : ks.take (a + 1) = ks.take a ++ [Klong.time i] := by
    rw [List.take_add_one, ha]
    rfl
  rw [timesOk_eq, Bool.and_eq_true] at hw
  have h2 := hw.2
  rw [hsplit, List.foldl_append, htake, List.foldl_append, List.foldl_cons, List.foldl_nil] at h2
  generalize (ks.take a).foldl tStep (true, none) = acc at h2
  obtain ⟨bb, ob⟩ := acc
  have e2 : tStep (bb, ob) (Klong.time i) = ((tStep (bb, ob) (Klong.time i)).1, some i) := rfl
  rw [e2] at h2
  have hm : Klong.time t ∈ ks.drop (a + 1) := by
    have : (ks.drop (a + 1))[b - (a + 1)]? = some (Klong.time t) := by
      rw [List.getElem?_drop, show a + 1 + (b - (a + 1)) = b by omega]
      exact hb
    exact List.mem_of_getElem? this
  refine wmg_tfold_no_time (ks.drop (a + 1)) _ i (fun t' ht' => hle t' ?_) h2 t hm
  rw [hsplit]
  exact List.mem_append_right _ ht'


/-- A tree sound with no node over its size is sound with x allowed over it. -/
theorem wmg_sound_some {M : Nat} {T : Tree} {r : NodeId} {C : List (Key × Nat)}
    (h : Sound M none T r C) (x : NodeId) : Sound M (some x) T r C := by
  refine ⟨h.key, h.good, fun z hz m hm => ?_, h.holds, h.tree⟩
  have := h.nodes z hz m hm
  simp only [reduceCtorEq, ite_false] at this
  exact tr_nodeOk this (by split <;> omega) (fun _ h => h)

/-- A node not reached and named by no node reached is dropped: the tree stays sound. -/
theorem wmg_sound_take {M : Nat} {ex : Option NodeId} {A B : Tree} {r o : NodeId}
    {C : List (Key × Nat)} (h : Sound M ex A r C) (hsame : ∀ z, z ≠ o → B.obj z = A.obj z)
    (hoR : o ∉ reachAt A (A.fuel r) r)
    (hnm : ∀ z ∈ reachAt A (A.fuel r) r, ∀ m, A.obj z = some (.key m) → ∀ c,
      Klong.key c o ∉ m.ks) : Sound M ex B r C := by
  have ha : ∀ z ∈ reachAt A (A.fuel r) r, B.obj z = A.obj z :=
    fun z hz => hsame z (fun e => hoR (e ▸ hz))
  have hr : B.obj r = A.obj r := ha r (tc_self _ _ _)
  have hf : B.fuel r = A.fuel r := by simp [Tree.fuel, hr]
  have hR : reachAt B (B.fuel r) r = reachAt A (A.fuel r) r := by
    rw [hf]
    exact reachAt_agree _ _ ha
  obtain ⟨n, ho, hne⟩ := h.key
  refine ⟨⟨n, hr.trans ho, hne⟩, h.good.agree ha, ?_, ?_, ?_⟩
  · intro z hz m hm
    rw [hR] at hz
    rw [ha z hz] at hm
    have hok := h.nodes z hz m hm
    simp only [nodeOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hok ⊢
    refine ⟨hok.1, fun k hk => ?_⟩
    cases k with
    | key c y =>
      have hy : y ≠ o := fun e => hnm z hz m hm c (e ▸ hk)
      show (B.obj y).isSome = true
      rw [hsame y hy]
      exact hok.2 _ hk
    | time t => rfl
    | del b => rfl
  · rw [← h.holds]
    exact L_agree ha
  · rw [hR]
    exact h.tree


/-! ## The two nodes merged, left out -/

theorem wmg_reach_eq {i : Time} {s : Tree} {u u' : MW} (hr : u'.top.rootKey = u.top.rootKey)
    (ha : ∀ z ∈ reachOf i s u, (treeOf i s u').obj z = (treeOf i s u).obj z) :
    reachOf i s u' = reachOf i s u := by
  unfold reachOf at *
  rw [hr]
  have hf : (treeOf i s u').fuel u.top.rootKey = (treeOf i s u).fuel u.top.rootKey := by
    simp [Tree.fuel, ha _ (tc_self _ _ _)]
  rw [hf]
  exact reachAt_agree _ _ ha

/-- `unlink o` of a node of before, not reached: cut back to its klongs of before (if it has
klongs of the transaction), which name nodes of s; nothing else changes. -/
theorem wmg_unlink {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} (hb : Books i base s tp) (hsn : SNamed s) {u : MW} {C : List (Key × Nat)}
    (hI : PInv p i base s tp none C u) {X : List NodeId} (hX : WcrLinkX X i s u) {o : NodeId}
    {on : MNode} (hlo : u.nodes.lookup o = some on) (hto : u.taken.contains o = false)
    (hoR : o ∉ reachOf i s u) (hwfo : klongsWf (ksOf on) = true) {n0 : KNode}
    (hso : s.obj o = some (.key n0)) :
    WP (SIS.Tree.unlink o) { p := p, i := i, view := v } u
      (fun _ u' => PInv p i base s tp none C u' ∧ WcrLinkX (X.erase o) i s u' ∧
        (∀ z, z ≠ o → (treeOf i s u').obj z = (treeOf i s u).obj z) ∧
        (∀ z n, z ≠ o → u.nodes.lookup z = some n → u'.nodes.lookup z = some n) ∧
        u'.taken = u.taken ∧ u'.top = u.top ∧ u'.path = u.path ∧ u'.outside = u.outside ∧
        u'.next = u.next ∧ u'.made = u.made ∧ reachOf i s u' = reachOf i s u ∧
        ∀ no, (treeOf i s u').obj o = some (.key no) → ∀ c y, Klong.key c y ∈ no.ks →
          (s.obj y).isSome = true) := by
  have hAo := treeOf_obj_overlay i s hlo hto
  obtain ⟨-, hleaf0, he⟩ := frame_overlay_ext hI.frame hlo hto hso
  have h0 := prim_timesBefore (hb.times o n0 hso)
  have hnamed : ∀ c y, Klong.key c y ∈ n0.ks → (s.obj y).isSome = true :=
    fun c y h => hsn o n0 hso c y h
  -- the link book, if o's node names only nodes of s
  have hlinkX : ∀ u' : MW, reachOf i s u' = reachOf i s u → u'.top = u.top →
      (∀ z, z ≠ o → (treeOf i s u').obj z = (treeOf i s u).obj z) →
      (∀ no, (treeOf i s u').obj o = some (.key no) → ∀ c y, Klong.key c y ∈ no.ks →
        (s.obj y).isSome = true) → WcrLinkX (X.erase o) i s u' := by
    intro u' hR htop hsame hon m hm mn hBm hsm w0 nw c hBw hk hwm hwX
    rw [hR] at hm
    have hmo : m ≠ o := fun e => hoR (e ▸ hm)
    rw [hsame m hmo] at hBm
    have hw0 : w0 ≠ o := by
      intro e
      rw [e] at hBw
      have := hon nw hBw c m hk
      rw [hsm] at this
      cases this
    have hwX' : w0 ∉ X := fun h => hwX ((List.mem_erase_of_ne hw0).mpr h)
    rw [hsame w0 hw0] at hBw
    obtain ⟨h1, h2⟩ := hX m hm mn hBm hsm w0 nw c hBw hk hwm hwX'
    refine ⟨by rw [htop]; exact h1, fun u2 nu2 c2 hB2 hk2 hu2m hu2X => ?_⟩
    have hu2o : u2 ≠ o := by
      intro e
      rw [e] at hB2
      have := hon nu2 hB2 c2 m hk2
      rw [hsm] at this
      cases this
    have hu2X' : u2 ∉ X := fun h => hu2X ((List.mem_erase_of_ne hu2o).mpr h)
    rw [hsame u2 hu2o] at hB2
    exact h2 u2 nu2 c2 hB2 hk2 hu2m hu2X'
  unfold SIS.Tree.unlink
  refine wput_read ?_
  refine wput_ok (getNode_hit _ hlo) ?_
  dsimp only
  split
  · next hlt =>
    have hlt' : on.lastTime = some i := by simpa using hlt
    intro r u' hr
    rw [putNode_eq] at hr
    simp only [Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨-, rfl⟩ := hr
    have hks : ksOf (on.toPrev (i - 1)) = n0.ks :=
      toPrev_ext h0 (hb.first o n0 hso) he
    have hTW := treeOf_withNode i s (on.toPrev (i - 1)) hto (w := u) (x := o)
    have hsame : ∀ z, z ≠ o → (treeOf i s (u.withNode o (on.toPrev (i - 1)))).obj z =
        (treeOf i s u).obj z := by
      intro z hz
      rw [hTW]
      simp [Tree.set, hz]
    have hBo : (treeOf i s (u.withNode o (on.toPrev (i - 1)))).obj o =
        some (.key ⟨wLevel s u o, on.leaf, n0.ks⟩) := by
      rw [hTW, ← hks]
      simp [Tree.set, toPrev_leaf]
    have hon : ∀ no, (treeOf i s (u.withNode o (on.toPrev (i - 1)))).obj o = some (.key no) →
        ∀ c y, Klong.key c y ∈ no.ks → (s.obj y).isSome = true := by
      intro no hno c y hk
      rw [hBo] at hno
      cases hno
      exact hnamed c y hk
    have hR : reachOf i s (u.withNode o (on.toPrev (i - 1))) = reachOf i s u :=
      wmg_reach_eq rfl (fun z hz => hsame z (fun e => hoR (e ▸ hz)))
    have hfst : (on.toPrev (i - 1)).ks.head? = on.ks.head? ∧
        ∀ t, SIS.Tree.Klong.time t ∈ (on.toPrev (i - 1)).ks → t ≤ i := by
      refine ts_old hI.books hlo hto (fun e => ?_)
      have := (hI.books.first o on hlo hto).mp (by rw [hso]; rfl)
      exact this e
    refine ⟨⟨hI.root, ?_, frame_withNode hI.frame hlo hto (toPrev_leaf _ _)
        (fun n1 hs1 => by rw [hso] at hs1; cases hs1; exact Or.inl hks), hI.top, ?_,
        putBooks_withNode hI.books hlo hto (toPrev_leaf _ _) hfst.1 hfst.2⟩,
      hlinkX _ hR rfl hsame hon, hsame, fun z n hz h => ?_, rfl, rfl, rfl, rfl, rfl, rfl, hR, hon⟩
    · refine hI.sound.agree (fun z hz => hsame z (fun e => hoR (e ▸ hz))) (fun z hz => ?_)
      by_cases hzo : z = o
      · rw [hzo, hBo]; rfl
      · rw [hsame z hzo]; exact hz
    · -- BalancedOK, by the nodes reached: o is not reached, and they are as before
      have hrB : (treeOf i s (u.withNode o (on.toPrev (i - 1)))).root = some u.top.rootKey :=
        hI.root
      refine Balanced.of_reach (N := [o]) hI.balanced (fun z hz => ?_) (fun z _ hz => ?_)
        (fun y m hm => ?_) (fun z hz hzB m hm => ?_)
      · left
        rw [reach_of_root hrB] at hz
        rw [reach_of_root hI.root]
        have h1 : z ∈ reachOf i s (u.withNode o (on.toPrev (i - 1))) := hz
        rw [hR] at h1
        exact h1
      · exact hsame z (by simpa using hz)
      · by_cases hyo : y = o
        · rw [hyo, hAo] at hm
          cases hm
          exact ⟨⟨wLevel s u o, on.leaf, n0.ks⟩, by rw [hyo]; exact hBo, rfl⟩
        · exact ⟨m, by rw [hsame y hyo]; exact hm, rfl⟩
      · simp only [List.mem_singleton] at hz
        exfalso
        apply hoR
        rw [reach_of_root hrB] at hzB
        have h1 : z ∈ reachOf i s (u.withNode o (on.toPrev (i - 1))) := hzB
        rw [hR, hz] at h1
        exact h1
    · rw [MW.withNode, lookup_upsert_ne _ _ hz]
      exact h
  · next hlt =>
    rw [wp_pure]
    have hks : ksOf on = n0.ks := by
      simp only [klongsWf, Bool.and_eq_true] at hwfo
      exact wcr_ks_old hwfo.1 (wput_timesLe hI.books hlo) he (by simpa using hlt)
    have hon : ∀ no, (treeOf i s u).obj o = some (.key no) → ∀ c y, Klong.key c y ∈ no.ks →
        (s.obj y).isSome = true := by
      intro no hno c y hk
      rw [hAo] at hno
      cases hno
      rw [hks] at hk
      exact hnamed c y hk
    exact ⟨hI, hlinkX u rfl rfl (fun _ _ => rfl) hon, fun _ _ => rfl, fun _ _ _ h => h, rfl,
      rfl, rfl, rfl, rfl, rfl, rfl, hon⟩



/-- `retarget q o m1`: q's klongs of the transaction that name o name m1; when all of q's klongs
that name o come after its last time klong, that is every klong of q that names o. -/
theorem wmg_retarget {p : MParams} {i : Time} {v : View BVal} {u : MW} {q o m1 : NodeId}
    {nq : MNode} (hlq : u.nodes.lookup q = some nq)
    (hafter : ∀ j c, nq.ks[j]? = some (.key c o) → nq.lastTime = some i ∧
      ∀ ti, nq.lastTimeIndex = some ti → ti < j) :
    WP (SIS.Tree.retarget q o m1) { p := p, i := i, view := v } u
      (fun _ u1 => (u1 = u ∧ ∀ (j c : Nat), nq.ks[j]? ≠ some (SIS.Tree.Klong.key c o)) ∨
        u1 = u.withNode q { nq with ks := nq.ks.map (wmgSwap o m1) }) := by
  unfold SIS.Tree.retarget
  refine wput_read ?_
  refine wput_ok (getNode_hit _ hlq) ?_
  refine wp_ite _ _ _ _ _ _ (fun hlt => ?_) (fun hlt => ?_)
  · have hlt' : nq.lastTime = some i := by simpa using hlt
    have hti : ∀ j c, nq.ks[j]? = some (.key c o) → nq.lastTimeIndex.getD 0 < j := by
      intro j c hj
      obtain ⟨-, h2⟩ := hafter j c hj
      have hm := lastT_mem (show lastT (ksOf nq) = some i by rw [lastT_ksOf]; exact hlt')
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hm
      obtain ⟨ti, h3, -⟩ := wmp_lti_ge hk
      rw [h3]
      exact h2 ti h3
    intro r u1 hr
    rw [putNode_eq] at hr
    simp only [Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨-, rfl⟩ := hr
    right
    congr 2
    exact wmg_zip_swap nq.ks _ o m1 hti _ (fun k j => by cases k <;> rfl)
  · rw [wp_pure]
    left
    refine ⟨rfl, fun j c hj => hlt ?_⟩
    simpa using (hafter j c hj).1


/-- `takenBack o` of a node the transaction made, not reached and named by no node: the map
without o. -/
theorem wmg_drop {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top} {u : MW}
    {C : List (Key × Nat)} (hI : PInv p i base s tp none C u) {X : List NodeId}
    (hX : WcrLinkX X i s u) {o : NodeId} {on : MNode} (hlo : u.nodes.lookup o = some on)
    (hoR : o ∉ reachOf i s u) (hso : s.obj o = none)
    (hnone : ∀ u0 nu c, (treeOf i s u).obj u0 = some (.key nu) → Klong.key c o ∉ nu.ks) :
    PInv p i base s tp none C { u with taken := o :: u.taken } ∧
      WcrLinkX (X.erase o) i s { u with taken := o :: u.taken } ∧
      (∀ z, (treeOf i s { u with taken := o :: u.taken }).obj z =
        if z = o then none else (treeOf i s u).obj z) ∧
      reachOf i s { u with taken := o :: u.taken } = reachOf i s u := by
  have hC := wcr_treeOf_take i s u o
  have hCne : ∀ z, z ≠ o → (treeOf i s { u with taken := o :: u.taken }).obj z =
      (treeOf i s u).obj z := fun z hz => by rw [hC]; simp [hz]
  have hCo : (treeOf i s { u with taken := o :: u.taken }).obj o = none := by rw [hC]; simp
  have hR : reachOf i s { u with taken := o :: u.taken } = reachOf i s u :=
    wmg_reach_eq rfl (fun z hz => hCne z (fun e => hoR (e ▸ hz)))
  have hom : o ∈ u.made.map (·.id) := by
    rcases hI.books.overlay o on hlo with h | h
    · rw [hso] at h; cases h
    · exact h
  refine ⟨⟨?_, ?_, ?_, hI.top, ?_, wcr_putBooks_take hI.books hom⟩, ?_, hC, hR⟩
  · show (treeOf i s { u with taken := o :: u.taken }).root = some u.top.rootKey
    exact hI.root
  · exact wmg_sound_take hI.sound hCne hoR (fun z _ m hm c => hnone z m c hm)
  · obtain ⟨f1, f2, f3⟩ := hI.frame
    have hD : dirtyOf { u with taken := o :: u.taken } = dirtyOf u := rfl
    rw [hD]
    refine ⟨fun z ob hz => ?_, fun z m hz hsz => ?_, ?_⟩
    · have hzo : z ≠ o := by intro e; rw [e, hso] at hz; cases hz
      rw [hCne z hzo]
      exact f1 z ob hz
    · have hzo : z ≠ o := by intro e; rw [e, hCo] at hz; cases hz
      rw [hCne z hzo] at hz
      exact f2 z m hz hsz
    · exact f3
  · -- BalancedOK, by the nodes reached: as before, and o is not reached
    intro z hzr nz hz
    have hrN : (treeOf i s { u with taken := o :: u.taken }).root = some u.top.rootKey := hI.root
    rw [reach_of_root hrN] at hzr
    have hzR : z ∈ reachOf i s u := by
      rw [← hR]
      exact hzr
    have hzo : z ≠ o := fun e => hoR (e ▸ hzR)
    rw [hCne z hzo] at hz
    obtain ⟨h1, h2, h3⟩ := hI.balanced z (by rw [reach_of_root hI.root]; exact hzR) nz hz
    refine ⟨h1, h2, fun hl c y hk => ?_⟩
    obtain ⟨m, hm, hlev⟩ := h3 hl c y hk
    have hyo : y ≠ o := fun e => hnone z nz c hz (e ▸ prim_live_mem_key hk)
    exact ⟨m, by rw [hCne y hyo]; exact hm, hlev⟩
  · intro m hm mn hBm hsm w0 nw c hBw hk hwm hwX
    rw [hR] at hm
    have hmo : m ≠ o := fun e => hoR (e ▸ hm)
    rw [hCne m hmo] at hBm
    have hw0 : w0 ≠ o := by intro e; rw [e, hCo] at hBw; cases hBw
    rw [hCne w0 hw0] at hBw
    have hwX' : w0 ∉ X := fun h => hwX ((List.mem_erase_of_ne hw0).mpr h)
    obtain ⟨h1, h2⟩ := hX m hm mn hBm hsm w0 nw c hBw hk hwm hwX'
    refine ⟨h1, fun u2 nu2 c2 hB2 hk2 hu2m hu2X => ?_⟩
    have hu2o : u2 ≠ o := by intro e; rw [e, hCo] at hB2; cases hB2
    rw [hCne u2 hu2o] at hB2
    exact h2 u2 nu2 c2 hB2 hk2 hu2m (fun h => hu2X ((List.mem_erase_of_ne hu2o).mpr h))


/-- The state after `retarget q o m1` that points q's klongs naming o to m1. -/
theorem wmg_swap_state {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    (hsn : SNamed s) {u : MW} {C : List (Key × Nat)} (hI : PInv p i base s tp none C u)
    {X : List NodeId} (hX : WcrLinkX X i s u) {o q m1 : NodeId} {nq : MNode}
    (hlq : u.nodes.lookup q = some nq) (htq : u.taken.contains q = false) (_hql : nq.leaf = false)
    (hso : s.obj o = none) (hm1o : m1 ≠ o)
    (hnamers : ∀ u0 nu c, (treeOf i s u).obj u0 = some (.key nu) → Klong.key c o ∈ nu.ks → u0 = q)
    (hlive : ∀ c, (c, o) ∉ live (ksOf nq))
    (hqn : ∀ c, Klong.key c o ∈ ksOf nq → klongsWf (ksOf nq) = true ∧ nq.size ≤ p.M ∧
      ∃ c', Klong.key c' m1 ∈ ksOf nq)
    {nm1 : KNode} (hm1 : (treeOf i s u).obj m1 = some (.key nm1))
    (hm1lev : ∀ no, (treeOf i s u).obj o = some (.key no) → nm1.level = no.level) :
    PInv p i base s tp none C (u.withNode q { nq with ks := nq.ks.map (wmgSwap o m1) }) ∧
      WcrLinkX X i s (u.withNode q { nq with ks := nq.ks.map (wmgSwap o m1) }) ∧
      (∀ z, z ≠ q → (treeOf i s (u.withNode q { nq with ks := nq.ks.map (wmgSwap o m1) })).obj z =
        (treeOf i s u).obj z) ∧
      reachOf i s (u.withNode q { nq with ks := nq.ks.map (wmgSwap o m1) }) = reachOf i s u ∧
      (∀ u0 nu c, (treeOf i s (u.withNode q { nq with ks := nq.ks.map (wmgSwap o m1) })).obj u0 =
        some (.key nu) → Klong.key c o ∉ nu.ks) ∧
      live (ksOf { nq with ks := nq.ks.map (wmgSwap o m1) }) = live (ksOf nq) ∧
      (klongsWf (ksOf nq) = true → klongsWf (ksOf { nq with ks := nq.ks.map (wmgSwap o m1) })
          = true) := by
  set nq' : MNode := { nq with ks := nq.ks.map (wmgSwap o m1) }
  have hsh0 : (ksOf nq').map wmgShape = (ksOf nq).map wmgShape := by
    rw [wmg_ksOf_swap]; exact wmg_swap_shape _ _ _
  have hwfimp : klongsWf (ksOf nq) = true → klongsWf (ksOf nq') = true := fun h => by
    rw [wmg_shape_wf hsh0]; exact h
  have hks : ksOf nq' = (ksOf nq).map (wmgSwapK o m1) := wmg_ksOf_swap nq o m1
  have hAq := treeOf_obj_overlay i s hlq htq
  have hTW : treeOf i s (u.withNode q nq') =
      (treeOf i s u).set q (.key ⟨wLevel s u q, nq'.leaf, ksOf nq'⟩) := treeOf_withNode i s nq' htq
  have hsame : ∀ z, z ≠ q → (treeOf i s (u.withNode q nq')).obj z = (treeOf i s u).obj z := by
    intro z hz; rw [hTW]; simp [Tree.set, hz]
  have hBq : (treeOf i s (u.withNode q nq')).obj q =
      some (.key ⟨wLevel s u q, nq.leaf, ksOf nq'⟩) := by rw [hTW]; simp [Tree.set]; rfl
  -- the key klongs of q after: those of before, o's pointed to m1
  have hkm : ∀ c y, Klong.key c y ∈ ksOf nq' →
      (Klong.key c y ∈ ksOf nq ∧ y ≠ o) ∨ (y = m1 ∧ Klong.key c o ∈ ksOf nq) := by
    intro c y h
    rw [hks, List.mem_map] at h
    obtain ⟨k, hk, hkk⟩ := h
    cases k with
    | key c0 y0 =>
      by_cases hy : y0 = o
      · subst hy
        simp only [wmgSwapK, ite_true, Klong.key.injEq] at hkk
        exact Or.inr ⟨hkk.2.symm, by rw [← hkk.1]; exact hk⟩
      · simp only [wmgSwapK, hy, ite_false, Klong.key.injEq] at hkk
        exact Or.inl ⟨by rw [← hkk.1, ← hkk.2]; exact hk, by rw [← hkk.2]; exact hy⟩
    | time _ => simp [wmgSwapK] at hkk
    | del _ => simp [wmgSwapK] at hkk
  have hnoo : ∀ c, Klong.key c o ∉ ksOf nq' := by
    intro c h
    rcases hkm c o h with ⟨-, h1⟩ | ⟨h1, -⟩
    · exact h1 rfl
    · exact hm1o h1.symm
  have hnone : ∀ u0 nu c, (treeOf i s (u.withNode q nq')).obj u0 = some (.key nu) →
      Klong.key c o ∉ nu.ks := by
    intro u0 nu c hu hk
    by_cases hu0 : u0 = q
    · subst hu0
      rw [hBq] at hu
      cases hu
      exact hnoo c hk
    · rw [hsame u0 hu0] at hu
      exact hu0 (hnamers u0 nu c hu hk)
  by_cases hex : ∃ c, Klong.key c o ∈ ksOf nq
  · obtain ⟨c0, hc0⟩ := hex
    obtain ⟨hwf, hsz, ⟨cm, hcm⟩⟩ := hqn c0 hc0
    have hsh : (ksOf nq').map wmgShape = (ksOf nq).map wmgShape := by
      rw [hks]; exact wmg_swap_shape _ _ _
    have hwf' : klongsWf (ksOf nq') = true := by rw [wmg_shape_wf hsh]; exact hwf
    have hlv : live (ksOf nq') = live (ksOf nq) := wmg_swap_live hwf hlive
    have hR : reachOf i s (u.withNode q nq') = reachOf i s u := by
      unfold reachOf
      exact ts_reach_live hAq hBq (by simpa using hlv) rfl hsame _
    have hsz' : nq'.size = nq.size := by simp [nq', SIS.Tree.KNode.size]
    obtain ⟨t0, rest, hr0⟩ := hI.books.timeFirst q nq hlq htq
    have hmapid : ∀ l : List Klong, (∀ c, Klong.key c o ∉ l) → l.map (wmgSwapK o m1) = l := by
      intro l hl
      induction l with
      | nil => rfl
      | cons k l ih =>
        rw [List.map_cons, ih (fun c h => hl c (List.mem_cons_of_mem _ h))]
        congr 1
        cases k with
        | key c y =>
          have hy : y ≠ o := fun e => hl c (by rw [e]; exact List.mem_cons_self)
          simp [wmgSwapK, hy]
        | time _ => rfl
        | del _ => rfl
    -- a namer after is a namer before
    have hnm : ∀ u0 nu c m, (treeOf i s (u.withNode q nq')).obj u0 = some (.key nu) →
        Klong.key c m ∈ nu.ks → ∃ nu0 c0, (treeOf i s u).obj u0 = some (.key nu0) ∧
          Klong.key c0 m ∈ nu0.ks := by
      intro u0 nu c m hu hk
      by_cases hu0 : u0 = q
      · subst hu0
        rw [hBq] at hu
        cases hu
        rcases hkm c m hk with ⟨h1, -⟩ | ⟨rfl, -⟩
        · exact ⟨_, c, hAq, h1⟩
        · exact ⟨_, cm, hAq, hcm⟩
      · rw [hsame u0 hu0] at hu
        exact ⟨nu, c, hu, hk⟩
    have hobj : ∀ m mn, (treeOf i s (u.withNode q nq')).obj m = some (.key mn) →
        ∃ mn0, (treeOf i s u).obj m = some (.key mn0) := by
      intro m mn hm
      by_cases hmq : m = q
      · subst hmq; exact ⟨_, hAq⟩
      · rw [hsame m hmq] at hm; exact ⟨mn, hm⟩
    refine ⟨⟨hI.root, ?_, ?_, hI.top, ?_, ?_⟩, ?_, hsame, hR, hnone, hlv, hwfimp⟩
    · by_cases hqR : q ∈ reachOf i s u
      · -- q reached: its klongs name nodes (`Sound`)
        have hok := hI.sound.nodes q hqR _ hAq
        simp only [reduceCtorEq, ite_false, nodeOk, Bool.and_eq_true, decide_eq_true_eq,
          List.all_eq_true] at hok
        refine Sound.inPlace (wmg_sound_some hI.sound q) hAq
          ⟨_, hBq, rfl, rfl, by simpa using hlv, ?_⟩ hsame
        simp only [nodeOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
        refine ⟨⟨by rw [ksOf_length, hsz']; exact hsz, hwf'⟩, fun k hk => ?_⟩
        cases k with
        | key c y =>
          show ((treeOf i s (u.withNode q nq')).obj y).isSome = true
          by_cases hyq : y = q
          · rw [hyq, hBq]; rfl
          · rw [hsame y hyq]
            rcases hkm c y hk with ⟨h1, -⟩ | ⟨rfl, -⟩
            · exact hok.2 _ h1
            · rw [hm1]; rfl
        | time _ => rfl
        | del _ => rfl
      · -- q not reached: the nodes reached are as before
        refine hI.sound.agree (fun z hz => hsame z (fun e => hqR (e ▸ hz))) (fun z hz => ?_)
        by_cases hzq : z = q
        · rw [hzq, hBq]; rfl
        · rw [hsame z hzq]; exact hz
    · refine frame_withNode hI.frame hlq htq rfl (fun n0 hs0 => ?_)
      obtain ⟨-, -, he⟩ := frame_overlay_ext hI.frame hlq htq hs0
      have hn0 : ∀ c, Klong.key c o ∉ n0.ks := by
        intro c h
        have := hsn q n0 hs0 c o h
        rw [hso] at this
        cases this
      rw [hks]
      rcases he with he | ⟨more, he⟩
      · exact Or.inl (by rw [he]; exact hmapid _ hn0)
      · refine Or.inr ⟨more.map (wmgSwapK o m1), ?_⟩
        rw [he, List.map_append, hmapid _ hn0]
        rfl
    · -- BalancedOK, by the nodes reached: q's live klongs are as before
      have hrB : (treeOf i s (u.withNode q nq')).root = some u.top.rootKey := hI.root
      have hlevq : ∀ y m, (treeOf i s u).obj y = some (.key m) →
          ∃ m', (treeOf i s (u.withNode q nq')).obj y = some (.key m') ∧ m'.level = m.level := by
        intro y m hm
        by_cases hyq : y = q
        · rw [hyq, hAq] at hm
          cases hm
          exact ⟨⟨wLevel s u q, nq.leaf, ksOf nq'⟩, by rw [hyq]; exact hBq, rfl⟩
        · exact ⟨m, by rw [hsame y hyq]; exact hm, rfl⟩
      refine Balanced.of_reach (N := [q]) hI.balanced (fun z hz => ?_) (fun z _ hz => ?_)
        hlevq (fun z hz hzB m hm => ?_)
      · left
        rw [reach_of_root hrB] at hz
        rw [reach_of_root hI.root]
        have h1 : z ∈ reachOf i s (u.withNode q nq') := hz
        rw [hR] at h1
        exact h1
      · exact hsame z (by simpa using hz)
      · simp only [List.mem_singleton] at hz
        rw [hz] at hzB hm
        rw [hBq] at hm
        cases hm
        rw [reach_of_root hrB] at hzB
        have h1 : q ∈ reachOf i s (u.withNode q nq') := hzB
        rw [hR] at h1
        obtain ⟨b1, b2, b3⟩ := hI.balanced q (by rw [reach_of_root hI.root]; exact h1) _ hAq
        refine ⟨b1, b2, fun hl c y hk => ?_⟩
        have hk' : (c, y) ∈ live (ksOf nq) := by rw [← hlv]; exact hk
        obtain ⟨m', hm', hl'⟩ := b3 hl c y hk'
        obtain ⟨m'', hm'', he⟩ := hlevq y m' hm'
        exact ⟨m'', hm'', by rw [he]; exact hl'⟩
    · refine putBooks_withNode hI.books hlq htq rfl ?_ (fun t ht => ?_)
      · show (nq.ks.map (wmgSwap o m1)).head? = nq.ks.head?
        rw [hr0]
        rfl
      · obtain ⟨k, hk, hkk⟩ := List.mem_map.mp ht
        have : k = SIS.Tree.Klong.time t := by
          cases k with
          | key c y => by_cases hy : y = o <;> simp [wmgSwap, hy] at hkk
          | time t' => simpa [wmgSwap] using hkk
          | del b => simp [wmgSwap] at hkk
        subst this
        exact hI.books.times q nq hlq t hk
    · intro m hm mn hBm hsm u0 nu c hBu hk hum hu0X
      rw [hR] at hm
      obtain ⟨mn0, hmn0⟩ := hobj m mn hBm
      obtain ⟨nu0, c0, hu0, hk0⟩ := hnm u0 nu c m hBu hk
      obtain ⟨h1, h2⟩ := hX m hm mn0 hmn0 hsm u0 nu0 c0 hu0 hk0 hum hu0X
      refine ⟨h1, fun u' nu' c' hBu' hk' hu'm hu'X => ?_⟩
      obtain ⟨nu0', c0', hu0', hk0'⟩ := hnm u' nu' c' m hBu' hk'
      exact h2 u' nu0' c0' hu0' hk0' hu'm hu'X
  · -- q names no o: the node is as it was
    have hno : ∀ c, Klong.key c o ∉ ksOf nq := fun c h => hex ⟨c, h⟩
    have hnq' : nq' = nq := by
      have e : ∀ l : List MKlong, (∀ c, SIS.Tree.Klong.key c o ∉ l) →
          l.map (wmgSwap o m1) = l := by
        intro l hl
        induction l with
        | nil => rfl
        | cons k l ih =>
          rw [List.map_cons, ih (fun c h => hl c (List.mem_cons_of_mem _ h))]
          congr 1
          cases k with
          | key c y =>
            have hy : y ≠ o := fun e => hl c (by rw [e]; exact List.mem_cons_self)
            simp [wmgSwap, hy]
          | time _ => rfl
          | del _ => rfl
      simp only [nq', e nq.ks (fun c h => hno c (ts_key_mem_ksOf h))]
    have hT : treeOf i s (u.withNode q nq') = treeOf i s u := by
      refine prim_tree_ext (fun y => ?_) rfl
      by_cases hyq : y = q
      · rw [hyq, hBq, hAq, hnq']
      · exact hsame y hyq
    have hR : reachOf i s (u.withNode q nq') = reachOf i s u := by unfold reachOf; rw [hT]; rfl
    have hbk : PutBooks p i base s (u.withNode q nq') := by
      rw [hnq']
      exact putBooks_withNode hI.books hlq htq rfl rfl (fun t ht => hI.books.times q nq hlq t ht)
    refine ⟨hI.of_map hT (by rw [dirtyOf_withNode hlq]; exact fun _ h => h) rfl rfl hbk, ?_,
      hsame, hR, hnone, by rw [hnq'], hwfimp⟩
    unfold WcrLinkX
    rw [hR, hT]
    exact hX


theorem wmg_swap_lastTime (nq : MNode) (o m1 : NodeId) :
    ({ nq with ks := nq.ks.map (wmgSwap o m1) } : MNode).lastTime = nq.lastTime := by
  unfold SIS.Tree.KNode.lastTime
  simp only
  rw [List.foldl_map]
  congr 1
  funext t k
  cases k with
  | key c y => by_cases hy : y = o <;> simp [wmgSwap, hy]
  | time _ => rfl
  | del _ => rfl

theorem wmg_swap_lti (nq : MNode) (o m1 : NodeId) :
    ({ nq with ks := nq.ks.map (wmgSwap o m1) } : MNode).lastTimeIndex = nq.lastTimeIndex := by
  unfold SIS.Tree.KNode.lastTimeIndex
  simp only
  rw [List.zipIdx_map, List.foldl_map]
  congr 1
  funext t ki
  obtain ⟨k, i⟩ := ki
  cases k with
  | key c y => by_cases hy : y = o <;> simp [wmgSwap, hy]
  | time _ => rfl
  | del _ => rfl

theorem wmg_swap_get {nq : MNode} {o m1 y : NodeId} (hyo : y ≠ o) (hym : y ≠ m1) (j c : Nat) :
    (nq.ks.map (wmgSwap o m1))[j]? = some (SIS.Tree.Klong.key c y) ↔
      nq.ks[j]? = some (SIS.Tree.Klong.key c y) := by
  rw [List.getElem?_map]
  cases h : nq.ks[j]? with
  | none => simp
  | some k =>
    cases k with
    | key c0 y0 =>
      by_cases h0 : y0 = o
      · subst h0
        simp only [Option.map_some, wmgSwap, ite_true, Option.some.injEq,
          SIS.Tree.Klong.key.injEq]
        constructor
        · rintro ⟨-, rfl⟩; exact absurd rfl hym
        · rintro ⟨-, rfl⟩; exact absurd rfl hyo
      · simp [wmgSwap, h0]
    | time _ => simp [wmgSwap]
    | del _ => simp [wmgSwap]

theorem wmg_swap_keymem {nq : MNode} {o m1 y : NodeId} (hyo : y ≠ o) (c : Nat) :
    Klong.key c y ∈ ksOf { nq with ks := nq.ks.map (wmgSwap o m1) } ↔
      Klong.key c y ∈ ksOf nq ∨ (y = m1 ∧ Klong.key c o ∈ ksOf nq) := by
  rw [wmg_ksOf_swap, List.mem_map]
  constructor
  · rintro ⟨k, hk, hkk⟩
    cases k with
    | key c0 y0 =>
      by_cases h0 : y0 = o
      · subst h0
        simp only [wmgSwapK, ite_true, Klong.key.injEq] at hkk
        exact Or.inr ⟨hkk.2.symm, by rw [← hkk.1]; exact hk⟩
      · simp only [wmgSwapK, h0, ite_false, Klong.key.injEq] at hkk
        exact Or.inl (by rw [← hkk.1, ← hkk.2]; exact hk)
    | time _ => simp [wmgSwapK] at hkk
    | del _ => simp [wmgSwapK] at hkk
  · rintro (h | ⟨rfl, h⟩)
    · exact ⟨_, h, by simp [wmgSwapK, hyo]⟩
    · exact ⟨_, h, by simp [wmgSwapK]⟩


/-- A node of the map has an id below the next. -/
theorem wmg_obj_lt {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top} {w : MW}
    (hb : Books i base s tp) (hk : PutBooks p i base s w) {y : NodeId} {o : Obj}
    (h : (treeOf i s w).obj y = some o) : y < w.next := by
  by_contra hy
  rw [(treeOf_fresh hb hk (Nat.le_of_not_lt hy)).1] at h
  cases h

/-- What the loop over the two nodes merged keeps: `PInv`; the link book but for the nodes still
to leave out (X); those are kept, not reached; a made one is named by q only, after q's last
time klong, by no live klong, and m1 is one level below q as it is. -/
structure WmgLoop (p : MParams) (i : Time) (base : NodeId) (s : Tree) (tp : Top)
    (C : List (Key × Nat)) (q m1 : NodeId) (u : MW) (X : List NodeId) : Prop where
  inv : PInv p i base s tp none C u
  link : WcrLinkX X i s u
  nodup : X.Nodup
  pend : ∀ o ∈ X, ∃ on, u.nodes.lookup o = some on ∧ u.taken.contains o = false ∧
    o ∉ reachOf i s u ∧ klongsWf (ksOf on) = true ∧ o ≠ q ∧ o ≠ m1
  named : ∀ o ∈ X, s.obj o = none → ∀ u0 nu c, (treeOf i s u).obj u0 = some (.key nu) →
    Klong.key c o ∈ nu.ks → u0 = q
  qn : ∃ nq, u.nodes.lookup q = some nq ∧ u.taken.contains q = false ∧ nq.leaf = false ∧
    ∀ o ∈ X, s.obj o = none →
      (∀ j c, nq.ks[j]? = some (.key c o) → nq.lastTime = some i ∧
        ∀ ti, nq.lastTimeIndex = some ti → ti < j) ∧
      (∀ c, (c, o) ∉ live (ksOf nq)) ∧
      (∀ c, Klong.key c o ∈ ksOf nq → klongsWf (ksOf nq) = true ∧ nq.size ≤ p.M ∧
        ∃ c', Klong.key c' m1 ∈ ksOf nq)
  lev : ∀ o ∈ X, s.obj o = none → ∃ nm1, (treeOf i s u).obj m1 = some (.key nm1) ∧
    ∀ no, (treeOf i s u).obj o = some (.key no) → nm1.level = no.level
  m1q : m1 ≠ q
  fresh : WmgFresh i s u


theorem wmg_linkX_congr {i : Time} {s : Tree} {X : List NodeId} {w w' : MW}
    (hT : treeOf i s w' = treeOf i s w) (hr : w'.top.rootKey = w.top.rootKey)
    (h : WcrLinkX X i s w) : WcrLinkX X i s w' := by
  have hR : reachOf i s w' = reachOf i s w := by unfold reachOf; rw [hT, hr]
  unfold WcrLinkX
  rw [hR, hT, hr]
  exact h

/-- The loop's invariant after its first node o is left out, from the state u1 after the
retarget (q's node nq1) and u2 after the take-back or cut back of o. -/
theorem wmg_loop_next {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {C : List (Key × Nat)} {q m1 : NodeId} {u u1 u2 : MW} {o : NodeId} {X : List NodeId}
    (hL : WmgLoop p i base s tp C q m1 u (o :: X)) {nq nq1 : MNode}
    (hlq : u.nodes.lookup q = some nq) (hlq1 : u1.nodes.lookup q = some nq1)
    (hl1 : nq1.leaf = nq.leaf) (hlv1 : live (ksOf nq1) = live (ksOf nq))
    (hwf1 : klongsWf (ksOf nq) = true → klongsWf (ksOf nq1) = true) (hsz1 : nq1.size = nq.size)
    (hlt1 : nq1.lastTime = nq.lastTime) (hti1 : nq1.lastTimeIndex = nq.lastTimeIndex)
    (hget1 : ∀ (j c : Nat) (y : NodeId), y ≠ o → y ≠ m1 →
      (nq1.ks[j]? = some (SIS.Tree.Klong.key c y) ↔ nq.ks[j]? = some (SIS.Tree.Klong.key c y)))
    (hmem1 : ∀ c y, y ≠ o → Klong.key c y ∈ ksOf nq1 → Klong.key c y ∈ ksOf nq ∨ y = m1)
    (hm1k : ∀ c, Klong.key c m1 ∈ ksOf nq → Klong.key c m1 ∈ ksOf nq1)
    (hk1 : ∀ z n, z ≠ q → u.nodes.lookup z = some n → u1.nodes.lookup z = some n)
    (hT1 : ∀ z, z ≠ q → (treeOf i s u1).obj z = (treeOf i s u).obj z)
    (htk1 : u1.taken = u.taken)
    (hI2 : PInv p i base s tp none C u2) (hX2 : WcrLinkX X i s u2) (hF2 : WmgFresh i s u2)
    (hT2 : ∀ z, z ≠ o → (treeOf i s u2).obj z = (treeOf i s u1).obj z)
    (h2o : ∀ no, (treeOf i s u2).obj o = some (.key no) → ∀ c y, Klong.key c y ∈ no.ks →
      (s.obj y).isSome = true)
    (hR2 : reachOf i s u2 = reachOf i s u)
    (hk2 : ∀ z n, z ≠ o → u1.nodes.lookup z = some n → u2.nodes.lookup z = some n)
    (htk2 : ∀ z, z ≠ o → u2.taken.contains z = u1.taken.contains z) :
    WmgLoop p i base s tp C q m1 u2 X := by
  have hnd := List.nodup_cons.mp hL.nodup
  have hsub : ∀ o' ∈ X, o' ∈ o :: X := fun o' h => List.mem_cons_of_mem _ h
  have hne : ∀ o' ∈ X, o' ≠ o := fun o' h e => hnd.1 (e ▸ h)
  obtain ⟨nq0, hlq0, htq, hql, hqX⟩ := hL.qn
  rw [hlq] at hlq0
  cases hlq0
  obtain ⟨-, -, -, -, -, hoq, hom1⟩ := hL.pend o List.mem_cons_self
  refine ⟨hI2, hX2, hnd.2, fun o' ho' => ?_, fun o' ho' hso' u0 nu c hu0 hk => ?_, ?_,
    fun o' ho' hso' => ?_, hL.m1q, hF2⟩
  · obtain ⟨on, h1, h2, h3, h4, h5, h6⟩ := hL.pend o' (hsub o' ho')
    refine ⟨on, hk2 o' on (hne o' ho') (hk1 o' on h5 h1), ?_, by rw [hR2]; exact h3, h4, h5, h6⟩
    rw [htk2 o' (hne o' ho'), htk1]
    exact h2
  · by_cases hu0q : u0 = q
    · exact hu0q
    · have hu0o : u0 ≠ o := by
        intro e
        rw [e] at hu0
        have := h2o nu hu0 c o' hk
        rw [hso'] at this
        cases this
      rw [hT2 u0 hu0o, hT1 u0 hu0q] at hu0
      exact hL.named o' (hsub o' ho') hso' u0 nu c hu0 hk
  · refine ⟨nq1, hk2 q nq1 (fun e => hoq e.symm) hlq1, ?_, by rw [hl1]; exact hql,
      fun o' ho' hso' => ?_⟩
    · rw [htk2 q (fun e => hoq e.symm), htk1]
      exact htq
    · obtain ⟨on', -, -, -, -, -, ho'm1⟩ := hL.pend o' (hsub o' ho')
      obtain ⟨h1, h2, h3⟩ := hqX o' (hsub o' ho') hso'
      refine ⟨fun j c hj => ?_, by rw [hlv1]; exact h2, fun c hc => ?_⟩
      · obtain ⟨h4, h5⟩ := h1 j c ((hget1 j c o' (hne o' ho') ho'm1).mp hj)
        exact ⟨by rw [hlt1]; exact h4, fun ti hti => h5 ti (by rw [← hti1]; exact hti)⟩
      · rcases hmem1 c o' (hne o' ho') hc with hc' | hc'
        · obtain ⟨h4, h5, c', h6⟩ := h3 c hc'
          exact ⟨hwf1 h4, by rw [hsz1]; exact h5, c', hm1k c' h6⟩
        · exact absurd hc' ho'm1
  · obtain ⟨nm1, hm1, hlev⟩ := hL.lev o' (hsub o' ho') hso'
    obtain ⟨-, -, -, -, -, ho'q, -⟩ := hL.pend o' (hsub o' ho')
    refine ⟨nm1, ?_, fun no hno => hlev no ?_⟩
    · rw [hT2 m1 (fun e => hom1 e.symm), hT1 m1 hL.m1q]
      exact hm1
    · rw [hT2 o' (hne o' ho'), hT1 o' ho'q] at hno
      exact hno

/-- One node of the loop, the first of X: a node of before cut back, a node made taken back. -/
theorem wmg_loop_step {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} (hb : Books i base s tp) (hsn : SNamed s) {C : List (Key × Nat)}
    {q m1 : NodeId} {u : MW} {o : NodeId} {X : List NodeId}
    (hL : WmgLoop p i base s tp C q m1 u (o :: X)) (made : Bool)
    (hmade : made = true ↔ s.obj o = none) :
    WP (if made = true then (do
          SIS.Tree.retarget q o m1
          SIS.Tree.takenBack o
          SIS.Tree.note "merge.takeback"
          pure (ForInStep.yield PUnit.unit))
        else (do
          SIS.Tree.unlink o
          pure (ForInStep.yield PUnit.unit)))
      { p := p, i := i, view := v } u
      (fun r u' => r = ForInStep.yield PUnit.unit ∧ WmgLoop p i base s tp C q m1 u' X) := by
  have hmem : o ∈ o :: X := List.mem_cons_self
  obtain ⟨on, hlo, hto, hoR, hwfo, hoq, hom1⟩ := hL.pend o hmem
  have hnd := List.nodup_cons.mp hL.nodup
  obtain ⟨nq, hlq, htq, hql, hqX⟩ := hL.qn
  have hsub : ∀ o' ∈ X, o' ∈ o :: X := fun o' h => List.mem_cons_of_mem _ h
  refine wp_ite _ _ _ _ _ _ (fun hm => ?_) (fun hm => ?_)
  · -- made by the transaction: taken back
    have hso : s.obj o = none := hmade.mp hm
    obtain ⟨hafter, hlive, hqn⟩ := hqX o hmem hso
    obtain ⟨nm1, hm1, hm1lev⟩ := hL.lev o hmem hso
    have hnamers := hL.named o hmem hso
    rw [wp_bind]
    refine (wmg_retarget hlq hafter).mono ?_
    rintro _ u1 hu1
    refine wput_ok rfl ?_
    refine wput_ok (note_eq _ _ _) ?_
    rw [wp_pure]
    refine ⟨rfl, ?_⟩
    have herase : (o :: X).erase o = X := List.erase_cons_head o X
    rcases hu1 with ⟨hu1, hno⟩ | hu1
    · subst u1
      have hnone : ∀ u0 nu c, (treeOf i s u).obj u0 = some (.key nu) → Klong.key c o ∉ nu.ks := by
        intro u0 nu c hu0 hk
        have hq := hnamers u0 nu c hu0 hk
        subst hq
        rw [treeOf_obj_overlay i s hlq htq] at hu0
        cases hu0
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hk
        exact hno j c (wmg_ks_model.mp hj)
      obtain ⟨hI2, hX2, hobj2, hR2⟩ := wmg_drop hL.inv hL.link hlo hoR hso hnone
      rw [herase] at hX2
      refine wmg_loop_next hL hlq hlq rfl rfl id rfl rfl rfl (fun _ _ _ _ _ => Iff.rfl)
        (fun c y _ h => Or.inl h) (fun c h => h) (fun _ _ _ h => h) (fun _ _ => rfl) rfl
        (hI2.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl)
        (wmg_linkX_congr (treeOf_congr i s rfl rfl rfl rfl rfl rfl) rfl hX2)
        (fun u0 nu c y h hk => by
          have h' : (treeOf i s { u with taken := o :: u.taken }).obj u0 = some (.key nu) := h
          rw [hobj2] at h'
          split at h'
          · cases h'
          · exact hL.fresh u0 nu c y h' hk)
        (fun z hz => by
          show (treeOf i s { u with taken := o :: u.taken }).obj z = _
          rw [hobj2]; simp [hz])
        (fun no hno' => by
          have e : (treeOf i s { u with taken := o :: u.taken }).obj o = none := by
            rw [hobj2]; simp
          exact absurd (hno'.symm.trans e) (by simp))
        (by rw [← hR2]; exact (wmg_reach_eq rfl (fun _ _ => rfl)))
        (fun _ _ _ h => h)
        (fun z hz => by
          show (o :: u.taken).contains z = u.taken.contains z
          simp [hz])
    · subst u1
      set nqS : MNode := { nq with ks := nq.ks.map (wmgSwap o m1) }
      obtain ⟨hI1, hX1, hsame1, hR1, hnone1, hlv1, hwf1⟩ := wmg_swap_state hsn hL.inv hL.link hlq
        htq hql hso (fun e => hom1 e.symm) hnamers hlive hqn hm1 hm1lev
      have hlo1 : (u.withNode q nqS).nodes.lookup o = some on := by
        rw [MW.withNode, lookup_upsert_ne _ _ hoq]; exact hlo
      obtain ⟨hI2, hX2, hobj2, hR2⟩ := wmg_drop hI1 hX1 hlo1 (by rw [hR1]; exact hoR) hso hnone1
      rw [herase] at hX2
      refine wmg_loop_next (nq1 := nqS) hL hlq (lookup_upsert_self _ _ _) rfl hlv1 hwf1
        (by simp [nqS, SIS.Tree.KNode.size]) (wmg_swap_lastTime nq o m1) (wmg_swap_lti nq o m1)
        (fun j c y hyo hym => wmg_swap_get hyo hym j c)
        (fun c y hyo h => by
          rcases (wmg_swap_keymem hyo c).mp h with h1 | ⟨h1, -⟩
          · exact Or.inl h1
          · exact Or.inr h1)
        (fun c h => (wmg_swap_keymem (fun e => hom1 e.symm) c).mpr (Or.inl h))
        (fun z n hz h => by rw [MW.withNode, lookup_upsert_ne _ _ hz]; exact h) hsame1 rfl
        (hI2.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl)
        (wmg_linkX_congr (treeOf_congr i s rfl rfl rfl rfl rfl rfl) rfl hX2)
        (fun u0 nu c y h hk => by
          have h' : (treeOf i s { u.withNode q nqS with
              taken := o :: (u.withNode q nqS).taken }).obj u0 = some (.key nu) := h
          rw [hobj2] at h'
          split at h'
          · cases h'
          · by_cases hu0 : u0 = q
            · subst hu0
              rcases em (y = o) with hyo | hyo
              · exact absurd (hyo ▸ hk) (hnone1 u0 nu c h')
              · rw [treeOf_withNode i s nqS htq] at h'
                simp only [Tree.set, ite_true, Option.some.injEq, Obj.key.injEq] at h'
                rw [← h'] at hk
                rcases (wmg_swap_keymem hyo c).mp hk with h1 | ⟨rfl, -⟩
                · exact hL.fresh u0 _ c y (treeOf_obj_overlay i s hlq htq) h1
                · exact wmg_obj_lt hb hL.inv.books hm1
            · rw [hsame1 u0 hu0] at h'
              exact hL.fresh u0 nu c y h' hk)
        (fun z hz => by
          show (treeOf i s { u.withNode q nqS with taken := o ::
              (u.withNode q nqS).taken }).obj z = _
          rw [hobj2]; simp [hz])
        (fun no hno' => by
          have e : (treeOf i s { u.withNode q nqS with
              taken := o :: (u.withNode q nqS).taken }).obj o = none := by
            rw [hobj2]; simp
          exact absurd (hno'.symm.trans e) (by simp))
        (by rw [← hR1, ← hR2]; exact (wmg_reach_eq rfl (fun _ _ => rfl)))
        (fun _ _ _ h => h)
        (fun z hz => by
          show (o :: (u.withNode q nqS).taken).contains z = (u.withNode q nqS).taken.contains z
          simp [hz])
  · -- a node of before: cut back
    have hso : (s.obj o).isSome = true := by
      cases h : s.obj o with
      | none => exact absurd (hmade.mpr h) hm
      | some _ => rfl
    obtain ⟨ob, hob⟩ := Option.isSome_iff_exists.mp hso
    obtain ⟨ob', hob', hext, -⟩ := hL.inv.frame.1 o ob hob
    rw [treeOf_obj_overlay i s hlo hto] at hob'
    cases hob'
    cases ob with
    | val h => exact absurd hext (by simp [Ext])
    | key n0 =>
    rw [wp_bind]
    refine (wmg_unlink hb hsn hL.inv hL.link hlo hto hoR hwfo hob).mono ?_
    rintro _ u2 ⟨hI2, hX2, hsame2, hk2, htk2, htop2, hp2, hout2, hn2, hmade2, hR2, ho2⟩
    rw [wp_pure]
    refine ⟨rfl, ?_⟩
    rw [List.erase_cons_head] at hX2
    exact wmg_loop_next hL hlq hlq rfl rfl id rfl rfl rfl (fun _ _ _ _ _ => Iff.rfl)
      (fun c y _ h => Or.inl h) (fun c h => h) (fun _ _ _ h => h) (fun _ _ => rfl) rfl hI2 hX2
      (fun u0 nu c y h hk => by
        by_cases hu0 : u0 = o
        · subst hu0
          have hsy := ho2 nu h c y hk
          obtain ⟨-, -, -, hbase, -⟩ := hL.inv.books.ids
          have hb2 : base ≤ u2.next := by rw [hn2]; exact hbase
          by_contra hy
          have := (hb.ids y (le_trans hb2 (Nat.le_of_not_lt hy))).1
          rw [this] at hsy
          cases hsy
        · rw [hsame2 u0 hu0] at h
          rw [hn2]
          exact hL.fresh u0 nu c y h hk)
      hsame2 ho2 hR2 (fun z n hz h => hk2 z n hz h) (fun z _ => by rw [htk2])



/-- The loop over the two nodes merged. -/
theorem wmg_loop {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} (hb : Books i base s tp) (hsn : SNamed s) {C : List (Key × Nat)}
    {q m1 : NodeId} {u : MW} {l r : NodeId} (hL : WmgLoop p i base s tp C q m1 u [l, r])
    (lMade rMade : Bool) (hlm : lMade = true ↔ s.obj l = none)
    (hrm : rMade = true ↔ s.obj r = none) :
    WP (forIn [(l, lMade), (r, rMade)] PUnit.unit (fun x _ =>
        if x.2 = true then (do
          SIS.Tree.retarget q x.1 m1
          SIS.Tree.takenBack x.1
          SIS.Tree.note "merge.takeback"
          pure (ForInStep.yield PUnit.unit))
        else (do
          SIS.Tree.unlink x.1
          pure (ForInStep.yield PUnit.unit))))
      { p := p, i := i, view := v } u
      (fun _ u' => WmgLoop p i base s tp C q m1 u' []) := by
  rw [List.forIn_cons, wp_bind]
  refine (wmg_loop_step (v := v) hb hsn hL lMade hlm).mono ?_
  rintro _ u1 ⟨rfl, hL1⟩
  dsimp only
  rw [List.forIn_cons, wp_bind]
  refine (wmg_loop_step (v := v) hb hsn hL1 rMade hrm).mono ?_
  rintro _ u2 ⟨rfl, hL2⟩
  dsimp only
  rw [List.forIn_nil, wp_pure]
  exact hL2

/-! ## The parent's live klongs, for the tree rules -/

/-- Two adjacent live klongs split the live klongs. -/
theorem wmg_split2 {L : List (Nat × NodeId)} (hs : L.Pairwise CvLt) {cL cR : Nat} {l r : NodeId}
    (hl : (cL, l) ∈ L) (hr : (cR, r) ∈ L) (hlt : cL < cR)
    (hadj : ∀ c y, (c, y) ∈ L → c ≤ cL ∨ cR ≤ c) :
    ∃ pre post, L = pre ++ (cL, l) :: (cR, r) :: post := by
  obtain ⟨pre, post', y1, hpre, hpost', hL, -⟩ := wmp_insertCv_at hs hl l
  have hy1 : y1 = l := by
    have h1 : (cL, y1) ∈ L := by rw [hL]; simp
    exact (Prod.mk.inj (sorted_unique hs h1 hl rfl)).2
  subst hy1
  have hr' : (cR, r) ∈ post' := by
    rw [hL] at hr
    rcases List.mem_append.mp hr with h | h
    · have := hpre _ h; simp at this; omega
    · rcases List.mem_cons.mp h with h | h
      · simp at h; omega
      · exact h
  obtain ⟨s1, t, hst⟩ := List.append_of_mem hr'
  have hs1 : s1 = [] := by
    rcases s1 with _ | ⟨a, s1⟩
    · rfl
    · exfalso
      have haL : a ∈ L := by rw [hL, hst]; simp
      have ha1 : cL < a.1 := hpost' a (by rw [hst]; simp)
      have hsorted : (a :: s1 ++ (cR, r) :: t).Pairwise CvLt := by
        rw [← hst]
        rw [hL] at hs
        exact (List.pairwise_append.mp hs).2.1.of_cons
      have ha2 : a.1 < cR := by
        have := (List.pairwise_cons.mp hsorted).1 (cR, r) (by simp)
        exact this
      rcases hadj a.1 a.2 haL with h | h <;> omega
  subst hs1
  exact ⟨pre, t, by rw [hL, hst]; rfl⟩

/-- The subtrees of two live klongs of a node, in a tree whose walk from the node visits each
node once, are disjoint. -/
theorem wmg_kids_disj {A : Tree} {q : NodeId} {nq : KNode} (hAq : A.obj q = some (.key nq))
    (hT : (reachAt A (A.fuel q) q).Nodup) {a b : Nat × NodeId} (ha : a ∈ live nq.ks)
    (hb : b ∈ live nq.ks) (hab : a ≠ b) :
    ∀ z ∈ reachAt A nq.level a.2, z ∉ reachAt A nq.level b.2 := by
  rw [show A.fuel q = nq.level + 1 by simp [Tree.fuel, hAq], tc_key hAq] at hT
  have hfm := (List.nodup_cons.mp hT).2
  rw [List.nodup_flatMap] at hfm
  have : Std.Symm (Function.onFun List.Disjoint
      (fun cy : Nat × NodeId => reachAt A nq.level cy.2)) :=
    ⟨fun _ _ h => List.Disjoint.symm h⟩
  have hd := hfm.2.forall ha hb hab
  intro z hz hz'
  exact hd hz hz'

/-- A node is named by one live klong of a node at most, in such a tree. -/
theorem wmg_kid_once {A : Tree} {q : NodeId} {nq : KNode} (hAq : A.obj q = some (.key nq))
    (hT : (reachAt A (A.fuel q) q).Nodup) {c1 c2 : Nat} {y : NodeId}
    (h1 : (c1, y) ∈ live nq.ks) (h2 : (c2, y) ∈ live nq.ks) : c1 = c2 := by
  by_contra hc
  exact wmg_kids_disj hAq hT h1 h2 (fun e => hc (Prod.mk.inj e).1) y (tc_self _ _ _)
    (tc_self _ _ _)

/-- Two live klongs of a node name two nodes, in such a tree. -/
theorem wmg_kids_ne {A : Tree} {q : NodeId} {nq : KNode} (hAq : A.obj q = some (.key nq))
    (hT : (reachAt A (A.fuel q) q).Nodup) {c1 c2 : Nat} {y1 y2 : NodeId}
    (h1 : (c1, y1) ∈ live nq.ks) (h2 : (c2, y2) ∈ live nq.ks) (hc : c1 ≠ c2) : y1 ≠ y2 := by
  intro e
  subst e
  exact hc (wmg_kid_once hAq hT h1 h2)

/-! ## The parent's node with the pointers set: its klongs of before -/

/-- The parent's node n on the way from pn (`mergeParent`), when pn's last time is i: its key
klongs but those naming m1 or m2 and its time klongs are pn's at their places. -/
structure WmgPos (i : Time) (pn n : MNode) (m1 : NodeId) (m2 : Option (NodeId × Nat)) :
    Prop where
  key : ∀ (j c : Nat) (y : NodeId), n.ks[j]? = some (SIS.Tree.Klong.key c y) → y ≠ m1 →
    (∀ g, m2 ≠ some (y, g)) → pn.ks[j]? = some (SIS.Tree.Klong.key c y)
  time : ∀ (j t : Nat), n.ks[j]? = some (SIS.Tree.Klong.time t) →
    pn.ks[j]? = some (SIS.Tree.Klong.time t)
  last : n.lastTime = some i

theorem wmg_pos_self {i : Time} {pn : MNode} (h : pn.lastTime = some i) (m1 : NodeId)
    (m2 : Option (NodeId × Nat)) : WmgPos i pn pn m1 m2 :=
  ⟨fun _ _ _ h _ _ => h, fun _ _ h => h, h⟩

theorem wmg_pos_add {i : Time} {pn n : MNode} {m1 : NodeId} {m2 : Option (NodeId × Nat)}
    (hP : WmgPos i pn n m1 m2) {k : MKlong} (hk : ∀ t, k ≠ .time t)
    (hkey : ∀ c y, k = .key c y → y = m1 ∨ ∃ g, m2 = some (y, g)) :
    WmgPos i pn (n.add i k) m1 m2 := by
  have hks : (n.add i k).ks = n.ks ++ [k] := by
    rcases add_ks n i k with ⟨_, h1⟩ | ⟨h, -⟩
    · exact absurd (h1 i hP.last) (Nat.lt_irrefl _)
    · exact h
  have hget : ∀ (j : Nat) (kk : MKlong), (n.add i k).ks[j]? = some kk →
      n.ks[j]? = some kk ∨ (j = n.ks.length ∧ kk = k) := by
    intro j kk hj
    rw [hks] at hj
    rcases Nat.lt_or_ge j n.ks.length with h1 | h1
    · left; rw [List.getElem?_append_left h1] at hj; exact hj
    · right
      rw [List.getElem?_append_right h1] at hj
      have h2 : j - n.ks.length = 0 := by
        by_contra hne
        rw [List.getElem?_eq_none (by simp; omega)] at hj
        cases hj
      rw [h2] at hj
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      exact ⟨by omega, hj.symm⟩
  refine ⟨fun j c y hj hy1 hy2 => ?_, fun j t hj => ?_, ?_⟩
  · rcases hget j _ hj with h | ⟨-, rfl⟩
    · exact hP.key j c y h hy1 hy2
    · rcases hkey c y rfl with h | ⟨g, h⟩
      · exact absurd h hy1
      · exact absurd h (hy2 g)
  · rcases hget j _ hj with h | ⟨-, rfl⟩
    · exact hP.time j t h
    · exact absurd rfl (hk t)
  · rw [← lastT_ksOf, show ksOf (n.add i k) = ksOf n ++ [kOf k] by simp [ksOf, hks]]
    unfold lastT
    rw [List.foldl_append]
    have : (ksOf n).foldl lastStep none = some i := by rw [← hP.last, ← lastT_ksOf]; rfl
    rw [this]
    cases k with
    | time t => exact absurd rfl (hk t)
    | key c y => rfl
    | del b => rfl

theorem wmg_pos_setDel {i : Time} {pn n : MNode} {m1 : NodeId} {m2 : Option (NodeId × Nat)}
    (hP : WmgPos i pn n m1 m2) (ht : hasTransDel n i = true) (u : List Nat) :
    WmgPos i pn (n.setAt (n.size - 1) (.del u)) m1 m2 := by
  obtain ⟨ks0, B, hks, -⟩ := hasTransDel_ks ht
  have h2 := setAt_last hks (.del u)
  have hget : ∀ (j : Nat) (kk : MKlong), (n.setAt (n.size - 1) (.del u)).ks[j]? = some kk →
      (∀ b, kk ≠ SIS.Tree.Klong.del b) → n.ks[j]? = some kk := by
    intro j kk hj hkk
    rw [h2] at hj
    rw [hks]
    rcases Nat.lt_or_ge j ks0.length with h1 | h1
    · rw [List.getElem?_append_left h1] at hj ⊢; exact hj
    · rw [List.getElem?_append_right h1] at hj
      have h3 : j - ks0.length = 0 := by
        by_contra hne
        rw [List.getElem?_eq_none (by simp; omega)] at hj
        cases hj
      rw [h3] at hj
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      exact absurd hj.symm (hkk u)
  refine ⟨fun j c y hj hy1 hy2 => hP.key j c y (hget j _ hj (fun b e => by cases e)) hy1 hy2,
    fun j t hj => hP.time j t (hget j _ hj (fun b e => by cases e)), ?_⟩
  rw [wmp_setDel_last ht]
  exact hP.last

theorem wmg_pos_repoint {i : Time} {pn n : MNode} {m1 : NodeId} {m2 : Option (NodeId × Nat)}
    (hP : WmgPos i pn n m1 m2) (j0 : Nat) {y' : NodeId}
    (hy' : y' = m1 ∨ ∃ g, m2 = some (y', g)) : WmgPos i pn (n.repoint j0 y') m1 m2 := by
  cases hj0 : n.ks[j0]? with
  | none =>
    have e : n.repoint j0 y' = n := by unfold SIS.Tree.KNode.repoint; rw [hj0]
    rw [e]; exact hP
  | some k0 =>
    cases k0 with
    | time t =>
      have e : n.repoint j0 y' = n := by unfold SIS.Tree.KNode.repoint; rw [hj0]
      rw [e]; exact hP
    | del bs =>
      have e : n.repoint j0 y' = n := by unfold SIS.Tree.KNode.repoint; rw [hj0]
      rw [e]; exact hP
    | key c0 y0 =>
    have hks : (n.repoint j0 y').ks = n.ks.set j0 (.key c0 y') := by
      unfold SIS.Tree.KNode.repoint
      rw [hj0]
      rfl
    refine ⟨fun j c y hj hy1 hy2 => ?_, fun j t hj => ?_, ?_⟩
    · rw [hks, List.getElem?_set] at hj
      split at hj
      · split at hj
        · simp only [Option.some.injEq, SIS.Tree.Klong.key.injEq] at hj
          rcases hy' with h | ⟨g, h⟩
          · exact absurd (hj.2 ▸ h) hy1
          · exact absurd (hj.2 ▸ h) (hy2 g)
        · cases hj
      · exact hP.key j c y hj hy1 hy2
    · rw [hks, List.getElem?_set] at hj
      split at hj
      · split at hj
        · simp at hj
        · cases hj
      · exact hP.time j t hj
    · rw [wmp_repoint_last hj0]
      exact hP.last

/-- The parent's node with the pointers set (`mergeParent`'s n3), when the parent's last time
is i. -/
theorem wmg_pos_n3 {i : Time} {pn : MNode} (h : pn.lastTime = some i) (il cL : Nat)
    (m1 : NodeId) (ir cR : Nat) (m2 : Option (NodeId × Nat)) :
    WmgPos i pn (wmp_n3 i pn il cL m1 ir cR m2) m1 m2 := by
  have h1 : WmgPos i pn (wmp_n1 i pn cR m2) m1 m2 := by
    unfold wmp_n1
    split
    · exact wmg_pos_self h m1 m2
    · split
      · exact wmg_pos_setDel (wmg_pos_self h m1 m2) (by assumption) _
      · exact wmg_pos_add (wmg_pos_self h m1 m2) (fun t e => by cases e) (fun c y e => by cases e)
  have h2 : WmgPos i pn (wmp_n2 i pn il cL m1 cR m2) m1 m2 := by
    unfold wmp_n2
    split
    · exact wmg_pos_repoint h1 il (Or.inl rfl)
    · exact wmg_pos_add h1 (fun t e => by cases e) (fun c y e => by cases e; exact Or.inl rfl)
  unfold wmp_n3
  split
  · rename_i y g
    split
    · exact wmg_pos_repoint h2 ir (Or.inr ⟨g, rfl⟩)
    · exact wmg_pos_add h2 (fun t e => by cases e) (fun c y' e => by cases e; exact Or.inr ⟨g, rfl⟩)
  · exact h2

/-- A klong of the parent's node with the pointers set that names o comes after its last time
klong, if in pn a time klong of i comes before every klong naming o. -/
theorem wmg_after {i : Time} {pn n : MNode} {m1 o : NodeId} {m2 : Option (NodeId × Nat)}
    (hP : WmgPos i pn n m1 m2) (hwf : klongsWf (ksOf pn) = true) (hT : TimesLe pn i)
    (hom1 : o ≠ m1) (hom2 : ∀ g, m2 ≠ some (o, g)) {a : Nat}
    (ha : pn.ks[a]? = some (.time i)) (hbefore : ∀ j c, pn.ks[j]? = some (.key c o) → a < j)
    {j c : Nat} (hj : n.ks[j]? = some (.key c o)) :
    n.lastTime = some i ∧ ∀ ti, n.lastTimeIndex = some ti → ti < j := by
  refine ⟨hP.last, fun ti hti => ?_⟩
  have hjp := hP.key j c o hj hom1 hom2
  have haj := hbefore j c hjp
  obtain ⟨t, ht⟩ := wmg_lti_time hti
  have hpt := hP.time ti t ht
  by_contra hle
  have hlt : a < ti := by
    rcases Nat.lt_or_ge j ti with h | h
    · omega
    · have : ti = j := by omega
      subst this
      rw [hjp] at hpt
      cases hpt
  simp only [klongsWf, Bool.and_eq_true] at hwf
  exact wmg_no_time_after hwf.1 hT (by rw [ksOf_getElem?, ha]; rfl) hlt t
    (by rw [ksOf_getElem?, hpt]; rfl)

/-- In a node of the overlay that names a node the transaction made, a time klong of i comes
before every klong naming it, and its last time is i. -/
theorem wmg_time_before {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {w : MW} {C : List (Key × Nat)} (hI : PInv p i base s tp none C w) (hsn : SNamed s)
    {q : NodeId} {pn : MNode} (hlq : w.nodes.lookup q = some pn)
    (htq : w.taken.contains q = false) (hwf : klongsWf (ksOf pn) = true) {o : NodeId}
    (hso : s.obj o = none) {j0 c0 : Nat} (hj0 : pn.ks[j0]? = some (.key c0 o)) :
    (∃ a : Nat, pn.ks[a]? = some (SIS.Tree.Klong.time i) ∧
      ∀ (j c : Nat), pn.ks[j]? = some (SIS.Tree.Klong.key c o) → a < j) ∧
      pn.lastTime = some i := by
  have hT := wput_timesLe hI.books hlq
  have hpos : ∃ a : Nat, pn.ks[a]? = some (SIS.Tree.Klong.time i) ∧
      ∀ (j c : Nat), pn.ks[j]? = some (SIS.Tree.Klong.key c o) → a < j := by
    cases hsq : s.obj q with
    | none =>
      have hf := hI.books.first q pn hlq htq
      rw [hsq] at hf
      have hfi : pn.firstTime = some i := by simpa using hf
      obtain ⟨t0, rest, hr0⟩ := hI.books.timeFirst q pn hlq htq
      rw [firstTime_eq hr0] at hfi
      cases hfi
      refine ⟨0, by rw [hr0]; rfl, fun j c hj => ?_⟩
      rcases Nat.eq_zero_or_pos j with rfl | h
      · rw [hr0] at hj; cases hj
      · exact h
    | some ob =>
      obtain ⟨ob', hob', hext, -⟩ := hI.frame.1 q ob hsq
      rw [treeOf_obj_overlay i s hlq htq] at hob'
      cases hob'
      cases ob with
      | val v => exact absurd hext (by simp [Ext])
      | key n0 =>
      obtain ⟨-, -, he⟩ := frame_overlay_ext hI.frame hlq htq hsq
      have hn0 : ∀ c, Klong.key c o ∉ n0.ks := by
        intro c h
        have := hsn q n0 hsq c o h
        rw [hso] at this
        cases this
      rcases he with he | ⟨more, he⟩
      · exfalso
        have : Klong.key c0 o ∈ ksOf pn := List.mem_of_getElem? (wmg_ks_model.mpr hj0)
        rw [he] at this
        exact hn0 c0 this
      · refine ⟨n0.ks.length, ?_, fun j c hj => ?_⟩
        · have h1 : (ksOf pn)[n0.ks.length]? = some (Klong.time i) := by
            rw [he, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl
          rw [ksOf_getElem?] at h1
          obtain ⟨k, hk, hkk⟩ := Option.map_eq_some_iff.mp h1
          rw [hk, kOf_eq_time hkk]
        · have hj' := wmg_ks_model.mpr hj
          rw [he] at hj'
          by_contra hle
          rcases Nat.lt_or_ge j n0.ks.length with h1 | h1
          · rw [List.getElem?_append_left h1] at hj'
            exact hn0 c (List.mem_of_getElem? hj')
          · have : j = n0.ks.length := by omega
            subst this
            rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at hj'
            cases hj'
  refine ⟨hpos, ?_⟩
  obtain ⟨a, ha, -⟩ := hpos
  have ha' : (ksOf pn)[a]? = some (Klong.time i) := by rw [ksOf_getElem?, ha]; rfl
  have hlt : a < (ksOf pn).length := (List.getElem?_eq_some_iff.mp ha').1
  have hsplit : ksOf pn = (ksOf pn).take a ++ Klong.time i :: (ksOf pn).drop (a + 1) := by
    conv_lhs => rw [← List.take_append_drop a (ksOf pn)]
    rw [List.drop_eq_getElem_cons hlt, (List.getElem?_eq_some_iff.mp ha').2]
  have hw := hwf
  simp only [klongsWf, Bool.and_eq_true] at hw
  have hw1 := hw.1
  rw [hsplit] at hw1
  rw [← lastT_ksOf, hsplit]
  refine wcr_lastT_ext hw1 (fun t ht => hT t ?_)
  rw [hsplit]
  exact List.mem_append_right _ (List.mem_cons_of_mem _ ht)

/-- In the room case, the parent's node with the pointers set names a node o the transaction
made, other than m1 and m2, only after its last time klong (what `retarget` asks). -/
theorem wmg_after_n3 {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {w : MW} {C : List (Key × Nat)} (hI : PInv p i base s tp none C w) (hsn : SNamed s)
    {q : NodeId} {pn : MNode} (hlq : w.nodes.lookup q = some pn)
    (htq : w.taken.contains q = false) (hwf : klongsWf (ksOf pn) = true)
    {il cL ir cR : Nat} {m1 : NodeId} {m2 : Option (NodeId × Nat)}
    {L' : List (Nat × NodeId)} {sz : Nat}
    (hN3 : WmpNode i s q pn m1 m2 (wmp_n3 i pn il cL m1 ir cR m2) L' sz)
    {o : NodeId} (hso : s.obj o = none) (hom1 : o ≠ m1) (hom2 : ∀ g, m2 ≠ some (o, g))
    {j c : Nat} (hj : (wmp_n3 i pn il cL m1 ir cR m2).ks[j]? = some (.key c o)) :
    (wmp_n3 i pn il cL m1 ir cR m2).lastTime = some i ∧
      ∀ ti, (wmp_n3 i pn il cL m1 ir cR m2).lastTimeIndex = some ti → ti < j := by
  have hk : Klong.key c o ∈ ksOf (wmp_n3 i pn il cL m1 ir cR m2) :=
    List.mem_of_getElem? (wmg_ks_model.mpr hj)
  rcases hN3.keys c o hk with ⟨c', hc'⟩ | h | ⟨g, h⟩
  · obtain ⟨j0, hj0⟩ := List.mem_iff_getElem?.mp hc'
    obtain ⟨⟨a, ha, hbefore⟩, hlast⟩ :=
      wmg_time_before hI hsn hlq htq hwf hso (wmg_ks_model.mp hj0)
    exact wmg_after (wmg_pos_n3 hlast il cL m1 ir cR m2) hwf (wput_timesLe hI.books hlq) hom1
      hom2 ha hbefore hj
  · exact absurd h hom1
  · exact absurd h (hom2 g)

/-- A klong of the merge's target: m1, m2, or a live klong of the parent but cL's and cR's. -/
theorem wmg_target_mem {L : List (Nat × NodeId)} (hs : L.Pairwise CvLt) {cL cR c : Nat}
    {m1 y : NodeId} {m2 : Option (NodeId × Nat)} (h : (c, y) ∈ mergeTarget L cL cR m1 m2) :
    y = m1 ∨ (∃ g, m2 = some (y, g)) ∨ ((c, y) ∈ L ∧ c ≠ cL ∧ c ≠ cR) := by
  have hD := dropCv_sorted cR hs
  cases m2 with
  | none =>
    rcases (mem_insertCv_iff hD).mp h with h1 | ⟨h1, h2⟩
    · exact Or.inl (Prod.mk.inj h1).2
    · obtain ⟨h3, h4⟩ := mem_dropCv.mp h1
      exact Or.inr (Or.inr ⟨h3, h2, h4⟩)
  | some yg =>
    obtain ⟨y2, g⟩ := yg
    by_cases hgc : g = cR
    · subst hgc
      simp only [mergeTarget, ite_true] at h
      rcases (mem_insertCv_iff (insertCv_sorted _ _ hs)).mp h with h1 | ⟨h1, h2⟩
      · exact Or.inr (Or.inl ⟨g, by rw [(Prod.mk.inj h1).2]⟩)
      · rcases (mem_insertCv_iff hs).mp h1 with h3 | ⟨h3, h4⟩
        · exact Or.inl (Prod.mk.inj h3).2
        · exact Or.inr (Or.inr ⟨h3, h4, h2⟩)
    · simp only [mergeTarget, hgc, ite_false] at h
      rcases (mem_insertCv_iff (insertCv_sorted _ _ hD)).mp h with h1 | ⟨h1, -⟩
      · exact Or.inr (Or.inl ⟨g, by rw [(Prod.mk.inj h1).2]⟩)
      · rcases (mem_insertCv_iff hD).mp h1 with h3 | ⟨h3, h4⟩
        · exact Or.inl (Prod.mk.inj h3).2
        · obtain ⟨h5, h6⟩ := mem_dropCv.mp h3
          exact Or.inr (Or.inr ⟨h5, h4, h6⟩)

/-- The merge's target names neither of the two nodes merged, in a tree whose walk from the
parent visits each node once. -/
theorem wmg_target_not {A : Tree} {q : NodeId} {nq : KNode} (hAq : A.obj q = some (.key nq))
    (hT : (reachAt A (A.fuel q) q).Nodup) {cL cR : Nat} {l r m1 : NodeId}
    {m2 : Option (NodeId × Nat)} (hl : (cL, l) ∈ live nq.ks) (hr : (cR, r) ∈ live nq.ks)
    {o : NodeId} (ho : o = l ∨ o = r) (hom1 : o ≠ m1) (hom2 : ∀ g, m2 ≠ some (o, g)) (c : Nat) :
    (c, o) ∉ mergeTarget (live nq.ks) cL cR m1 m2 := by
  intro h
  rcases wmg_target_mem (live_sorted _) h with h1 | ⟨g, h1⟩ | ⟨h1, h2, h3⟩
  · exact hom1 h1
  · exact hom2 g h1
  · rcases ho with rfl | rfl
    · exact h2 (wmg_kid_once hAq hT h1 hl)
    · exact h3 (wmg_kid_once hAq hT h1 hr)

/-- `mergeKlongs` in one node: the merged klongs, at most c of them. -/
theorem wmg_mk_one {inner : Bool} {cap cR : Nat} {lvL lvR first : List (Nat × NodeId)}
    (h : SIS.Tree.mergeKlongs inner cap cR lvL lvR = (first, none)) :
    first = SIS.Tree.mergeList inner cR lvL lvR ∧ first.length ≤ cap := by
  unfold SIS.Tree.mergeKlongs SIS.Tree.splitMerged at h
  split at h
  · simp only [Prod.mk.injEq] at h
    exact ⟨h.1.symm, by rwa [← h.1]⟩
  · simp at h

/-- `mergeKlongs` in two nodes: the merged klongs cut after their first half; the second
node's klongs start with g (an inner node's renamed to the empty key). -/
theorem wmg_mk_two {inner : Bool} {cap cR : Nat} {lvL lvR first ks2 : List (Nat × NodeId)}
    {g2 : Nat} (hL : lvL ≠ []) (hR : lvR ≠ [])
    (h : SIS.Tree.mergeKlongs inner cap cR lvL lvR = (first, some (ks2, g2))) :
    ∃ y0 rest, SIS.Tree.mergeList inner cR lvL lvR = first ++ (g2, y0) :: rest ∧
      first ≠ [] ∧ ks2 = (if inner then (0, y0) :: rest else (g2, y0) :: rest) := by
  unfold SIS.Tree.mergeKlongs SIS.Tree.splitMerged at h
  split at h
  · simp at h
  · simp only [Prod.mk.injEq, Option.some.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    set e := SIS.Tree.mergeList inner cR lvL lvR with he
    have hlen : 2 ≤ e.length := by
      rw [he]
      unfold SIS.Tree.mergeList
      have h4 : 1 ≤ lvL.length := List.length_pos_iff.mpr hL
      have h5 : 1 ≤ (if inner then SIS.Tree.renameHead cR lvR else lvR).length := by
        split
        · cases lvR with
          | nil => exact absurd rfl hR
          | cons a r => simp [SIS.Tree.renameHead]
        · exact List.length_pos_iff.mpr hR
      simp only [List.length_append]
      omega
    obtain ⟨⟨g0, y0⟩, rest, hdrop⟩ : ∃ a rest, e.drop ((e.length + 1) / 2) = a :: rest := by
      cases hd : e.drop ((e.length + 1) / 2) with
      | nil =>
        have := congrArg List.length hd
        simp at this
        omega
      | cons a rest => exact ⟨a, rest, rfl⟩
    rw [hdrop] at h2 h3
    simp only [List.head?_cons, Option.map_some, Option.getD_some] at h3
    subst h3
    refine ⟨y0, rest, ?_, ?_, ?_⟩
    · rw [← h1, ← hdrop, List.take_append_drop]
    · rw [← h1]
      intro h6
      have := congrArg List.length h6
      rw [List.length_take, List.length_nil] at this
      omega
    · rw [← h2]
      cases inner <;> simp [SIS.Tree.renameHead]

/-! ## 6. The merge -/

theorem wmg_pathInner_ext {i : Time} {s : Tree} {w u : MW} {d : Nat} (hP : PathOk i s w d)
    (hin : PathInner w d) (hp : u.path = w.path)
    (hext : ∀ z n, w.nodes.lookup z = some n → u.nodes.lookup z = some n) : PathInner u d := by
  intro e c y n he hy hn
  rw [hp] at hy
  obtain ⟨n0, h0, -⟩ := hP.lookup (Nat.le_of_lt he) hy
  rw [hext y n0 h0] at hn
  cases hn
  exact hin e c y _ he hy h0

/-- What is left of the merge (bergdb 030-16, open): from the two nodes chosen, the merge's
klongs, the new nodes, the parent's klongs (`mergeParent`, by the tree rules `Sound.mergeOne`
and `Sound.mergeTwo`, and for a full parent `WmgSplitLink`), and the two nodes left out
(`wmg_loop`, proved). -/
def WmgRestOk (p : MParams) (i : Time) (base : NodeId) (s : Tree) (tp : Top) (v : View BVal) :
    Prop :=
  ∀ (w : MW) (C : List (Key × Nat)) (d : Nat) (q x : NodeId) (c0 : Option Nat) (cx : Nat)
    (pn xn : MNode) (l r : NodeId) (ln rn : MNode) (il ir cL cR : Nat) (isLeft : Bool),
    PInv p i base s tp none C w → WcrLink i s w → WmgFresh i s w → d ≠ 0 →
    PathOk i s w d → PathInner w d → w.path[d - 1]? = some (c0, q) →
    w.path[d]? = some (some cx, x) → w.nodes.lookup q = some pn →
    w.nodes.lookup x = some xn → w.nodes.lookup l = some ln → w.nodes.lookup r = some rn →
    LiveAt pn il cL l → LiveAt pn ir cR r → cL < cR →
    (∀ c y, (c, y) ∈ live (ksOf pn) → c ≤ cL ∨ cR ≤ c) → (x = l ∨ x = r) →
    ln.leaf = xn.leaf → rn.leaf = xn.leaf →
    WP (wmg_rest { p := p, i := i, view := v } q x pn xn d isLeft l ln il r rn ir)
      { p := p, i := i, view := v } w
      (fun _ w' => w'.outside = [] →
        PInv p i base s tp none C w' ∧ WcrLink i s w' ∧ WmgFresh i s w')

theorem wmg_pick_spec {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {z : NodeId} (hs : Shows p v z s tp) (hb : Books i base s tp)
    (hrest : WmgRestOk p i base s tp v) {w : MW} {C : List (Key × Nat)}
    (hI : PInv p i base s tp none C w) (ho : OldReach i s w) (hK : WcrLink i s w)
    (hF : WmgFresh i s w) {d : Nat} (hd : d ≠ 0)
    (hpath : PathOk i s w d) (hin : PathInner w d) {q x : NodeId} {c0 : Option Nat} {cx : Nat}
    (hq : w.path[d - 1]? = some (c0, q)) (hx : w.path[d]? = some (some cx, x))
    {pn xn : MNode} (hlq : w.nodes.lookup q = some pn) (hlx : w.nodes.lookup x = some xn) :
    WP (wmg_pick { p := p, i := i, view := v } q x pn xn d cx) { p := p, i := i, view := v } w
      (fun _ w' => w'.outside = [] →
        PInv p i base s tp none C w' ∧ WcrLink i s w' ∧ WmgFresh i s w') := by
  have htq : w.taken.contains q = false := (hpath.lookup (by omega) hq).choose_spec.2
  have htx : w.taken.contains x = false := (hpath.lookup (Nat.le_refl _) hx).choose_spec.2
  have hAq := treeOf_obj_overlay i s hlq htq
  have hql : pn.leaf = false := hin (d - 1) c0 q pn (by omega) hq hlq
  have hqR : q ∈ reachOf i s w :=
    ts_path_reach (A := treeOf i s w) (x := w.next) hI.sound.good hpath
      (fun d' c hd' he => by
        obtain ⟨m, hm, -⟩ := hpath.lookup (Nat.le_of_lt hd') he
        exact Nat.lt_irrefl _ (hI.books.ids.1 _ m hm))
      (fun _ _ => rfl) (d - 1) (by omega) c0 q hq
  have hok := hI.sound.nodes q hqR _ hAq
  simp only [reduceCtorEq, ite_false, nodeOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  have hwf : klongsWf (ksOf pn) = true := hok.1.2
  have hK' : ∀ u : MW, treeOf i s u = treeOf i s w → u.top = w.top → WcrLink i s u :=
    fun u hT ht => wcr_books_congr hT (by rw [ht]) hK
  have hF' : ∀ u : MW, treeOf i s u = treeOf i s w → u.next = w.next → WmgFresh i s u := by
    intro u hT hn
    unfold WmgFresh
    rw [hT, hn]
    exact hF
  unfold wmg_pick
  dsimp only
  rw [wmg_mergeIdx_eq]
  have hidx := wmg_idx_inv pn.lastBitmap cx pn.ks
  generalize pn.ks.zipIdx.foldl (wmg_idxStep pn.lastBitmap cx) (none, none, none) = R at hidx ⊢
  obtain ⟨ix?, ia, ib⟩ := R
  dsimp only
  cases ix? with
  | none =>
    rw [wp_bind]
    exact wp_throw _ _ _ _
  | some ix =>
    obtain ⟨⟨y0, hy0⟩, hD0, hlast0⟩ := hidx.ix ix rfl
    refine wput_ok rfl ?_
    refine wp_ite _ _ _ _ _ _ (fun _ => by rw [wp_bind]; exact wp_throw _ _ _ _) (fun hptr => ?_)
    have hy0x : y0 = x := by
      have h1 : pn.ptr? ix = some x := by simpa using hptr
      rw [wmg_ptr hy0] at h1
      exact Option.some.inj h1
    rw [hy0x] at hy0
    have hLx : LiveAt pn ix cx x := wmg_liveAt_of hwf hy0 hD0 hlast0
    -- the right sibling, from a state u as w
    have hright : ∀ (u : MW) (ia ca : Nat), PInv p i base s tp none C u →
        treeOf i s u = treeOf i s w → u.top = w.top → u.path = w.path →
        (∀ d, PathOk i s w d → PathOk i s u d) →
        (∀ z n, w.nodes.lookup z = some n → u.nodes.lookup z = some n) → u.next = w.next →
        (cx < ca ∧ (∃ y, pn.ks[ia]? = some (.key ca y)) ∧ ia ∉ pn.lastBitmap ∧
          (∀ j c y', pn.ks[j]? = some (.key c y') → j ∉ pn.lastBitmap → cx < c → ca ≤ c) ∧
          ∀ j y', ia < j → pn.ks[j]? = some (.key ca y') → j ∈ pn.lastBitmap) →
        WP (do
          let __x ← SIS.Tree.sibling q pn ia !xn.leaf
          let __x ← (pure (x, xn, ix, __x.1, __x.2, ia) :
            SIS.Tree.M (NodeId × MNode × Nat × NodeId × MNode × Nat))
          wmg_rest { p := p, i := i, view := v } q x pn xn d false __x.1 __x.2.1 __x.2.2.1
            __x.2.2.2.1 __x.2.2.2.2.1 __x.2.2.2.2.2)
          { p := p, i := i, view := v } u
          (fun _ w' => w'.outside = [] →
            PInv p i base s tp none C w' ∧ WcrLink i s w' ∧ WmgFresh i s w') := by
      intro u ia ca hIu hTu htopu hpu hPu hlku hnu ⟨h1, ⟨y, hy⟩, h2, h3, h4⟩
      have htqu : u.taken.contains q = false := by
        rw [← htq]
        exact (wput_taken (o := .key _) (by rw [hTu]; exact hAq)).trans htq.symm
      have hqRu : q ∈ reachOf i s u := by
        unfold reachOf
        rw [hTu, htopu]
        exact hqR
      have hou : OldReach i s u := by
        unfold OldReach at ho ⊢
        rw [hTu]
        exact ho
      rw [wp_bind]
      refine (wmg_sibling hs hb hIu hou (hlku q pn hlq) htqu hqRu hql hy
        (linkIndex_some hwf (wmp_linkIndex (wmg_liveAt_of hwf hy h2 h4))).2.1 _).mono ?_
      rintro ⟨rs, rsn⟩ u1 ⟨hrs, hl1, hleaf1, hT1, hI1, hp1, htop1, -, hn1, hext1, hP1⟩
      simp only at hrs hl1 hleaf1
      subst hrs
      refine wput_ok rfl ?_
      refine hrest u1 C d q x c0 cx pn xn x rs xn rsn ix ia cx ca false hI1
        (hK' u1 (hT1.trans hTu) (htop1.trans htopu)) (hF' u1 (hT1.trans hTu) (hn1.trans hnu))
        hd (hP1 d (hPu d hpath)) (wmg_pathInner_ext hpath hin (hp1.trans hpu)
          (fun z n h => hext1 z n (hlku z n h)))
        (by rw [hp1, hpu]; exact hq) (by rw [hp1, hpu]; exact hx)
        (hext1 q pn (hlku q pn hlq)) (hext1 x xn (hlku x xn hlx))
        (hext1 x xn (hlku x xn hlx)) hl1 hLx (wmg_liveAt_of hwf hy h2 h4) h1 ?_ (Or.inl rfl)
        rfl (by rw [hleaf1]; simp)
      intro c y' hm
      obtain ⟨j, hj, hjD⟩ := wmg_live_idx hm
      by_cases hc : cx < c
      · exact Or.inr (h3 j c y' hj hjD hc)
      · exact Or.inl (by omega)
    have hlku0 : ∀ z n, w.nodes.lookup z = some n → w.nodes.lookup z = some n := fun _ _ h => h
    cases ib with
    | none =>
      refine wput_ok rfl ?_
      cases ia with
      | none =>
        rw [wp_bind]
        exact wp_throw _ _ _ _
      | some iac =>
        obtain ⟨ia, ca⟩ := iac
        exact hright w ia ca hI rfl rfl rfl (fun _ h => h) hlku0 rfl (hidx.ia ia ca rfl)
    | some ibc =>
      obtain ⟨ib, cb⟩ := ibc
      obtain ⟨g1, ⟨yb, hyb⟩, g2, g3, g4⟩ := hidx.ib ib cb rfl
      dsimp only
      rw [wp_bind]
      refine (wmg_sibling hs hb hI ho hlq htq hqR hql hyb
        (linkIndex_some hwf (wmp_linkIndex (wmg_liveAt_of hwf hyb g2 g4))).2.1 _).mono ?_
      rintro ⟨ls, lsn⟩ u1 ⟨hls, hl1, hleaf1, hT1, hI1, hp1, htop1, -, hn1, hext1, hP1⟩
      simp only at hls hl1 hleaf1
      subst hls
      have hleft : WP (wmg_rest { p := p, i := i, view := v } q x pn xn d true ls lsn ib x xn ix)
          { p := p, i := i, view := v } u1
          (fun _ w' => w'.outside = [] →
            PInv p i base s tp none C w' ∧ WcrLink i s w' ∧ WmgFresh i s w') := by
        refine hrest u1 C d q x c0 cx pn xn ls x lsn xn ib ix cb cx true hI1 (hK' u1 hT1 htop1)
          (hF' u1 hT1 hn1) hd (hP1 d hpath)
          (wmg_pathInner_ext hpath hin hp1 hext1)
          (by rw [hp1]; exact hq) (by rw [hp1]; exact hx) (hext1 q pn hlq) (hext1 x xn hlx)
          hl1 (hext1 x xn hlx) (wmg_liveAt_of hwf hyb g2 g4) hLx g1 ?_ (Or.inr rfl)
          (by rw [hleaf1]; simp) rfl
        intro c y' hm
        obtain ⟨j, hj, hjD⟩ := wmg_live_idx hm
        by_cases hc : c < cx
        · exact Or.inl (g3 j c y' hj hjD hc)
        · exact Or.inr (by omega)
      refine wp_ite _ _ _ _ _ _ (fun _ => ?_) (fun _ => ?_)
      · refine wput_ok rfl ?_
        refine wput_ok rfl ?_
        exact hleft
      · refine wput_ok rfl ?_
        cases ia with
        | none =>
          rw [wp_bind]
          exact wp_throw _ _ _ _
        | some iac =>
          obtain ⟨ia, ca⟩ := iac
          exact hright u1 ia ca hI1 hT1 htop1 hp1 hP1 hext1 hn1 (hidx.ia ia ca rfl)

/-- The merge from what is left (`WmgRestOk`): the reads, `mergeIdx` and the choice of the
sibling. -/
theorem merge_spec_of_rest {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {z : NodeId} (hs : Shows p v z s tp) (hb : Books i base s tp)
    (hrest : WmgRestOk p i base s tp v)
    {d : Nat} {x : NodeId} {w : MW} {C : List (Key × Nat)}
    (hI : PInv p i base s tp none C w) (ho : OldReach i s w) (hK : WcrLink i s w)
    (hF : WmgFresh i s w)
    (hpath : PathOk i s w d) (hin : PathInner w d) (hon : ∃ c0, w.path[d]? = some (c0, x))
    (hd : d ≠ 0) :
    WP (SIS.Tree.merge x d) { p := p, i := i, view := v } w
      (fun _ w' => w'.outside = [] →
        PInv p i base s tp none C w' ∧ WcrLink i s w' ∧ WmgFresh i s w') := by
  obtain ⟨c0', q, cc, y, nq, e1, e2, -, -⟩ := hpath.links (d - 1) (by omega)
  rw [show d - 1 + 1 = d by omega] at e2
  obtain ⟨c0, hx⟩ := hon
  rw [hx] at e2
  cases e2
  obtain ⟨pn, hlq, -⟩ := hpath.lookup (by omega) e1
  obtain ⟨xn, hlx, -⟩ := hpath.lookup (Nat.le_refl _) hx
  rw [wmg_eq]
  refine wput_read ?_
  refine wput_ok (pathNode_eq _ e1) ?_
  refine wput_ok (getNode_hit _ hlq) ?_
  refine wput_ok (getNode_hit _ hlx) ?_
  refine wput_ok (klongAt_eq _ hx) ?_
  exact wmg_pick_spec hs hb hrest hI ho hK hF hd hpath hin e1 hx hlq hlx

end Contract
