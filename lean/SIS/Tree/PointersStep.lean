/-
The tree model (bergdb 024-12, TP4 and TP7): TP4 after a transaction. Every
entry of the structure after a transaction is an entry of P or an entry that
the transaction adds (`ptrStep_entry`). A node of P is a node after it, so an
entry of P still points to a node. An added entry is one of the overlay's
klongs of a node not taken back, a value's data, or one of the new top node's
entries (`changesOf`). A klong of the overlay names a node of P or a made node
(`PtrsOK`) that is not taken back, and a made node not taken back is a node
after the transaction; so are the new top node, the node its root key names
and those its skips name. So every pointer after it names a node
(`pointersOK_step`).
-/
import SIS.Tree.GetCommit
import SIS.Tree.OverlayBook
import SIS.Tree.OverlayPtrs
import SIS.Tree.ExportLedger
import SIS.Tree.ExportHistory
import SIS.Tree.KlongRoundTrip

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## The entries of a structure after a transaction -/

/-- An entry after adding entries is an entry of the node before, or one
added to it. -/
theorem ptrStep_mem_foldl (i : Time) (adds : List (NodeId × BVal)) (Q : Struct BVal)
    (q : NodeId × Node BVal) (hq : q ∈ adds.foldl (fun P a => P.addEntry i a.1 a.2) Q)
    (e : Entry BVal) (he : e ∈ q.2.hist) :
    (∃ old, (q.1, old) ∈ Q ∧ e ∈ old.hist) ∨ (q.1, e.val) ∈ adds := by
  induction adds generalizing Q with
  | nil => exact Or.inl ⟨q.2, hq, he⟩
  | cons a adds ih =>
    rw [List.foldl_cons] at hq
    rcases ih _ hq with ⟨old, hold, heo⟩ | hm
    · unfold Struct.addEntry at hold
      obtain ⟨r, hr, hfr⟩ := List.mem_map.mp hold
      by_cases hra : r.1 = a.1
      · simp only [hra, ↓reduceIte] at hfr
        obtain ⟨h1, h2⟩ := Prod.mk.inj hfr
        rw [← h2] at heo
        rcases List.mem_append.mp heo with heo | heo
        · left
          refine ⟨r.2, ?_, heo⟩
          rw [← h1, ← hra]
          exact hr
        · right
          have : e = ⟨i, a.2⟩ := List.mem_singleton.mp heo
          subst this
          rw [← h1]
          exact List.mem_cons_self
      · simp only [hra, ↓reduceIte] at hfr
        left
        refine ⟨old, ?_, heo⟩
        rw [← hfr]
        exact hr
    · exact Or.inr (List.mem_cons_of_mem _ hm)

/-- Every entry of the structure after a transaction is an entry of P, or one
the transaction adds. -/
theorem ptrStep_entry (P : Struct BVal) (i : Time) (c : Changes BVal)
    (q : NodeId × Node BVal) (hq : q ∈ P.apply i c) (e : Entry BVal) (he : e ∈ q.2.hist) :
    (∃ old, (q.1, old) ∈ P ∧ e ∈ old.hist) ∨ (q.1, e.val) ∈ c.adds := by
  unfold Struct.apply at hq
  rcases ptrStep_mem_foldl i c.adds _ q hq e he with ⟨old, hold, heo⟩ | hm
  · rcases List.mem_append.mp hold with hold | hold
    · exact Or.inl ⟨old, hold, heo⟩
    · obtain ⟨nn, _, hnn⟩ := List.mem_map.mp hold
      obtain ⟨_, h2⟩ := Prod.mk.inj hnn
      rw [← h2] at heo
      cases heo
  · exact Or.inr hm

/-! ## The pointers of the entries of klongs -/

/-- The pointers of an entry from klongs name the children of key klongs. -/
theorem ptrStep_entriesOf (ks : List Klong) (e : Entry BVal) (he : e ∈ entriesOf ks)
    (y : NodeId) (hy : y ∈ bptrs e.val) : ∃ cv, Klong.key cv y ∈ ks := by
  let Good : History BVal → Prop := fun h =>
    ∀ e ∈ h, ∀ y ∈ bptrs e.val, ∃ cv, Klong.key cv y ∈ ks
  have hmarker : ∀ t, Good [⟨t, marker⟩] := by
    intro t e he y hy
    have := List.mem_singleton.mp he
    subst this
    simp [marker, bptrs] at hy
  have happ : ∀ a b, Good a → Good b → Good (a ++ b) := by
    intro a b ha hb e he
    rcases List.mem_append.mp he with he | he
    · exact ha e he
    · exact hb e he
  have hfold : ∀ (qs : List Klong), (∀ k ∈ qs, k ∈ ks) → ∀ (a : KlongEntryState), Good a.1 →
      Good (qs.foldl (encodeKlong ks) a).1 := by
    intro qs
    induction qs with
    | nil => intro _ a ha; exact ha
    | cons k qs ih =>
      intro hqs a ha
      rw [List.foldl_cons]
      apply ih (fun k' hk' => hqs k' (List.mem_cons_of_mem _ hk'))
      have hk : k ∈ ks := hqs k List.mem_cons_self
      rcases a with ⟨es, t, bits, had⟩
      cases k with
      | time t' =>
        show Good (if had then es else es ++ [⟨t, marker⟩])
        split
        · exact ha
        · exact happ _ _ ha (hmarker t)
      | key cv y' =>
        show Good (es ++ [⟨t, .key cv y'⟩])
        refine happ _ _ ha ?_
        intro e he y hy
        have := List.mem_singleton.mp he
        subst this
        simp only [bptrs, List.mem_singleton] at hy
        subst hy
        exact ⟨cv, hk⟩
      | del bs =>
        show Good (es ++ [⟨t, .del (bitmapEntryCvs ks bits bs)⟩])
        refine happ _ _ ha ?_
        intro e he y hy
        have := List.mem_singleton.mp he
        subst this
        simp [bptrs] at hy
  have hf := hfold ks (fun k hk => hk) ([], 0, [], true) (by intro e he; cases he)
  rw [entriesOf_eq_encode] at he
  unfold finishKlongEntries at he
  split at he
  · exact hf e he y hy
  · exact happ _ _ hf (hmarker _) e he y hy

/-! ## TP4 after a transaction -/

/-- TP4 after a transaction: for a successful run of the writer at time i on
P@(i-1), whose overlay names nodes of P or made nodes (`PtrsOK`), with the
writer's books (`Book`), where no node kept names a node taken back and the
root key of the top node is not taken back, every pointer of the structure
after it names a node if every pointer of P does. -/
theorem pointersOK_step (p : Params) (P : Struct BVal) (i : Time) (tx : Tx) (bs : List Bool) (w : W)
    (_hfresh : ∀ q ∈ P, q.1 < tx.base) (hP : PointersOK P)
    (he : execW p tx i (view (treeSpec p) P (i - 1)) = .ok (bs, w))
    (hptrs : PtrsOK (fun y => (P.get? y).isSome = true)
      { p := p, i := i, view := rootless (view (treeSpec p) P (i - 1)) } w)
    (hbook : Book tx.base { p := p, i := i, view := rootless (view (treeSpec p) P (i - 1)) } w)
    (hT1 : ∀ q ∈ w.nodes, w.taken.contains q.1 = false →
      ∀ cv y, Klong.key cv y ∈ q.2.ks → w.taken.contains y = false)
    (hT2 : w.taken.contains w.top.rootKey = false) :
    PointersOK (P.apply i (changesOf i w)) := by
  have halloc := execW_allocatedIds p tx i _ bs w he
  have hledger := execW_ledger p tx i _ bs w he
  -- A node of P, or a made node not taken back, is a node after.
  have hold : ∀ y, (P.get? y).isSome = true →
      ((P.apply i (changesOf i w)).get? y).isSome = true := by
    intro y hy
    cases hpy : P.get? y with
    | none => rw [hpy] at hy; cases hy
    | some nd => rw [get?_apply_of_get? hpy]; rfl
  have hmade : ∀ y, y ∈ w.made.map (·.id) → w.taken.contains y = false →
      ((P.apply i (changesOf i w)).get? y).isSome = true := by
    intro y hy ht
    obtain ⟨m, hm, hmy⟩ := List.mem_map.mp hy
    subst hmy
    rw [get?_apply, newNodeOf_changesOf_made tx.base i w halloc m hm ht]
    cases P.get? m.id <;> rfl
  have hboth : ∀ y, ((P.get? y).isSome = true ∨ y ∈ w.made.map (·.id)) →
      w.taken.contains y = false → ((P.apply i (changesOf i w)).get? y).isSome = true := by
    intro y hy ht
    rcases hy with hy | hy
    · exact hold y hy
    · exact hmade y hy ht
  intro q hq e heq y hy
  rcases ptrStep_entry P i (changesOf i w) q hq e heq with ⟨old, hq0, he0⟩ | hadd
  · exact hold y (hP (q.1, old) hq0 e he0 y hy)
  · rw [changesOf_adds] at hadd
    have hadd' := (List.mergeSort_perm _ _).mem_iff.mp hadd
    rcases List.mem_append.mp hadd' with hadd' | htop
    · rcases List.mem_append.mp hadd' with hkey | hval
      · -- A klong of a node of the overlay not taken back.
        unfold keyAdditions at hkey
        obtain ⟨r, hr, hre⟩ := List.mem_flatMap.mp hkey
        obtain ⟨hrn, hrt⟩ := List.mem_filter.mp hr
        have hrt' : w.taken.contains r.1 = false := by simpa using hrt
        obtain ⟨e', he', hee⟩ := List.mem_map.mp hre
        obtain ⟨_, hv⟩ := Prod.mk.inj hee
        have he'' : e' ∈ entriesOf r.2.ks := (List.mem_filter.mp he').1
        rw [← hv] at hy
        obtain ⟨cv, hk⟩ := ptrStep_entriesOf r.2.ks e' he'' y hy
        exact hboth y (hptrs.klongs r hrn cv y hk) (hT1 r hrn hrt' cv y hk)
      · -- A value's data has no pointer.
        unfold valueAdditions at hval
        obtain ⟨r, _, hre⟩ := List.mem_map.mp hval
        obtain ⟨_, hv⟩ := Prod.mk.inj hre
        rw [← hv] at hy
        simp [bptrs] at hy
    · -- The new top node's entries and the root's entry for it.
      unfold topAdditions at htop
      cases hnt : w.newTop with
      | false => simp [hnt] at htop
      | true =>
        simp only [hnt, ↓reduceIte] at htop
        rcases List.mem_cons.mp htop with htop | htop
        · obtain ⟨_, hv⟩ := Prod.mk.inj htop
          rw [hv] at hy
          simp only [bptrs, List.mem_singleton] at hy
          subst hy
          obtain ⟨lvl, _, hm⟩ := hledger.2.2 hnt
          apply hmade _ (List.mem_map.mpr ⟨_, hm, rfl⟩)
          cases htk : w.taken.contains w.top.id with
          | false => rfl
          | true =>
            have hmem : w.top.id ∈ w.taken := by simpa using htk
            exact absurd (hbook.taken _ hmem) (hbook.top hnt).2.2
        rcases List.mem_cons.mp htop with htop | htop
        · obtain ⟨_, hv⟩ := Prod.mk.inj htop
          rw [hv] at hy
          simp only [bptrs, List.mem_singleton] at hy
          subst hy
          exact hboth _ hptrs.rootKey hT2
        · obtain ⟨s, hs, hse⟩ := List.mem_map.mp htop
          obtain ⟨_, hv⟩ := Prod.mk.inj hse
          rw [← hv] at hy
          simp only [bptrs, List.mem_singleton] at hy
          subst hy
          exact hold _ (hptrs.skips s hs)

end SIS.Tree
