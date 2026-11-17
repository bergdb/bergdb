/-
The contract package (bergdb 030-10): the model's structure after a transaction
holds the tree of the writer's state. A part of "the view after a transaction"
(the item, section 6): the model's `exec?` applies the writer's changes
(`SIS.Tree.changesOf`) to its abstract structure P (`SIS.Struct.apply`), and
the next transaction's view is read from the result. `Holds p P s`: each key
node of the tree s is a key node of P with its level and its klongs. It is
kept (`holds_apply`): after an accepted run of the writer from P@(i-1) with
the state w, the structure after the changes holds the tree of w
(`treeOf i s w`).

The work on the structure is the old package's (lean/SIS/Tree/ApplyBridge.lean,
`apply_keyNode`, the old TP7: a key node of the structure after the
transaction is an overlay node not taken back, with the overlay's klongs, or a
node of P as it was), imported, not copied: it is proved there for every
accepted run from premises on P only. From `SIS.Tree.GetCommit` (and the
`DataEntries` it imports): a node made with an id is the new node of the
changes (`newNodeOf_changesOf_made`), and a data node made is a value
(`execW_madeData`), so a node made in the overlay is a key node.
-/
import Contract.Proof.WriterRun
import SIS.Tree.ApplyBridge
import SIS.Tree.GetCommit

namespace Contract

open SIS (View Struct)
open SIS.Check (BVal)

/-- The structure P holds the tree s: each key node of s is a key node of P,
with its level and its klongs (the klongs of the node's history in P). P may
hold more: the nodes of the top, the root, and nodes that s lacks. -/
def Holds (p : MParams) (P : Struct BVal) (s : Tree) : Prop :=
  ∀ x n, s.obj x = some (.key n) → ∃ nd, P.get? x = some nd ∧ nd.isData = false ∧
    nd.level = n.level ∧ n.level ≤ p.keyMax ∧ (SIS.Tree.klongsOf nd.hist).map kOf = n.ks

/-- `Holds` is kept by a transaction: for an accepted run of the writer at time
i from P@(i-1) (the premises of `SIS.Tree.apply_keyNode` on P) that ends in
the state w with the writer's books, from a tree s that P holds and whose ids
are below the transaction's first id, the structure after the writer's
changes holds the tree of w. -/
theorem holds_apply {p : MParams} {P : Struct BVal} {i : Time} {tx : SIS.Tree.Tx}
    {bs : List Bool} {w : MW} {s : Tree}
    (hpos : 0 < i) (hfresh : ∀ q ∈ P, q.1 < tx.base)
    (htimes : SIS.Tree.StructTimesLE P (i - 1))
    (hroot : ∃ r, P.get? SIS.root = some r ∧ p.keyMax < r.level)
    (hH : SIS.Tree.KeyHistOK p P)
    (hl : SIS.Tree.ViewLinksOK tx.base p (SIS.view (SIS.Tree.treeSpec p) P (i - 1)))
    (he : SIS.Tree.execW p tx i (SIS.view (SIS.Tree.treeSpec p) P (i - 1)) = .ok (bs, w))
    (hS : Holds p P s) (hids : ∀ x, tx.base ≤ x → s.obj x = none)
    (hB : MidBooks p i tx.base s w) :
    Holds p (P.apply i (SIS.Tree.changesOf i w)) (treeOf i s w) := by
  have halloc := SIS.Tree.execW_allocatedIds p tx i _ bs w he
  have hledger := SIS.Tree.execW_ledger p tx i _ bs w he
  have hmd := SIS.Tree.execW_madeData p tx i _ bs w he
  -- A key node after the changes that the overlay holds, not taken back: the overlay's klongs.
  have hkl : ∀ x nd' m, (P.apply i (SIS.Tree.changesOf i w)).get? x = some nd' →
      nd'.isData = false → nd'.level ≤ p.keyMax → w.nodes.lookup x = some m →
      w.taken.contains x = false → SIS.Tree.klongsOf nd'.hist = m.ks := by
    intro x nd' m hx hd hlv hm ht
    rcases SIS.Tree.apply_keyNode p P i tx bs w hpos hfresh htimes hroot hH hl he x nd' hx hd
      hlv with ⟨n, hn, _, _, hk, _⟩ | ⟨_, hn | hn⟩
    · rw [hm] at hn
      cases hn
      exact hk
    · rw [hm] at hn
      cases hn
    · rw [ht] at hn
      cases hn
  intro x n hx
  simp only [treeOf] at hx
  cases ht : w.taken.contains x with
  | true => simp only [ht, ↓reduceIte, reduceCtorEq] at hx
  | false =>
    simp only [ht, Bool.false_eq_true, ↓reduceIte] at hx
    cases hm : w.nodes.lookup x with
    | some m =>
      simp only [hm, Option.some.injEq, Obj.key.injEq] at hx
      subst hx
      obtain ⟨g, h, _, _, hh, hlev, _⟩ := hB.levels x m hm ht
      have hmax : wLevel s w x ≤ p.keyMax := hlev ▸ SIS.Tree.keyLevel_le_keyMax p g h hh
      have hlpos : 0 < wLevel s w x := by
        rw [hlev]
        unfold SIS.Tree.Params.keyLevel
        omega
      obtain ⟨nd', hx', hd', hlv'⟩ : ∃ nd',
          (P.apply i (SIS.Tree.changesOf i w)).get? x = some nd' ∧
          nd'.isData = false ∧ nd'.level = wLevel s w x := by
        by_cases hxb : x < tx.base
        · -- A node of s.
          have hnm : x ∉ w.made.map (·.id) := by
            intro hxm
            obtain ⟨mm, hmm, rfl⟩ := List.mem_map.mp hxm
            exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hxb (hB.ids.2.2.1 mm hmm).2)
          cases hs : s.obj x with
          | none =>
            rcases hB.overlay x m hm with h1 | h1
            · rw [hs] at h1
              cases h1
            · exact absurd h1 hnm
          | some o =>
            cases o with
            | key n0 =>
              obtain ⟨nd, hnd, hd, hlv, _, _⟩ := hS x n0 hs
              have hw : wLevel s w x = n0.level := by
                unfold wLevel
                rw [hs]
              exact ⟨_, SIS.get?_apply_of_get? hnd, hd, by rw [hw]; exact hlv⟩
            | val v =>
              have hf : w.made.find? (fun m => m.id == x) = none := by
                apply List.find?_eq_none.mpr
                intro mm hmm hid
                exact hnm (List.mem_map.mpr ⟨mm, hmm, by simpa using hid⟩)
              have hw : wLevel s w x = 0 := by
                unfold wLevel
                rw [hs, hf]
              omega
        · -- A node made.
          have hs : s.obj x = none := hids x (Nat.not_lt.mp hxb)
          obtain ⟨mm, hmm, hid⟩ : ∃ mm ∈ w.made, mm.id = x := by
            rcases hB.overlay x m hm with h1 | h1
            · rw [hs] at h1
              cases h1
            · exact List.mem_map.mp h1
          subst hid
          have hw : wLevel s w mm.id = mm.level := by
            unfold wLevel
            rw [hs]
            cases hf : w.made.find? (fun m => m.id == mm.id) with
            | none =>
              have := List.find?_eq_none.mp hf mm hmm
              simp at this
            | some m' =>
              have h1 := List.mem_of_find?_eq_some hf
              have h2 : m'.id = mm.id := by simpa using List.find?_some hf
              rw [SIS.Tree.made_unique tx.base w halloc _ _ h1 hmm h2]
          have hd : mm.isData = false := by
            cases hdat : mm.isData with
            | false => rfl
            | true =>
              obtain ⟨v, hv⟩ := hmd mm hmm hdat
              have h0 := SIS.Tree.made_unique tx.base w halloc _ _ (hledger.2.1 _ hv) hmm rfl
              have : mm.level = 0 := by rw [← h0]
              omega
          have hp : P.get? mm.id = none := by
            cases hp : P.get? mm.id with
            | none => rfl
            | some nd =>
              have h1 : mm.id < tx.base := hfresh _ (SIS.mem_of_get? hp)
              have h2 := (halloc.2.2 mm hmm).1
              omega
          have hn := SIS.Tree.newNodeOf_changesOf_made tx.base i w halloc mm hmm ht
          have hx2 : (P.apply i (SIS.Tree.changesOf i w)).get? mm.id = some
              { level := mm.level, isData := mm.isData,
                hist := [] ++ SIS.addsFor (SIS.Tree.changesOf i w) i mm.id } := by
            rw [SIS.get?_apply, hp, hn]
            rfl
          exact ⟨_, hx2, hd, hw.symm⟩
      refine ⟨nd', hx', hd', hlv', hmax, ?_⟩
      rw [hkl x nd' m hx' hd' (hlv' ▸ hmax) hm ht]
    | none =>
      simp only [hm] at hx
      cases hv : w.vals.lookup x with
      | some h => simp [hv] at hx
      | none =>
        simp only [hv] at hx
        obtain ⟨nd, hnd, hd, hlv, hmax, hk⟩ := hS x n hx
        have hx' := SIS.get?_apply_of_get? (i := i) (c := SIS.Tree.changesOf i w) hnd
        rcases SIS.Tree.apply_keyNode p P i tx bs w hpos hfresh htimes hroot hH hl he x _ hx' hd
          (by rw [← hlv] at hmax; exact hmax) with ⟨n', hn', _⟩ | ⟨hp, _⟩
        · rw [hm] at hn'
          cases hn'
        · rw [hnd] at hp
          refine ⟨_, hx', hd, hlv, hmax, ?_⟩
          rw [← Option.some.inj hp]
          exact hk

end Contract
