/-
The tree model (bergdb 024-12, TP7): the kinds in P after a transaction.
Every key klong of a key node of P names, if P holds it, a node of the kind
the klong promises (`KindsAllOK`). A transaction keeps it when the writer's
overlay has `KindCache` for the oracle of P (`kindsAllOK_step`): a key node
after the transaction is a node of P as it was, or an overlay node not taken
back whose segment and height are those of its entry in the writer's list;
a node that `KindCache` names is, after the transaction, a key node of the
segment named or a value. The view of a structure with `KindsAllOK` meets
`ViewKinds` (`viewKinds_of`); the first structure has it
(`kindsAllOK_init`); and the walk's kind tests but the height's follow for
live klongs (`kindsAllOK_live`).
-/
import SIS.Tree.OverlayKinds
import SIS.Tree.OverlayLift
import SIS.Tree.WalkNil
import SIS.Proof.TreeInit

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## 1. The nodes after a transaction -/

/-- A node of P after the changes: same level and kind. -/
theorem kindsStep_old (P : Struct BVal) (i : Time) (c : Changes BVal) (y : NodeId)
    (n ny : Node BVal) (hPy : P.get? y = some n) (hy : (P.apply i c).get? y = some ny) :
    ny.level = n.level ∧ ny.isData = n.isData := by
  rw [get?_apply_of_get? hPy] at hy
  obtain rfl := Option.some.inj hy
  exact ⟨rfl, rfl⟩

/-- A node after a transaction that P does not hold: one the transaction
made and did not take back, of the made node's level and kind. -/
theorem kindsStep_new (P : Struct BVal) (i : Time) (w : W) (y : NodeId) (ny : Node BVal)
    (hPy : P.get? y = none) (hy : (P.apply i (changesOf i w)).get? y = some ny) :
    ∃ nn ∈ w.made, nn.id = y ∧ w.taken.contains y = false ∧ ny.level = nn.level ∧
      ny.isData = nn.isData := by
  rw [get?_apply, hPy, Option.none_or] at hy
  cases hn : newNodeOf (changesOf i w) y with
  | none => rw [hn] at hy; cases hy
  | some nd0 =>
    rw [hn] at hy
    obtain ⟨nn, hnn, hid, hnd0⟩ := newNodeOf_new_mem _ y nd0 hn
    obtain ⟨hmade, hnt⟩ := changesOf_new_mem i w nn hnn
    obtain rfl := Option.some.inj hy
    subst hid
    refine ⟨nn, hmade, rfl, hnt, ?_, ?_⟩ <;> rw [hnd0]

section
variable (p : Params) (P : Struct BVal) (i : Time) (tx : Tx) (bs : List Bool) (w : W)

/-- A node of the writer's list of segments and heights is, after the
transaction, a key node of its segment and height. -/
theorem kindsStep_gh (hfresh : ∀ q ∈ P, q.1 < tx.base) (htimes : StructTimesLE P (i - 1))
    (he : execW p tx i (view (treeSpec p) P (i - 1)) = .ok (bs, w))
    (hbook : Book tx.base { p := p, i := i, view := rootless (view (treeSpec p) P (i - 1)) } w)
    (y : NodeId) (g h : Nat) (hgh : (y, g, h) ∈ w.gh) (ny : Node BVal)
    (hy : (P.apply i (changesOf i w)).get? y = some ny) :
    ny.isData = false ∧ ny.level ≤ p.keyMax ∧ p.segOf ny.level = g ∧ p.heightOf ny.level = h := by
  rcases hbook.tag y g h hgh with ⟨nd, hv, hd, hlv, hg, hh⟩ | ⟨hB, hmade, hout⟩
  · have hg' := view_eq_get? p P (i - 1) htimes y nd (rootless_some_eq _ y nd hv)
    obtain ⟨h1, h2⟩ := kindsStep_old P i _ y nd ny hg' hy
    rw [h1, h2]
    exact ⟨hd, hlv, hg.symm, hh.symm⟩
  · have hPy := get?_none_of_ge P tx.base y hfresh hB
    obtain ⟨nn, hnn, hid, hnt, h1, h2⟩ := kindsStep_new P i w y ny hPy hy
    have halloc := execW_allocatedIds p tx i _ bs w he
    have heq := made_unique tx.base w halloc _ _ hnn hmade hid
    subst heq
    have hin : ¬ (p.G < g ∨ p.H < h) := by
      intro hc
      have := execW_outside_taken p tx i _ bs w he _ (hout hc)
      simp only at this
      rw [hnt] at this
      cases this
    rw [h1, h2]
    exact ⟨rfl, keyLevel_le_keyMax p g h (by omega),
      Params.segOf_keyLevel p g h (by omega) (by omega), Params.heightOf_keyLevel p g h (by omega)⟩

/-- A value that the transaction made is, after it, a data node. -/
theorem kindsStep_vals (hfresh : ∀ q ∈ P, q.1 < tx.base)
    (he : execW p tx i (view (treeSpec p) P (i - 1)) = .ok (bs, w))
    (y : NodeId) (hh : Nat) (hv : (y, hh) ∈ w.vals) (ny : Node BVal)
    (hy : (P.apply i (changesOf i w)).get? y = some ny) : ny.isData = true := by
  have hledger := execW_ledger p tx i _ bs w he
  have halloc := execW_allocatedIds p tx i _ bs w he
  have hmade : (⟨y, 0, true⟩ : NewNode) ∈ w.made := hledger.2.1 _ hv
  have hB : tx.base ≤ y := (halloc.2.2 _ hmade).1
  have hPy := get?_none_of_ge P tx.base y hfresh hB
  obtain ⟨nn, hnn, hid, _, _, h2⟩ := kindsStep_new P i w y ny hPy hy
  have heq := made_unique tx.base w halloc _ _ hnn hmade hid
  subst heq
  exact h2

/-- A key node of segment g for the writer is, after the transaction, a key
node of segment g. -/
theorem kindsStep_keySeg (hfresh : ∀ q ∈ P, q.1 < tx.base) (htimes : StructTimesLE P (i - 1))
    (he : execW p tx i (view (treeSpec p) P (i - 1)) = .ok (bs, w))
    (hbook : Book tx.base { p := p, i := i, view := rootless (view (treeSpec p) P (i - 1)) } w)
    (y : NodeId) (g : Nat) (hk : IsKeySeg (kindOracleOf p P) w y g) (ny : Node BVal)
    (hy : (P.apply i (changesOf i w)).get? y = some ny) :
    ny.isData = false ∧ ny.level ≤ p.keyMax ∧ p.segOf ny.level = g := by
  rcases hk with ⟨h, hgh⟩ | ⟨n, hPy, hd, hlv, hg⟩
  · obtain ⟨a, b, c, _⟩ := kindsStep_gh p P i tx bs w hfresh htimes he hbook y g h hgh ny hy
    exact ⟨a, b, c⟩
  · obtain ⟨h1, h2⟩ := kindsStep_old P i _ y n ny hPy hy
    rw [h1, h2]
    exact ⟨hd, hlv, hg⟩

/-- A value for the writer is, after the transaction, a data node. -/
theorem kindsStep_valId (hfresh : ∀ q ∈ P, q.1 < tx.base)
    (he : execW p tx i (view (treeSpec p) P (i - 1)) = .ok (bs, w))
    (y : NodeId) (hk : IsValId (kindOracleOf p P) w y) (ny : Node BVal)
    (hy : (P.apply i (changesOf i w)).get? y = some ny) : ny.isData = true := by
  rcases hk with ⟨hh, hv⟩ | ⟨n, hPy, hd⟩
  · exact kindsStep_vals p P i tx bs w hfresh he y hh hv ny hy
  · obtain ⟨_, h2⟩ := kindsStep_old P i _ y n ny hPy hy
    rw [h2]
    exact hd

end

/-- The node that a key klong of a node of P names is a node of P (TP4). -/
theorem kindsStep_ptr (P : Struct BVal) (hP : PointersOK P) (x : NodeId) (nd : Node BVal)
    (hx : P.get? x = some nd) (c : Nat) (y : NodeId) (hk : Klong.key c y ∈ klongsOf nd.hist) :
    ∃ ny, P.get? y = some ny := by
  obtain ⟨e, he, hev⟩ := klongsOf_key_mem nd.hist c y hk
  have hsome := hP _ (mem_of_get? hx) e he y (by rw [hev]; simp [bptrs])
  cases hy : P.get? y with
  | none => rw [hy] at hsome; cases hsome
  | some ny => exact ⟨ny, rfl⟩

/-! ## 2. The step -/

/-- A transaction keeps `KindsAllOK` when the writer's overlay has
`KindCache` for the oracle of P: a key node after it is a node of P as it
was, whose klongs name nodes of P, or an overlay node not taken back, of the
segment and height of its entry in the writer's list. -/
theorem kindsAllOK_step (p : Params) (P : Struct BVal) (i : Time) (tx : Tx) (bs : List Bool) (w : W)
    (hpos : 0 < i) (hfresh : ∀ q ∈ P, q.1 < tx.base) (htimes : StructTimesLE P (i - 1))
    (hroot : ∃ r, P.get? root = some r ∧ p.keyMax < r.level) (hH : KeyHistOK p P)
    (hl : ViewLinksOK tx.base p (view (treeSpec p) P (i - 1)))
    (hP : PointersOK P)
    (he : execW p tx i (view (treeSpec p) P (i - 1)) = .ok (bs, w))
    (hbook : Book tx.base { p := p, i := i, view := rootless (view (treeSpec p) P (i - 1)) } w)
    (_htaken : TakenAbove tx.base w)
    (hK : KindsAllOK p P) (hKW : KindCache (kindOracleOf p P) w) :
    KindsAllOK p (P.apply i (changesOf i w)) := by
  intro x nd' hx hd hlv c y hk ny' hy
  rcases apply_keyNode p P i tx bs w hpos hfresh htimes hroot hH hl he x nd' hx hd hlv with
    ⟨n, hlook, _, _, hks, _⟩ | ⟨hPx, _⟩
  · have hmem := mem_ids_of_lookup w.nodes x n hlook
    have hxg : x ∈ (w.gh.map (·.1)).reverse := by
      rw [← hbook.ids]
      exact List.mem_map.mpr ⟨(x, n), hmem, rfl⟩
    obtain ⟨⟨x', g, h⟩, hgh, hx'⟩ := List.mem_map.mp (List.mem_reverse.mp hxg)
    have hxx : x' = x := hx'
    rw [hxx] at hgh
    obtain ⟨_, _, hg, hh⟩ := kindsStep_gh p P i tx bs w hfresh htimes he hbook x g h hgh nd' hx
    have hkk := hKW x n g h hmem hgh c y (by rw [← hks]; exact hk)
    subst hg
    subst hh
    obtain ⟨hk1, hk2⟩ := hkk
    refine ⟨fun h0 => ?_, fun h0 => ⟨fun h7 => ?_, fun h7 => ?_⟩⟩
    · exact kindsStep_keySeg p P i tx bs w hfresh htimes he hbook y _ (hk1 h0) ny' hy
    · exact kindsStep_keySeg p P i tx bs w hfresh htimes he hbook y _ ((hk2 h0).1 h7) ny' hy
    · exact kindsStep_valId p P i tx bs w hfresh he y ((hk2 h0).2 h7) ny' hy
  · obtain ⟨ny, hPy⟩ := kindsStep_ptr P hP x nd' hPx c y hk
    obtain ⟨h1, h2⟩ := kindsStep_old P i _ y ny ny' hPy hy
    rw [h1, h2]
    exact hK x nd' hPx hd hlv c y hk ny hPy

/-! ## 3. The view's premise and the first structure -/

/-- The view at t of a structure without later entries, with pointers to its
nodes and `KindsAllOK`, meets `ViewKinds` for the oracle of the structure. -/
theorem viewKinds_of (p : Params) (P : Struct BVal) (t : Time) (B : NodeId)
    (hfresh : ∀ q ∈ P, q.1 < B) (htimes : StructTimesLE P t) (hP : PointersOK P)
    (hK : KindsAllOK p P) :
    ViewKinds (kindOracleOf p P) B { p := p, i := t + 1, view := rootless (view (treeSpec p) P t) } := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro y g ⟨ny, hy, _, _, _⟩
    exact hfresh _ (mem_of_get? hy)
  · rintro y ⟨ny, hy, _⟩
    exact hfresh _ (mem_of_get? hy)
  · rintro y g g' ⟨ny, hy, _, _, hg⟩ ⟨ny', hy', _, _, hg'⟩
    rw [hy] at hy'
    obtain rfl := Option.some.inj hy'
    rw [← hg, ← hg']
  · rintro y g ⟨ny, hy, hd, _, _⟩ ⟨ny', hy', hd'⟩
    rw [hy] at hy'
    obtain rfl := Option.some.inj hy'
    rw [hd] at hd'
    cases hd'
  · intro x nd hv hd hlv
    exact ⟨nd, view_eq_get? p P t htimes x nd (rootless_some_eq _ x nd hv), hd, hlv, rfl⟩
  · intro x nd hv hd hlv cv y hk
    have hx := view_eq_get? p P t htimes x nd (rootless_some_eq _ x nd hv)
    obtain ⟨ny, hy⟩ := kindsStep_ptr P hP x nd hx cv y hk
    have hr := hK x nd hx hd hlv cv y hk ny hy
    refine ⟨fun h0 => ?_, fun h0 => ⟨fun h7 => ?_, fun h7 => ?_⟩⟩
    · obtain ⟨a, b, c⟩ := hr.1 h0
      exact ⟨ny, hy, a, b, c⟩
    · obtain ⟨a, b, c⟩ := (hr.2 h0).1 h7
      exact ⟨ny, hy, a, b, c⟩
    · exact ⟨ny, hy, (hr.2 h0).2 h7⟩

/-- The first structure: its only key node, a segment leaf, has no key
klong. -/
theorem kindsAllOK_init (p : Params) : KindsAllOK p (initStruct p) := by
  intro x nd hx hd hlv c y hk
  rcases mem_init p (x, nd) (mem_of_get? hx) with h | h | h
  · simp only [Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    simp only [Params.rootLevel] at hlv
    omega
  · simp only [Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    have hz : klongsOf [(⟨0, marker⟩ : Entry BVal)] = [Klong.time 0] := by decide
    simp only [hz, List.mem_singleton, reduceCtorEq] at hk
  · simp only [Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    simp only [Params.topLevel] at hlv
    omega

/-! ## 4. What the walk reads -/

/-- For a live klong of a key node of P that names a node of P, the walk's
kind tests but the height's: an inner node's child is a key node of its
segment; a segment leaf's child is a key node of the next segment for a
long segment, a value otherwise. -/
theorem kindsAllOK_live (p : Params) (P : Struct BVal) (t : Time) (hK : KindsAllOK p P)
    (x : NodeId) (nd : Node BVal) (hx : P.get? x = some nd) (hd : nd.isData = false)
    (hl : nd.level ≤ p.keyMax) (c : Nat) (y : NodeId) (hc : (c, y) ∈ (nodeK p nd).liveAt t)
    (ny : Node BVal) (hy : P.get? y = some ny) :
    (p.heightOf nd.level ≠ 0 → ny.isData = false ∧ p.segOf ny.level = p.segOf nd.level) ∧
    (p.heightOf nd.level = 0 →
      (segLen c = 7 → ny.isData = false ∧ p.segOf ny.level = p.segOf nd.level + 1) ∧
      (segLen c ≠ 7 → ny.isData = true)) := by
  have hk : Klong.key c y ∈ klongsOf nd.hist := KNode.liveAt_key_mem _ t c y hc
  have hr := hK x nd hx hd hl c y hk ny hy
  refine ⟨fun h0 => ?_, fun h0 => ⟨fun h7 => ?_, fun h7 => (hr.2 h0).2 h7⟩⟩
  · obtain ⟨a, _, b⟩ := hr.1 h0
    exact ⟨a, b⟩
  · obtain ⟨a, _, b⟩ := (hr.2 h0).1 h7
    exact ⟨a, b⟩

end SIS.Tree
