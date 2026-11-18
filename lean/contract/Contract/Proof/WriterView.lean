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
import Contract.Proof.BridgeInv

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

/-! ## 2. The view shows the key nodes reached -/

/-- Levels go down along the live klongs of the key nodes reached: a live klong
of a key node reached that names a key node names one of a lower level. (The
model follows a pointer only to a node of a lower level, `SIS.reachFrom`.) -/
def LevFalls (s : Tree) : Prop :=
  ∀ x ∈ reach s, ∀ n, s.obj x = some (.key n) → ∀ c y, (c, y) ∈ live n.ks →
    ∀ m, s.obj y = some (.key m) → m.level < n.level

/-! ### The model's live children of a key node of P -/

/-- One step of the fold of the model's `SIS.Tree.entriesOf` on the klongs ks. -/
def wvStep (ks : List MKlong) (acc : SIS.History BVal × Time × List Nat × Bool) (k : MKlong) :
    SIS.History BVal × Time × List Nat × Bool :=
  match k with
  | .time t =>
    (if acc.2.2.2 then acc.1 else acc.1 ++ [⟨acc.2.1, SIS.Tree.marker⟩], t, acc.2.2.1, false)
  | .key c y => (acc.1 ++ [⟨acc.2.1, .key c y⟩], acc.2.1, acc.2.2.1, true)
  | .del bits =>
    let new := bits.filter (fun b => !acc.2.2.1.contains b)
    let cs := (new.filterMap (fun b => match (ks[b]? : Option MKlong) with
      | some (.key c _) => some c
      | _ => none)).eraseDups.mergeSort (fun x y => decide (x ≤ y))
    (acc.1 ++ [⟨acc.2.1, .del cs⟩], acc.2.1, bits, true)

theorem tree_entriesOf_eq (ks : List MKlong) : SIS.Tree.entriesOf ks =
    let r := ks.foldl (wvStep ks) ([], 0, [], true)
    if r.2.2.2 then r.1 else r.1 ++ [⟨r.2.1, SIS.Tree.marker⟩] := rfl

/-- An entry that is not the empty delete, the model's marker. -/
def wvKeep (e : SIS.Entry BVal) : Bool :=
  match e.val with
  | .del [] => false
  | _ => true

theorem foldl_bstep_wvKeep : ∀ (h : SIS.History BVal) (st : SIS.Check.LState),
    h.foldl SIS.Check.bstep st = (h.filter wvKeep).foldl SIS.Check.bstep st
  | [], _ => rfl
  | e :: h, st => by
    cases hk : wvKeep e with
    | true =>
      rw [List.filter_cons_of_pos hk]
      simp only [List.foldl_cons]
      exact foldl_bstep_wvKeep h _
    | false =>
      rw [List.filter_cons_of_neg (by simp [hk])]
      simp only [List.foldl_cons]
      have hv : e.val = .del [] := by
        unfold wvKeep at hk
        split at hk
        · assumption
        · cases hk
      have : SIS.Check.bstep st e = st := by
        unfold SIS.Check.bstep
        rw [hv]
        rfl
      rw [this]
      exact foldl_bstep_wvKeep h st

theorem wvStep_sim (K : List MKlong)
    (hb : ∀ A bits B, K = A ++ .del bits :: B → ∀ j ∈ bits, j < A.length) :
    ∀ (L A C : List MKlong) (H : SIS.History BVal) (t : Time) (b : List Nat) (fl : Bool),
      K = A ++ L ++ C →
      (L.foldl (wvStep K) (H, t, b, fl)).1.filter wvKeep =
        H.filter wvKeep ++ (entriesFrom (A.map kOf) t b (L.map kOf)).filter wvKeep := by
  intro L
  induction L with
  | nil => intro A C H t b fl _; simp [entriesFrom]
  | cons k L ih =>
    intro A C H t b fl hK
    rw [List.foldl_cons]
    cases k with
    | time t' =>
      simp only [wvStep]
      rw [ih (A ++ [.time t']) C _ _ _ _ (by rw [hK]; simp)]
      simp only [List.map_append, List.map_cons, List.map_nil, kOf, entriesFrom]
      congr 1
      split <;> simp [wvKeep, SIS.Tree.marker]
    | key c y =>
      simp only [wvStep]
      rw [ih (A ++ [.key c y]) C _ _ _ _ (by rw [hK]; simp)]
      simp only [List.map_append, List.map_cons, List.map_nil, kOf, entriesFrom,
        List.filter_append, List.filter_cons, List.append_assoc]
      simp [wvKeep]
    | del bits =>
      simp only [wvStep]
      rw [ih (A ++ [.del bits]) C _ _ _ _ (by rw [hK]; simp)]
      simp only [List.map_append, List.map_cons, List.map_nil, kOf, entriesFrom,
        List.filter_append, List.filter_cons, List.append_assoc]
      have hj := hb A bits (L ++ C) (by rw [hK]; simp)
      have hcs : (List.filterMap (fun j => match (K[j]? : Option MKlong) with
          | some (.key c _) => some c
          | _ => none) (bits.filter (fun j => !b.contains j))) =
          (bits.filter (fun j => !b.contains j)).filterMap (cvAt (A.map kOf)) := by
        apply List.filterMap_congr
        intro j hjm
        have hjA := hj j (List.mem_filter.mp hjm).1
        rw [hK, List.append_assoc, List.getElem?_append_left hjA]
        unfold cvAt
        rw [List.getElem?_map]
        cases A[j]? with
        | none => rfl
        | some k => cases k <;> rfl
      rw [hcs]
      simp only [newCvs]
      split <;> rename_i h <;>
        simp only [h, ↓reduceIte, List.filter_nil, List.cons_append, List.nil_append,
          Bool.false_eq_true]

theorem blive_entriesOf_kOf (K : List MKlong) (hb : BmW (K.map kOf)) :
    SIS.Check.blive (SIS.Tree.entriesOf K) = SIS.Check.blive (entriesOf (K.map kOf)) := by
  have hb' : ∀ A bits B, K = A ++ .del bits :: B → ∀ j ∈ bits, j < A.length := by
    intro A bits B hK j hj
    have := (hb (A.map kOf) bits (B.map kOf) (by rw [hK]; simp [kOf])).1 j hj
    simpa using this
  have hs := wvStep_sim K hb' K [] [] [] 0 [] true (by simp)
  rw [SIS.Check.blive_eq, SIS.Check.blive_eq, foldl_bstep_wvKeep, foldl_bstep_wvKeep
    (entriesOf _), tree_entriesOf_eq]
  simp only at hs ⊢
  congr 2
  split
  · rw [hs]
    rfl
  · rw [List.filter_append, hs]
    simp [wvKeep, SIS.Tree.marker]
    rfl

/-- The key nodes that the tree reaches from its space root are reachable in
the model's structure at time t, if the space root is: P holds the tree, P's
key nodes have well-formed klongs that give their histories, no entry of P is
after t, levels go down, and the key nodes reached have well-formed klongs
with W5 (`AllWf` for the nodes reached; `mem_blive_entriesOf` needs it). -/
theorem reachable_of_holds {p : MParams} {P : Struct BVal} {t : Time} {s : Tree}
    (hS : Holds p P s) (hH : SIS.Tree.KeyHistOK p P) (htimes : SIS.Tree.StructTimesLE P t)
    (hlev : LevFalls s)
    (hwf : ∀ x ∈ reach s, ∀ n, s.obj x = some (.key n) →
      klongsWf n.ks = true ∧ fullOk n.ks = true)
    (hr : ∀ r, s.root = some r → SIS.reachable (SIS.Tree.treeSpec p) P t r = true) :
    ∀ x ∈ reach s, ∀ n, s.obj x = some (.key n) →
      SIS.reachable (SIS.Tree.treeSpec p) P t x = true := by
  -- One step: a live klong of a key node reached and reachable names a reachable node.
  have hstep : ∀ x n, x ∈ reach s → s.obj x = some (.key n) →
      SIS.Reach (SIS.Tree.treeSpec p) P t x → ∀ c y m, (c, y) ∈ live n.ks →
      s.obj y = some (.key m) → SIS.Reach (SIS.Tree.treeSpec p) P t y := by
    intro x n hx hn hrx c y m hcy hm
    obtain ⟨nd, hnd, hd, hlv, hmax, hk⟩ := hS x n hn
    obtain ⟨ndy, hndy, _, hlvy, _, _⟩ := hS y m hm
    have hlt := hlev x hx n hn c y hcy m hm
    obtain ⟨hw, hf⟩ := hwf x hx n hn
    have hH' := hH x nd hnd hd (by rw [hlv]; exact hmax)
    have hb : BmW ((SIS.Tree.klongsOf nd.hist).map kOf) := by
      rw [hk]
      exact (wf5_of _ hw hf).bmW
    refine SIS.Reach.child hrx hnd ?_ hndy (by rw [hlvy, hlv]; exact hlt)
    show y ∈ SIS.Check.blive (nd.hist.upTo t)
    rw [SIS.Tree.upTo_eq_self _ _ (htimes _ (SIS.mem_of_get? hnd)), ← hH'.2,
      blive_entriesOf_kOf _ hb, hk]
    exact (mem_blive_entriesOf n.ks hw hf y).mpr ⟨c, hcy⟩
  -- The walk: every key node that `reachAt` lists from a reachable node is reachable.
  have hwalk : ∀ f x, (∀ z ∈ reachAt s f x, z ∈ reach s) →
      (∀ n, s.obj x = some (.key n) → SIS.Reach (SIS.Tree.treeSpec p) P t x) →
      ∀ z ∈ reachAt s f x, ∀ n, s.obj z = some (.key n) →
        SIS.Reach (SIS.Tree.treeSpec p) P t z := by
    intro f
    induction f with
    | zero =>
      intro x _ hx z hz n hn
      simp only [reachAt, List.mem_singleton] at hz
      subst hz
      exact hx n hn
    | succ f ih =>
      intro x hsub hx z hz n hn
      have hxr : x ∈ reach s := hsub x (by simp [reachAt])
      simp only [reachAt, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact hx n hn
      · cases hxo : s.obj x with
        | none =>
          rw [hxo] at hz
          cases hz
        | some o =>
          cases o with
          | val v =>
            rw [hxo] at hz
            cases hz
          | key nx =>
            rw [hxo] at hz
            obtain ⟨⟨c, y⟩, hcy, hz⟩ := List.mem_flatMap.mp hz
            have hsuby : ∀ w ∈ reachAt s f y, w ∈ reach s := fun w hw => hsub w (by
              simp only [reachAt, List.mem_cons, hxo, List.mem_flatMap]
              exact Or.inr ⟨(c, y), hcy, hw⟩)
            exact ih y hsuby (fun m hm => hstep x nx hxr hxo (hx nx hxo) c y m hcy hm) z hz n hn
  intro x hx n hn
  rw [SIS.reachable_iff]
  cases hroot : s.root with
  | none => simp [reach, hroot] at hx
  | some r =>
    have hreach : reach s = reachAt s (s.fuel r) r := by simp [reach, hroot]
    rw [hreach] at hx
    exact hwalk (s.fuel r) r (fun z hz => hreach ▸ hz)
      (fun _ _ => (SIS.reachable_iff _ _ _ _).mp (hr r hroot)) x hx n hn

/-- `Shows.key` for the model's own view: the view of P at time i - 1, without
the root, shows each key node that the tree reaches, if the model reaches it. -/
theorem shows_key_of_holds {p : MParams} {P : Struct BVal} {i : Time} {s : Tree}
    (hS : Holds p P s) (htimes : SIS.Tree.StructTimesLE P (i - 1))
    (hroot : ∃ r, P.get? SIS.root = some r ∧ p.keyMax < r.level)
    (hbal : Balanced p s)
    (hreach : ∀ x ∈ reach s, ∀ n, s.obj x = some (.key n) →
      SIS.reachable (SIS.Tree.treeSpec p) P (i - 1) x = true) :
    ∀ x ∈ reach s, ∀ n, s.obj x = some (.key n) → ∃ nd,
      SIS.Tree.rootless (SIS.view (SIS.Tree.treeSpec p) P (i - 1)) x = some nd ∧
      nd.isData = false ∧ nd.level = n.level ∧ n.level ≤ p.keyMax ∧
      (SIS.Tree.klongsOf nd.hist).map kOf = n.ks ∧ n.leaf = (p.heightOf n.level == 0) := by
  intro x hx n hn
  obtain ⟨nd, hnd, hd, hlv, hmax, hk⟩ := hS x n hn
  have hup : nd.hist.upTo (i - 1) = nd.hist :=
    SIS.Tree.upTo_eq_self _ _ (htimes _ (SIS.mem_of_get? hnd))
  have hxr : x ≠ SIS.root := by
    intro hxr
    obtain ⟨r, hr, hrl⟩ := hroot
    rw [hxr, hr] at hnd
    cases hnd
    omega
  refine ⟨nd, ?_, hd, hlv, hmax, hk, (hbal x hx n hn).2.1⟩
  have hxr' : (x == SIS.root) = false := by simpa using hxr
  simp only [SIS.Tree.rootless, hxr', Bool.false_eq_true, ↓reduceIte, SIS.view,
    hreach x hx n hn, hnd, Option.map_some, hup]

end Contract
