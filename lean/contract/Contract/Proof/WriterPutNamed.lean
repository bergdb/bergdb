/-
The contract package (bergdb 030-10): a put gives `SNamed` back. Every key
klong of every key node of the map after a put names a node of the map, if it
was so before: no step of a put takes a node away from the map, and every
node the put writes has key klongs that are klongs of a node it read, or name
a node it made, or the klongs given by the step below (`ins`), which name
nodes of the map (`putKv_put_named`). Then a transaction of puts meets the
writer's contract and gives `SNamed` back (`writerMeets_put_named`), and a
run of puts that asks `SNamed` of its start tree only is a history that meets
`MeetsTop` (`runs_meetsTop_puts`).

The walk over the put's code: the descents read the map without changing
it (the put's `PInv` holds there); after them the writes, with the invariant
`NInv` (`SNamed` of the map, the ids from the next one on are free, the key
access path is of nodes of the overlay) and the steps' relation `NGrow`.
-/
import Contract.Proof.WriterPutAll

namespace Contract

open SIS (View)
open SIS.Check (BVal)

/-! ## 1. Live klongs are key klongs -/

theorem wputn_liveWith_mem (del : List Nat) : ∀ (l : List (Klong × Nat)) (m : List (Nat × NodeId))
    (a : Nat × NodeId),
    a ∈ l.foldl (fun m (ki : Klong × Nat) => match ki with
      | (k, i) => match k with
        | .key c y => if del.contains i then m else insertCv c y m
        | _ => m) m →
    a ∈ m ∨ ∃ i, (Klong.key a.1 a.2, i) ∈ l
  | [], m, a, h => Or.inl h
  | (k, i) :: r, m, a, h => by
    simp only [List.foldl_cons] at h
    rcases wputn_liveWith_mem del r _ a h with h1 | ⟨i', h1⟩
    · cases k with
      | time t => exact Or.inl h1
      | del b => exact Or.inl h1
      | key c y =>
        simp only at h1
        split at h1
        · exact Or.inl h1
        · rcases mem_insertCv h1 with h2 | h2
          · right
            refine ⟨i, ?_⟩
            rw [h2]
            exact List.mem_cons_self
          · exact Or.inl h2
    · exact Or.inr ⟨i', List.mem_cons_of_mem _ h1⟩

/-- A live klong is a key klong of the node. -/
theorem wputn_live_mem_key {ks : List Klong} {c : Nat} {y : NodeId} (h : (c, y) ∈ live ks) :
    Klong.key c y ∈ ks := by
  unfold live liveWith at h
  rcases wputn_liveWith_mem (lastBitmap ks) ks.zipIdx [] (c, y) h with h1 | ⟨i, h1⟩
  · simp at h1
  · obtain ⟨hlt, heq⟩ := List.mem_zipIdx' h1
    have h2 : Klong.key c y = ks[i] := heq
    rw [h2]
    exact List.getElem_mem hlt

/-! ## 2. The invariant of the walk and the steps' relation -/

/-- The key klongs ks name nodes of the map of w. -/
def NPtrs (i : Time) (s : Tree) (w : MW) (ks : List Klong) : Prop :=
  ∀ c y, Klong.key c y ∈ ks → ((treeOf i s w).obj y).isSome = true

/-- What the walk keeps: `SNamed` of the map; the ids from the next one on
are free; the key access path is of nodes of the overlay, kept. -/
structure NInv (i : Time) (s : Tree) (w : MW) : Prop where
  named : SNamed (treeOf i s w)
  fresh : ∀ z, w.next ≤ z → w.nodes.lookup z = none ∧ w.vals.lookup z = none ∧
    w.taken.contains z = false ∧ s.obj z = none ∧ ∀ m ∈ w.made, m.id ≠ z
  path : ∀ (e : Nat) (c : Option Nat) (u : NodeId), w.path[e]? = some (c, u) →
    (w.nodes.lookup u).isSome = true ∧ w.taken.contains u = false

/-- A step from w to w': the nodes of the map and of the overlay stay, the
next id grows, the path and the nodes taken back stay. -/
structure NGrow (i : Time) (s : Tree) (w w' : MW) : Prop where
  obj : ∀ y, ((treeOf i s w).obj y).isSome = true → ((treeOf i s w').obj y).isSome = true
  look : ∀ y, (w.nodes.lookup y).isSome = true → (w'.nodes.lookup y).isSome = true
  next : w.next ≤ w'.next
  path : w'.path = w.path
  taken : w'.taken = w.taken

theorem NGrow.refl (i : Time) (s : Tree) (w : MW) : NGrow i s w w :=
  ⟨fun _ h => h, fun _ h => h, Nat.le_refl _, rfl, rfl⟩

theorem NGrow.trans {i : Time} {s : Tree} {w1 w2 w3 : MW} (h1 : NGrow i s w1 w2)
    (h2 : NGrow i s w2 w3) : NGrow i s w1 w3 :=
  ⟨fun y h => h2.obj y (h1.obj y h), fun y h => h2.look y (h1.look y h),
    Nat.le_trans h1.next h2.next, h2.path.trans h1.path, h2.taken.trans h1.taken⟩

theorem NPtrs.mono {i : Time} {s : Tree} {w w' : MW} {ks : List Klong} (h : NPtrs i s w ks)
    (hg : NGrow i s w w') : NPtrs i s w' ks :=
  fun c y hy => hg.obj y (h c y hy)

/-- `SNamed` after a change: every key node is one of before with its klongs,
or its klongs name nodes of before; and no node goes away. -/
theorem wputn_named_transfer {T T' : Tree} (hT : SNamed T)
    (hsome : ∀ y, (T.obj y).isSome = true → (T'.obj y).isSome = true)
    (hkey : ∀ z m', T'.obj z = some (.key m') →
      (∃ m, T.obj z = some (.key m) ∧ m.ks = m'.ks) ∨
        (∀ c y, Klong.key c y ∈ m'.ks → (T.obj y).isSome = true)) : SNamed T' := by
  intro z m' hz c y hy
  rcases hkey z m' hz with ⟨m, hm, hks⟩ | hp
  · exact hsome y (hT z m hm c y (hks ▸ hy))
  · exact hsome y (hp c y hy)

/-- The klongs of a node of the overlay, kept, name nodes of the map. -/
theorem wputn_ptrs_overlay {i : Time} {s : Tree} {w : MW} {x : NodeId} {n : MNode}
    (hI : NInv i s w) (hx : w.nodes.lookup x = some n) (ht : w.taken.contains x = false) :
    NPtrs i s w (ksOf n) :=
  fun c y hy => hI.named x _ (treeOf_obj_overlay i s hx ht) c y hy

/-- A state with the same nodes, values and nodes taken back has the map of
the same nodes and klongs. -/
theorem wputn_obj_same {i : Time} {s : Tree} {w w' : MW} (h1 : w'.nodes = w.nodes)
    (h2 : w'.vals = w.vals) (h3 : w'.taken = w.taken) (y : NodeId) :
    (((treeOf i s w).obj y).isSome = true → ((treeOf i s w').obj y).isSome = true) ∧
      ∀ m', (treeOf i s w').obj y = some (.key m') →
        ∃ m, (treeOf i s w).obj y = some (.key m) ∧ m.ks = m'.ks := by
  simp only [treeOf, h1, h2, h3]
  split
  · simp
  · split
    · next n hn =>
      refine ⟨fun _ => rfl, fun m' hm => ?_⟩
      simp only [Option.some.injEq, Obj.key.injEq] at hm
      exact ⟨_, rfl, by rw [← hm]⟩
    · exact ⟨id, fun m' hm => ⟨m', hm, rfl⟩⟩

/-- A step that leaves the nodes, values and nodes taken back as they are,
the path too, and keeps or raises the next id. -/
theorem wputn_same {i : Time} {s : Tree} {w w' : MW} (hI : NInv i s w)
    (h1 : w'.nodes = w.nodes) (h2 : w'.vals = w.vals) (h3 : w'.taken = w.taken)
    (h4 : w'.path = w.path) (h5 : w.next ≤ w'.next)
    (h6 : ∀ m ∈ w'.made, m ∈ w.made ∨ m.id < w'.next) : NInv i s w' ∧ NGrow i s w w' := by
  have hs := wputn_obj_same (i := i) (s := s) h1 h2 h3
  refine ⟨⟨wputn_named_transfer hI.named (fun y => (hs y).1)
    (fun z m' hz => Or.inl ((hs z).2 m' hz)), fun z hz => ?_, fun e c u hu => ?_⟩,
    ⟨fun y => (hs y).1, fun y h => by rw [h1]; exact h, h5, h4, h3⟩⟩
  · obtain ⟨a1, a2, a3, a4, a5⟩ := hI.fresh z (Nat.le_trans h5 hz)
    refine ⟨by rw [h1]; exact a1, by rw [h2]; exact a2, by rw [h3]; exact a3, a4, ?_⟩
    intro m hm
    rcases h6 m hm with hm | hm
    · exact a5 m hm
    · omega
  · rw [h4] at hu
    rw [h1, h3]
    exact hI.path e c u hu

/-! ## 3. The steps -/

/-- `putNode` of a node of the overlay with klongs that name nodes of the map
(if it is kept). -/
theorem wputn_put {i : Time} {s : Tree} {w : MW} {x : NodeId} {n' : MNode} (hI : NInv i s w)
    (hx : (w.nodes.lookup x).isSome = true)
    (hp : w.taken.contains x = false → NPtrs i s w (ksOf n')) :
    NInv i s (w.withNode x n') ∧ NGrow i s w (w.withNode x n') := by
  have hxn : x < w.next := by
    by_contra hc
    have := (hI.fresh x (Nat.le_of_not_lt hc)).1
    rw [this] at hx
    cases hx
  have hlook : ∀ y, (w.nodes.lookup y).isSome = true →
      ((w.withNode x n').nodes.lookup y).isSome = true := by
    intro y hy
    by_cases e : y = x
    · subst e
      rw [MW.withNode, lookup_upsert_self]
      rfl
    · rw [MW.withNode, lookup_upsert_ne _ _ e]
      exact hy
  have hmap : SNamed (treeOf i s (w.withNode x n')) ∧ ∀ y, ((treeOf i s w).obj y).isSome = true →
      ((treeOf i s (w.withNode x n')).obj y).isSome = true := by
    cases ht : w.taken.contains x
    · rw [treeOf_withNode i s n' ht]
      refine ⟨wputn_named_transfer hI.named (fun y h => wput_set_isSome h) (fun z m' hz => ?_),
        fun y h => wput_set_isSome h⟩
      by_cases e : z = x
      · subst e
        simp only [Tree.set, ite_true, Option.some.injEq, Obj.key.injEq] at hz
        subst hz
        exact Or.inr (hp ht)
      · left
        refine ⟨m', ?_, rfl⟩
        simpa [Tree.set, e] using hz
    · have heq : treeOf i s (w.withNode x n') = treeOf i s w := by
        apply prim_tree_ext
        · intro y
          by_cases e : y = x
          · subst e
            unfold treeOf
            simp only [MW.withNode, ht, ↓reduceIte]
          · simp only [treeOf, MW.withNode, lookup_upsert_ne _ _ e]
            rfl
        · rfl
      rw [heq]
      exact ⟨hI.named, fun y h => h⟩
  refine ⟨⟨hmap.1, fun z hz => ?_, fun e c u hu => ?_⟩, ⟨hmap.2, hlook, Nat.le_refl _, rfl, rfl⟩⟩
  · have hnx : (w.withNode x n').next = w.next := rfl
    obtain ⟨a1, a2, a3, a4, a5⟩ := hI.fresh z (by omega)
    refine ⟨?_, a2, a3, a4, a5⟩
    have : z ≠ x := by omega
    rw [MW.withNode, lookup_upsert_ne _ _ this]
    exact a1
  · obtain ⟨h1, h2⟩ := hI.path e c u hu
    exact ⟨hlook u h1, h2⟩

/-- `newKey` with klongs that name nodes of the map. -/
theorem wputn_newKey {i : Time} {s : Tree} (c : SIS.Tree.Ctx) {w : MW} (hI : NInv i s w)
    (g h : Nat) (leaf : Bool) (ks : List MKlong) (hks : NPtrs i s w (ks.map kOf)) :
    WP (SIS.Tree.newKey g h leaf ks) c w (fun r w' => NInv i s w' ∧ NGrow i s w w' ∧
      r = w.next ∧ w'.nodes.lookup r = some ⟨leaf, ks⟩ ∧
      ((treeOf i s w').obj r).isSome = true ∧ w'.next = w.next + 2) := by
  intro r w' hr
  rw [newKey_eq] at hr
  simp only [Except.ok.injEq, Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl⟩ := hr
  obtain ⟨hn, hv, ht, hs, hm⟩ := hI.fresh w.next (Nat.le_refl _)
  have hT := treeOf_afterNewKey i s c.p g h leaf ks hs hn ht hm
  have hlk : (w.afterNewKey c.p g h leaf ks).nodes.lookup w.next = some ⟨leaf, ks⟩ :=
    prim_lookup_append_self _ _ hn
  have hlook : ∀ y, (w.nodes.lookup y).isSome = true →
      ((w.afterNewKey c.p g h leaf ks).nodes.lookup y).isSome = true := by
    intro y hy
    obtain ⟨n, hn'⟩ := Option.isSome_iff_exists.mp hy
    rw [MW.afterNewKey, prim_lookup_append_some _ hn']
    rfl
  refine ⟨⟨?_, fun z hz => ?_, fun e c' u hu => ?_⟩, ⟨fun y hy => ?_, hlook,
    Nat.le_add_right _ 2, rfl, rfl⟩, rfl, hlk, ?_, rfl⟩
  · rw [hT]
    refine wputn_named_transfer hI.named (fun y hy => wput_set_isSome hy) (fun z m' hz => ?_)
    by_cases e : z = w.next
    · subst e
      simp only [Tree.set, ite_true, Option.some.injEq, Obj.key.injEq] at hz
      subst hz
      exact Or.inr hks
    · left
      refine ⟨m', ?_, rfl⟩
      simpa [Tree.set, e] using hz
  · have hz' : w.next ≤ z := by
      have : (w.afterNewKey c.p g h leaf ks).next = w.next + 2 := rfl
      omega
    obtain ⟨a1, a2, a3, a4, a5⟩ := hI.fresh z hz'
    have hzn : z ≠ w.next := by
      have : (w.afterNewKey c.p g h leaf ks).next = w.next + 2 := rfl
      omega
    refine ⟨?_, a2, a3, a4, fun m hm' => ?_⟩
    · rw [MW.afterNewKey, prim_lookup_append_ne _ _ hzn]
      exact a1
    · simp only [MW.afterNewKey, List.mem_append, List.mem_singleton] at hm'
      rcases hm' with hm' | rfl
      · exact a5 m hm'
      · exact Ne.symm hzn
  · obtain ⟨h1, h2⟩ := hI.path e c' u hu
    exact ⟨hlook u h1, h2⟩
  · rw [hT]
    exact wput_set_isSome hy
  · rw [hT]
    simp [Tree.set]

/-- `newValue`. -/
theorem wputn_newValue {i : Time} {s : Tree} (c : SIS.Tree.Ctx) {w : MW} (hI : NInv i s w)
    (h : Nat) :
    WP (SIS.Tree.newValue h) c w (fun r w' => NInv i s w' ∧ NGrow i s w w' ∧ r = w.next ∧
      ((treeOf i s w').obj r).isSome = true ∧ w'.nodes = w.nodes ∧ w'.next = w.next + 2) := by
  intro r w' hr
  rw [newValue_eq] at hr
  simp only [Except.ok.injEq, Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl⟩ := hr
  obtain ⟨hn, hv, ht, hs, hm⟩ := hI.fresh w.next (Nat.le_refl _)
  have hT := treeOf_afterNewValue i s h hn hv ht
  refine ⟨⟨?_, fun z hz => ?_, fun e c' u hu => hI.path e c' u hu⟩,
    ⟨fun y hy => ?_, fun y hy => hy, Nat.le_add_right _ 2, rfl, rfl⟩, rfl, ?_, rfl, rfl⟩
  · rw [hT]
    refine wputn_named_transfer hI.named (fun y hy => wput_set_isSome hy) (fun z m' hz => ?_)
    by_cases e : z = w.next
    · subst e
      simp [Tree.set] at hz
    · left
      refine ⟨m', ?_, rfl⟩
      simpa [Tree.set, e] using hz
  · have hz' : w.next ≤ z := by
      have : (w.afterNewValue h).next = w.next + 2 := rfl
      omega
    obtain ⟨a1, a2, a3, a4, a5⟩ := hI.fresh z hz'
    have hzn : z ≠ w.next := by
      have : (w.afterNewValue h).next = w.next + 2 := rfl
      omega
    refine ⟨a1, ?_, a3, a4, fun m hm' => ?_⟩
    · rw [MW.afterNewValue, prim_lookup_append_ne _ _ hzn]
      exact a2
    · simp only [MW.afterNewValue, List.mem_append, List.mem_singleton] at hm'
      rcases hm' with hm' | rfl
      · exact a5 m hm'
      · exact Ne.symm hzn
  · rw [hT]
    exact wput_set_isSome hy
  · rw [hT]
    simp [Tree.set]

/-- `newSuperRoot`. -/
theorem wputn_newSuperRoot {i : Time} {s : Tree} (c : SIS.Tree.Ctx) {w : MW} (hI : NInv i s w)
    (y : NodeId) : WP (SIS.Tree.newSuperRoot y) c w (fun _ w' => NInv i s w' ∧ NGrow i s w w') := by
  intro r w' hr
  by_cases hi : c.i = w.top.time
  · rw [newSuperRoot_inPlace_eq c w y hi] at hr
    simp only [Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨-, rfl⟩ := hr
    exact wputn_same hI rfl rfl rfl rfl (Nat.le_refl _) (fun m hm => Or.inl hm)
  · rw [newSuperRoot_new_eq c w y hi] at hr
    simp only [Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨-, rfl⟩ := hr
    refine wputn_same hI rfl rfl rfl rfl (Nat.le_add_right _ 2) (fun m hm => ?_)
    simp only [MW.superRootNew, List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | rfl
    · exact Or.inl hm
    · right
      show w.next < w.next + 2
      omega

/-! ## 4. Klongs of the nodes written -/

theorem wputn_mkey {n : MNode} {c : Nat} {y : NodeId} :
    Klong.key c y ∈ ksOf n ↔ SIS.Tree.Klong.key c y ∈ n.ks :=
  ⟨prim_key_mem_ksOf, fun h => List.mem_map_of_mem (f := kOf) h⟩

/-- The pointers of the halves of a space split: those of the last version,
and those of the klongs added. -/
theorem wputn_halves_ptrs {leaf : Bool} {t : Time} {last : MNode} {ins : List (Nat × NodeId)}
    {f s2 : MNode} {sc : Nat} (hh : SIS.Tree.halves leaf t last ins = (f, s2, sc)) (c : Nat)
    (y : NodeId) (hm : SIS.Tree.Klong.key c y ∈ f.ks ∨ SIS.Tree.Klong.key c y ∈ s2.ks) :
    (∃ c', SIS.Tree.Klong.key c' y ∈ last.ks) ∨ (∃ c', (c', y) ∈ ins) := by
  have hb : ∀ k ∈ last.ks.drop 1, k ∈ last.ks := fun k hk => List.mem_of_mem_drop hk
  have hins : ∀ (P : Nat × NodeId → Bool),
      SIS.Tree.Klong.key c y ∈ ins.map (fun (cy : Nat × NodeId) =>
        if P cy = true then SIS.Tree.Klong.key 0 cy.2 else SIS.Tree.Klong.key cy.1 cy.2) →
      ∃ c', (c', y) ∈ ins := by
    intro P h
    obtain ⟨⟨c0, y0⟩, hm0, he⟩ := List.mem_map.mp h
    simp only at he
    split at he
    · simp only [SIS.Tree.Klong.key.injEq] at he
      exact ⟨c0, by rw [← he.2]; exact hm0⟩
    · simp only [SIS.Tree.Klong.key.injEq] at he
      exact ⟨c0, by rw [← he.2]; exact hm0⟩
  simp only [SIS.Tree.halves] at hh
  split_ifs at hh
  all_goals
    simp only [Prod.mk.injEq] at hh
    obtain ⟨rfl, rfl, -⟩ := hh
    simp only [List.mem_cons, List.mem_append, reduceCtorEq, false_or, or_assoc] at hm
    rcases hm with hm | hm | hm
  all_goals first
    | exact Or.inl ⟨c, hb _ (List.mem_of_mem_take hm)⟩
    | exact Or.inl ⟨c, hb _ (List.mem_of_mem_drop hm)⟩
    | exact Or.inr (hins _ hm)
    | (split at hm
       · next c1 y1 r heq =>
         have hd : ∀ k, k ∈ SIS.Tree.Klong.key c1 y1 :: r → k ∈ last.ks := fun k hk =>
           hb _ (List.mem_of_mem_drop (heq ▸ hk))
         rcases List.mem_cons.mp hm with hm | hm
         · simp only [SIS.Tree.Klong.key.injEq] at hm
           refine Or.inl ⟨c1, hd _ ?_⟩
           rw [hm.2]
           exact List.mem_cons_self
         · exact Or.inl ⟨c, hd _ (List.mem_cons_of_mem _ hm)⟩
       · exact Or.inl ⟨c, hb _ (List.mem_of_mem_drop hm)⟩)

/-- A node cut back to an earlier time keeps some of its klongs. -/
theorem wputn_toPrev_mem {n : MNode} {t : Time} {k : Klong} (h : k ∈ ksOf (n.toPrev t)) :
    k ∈ ksOf n := by
  rw [ksOf_toPrev] at h
  exact (List.takeWhile_sublist _).subset h

/-! ## 5. The recursion up the path -/

/-- The nodes of the overlay off the path, of ids below the next one, keep
their nodes. -/
def NOff (w w' : MW) : Prop :=
  ∀ y : NodeId, (∀ (e : Nat) (c : Option Nat), w.path[e]? ≠ some (c, y)) → y < w.next →
    w'.nodes.lookup y = w.nodes.lookup y

theorem NOff.refl (w : MW) : NOff w w := fun _ _ _ => rfl

theorem NOff.trans {w1 w2 w3 : MW} (h1 : NOff w1 w2) (h2 : NOff w2 w3) (hp : w2.path = w1.path)
    (hn : w1.next ≤ w2.next) : NOff w1 w3 := by
  intro y hy hyn
  rw [h2 y (by rw [hp]; exact hy) (by omega), h1 y hy hyn]

/-- The step up: given klongs that name nodes of the map, for a node on the
path, it keeps `NInv`, grows, and keeps the nodes off the path. -/
def UpN (p : MParams) (i : Time) (s : Tree) (v : View BVal)
    (up : NodeId → List (Nat × NodeId) → SIS.Tree.M Unit) : Prop :=
  ∀ (q : NodeId) (ins : List (Nat × NodeId)) (w : MW), NInv i s w →
    (∃ (e : Nat) (c : Option Nat), w.path[e]? = some (c, q)) →
    (∀ cy ∈ ins, ((treeOf i s w).obj cy.2).isSome = true) →
    WP (up q ins) { p := p, i := i, view := v } w
      (fun _ w' => NInv i s w' ∧ NGrow i s w w' ∧ NOff w w')

/-- The walk from w0 to w: `NInv` at w, grown, and the nodes off the path
kept. -/
structure NAt (i : Time) (s : Tree) (w0 w : MW) : Prop where
  inv : NInv i s w
  grow : NGrow i s w0 w
  off : NOff w0 w

theorem NAt.start {i : Time} {s : Tree} {w : MW} (hI : NInv i s w) : NAt i s w w :=
  ⟨hI, NGrow.refl _ _ _, NOff.refl _⟩

theorem NAt.same {i : Time} {s : Tree} {w0 w w' : MW} (hA : NAt i s w0 w)
    (h1 : w'.nodes = w.nodes) (h2 : w'.vals = w.vals) (h3 : w'.taken = w.taken)
    (h4 : w'.path = w.path) (h5 : w.next ≤ w'.next)
    (h6 : ∀ m ∈ w'.made, m ∈ w.made ∨ m.id < w'.next) : NAt i s w0 w' := by
  obtain ⟨hI', hG⟩ := wputn_same hA.inv h1 h2 h3 h4 h5 h6
  exact ⟨hI', hA.grow.trans hG, fun y hy hyn => by rw [h1]; exact hA.off y hy hyn⟩

theorem NAt.put {i : Time} {s : Tree} {w0 w : MW} {x : NodeId} {n' : MNode} (hA : NAt i s w0 w)
    (hx : (w.nodes.lookup x).isSome = true)
    (hp : w.taken.contains x = false → NPtrs i s w (ksOf n'))
    (hxo : (∃ (e : Nat) (c : Option Nat), w0.path[e]? = some (c, x)) ∨ w0.next ≤ x) :
    NAt i s w0 (w.withNode x n') := by
  obtain ⟨hI', hG⟩ := wputn_put hA.inv hx hp
  refine ⟨hI', hA.grow.trans hG, fun y hy hyn => ?_⟩
  have hyx : y ≠ x := by
    rcases hxo with ⟨e, c, he⟩ | h
    · intro e'
      exact hy e c (e' ▸ he)
    · omega
  rw [MW.withNode, lookup_upsert_ne _ _ hyx]
  exact hA.off y hy hyn

theorem NAt.up {i : Time} {s : Tree} {w0 w w' : MW} (hA : NAt i s w0 w)
    (h : NInv i s w' ∧ NGrow i s w w' ∧ NOff w w') : NAt i s w0 w' :=
  ⟨h.1, hA.grow.trans h.2.1, NOff.trans hA.off h.2.2 hA.grow.path hA.grow.next⟩

/-! ### The steps of the walk, in the form of a bind -/

theorem wputn_put_end {c : SIS.Tree.Ctx} {w : MW} {x : NodeId} {n' : MNode}
    {post : Unit → MW → Prop} (h : post () (w.withNode x n')) :
    WP (SIS.Tree.putNode x n') c w post := by
  intro r w' hr
  rw [putNode_eq] at hr
  simp only [Except.ok.injEq, Prod.mk.injEq] at hr
  obtain ⟨-, rfl⟩ := hr
  exact h

theorem wputn_ghOf_none {α : Type} {c : SIS.Tree.Ctx} {w : MW} {x : NodeId} {n : MNode}
    {k : Nat × Nat → SIS.Tree.M α} {post : α → MW → Prop} (hn : w.nodes.lookup x = some n)
    (hg : w.gh.lookup x = none) : WP (SIS.Tree.ghOf x >>= k) c w post := by
  rw [wp_bind]
  unfold SIS.Tree.ghOf
  refine wput_ok (getNode_hit _ hn) ?_
  rw [wp_bind, wp_get]
  simp only [hg]
  exact wp_throw _ _ _ _

theorem wputn_pathNode_none {α : Type} {c : SIS.Tree.Ctx} {w : MW} {d : Nat}
    {k : NodeId → SIS.Tree.M α} {post : α → MW → Prop} (hp : w.path[d]? = none) :
    WP (SIS.Tree.pathNode d >>= k) c w post := by
  rw [wp_bind]
  unfold SIS.Tree.pathNode
  rw [wp_bind, wp_get]
  simp only [hp]
  exact wp_throw _ _ _ _

theorem nw_same {α β : Type} {i : Time} {s : Tree} {f : SIS.Tree.M α} {g : α → SIS.Tree.M β}
    {c : SIS.Tree.Ctx} {w0 w w' : MW} {a : α} {post : β → MW → Prop} (hA : NAt i s w0 w)
    (hf : f c w = .ok (a, w')) (h1 : w'.nodes = w.nodes) (h2 : w'.vals = w.vals)
    (h3 : w'.taken = w.taken) (h4 : w'.path = w.path) (h5 : w'.next = w.next)
    (h6 : w'.made = w.made) (hk : NAt i s w0 w' → NGrow i s w w' → WP (g a) c w' post) :
    WP (f >>= g) c w post := by
  refine wput_ok hf ?_
  obtain ⟨hI', hG⟩ := wputn_same hA.inv h1 h2 h3 h4 (by rw [h5]) (fun m hm => Or.inl (h6 ▸ hm))
  exact hk ⟨hI', hA.grow.trans hG, fun y hy hyn => by rw [h1]; exact hA.off y hy hyn⟩ hG

theorem nw_note {β : Type} {i : Time} {s : Tree} {g : Unit → SIS.Tree.M β} {c : SIS.Tree.Ctx}
    {w0 w : MW} {post : β → MW → Prop} (t : String) (hA : NAt i s w0 w)
    (hk : ∀ w', NAt i s w0 w' → NGrow i s w w' → WP (g ()) c w' post) :
    WP (SIS.Tree.note t >>= g) c w post :=
  nw_same hA (note_eq c w t) rfl rfl rfl rfl rfl rfl (hk _)

theorem nw_setMadeFor {β : Type} {i : Time} {s : Tree} {g : Unit → SIS.Tree.M β}
    {c : SIS.Tree.Ctx} {w0 w : MW} {post : β → MW → Prop} (m : NodeId) (o : Option NodeId)
    (hA : NAt i s w0 w) (hk : ∀ w', NAt i s w0 w' → NGrow i s w w' → WP (g ()) c w' post) :
    WP (SIS.Tree.setMadeFor m o >>= g) c w post := by
  cases o with
  | none => exact nw_same hA (setMadeFor_none c w m) rfl rfl rfl rfl rfl rfl (hk _)
  | some o => exact nw_same hA (setMadeFor_some c w m o) rfl rfl rfl rfl rfl rfl (hk _)

theorem nw_replacedBy {β : Type} {i : Time} {s : Tree} {g : Option NodeId → SIS.Tree.M β}
    {c : SIS.Tree.Ctx} {w0 w : MW} {post : β → MW → Prop} (x : NodeId) (hA : NAt i s w0 w)
    (hk : ∀ o w', NAt i s w0 w' → NGrow i s w w' → WP (g o) c w' post) :
    WP (SIS.Tree.replacedBy x >>= g) c w post :=
  nw_same hA (replacedBy_eq c w x) rfl rfl rfl rfl rfl rfl (hk _ _)

theorem nw_pure {α β : Type} {i : Time} {s : Tree} {g : α → SIS.Tree.M β} {c : SIS.Tree.Ctx}
    {w0 w : MW} {post : β → MW → Prop} (a : α) (hA : NAt i s w0 w)
    (hk : NAt i s w0 w → WP (g a) c w post) : WP (pure a >>= g) c w post :=
  wput_ok (f := pure a) (a := a) (w' := w) rfl (hk hA)

theorem nw_newKey {β : Type} {i : Time} {s : Tree} {g : NodeId → SIS.Tree.M β}
    {c : SIS.Tree.Ctx} {w0 w : MW} {post : β → MW → Prop} (gg h : Nat) (leaf : Bool)
    (ks : List MKlong) (hA : NAt i s w0 w) (hks : NPtrs i s w (ks.map kOf))
    (hk : NAt i s w0 (w.afterNewKey c.p gg h leaf ks) →
      NGrow i s w (w.afterNewKey c.p gg h leaf ks) →
      ((treeOf i s (w.afterNewKey c.p gg h leaf ks)).obj w.next).isSome = true →
      ((w.afterNewKey c.p gg h leaf ks).nodes.lookup w.next).isSome = true →
      w0.next ≤ w.next → WP (g w.next) c (w.afterNewKey c.p gg h leaf ks) post) :
    WP (SIS.Tree.newKey gg h leaf ks >>= g) c w post := by
  refine wput_ok (newKey_eq c w gg h leaf ks) ?_
  obtain ⟨hI', hG, -, hlk, hobj, -⟩ := wputn_newKey (i := i) (s := s) c hA.inv gg h leaf ks hks
    w.next _ (newKey_eq _ w gg h leaf ks)
  refine hk ⟨hI', hA.grow.trans hG, fun y hy hyn => ?_⟩ hG hobj (by rw [hlk]; rfl)
    hA.grow.next
  have hyn' : y ≠ w.next := by
    have := hA.grow.next
    omega
  rw [MW.afterNewKey, prim_lookup_append_ne _ _ hyn']
  exact hA.off y hy hyn

theorem nw_put {β : Type} {i : Time} {s : Tree} {g : Unit → SIS.Tree.M β} {c : SIS.Tree.Ctx}
    {w0 w : MW} {post : β → MW → Prop} {x : NodeId} {n' : MNode} (hA : NAt i s w0 w)
    (hx : (w.nodes.lookup x).isSome = true)
    (hp : w.taken.contains x = false → NPtrs i s w (ksOf n'))
    (hxo : (∃ (e : Nat) (c : Option Nat), w0.path[e]? = some (c, x)) ∨ w0.next ≤ x)
    (hk : NAt i s w0 (w.withNode x n') → NGrow i s w (w.withNode x n') →
      WP (g ()) c (w.withNode x n') post) :
    WP (SIS.Tree.putNode x n' >>= g) c w post := by
  refine wput_ok (putNode_eq c w x n') ?_
  have hA' := hA.put hx hp hxo
  exact hk hA' (wputn_put hA.inv hx hp).2

theorem nw_newSuperRoot {β : Type} {i : Time} {s : Tree} {g : Unit → SIS.Tree.M β}
    {c : SIS.Tree.Ctx} {w0 w : MW} {post : β → MW → Prop} (y : NodeId) (hA : NAt i s w0 w)
    (hk : ∀ w', NAt i s w0 w' → NGrow i s w w' → WP (g ()) c w' post) :
    WP (SIS.Tree.newSuperRoot y >>= g) c w post := by
  rw [wp_bind]
  intro r w' hr
  obtain ⟨hI', hG⟩ := wputn_newSuperRoot (i := i) (s := s) c hA.inv y r w' hr
  have hnodes : w'.nodes = w.nodes := by
    by_cases hi : c.i = w.top.time
    · rw [newSuperRoot_inPlace_eq c w y hi] at hr
      simp only [Except.ok.injEq, Prod.mk.injEq] at hr
      rw [← hr.2]
      rfl
    · rw [newSuperRoot_new_eq c w y hi] at hr
      simp only [Except.ok.injEq, Prod.mk.injEq] at hr
      rw [← hr.2]
      rfl
  exact hk w' ⟨hI', hA.grow.trans hG, fun y hy hyn => by rw [hnodes]; exact hA.off y hy hyn⟩ hG

theorem nw_klongAt {β : Type} {g : Nat → SIS.Tree.M β} {c : SIS.Tree.Ctx}
    {w : MW} {post : β → MW → Prop} (d : Nat) (hk : ∀ k, WP (g k) c w post) :
    WP (SIS.Tree.klongAt d >>= g) c w post := by
  rw [wp_bind]
  unfold SIS.Tree.klongAt
  rw [wp_bind, wp_get]
  split
  · rw [wp_pure]
    exact hk _
  · exact wp_throw _ _ _ _

theorem nw_up {β : Type} {p : MParams} {i : Time} {s : Tree} {v : View BVal}
    {up : NodeId → List (Nat × NodeId) → SIS.Tree.M Unit} {g : Unit → SIS.Tree.M β} {w0 w : MW}
    {post : β → MW → Prop} (hup : UpN p i s v up) {q : NodeId} {ins : List (Nat × NodeId)}
    (hA : NAt i s w0 w) (hq : ∃ (e : Nat) (c : Option Nat), w0.path[e]? = some (c, q))
    (hins : ∀ cy ∈ ins, ((treeOf i s w).obj cy.2).isSome = true)
    (hk : ∀ w', NAt i s w0 w' → WP (g ()) { p := p, i := i, view := v } w' post) :
    WP (up q ins >>= g) { p := p, i := i, view := v } w post := by
  rw [wp_bind]
  refine (hup q ins w hA.inv (by rw [hA.grow.path]; exact hq) hins).mono ?_
  intro _ w' h
  exact hk w' (hA.up h)

theorem nw_maybe_note {β : Type} {i : Time} {s : Tree} {K : SIS.Tree.M β} {c : SIS.Tree.Ctx}
    {w0 w : MW} {post : β → MW → Prop} (b : Bool) (t : String) (hA : NAt i s w0 w)
    (hk : ∀ w', NAt i s w0 w' → NGrow i s w w' → WP K c w' post) :
    WP (if b = true then (SIS.Tree.note t >>= fun _ => K) else K) c w post := by
  split
  · exact nw_note t hA hk
  · exact hk w hA (NGrow.refl _ _ _)

/-- `handleFullWith` keeps `NInv`, grows, and keeps the nodes off the path,
for a node x on the path with klongs `ins` and a last version `last` whose
klongs name nodes of the map. -/
theorem wputn_handleFull {p : MParams} {i : Time} {s : Tree} {v : View BVal}
    {up : NodeId → List (Nat × NodeId) → SIS.Tree.M Unit} {depth : Nat} {x : NodeId}
    {ins : List (Nat × NodeId)} {last : MNode} {compact : Bool} {w : MW}
    (hI : NInv i s w) (hxp : ∃ (e : Nat) (c : Option Nat), w.path[e]? = some (c, x))
    (hl : ∃ l : List (Nat × NodeId), l.Pairwise CvLt ∧
      ksOf last = Klong.time i :: l.map (fun cy => Klong.key cy.1 cy.2) ∧
      ∀ cy ∈ l, ((treeOf i s w).obj cy.2).isSome = true)
    (hins : ∀ cy ∈ ins, ((treeOf i s w).obj cy.2).isSome = true) (hup : UpN p i s v up) :
    WP (SIS.Tree.handleFullWith up depth x ins last compact) { p := p, i := i, view := v } w
      (fun _ w' => NInv i s w' ∧ NGrow i s w w' ∧ NOff w w') := by
  obtain ⟨e0, c0, hx0⟩ := hxp
  obtain ⟨hxs, hxt⟩ := hI.path e0 c0 x hx0
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hxs
  obtain ⟨l, hls, hlk, hlp⟩ := hl
  have hA0 := NAt.start hI
  have hxo : ∃ (e : Nat) (c : Option Nat), w.path[e]? = some (c, x) := ⟨e0, c0, hx0⟩
  have hlastP : ∀ c y, SIS.Tree.Klong.key c y ∈ last.ks →
      ((treeOf i s w).obj y).isSome = true := by
    intro c y hy
    have hy' : Klong.key c y ∈ ksOf last := wputn_mkey.mpr hy
    rw [hlk] at hy'
    simp only [List.mem_cons, reduceCtorEq, false_or, List.mem_map, Klong.key.injEq] at hy'
    obtain ⟨cy, hcy, -, rfl⟩ := hy'
    exact hlp cy hcy
  have hinsP : ∀ c y, (c, y) ∈ ins → ((treeOf i s w).obj y).isSome = true :=
    fun c y h => hins (c, y) h
  have hhalf : ∀ w', NAt i s w w' →
      NPtrs i s w' (ksOf (SIS.Tree.halves n.leaf i last ins).1) ∧
        NPtrs i s w' (ksOf (SIS.Tree.halves n.leaf i last ins).2.1) := by
    intro w' hA
    have key : ∀ c y, SIS.Tree.Klong.key c y ∈ (SIS.Tree.halves n.leaf i last ins).1.ks ∨
        SIS.Tree.Klong.key c y ∈ (SIS.Tree.halves n.leaf i last ins).2.1.ks →
        ((treeOf i s w').obj y).isSome = true := by
      intro c y hm
      rcases wputn_halves_ptrs (f := (SIS.Tree.halves n.leaf i last ins).1)
        (s2 := (SIS.Tree.halves n.leaf i last ins).2.1)
        (sc := (SIS.Tree.halves n.leaf i last ins).2.2) rfl c y hm with ⟨c', h⟩ | ⟨c', h⟩
      · exact hA.grow.obj y (hlastP c' y h)
      · exact hA.grow.obj y (hinsP c' y h)
    exact ⟨fun c y hy => key c y (Or.inl (wputn_mkey.mp hy)),
      fun c y hy => key c y (Or.inr (wputn_mkey.mp hy))⟩
  have hfin : ∀ w', NAt i s w w' →
      WP (SIS.Tree.getNode x >>= fun n' => SIS.Tree.putNode x (n'.toPrev (i - 1)))
        { p := p, i := i, view := v } w'
        (fun _ w'' => NInv i s w'' ∧ NGrow i s w w'' ∧ NOff w w'') := by
    intro w' hA
    obtain ⟨n', hn'⟩ := Option.isSome_iff_exists.mp (hA.grow.look x hxs)
    refine wput_ok (getNode_hit _ hn') (wputn_put_end ?_)
    have hA' := hA.put (n' := n'.toPrev (i - 1)) (by rw [hn']; rfl)
      (fun ht c y hy => wputn_ptrs_overlay hA.inv hn' ht c y
        (wputn_toPrev_mem hy)) (Or.inl hxo)
    exact ⟨hA'.inv, hA'.grow, hA'.off⟩
  unfold SIS.Tree.handleFullWith
  refine wput_read (wput_ok (getNode_hit _ hn) ?_)
  cases hg : w.gh.lookup x with
  | none => exact wputn_ghOf_none hn hg
  | some gh =>
  obtain ⟨g, h⟩ := gh
  refine wput_ok (ghOf_hit _ hn hg) ?_
  have hxobj : ((treeOf i s w).obj x).isSome = true := by
    rw [treeOf_obj_overlay i s hn hxt]
    rfl
  have hnoks : ∀ (w' : MW), NPtrs i s w' (([] : List MKlong).map kOf) := by
    intro w' c y hy
    simp at hy
  have hend : ∀ (b : Bool) (w' : MW), NAt i s w w' →
      WP (if b = true then (SIS.Tree.getNode x >>= fun n' => SIS.Tree.putNode x (n'.toPrev (i - 1)))
        else pure ()) { p := p, i := i, view := v } w'
        (fun _ w'' => NInv i s w'' ∧ NGrow i s w w'' ∧ NOff w w'') := by
    intro b w' hA
    split
    · exact hfin w' hA
    · rw [wp_pure]
      exact ⟨hA.inv, hA.grow, hA.off⟩
  have hts : ∀ (w' : MW), NAt i s w w' → ∃ r, SIS.Tree.replaceOrAdd last ins
      { p := p, i := i, view := v } w' = .ok (r, w') ∧ NPtrs i s w' (ksOf r) := by
    intro w' hA
    obtain ⟨r, hro, -, -, -, -, -, -, -, hptr⟩ :=
      replaceOrAdd_spec { p := p, i := i, view := v } w' hls hlk ins
    refine ⟨r, hro, fun c y hy => ?_⟩
    rcases hptr c y hy with h1 | h1
    · exact hA.grow.obj y (hlp (c, y) h1)
    · exact hA.grow.obj y (hins (c, y) h1)
  dsimp only
  cases depth with
  | zero =>
    refine wput_ok (parentAt_zero _ _) ?_
    dsimp only
    cases compact
    · simp only [Bool.not_false, Bool.true_and, Bool.false_eq_true, ↓reduceIte]
      refine nw_pure _ hA0 (fun _ => ?_)
      split
      · refine nw_same hA0 rfl rfl rfl rfl rfl rfl rfl (fun hA1 _ => ?_)
        split
        · refine nw_newKey _ _ _ _ hA1 (hnoks _) (fun hA2 _ hsec hsecL hle2 => ?_)
          refine nw_replacedBy _ hA2 (fun o w3 hA3 hG3 => ?_)
          refine nw_setMadeFor _ _ hA3 (fun w4 hA4 hG4 => ?_)
          refine nw_put hA4 (hA4.grow.look x hxs) (fun _ => (hhalf _ hA4).1) (Or.inl hxo)
            (fun hA5 hG5 => ?_)
          refine nw_put hA5 (hG5.look _ (hG4.look _ (hG3.look _ hsecL)))
            (fun _ => (hhalf _ hA5).2) (Or.inr hle2) (fun hA6 hG6 => ?_)
          refine nw_note _ hA6 (fun w7 hA7 hG7 => ?_)
          refine nw_newKey _ _ _ _ hA7 ?_ (fun hA8 _ _ _ _ => ?_)
          · intro c' y hy
            simp only [List.map, kOf, List.mem_cons, reduceCtorEq, Klong.key.injEq,
              List.not_mem_nil, or_false, false_or] at hy
            rcases hy with ⟨-, rfl⟩ | ⟨-, rfl⟩
            · exact hA7.grow.obj _ hxobj
            · exact hG7.obj _ (hG6.obj _ (hG5.obj _ (hG4.obj _ (hG3.obj _ hsec))))
          refine nw_replacedBy _ hA8 (fun o' w9 hA9 _ => ?_)
          refine nw_setMadeFor _ _ hA9 (fun w10 hA10 _ => ?_)
          refine nw_newSuperRoot _ hA10 (fun w11 hA11 _ => ?_)
          exact hend _ w11 hA11
        · refine nw_newKey _ _ _ _ hA1 (hnoks _) (fun hA2 _ hf hfL hle2 => ?_)
          refine nw_newKey _ _ _ _ hA2 (hnoks _) (fun hA3 hG3 hs2 hs2L hle3 => ?_)
          refine nw_setMadeFor _ _ hA3 (fun w4 hA4 hG4 => ?_)
          refine nw_setMadeFor _ _ hA4 (fun w5 hA5 hG5 => ?_)
          refine nw_note _ hA5 (fun w6 hA6 hG6 => ?_)
          refine nw_newKey _ _ _ _ hA6 (hnoks _) (fun hA7 hG7 hr hrL hle7 => ?_)
          refine nw_setMadeFor _ _ hA7 (fun w8 hA8 hG8 => ?_)
          have hfL8 := hG8.look _ (hG7.look _ (hG6.look _ (hG5.look _ (hG4.look _
            (hG3.look _ hfL)))))
          have hf8 := hG8.obj _ (hG7.obj _ (hG6.obj _ (hG5.obj _ (hG4.obj _ (hG3.obj _ hf)))))
          have hs8L := hG8.look _ (hG7.look _ (hG6.look _ (hG5.look _ (hG4.look _ hs2L))))
          have hs8 := hG8.obj _ (hG7.obj _ (hG6.obj _ (hG5.obj _ (hG4.obj _ hs2))))
          have hr8L := hG8.look _ hrL
          refine nw_put hA8 hfL8 (fun _ => (hhalf _ hA8).1) (Or.inr hle2) (fun hA9 hG9 => ?_)
          refine nw_put hA9 (hG9.look _ hs8L) (fun _ => (hhalf _ hA9).2) (Or.inr hle3)
            (fun hA10 hG10 => ?_)
          refine nw_put hA10 (hG10.look _ (hG9.look _ hr8L)) ?_ (Or.inr hle7)
            (fun hA11 _ => ?_)
          · intro _ c' y hy
            simp only [ksOf, List.map, kOf, List.mem_cons, reduceCtorEq, Klong.key.injEq,
              List.not_mem_nil, or_false, false_or] at hy
            rcases hy with ⟨-, rfl⟩ | ⟨-, rfl⟩
            · exact hG10.obj _ (hG9.obj _ hf8)
            · exact hG10.obj _ (hG9.obj _ hs8)
          refine nw_newSuperRoot _ hA11 (fun w12 hA12 _ => ?_)
          exact hend _ w12 hA12
      · split
        · refine nw_note _ hA0 (fun w1 hA1 _ => ?_)
          obtain ⟨r, hro, hrp⟩ := hts w1 hA1
          refine wput_ok hro ?_
          refine nw_maybe_note _ _ hA1 (fun w2 hA2 hG2 => ?_)
          refine nw_put hA2 (hA2.grow.look x hxs) (fun _ => hrp.mono hG2) (Or.inl hxo)
            (fun hA3 _ => ?_)
          exact hend _ _ hA3
        · obtain ⟨r, hro, hrp⟩ := hts w hA0
          refine wput_ok hro ?_
          refine nw_maybe_note _ _ hA0 (fun w2 hA2 hG2 => ?_)
          refine nw_newKey _ _ _ _ hA2 (hrp.mono hG2) (fun hA3 _ _ _ _ => ?_)
          refine nw_setMadeFor _ _ hA3 (fun w4 hA4 _ => ?_)
          refine nw_note _ hA4 (fun w5 hA5 _ => ?_)
          refine nw_newSuperRoot _ hA5 (fun w6 hA6 _ => ?_)
          exact hend _ w6 hA6
    · simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      refine nw_pure _ hA0 (fun _ => ?_)
      refine nw_note _ hA0 (fun w1 hA1 _ => ?_)
      split
      · refine nw_note _ hA1 (fun w2 hA2 _ => ?_)
        obtain ⟨r, hro, hrp⟩ := hts w2 hA2
        refine wput_ok hro ?_
        refine nw_maybe_note _ _ hA2 (fun w3 hA3 hG3 => ?_)
        refine nw_put hA3 (hA3.grow.look x hxs) (fun _ => hrp.mono hG3) (Or.inl hxo)
          (fun hA4 _ => ?_)
        exact hend _ _ hA4
      · obtain ⟨r, hro, hrp⟩ := hts w1 hA1
        refine wput_ok hro ?_
        refine nw_maybe_note _ _ hA1 (fun w2 hA2 hG2 => ?_)
        refine nw_newKey _ _ _ _ hA2 (hrp.mono hG2) (fun hA3 _ _ _ _ => ?_)
        refine nw_setMadeFor _ _ hA3 (fun w4 hA4 _ => ?_)
        refine nw_note _ hA4 (fun w5 hA5 _ => ?_)
        refine nw_newSuperRoot _ hA5 (fun w6 hA6 _ => ?_)
        exact hend _ w6 hA6
  | succ d =>
    cases hpd : w.path[d]? with
    | none =>
      rw [wp_bind]
      unfold SIS.Tree.parentAt
      exact wputn_pathNode_none hpd
    | some e =>
      refine wput_ok (parentAt_succ _ hpd) ?_
      obtain ⟨hqs, hqt⟩ := hI.path d e.1 e.2 hpd
      have hqo : ∃ (e' : Nat) (c : Option Nat), w.path[e']? = some (c, e.2) := ⟨d, e.1, hpd⟩
      obtain ⟨pn, hpn⟩ := Option.isSome_iff_exists.mp hqs
      dsimp only
      refine wput_ok (getNode_hit _ hpn) ?_
      have hT2 : ∀ (w1 : MW), NAt i s w w1 →
          WP (SIS.Tree.replaceOrAdd last ins >>= fun l =>
            if (l.size == 1) = true then (SIS.Tree.note "lone-time-klong" >>= fun _ =>
              SIS.Tree.newKey g h n.leaf l.ks >>= fun y => SIS.Tree.setMadeFor y (some x) >>=
              fun _ => SIS.Tree.note "split.time1" >>= fun _ => SIS.Tree.klongAt (d + 1) >>=
              fun k1 => up e.2 [(k1, y)] >>= fun _ =>
              if (!n.firstTime == some i) = true then (SIS.Tree.getNode x >>= fun n' =>
                SIS.Tree.putNode x (n'.toPrev (i - 1))) else pure ())
            else (SIS.Tree.newKey g h n.leaf l.ks >>= fun y => SIS.Tree.setMadeFor y (some x) >>=
              fun _ => SIS.Tree.note "split.time1" >>= fun _ => SIS.Tree.klongAt (d + 1) >>=
              fun k1 => up e.2 [(k1, y)] >>= fun _ =>
              if (!n.firstTime == some i) = true then (SIS.Tree.getNode x >>= fun n' =>
                SIS.Tree.putNode x (n'.toPrev (i - 1))) else pure ()))
            { p := p, i := i, view := v } w1
            (fun _ w'' => NInv i s w'' ∧ NGrow i s w w'' ∧ NOff w w'') := by
        intro w1 hA1
        obtain ⟨r, hro, hrp⟩ := hts w1 hA1
        refine wput_ok hro ?_
        refine nw_maybe_note _ _ hA1 (fun w2 hA2 hG2 => ?_)
        refine nw_newKey _ _ _ _ hA2 (hrp.mono hG2) (fun hA3 _ hy _ _ => ?_)
        refine nw_setMadeFor _ _ hA3 (fun w4 hA4 hG4 => ?_)
        refine nw_note _ hA4 (fun w5 hA5 hG5 => ?_)
        refine nw_klongAt _ (fun k1 => ?_)
        refine nw_up hup hA5 hqo ?_ (fun w6 hA6 => hend _ w6 hA6)
        intro cy hcy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hcy
        subst hcy
        exact hG5.obj _ (hG4.obj _ hy)
      have hT1 : ∀ (w1 : MW), NAt i s w w1 →
          WP (SIS.Tree.note "split.time.inplace" >>= fun _ => SIS.Tree.replaceOrAdd last ins >>=
            fun l => if (l.size == 1) = true then (SIS.Tree.note "lone-time-klong" >>= fun _ =>
              SIS.Tree.putNode x { leaf := n.leaf, ks := l.ks } >>= fun _ =>
              if (!n.firstTime == some i) = true then (SIS.Tree.getNode x >>= fun n' =>
                SIS.Tree.putNode x (n'.toPrev (i - 1))) else pure ())
            else (SIS.Tree.putNode x { leaf := n.leaf, ks := l.ks } >>= fun _ =>
              if (!n.firstTime == some i) = true then (SIS.Tree.getNode x >>= fun n' =>
                SIS.Tree.putNode x (n'.toPrev (i - 1))) else pure ()))
            { p := p, i := i, view := v } w1
            (fun _ w'' => NInv i s w'' ∧ NGrow i s w w'' ∧ NOff w w'') := by
        intro w1 hA1
        refine nw_note _ hA1 (fun w2 hA2 _ => ?_)
        obtain ⟨r, hro, hrp⟩ := hts w2 hA2
        refine wput_ok hro ?_
        refine nw_maybe_note _ _ hA2 (fun w3 hA3 hG3 => ?_)
        refine nw_put hA3 (hA3.grow.look x hxs) (fun _ => hrp.mono hG3) (Or.inl hxo)
          (fun hA4 _ => ?_)
        exact hend _ _ hA4
      cases compact
      · simp only [Bool.not_false, Bool.true_and, Bool.false_eq_true, ↓reduceIte]
        refine nw_pure _ hA0 (fun _ => ?_)
        split
        · refine nw_same hA0 rfl rfl rfl rfl rfl rfl rfl (fun hA1 _ => ?_)
          split
          · refine nw_newKey _ _ _ _ hA1 (hnoks _) (fun hA2 _ hsec hsecL hle2 => ?_)
            refine nw_replacedBy _ hA2 (fun o w3 hA3 hG3 => ?_)
            refine nw_setMadeFor _ _ hA3 (fun w4 hA4 hG4 => ?_)
            refine nw_put hA4 (hA4.grow.look x hxs) (fun _ => (hhalf _ hA4).1) (Or.inl hxo)
              (fun hA5 hG5 => ?_)
            refine nw_put hA5 (hG5.look _ (hG4.look _ (hG3.look _ hsecL)))
              (fun _ => (hhalf _ hA5).2) (Or.inr hle2) (fun hA6 hG6 => ?_)
            have hsec6 := hG6.obj _ (hG5.obj _ (hG4.obj _ (hG3.obj _ hsec)))
            split
            · refine nw_note _ hA6 (fun w7 hA7 hG7 => ?_)
              refine nw_newKey _ _ _ _ hA7 ?_ (fun hA8 hG8 hr _ _ => ?_)
              · intro c' y hy
                simp only [List.map, kOf, List.mem_cons, reduceCtorEq, Klong.key.injEq,
                  List.not_mem_nil, or_false, false_or] at hy
                rcases hy with ⟨-, rfl⟩ | ⟨-, rfl⟩
                · exact hA7.grow.obj _ hxobj
                · exact hG7.obj _ hsec6
              refine nw_replacedBy _ hA8 (fun o' w9 hA9 hG9 => ?_)
              refine nw_setMadeFor _ _ hA9 (fun w10 hA10 hG10 => ?_)
              refine nw_klongAt _ (fun k1 => ?_)
              obtain ⟨pn', hpn'⟩ := Option.isSome_iff_exists.mp (hA10.grow.look _ hqs)
              refine wput_ok (getNode_hit _ hpn') ?_
              split
              · next j hj =>
                split
                · rw [wp_bind]
                  exact wp_throw _ _ _ _
                · refine nw_put hA10 (by rw [hpn']; rfl) ?_ (Or.inl hqo) (fun hA11 _ => ?_)
                  · intro ht c' z hz
                    rcases repoint_key_mem hj hz with hz | ⟨-, rfl⟩
                    · exact wputn_ptrs_overlay hA10.inv hpn' ht c' z hz
                    · exact hG10.obj _ (hG9.obj _ hr)
                  exact hend _ _ hA11
              · rw [wp_bind]
                exact wp_throw _ _ _ _
            · refine nw_note _ hA6 (fun w7 hA7 hG7 => ?_)
              refine nw_up hup hA7 hqo ?_ (fun w8 hA8 => hend _ w8 hA8)
              intro cy hcy
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hcy
              subst hcy
              exact hG7.obj _ hsec6
          · refine nw_newKey _ _ _ _ hA1 (hnoks _) (fun hA2 _ hf hfL hle2 => ?_)
            refine nw_newKey _ _ _ _ hA2 (hnoks _) (fun hA3 hG3 hs2 hs2L hle3 => ?_)
            refine nw_setMadeFor _ _ hA3 (fun w4 hA4 hG4 => ?_)
            refine nw_setMadeFor _ _ hA4 (fun w5 hA5 hG5 => ?_)
            have hf5 := hG5.obj _ (hG4.obj _ (hG3.obj _ hf))
            have hf5L := hG5.look _ (hG4.look _ (hG3.look _ hfL))
            have hs5 := hG5.obj _ (hG4.obj _ hs2)
            have hs5L := hG5.look _ (hG4.look _ hs2L)
            split
            · refine nw_note _ hA5 (fun w6 hA6 hG6 => ?_)
              refine nw_newKey _ _ _ _ hA6 (hnoks _) (fun hA7 hG7 hr hrL hle7 => ?_)
              refine nw_setMadeFor _ _ hA7 (fun w8 hA8 hG8 => ?_)
              refine nw_put hA8 (hG8.look _ (hG7.look _ (hG6.look _ hf5L)))
                (fun _ => (hhalf _ hA8).1) (Or.inr hle2) (fun hA9 hG9 => ?_)
              refine nw_put hA9 (hG9.look _ (hG8.look _ (hG7.look _ (hG6.look _ hs5L))))
                (fun _ => (hhalf _ hA9).2) (Or.inr hle3) (fun hA10 hG10 => ?_)
              refine nw_put hA10 (hG10.look _ (hG9.look _ (hG8.look _ hrL))) ?_ (Or.inr hle7)
                (fun hA11 hG11 => ?_)
              · intro _ c' y hy
                simp only [ksOf, List.map, kOf, List.mem_cons, reduceCtorEq, Klong.key.injEq,
                  List.not_mem_nil, or_false, false_or] at hy
                rcases hy with ⟨-, rfl⟩ | ⟨-, rfl⟩
                · exact hG10.obj _ (hG9.obj _ (hG8.obj _ (hG7.obj _ (hG6.obj _ hf5))))
                · exact hG10.obj _ (hG9.obj _ (hG8.obj _ (hG7.obj _ (hG6.obj _ hs5))))
              refine nw_klongAt _ (fun k1 => ?_)
              refine nw_up hup hA11 hqo ?_ (fun w12 hA12 => hend _ w12 hA12)
              intro cy hcy
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hcy
              subst hcy
              exact hG11.obj _ (hG10.obj _ (hG9.obj _ (hG8.obj _ hr)))
            · refine nw_note _ hA5 (fun w6 hA6 hG6 => ?_)
              refine nw_put hA6 (hG6.look _ hf5L) (fun _ => (hhalf _ hA6).1) (Or.inr hle2)
                (fun hA7 hG7 => ?_)
              refine nw_put hA7 (hG7.look _ (hG6.look _ hs5L)) (fun _ => (hhalf _ hA7).2)
                (Or.inr hle3) (fun hA8 hG8 => ?_)
              refine nw_klongAt _ (fun k1 => ?_)
              refine nw_up hup hA8 hqo ?_ (fun w9 hA9 => hend _ w9 hA9)
              intro cy hcy
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hcy
              rcases hcy with rfl | rfl
              · exact hG8.obj _ (hG7.obj _ (hG6.obj _ hf5))
              · exact hG8.obj _ (hG7.obj _ (hG6.obj _ hs5))
        · split
          · exact hT1 w hA0
          · exact hT2 w hA0
      · simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        refine nw_pure _ hA0 (fun _ => ?_)
        refine nw_note _ hA0 (fun w1 hA1 _ => ?_)
        split
        · exact hT1 w1 hA1
        · exact hT2 w1 hA1

/-- One level of `appendKlongs` meets `UpN`, given the levels above it. -/
theorem wputn_append_step {p : MParams} {i : Time} {s : Tree} {v : View BVal} (depth : Nat)
    (hup : ∀ d, depth = d + 1 → UpN p i s v (fun q ins => SIS.Tree.appendKlongs d q ins)) :
    UpN p i s v (fun q ins => SIS.Tree.appendKlongs depth q ins) := by
  intro x ins w hI hxp hins
  obtain ⟨e0, c0, hx0⟩ := hxp
  obtain ⟨hxs, hxt⟩ := hI.path e0 c0 x hx0
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hxs
  have hxo : ∃ (e : Nat) (c : Option Nat), w.path[e]? = some (c, x) := ⟨e0, c0, hx0⟩
  have hl : ∃ l : List (Nat × NodeId), l.Pairwise CvLt ∧
      ksOf (n.lastVersion i) = Klong.time i :: l.map (fun cy => Klong.key cy.1 cy.2) ∧
      ∀ cy ∈ l, ((treeOf i s w).obj cy.2).isSome = true :=
    ⟨live (ksOf n), live_sorted _, lastVersion_ks i, fun cy hcy =>
      wputn_ptrs_overlay hI hn hxt cy.1 cy.2 (wputn_live_mem_key hcy)⟩
  simp only []
  rw [wput_appendKlongs_eq]
  refine wput_read (wput_ok (getNode_hit _ hn) ?_)
  dsimp only
  split
  · refine wputn_handleFull hI hxo hl hins ?_
    cases depth with
    | zero => exact fun _ _ _ _ _ _ => wp_throw _ _ _ _
    | succ d => exact hup d rfl
  · split
    · refine wputn_handleFull hI hxo hl hins ?_
      cases depth with
      | zero => exact fun _ _ _ _ _ _ => wp_throw _ _ _ _
      | succ d => exact hup d rfl
    · unfold SIS.Tree.addKeys
      refine wput_read (wput_ok (getNode_hit _ hn) (wputn_put_end ?_))
      have hA := (NAt.start hI).put (n' := addAll i n ins) (by rw [hn]; rfl)
        (fun ht c y hy => ?_) (Or.inl hxo)
      · exact ⟨hA.inv, hA.grow, hA.off⟩
      · rcases (addAll_key_mem ins n).mp hy with hy | hy
        · exact wputn_ptrs_overlay hI hn ht c y hy
        · exact hins (c, y) hy

/-- `appendKlongs` meets `UpN` at every depth. -/
theorem wputn_append {p : MParams} {i : Time} {s : Tree} {v : View BVal} :
    ∀ d, UpN p i s v (fun q ins => SIS.Tree.appendKlongs d q ins) := by
  intro d
  induction d with
  | zero => exact wputn_append_step 0 (fun d h => absurd h (by omega))
  | succ d ih =>
    exact wputn_append_step (d + 1) (fun d' h => by
      obtain rfl : d = d' := by omega
      exact ih)

/-! ## 6. The new segment leaves -/

/-- `setNode` with `create` on a new segment leaf y of the overlay with no
klongs: a new segment leaf y' with no klongs, linked from y. -/
theorem wputn_setNode_new {p : MParams} {i : Time} {s : Tree} {v : View BVal}
    (hp : ParamsOK p) {w : MW} {y : NodeId} (hI : NInv i s w)
    (hy : w.nodes.lookup y = some ⟨true, []⟩) (hyt : w.taken.contains y = false) (c : Nat) :
    WP (SIS.Tree.setNode y c true) { p := p, i := i, view := v } w
      (fun r w' => ∃ y', r = some y' ∧ NInv i s w' ∧ w'.nodes.lookup y' = some ⟨true, []⟩ ∧
        w'.taken.contains y' = false) := by
  unfold SIS.Tree.setNode
  refine wput_read ?_
  rw [wp_bind]
  dsimp only
  rw [wputs_fuel]
  refine (wputs_descend_leaf _ hy rfl c _).mono ?_
  rintro r w1 ⟨rfl, hw1⟩
  subst w1
  refine wput_ok (getNode_hit _ hy) ?_
  have hse : (⟨true, []⟩ : MNode).searchEq i c = none := rfl
  rw [hse]
  dsimp only
  cases hg : w.gh.lookup r with
  | none => exact wputn_ghOf_none hy hg
  | some gh =>
  obtain ⟨g, hh⟩ := gh
  refine wput_ok (ghOf_hit _ hy hg) ?_
  dsimp only
  refine wput_ok (note_eq _ _ _) ?_
  obtain ⟨hIN, -⟩ := wputn_same (w' := { w with trail := "segment.new" :: w.trail }) hI rfl rfl
    rfl rfl (Nat.le_refl _) (fun m hm => Or.inl hm)
  refine wput_ok (newKey_eq _ _ _ _ _ _) ?_
  obtain ⟨hIA, hGA, -, hlkA, hobjA, -⟩ := wputn_newKey (i := i) (s := s)
    { p := p, i := i, view := v } hIN (g + 1) 0 true [] (fun c' y' hy' => by simp at hy') _ _
    (newKey_eq _ _ _ _ _ _)
  have hrw : r < w.next := by
    by_contra hc
    have := (hI.fresh r (Nat.le_of_not_lt hc)).1
    rw [this] at hy
    cases hy
  have hrn : r ≠ w.next := Nat.ne_of_lt hrw
  have hyA := hGA.look r (by rw [hy]; rfl)
  split
  · refine wput_ok (putNode_eq _ _ _ _) ?_
    rw [wp_pure]
    rw [wputs_add_empty]
    obtain ⟨hIP, -⟩ := wputn_put (n' := ⟨true, [.time i, .key c w.next]⟩) hIA hyA
      (fun _ c' y' hy' => by
      simp only [ksOf, List.map, kOf, List.mem_cons, reduceCtorEq, Klong.key.injEq,
        List.not_mem_nil, or_false, false_or] at hy'
      rw [hy'.2]
      exact hobjA)
    refine ⟨w.next, rfl, hIP, ?_, ?_⟩
    · rw [MW.withNode, lookup_upsert_ne _ _ (Ne.symm hrn)]
      exact hlkA
    · exact (hI.fresh w.next (Nat.le_refl _)).2.2.1
  · next hc =>
    exfalso
    have := hp.size
    apply hc
    show 0 + 1 < p.M
    omega

/-- The rest of the key's segments from a new segment leaf y with no klongs:
a new segment leaf for each, the value's klong in the last; `NInv` is kept. -/
theorem wputn_chain {p : MParams} {i : Time} {s : Tree} {v : View BVal} (hp : ParamsOK p)
    {key : Key} {h : Nat} :
    ∀ (rest : Key) (w : MW) (y : NodeId), rest ≠ [] → NInv i s w →
      w.nodes.lookup y = some ⟨true, []⟩ → w.taken.contains y = false →
      WP (SIS.Tree.putSegs key (some h) rest y) { p := p, i := i, view := v } w
        (fun _ w' => NInv i s w')
  | [], _, _, hne, _, _, _ => absurd rfl hne
  | [c], w, y, _, hI, hy, hyt => by
    rw [SIS.Tree.putSegs.eq_2]
    refine (wputs_setValue_new hp hy c key h).mono ?_
    rintro _ w' rfl
    rw [wputs_add_empty]
    obtain ⟨hIV, -, -, hobj, hnodes, -⟩ := wputn_newValue (i := i) (s := s)
      { p := p, i := i, view := v } hI h w.next _ (newValue_eq _ w h)
    exact (wputn_put (n' := ⟨true, [.time i, .key c w.next]⟩) hIV (by rw [hnodes, hy]; rfl)
      (fun _ c' y' hy' => by
      simp only [ksOf, List.map, kOf, List.mem_cons, reduceCtorEq, Klong.key.injEq,
        List.not_mem_nil, or_false, false_or] at hy'
      rw [hy'.2]
      exact hobj)).1
  | c :: c2 :: r, w, y, _, hI, hy, hyt => by
    rw [SIS.Tree.putSegs.eq_3 _ _ _ _ _ (by simp), wp_bind]
    refine (wputn_setNode_new hp hI hy hyt c).mono ?_
    rintro _ w' ⟨y', rfl, hI', hy', hyt'⟩
    exact wputn_chain hp (c2 :: r) w' y' (by simp) hI' hy' hyt'

/-! ## 7. The descent and the put -/

/-- On the way down from node x, not read yet: the put's `PInv`; the map is
T0; x is sound; the path's nodes but the last are of the overlay, kept; the
last is x. -/
structure DInv (p : MParams) (i : Time) (base : NodeId) (s : Tree) (tp : Top)
    (C : List (Key × Nat)) (T0 : Tree) (w : MW) (x : NodeId) : Prop where
  inv : PInv p i base s tp none C w
  map : treeOf i s w = T0
  good : ∃ lo hi, Good T0 x lo hi
  path : ∀ (e : Nat) (c : Option Nat) (u : NodeId), w.path[e]? = some (c, u) →
    e + 1 < w.path.length → (w.nodes.lookup u).isSome = true ∧ w.taken.contains u = false
  last : ∃ c0, w.path[w.path.length - 1]? = some (c0, x)

/-- At a segment leaf L of the overlay that ends the path, the walk's
invariant holds. -/
theorem wputn_ninv_of {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {C : List (Key × Nat)} {T0 : Tree} (hb : Books i base s tp) (hn : SNamed T0) {w : MW}
    {L : NodeId} {nl : MNode} (hD : DInv p i base s tp C T0 w L)
    (hlk : w.nodes.lookup L = some nl) : NInv i s w := by
  obtain ⟨lo, hi, hGL⟩ := hD.good
  obtain ⟨m, hm⟩ := wput_good_obj hGL
  rw [← hD.map] at hm
  have hLt := wput_taken hm
  refine ⟨by rw [hD.map]; exact hn, fun z hz => ?_, fun e c u hu => ?_⟩
  · obtain ⟨-, a2, a3, a4, a5, a6⟩ := treeOf_fresh hb hD.inv.books hz
    exact ⟨a3, a4, a5, a2, a6⟩
  · obtain ⟨c0, hc0⟩ := hD.last
    have hlen : e < w.path.length := by
      by_contra hc
      rw [List.getElem?_eq_none (by omega)] at hu
      cases hu
    by_cases he : e + 1 < w.path.length
    · exact hD.path e c u hu he
    · have : e = w.path.length - 1 := by omega
      subst this
      rw [hc0] at hu
      cases hu
      exact ⟨by rw [hlk]; rfl, hLt⟩

/-- The descent keeps `DInv` and ends at a segment leaf of the overlay. -/
theorem wputn_descend {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {z : NodeId} {C : List (Key × Nat)} {T0 : Tree} {c : Nat}
    (hs : Shows p v z s tp) (hb : Books i base s tp) :
    ∀ (f : Nat) (w : MW) (x : NodeId), DInv p i base s tp C T0 w x →
      WP (SIS.Tree.descendLte c f x) { p := p, i := i, view := v } w
        (fun L w' => DInv p i base s tp C T0 w' L ∧
          ∃ nl, w'.nodes.lookup L = some nl ∧ nl.leaf = true) := by
  intro f
  induction f with
  | zero =>
    intro w x _
    rw [wput_descend_zero]
    exact wp_throw _ _ _ _
  | succ f ih =>
    intro w x hD
    rw [wput_descend_succ]
    refine wput_read ?_
    obtain ⟨lo, hi, hGx⟩ := hD.good
    obtain ⟨m, hxm⟩ := wput_good_obj hGx
    rw [← hD.map] at hxm
    obtain ⟨n, w1, hget, hks, hleaf, hlk1, hT1, hI1, hw1, -⟩ := getNode_spec hs hb hD.inv hxm
    refine wput_ok hget ?_
    have hfield : w1.path = w.path ∧ w1.taken = w.taken ∧
        ∀ u n0, w.nodes.lookup u = some n0 → w1.nodes.lookup u = some n0 := by
      rcases hw1 with rfl | ⟨-, gh, rfl⟩
      · exact ⟨rfl, rfl, fun _ _ h => h⟩
      · exact ⟨rfl, rfl, fun _ _ h => prim_lookup_append_some _ h⟩
    obtain ⟨hp1, htk1, hext1⟩ := hfield
    have hxt : w1.taken.contains x = false := by rw [htk1]; exact wput_taken hxm
    have hpath1 : ∀ (e : Nat) (c : Option Nat) (u : NodeId), w1.path[e]? = some (c, u) →
        e + 1 < w1.path.length → (w1.nodes.lookup u).isSome = true ∧
          w1.taken.contains u = false := by
      intro e c u hu he
      rw [hp1] at hu he
      obtain ⟨h1, h2⟩ := hD.path e c u hu he
      obtain ⟨n0, hn0⟩ := Option.isSome_iff_exists.mp h1
      exact ⟨by rw [hext1 u n0 hn0]; rfl, by rw [htk1]; exact h2⟩
    obtain ⟨c0, hc0⟩ := hD.last
    have hlen : 0 < w.path.length := by
      by_contra hc
      rw [List.getElem?_eq_none (by omega)] at hc0
      cases hc0
    split
    · next hl =>
      rw [wp_pure]
      exact ⟨⟨hI1, hT1.trans hD.map, ⟨lo, hi, hGx⟩, hpath1, ⟨c0, by rw [hp1]; exact hc0⟩⟩,
        n, hlk1, hl⟩
    · next hl =>
      split
      · exact wp_throw _ _ _ _
      · next fd hfd =>
        obtain ⟨hm, hle, hmax⟩ := searchLte_some (wput_timesLe hI1.books hlk1) hfd
        rw [hks] at hm hmax
        have hml : m.leaf = false := by
          rw [← hleaf]
          cases e : n.leaf
          · rfl
          · exact absurd e hl
        rw [hD.map] at hxm
        obtain ⟨m', lo', hi', -, -, -, hG'⟩ := hGx.child hxm hm (fun h => by
          rw [hml] at h; cases h)
        refine wput_ok (pathAdd_eq _ _ _ _) ?_
        refine ih { w1 with path := w1.path ++ [(some fd.c, fd.y)] } fd.y ⟨hI1.congr rfl rfl rfl
          rfl rfl rfl rfl rfl rfl, hT1.trans hD.map, ⟨lo', hi', hG'⟩, fun e c u hu he => ?_,
          ⟨some fd.c, ?_⟩⟩
        · have hlen1 : w1.path.length = w.path.length := by rw [hp1]
          simp only [List.length_append, List.length_singleton] at he
          rw [List.getElem?_append_left (by omega)] at hu
          by_cases he' : e + 1 < w1.path.length
          · exact hpath1 e c u hu he'
          · have : e = w.path.length - 1 := by omega
            subst this
            rw [hp1, hc0] at hu
            cases hu
            exact ⟨by rw [hlk1]; rfl, hxt⟩
        · show (w1.path ++ [(some fd.c, fd.y)])[(w1.path ++ [(some fd.c, fd.y)]).length - 1]? = _
          rw [List.length_append, List.length_singleton, Nat.add_sub_cancel,
            List.getElem?_append_right (Nat.le_refl _)]
          simp

/-- `putSegs` on the segments c :: rest from x keeps the walk's invariant:
the descents read, the writes keep `SNamed`. -/
theorem wputn_putSegs {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {z : NodeId} {C : List (Key × Nat)} {T0 : Tree} {key : Key} {h : Nat}
    (hp : ParamsOK p) (hs : Shows p v z s tp) (hb : Books i base s tp) (hn : SNamed T0) :
    ∀ (rest : Key) (c : Nat) (w : MW) (x : NodeId), keyWf (c :: rest) = true →
      DInv p i base s tp C T0 w x →
      WP (SIS.Tree.putSegs key (some h) (c :: rest) x) { p := p, i := i, view := v } w
        (fun _ w' => NInv i s w') := by
  intro rest
  induction rest with
  | nil =>
    intro c w x _ hD
    rw [SIS.Tree.putSegs.eq_2]
    unfold SIS.Tree.setValue
    refine wput_read ?_
    rw [wp_bind]
    refine (wputn_descend hs hb _ w x hD).mono ?_
    rintro L (w3 : MW) ⟨hD3, nl, hlk, -⟩
    dsimp only
    have hI3 := wputn_ninv_of hb hn hD3 hlk
    obtain ⟨c0, hc0⟩ := hD3.last
    refine wput_ok (newValue_eq _ _ _) ?_
    obtain ⟨hI4, -, -, hobj4, hnodes4, -⟩ := wputn_newValue (i := i) (s := s)
      { p := p, i := i, view := v } hI3 h w3.next _ (newValue_eq _ w3 h)
    have hlk4 : (w3.afterNewValue h).nodes.lookup L = some nl := by rw [hnodes4]; exact hlk
    refine wput_ok (getNode_hit _ hlk4) ?_
    split
    · refine wput_ok (putNode_eq _ _ _ _) ?_
      rw [wp_pure]
      refine (wputn_put hI4 (by rw [hlk4]; rfl) (fun ht c' y hy => ?_)).1
      rcases add_key_mem.mp hy with hy | ⟨-, rfl⟩
      · exact wputn_ptrs_overlay hI4 hlk4 ht c' y hy
      · exact hobj4
    · refine wput_ok (pathSize_eq _ _) ?_
      rw [wp_bind]
      refine (wputn_append _ L [(c, w3.next)] _ hI4 ⟨_, c0, hc0⟩ ?_).mono ?_
      · intro cy hcy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hcy
        subst hcy
        exact hobj4
      · intro _ w5 hw5
        rw [wp_pure]
        exact hw5.1
  | cons c2 rest2 ih =>
    intro c w x hk hD
    have hk2 : isLong c = true ∧ keyWf (c2 :: rest2) = true := by
      simp only [keyWf, Bool.and_eq_true] at hk
      exact hk
    rw [SIS.Tree.putSegs.eq_3 _ _ _ _ _ (by simp), wp_bind]
    unfold SIS.Tree.setNode
    refine wput_read ?_
    rw [wp_bind]
    refine (wputn_descend hs hb _ w x hD).mono ?_
    rintro L (w3 : MW) ⟨hD3, nl, hlk, hl⟩
    have hI3 := wputn_ninv_of hb hn hD3 hlk
    obtain ⟨c0, hc0⟩ := hD3.last
    obtain ⟨lo, hi, hGL⟩ := hD3.good
    have hLt : w3.taken.contains L = false := (hI3.path _ _ _ hc0).2
    have hLm : T0.obj L = some (.key ⟨wLevel s w3 L, nl.leaf, ksOf nl⟩) := by
      rw [← hD3.map]
      exact treeOf_obj_overlay i s hlk hLt
    have hwf := wputg_good_wf hGL hLm
    refine wput_ok (getNode_hit _ hlk) ?_
    split
    · next fd hfd =>
      obtain ⟨-, hfm⟩ := searchEq_some hwf (wput_timesLe hD3.inv.books hlk) hfd
      obtain ⟨m', lo', hi', -, -, -, hG'⟩ := hGL.child hLm hfm (fun _ => hk2.1)
      refine wput_ok (pathAdd_eq _ _ _ _) ?_
      rw [wp_pure]
      dsimp only
      have hlen : 0 < w3.path.length := by
        by_contra hc
        rw [List.getElem?_eq_none (by omega)] at hc0
        cases hc0
      refine ih c2 _ fd.y hk2.2 ⟨hD3.inv.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl, hD3.map,
        ⟨lo', hi', hG'⟩, fun e c' u hu he => ?_, ⟨some fd.c, ?_⟩⟩
      · simp only [List.length_append, List.length_singleton] at he
        rw [List.getElem?_append_left (by omega)] at hu
        exact hI3.path e c' u hu
      · show (w3.path ++ [(some fd.c, fd.y)])[(w3.path ++ [(some fd.c, fd.y)]).length - 1]? = _
        rw [List.length_append, List.length_singleton, Nat.add_sub_cancel,
          List.getElem?_append_right (Nat.le_refl _)]
        simp
    · dsimp only
      cases hg : w3.gh.lookup L with
      | none => exact wputn_ghOf_none hlk hg
      | some gh =>
      obtain ⟨g, hh⟩ := gh
      refine wput_ok (ghOf_hit _ hlk hg) ?_
      dsimp only
      refine wput_ok (note_eq _ _ _) ?_
      obtain ⟨hIN, -⟩ := wputn_same (w' := { w3 with trail := "segment.new" :: w3.trail }) hI3
        rfl rfl rfl rfl (Nat.le_refl _) (fun m hm => Or.inl hm)
      refine wput_ok (newKey_eq _ _ _ _ _ _) ?_
      obtain ⟨hIA, hGA, -, hlkA, hobjA, -⟩ := wputn_newKey (i := i) (s := s)
        { p := p, i := i, view := v } hIN (g + 1) 0 true [] (fun c' y' hy' => by simp at hy')
        _ _ (newKey_eq _ _ _ _ _ _)
      have hLn : L < w3.next := by
        by_contra hc
        have := (hI3.fresh L (Nat.le_of_not_lt hc)).1
        rw [this] at hlk
        cases hlk
      have hLv : L ≠ w3.next := Nat.ne_of_lt hLn
      have hLA := hGA.look L (by rw [hlk]; rfl)
      have htc : w3.taken.contains w3.next = false := (hI3.fresh w3.next (Nat.le_refl _)).2.2.1
      split
      · refine wput_ok (putNode_eq _ _ _ _) ?_
        rw [wp_pure]
        dsimp only
        obtain ⟨hIP, -⟩ := wputn_put (n' := nl.add i (.key c w3.next)) hIA hLA (fun ht c' y hy => by
          rcases add_key_mem.mp hy with hy | ⟨-, rfl⟩
          · exact hGA.obj _ (wputn_ptrs_overlay hI3 hlk ht c' y hy)
          · exact hobjA)
        refine wputn_chain hp (c2 :: rest2) _ w3.next (by simp) hIP ?_ htc
        rw [MW.withNode, lookup_upsert_ne _ _ (Ne.symm hLv)]
        exact hlkA
      · refine wput_ok (pathSize_eq _ _) ?_
        rw [wp_bind]
        refine (wputn_append _ L [(c, w3.next)] _ hIA ⟨_, c0, hc0⟩ ?_).mono ?_
        · intro cy hcy
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hcy
          subst hcy
          exact hobjA
        · rintro _ w5 ⟨hI5, hG5, hO5⟩
          rw [wp_pure]
          dsimp only
          have ht5 : w5.taken.contains w3.next = false := by
            rw [hG5.taken]
            exact htc
          refine wputn_chain hp (c2 :: rest2) w5 w3.next (by simp) hI5 ?_ ht5
          rw [hO5 w3.next (fun e c' he => ?_) (by show w3.next < w3.next + 2; omega)]
          · exact hlkA
          · obtain ⟨hu, -⟩ := hI3.path e c' w3.next he
            rw [(hI3.fresh w3.next (Nat.le_refl _)).1] at hu
            cases hu

/-- A put of a key as `Keys.toSegments` makes it keeps `SNamed` of the map:
every key klong of every key node of the map after it names a node of the
map, if it was so before. -/
theorem putKv_put_named {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {z : NodeId} (hp : ParamsOK p) (hs : Shows p v z s tp)
    (hb : Books i base s tp) {done : List Op} {w w' : MW} {b : Bool} {key : Key} {h : Nat}
    (hm : MidP p i base s tp done w) (hkey : keyWf key = true) (hn : SNamed (treeOf i s w))
    (hrun : SIS.Tree.putKv (.put key h) { p := p, i := i, view := v } w = .ok (b, w')) :
    SNamed (treeOf i s w') := by
  suffices hW : WP (SIS.Tree.putKv (.put key h)) { p := p, i := i, view := v } w
      (fun _ w' => NInv i s w') from (hW b w' hrun).named
  unfold SIS.Tree.putKv
  refine wput_ok (pathClear_eq _ _) ?_
  refine wput_ok (w' := { w with path := [(none, w.top.rootKey)] }) rfl ?_
  dsimp only
  cases key with
  | nil => simp [keyWf] at hkey
  | cons c rest =>
    exact wputn_putSegs (T0 := treeOf i s w) hp hs hb hn rest c _ _ hkey
      ⟨hm.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl, rfl, ⟨0, none, hm.sound.good⟩,
        fun e c u _ he => absurd he (by simp), ⟨none, rfl⟩⟩

/-! ## 8. A transaction of puts, and a run -/

/-- The accepted puts keep `MidP` and `SNamed` of the map. -/
theorem wputn_midP_run {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {z : NodeId} (hp : ParamsOK p) (hs : Shows p v z s tp)
    (hb : Books i base s tp) (hn : SNamed s) :
    ∀ (ops : List MOp) (w w' : MW), OpsRun { p := p, i := i, view := v } w ops w' →
      (∀ op ∈ ops, ∃ key h, op = SIS.Tree.Op.put key h) →
      ∀ done, MidP p i base s tp done w → SNamed (treeOf i s w) →
        SNamed (treeOf i s w') := by
  intro ops w w' hrun
  induction hrun with
  | nil w => intro _ _ _ hw; exact hw
  | cons w w1 w' op ops b hk h1 h2 _ ih =>
    intro hops done hm hw
    obtain ⟨key, h, rfl⟩ := hops _ List.mem_cons_self
    have hm1 := putKv_put (key := key) hp hs hb hn hm hk h1 h2
    have hw1 := putKv_put_named (key := key) hp hs hb hm hk hw h1
    exact ih (fun o ho => hops o (List.mem_cons_of_mem _ ho)) _ hm1 hw1

/-- One transaction of puts: the model's writer meets the writer's contract
(`WriterMeets`' conclusion) and gives `SNamed` back. -/
def WriterMeetsPutNamed (p : MParams) (ops : List MOp) : Prop :=
  ∀ (i : Time) (base : NodeId) (s : Tree) (tp : Top) (v : View BVal) (z : NodeId) (t : SIS.Tree.Top)
    (w : MW),
    SNamed s → Before p i base s tp → Shows p v z s tp → SIS.Tree.topOf p v z = .ok t →
    OpsRun { p := p, i := i, view := v } { next := base, top := t } ops w →
    (Contract (cpOf p) i s (ops.map opOf) (dirtyOf w) (treeOf i s w) ∧
      TreeOk ((treeOf i s w).at i) ∧ TopStep i tp (topOf i tp w) ∧
      (treeOf i s w).roots = rootsOf (topOf i tp w) ∧
      invOk (cpOf p) (treeOf i s w) = true ∧ TreeOk (treeOf i s w) ∧
      BalancedAll p (treeOf i s w) ∧
      (∀ x n, (treeOf i s w).obj x = some (.key n) → ∃ t rest, n.ks = Klong.time t :: rest) ∧
      (∀ x n, (treeOf i s w).obj x = some (.key n) → timesBefore (i + 1) n.ks = true) ∧
      (∀ r ∈ (treeOf i s w).roots, r.1 < i + 1) ∧
      (∀ x, w.next ≤ x → (treeOf i s w).obj x = none ∧ (topOf i tp w).node x = none) ∧
      (∀ z zn, (topOf i tp w).getLast? = some (z, zn) → ∀ q ∈ zn.skips,
        ((topOf i tp w).node q.2.1).map (·.time) = some q.2.2)) ∧
      SNamed (treeOf i s w)

/-- A transaction of puts meets the writer's contract and gives `SNamed` back. -/
theorem writerMeets_put_named {p : MParams} (hp : ParamsOK p) (ops : List MOp)
    (hops : ∀ op ∈ ops, ∃ key h, op = SIS.Tree.Op.put key h) : WriterMeetsPutNamed p ops := by
  intro i base s tp v z t w hn hbf hs ht hrun
  refine ⟨writerMeets_put hp ops hops i base s tp v z t w hn hbf hs ht hrun, ?_⟩
  exact wputn_midP_run hp hs hbf.books hn ops _ w hrun hops [] (wput_midP_start hs ht hbf)
    (by rw [treeOf_start]; exact hn)

/-- A run of the model's writer whose transactions are puts: `Runs` with
`SNamed` of its start tree and every operation a put. -/
inductive RunsPuts (p : MParams) : List (List Op) → Tree → Top → Prop where
  | start (s : Tree) (tp : Top) (base : NodeId) :
      Before p 1 base s tp → contents s = [] → TopStart tp → SNamed s → RunsPuts p [] s tp
  | step (txs : List (List Op)) (s : Tree) (tp : Top) (ops : List MOp) (base : NodeId)
      (v : View BVal) (z : NodeId) (t : SIS.Tree.Top) (w : MW) :
      RunsPuts p txs s tp → (∀ op ∈ ops, ∃ key h, op = SIS.Tree.Op.put key h) →
      Shows p v z s tp → SIS.Tree.topOf p v z = .ok t →
      (∀ x, base ≤ x → s.obj x = none ∧ tp.node x = none) →
      OpsRun { p := p, i := txs.length + 1, view := v } { next := base, top := t } ops w →
      RunsPuts p (txs ++ [ops.map opOf]) (treeOf (txs.length + 1) s w)
        (topOf (txs.length + 1) tp w)

/-- Such a run is a run (`Runs`). -/
theorem RunsPuts.runs {p : MParams} {txs : List (List Op)} {s : Tree} {tp : Top}
    (h : RunsPuts p txs s tp) : Runs p txs s tp := by
  induction h with
  | start s tp base hb hc ht _ => exact Runs.start s tp base hb hc ht
  | step txs s tp ops base v z t w _ _ hs ht hids hrun ih =>
    exact Runs.step txs s tp ops base v z t w ih hs ht hids hrun

/-- A run of the model's writer whose transactions are puts, from a start
tree whose key klongs name its nodes, is a history that meets the writer's
contract, TREE and the top's clauses. -/
theorem runs_meetsTop_puts {p : MParams} (hp : ParamsOK p) {txs : List (List Op)} {s : Tree}
    {tp : Top} (h : RunsPuts p txs s tp) : MeetsTop (cpOf p) txs s tp := by
  have key : ∀ {txs : List (List Op)} {s : Tree} {tp : Top}, RunsPuts p txs s tp →
      MeetsTop (cpOf p) txs s tp ∧ RunInv p txs s tp ∧ SNamed s := by
    intro txs s tp h
    induction h with
    | start s tp base hb hc ht hn =>
      have hat : s.at 0 = s := by
        apply Tree.at_eq_self
        · intro x n hx t' ht'
          exact Nat.le_of_lt_succ (timesBefore_iff.mp (hb.books.times x n hx) t' ht')
        · intro r hr
          exact Nat.le_of_lt_succ (hb.books.rootTimes r hr)
      refine ⟨MeetsTop.start s tp ⟨by rw [hat]; exact hb.inv, by rw [hat]; exact hc⟩
        (by rw [hat]; exact hb.tree) ht hb.books.roots, ?_, hn⟩
      exact ⟨hb.inv, hb.tree, hb.balanced, hb.books.first, hb.books.times, hb.books.rootTimes,
        hb.books.roots, hb.books.skips⟩
    | step txs s tp ops base v z t w _ hops hs ht hids hrun ih =>
      obtain ⟨hmeets, hinv, hn⟩ := ih
      have hbf : Before p (txs.length + 1) base s tp :=
        ⟨hinv.inv, hinv.tree, hinv.balanced,
          ⟨hinv.first, hinv.times, hinv.rootTimes, hids, hinv.roots, hinv.skips⟩⟩
      obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, hf, h8, h9, _, h11⟩, hn'⟩ :=
        writerMeets_put_named hp ops hops (txs.length + 1) base s tp v z t w hn hbf hs ht hrun
      refine ⟨MeetsTop.step txs s tp (ops.map opOf) (dirtyOf w) _ _ hmeets h1 h2 h3 h4, ?_, hn'⟩
      refine ⟨h5, h6, h7, hf, ?_, ?_, h4, h11⟩
      · simpa using h8
      · simpa using h9
  exact (key h).1

end Contract
