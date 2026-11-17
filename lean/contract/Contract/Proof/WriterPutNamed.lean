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

end Contract
