/-
The merges' loop finds the hole one height up (bergdb 030-01, step 2, the first
stall point R1): the descent of `mergeUp`, `descendToHeight key g h`, as pure
functions of what the writer reads (`rdN`, `rdG`), and the descent one height
up, on a state that reads alike above the node at that height, stops one node
earlier on the same path (`dhP_up`).
-/
import SIS.Tree.LiveHole

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## What the writer reads -/

/-- What `getNode y` returns at w: the overlay's node, or P@(i-1)'s as a key node. -/
def rdN (c : Ctx) (w : W) (y : NodeId) : Option KNode :=
  match w.nodes.lookup y with
  | some n => some n
  | none => match c.view y with
    | some nd => if nd.isData || c.p.keyMax < nd.level then none
        else some { leaf := c.p.heightOf nd.level == 0, ks := klongsOf nd.hist }
    | none => none

/-- What `ghOf y` returns at w: the overlay's segment and height, or those of
P@(i-1)'s node by its level. -/
def rdG (c : Ctx) (w : W) (y : NodeId) : Option (Nat × Nat) :=
  match w.nodes.lookup y with
  | some _ => w.gh.lookup y
  | none => match c.view y with
    | some nd => if nd.isData || c.p.keyMax < nd.level then none
        else some (c.p.segOf nd.level, c.p.heightOf nd.level)
    | none => none

/-- A read keeps what the writer reads, its path and its super root. -/
def ObsKept (c : Ctx) (w w' : W) : Prop :=
  rdN c w' = rdN c w ∧ rdG c w' = rdG c w ∧ w'.top = w.top

theorem ObsKept.refl (c : Ctx) (w : W) : ObsKept c w w := ⟨rfl, rfl, rfl⟩

theorem ObsKept.trans {c : Ctx} {u v w : W} (h1 : ObsKept c u v) (h2 : ObsKept c v w) :
    ObsKept c u w := ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩

theorem rdN_of_lookup (c : Ctx) (w : W) (y : NodeId) (n : KNode) (h : w.nodes.lookup y = some n) :
    rdN c w y = some n := by
  simp [rdN, h]

theorem rdG_of_lookup (c : Ctx) (w : W) (y : NodeId) (n : KNode) (h : w.nodes.lookup y = some n) :
    rdG c w y = w.gh.lookup y := by
  simp [rdG, h]

theorem writerWP_getNode_rd (y : NodeId) (c : Ctx) (w : W) :
    WriterWP (getNode y) c w (fun n w' => rdN c w y = some n ∧ ObsKept c w w' ∧ w'.path = w.path ∧
      w'.nodes.lookup y = some n) := by
  unfold getNode
  simp only [writerWP_bind, writerWP_get]
  split
  · rename_i n hn
    simp only [writerWP_pure]
    exact ⟨rdN_of_lookup c w y n hn, ObsKept.refl c w, by simp, hn⟩
  · rename_i hn
    simp only [writerWP_bind, writerWP_read]
    split
    · rename_i nd hv
      split
      · exact writerWP_throw _ _ _ _
      · rename_i hkind
        simp only [writerWP_bind, writerWP_set, writerWP_pure]
        have hlk : (w.nodes ++ [(y, ({ leaf := c.p.heightOf nd.level == 0, ks := klongsOf nd.hist } : KNode))]).lookup y =
            some { leaf := c.p.heightOf nd.level == 0, ks := klongsOf nd.hist } := by
          simp [List.lookup_append, hn]
        refine ⟨by simp [rdN, hn, hv, hkind], ⟨?_, ?_, by simp⟩, by simp, hlk⟩
        · funext z
          by_cases hz : z = y
          · subst hz; simp [rdN, hn, hv, hkind, List.lookup_append]
          · unfold rdN
            rw [lookup_append_single_ne _ _ _ _ hz]
        · funext z
          by_cases hz : z = y
          · subst hz; simp [rdG, hn, hv, hkind, List.lookup_append]
          · unfold rdG
            rw [lookup_append_single_ne _ _ _ _ hz, lookup_cons_ne _ _ _ _ hz]
    · exact writerWP_throw _ _ _ _

theorem writerWP_ghOf_rd (y : NodeId) (c : Ctx) (w : W) :
    WriterWP (ghOf y) c w (fun r w' => (∃ n, rdN c w y = some n) ∧ rdG c w y = some r ∧
      ObsKept c w w' ∧ w'.path = w.path) := by
  unfold ghOf
  simp only [writerWP_bind]
  refine writerWP_mono (writerWP_getNode_rd y c w) ?_
  rintro n w1 ⟨hn, hk, hp, hl⟩
  simp only [writerWP_get]
  split
  · rename_i r hr
    simp only [writerWP_pure]
    refine ⟨⟨n, hn⟩, ?_, hk, hp⟩
    rw [← hk.2.1, rdG_of_lookup c w1 y n hl, hr]
  · exact writerWP_throw _ _ _ _

theorem writerWP_pathAdd_rd (a : Option Nat) (y : NodeId) (c : Ctx) (w : W) :
    WriterWP (pathAdd a y) c w (fun _ w' => ObsKept c w w' ∧ w'.path = w.path ++ [(a, y)]) := by
  unfold pathAdd
  simp only [writerWP_modify]
  exact ⟨⟨rfl, rfl, rfl⟩, by simp⟩

/-! ## The descents as functions of the reads -/

/-- `descendLte` as a function of the node reads: the leaf and the path's steps. -/
def lteP (Rd : NodeId → Option KNode) (t : Time) (cv : Nat) :
    Nat → NodeId → Option (NodeId × List (Option Nat × NodeId))
  | 0, _ => none
  | f + 1, x => match Rd x with
    | none => none
    | some n => if n.leaf then some (x, []) else
        match n.searchLte t cv with
        | none => none
        | some fd => (lteP Rd t cv f fd.y).map (fun r => (r.1, (some fd.c, fd.y) :: r.2))

theorem writerWP_descendLte_rd (cv : Nat) (c : Ctx) :
    ∀ f x w, WriterWP (descendLte cv f x) c w (fun a w' => ∃ ext, lteP (rdN c w) c.i cv f x = some (a, ext) ∧
      w'.path = w.path ++ ext ∧ ObsKept c w w') := by
  intro f
  induction f with
  | zero => intro x w; exact writerWP_throw _ _ _ _
  | succ f ih =>
    intro x w
    unfold descendLte
    simp only [writerWP_bind, writerWP_read]
    refine writerWP_mono (writerWP_getNode_rd x c w) ?_
    rintro n w1 ⟨hn, hk1, hp1, _⟩
    split
    · rename_i hleaf
      simp only [writerWP_pure]
      exact ⟨[], by simp [lteP, hn, hleaf], by simp [hp1], hk1⟩
    · rename_i hleaf
      split
      · exact writerWP_throw _ _ _ _
      · rename_i fd hfd
        simp only [writerWP_bind]
        refine writerWP_mono (writerWP_pathAdd_rd _ _ c w1) ?_
        rintro _ w2 ⟨hk2, hp2⟩
        refine writerWP_mono (ih fd.y w2) ?_
        rintro a w3 ⟨ext, he, hp3, hk3⟩
        have hk12 := hk1.trans hk2
        refine ⟨(some fd.c, fd.y) :: ext, ?_, by rw [hp3, hp2, hp1]; simp, hk12.trans hk3⟩
        rw [hk12.1] at he
        simp [lteP, hn, hleaf, hfd, he]

/-- One segment of `descendToSegmentRoot`'s loop as a function of the reads. -/
def dsrStep (Rd : NodeId → Option KNode) (t : Time) (fuel : Nat)
    (acc : Option (NodeId × List (Option Nat × NodeId))) (cv : Nat) :
    Option (NodeId × List (Option Nat × NodeId)) :=
  match acc with
  | none => none
  | some (node, ps) => match lteP Rd t cv fuel node with
    | none => none
    | some (leaf, ext) => match Rd leaf with
      | none => none
      | some n => match n.searchEq t cv with
        | none => none
        | some fd => some (fd.y, ps ++ ext ++ [(some fd.c, fd.y)])

theorem writerWP_dsrLoop_rd (c : Ctx) :
    ∀ (cvs : List Nat) (node : NodeId) (w : W),
      WriterWP (cvs.foldlM (fun node cv => do
        let leaf ← descendLte cv c.p.fuel node
        let n ← getNode leaf
        match n.searchEq c.i cv with
        | none => throw s!"Bug: descent at {c.i}: segment {cv} not found"
        | some fd =>
          pathAdd (some fd.c) fd.y
          pure fd.y) node) c w
        (fun root w' => cvs.foldl (dsrStep (rdN c w) c.i c.p.fuel) (some (node, w.path)) =
          some (root, w'.path) ∧ ObsKept c w w') := by
  intro cvs
  induction cvs with
  | nil =>
    intro node w
    simp only [List.foldlM, writerWP_pure, List.foldl]
    exact ⟨by simp, ObsKept.refl c w⟩
  | cons cv rest ih =>
    intro node w
    simp only [List.foldlM, writerWP_bind]
    refine writerWP_mono (writerWP_descendLte_rd cv c c.p.fuel node w) ?_
    rintro leaf w1 ⟨ext, he, hp1, hk1⟩
    refine writerWP_mono (writerWP_getNode_rd leaf c w1) ?_
    rintro n w2 ⟨hn, hk2, hp2, _⟩
    split
    · exact writerWP_throw _ _ _ _
    · rename_i fd hfd
      simp only [writerWP_bind]
      refine writerWP_mono (writerWP_pathAdd_rd _ _ c w2) ?_
      rintro _ w3 ⟨hk3, hp3⟩
      simp only [writerWP_pure]
      refine writerWP_mono (ih fd.y w3) ?_
      rintro root w4 ⟨hf, hk4⟩
      have hk13 := (hk1.trans hk2).trans hk3
      refine ⟨?_, hk13.trans hk4⟩
      rw [hk13.1] at hf
      rw [hk1.1] at hn
      simp only [List.foldl]
      have hstep : dsrStep (rdN c w) c.i c.p.fuel (some (node, w.path)) cv =
          some (fd.y, w3.path) := by
        simp [dsrStep, he, hn, hfd, hp3, hp2, hp1]
      rw [hstep]; exact hf

/-- `descendToSegmentRoot` as a function of the reads. -/
def dsrP (Rd : NodeId → Option KNode) (t : Time) (fuel : Nat) (key : Key) (g : Nat) (r : NodeId) :
    Option (NodeId × List (Option Nat × NodeId)) :=
  (key.take g).foldl (dsrStep Rd t fuel) (some (r, [(none, r)]))

theorem writerWP_descendToSegmentRoot_rd (key : Key) (g : Nat) (c : Ctx) (w : W) :
    WriterWP (descendToSegmentRoot key g) c w (fun root w' =>
      dsrP (rdN c w) c.i c.p.fuel key g w.top.rootKey = some (root, w'.path) ∧ ObsKept c w w') := by
  unfold descendToSegmentRoot pathClear findRoot pathAdd
  simp only [writerWP_bind, writerWP_read, writerWP_modify, writerWP_get, writerWP_pure]
  refine writerWP_mono (writerWP_dsrLoop_rd c (key.take g) _ _) ?_
  rintro root w' ⟨hf, hk⟩
  exact ⟨hf, hk⟩

/-- `descendHeight` as a function of the reads: the path's steps. -/
def dhP (Rd : NodeId → Option KNode) (Gh : NodeId → Option (Nat × Nat)) (t : Time) (cv h : Nat) :
    Nat → NodeId → Option (List (Option Nat × NodeId))
  | 0, _ => none
  | f + 1, x => match Rd x, Gh x with
    | some n, some (_, hx) => if hx == h then some [] else
        if n.leaf || hx < h then none else
        match n.searchLte t cv with
        | none => none
        | some fd => (dhP Rd Gh t cv h f fd.y).map ((some fd.c, fd.y) :: ·)
    | _, _ => none

theorem writerWP_descendHeight_rd (cv h : Nat) (c : Ctx) :
    ∀ f x w, WriterWP (descendHeight cv h f x) c w (fun _ w' => ∃ ext,
      dhP (rdN c w) (rdG c w) c.i cv h f x = some ext ∧ w'.path = w.path ++ ext ∧ ObsKept c w w') := by
  intro f
  induction f with
  | zero => intro x w; exact writerWP_throw _ _ _ _
  | succ f ih =>
    intro x w
    unfold descendHeight
    simp only [writerWP_bind, writerWP_read]
    refine writerWP_mono (writerWP_ghOf_rd x c w) ?_
    rintro ⟨gx, hx⟩ w1 ⟨⟨n0, hn0⟩, hg, hk1, hp1⟩
    split
    · rename_i hxh
      simp only [writerWP_pure]
      refine ⟨[], ?_, by simp [hp1], hk1⟩
      simp [dhP, hn0, hg, hxh]
    · rename_i hxh
      simp only [writerWP_bind]
      refine writerWP_mono (writerWP_getNode_rd x c w1) ?_
      rintro n w2 ⟨hn, hk2, hp2, _⟩
      rw [hk1.1, hn0] at hn
      cases hn
      split
      · exact writerWP_throw _ _ _ _
      · rename_i hlh
        split
        · exact writerWP_throw _ _ _ _
        · rename_i fd hfd
          simp only [writerWP_bind]
          refine writerWP_mono (writerWP_pathAdd_rd _ _ c w2) ?_
          rintro _ w3 ⟨hk3, hp3⟩
          refine writerWP_mono (ih fd.y w3) ?_
          rintro _ w4 ⟨ext, he, hp4, hk4⟩
          have hk13 := (hk1.trans hk2).trans hk3
          refine ⟨(some fd.c, fd.y) :: ext, ?_, by rw [hp4, hp3, hp2, hp1]; simp, hk13.trans hk4⟩
          rw [hk13.1, hk13.2.1] at he
          have hxh' : (hx == h) = false := by simpa using hxh
          simp [dhP, hn0, hg, hxh', hlh, hfd, he]

theorem writerWP_descendToHeight_rd (key : Key) (g h : Nat) (c : Ctx) (w : W) :
    WriterWP (descendToHeight key g h) c w (fun d w' => ∃ root P0 cv ext,
      dsrP (rdN c w) c.i c.p.fuel key g w.top.rootKey = some (root, P0) ∧ key[g]? = some cv ∧
      dhP (rdN c w) (rdG c w) c.i cv h c.p.fuel root = some ext ∧ w'.path = P0 ++ ext ∧
      d = (P0 ++ ext).length - 1 ∧ ObsKept c w w') := by
  unfold descendToHeight
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (writerWP_descendToSegmentRoot_rd key g c w) ?_
  rintro root w1 ⟨hd, hk1⟩
  split
  · exact writerWP_throw _ _ _ _
  · rename_i cv hcv
    simp only [writerWP_bind]
    refine writerWP_mono (writerWP_descendHeight_rd cv h c c.p.fuel root w1) ?_
    rintro _ w2 ⟨ext, he, hp2, hk2⟩
    unfold pathSize
    simp only [writerWP_bind, writerWP_get, writerWP_pure]
    rw [hk1.1, hk1.2.1] at he
    exact ⟨root, w1.path, cv, ext, hd, hcv, he, hp2, by rw [hp2], hk1.trans hk2⟩

/-! ## The descents compared -/

/-- One step of `descendToSegmentRoot`'s loop, unfolded. -/
theorem dsrStep_some (Rd : NodeId → Option KNode) (t : Time) (fuel : Nat) (node : NodeId)
    (ps : List (Option Nat × NodeId)) (cv : Nat) (acc : NodeId × List (Option Nat × NodeId))
    (h : dsrStep Rd t fuel (some (node, ps)) cv = some acc) :
    ∃ leaf ext n fd, lteP Rd t cv fuel node = some (leaf, ext) ∧ Rd leaf = some n ∧
      n.searchEq t cv = some fd ∧ acc = (fd.y, ps ++ ext ++ [(some fd.c, fd.y)]) := by
  simp only [dsrStep] at h
  cases hl : lteP Rd t cv fuel node with
  | none => simp [hl] at h
  | some le =>
    obtain ⟨leaf, ext⟩ := le
    simp only [hl] at h
    cases hn : Rd leaf with
    | none => simp [hn] at h
    | some n =>
      simp only [hn] at h
      cases hf : n.searchEq t cv with
      | none => simp [hf] at h
      | some fd =>
        simp only [hf, Option.some.injEq] at h
        exact ⟨leaf, ext, n, fd, rfl, hn, hf, h.symm⟩

/-- One step of `lteP`, unfolded. -/
theorem lteP_succ_some (Rd : NodeId → Option KNode) (t : Time) (cv f : Nat) (x a : NodeId)
    (ext : List (Option Nat × NodeId)) (h : lteP Rd t cv (f + 1) x = some (a, ext)) :
    ∃ n, Rd x = some n ∧ ((n.leaf = true ∧ a = x ∧ ext = []) ∨
      (n.leaf = false ∧ ∃ fd ext', n.searchLte t cv = some fd ∧ lteP Rd t cv f fd.y = some (a, ext') ∧
        ext = (some fd.c, fd.y) :: ext')) := by
  simp only [lteP] at h
  cases hR : Rd x with
  | none => simp [hR] at h
  | some n =>
    simp only [hR] at h
    refine ⟨n, rfl, ?_⟩
    cases hl : n.leaf
    · simp only [hl, Bool.false_eq_true, ↓reduceIte] at h
      cases hfd : n.searchLte t cv with
      | none => simp [hfd] at h
      | some fd =>
        simp only [hfd] at h
        cases hr : lteP Rd t cv f fd.y with
        | none => simp [hr] at h
        | some r =>
          simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨a', ext'⟩ := r
          obtain ⟨h1, h2⟩ := h
          simp only at h1 h2
          subst h1
          exact Or.inr ⟨rfl, fd, ext', rfl, hr, h2.symm⟩
    · simp only [hl, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      exact Or.inl ⟨rfl, h.1.symm, h.2.symm⟩

theorem lteP_leaf_mem (Rd : NodeId → Option KNode) (t : Time) (cv : Nat) :
    ∀ f x a ext, lteP Rd t cv f x = some (a, ext) → a ∈ x :: ext.map (·.2) := by
  intro f
  induction f with
  | zero => intro x a ext h; simp [lteP] at h
  | succ f ih =>
    intro x a ext h
    obtain ⟨n, _, ⟨_, rfl, rfl⟩ | ⟨_, fd, ext', _, hr, rfl⟩⟩ := lteP_succ_some Rd t cv f x a ext h
    · simp
    · have := ih fd.y a ext' hr
      simp only [List.mem_cons, List.map_cons] at this ⊢
      rcases this with h' | h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h')

/-- `lteP` reads only the nodes it visits. -/
theorem lteP_congr (Rd Rd' : NodeId → Option KNode) (t : Time) (cv : Nat) :
    ∀ f x a ext, lteP Rd t cv f x = some (a, ext) → (∀ y ∈ x :: ext.map (·.2), Rd' y = Rd y) →
      lteP Rd' t cv f x = some (a, ext) := by
  intro f
  induction f with
  | zero => intro x a ext h; simp [lteP] at h
  | succ f ih =>
    intro x a ext h hag
    have hx := hag x (by simp)
    obtain ⟨n, hRx, ⟨hl, rfl, rfl⟩ | ⟨hl, fd, ext', hfd, hr, rfl⟩⟩ := lteP_succ_some Rd t cv f x a ext h
    · simp [lteP, hx, hRx, hl]
    · have h' := ih fd.y a ext' hr (fun y hy => hag y (by
        simp only [List.mem_cons, List.map_cons] at hy ⊢; exact Or.inr hy))
      simp [lteP, hx, hRx, hl, hfd, h']

theorem dsrFold_none (Rd : NodeId → Option KNode) (t : Time) (fuel : Nat) :
    ∀ (l : List Nat), l.foldl (dsrStep Rd t fuel) none = none := by
  intro l; induction l with
  | nil => rfl
  | cons _ _ ih' => simpa [List.foldl, dsrStep] using ih'

theorem dsrFold_prefix (Rd : NodeId → Option KNode) (t : Time) (fuel : Nat) :
    ∀ (cvs : List Nat) node ps root P, cvs.foldl (dsrStep Rd t fuel) (some (node, ps)) = some (root, P) →
      ∃ sfx, P = ps ++ sfx ∧ (cvs ≠ [] → sfx ≠ []) := by
  intro cvs
  induction cvs with
  | nil =>
    intro node ps root P h
    simp only [List.foldl, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨[], by rw [h.2]; simp, fun h' => absurd rfl h'⟩
  | cons cv rest ih =>
    intro node ps root P h
    simp only [List.foldl] at h
    cases hs : dsrStep Rd t fuel (some (node, ps)) cv with
    | none => rw [hs, dsrFold_none] at h; cases h
    | some acc =>
      rw [hs] at h
      obtain ⟨leaf, ext, n, fd, _, _, _, rfl⟩ := dsrStep_some Rd t fuel node ps cv acc hs
      obtain ⟨sfx, hP, _⟩ := ih _ _ root P h
      exact ⟨ext ++ [(some fd.c, fd.y)] ++ sfx, by rw [hP]; simp, fun _ => by simp⟩

theorem mem_dropLast_of_append {α : Type} (l1 l2 : List α) (y : α) (hy : y ∈ l1) (h2 : l2 ≠ []) :
    y ∈ (l1 ++ l2).dropLast := by
  rw [List.dropLast_append_of_ne_nil h2]
  exact List.mem_append_left _ hy

/-- `descendToSegmentRoot`'s loop reads only the nodes of its path but the last. -/
theorem dsrFold_congr (Rd Rd' : NodeId → Option KNode) (t : Time) (fuel : Nat) :
    ∀ (cvs : List Nat) node ps root P, cvs.foldl (dsrStep Rd t fuel) (some (node, ps)) = some (root, P) →
      (cvs ≠ [] → Rd' node = Rd node) → (∀ y ∈ P.dropLast.map (·.2), Rd' y = Rd y) →
      cvs.foldl (dsrStep Rd' t fuel) (some (node, ps)) = some (root, P) := by
  intro cvs
  induction cvs with
  | nil => intro node ps root P h _ _; exact h
  | cons cv rest ih =>
    intro node ps root P h hnode hag
    simp only [List.foldl] at h ⊢
    cases hs : dsrStep Rd t fuel (some (node, ps)) cv with
    | none => rw [hs, dsrFold_none] at h; cases h
    | some acc =>
      rw [hs] at h
      obtain ⟨leaf, ext, n, fd, hl, hn, hfd, rfl⟩ := dsrStep_some Rd t fuel node ps cv acc hs
      obtain ⟨sfx, hP, hne⟩ := dsrFold_prefix Rd t fuel rest _ _ root P h
      -- the nodes read in this step are in P but its last
      have hin : ∀ y ∈ ext.map (·.2), Rd' y = Rd y := by
        intro y hy
        apply hag
        rw [hP, List.map_dropLast]
        rw [show (ps ++ ext ++ [(some fd.c, fd.y)] ++ sfx).map (·.2) =
          (ps.map (·.2) ++ ext.map (·.2)) ++ ([fd.y] ++ sfx.map (·.2)) by simp]
        exact mem_dropLast_of_append _ _ y (List.mem_append_right _ hy) (by simp)
      have hx : Rd' node = Rd node := hnode (by simp)
      have hl' := lteP_congr Rd Rd' t cv fuel node leaf ext hl (fun y hy => by
        simp only [List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact hx
        · exact hin y hy)
      have hleaf : Rd' leaf = Rd leaf := by
        have := lteP_leaf_mem Rd t cv fuel node leaf ext hl
        simp only [List.mem_cons] at this
        rcases this with rfl | hy
        · exact hx
        · exact hin leaf hy
      have hstep : dsrStep Rd' t fuel (some (node, ps)) cv =
          some (fd.y, ps ++ ext ++ [(some fd.c, fd.y)]) := by
        simp [dsrStep, hl', hleaf, hn, hfd]
      rw [hstep]
      refine ih fd.y _ root P h (fun hr => ?_) hag
      cases sfx with
      | nil => exact absurd rfl (hne hr)
      | cons s0 s1 =>
      apply hag
      rw [hP, List.map_dropLast]
      rw [show (ps ++ ext ++ [(some fd.c, fd.y)] ++ s0 :: s1).map (·.2) =
        ((ps.map (·.2) ++ ext.map (·.2)) ++ [fd.y]) ++ (s0.2 :: s1.map (·.2)) by simp]
      exact mem_dropLast_of_append _ _ fd.y (by simp) (by simp)

theorem dsrP_congr (Rd Rd' : NodeId → Option KNode) (t : Time) (fuel : Nat) (key : Key) (g : Nat)
    (r root : NodeId) (P : List (Option Nat × NodeId)) (h : dsrP Rd t fuel key g r = some (root, P))
    (hag : ∀ y ∈ P.dropLast.map (·.2), Rd' y = Rd y) : dsrP Rd' t fuel key g r = some (root, P) := by
  unfold dsrP at h ⊢
  refine dsrFold_congr Rd Rd' t fuel _ r _ root P h (fun hne => ?_) hag
  obtain ⟨sfx, hP, hs⟩ := dsrFold_prefix Rd t fuel _ r _ root P h
  apply hag
  rw [hP, List.map_dropLast]
  cases sfx with
  | nil => exact absurd rfl (hs hne)
  | cons s0 s1 => simp

theorem mem_dropLast_cons {α : Type} (a : α) (l : List α) (y : α) (h : y ∈ l.dropLast) :
    y ∈ (a :: l).dropLast := by
  cases l with
  | nil => simp at h
  | cons b l' => simp only [List.dropLast_cons_cons, List.mem_cons]; exact Or.inr h

theorem mem_dropLast_dropLast_cons {α : Type} (a : α) (l : List α) (y : α)
    (h : y ∈ l.dropLast.dropLast) : y ∈ (a :: l).dropLast.dropLast := by
  cases l with
  | nil => simp at h
  | cons b l' =>
    rw [List.dropLast_cons_cons]
    exact mem_dropLast_cons a _ y h

/-- `dhP` returns no step only at a node of height h. -/
theorem dhP_nil (Rd : NodeId → Option KNode) (Gh : NodeId → Option (Nat × Nat)) (t : Time) (cv h : Nat) :
    ∀ f y, dhP Rd Gh t cv h f y = some [] → ∃ g, Gh y = some (g, h) := by
  intro f y hy
  cases f with
  | zero => simp [dhP] at hy
  | succ f =>
    unfold dhP at hy
    split at hy
    · rename_i n g' hx _ hG
      split at hy
      · rename_i hxh
        exact ⟨g', by rw [hG]; simp at hxh; rw [hxh]⟩
      · split at hy
        · cases hy
        · split at hy
          · cases hy
          · cases hr : dhP Rd Gh t cv h f _ <;> rw [hr] at hy <;> simp at hy
    · cases hy

/-- The heights along a list of nodes: one less at each step down from an inner node. -/
def GradedL (Rd : NodeId → Option KNode) (Gh : NodeId → Option (Nat × Nat)) : List NodeId → Prop
  | x :: y :: rest => (∀ n, Rd x = some n → n.leaf = false →
      ∃ g1 h1 g2 h2, Gh x = some (g1, h1) ∧ Gh y = some (g2, h2) ∧ h1 = h2 + 1) ∧
      GradedL Rd Gh (y :: rest)
  | _ => True

/-- The descent one height up, reading alike above its stop, stops one node
earlier on the same path. -/
theorem dhP_up (Rd Rd' : NodeId → Option KNode) (Gh Gh' : NodeId → Option (Nat × Nat)) (t : Time)
    (cv h : Nat) :
    ∀ f x ext ext', dhP Rd Gh t cv h f x = some ext → dhP Rd' Gh' t cv (h + 1) f x = some ext' →
      ext ≠ [] → GradedL Rd Gh (x :: ext.map (·.2)) →
      (∀ y ∈ (x :: ext.map (·.2)).dropLast.dropLast, Rd' y = Rd y) →
      (∀ y ∈ (x :: ext.map (·.2)).dropLast, Gh' y = Gh y) →
      ext' = ext.dropLast := by
  intro f
  induction f with
  | zero => intro x ext ext' h1; simp [dhP] at h1
  | succ f ih =>
    intro x ext ext' h1 h2 hne hgr hagN hagG
    unfold dhP at h1
    split at h1
    · rename_i n gx hx hRx hGx
      split at h1
      · simp only [Option.some.injEq] at h1; exact absurd h1.symm hne
      · rename_i hxh
        split at h1
        · cases h1
        · rename_i hlh
          split at h1
          · cases h1
          · rename_i fd hfd
            cases hr : dhP Rd Gh t cv h f fd.y with
            | none => rw [hr] at h1; cases h1
            | some r =>
              rw [hr] at h1
              simp only [Option.map_some, Option.some.injEq] at h1
              subst h1
              have hnl : n.leaf = false := by
                cases hl : n.leaf
                · rfl
                · simp [hl] at hlh
              have hxh' : ¬ hx < h := by
                intro hc; simp [hc] at hlh
              have hxne : hx ≠ h := by simpa using hxh
              -- the step down from x is graded
              obtain ⟨g1, h1', g2, h2', hG1, hG2, hstep⟩ := hgr.1 n hRx hnl
              rw [hGx] at hG1
              simp only [Option.some.injEq, Prod.mk.injEq] at hG1
              obtain ⟨rfl, rfl⟩ := hG1
              have hGx' : Gh' x = Gh x := hagG x (by simp)
              -- T at x
              unfold dhP at h2
              rw [hGx'] at h2
              split at h2
              · rename_i n' gx' hx' hR' hG'
                rw [hGx] at hG'
                simp only [Option.some.injEq, Prod.mk.injEq] at hG'
                obtain ⟨rfl, rfl⟩ := hG'
                by_cases hup : hx == h + 1
                · -- T stops at x, and S stops at the next node
                  simp only [hup, ↓reduceIte, Option.some.injEq] at h2
                  subst h2
                  have hx1 : hx = h + 1 := by simpa using hup
                  have hr0 : r = [] := by
                    cases r with
                    | nil => rfl
                    | cons e r' =>
                      exfalso
                      cases f with
                      | zero => simp [dhP] at hr
                      | succ f =>
                        unfold dhP at hr
                        split at hr
                        · rename_i _ _ hy _ hGy
                          rw [hG2] at hGy
                          simp only [Option.some.injEq, Prod.mk.injEq] at hGy
                          obtain ⟨_, rfl⟩ := hGy
                          have : (h2' == h) = true := by simp; omega
                          simp [this] at hr
                        · cases hr
                  subst hr0
                  simp
                · simp only [hup, Bool.false_eq_true, ↓reduceIte] at h2
                  have hx1 : hx ≠ h + 1 := by simpa using hup
                  -- r is not empty: S does not stop at the next node
                  have hrne : r ≠ [] := by
                    intro hr0
                    subst hr0
                    obtain ⟨g', hg'⟩ := dhP_nil Rd Gh t cv h f fd.y hr
                    rw [hG2] at hg'
                    simp only [Option.some.injEq, Prod.mk.injEq] at hg'
                    omega
                  have hRx' : Rd' x = Rd x := hagN x (by
                    cases r with
                    | nil => exact absurd rfl hrne
                    | cons e r' => simp)
                  rw [hRx', hRx] at hR'
                  simp only [Option.some.injEq] at hR'
                  subst hR'
                  have hlt : ¬ hx < h + 1 := by omega
                  simp only [hnl, hlt, decide_false, Bool.or_false, Bool.false_eq_true, ↓reduceIte, hfd] at h2
                  cases hr' : dhP Rd' Gh' t cv (h + 1) f fd.y with
                  | none => rw [hr'] at h2; cases h2
                  | some r' =>
                    rw [hr'] at h2
                    simp only [Option.map_some, Option.some.injEq] at h2
                    subst h2
                    have hih := ih fd.y r r' hr hr' hrne hgr.2
                      (fun y hy => hagN y (mem_dropLast_dropLast_cons x _ y hy))
                      (fun y hy => hagG y (mem_dropLast_cons x _ y hy))
                    rw [hih]
                    cases r with
                    | nil => exact absurd rfl hrne
                    | cons e r2 => simp
              · cases h2
    · cases h1

/-! ## The descent one height up -/

theorem lteP_leaf (Rd : NodeId → Option KNode) (t : Time) (cv : Nat) :
    ∀ f x a ext, lteP Rd t cv f x = some (a, ext) →
      (∃ n, Rd a = some n ∧ n.leaf = true) ∧ (x :: ext.map (·.2)).getLast? = some a := by
  intro f
  induction f with
  | zero => intro x a ext h; simp [lteP] at h
  | succ f ih =>
    intro x a ext h
    obtain ⟨n, hRx, ⟨hl, rfl, rfl⟩ | ⟨_, fd, ext', _, hr, rfl⟩⟩ := lteP_succ_some Rd t cv f x a ext h
    · exact ⟨⟨n, hRx, hl⟩, by simp⟩
    · obtain ⟨h1, h2⟩ := ih fd.y a ext' hr
      refine ⟨h1, ?_⟩
      rw [List.map_cons, List.getLast?_cons_cons]
      exact h2

/-- The path of `descendToSegmentRoot`'s loop ends at its node, and the node
before the last is a segment leaf once a segment is passed. -/
theorem dsrFold_shape (Rd : NodeId → Option KNode) (t : Time) (fuel : Nat) :
    ∀ (cvs : List Nat) node ps root P, cvs.foldl (dsrStep Rd t fuel) (some (node, ps)) = some (root, P) →
      (ps.map (·.2)).getLast? = some node →
      (P.map (·.2)).getLast? = some root ∧
      (cvs ≠ [] → ∃ y n, (P.map (·.2)).dropLast.getLast? = some y ∧ Rd y = some n ∧ n.leaf = true) := by
  intro cvs
  induction cvs with
  | nil =>
    intro node ps root P h hl
    simp only [List.foldl, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hl, fun h' => absurd rfl h'⟩
  | cons cv rest ih =>
    intro node ps root P h hl
    simp only [List.foldl] at h
    cases hs : dsrStep Rd t fuel (some (node, ps)) cv with
    | none => rw [hs, dsrFold_none] at h; cases h
    | some acc =>
      rw [hs] at h
      obtain ⟨leaf, ext, n, fd, hlte, hn, _, rfl⟩ := dsrStep_some Rd t fuel node ps cv acc hs
      have hl' : ((ps ++ ext ++ [(some fd.c, fd.y)]).map (·.2)).getLast? = some fd.y := by simp
      obtain ⟨h1, h2⟩ := ih _ _ root P h hl'
      refine ⟨h1, fun _ => ?_⟩
      by_cases hr : rest = []
      · subst hr
        simp only [List.foldl, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        obtain ⟨⟨n', hn', hleaf⟩, hlast⟩ := lteP_leaf Rd t cv fuel node leaf ext hlte
        rw [hn] at hn'; cases hn'
        refine ⟨leaf, n, ?_, hn, hleaf⟩
        rw [show ((ps ++ ext ++ [(some fd.c, fd.y)]).map (·.2)).dropLast = (ps ++ ext).map (·.2) by simp]
        cases ext with
        | nil =>
          simp only [List.map_nil, List.getLast?_singleton, Option.some.injEq] at hlast
          subst hlast
          simpa using hl
        | cons e ext' =>
          have : ((ps ++ e :: ext').map (·.2)).getLast? = ((e :: ext').map (·.2)).getLast? := by
            rw [List.map_append, List.getLast?_append]
            cases hx : ((e :: ext').map (·.2)).getLast? with
            | none => simp at hx
            | some a => rfl
          rw [this]
          rw [List.map_cons, List.getLast?_cons_cons] at hlast
          exact hlast
      · exact h2 hr

theorem dsrP_shape (Rd : NodeId → Option KNode) (t : Time) (fuel : Nat) (key : Key) (g : Nat)
    (r root : NodeId) (P : List (Option Nat × NodeId)) (h : dsrP Rd t fuel key g r = some (root, P)) :
    (P.map (·.2)).getLast? = some root ∧
      (key.take g ≠ [] → ∃ y n, (P.map (·.2)).dropLast.getLast? = some y ∧ Rd y = some n ∧ n.leaf = true) ∧
      (key.take g = [] → P = [(none, r)]) := by
  obtain ⟨h1, h2⟩ := dsrFold_shape Rd t fuel _ r _ root P h (by simp)
  refine ⟨h1, h2, fun he => ?_⟩
  unfold dsrP at h
  rw [he] at h
  simp only [List.foldl, Option.some.injEq, Prod.mk.injEq] at h
  exact h.2.symm

theorem gradedL_append_right (Rd : NodeId → Option KNode) (Gh : NodeId → Option (Nat × Nat)) :
    ∀ (l1 l2 : List NodeId), GradedL Rd Gh (l1 ++ l2) → GradedL Rd Gh l2 := by
  intro l1
  induction l1 with
  | nil => intro l2 h; exact h
  | cons a l1 ih =>
    intro l2 h
    apply ih
    cases l1 with
    | nil =>
      cases l2 with
      | nil => trivial
      | cons b l2 => exact h.2
    | cons b l1' => exact h.2

/-- The merges' descent one height up, on a state that reads alike above the
node it found one height down, stops at that node's parent on the same path. -/
theorem descendToHeight_up (key : Key) (g h : Nat) (c : Ctx) (S S1 T : W) (d : Nat)
    (hS : descendToHeight key g h c S = .ok (d, S1)) (hd : 0 < d)
    (hq : ∀ e, S1.path[d - 1]? = some e → ∃ n, rdN c S e.2 = some n ∧ n.leaf = false)
    (hroot : T.top.rootKey = S.top.rootKey)
    (hagN : ∀ y ∈ (S1.path.map (·.2)).dropLast.dropLast, rdN c T y = rdN c S y)
    (hagG : ∀ y ∈ (S1.path.map (·.2)).dropLast, rdG c T y = rdG c S y)
    (hgr : GradedL (rdN c S) (rdG c S) (S1.path.map (·.2))) :
    WriterWP (descendToHeight key g (h + 1)) c T (fun d' T1 => d' = d - 1 ∧ T1.path = S1.path.dropLast) := by
  obtain ⟨root, P0, cv, ext, hdsr, hcv, hdh, hp1, hd1, -⟩ :=
    writerWP_descendToHeight_rd key g h c S d S1 hS
  intro d' T1 hT
  obtain ⟨root', P0', cv', ext', hdsr', hcv', hdh', hp1', hd1', -⟩ :=
    writerWP_descendToHeight_rd key g (h + 1) c T d' T1 hT
  rw [hcv] at hcv'
  cases hcv'
  obtain ⟨hlast, hpre, hnil⟩ := dsrP_shape (rdN c S) c.i c.p.fuel key g _ root P0 hdsr
  obtain ⟨B, hB⟩ := List.getLast?_eq_some_iff.mp hlast
  -- the node one height down is not the segment's root
  have hext : ext ≠ [] := by
    intro he
    subst he
    rw [List.append_nil] at hp1 hd1
    by_cases hg : key.take g = []
    · rw [hnil hg] at hd1; simp at hd1; omega
    · obtain ⟨y, n, hy, hyn, hyl⟩ := hpre hg
      rw [hB, List.dropLast_concat] at hy
      obtain ⟨C, hC⟩ := List.getLast?_eq_some_iff.mp hy
      have hlen : P0.length = C.length + 2 := by
        have := congrArg List.length hB
        rw [hC] at this; simp at this; (try omega)
      have hidx : (P0.map (·.2))[d - 1]? = some y := by
        rw [hB, hC, hd1, hlen]
        rw [List.getElem?_append_left (by simp), List.getElem?_append_right (by omega)]
        simp
      rw [List.getElem?_map] at hidx
      cases he : P0[d - 1]? with
      | none => rw [he] at hidx; cases hidx
      | some e =>
        rw [he] at hidx
        simp only [Option.map_some, Option.some.injEq] at hidx
        obtain ⟨n', hn', hl'⟩ := hq e (by rw [hp1]; exact he)
        rw [hidx, hyn] at hn'
        cases hn'
        rw [hyl] at hl'
        cases hl'
  -- the path's nodes: the part above the segment's root, and the descent below it
  have hL : S1.path.map (·.2) = B ++ (root :: ext.map (·.2)) := by
    rw [hp1, List.map_append, hB]; simp
  have hPB : (P0.map (·.2)).dropLast = B := by rw [hB, List.dropLast_concat]
  have hext2 : (root :: ext.map (·.2)).dropLast ≠ [] := by
    cases ext with
    | nil => exact absurd rfl hext
    | cons e ext' => simp
  have hsplit : (S1.path.map (·.2)).dropLast.dropLast =
      B ++ ((root :: ext.map (·.2)).dropLast.dropLast) := by
    rw [hL, List.dropLast_append_of_ne_nil (by simp), List.dropLast_append_of_ne_nil hext2]
  have hdsrT := dsrP_congr (rdN c S) (rdN c T) c.i c.p.fuel key g _ root P0 hdsr
    (fun y hy => hagN y (by
      rw [hsplit]
      apply List.mem_append_left
      rw [← hPB, ← List.map_dropLast]
      exact hy))
  rw [hroot, hdsrT] at hdsr'
  simp only [Option.some.injEq, Prod.mk.injEq] at hdsr'
  obtain ⟨rfl, rfl⟩ := hdsr'
  have hup := dhP_up (rdN c S) (rdN c T) (rdG c S) (rdG c T) c.i cv h c.p.fuel _ ext ext' hdh hdh' hext
    (gradedL_append_right _ _ B _ (hL ▸ hgr))
    (fun y hy => hagN y (by rw [hsplit]; exact List.mem_append_right _ hy))
    (fun y hy => hagG y (by
      rw [hL, List.dropLast_append_of_ne_nil (by simp)]
      exact List.mem_append_right _ hy))
  subst hup
  refine ⟨?_, ?_⟩
  · rw [hd1', hd1]
    have : ext.dropLast.length = ext.length - 1 := by simp
    simp only [List.length_append, this]
    have : 0 < ext.length := List.length_pos_iff.mpr hext
    omega
  · rw [hp1', hp1, List.dropLast_append_of_ne_nil hext]

end SIS.Tree
