/-
Root collapse's two steps commute (bergdb 026-16, section 5.3; 024-22, section
11.1): the leaf's `appendKlongs` (with its cascade) neither reads nor writes the
segment root x below it, so it runs the same from a state whose node x is
changed. Here, the relational walk: `RelOK x m f c u` says that every successful
run of f from u with x's node set to m is a run from u, with x's node set to m
after it. `XWP` carries a postcondition of the run from u with it, so that the
walk knows the ids it reads and writes (`RJ`: x is cached, below the next id,
and the key access path is fixed).
-/
import SIS.Tree.GetFrame

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The writer's state with node x set to m in its overlay. -/
def setX (x : NodeId) (m : KNode) (w : W) : W := { w with nodes := upsert w.nodes x m }

/-- Every successful run of f from u with x's node set to m is a run from u,
with x's node set to m after it. -/
def RelOK {α : Type} (x : NodeId) (m : KNode) (f : M α) (c : Ctx) (u : W) : Prop :=
  ∀ r w2, f c (setX x m u) = .ok (r, w2) → ∃ u2, f c u = .ok (r, u2) ∧ w2 = setX x m u2

/-- `RelOK` with a postcondition of the run from u. -/
def XWP {α : Type} (x : NodeId) (m : KNode) (f : M α) (c : Ctx) (u : W)
    (post : α → W → Prop) : Prop :=
  RelOK x m f c u ∧ WriterWP f c u post

/-- The walk's invariant: x is in the overlay with node nx, below the next id,
and the key access path is `path0`. -/
def RJ (x : NodeId) (nx : KNode) (path0 : List (Option Nat × NodeId)) (u : W) : Prop :=
  u.nodes.lookup x = some nx ∧ x < u.next ∧ u.path = path0

/-- The transfer: a postcondition of every run from the state with x's node set
to m, from the runs from u. -/
theorem writerWP_setX_of_xwp {α : Type} {x : NodeId} {m : KNode} {f : M α} {c : Ctx} {u : W}
    {post : α → W → Prop} (h : XWP x m f c u (fun r u2 => post r (setX x m u2))) :
    WriterWP f c (setX x m u) post := by
  intro r w2 h2
  obtain ⟨u2, h3, rfl⟩ := h.1 r w2 h2
  exact h.2 r u2 h3

/-! ## Runs of the steps -/

theorem run_read_bind {β : Type} (g : Ctx → M β) (c : Ctx) (u : W) : (read >>= g) c u = g c c u := rfl
theorem run_get_bind {β : Type} (g : W → M β) (c : Ctx) (u : W) :
    ((MonadState.get : M W) >>= g) c u = g u c u := rfl
theorem run_pure {α : Type} (a : α) (c : Ctx) (u : W) : (pure a : M α) c u = .ok (a, u) := rfl
theorem run_pure_bind {α β : Type} (a : α) (g : α → M β) (c : Ctx) (u : W) :
    (pure a >>= g) c u = g a c u := rfl
theorem run_modify (f : W → W) (c : Ctx) (u : W) : (modify f : M Unit) c u = .ok ((), f u) := rfl
theorem run_modify_bind {β : Type} (f : W → W) (g : Unit → M β) (c : Ctx) (u : W) :
    (modify f >>= g) c u = g () c (f u) := rfl
theorem run_set_bind {β : Type} (v : W) (g : Unit → M β) (c : Ctx) (u : W) :
    (set v >>= g) c u = g () c v := rfl
theorem run_throw {α : Type} (e : String) (c : Ctx) (u : W) : (throw e : M α) c u = .error e := rfl
theorem run_throw_bind {α β : Type} (e : String) (g : α → M β) (c : Ctx) (u : W) :
    ((throw e : M α) >>= g) c u = .error e := rfl
theorem run_bind_ok_iff {α β : Type} (f : M α) (g : α → M β) (c : Ctx) (w : W) (x : β × W) :
    (f >>= g) c w = .ok x ↔ ∃ a w', f c w = .ok (a, w') ∧ g a c w' = .ok x := by
  show (f c w).bind (fun p => g p.1 c p.2) = _ ↔ _
  cases hf : f c w with
  | error e => simp [Except.bind]
  | ok aw =>
    rcases aw with ⟨a0, w0⟩
    simp only [Except.bind]
    constructor
    · intro h; exact ⟨a0, w0, rfl, h⟩
    · rintro ⟨a, w', h1, h2⟩
      cases h1
      exact h2

theorem run_bind_ok {α β : Type} (f : M α) (g : α → M β) (c : Ctx) (u : W) (a : α) (u' : W)
    (h : f c u = .ok (a, u')) : (f >>= g) c u = g a c u' := by
  show (f c u).bind (fun p => g p.1 c p.2) = _
  rw [h]; rfl
theorem run_fresh (c : Ctx) (u : W) : fresh c u = .ok (u.next, { u with next := u.next + 2 }) := rfl
theorem run_note (s : String) (c : Ctx) (u : W) :
    note s c u = .ok ((), { u with trail := s :: u.trail }) := rfl
theorem run_putNode (y : NodeId) (n : KNode) (c : Ctx) (u : W) :
    putNode y n c u = .ok ((), { u with nodes := upsert u.nodes y n }) := rfl

theorem run_getNode_some (y : NodeId) (n : KNode) (c : Ctx) (u : W) (h : u.nodes.lookup y = some n) :
    getNode y c u = .ok (n, u) := by
  unfold getNode
  rw [run_get_bind]
  simp only [h]
  rfl

theorem run_getNode_none (y : NodeId) (c : Ctx) (u : W) (h : u.nodes.lookup y = none) (nd : Node BVal)
    (hv : c.view y = some nd) (hc : (nd.isData || decide (c.p.keyMax < nd.level)) = false) :
    getNode y c u = .ok (⟨c.p.heightOf nd.level == 0, klongsOf nd.hist⟩,
      { u with nodes := u.nodes ++ [(y, ⟨c.p.heightOf nd.level == 0, klongsOf nd.hist⟩)],
                 gh := (y, c.p.segOf nd.level, c.p.heightOf nd.level) :: u.gh }) := by
  unfold getNode
  rw [run_get_bind]
  simp only [h]
  rw [run_read_bind]
  simp only [hv, hc, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- A successful `getNode` of an id not cached: the node of the view. -/
theorem run_getNode_none_ok (y : NodeId) (c : Ctx) (u : W) (h : u.nodes.lookup y = none) (r : KNode)
    (w2 : W) (h2 : getNode y c u = .ok (r, w2)) :
    ∃ nd, c.view y = some nd ∧ (nd.isData || decide (c.p.keyMax < nd.level)) = false ∧
      r = ⟨c.p.heightOf nd.level == 0, klongsOf nd.hist⟩ ∧
      w2 = { u with
        nodes := u.nodes ++ [(y, ⟨c.p.heightOf nd.level == 0, klongsOf nd.hist⟩)],
        gh := (y, c.p.segOf nd.level, c.p.heightOf nd.level) :: u.gh } := by
  cases hv : c.view y with
  | none =>
    unfold getNode at h2
    rw [run_get_bind] at h2
    simp only [h] at h2
    rw [run_read_bind] at h2
    simp only [hv] at h2
    cases h2
  | some nd =>
    cases hc : (nd.isData || decide (c.p.keyMax < nd.level)) with
    | true =>
      unfold getNode at h2
      rw [run_get_bind] at h2
      simp only [h] at h2
      rw [run_read_bind] at h2
      simp only [hv, hc, ↓reduceIte] at h2
      cases h2
    | false =>
      rw [run_getNode_none y c u h nd hv hc] at h2
      cases h2
      exact ⟨nd, rfl, hc, rfl, rfl⟩

/-! ## Upsert at two ids -/

theorem upsert_of_any (ns : List (NodeId × KNode)) (x : NodeId) (m : KNode)
    (h : ns.any (fun q => q.1 == x) = true) :
    upsert ns x m = ns.map (fun q => if q.1 == x then (x, m) else q) := by
  unfold upsert; rw [if_pos h]

theorem upsert_of_not_any (ns : List (NodeId × KNode)) (x : NodeId) (m : KNode)
    (h : ns.any (fun q => q.1 == x) = false) : upsert ns x m = ns ++ [(x, m)] := by
  unfold upsert; rw [if_neg (by simp [h])]

theorem any_map_set (ns : List (NodeId × KNode)) (x z : NodeId) (m : KNode) :
    (ns.map (fun q => if q.1 == x then (x, m) else q)).any (fun q => q.1 == z) =
      ns.any (fun q => q.1 == z) := by
  induction ns with
  | nil => rfl
  | cons q qs ih =>
    simp only [List.map_cons, List.any_cons, ih]
    by_cases hq : q.1 = x
    · simp only [hq, beq_self_eq_true, ↓reduceIte]
    · simp only [beq_iff_eq, hq, ↓reduceIte]

theorem upsert_comm (ns : List (NodeId × KNode)) (x y : NodeId) (m n : KNode) (hxy : y ≠ x)
    (hx : ns.any (fun q => q.1 == x) = true) :
    upsert (upsert ns x m) y n = upsert (upsert ns y n) x m := by
  have hxy' : x ≠ y := Ne.symm hxy
  rw [upsert_of_any ns x m hx]
  cases hy : ns.any (fun q => q.1 == y) with
  | true =>
    rw [upsert_of_any _ y n (by rw [any_map_set]; exact hy), upsert_of_any ns y n hy,
      upsert_of_any _ x m (by rw [any_map_set]; exact hx), List.map_map, List.map_map]
    apply List.map_congr_left
    intro q _
    simp only [Function.comp]
    by_cases h1 : q.1 = x
    · simp [h1, hxy']
    · by_cases h2 : q.1 = y
      · simp [h2, hxy]
      · simp [h1, h2]
  | false =>
    rw [upsert_of_not_any _ y n (by rw [any_map_set]; exact hy), upsert_of_not_any ns y n hy,
      upsert_of_any _ x m (by simp [List.any_append, hx]), List.map_append]
    simp [hxy]

theorem upsert_append_ne (ns : List (NodeId × KNode)) (x y : NodeId) (m n : KNode) (hxy : y ≠ x)
    (hx : ns.any (fun q => q.1 == x) = true) :
    upsert (ns ++ [(y, n)]) x m = upsert ns x m ++ [(y, n)] := by
  rw [upsert_of_any _ x m (by simp [List.any_append, hx]), upsert_of_any ns x m hx, List.map_append]
  simp [hxy]

theorem any_of_lookup (ns : List (NodeId × KNode)) (x : NodeId) (n : KNode)
    (h : ns.lookup x = some n) : ns.any (fun q => q.1 == x) = true := by
  induction ns with
  | nil => simp at h
  | cons q qs ih =>
    rcases q with ⟨a, b⟩
    by_cases hax : a = x
    · simp [hax]
    · have : (List.lookup x ((a, b) :: qs)) = qs.lookup x := by
        simp only [List.lookup, show (x == a) = false from by simpa using Ne.symm hax]
      rw [this] at h
      simp [ih h]

theorem lookup_upsert_x (ns : List (NodeId × KNode)) (x y : NodeId) (n : KNode) (hy : y ≠ x)
    (m : KNode) (h : ns.lookup x = some m) : (upsert ns y n).lookup x = some m := by
  rw [lookup_upsert]; simp [Ne.symm hy, h]

/-! ## The calculus -/

section
variable {x : NodeId} {m nx : KNode}

theorem xwp_mono {α : Type} {f : M α} {c : Ctx} {u : W} {post post' : α → W → Prop}
    (h : XWP x m f c u post) (hp : ∀ r v, post r v → post' r v) : XWP x m f c u post' :=
  ⟨h.1, writerWP_mono h.2 hp⟩

theorem xwp_bind {α β : Type} {f : M α} {g : α → M β} {c : Ctx} {u : W} {post : β → W → Prop}
    (h : XWP x m f c u (fun a u' => XWP x m (g a) c u' post)) : XWP x m (f >>= g) c u post := by
  obtain ⟨hr, hw⟩ := h
  refine ⟨?_, (writerWP_bind f g c u post).mpr (writerWP_mono hw fun _ _ h => h.2)⟩
  intro r w2 h2
  simp only [bind, ReaderT.bind, StateT.bind] at h2 ⊢
  cases hf : f c (setX x m u) with
  | error e => rw [hf] at h2; cases h2
  | ok aw =>
    rcases aw with ⟨a, w'⟩
    rw [hf] at h2
    obtain ⟨u', hu', rfl⟩ := hr a w' hf
    obtain ⟨u2, hu2, rfl⟩ := (hw a u' hu').1 r w2 h2
    exact ⟨u2, by rw [hu']; exact hu2, rfl⟩

/-- A step whose runs are known on both sides. -/
theorem xwp_of_run {α : Type} {f : M α} {c : Ctx} {u : W} {post : α → W → Prop} (a : α) (u' : W)
    (h1 : f c u = .ok (a, u')) (h2 : f c (setX x m u) = .ok (a, setX x m u')) (hp : post a u') :
    XWP x m f c u post := by
  refine ⟨fun r w2 h => ?_, fun r w2 h => ?_⟩
  · rw [h2] at h; cases h; exact ⟨u', h1, rfl⟩
  · rw [h1] at h; cases h; exact hp

/-- A step that fails on both sides. -/
theorem xwp_of_err {α : Type} {f : M α} {c : Ctx} {u : W} {post : α → W → Prop} (e : String)
    (h1 : f c u = .error e) (h2 : f c (setX x m u) = .error e) : XWP x m f c u post := by
  refine ⟨fun r w2 h => ?_, fun r w2 h => ?_⟩
  · rw [h2] at h; cases h
  · rw [h1] at h; cases h

/-- A step that fails on both sides. -/
theorem xwp_of_noOk {α : Type} {f : M α} {c : Ctx} {u : W} {post : α → W → Prop}
    (h1 : ∀ r u', f c u = .ok (r, u') → False) (h2 : ∀ r w2, f c (setX x m u) = .ok (r, w2) → False) :
    XWP x m f c u post :=
  ⟨fun r w2 h => (h2 r w2 h).elim, fun r w2 h => (h1 r w2 h).elim⟩

theorem xwp_ite {α : Type} (b : Prop) [Decidable b] {f g : M α} {c : Ctx} {u : W}
    {post : α → W → Prop} (h1 : b → XWP x m f c u post) (h2 : ¬ b → XWP x m g c u post) :
    XWP x m (if b then f else g) c u post := by
  by_cases hb : b
  · simpa [hb] using h1 hb
  · simpa [hb] using h2 hb

theorem xwp_pure {α : Type} (a : α) {c : Ctx} {u : W} {post : α → W → Prop} (h : post a u) :
    XWP x m (pure a) c u post :=
  xwp_of_run a u rfl rfl h

theorem xwp_throw {α : Type} (e : String) {c : Ctx} {u : W} {post : α → W → Prop} :
    XWP x m (throw e : M α) c u post :=
  xwp_of_err e rfl rfl

theorem xwp_read {c : Ctx} {u : W} {post : Ctx → W → Prop} (h : post c u) : XWP x m read c u post :=
  xwp_of_run c u rfl rfl h

variable (path0 : List (Option Nat × NodeId))

theorem xwp_note (s : String) {c : Ctx} {u : W} {post : Unit → W → Prop} (hJ : RJ x nx path0 u)
    (h : ∀ u', RJ x nx path0 u' → post () u') : XWP x m (note s) c u post :=
  xwp_of_run () _ rfl rfl (h _ hJ)

/-- A step that changes no node, the key access path, nor the next id. -/
theorem xwp_modify (f : W → W) {c : Ctx} {u : W} {post : Unit → W → Prop}
    (hf : f (setX x m u) = setX x m (f u)) (hfJ : RJ x nx path0 (f u))
    (h : ∀ u', RJ x nx path0 u' → post () u') : XWP x m (modify f) c u post :=
  xwp_of_run () _ rfl (by rw [run_modify, hf]) (h _ hfJ)

theorem xwp_setMadeFor (y : NodeId) (o : Option NodeId) {c : Ctx} {u : W} {post : Unit → W → Prop}
    (hJ : RJ x nx path0 u) (h : ∀ u', RJ x nx path0 u' → post () u') : XWP x m (setMadeFor y o) c u post := by
  cases o with
  | none => exact xwp_pure () (h _ hJ)
  | some o => exact xwp_of_run () _ rfl rfl (h _ hJ)

theorem xwp_replacedBy (y : NodeId) {c : Ctx} {u : W} {post : Option NodeId → W → Prop}
    (hJ : RJ x nx path0 u) (h : ∀ r u', RJ x nx path0 u' → post r u') : XWP x m (replacedBy y) c u post :=
  xwp_of_run _ _ rfl rfl (h _ _ hJ)

theorem xwp_fresh {c : Ctx} {u : W} {post : NodeId → W → Prop}
    (hJ : RJ x nx path0 u) (h : ∀ r u', RJ x nx path0 u' → r ≠ x → post r u') : XWP x m fresh c u post :=
  xwp_of_run _ _ rfl rfl (h _ _ ⟨hJ.1, by have := hJ.2.1; show x < u.next + 2; omega, hJ.2.2⟩
    (by have := hJ.2.1; omega))

theorem xwp_klongAt (d : Nat) {c : Ctx} {u : W} {post : Nat → W → Prop}
    (hJ : RJ x nx path0 u) (h : ∀ k u', RJ x nx path0 u' → post k u') : XWP x m (klongAt d) c u post := by
  unfold klongAt
  cases hp : u.path[d]? with
  | none =>
    refine xwp_of_noOk ?_ ?_ <;> intro _ _ hh <;> revert hh <;> (rw [run_get_bind]; simp only [setX, hp]; intro hh; cases hh)
  | some e =>
    rcases e with ⟨o, y⟩
    cases o with
    | none => refine xwp_of_noOk ?_ ?_ <;> intro _ _ hh <;> revert hh <;> (rw [run_get_bind]; simp only [setX, hp]; intro hh; cases hh)
    | some k =>
      refine xwp_of_run k u ?_ ?_ (h _ _ hJ) <;> (rw [run_get_bind]; simp only [setX, hp]; rfl)

theorem xwp_pathNode (d : Nat) {c : Ctx} {u : W} {post : NodeId → W → Prop}
    (hJ : RJ x nx path0 u) (h : ∀ e, path0[d]? = some e → post e.2 u) : XWP x m (pathNode d) c u post := by
  unfold pathNode
  cases hp : u.path[d]? with
  | none =>
    refine xwp_of_noOk ?_ ?_ <;> intro _ _ hh <;> revert hh <;> (rw [run_get_bind]; simp only [setX, hp]; intro hh; cases hh)
  | some e =>
    refine xwp_of_run e.2 u ?_ ?_ (h e (by rw [← hJ.2.2]; exact hp)) <;>
      (rw [run_get_bind]; simp only [setX, hp]; rfl)

theorem xwp_parentAt_zero {c : Ctx} {u : W} {post : Option NodeId → W → Prop}
    (hJ : RJ x nx path0 u) (h : ∀ u', RJ x nx path0 u' → post none u') : XWP x m (parentAt 0) c u post :=
  xwp_pure none (h _ hJ)

theorem xwp_parentAt_succ (e : Nat) {c : Ctx} {u : W} {post : Option NodeId → W → Prop}
    (hJ : RJ x nx path0 u) (h : ∀ q, (∃ a, path0[e]? = some (a, q)) → post (some q) u) :
    XWP x m (parentAt (e + 1)) c u post := by
  unfold parentAt
  refine xwp_bind (xwp_pathNode path0 e hJ ?_)
  intro ee hee
  exact xwp_pure _ (h ee.2 ⟨ee.1, hee⟩)

theorem xwp_getNode (y : NodeId) {c : Ctx} {u : W} {post : KNode → W → Prop}
    (hJ : RJ x nx path0 u) (hy : y ≠ x) (h : ∀ n u', RJ x nx path0 u' → post n u') :
    XWP x m (getNode y) c u post := by
  obtain ⟨hnx, hxn, hpath⟩ := hJ
  have hany := any_of_lookup u.nodes x nx hnx
  cases hl : u.nodes.lookup y with
  | some n =>
    have hl' : (setX x m u).nodes.lookup y = some n := by
      simp only [setX, lookup_upsert, hy, ↓reduceIte, hl]
    exact xwp_of_run n u (run_getNode_some y n c u hl) (run_getNode_some y n c _ hl')
      (h n u ⟨hnx, hxn, hpath⟩)
  | none =>
    have hl' : (setX x m u).nodes.lookup y = none := by
      simp only [setX, lookup_upsert, hy, ↓reduceIte, hl]
    refine ⟨fun r w2 h2 => ?_, fun r w2 h2 => ?_⟩
    · obtain ⟨nd, hv, hc, rfl, rfl⟩ := run_getNode_none_ok y c _ hl' r w2 h2
      refine ⟨_, run_getNode_none y c u hl nd hv hc, ?_⟩
      simp only [setX, upsert_append_ne u.nodes x y m _ hy hany]
    · obtain ⟨nd, hv, hc, rfl, rfl⟩ := run_getNode_none_ok y c u hl r w2 h2
      refine h _ _ ⟨?_, hxn, hpath⟩
      simp only [List.lookup_append, hnx, Option.some_or]

theorem xwp_ghOf (y : NodeId) {c : Ctx} {u : W} {post : Nat × Nat → W → Prop}
    (hJ : RJ x nx path0 u) (hy : y ≠ x) (h : ∀ r u', RJ x nx path0 u' → post r u') :
    XWP x m (ghOf y) c u post := by
  unfold ghOf
  refine xwp_bind (xwp_getNode path0 y hJ hy ?_)
  intro _ u' hJ'
  cases hg : u'.gh.lookup y with
  | none => refine xwp_of_noOk ?_ ?_ <;> intro _ _ hh <;> revert hh <;> (rw [run_get_bind]; simp only [setX, hg]; intro hh; cases hh)
  | some v => refine xwp_of_run v u' ?_ ?_ (h _ _ hJ') <;> (rw [run_get_bind]; simp only [setX, hg]; rfl)

theorem xwp_putNode (y : NodeId) (n : KNode) {c : Ctx} {u : W} {post : Unit → W → Prop}
    (hJ : RJ x nx path0 u) (hy : y ≠ x) (h : ∀ u', RJ x nx path0 u' → post () u') :
    XWP x m (putNode y n) c u post := by
  obtain ⟨hnx, hxn, hpath⟩ := hJ
  have hany := any_of_lookup u.nodes x nx hnx
  refine xwp_of_run () _ rfl ?_ (h _ ⟨lookup_upsert_x u.nodes x y n hy nx hnx, hxn, hpath⟩)
  rw [run_putNode]
  simp only [setX, upsert_comm u.nodes x y m n hy hany]

theorem xwp_newKey (g h : Nat) (leaf : Bool) (ks : List Klong) {c : Ctx} {u : W}
    {post : NodeId → W → Prop} (hJ : RJ x nx path0 u) (hk : ∀ r u', RJ x nx path0 u' → r ≠ x → post r u') :
    XWP x m (newKey g h leaf ks) c u post := by
  obtain ⟨hnx, hxn, hpath⟩ := hJ
  have hany := any_of_lookup u.nodes x nx hnx
  have hne : u.next ≠ x := by omega
  have hJ' : ∀ (o : List (NodeId × Nat × Nat)), RJ x nx path0
      { u with next := u.next + 2, outside := o,
               nodes := u.nodes ++ [(u.next, ⟨leaf, ks⟩)], gh := (u.next, g, h) :: u.gh,
               made := u.made ++ [⟨u.next, c.p.keyLevel g h, false⟩] } := by
    intro o
    refine ⟨?_, by show x < u.next + 2; omega, hpath⟩
    simp only [List.lookup_append, hnx, Option.some_or]
  unfold newKey
  by_cases hb : (c.p.G < g || c.p.H < h) = true
  · refine xwp_of_run u.next _ ?_ ?_ (hk _ _ (hJ' ((u.next, g, h) :: u.outside)) hne)
    · rw [run_read_bind]; dsimp only; rw [run_bind_ok _ _ c u u.next _ (run_fresh c u)]
      simp only [hb, ↓reduceIte]
      rfl
    · rw [run_read_bind]; dsimp only; rw [run_bind_ok _ _ c (setX x m u) u.next _ (run_fresh c (setX x m u))]
      simp only [hb, ↓reduceIte]
      show Except.ok _ = Except.ok _
      simp only [setX, upsert_append_ne u.nodes x u.next m _ hne hany]
  · refine xwp_of_run u.next _ ?_ ?_ (hk _ _ (hJ' u.outside) hne)
    · rw [run_read_bind]; dsimp only; rw [run_bind_ok _ _ c u u.next _ (run_fresh c u)]
      simp only [hb, Bool.false_eq_true, ↓reduceIte]
      rfl
    · rw [run_read_bind]; dsimp only; rw [run_bind_ok _ _ c (setX x m u) u.next _ (run_fresh c (setX x m u))]
      simp only [hb, Bool.false_eq_true, ↓reduceIte]
      show Except.ok _ = Except.ok _
      simp only [setX, upsert_append_ne u.nodes x u.next m _ hne hany]

theorem xwp_newSuperRoot (y : NodeId) {c : Ctx} {u : W} {post : Unit → W → Prop}
    (hJ : RJ x nx path0 u) (h : ∀ u', RJ x nx path0 u' → post () u') :
    XWP x m (newSuperRoot y) c u post := by
  obtain ⟨hnx, hxn, hpath⟩ := hJ
  unfold newSuperRoot
  by_cases ht : (c.i == u.top.time) = true
  · refine xwp_of_run () ?w ?h1 ?h2 ?h3
    case h1 => rw [run_read_bind, run_get_bind]; simp only [ht, ↓reduceIte]; rfl
    case h2 => rw [run_read_bind, run_get_bind]; simp only [setX, ht, ↓reduceIte]; rfl
    case h3 => exact h _ ⟨hnx, hxn, hpath⟩
  · refine xwp_of_run () ?v ?k1 ?k2 ?k3
    case k1 => rw [run_read_bind, run_get_bind]; simp only [ht, Bool.false_eq_true, ↓reduceIte]; rfl
    case k2 => rw [run_read_bind, run_get_bind]; simp only [setX, ht, Bool.false_eq_true, ↓reduceIte]; rfl
    case k3 => exact h _ ⟨hnx, by show x < u.next + 2; omega, hpath⟩

theorem xwp_parentAt_succ' (e : Nat) (a : Option Nat) (q : NodeId) {c : Ctx} {u : W}
    {post : Option NodeId → W → Prop} (hJ : RJ x nx path0 u) (hpe : path0[e]? = some (a, q))
    (h : post (some q) u) : XWP x m (parentAt (e + 1)) c u post :=
  xwp_parentAt_succ path0 e hJ (fun q' ⟨a', ha'⟩ => by
    rw [hpe] at ha'; cases ha'; exact h)

theorem xwp_parentAt_none (e : Nat) {c : Ctx} {u : W} {post : Option NodeId → W → Prop}
    (hJ : RJ x nx path0 u) (hpe : path0[e]? = none) : XWP x m (parentAt (e + 1)) c u post :=
  xwp_parentAt_succ path0 e hJ (fun q' ⟨a', ha'⟩ => by rw [hpe] at ha'; cases ha')

theorem xwp_ghOf' (y : NodeId) {c : Ctx} {u : W} {post : Nat × Nat → W → Prop}
    (hJ : RJ x nx path0 u) (hy : y ≠ x) (h : ∀ g hh u', RJ x nx path0 u' → post (g, hh) u') :
    XWP x m (ghOf y) c u post :=
  xwp_ghOf path0 y hJ hy (fun r u' hJ' => h r.1 r.2 u' hJ')

theorem xwp_foldlM {α β : Type} (xs : List α) (f : β → α → M β) {c : Ctx}
    (hf : ∀ b a u, RJ x nx path0 u → XWP x m (f b a) c u (fun _ v => RJ x nx path0 v)) :
    ∀ (init : β) (u : W), RJ x nx path0 u → XWP x m (xs.foldlM f init) c u (fun _ v => RJ x nx path0 v) := by
  induction xs with
  | nil => intro init u hJ; exact xwp_pure init hJ
  | cons a as ih =>
    intro init u hJ
    rw [List.foldlM_cons]
    exact xwp_bind (xwp_mono (hf init a u hJ) (fun b v hv => ih b v hv))

theorem xwp_replaceOrAdd (last : KNode) (ins : List (Nat × NodeId)) {c : Ctx} {u : W}
    {post : KNode → W → Prop} (hJ : RJ x nx path0 u) (h : ∀ l u', RJ x nx path0 u' → post l u') :
    XWP x m (replaceOrAdd last ins) c u post := by
  unfold replaceOrAdd
  refine xwp_bind (xwp_read ?_)
  refine xwp_mono (xwp_foldlM path0 ins _ ?_ last u hJ) h
  intro b a u' hJ'
  rcases a with ⟨cv, y⟩
  dsimp only
  split
  · exact xwp_throw _
  · exact xwp_pure _ hJ'
  · exact xwp_pure _ hJ'

theorem xwp_addKeys (y : NodeId) (ins : List (Nat × NodeId)) {c : Ctx} {u : W}
    {post : Unit → W → Prop} (hJ : RJ x nx path0 u) (hy : y ≠ x) (h : ∀ u', RJ x nx path0 u' → post () u') :
    XWP x m (addKeys y ins) c u post := by
  unfold addKeys
  refine xwp_bind (xwp_read ?_)
  refine xwp_bind (xwp_getNode path0 y hJ hy ?_)
  intro n u' hJ'
  exact xwp_putNode path0 y _ hJ' hy h

theorem xwp_spaceSplits {c : Ctx} {u : W} {post : Unit → W → Prop} (hJ : RJ x nx path0 u)
    (h : ∀ u', RJ x nx path0 u' → post () u') :
    XWP x m (modify (fun w => { w with spaceSplits := w.spaceSplits + 1 })) c u post :=
  xwp_modify path0 _ rfl hJ h

end

/-- One step of the relational walk. -/
macro "xwpStep" : tactic => `(tactic| first
  | (refine xwp_bind (xwp_ite _ ?_ ?_) <;> intro _)
  | (refine xwp_ite _ ?_ ?_ <;> intro _)
  | exact xwp_throw _
  | (with_reducible refine xwp_bind (xwp_read ?_))
  | (with_reducible refine xwp_bind (xwp_getNode _ _ (by assumption) (by assumption) ?_); intro _ _ _)
  | (with_reducible refine xwp_getNode _ _ (by assumption) (by assumption) ?_; intro _ _ _)
  | (with_reducible refine xwp_bind (xwp_ghOf' _ _ (by assumption) (by assumption) ?_); intro _ _ _ _)
  | (with_reducible refine xwp_bind (xwp_note _ _ (by assumption) ?_); intro _ _)
  | (with_reducible refine xwp_note _ _ (by assumption) ?_; intro _ _)
  | (with_reducible refine xwp_bind (xwp_spaceSplits _ (by assumption) ?_); intro _ _)
  | (with_reducible refine xwp_bind (xwp_newKey _ _ _ _ _ (by assumption) ?_); intro _ _ _ _)
  | (with_reducible refine xwp_bind (xwp_setMadeFor _ _ _ (by assumption) ?_); intro _ _)
  | (with_reducible refine xwp_bind (xwp_replacedBy _ _ (by assumption) ?_); intro _ _ _)
  | (with_reducible refine xwp_bind (xwp_putNode _ _ _ (by assumption) (by assumption) ?_); intro _ _)
  | (with_reducible refine xwp_putNode _ _ _ (by assumption) (by assumption) ?_; intro _ _)
  | (with_reducible refine xwp_bind (xwp_newSuperRoot _ _ (by assumption) ?_); intro _ _)
  | (with_reducible refine xwp_newSuperRoot _ _ (by assumption) ?_; intro _ _)
  | (with_reducible refine xwp_bind (xwp_klongAt _ _ (by assumption) ?_); intro _ _ _)
  | (with_reducible refine xwp_bind (xwp_replaceOrAdd _ _ _ (by assumption) ?_); intro _ _ _)
  | (with_reducible refine xwp_bind (xwp_parentAt_zero _ (by assumption) ?_); intro _ _)
  | (with_reducible refine xwp_bind (xwp_parentAt_succ' _ _ _ _ (by assumption) (by assumption) ?_))
  | (with_reducible exact xwp_bind (xwp_parentAt_none _ _ (by assumption) (by assumption)))
  | (with_reducible refine xwp_bind (xwp_pure _ ?_))
  | (with_reducible refine xwp_pure _ ?_)
  | assumption)

section
variable {x : NodeId} {m nx : KNode} (path0 : List (Option Nat × NodeId))

set_option maxHeartbeats 4000000 in
/-- The relational walk of a full node at depth 0: the space root's split. -/
theorem xwp_handleFullWith_zero (up : NodeId → List (Nat × NodeId) → M Unit) (y : NodeId)
    (ins : List (Nat × NodeId)) (last : KNode) (compact : Bool) {c : Ctx} {u : W}
    (hJ : RJ x nx path0 u) (hy : y ≠ x) :
    XWP x m (handleFullWith up 0 y ins last compact) c u (fun _ v => RJ x nx path0 v) := by
  unfold handleFullWith
  simp only []
  repeat' (first
    | xwpStep
    | (simp only [Bool.false_eq_true, ↓reduceIte])
    | split)

set_option maxHeartbeats 4000000 in
/-- The relational walk of a full node at depth e + 1, whose parent q on the key
access path is not x, given the walk of `up` at q. -/
theorem xwp_handleFullWith_succ (up : NodeId → List (Nat × NodeId) → M Unit) (e : Nat)
    (a : Option Nat) (q : NodeId) (y : NodeId) (ins : List (Nat × NodeId)) (last : KNode)
    (compact : Bool) {c : Ctx} {u : W} (hJ : RJ x nx path0 u) (hy : y ≠ x)
    (hpe : path0[e]? = some (a, q)) (hq : q ≠ x)
    (hup : ∀ more u', RJ x nx path0 u' → XWP x m (up q more) c u' (fun _ v => RJ x nx path0 v)) :
    XWP x m (handleFullWith up (e + 1) y ins last compact) c u (fun _ v => RJ x nx path0 v) := by
  unfold handleFullWith
  simp only []
  repeat' (first
    | xwpStep
    | (refine xwp_bind (xwp_mono (hup _ _ (by assumption)) ?_); intro _ _ _)
    | (simp only [Bool.false_eq_true, ↓reduceIte])
    | split)

/-- The relational walk of a full node at depth e + 1 with no entry e on the key
access path: it fails. -/
theorem xwp_handleFullWith_none (up : NodeId → List (Nat × NodeId) → M Unit) (e : Nat)
    (y : NodeId) (ins : List (Nat × NodeId)) (last : KNode)
    (compact : Bool) {c : Ctx} {u : W} (hJ : RJ x nx path0 u) (hy : y ≠ x)
    (hpe : path0[e]? = none) :
    XWP x m (handleFullWith up (e + 1) y ins last compact) c u (fun _ v => RJ x nx path0 v) := by
  unfold handleFullWith
  simp only []
  repeat' (first
    | xwpStep
    | (simp only [Bool.false_eq_true, ↓reduceIte])
    | split)

/-- The relational walk of the cascade: `appendKlongs` at depth d from node y,
neither of which nor any node of the key access path above is x. -/
theorem xwp_appendKlongs : ∀ (depth : Nat) (y : NodeId) (ins : List (Nat × NodeId)) (c : Ctx) (u : W),
    RJ x nx path0 u → y ≠ x → (∀ i e, i < depth → path0[i]? = some e → e.2 ≠ x) →
    XWP x m (appendKlongs depth y ins) c u (fun _ v => RJ x nx path0 v) := by
  intro depth
  induction depth with
  | zero =>
    intro y ins c u hJ hy _
    rw [appendKlongs_step_dead]
    refine xwp_bind (xwp_read ?_)
    refine xwp_bind (xwp_getNode path0 y hJ hy ?_)
    intro n u' hJ'
    simp only []
    refine xwp_ite _ (fun _ => xwp_handleFullWith_zero path0 _ y ins _ false hJ' hy) (fun _ => ?_)
    refine xwp_ite _ (fun _ => xwp_handleFullWith_zero path0 _ y ins _ true hJ' hy) (fun _ => ?_)
    exact xwp_addKeys path0 y ins hJ' hy (fun _ h => h)
  | succ d ih =>
    intro y ins c u hJ hy hp
    rw [appendKlongs_step_dead]
    refine xwp_bind (xwp_read ?_)
    refine xwp_bind (xwp_getNode path0 y hJ hy ?_)
    intro n u' hJ'
    simp only []
    cases hpe : path0[d]? with
    | none =>
      refine xwp_ite _ (fun _ => xwp_handleFullWith_none path0 _ d y ins _ false hJ' hy hpe) (fun _ => ?_)
      refine xwp_ite _ (fun _ => xwp_handleFullWith_none path0 _ d y ins _ true hJ' hy hpe) (fun _ => ?_)
      exact xwp_addKeys path0 y ins hJ' hy (fun _ h => h)
    | some e =>
      rcases e with ⟨a, q⟩
      have hq : q ≠ x := hp d (a, q) (Nat.lt_succ_self d) hpe
      have hup : ∀ more u'', RJ x nx path0 u'' →
          XWP x m (appendKlongs d q more) c u'' (fun _ v => RJ x nx path0 v) :=
        fun more u'' hJ'' => ih q more c u'' hJ'' hq (fun i e hi he => hp i e (by omega) he)
      refine xwp_ite _ (fun _ => xwp_handleFullWith_succ path0 _ d a q y ins _ false hJ' hy hpe hq hup)
        (fun _ => ?_)
      refine xwp_ite _ (fun _ => xwp_handleFullWith_succ path0 _ d a q y ins _ true hJ' hy hpe hq hup)
        (fun _ => ?_)
      exact xwp_addKeys path0 y ins hJ' hy (fun _ h => h)


/-- `handleFull` (a delete's full node) in the walk, at depth 0. -/
theorem xwp_handleFull_zero (y : NodeId) (last : KNode) (compact : Bool) {c : Ctx} {u : W}
    (hJ : RJ x nx path0 u) (hy : y ≠ x) :
    XWP x m (handleFull 0 y last compact) c u (fun _ v => RJ x nx path0 v) :=
  xwp_handleFullWith_zero path0 _ y [] last compact hJ hy

/-- `handleFull` in the walk at depth d + 1: its cascade goes up the key access
path, none of whose nodes is x. -/
theorem xwp_handleFull_succ (d : Nat) (y : NodeId) (last : KNode) (compact : Bool) {c : Ctx} {u : W}
    (hJ : RJ x nx path0 u) (hy : y ≠ x) (hp : ∀ i e, i ≤ d → path0[i]? = some e → e.2 ≠ x) :
    XWP x m (handleFull (d + 1) y last compact) c u (fun _ v => RJ x nx path0 v) := by
  unfold handleFull
  cases hpe : path0[d]? with
  | none => exact xwp_handleFullWith_none path0 _ d y [] last compact hJ hy hpe
  | some e =>
    rcases e with ⟨a, q⟩
    exact xwp_handleFullWith_succ path0 _ d a q y [] last compact hJ hy hpe (hp d (a, q) (Nat.le_refl _) hpe)
      (fun more u' hJ' => xwp_appendKlongs path0 d q more c u' hJ' (hp d (a, q) (Nat.le_refl _) hpe)
        (fun i e hi he => hp i e (by omega) he))

end

/-! ## The two steps of a segment collapse commute -/

/-- `replaceRoot` with the two steps of a segment root's collapse the other way
round (bergdb 026-16, section 5.3): the klong of the segment leaf to the root's
child first, with its cascade, then the unlink of the root. -/
def replaceRootLF (x : NodeId) (depth only : Nat) : M Unit := do
  let c ← read
  let n ← getNode x
  match n.ptr? only with
  | none => throw s!"corrupt: root collapse at {c.i}: klong {only} of {x} is no key klong"
  | some child =>
    match depth with
    | 0 =>
      note "rc.replace.space"
      unlink x
      newSuperRoot child
    | d + 1 =>
      note "rc.replace.segment"
      let leaf ← pathNode d
      let k ← klongAt (d + 1)
      appendKlongs d leaf [(k, child)]
      unlink x

theorem run_unlink (x : NodeId) (n : KNode) (c : Ctx) (u : W) (hx : u.nodes.lookup x = some n) :
    unlink x c u = if n.lastTime == some c.i then .ok ((), setX x (n.toPrev (c.i - 1)) u)
      else .ok ((), u) := by
  unfold unlink
  rw [run_read_bind]
  rw [run_bind_ok _ _ c u n u (run_getNode_some x n c u hx)]
  split <;> rfl

theorem run_pathNode_some (d : Nat) (e : Option Nat × NodeId) (c : Ctx) (u : W) (h : u.path[d]? = some e) :
    pathNode d c u = .ok (e.2, u) := by
  unfold pathNode; rw [run_get_bind]; simp only [h]; rfl

theorem run_pathNode_none (d : Nat) (c : Ctx) (u : W) (h : u.path[d]? = none) (r : NodeId) (w : W) :
    pathNode d c u ≠ .ok (r, w) := by
  unfold pathNode; rw [run_get_bind]; simp only [h]; intro h'; cases h'

theorem run_klongAt_some (d k : Nat) (y : NodeId) (c : Ctx) (u : W) (h : u.path[d]? = some (some k, y)) :
    klongAt d c u = .ok (k, u) := by
  unfold klongAt; rw [run_get_bind]; simp only [h]; rfl

theorem run_klongAt_ok (d : Nat) (c : Ctx) (u : W) (k : Nat) (w : W) (h : klongAt d c u = .ok (k, w)) :
    w = u ∧ ∃ y, u.path[d]? = some (some k, y) := by
  unfold klongAt at h; rw [run_get_bind] at h
  cases hp : u.path[d]? with
  | none => simp only [hp] at h; cases h
  | some e =>
    rcases e with ⟨o, y⟩
    cases o with
    | none => simp only [hp] at h; cases h
    | some k' =>
      simp only [hp] at h
      cases h
      exact ⟨rfl, y, rfl⟩

/-- Root collapse's two steps commute: at a segment root x at depth d + 1 of the
key access path, cached and below the next id, with no node of the path above it
x, every successful run of `replaceRoot` is a run of `replaceRootLF`, with the
same result and state. -/
theorem replaceRoot_linkFirst (x : NodeId) (d only : Nat) (c : Ctx) (v : W) (n : KNode)
    (hx : v.nodes.lookup x = some n) (hxn : x < v.next)
    (hpath : ∀ i e, i ≤ d → v.path[i]? = some e → e.2 ≠ x) :
    ∀ r w2, replaceRoot x (d + 1) only c v = .ok (r, w2) → replaceRootLF x (d + 1) only c v = .ok (r, w2) := by
  intro r w2 h
  unfold replaceRoot at h
  unfold replaceRootLF
  rw [run_read_bind] at h ⊢
  dsimp only at h ⊢
  rw [run_bind_ok _ _ c v n v (run_getNode_some x n c v hx)] at h ⊢
  cases hp : n.ptr? only with
  | none => rw [hp] at h; cases h
  | some child =>
    rw [hp] at h
    dsimp only at h ⊢
    rw [run_bind_ok _ _ c v () _ (run_note _ c v)] at h ⊢
    -- the leaf and the klong
    cases hd : v.path[d]? with
    | none =>
      obtain ⟨leaf, u1, h1, _⟩ := (run_bind_ok_iff _ _ c _ _).mp h
      exact absurd h1 (run_pathNode_none d c { v with trail := "rc.replace.segment" :: v.trail } hd leaf u1)
    | some e =>
    rw [run_bind_ok _ _ c _ e.2 _
      (run_pathNode_some d e c { v with trail := "rc.replace.segment" :: v.trail } hd)] at h ⊢
    obtain ⟨k, u2, h3, h4⟩ := (run_bind_ok_iff _ _ c _ _).mp h
    obtain ⟨rfl, _⟩ := run_klongAt_ok (d + 1) c _ k u2 h3
    rw [run_bind_ok _ _ c _ k _ h3]
    have hlx : e.2 ≠ x := hpath d e (Nat.le_refl _) hd
    have hJ : RJ x n v.path { v with trail := "rc.replace.segment" :: v.trail } := ⟨hx, hxn, rfl⟩
    have hW := xwp_appendKlongs (m := n.toPrev (c.i - 1)) v.path d e.2 [(k, child)] c _ hJ hlx
      (fun i e hi he => hpath i e (by omega) he)
    obtain ⟨a, w1, h5, h6⟩ := (run_bind_ok_iff _ _ c _ _).mp h4
    rw [run_unlink x n c { v with trail := "rc.replace.segment" :: v.trail } hx] at h5
    split at h5
    · rename_i hlt
      cases h5
      obtain ⟨u3, h7, rfl⟩ := hW.1 r w2 h6
      have hJ3 := hW.2 r u3 h7
      rw [run_bind_ok _ _ c _ r u3 h7, run_unlink x n c u3 hJ3.1, if_pos hlt]
    · rename_i hlt
      cases h5
      have hJ3 := hW.2 r w2 h6
      rw [run_bind_ok _ _ c _ r w2 h6, run_unlink x n c w2 hJ3.1, if_neg hlt]

end SIS.Tree
