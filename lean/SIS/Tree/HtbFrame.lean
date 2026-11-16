/-
`htb`'s sites (bergdb 025-05, step 8): the frame of the tall nodes. A node found at a
delete's start (in `gh`, not taken back) whose cached height is at or above the fuel
is tall; the delete keeps every tall node as it is in what counts: not taken back, an
inner node of the transaction, with two live klongs or more (`TallOK`). The writer's
steps keep it: a step that changes a node either changes no tall node, or adds klongs,
or points klongs elsewhere, or makes a split's first half or a time split's last
version, which keep two live klongs (a node that the transaction made is split in
place). So root collapse, which takes back a root with one live klong, and the upward
loop, which takes back nodes with one live klong, never take a tall node back.
-/
import SIS.Tree.DeadTop

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- Every node of T is below the next id and not taken back, and the writer reads it
as an inner node of the transaction with two live klongs or more. -/
def TallOK (base : View BVal) (T : NodeId → Prop) (c : Ctx) (w : W) : Prop :=
  ∀ y, T y → y < w.next ∧ w.taken.contains y = false ∧
    ∃ n, wNode c.p base w y = some n ∧ n.leaf = false ∧ n.firstTime = some c.i ∧ 2 ≤ n.cnt

/-- A node with at most one live klong, or a segment leaf, or one that the
transaction did not make, is not tall. -/
theorem TallOK.not_of {base : View BVal} {T : NodeId → Prop} {c : Ctx} {w : W}
    (h : TallOK base T c w) (y : NodeId) (n : KNode) (hn : wNode c.p base w y = some n)
    (hy : n.cnt ≤ 1 ∨ n.leaf = true ∨ n.firstTime ≠ some c.i) : ¬ T y := by
  intro hT
  obtain ⟨_, _, n', hn', hl, hf, hc⟩ := h y hT
  rw [hn] at hn'
  cases hn'
  rcases hy with hy | hy | hy
  · omega
  · rw [hl] at hy; cases hy
  · exact hy hf

/-- The frame: what the tall nodes are read as is kept. -/
theorem TallOK.frame {base : View BVal} {T : NodeId → Prop} {c : Ctx} {w v : W}
    (h : TallOK base T c w) (hn : w.next ≤ v.next)
    (hf : ∀ y, T y → w.taken.contains y = false →
      v.taken.contains y = false ∧ wNode c.p base v y = wNode c.p base w y) :
    TallOK base T c v := by
  intro y hT
  obtain ⟨h1, h2, n, hn', h3⟩ := h y hT
  obtain ⟨h4, h5⟩ := hf y hT h2
  exact ⟨Nat.lt_of_lt_of_le h1 hn, h4, n, by rw [h5]; exact hn', h3⟩

theorem TallOK.of_reads {base : View BVal} {T : NodeId → Prop} {c : Ctx} {w v : W}
    (h : TallOK base T c w) (hr : ReadsAs c.p base w v) : TallOK base T c v :=
  h.frame (Nat.le_of_eq hr.2.2.2.2.symm) (fun y _ hy => ⟨by rw [hr.2.2.1]; exact hy, by rw [hr.1]⟩)

/-- A step that changes only node x, which is not tall, and does not take any node
back. -/
theorem TallOK.put_other {base : View BVal} {T : NodeId → Prop} {c : Ctx} {w v : W}
    (h : TallOK base T c w) (x : NodeId) (hx : ¬ T x) (n : KNode)
    (hv : v.nodes = upsert w.nodes x n) (ht : v.taken = w.taken) (hn : w.next ≤ v.next) :
    TallOK base T c v := by
  refine h.frame hn (fun y hT hy => ⟨by rw [ht]; exact hy, ?_⟩)
  have hyx : y ≠ x := fun e => hx (e ▸ hT)
  unfold wNode
  rw [ht, hv]; simp only [lookup_upsert, hyx, ↓reduceIte]

/-- A step that changes only node x to a node with the tall facts. -/
theorem TallOK.put_good {base : View BVal} {T : NodeId → Prop} {c : Ctx} {w v : W}
    (h : TallOK base T c w) (x : NodeId) (n : KNode)
    (hgood : T x → n.leaf = false ∧ n.firstTime = some c.i ∧ 2 ≤ n.cnt)
    (hv : v.nodes = upsert w.nodes x n) (ht : v.taken = w.taken) (hn : w.next ≤ v.next) :
    TallOK base T c v := by
  intro y hT
  obtain ⟨h1, h2, m, hm, h3⟩ := h y hT
  refine ⟨Nat.lt_of_lt_of_le h1 hn, by rw [ht]; exact h2, ?_⟩
  by_cases hyx : y = x
  · subst hyx
    refine ⟨n, ?_, hgood hT⟩
    unfold wNode
    rw [ht, h2, hv]; simp only [lookup_upsert, ↓reduceIte, Bool.false_eq_true]
  · refine ⟨m, ?_, h3⟩
    rw [← hm]
    unfold wNode
    rw [ht, hv]; simp only [lookup_upsert, hyx, ↓reduceIte]

/-- Taking back a node that is not tall. -/
theorem TallOK.take_other {base : View BVal} {T : NodeId → Prop} {c : Ctx} {w v : W}
    (h : TallOK base T c w) (x : NodeId) (hx : ¬ T x)
    (hv : v.nodes = w.nodes) (ht : v.taken = x :: w.taken) (hn : w.next ≤ v.next) :
    TallOK base T c v := by
  refine h.frame hn (fun y hT hy => ?_)
  have hyx : y ≠ x := fun e => hx (e ▸ hT)
  have hy' : v.taken.contains y = false := by
    rw [ht]; simp only [List.contains_cons, Bool.or_eq_false_iff]
    exact ⟨by simpa using hyx, hy⟩
  refine ⟨hy', ?_⟩
  unfold wNode
  rw [hy', hy, hv]



/-! ## The steps that keep the frame -/

/-- f keeps `TallOK`. -/
def TallKeeps (base : View BVal) (T : NodeId → Prop) {α : Type} (f : M α) : Prop :=
  ∀ (c : Ctx) (w : W), MergeParamsOK c.p → ViewCoherent c base → TallOK base T c w →
    WriterWP f c w (fun _ v => TallOK base T c v)

section Keeps

variable {base : View BVal} {T : NodeId → Prop}

theorem writerWP_of_tk {α : Type} {f : M α} (hf : TallKeeps base T f) (c : Ctx) (w : W)
    (post : α → W → Prop) (hmp : MergeParamsOK c.p) (hvc : ViewCoherent c base) (h : TallOK base T c w)
    (hp : ∀ r v, TallOK base T c v → post r v) : WriterWP f c w post :=
  writerWP_mono (hf c w hmp hvc h) hp

/-- A change of the state that keeps the nodes, what is taken back, and does not
lower the next id. -/
theorem TallOK.same {c : Ctx} {w v : W} (h : TallOK base T c w) (hn : v.nodes = w.nodes)
    (ht : v.taken = w.taken) (hx : w.next ≤ v.next) : TallOK base T c v :=
  h.frame hx (fun y _ hy => ⟨by rw [ht]; exact hy, by unfold wNode; rw [hn, ht]⟩)

theorem tk_getNode (x : NodeId) : TallKeeps base T (getNode x) := fun c w _ hvc h =>
  writerWP_mono (writerWP_getNode_all x c w base hvc) (fun _ _ hv => h.of_reads hv.1)

theorem tk_reads {α : Type} (f : M α)
    (hf : ∀ c w, ViewCoherent c base → WriterWP f c w (fun _ v => ReadsAs c.p base w v)) :
    TallKeeps base T f := fun c w _ hvc h => writerWP_mono (hf c w hvc) (fun _ _ hv => h.of_reads hv)

theorem tk_ghOf (x : NodeId) : TallKeeps base T (ghOf x) := by
  intro c w hmp hvc h
  unfold ghOf
  simp only [writerWP_bind]
  refine writerWP_mono (tk_getNode x c w hmp hvc h) ?_
  intro _ v hv
  simp only [writerWP_get]
  split
  · exact (writerWP_pure _ _ _ _).mpr hv
  · exact writerWP_throw _ _ _ _

theorem tk_pathNode (d : Nat) : TallKeeps base T (pathNode d) := fun c w _ _ h =>
  writerWP_mono (kd_pathNode d c w) (fun _ _ hv => by rw [hv.1]; exact h)

theorem tk_klongAt (d : Nat) : TallKeeps base T (klongAt d) := fun c w _ _ h =>
  writerWP_mono (kd_klongAt d c w) (fun _ _ hv => by rw [hv.1]; exact h)

theorem tk_pathSize : TallKeeps base T pathSize := fun c w _ _ h =>
  writerWP_mono (kd_pathSize c w) (fun _ _ hv => by rw [hv.1]; exact h)

theorem tk_replacedBy (x : NodeId) : TallKeeps base T (replacedBy x) := fun c w _ _ h =>
  writerWP_mono (kd_replacedBy x c w) (fun _ _ hv => by rw [hv.1]; exact h)

theorem tk_note (s : String) : TallKeeps base T (note s) := by
  intro c w _ _ h
  unfold note
  simp only [writerWP_modify]
  exact h.same rfl rfl (Nat.le_refl _)

theorem tk_pathAdd (a : Option Nat) (x : NodeId) : TallKeeps base T (pathAdd a x) := by
  intro c w _ _ h
  unfold pathAdd
  simp only [writerWP_modify]
  exact h.same rfl rfl (Nat.le_refl _)

theorem tk_pathClear : TallKeeps base T pathClear := by
  intro c w _ _ h
  unfold pathClear
  simp only [writerWP_modify]
  exact h.same rfl rfl (Nat.le_refl _)

theorem tk_findRoot : TallKeeps base T findRoot := by
  intro c w hmp hvc h
  unfold findRoot
  simp only [writerWP_bind, writerWP_get]
  exact writerWP_mono (tk_pathAdd none _ c w hmp hvc h) (fun _ v hv => (writerWP_pure _ _ _ _).mpr hv)

theorem tk_parentAt (d : Nat) : TallKeeps base T (parentAt d) := by
  intro c w hmp hvc h
  cases d with
  | zero => simpa only [parentAt, writerWP_pure] using h
  | succ d =>
    unfold parentAt
    simp only [writerWP_bind]
    exact writerWP_mono (tk_pathNode d c w hmp hvc h) (fun _ v hv => (writerWP_pure _ _ _ _).mpr hv)

theorem tk_fresh : TallKeeps base T fresh := by
  intro c w _ _ h
  unfold fresh
  simp only [writerWP_bind, writerWP_get, writerWP_set, writerWP_pure]
  exact h.same rfl rfl (Nat.le_add_right _ _)

theorem tk_setMadeFor (x : NodeId) (o : Option NodeId) : TallKeeps base T (setMadeFor x o) := by
  intro c w _ _ h
  unfold setMadeFor
  split
  · simp only [writerWP_modify]; exact h.same rfl rfl (Nat.le_refl _)
  · exact (writerWP_pure _ _ _ _).mpr h

/-- A node appended to the overlay under an id that is not tall. -/
theorem TallOK.append_other {c : Ctx} {w v : W} (h : TallOK base T c w) (x : NodeId) (hx : ¬ T x)
    (n : KNode) (hv : v.nodes = w.nodes ++ [(x, n)]) (ht : v.taken = w.taken) (hn : w.next ≤ v.next) :
    TallOK base T c v := by
  refine h.frame hn (fun y hT hy => ⟨by rw [ht]; exact hy, ?_⟩)
  have hyx : y ≠ x := fun e => hx (e ▸ hT)
  unfold wNode
  rw [ht, hy, hv, List.lookup_append]
  cases hl : w.nodes.lookup y with
  | some m => rfl
  | none =>
    have : (y == x) = false := by simpa using hyx
    simp [List.lookup, this]

/-- A new key node is not tall. -/
theorem tk_newKey (g hh : Nat) (leaf : Bool) (ks : List Klong) (c : Ctx) (w : W)
    (h : TallOK base T c w) :
    WriterWP (newKey g hh leaf ks) c w (fun x v => TallOK base T c v ∧ ¬ T x ∧ x = w.next) := by
  unfold newKey fresh
  simp only [writerWP_bind, writerWP_read, writerWP_get, writerWP_set, writerWP_pure]
  have hx : ¬ T w.next := fun hT => by have := (h w.next hT).1; omega
  split <;> simp only [writerWP_modify, writerWP_bind, writerWP_pure] <;>
    exact ⟨h.append_other _ hx _ rfl rfl (by simp only; omega), hx, trivial⟩

theorem tk_newValue (hh : Nat) : TallKeeps base T (newValue hh) := by
  intro c w _ _ h
  unfold newValue fresh
  simp only [writerWP_bind, writerWP_get, writerWP_set, writerWP_pure, writerWP_modify]
  exact h.same rfl rfl (Nat.le_add_right _ _)

theorem tk_newSuperRoot (y : NodeId) : TallKeeps base T (newSuperRoot y) := by
  intro c w _ _ h
  unfold newSuperRoot fresh note
  simp only [writerWP_bind, writerWP_read, writerWP_get]
  split <;> simp only [writerWP_bind, writerWP_get, writerWP_set, writerWP_pure, writerWP_modify] <;>
    exact h.same rfl rfl (by simp only; omega)

/-- `putNode` of a node that is not tall. -/
theorem tk_putNode_other (x : NodeId) (n : KNode) (c : Ctx) (w : W) (h : TallOK base T c w)
    (hx : ¬ T x) : WriterWP (putNode x n) c w (fun _ v => TallOK base T c v) := by
  unfold putNode
  simp only [writerWP_modify]
  exact h.put_other x hx n rfl rfl (Nat.le_refl _)

/-- `putNode` of a node changed so that, if it is tall, it keeps its leaf flag and
first time, and has no fewer live klongs. -/
theorem tk_putNode_change (x : NodeId) (n n' : KNode) (c : Ctx) (w : W) (h : TallOK base T c w)
    (hn : w.taken.contains x = false → wNode c.p base w x = some n)
    (hgood : T x → n.firstTime = some c.i → n'.leaf = n.leaf ∧ n'.firstTime = n.firstTime ∧ n.cnt ≤ n'.cnt) :
    WriterWP (putNode x n') c w (fun _ v => TallOK base T c v) := by
  unfold putNode
  simp only [writerWP_modify]
  refine h.put_good x n' (fun hT => ?_) rfl rfl (Nat.le_refl _)
  obtain ⟨_, ht, m, hm, hml, hmf, hmc⟩ := h x hT
  rw [hn ht] at hm
  cases hm
  obtain ⟨hl, hf, hc⟩ := hgood hT hmf
  exact ⟨by rw [hl]; exact hml, by rw [hf]; exact hmf, by omega⟩

theorem tk_takenBack (x : NodeId) (c : Ctx) (w : W) (h : TallOK base T c w) (hx : ¬ T x) :
    WriterWP (takenBack x) c w (fun _ v => TallOK base T c v) := by
  unfold takenBack
  simp only [writerWP_modify]
  exact h.take_other x hx rfl rfl (Nat.le_refl _)

/-- `getNode` with what it returns: the node the writer reads at the state after it. -/
theorem tk_getNodeI (x : NodeId) (c : Ctx) (w : W) (hvc : ViewCoherent c base)
    (h : TallOK base T c w) :
    WriterWP (getNode x) c w (fun n v => TallOK base T c v ∧
      (v.taken.contains x = false → wNode c.p base v x = some n) ∧ v.taken = w.taken ∧
      v.next = w.next ∧ v.nodes.lookup x = some n ∧ wNode c.p base v = wNode c.p base w) := by
  refine writerWP_mono (writerWP_getNode_all x c w base hvc) ?_
  rintro n v ⟨hr, hl, hw, -, -⟩
  refine ⟨h.of_reads hr, fun ht => ?_, hr.2.2.1, hr.2.2.2.2, hl, hr.1⟩
  rw [hr.1]; exact hw (by rw [← hr.2.2.1]; exact ht)

end Keeps

/-! ## Live counts of changed nodes -/

/-- A node whose live compare values are among another's has no more live klongs. -/
theorem KNode.cnt_le_of_keys (a b : KNode)
    (h : ∀ c y i, (Klong.key c y, i) ∈ a.ks.zipIdx → i ∉ a.lastBitmap →
      ∃ y' i', (Klong.key c y', i') ∈ b.ks.zipIdx ∧ i' ∉ b.lastBitmap) : a.cnt ≤ b.cnt := by
  have := KNode.cnt_ge_protected_keys b (a.live.map Prod.fst) a.live_keys_nodup (fun c hc => by
    obtain ⟨y, i, hm, hi⟩ := (a.live_has_key c).mp hc
    exact h c y i hm hi)
  simpa [KNode.cnt] using this

theorem KNode.cnt_le_add_key (n : KNode) (t : Time) (cv : Nat) (y : NodeId) :
    n.cnt ≤ (n.add t (.key cv y)).cnt := by
  apply KNode.cnt_le_of_keys
  intro c z i hm hi
  refine ⟨z, i, ?_, by rw [KNode.add_key_lastBitmap]; exact hi⟩
  unfold KNode.add
  have hz : ∀ l : List Klong, (Klong.key c z, i) ∈ (n.ks ++ l).zipIdx := by
    intro l
    rw [List.zipIdx_append]; exact List.mem_append_left _ hm
  split
  · split
    · exact hz _
    · exact hz _
  · exact hz _

theorem KNode.foldl_add_facts (t : Time) (ins : List (Nat × NodeId)) :
    ∀ (n : KNode), (ins.foldl (fun n (cv, y) => n.add t (.key cv y)) n).leaf = n.leaf ∧
      (∀ s, n.firstTime = some s → (ins.foldl (fun n (cv, y) => n.add t (.key cv y)) n).firstTime = some s) ∧
      n.cnt ≤ (ins.foldl (fun n (cv, y) => n.add t (.key cv y)) n).cnt := by
  induction ins with
  | nil => intro n; exact ⟨rfl, fun _ h => h, Nat.le_refl _⟩
  | cons q rest ih =>
    intro n
    obtain ⟨h1, h2, h3⟩ := ih (n.add t (.key q.1 q.2))
    simp only [List.foldl_cons]
    refine ⟨h1.trans (KNode.add_leaf _ _ _), fun s hs => h2 s (KNode.firstTime_add_some _ _ _ _ hs),
      Nat.le_trans (KNode.cnt_le_add_key n t q.1 q.2) h3⟩

theorem KNode.firstTime_newKlongs (leaf : Bool) (t : Time) (l : List (Nat × NodeId)) :
    (⟨leaf, newKlongs t l⟩ : KNode).firstTime = some t := by
  simp [KNode.firstTime, newKlongs]

theorem KNode.retarget_facts (n : KNode) (ti : Nat) (src dst : NodeId) :
    ({ n with ks := retargetKlongs n.ks ti src dst } : KNode).leaf = n.leaf ∧
    ({ n with ks := retargetKlongs n.ks ti src dst } : KNode).firstTime = n.firstTime ∧
    ({ n with ks := retargetKlongs n.ks ti src dst } : KNode).cnt = n.cnt := by
  have hs := retargetKlongs_shape n.ks ti src dst
  refine ⟨rfl, KNode.firstTime_of_shapeOf (by simp only [KNode.shapeOf, hs]), KNode.cnt_eq_of_shape _ _ hs⟩

theorem KNode.repoint_facts (n : KNode) (i : Nat) (y : NodeId) :
    (n.repoint i y).leaf = n.leaf ∧ (n.repoint i y).firstTime = n.firstTime ∧
    (n.repoint i y).cnt = n.cnt := by
  refine ⟨?_, KNode.firstTime_repoint n i y, KNode.cnt_eq_of_shape _ _ (KNode.repoint_shape n i y)⟩
  unfold KNode.repoint; split <;> rfl

theorem halves_fst_shape (leaf : Bool) (t : Time) (last : KNode) (ins : List (Nat × NodeId)) :
    ∃ l, (halves leaf t last ins).1 = ⟨leaf, .time t :: l⟩ := by
  unfold halves
  simp only [apply_ite Prod.fst]
  repeat' split
  all_goals exact ⟨_, rfl⟩

theorem halves_fst_facts (leaf : Bool) (t : Time) (last : KNode) (ins : List (Nat × NodeId)) :
    (halves leaf t last ins).1.leaf = leaf ∧ (halves leaf t last ins).1.firstTime = some t := by
  obtain ⟨l, hl⟩ := halves_fst_shape leaf t last ins
  rw [hl]
  simp [KNode.firstTime]

section Keeps2

variable {base : View BVal} {T : NodeId → Prop}

theorem tk_retarget (q src dst : NodeId) : TallKeeps base T (retarget q src dst) := by
  intro c w hmp hvc h
  unfold retarget
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (tk_getNodeI q c w hvc h) ?_
  rintro n v ⟨hv, hn, -, -, -, -⟩
  split
  · have hf := KNode.retarget_facts n (n.lastTimeIndex.getD 0) src dst
    exact tk_putNode_change q n _ c v hv hn (fun _ _ => ⟨hf.1, hf.2.1, Nat.le_of_eq hf.2.2.symm⟩)
  · exact (writerWP_pure _ _ _ _).mpr hv

theorem tk_addKeys (x : NodeId) (ins : List (Nat × NodeId)) : TallKeeps base T (addKeys x ins) := by
  intro c w hmp hvc h
  unfold addKeys
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (tk_getNodeI x c w hvc h) ?_
  rintro n v ⟨hv, hn, -, -, -, -⟩
  obtain ⟨h1, h2, h3⟩ := KNode.foldl_add_facts c.i ins n
  exact tk_putNode_change x n _ c v hv hn (fun _ hf => ⟨h1, by rw [h2 _ hf, hf], h3⟩)

/-- `putNode` of a node that is good if tall. -/
theorem tk_putNode_good (x : NodeId) (n' : KNode) (c : Ctx) (w : W) (h : TallOK base T c w)
    (hgood : T x → n'.leaf = false ∧ n'.firstTime = some c.i ∧ 2 ≤ n'.cnt) :
    WriterWP (putNode x n') c w (fun _ v => TallOK base T c v) := by
  unfold putNode
  simp only [writerWP_modify]
  exact h.put_good x n' hgood rfl rfl (Nat.le_refl _)

end Keeps2

macro "tkUse " h:term : tactic => `(tactic| (
  (refine writerWP_mono ($h _ _ (by assumption) (by assumption) (by assumption)) ?tkPost)
  intro _ _ _))

macro "tkNew" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (newKey _ _ _ _) _ _ _)
  (refine writerWP_mono (tk_newKey _ _ _ _ _ _ (by assumption)) ?tkPost)
  rintro _ _ ⟨_, _, _⟩))

macro "tkGet" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (getNode _) _ _ _)
  (refine writerWP_mono (tk_getNodeI _ _ _ (by assumption) (by assumption)) ?tkPost)
  rintro _ _ ⟨_, _, _, _, _, _⟩))

macro "tkCore" : tactic => `(tactic| first
  | exact writerWP_throw _ _ _ _
  | ((with_unfolding_none guard_target = WriterWP (klongAt _) _ _ _)
     refine writerWP_mono (kd_klongAt _ _ _) ?_; rintro _ _ ⟨heq, _⟩; subst heq)
  | ((with_unfolding_none guard_target = WriterWP (pathNode _) _ _ _)
     refine writerWP_mono (kd_pathNode _ _ _) ?_; rintro _ _ ⟨heq, _⟩; subst heq)
  | ((with_unfolding_none guard_target = WriterWP pathSize _ _ _)
     refine writerWP_mono (kd_pathSize _ _) ?_; rintro _ _ ⟨heq, _⟩; subst heq)
  | ((with_unfolding_none guard_target = WriterWP (replacedBy _) _ _ _)
     refine writerWP_mono (kd_replacedBy _ _ _) ?_; rintro _ _ ⟨heq, _⟩; subst heq)
  | tkNew
  | tkGet
  | tkUse (tk_ghOf _)
  | tkUse (tk_parentAt _)
  | tkUse (tk_note _)
  | tkUse (tk_pathNode _)
  | tkUse (tk_klongAt _)
  | tkUse tk_pathSize
  | tkUse (tk_replacedBy _)
  | tkUse (tk_setMadeFor _ _)
  | tkUse tk_fresh
  | tkUse (tk_newSuperRoot _)
  | tkUse (tk_retarget _ _ _)
  | tkUse (tk_addKeys _ _)
  | tkUse tk_findRoot
  | tkUse (tk_pathAdd _ _))

/-! ## The splits -/

theorem KNode.cnt_le_of_lookup (a b : KNode) (h : ∀ q, (a.live.lookup q).isSome = true → (b.live.lookup q).isSome = true) :
    a.cnt ≤ b.cnt := by
  have hs : ∀ q ∈ a.live.map Prod.fst, q ∈ b.live.map Prod.fst := by
    intro q hq
    have h1 : (a.live.lookup q).isSome = true := by
      obtain ⟨⟨q', y⟩, hm, rfl⟩ := List.mem_map.mp hq
      exact Option.isSome_iff_exists.mpr ⟨y, (mem_iff_lookup _ (KNode.live_keys_nodup a) q' y).mp hm⟩
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (h q h1)
    exact List.mem_map.mpr ⟨(q, y), (mem_iff_lookup _ (KNode.live_keys_nodup b) q y).mpr hy, rfl⟩
  have := a.live_keys_nodup.length_le_of_subset hs
  simpa [KNode.cnt] using this

section Split

variable {base : View BVal} {T : NodeId → Prop}

theorem tk_replaceOrAdd (last : KNode) (ins : List (Nat × NodeId)) (c : Ctx) (w : W) :
    WriterWP (replaceOrAdd last ins) c w (fun _ v => v = w) := by
  unfold replaceOrAdd
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_foldlM_state ins _ last c w (fun _ v => v = w) rfl ?_
  intro a b v hv
  split
  · exact writerWP_throw _ _ _ _
  · exact (writerWP_pure _ _ _ _).mpr hv
  · exact (writerWP_pure _ _ _ _).mpr hv

set_option maxHeartbeats 3200000 in
/-- A full node's replacement keeps the frame; a tall node is split in place, from its
last version. -/
theorem tk_handleFullWith (up : NodeId → List (Nat × NodeId) → M Unit) (depth : Nat) (x : NodeId)
    (ins : List (Nat × NodeId)) (last : KNode) (compact : Bool)
    (hup : ∀ q more, TallKeeps base T (up q more)) (c : Ctx) (w : W) (hmp : MergeParamsOK c.p)
    (hvc : ViewCoherent c base) (h : TallOK base T c w)
    (hx : T x → ∃ n0, wNode c.p base w x = some n0 ∧ last = n0.lastVersion c.i) :
    WriterWP (handleFullWith up depth x ins last compact) c w (fun _ v => TallOK base T c v) := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (tk_getNodeI x c w hvc h) ?_
  rintro n v1 ⟨h1, hn1, ht1, hnx1, hl1, hw1⟩
  have hT : T x → n.leaf = false ∧ n.firstTime = some c.i ∧ 2 ≤ n.cnt ∧ last = n.lastVersion c.i := by
    intro hTx
    obtain ⟨n0, hn0, hlast⟩ := hx hTx
    obtain ⟨_, htk, m, hm, hml, hmf, hmc⟩ := h x hTx
    have e1 : wNode c.p base v1 x = some n := hn1 (by rw [ht1]; exact htk)
    rw [hw1, hn0] at e1
    cases e1
    rw [hn0] at hm
    cases hm
    exact ⟨hml, hmf, hmc, hlast⟩
  have hgoodF : T x → c.p.splitAbove < (n.lastVersion c.i).size →
      ((halves n.leaf c.i (n.lastVersion c.i) ins).1.leaf = false ∧
       (halves n.leaf c.i (n.lastVersion c.i) ins).1.firstTime = some c.i ∧
       2 ≤ (halves n.leaf c.i (n.lastVersion c.i) ins).1.cnt) := by
    intro hTx hsz
    obtain ⟨hl, -, -, -⟩ := hT hTx
    have hf2 := halves_fst_facts n.leaf c.i (n.lastVersion c.i) ins
    refine ⟨by rw [hf2.1, hl], hf2.2, ?_⟩
    have hsz' : c.p.splitAbove < (⟨n.leaf, newKlongs c.i n.live⟩ : KNode).size := by
      rw [← KNode.lastVersion_eq_newKlongs]; exact hsz
    have := halves_first_protected_fill c.p hmp n.leaf c.i n.live ins n.live_order hsz'
    rw [KNode.lastVersion_eq_newKlongs]
    have := hmp.1
    omega
  by_cases hTx : T x
  · obtain ⟨hnl, hnf, hnc, hlast⟩ := hT hTx
    subst hlast
    have hgF := hgoodF hTx
    have hnew : (n.firstTime == some c.i) = true := by rw [hnf]; simp
    have hl2 : ∀ (l : KNode) (more : List (Nat × NodeId)), l.ks = newKlongs c.i more →
        (∀ q, l.live.lookup q = ins.foldl (pairLookupStep q) (n.live.lookup q)) →
        ({ l with leaf := n.leaf } : KNode).leaf = false ∧
        ({ l with leaf := n.leaf } : KNode).firstTime = some c.i ∧ 2 ≤ ({ l with leaf := n.leaf } : KNode).cnt := by
      intro l more hks hlk
      refine ⟨hnl, ?_, ?_⟩
      · show (⟨n.leaf, l.ks⟩ : KNode).firstTime = some c.i
        rw [hks]; exact KNode.firstTime_newKlongs _ _ _
      · have e : ({ l with leaf := n.leaf } : KNode).cnt = l.cnt := KNode.cnt_eq_of_shape _ _ rfl
        rw [e]
        refine Nat.le_trans hnc (KNode.cnt_le_of_lookup n l (fun q hq => ?_))
        rw [hlk q]
        obtain ⟨z, hz⟩ := pairLookupFold_isSome q ins _ hq
        rw [hz]; rfl
    repeat' first
      | assumption
      | wpSimplify
      | exact absurd hnew (by assumption)
      | exact absurd (‹(!(n.firstTime == some c.i)) = true›) (by rw [hnew]; decide)
      | tkCore
      | tkUse (hup _ _)
      | (with_unfolding_none guard_target = WriterWP (putNode x (halves _ _ _ _).1) _ _ _
         refine writerWP_mono (tk_putNode_good _ _ c _ (by assumption)
           (fun _ => hgF (by simp_all))) ?_
         intro _ _ _)
      | (with_unfolding_none guard_target = WriterWP (putNode _ (KNode.repoint _ _ _)) _ _ _
         refine writerWP_mono (tk_putNode_change _ _ _ c _ (by assumption) (by assumption)
           (fun _ _ => ⟨(KNode.repoint_facts _ _ _).1, (KNode.repoint_facts _ _ _).2.1,
             Nat.le_of_eq (KNode.repoint_facts _ _ _).2.2.symm⟩)) ?_
         intro _ _ _)
      | (with_unfolding_none guard_target = WriterWP (putNode _ _) _ _ _
         refine writerWP_mono (tk_putNode_other _ _ c _ (by assumption) (by assumption)) ?_
         intro _ _ _)
      | (with_unfolding_none guard_target = WriterWP (replaceOrAdd _ _) _ _ _
         refine writerWP_mono (writerWP_replaceOrAdd_lastN n ins c _) ?_
         rintro l _ ⟨rfl, -, -, -, hlk, more, hks, -⟩
         have hl3 := hl2 l more hks hlk
         repeat' first
           | wpSimplify
           | tkUse (tk_note _)
           | wpSplit
         all_goals exact tk_putNode_good _ _ c _ (by assumption) (fun _ => hl3))
      | wpSplit
      | split
  · repeat' first
      | assumption
      | wpSimplify
      | tkCore
      | tkUse (hup _ _)
      | (with_unfolding_none guard_target = WriterWP (putNode _ (KNode.repoint _ _ _)) _ _ _
         refine writerWP_mono (tk_putNode_change _ _ _ c _ (by assumption) (by assumption)
           (fun _ _ => ⟨(KNode.repoint_facts _ _ _).1, (KNode.repoint_facts _ _ _).2.1,
             Nat.le_of_eq (KNode.repoint_facts _ _ _).2.2.symm⟩)) ?_
         intro _ _ _)
      | (with_unfolding_none guard_target = WriterWP (putNode _ _) _ _ _
         refine writerWP_mono (tk_putNode_other _ _ c _ (by assumption) (by assumption)) ?_
         intro _ _ _)
      | (with_unfolding_none guard_target = WriterWP (replaceOrAdd _ _) _ _ _
         refine writerWP_mono (tk_replaceOrAdd _ _ c _) ?_
         rintro _ _ rfl)
      | wpSplit
      | split

theorem tk_appendKlongs (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)) :
    TallKeeps base T (appendKlongs depth x ins) := by
  induction depth generalizing x ins with
  | zero =>
    intro c w hmp hvc h
    rw [appendKlongs_step_dead]
    simp only [writerWP_bind, writerWP_read]
    refine writerWP_mono (tk_getNodeI x c w hvc h) ?_
    rintro n v ⟨hv, hn, -, -, -, -⟩
    have hx : T x → ∃ n0, wNode c.p base v x = some n0 ∧ n.lastVersion c.i = n0.lastVersion c.i :=
      fun hT => ⟨n, hn (hv x hT).2.1, rfl⟩
    split
    · exact tk_handleFullWith _ _ _ _ _ _ (fun _ _ c w _ _ _ => writerWP_throw _ _ _ _) c v hmp hvc hv hx
    · split
      · exact tk_handleFullWith _ _ _ _ _ _ (fun _ _ c w _ _ _ => writerWP_throw _ _ _ _) c v hmp hvc hv hx
      · exact tk_addKeys x ins c v hmp hvc hv
  | succ d ih =>
    intro c w hmp hvc h
    rw [appendKlongs_step_dead]
    simp only [writerWP_bind, writerWP_read]
    refine writerWP_mono (tk_getNodeI x c w hvc h) ?_
    rintro n v ⟨hv, hn, -, -, -, -⟩
    have hx : T x → ∃ n0, wNode c.p base v x = some n0 ∧ n.lastVersion c.i = n0.lastVersion c.i :=
      fun hT => ⟨n, hn (hv x hT).2.1, rfl⟩
    split
    · exact tk_handleFullWith _ _ _ _ _ _ (fun q more => ih q more) c v hmp hvc hv hx
    · split
      · exact tk_handleFullWith _ _ _ _ _ _ (fun q more => ih q more) c v hmp hvc hv hx
      · exact tk_addKeys x ins c v hmp hvc hv

theorem tk_handleFull (depth : Nat) (x : NodeId) (last : KNode) (compact : Bool) (c : Ctx) (w : W)
    (hmp : MergeParamsOK c.p) (hvc : ViewCoherent c base) (h : TallOK base T c w) (hx : ¬ T x) :
    WriterWP (handleFull depth x last compact) c w (fun _ v => TallOK base T c v) := by
  unfold handleFull
  cases depth with
  | zero =>
    exact tk_handleFullWith _ _ _ _ _ _ (fun _ _ c w _ _ _ => writerWP_throw _ _ _ _) c w hmp hvc h
      (fun hT => absurd hT hx)
  | succ d =>
    exact tk_handleFullWith _ _ _ _ _ _ (fun q more => tk_appendKlongs d q more) c w hmp hvc h
      (fun hT => absurd hT hx)

theorem tk_unlink (x : NodeId) (c : Ctx) (w : W) (hvc : ViewCoherent c base) (h : TallOK base T c w)
    (hx : ¬ T x) : WriterWP (unlink x) c w (fun _ v => TallOK base T c v) := by
  unfold unlink
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (tk_getNodeI x c w hvc h) ?_
  rintro n v ⟨hv, -, -, -, -, -⟩
  split
  · exact tk_putNode_other x _ c v hv hx
  · exact (writerWP_pure _ _ _ _).mpr hv

/-- A read-only check. -/
theorem tk_check (f : M Unit) (hf : ∀ c w, WriterWP f c w (fun _ v => v = w)) :
    TallKeeps base T f := fun c w _ _ h => writerWP_mono (hf c w) (fun _ v hv => by rw [hv]; exact h)

theorem tk_checkFree (o : NodeId) : TallKeeps base T (checkFree o) :=
  tk_check _ (fun c w => writerWP_mono (writerWP_checkFree o c w) (fun _ _ hv => hv.1))

theorem tk_checkOld (pn : KNode) (old : NodeId) : TallKeeps base T (checkOld pn old) := by
  refine tk_check _ (fun c w => ?_)
  unfold checkOld
  simp only [writerWP_bind, writerWP_read]
  split
  · exact (writerWP_pure _ _ _ _).mpr rfl
  · exact writerWP_throw _ _ _ _

theorem tk_checkRoot (x : NodeId) (d : Nat) : TallKeeps base T (checkRoot x d) := by
  refine tk_check _ (fun c w => ?_)
  unfold checkRoot
  simp only [writerWP_bind, writerWP_read, writerWP_get]
  split
  · exact (writerWP_pure _ _ _ _).mpr rfl
  · exact writerWP_throw _ _ _ _

end Split

macro "tkMore" : tactic => `(tactic| first
  | tkCore
  | tkUse (tk_appendKlongs _ _ _)
  | tkUse (tk_checkFree _)
  | tkUse (tk_checkOld _ _)
  | tkUse (tk_checkRoot _ _)
  | (with_unfolding_none guard_target = WriterWP (handleFull _ _ _ _) _ _ _
     refine writerWP_mono (tk_handleFull _ _ _ _ _ _ (by assumption) (by assumption) (by assumption)
       (by assumption)) ?_
     intro _ _ _)
  | (with_unfolding_none guard_target = WriterWP (unlink _) _ _ _
     refine writerWP_mono (tk_unlink _ _ _ (by assumption) (by assumption) (by assumption)) ?_
     intro _ _ _)
  | (with_unfolding_none guard_target = WriterWP (takenBack _) _ _ _
     refine writerWP_mono (tk_takenBack _ _ _ (by assumption) (by assumption)) ?_
     intro _ _ _)
  | (with_unfolding_none guard_target = WriterWP (putNode _ (KNode.repoint _ _ _)) _ _ _
     refine writerWP_mono (tk_putNode_change _ _ _ _ _ (by assumption) (by assumption)
       (fun _ _ => ⟨(KNode.repoint_facts _ _ _).1, (KNode.repoint_facts _ _ _).2.1,
         Nat.le_of_eq (KNode.repoint_facts _ _ _).2.2.symm⟩)) ?_
     intro _ _ _)
  | (with_unfolding_none guard_target = WriterWP (putNode _ _) _ _ _
     refine writerWP_mono (tk_putNode_other _ _ _ _ (by assumption) (by assumption)) ?_
     intro _ _ _))

section Ops

variable {base : View BVal} {T : NodeId → Prop}

set_option maxHeartbeats 1600000 in
theorem tk_appendDeleteKlong (x : NodeId) (depth cv : Nat) (c : Ctx) (w : W) (hmp : MergeParamsOK c.p)
    (hvc : ViewCoherent c base) (h : TallOK base T c w) (hx : ¬ T x) :
    WriterWP (appendDeleteKlong x depth cv) c w (fun _ v => TallOK base T c v) := by
  unfold appendDeleteKlong
  repeat' first
    | assumption
    | wpSimplify
    | tkMore
    | wpSplit
    | split

set_option maxHeartbeats 1600000 in
theorem tk_mergeParent (q : NodeId) (depth il cL : Nat) (m1 : NodeId) (ir cR : Nat)
    (m2 : Option (NodeId × Nat)) (c : Ctx) (w : W) (hmp : MergeParamsOK c.p)
    (hvc : ViewCoherent c base) (h : TallOK base T c w) (hq : ¬ T q) :
    WriterWP (mergeParent q depth il cL m1 ir cR m2) c w (fun _ v => TallOK base T c v) := by
  unfold mergeParent
  repeat' first
    | assumption
    | wpSimplify
    | tkMore
    | wpSplit
    | split

set_option maxHeartbeats 1600000 in
theorem tk_takeBackChk (x parent : NodeId) (cv : Nat) (c : Ctx) (w : W) (hmp : MergeParamsOK c.p)
    (hvc : ViewCoherent c base) (h : TallOK base T c w) (hx : ¬ T x) :
    WriterWP (takeBackChk x parent cv) c w (fun _ v => TallOK base T c v) := by
  unfold takeBackChk
  repeat' first
    | assumption
    | wpSimplify
    | tkMore
    | wpSplit
    | split

set_option maxHeartbeats 1600000 in
theorem tk_takeBackRoot (x : NodeId) (depth only : Nat) (c : Ctx) (w : W) (hmp : MergeParamsOK c.p)
    (hvc : ViewCoherent c base) (h : TallOK base T c w) (hx : ¬ T x) :
    WriterWP (takeBackRoot x depth only) c w (fun _ v => TallOK base T c v) := by
  unfold takeBackRoot
  repeat' first
    | assumption
    | wpSimplify
    | tkMore
    | wpSplit
    | split

set_option maxHeartbeats 6400000 in
theorem tk_replaceRoot (x : NodeId) (depth only : Nat) (c : Ctx) (w : W) (hmp : MergeParamsOK c.p)
    (hvc : ViewCoherent c base) (h : TallOK base T c w) (hx : ¬ T x) :
    WriterWP (replaceRoot x depth only) c w (fun _ v => TallOK base T c v) := by
  unfold replaceRoot
  repeat' first
    | assumption
    | wpSimplify
    | tkMore
    | wpSplit
    | split

end Ops

end SIS.Tree
