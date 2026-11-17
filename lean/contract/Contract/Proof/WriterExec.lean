/-
The contract package (bergdb 030-10): the model's own entry point
(`SIS.Tree.runOpsFrom`, lean/SIS/Tree/Exec.lean; `runOps` and `exec?` call it)
and the proved puts. `runOpsFrom` reads the super root (`topOf`), runs the
operations one by one (`List.mapM putKv`) from the state with the first id and
the super root, and refuses a state with a key node made outside G and H that
the transaction did not take back (`boundsOK`). A put takes nothing back, so
for a transaction of puts that `runOpsFrom` accepts no node was made outside
G and H, after any of its operations: the run is an `OpsRun`
(`opsRun_of_runOps`), and the writer's contract follows
(`writerMeets_exec_put`, by `writerMeets_put`).
-/
import Contract.Proof.WriterPutAll

namespace Contract

open SIS (View)
open SIS.Check (BVal)

/-! ## 1. A put is a `WStep` -/

theorem wexec_so_get {c : SIS.Tree.Ctx} : StepOk c (MonadState.get : SIS.Tree.M MW) := by
  intro w
  rw [wp_get]
  exact WStep.refl w

/-- `putKv` of a put keeps or raises the next id, keeps the nodes taken back,
and only adds to the nodes made and to `outside`. -/
theorem wexec_so_putKv (c : SIS.Tree.Ctx) (key : Key) (h : Nat) :
    StepOk c (SIS.Tree.putKv (.put key h)) := by
  unfold SIS.Tree.putKv SIS.Tree.pathClear SIS.Tree.findRoot
  refine so_bind (so_modify (fun _ => ⟨Nat.le_refl _, rfl, id, List.prefix_refl _⟩))
    (fun _ => so_bind (so_bind wexec_so_get (fun w => so_bind (so_pathAdd _ _)
      (fun _ => so_pure _))) (fun r => ?_))
  exact so_putSegs c key h key r

/-! ## 2. `List.mapM putKv` is an `OpsRun` -/

/-- The operations run one by one: every result of `ops.mapM putKv` from w is
a `WStep` from w, and, if no node is outside G and H at its end, an `OpsRun`
from w. -/
theorem wexec_mapM (c : SIS.Tree.Ctx) :
    ∀ (ops : List MOp) (w : MW),
      (∀ op ∈ ops, ∃ key h, op = SIS.Tree.Op.put key h ∧ keyWf key = true) →
      WP (ops.mapM SIS.Tree.putKv) c w
        (fun _ w' => WStep w w' ∧ (w'.outside = [] → OpsRun c w ops w'))
  | [], w, _ => by
    rw [List.mapM_nil, wp_pure]
    exact ⟨WStep.refl w, fun _ => OpsRun.nil w⟩
  | op :: ops, w, hops => by
    obtain ⟨key, h, rfl, hk⟩ := hops _ List.mem_cons_self
    rw [List.mapM_cons, wp_bind]
    intro b w1 h1
    have hs1 : WStep w w1 := wexec_so_putKv c key h w b w1 h1
    rw [wp_bind]
    intro bs w' h2
    rw [wp_pure]
    obtain ⟨hs2, hrun⟩ :=
      wexec_mapM c ops w1 (fun o ho => hops o (List.mem_cons_of_mem _ ho)) bs w' h2
    refine ⟨hs1.trans hs2, fun ho => ?_⟩
    exact OpsRun.cons w w1 w' _ ops b hk h1 (hs2.2.2.1 ho) (hrun ho)

/-! ## 3. The entry point -/

/-- A transaction of puts, of keys as `Keys.toSegments` makes them, that the
model's entry point `runOpsFrom` accepts from the super root z: the writer
reads z, and the run is an `OpsRun` from the state with the first id and that
super root. -/
theorem opsRun_of_runOps {p : MParams} {base : NodeId} {ops : List MOp} {i : Time}
    {z : NodeId} {v : View BVal} {flags : List Bool} {w : MW}
    (hops : ∀ op ∈ ops, ∃ key h, op = SIS.Tree.Op.put key h ∧ keyWf key = true)
    (h : SIS.Tree.runOpsFrom p base ops i (some z) v = .ok (flags, w)) :
    ∃ t, SIS.Tree.topOf p v z = .ok t ∧
      OpsRun { p := p, i := i, view := v } { next := base, top := t } ops w := by
  simp only [SIS.Tree.runOpsFrom] at h
  split at h
  · cases h
  · next t ht =>
    refine ⟨t, ht, ?_⟩
    cases hr : ((ops.mapM SIS.Tree.putKv).run { p := p, i := i, view := v }).run
        { next := base, top := t } with
    | error e =>
      rw [hr] at h
      cases h
    | ok r =>
      obtain ⟨fl, w'⟩ := r
      rw [hr] at h
      simp only [SIS.Tree.boundsOK] at h
      split at h
      · cases h
      · next hf =>
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        obtain ⟨hs, hrun⟩ := wexec_mapM _ ops _ hops fl w' hr
        apply hrun
        have ht0 : w'.taken = [] := hs.2.1
        rw [ht0] at hf
        cases ho : w'.outside with
        | nil => rfl
        | cons q r =>
          rw [ho] at hf
          simp at hf

/-- A transaction of puts, of keys as `Keys.toSegments` makes them, that the
model's entry point `runOpsFrom` accepts, from a tree with its top that meet
`Before` and whose key klongs name its nodes, shown to the writer by its view:
the writer meets the writer's contract, TREE and the top's clauses
(`WriterMeetsPut`'s conclusion). -/
theorem writerMeets_exec_put {p : MParams} (hp : ParamsOK p) {i : Time} {base : NodeId}
    {s : Tree} {tp : Top} {v : View BVal} {z : NodeId} {ops : List MOp} {flags : List Bool}
    {w : MW} (hops : ∀ op ∈ ops, ∃ key h, op = SIS.Tree.Op.put key h ∧ keyWf key = true)
    (hn : SNamed s) (hbf : Before p i base s tp) (hs : Shows p v z s tp)
    (h : SIS.Tree.runOpsFrom p base ops i (some z) v = .ok (flags, w)) :
    Contract (cpOf p) i s (ops.map opOf) (dirtyOf w) (treeOf i s w) ∧
      TreeOk ((treeOf i s w).at i) ∧ TopStep i tp (topOf i tp w) ∧
      (treeOf i s w).roots = rootsOf (topOf i tp w) ∧
      invOk (cpOf p) (treeOf i s w) = true ∧ TreeOk (treeOf i s w) ∧
      BalancedAll p (treeOf i s w) ∧
      (∀ x n, (treeOf i s w).obj x = some (.key n) → ∃ t rest, n.ks = Klong.time t :: rest) ∧
      (∀ x n, (treeOf i s w).obj x = some (.key n) → timesBefore (i + 1) n.ks = true) ∧
      (∀ r ∈ (treeOf i s w).roots, r.1 < i + 1) ∧
      (∀ x, w.next ≤ x → (treeOf i s w).obj x = none ∧ (topOf i tp w).node x = none) ∧
      (∀ z zn, (topOf i tp w).getLast? = some (z, zn) → ∀ q ∈ zn.skips,
        ((topOf i tp w).node q.2.1).map (·.time) = some q.2.2) := by
  obtain ⟨t, ht, hrun⟩ := opsRun_of_runOps hops h
  have hops' : ∀ op ∈ ops, ∃ key h, op = SIS.Tree.Op.put key h := by
    intro op hop
    obtain ⟨key, h, he, -⟩ := hops op hop
    exact ⟨key, h, he⟩
  exact writerMeets_put hp ops hops' i base s tp v z t w hn hbf hs ht hrun

end Contract
