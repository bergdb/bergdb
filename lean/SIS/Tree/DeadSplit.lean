/-
The dead klongs' bound through a full node's split and the cascade above it
(bergdb 024-12, section 1, `d4`'s plan of 2026-11-15; `DW`, DeadLocal.lean): a
half of a last version holds at most the klongs it is given more, at most two;
a new root and a time split's copy none; the parent's repoint and the version
before the transaction no more than the node the writer read.
-/
import SIS.Tree.DeadLocal

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

set_option maxHeartbeats 40000000 in
/-- A full node's split and its cascade keep `DW`, for a last version (`NormKs`)
and at most two klongs to insert, given that the cascade above (`up`) does. -/
theorem dw_handleFullWith (base : View BVal) (up : NodeId → List (Nat × NodeId) → M Unit)
    (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)) (last : KNode) (compact : Bool)
    (c : Ctx) (hlast : NormKs c.i last.ks) (hins : ins.length ≤ 2)
    (hup : ∀ q more, more.length ≤ 2 → KeepsDW base (up q more)) :
    ∀ w, ViewCoherent c base → (2 ≤ c.p.theta ∨ c.p.theta = 0) → DW c base w →
      WriterWP (handleFullWith up depth x ins last compact) c w (fun _ v => DW c base v) := by
  intro w hvc hth hw
  obtain ⟨pairs, hks, hs⟩ := id hlast
  have hnd : (pairs.map Prod.fst).Nodup := List.pairwise_map.mpr (hs.imp (by intro a b h; omega))
  have hup' : ∀ q more, more.length ≤ 2 → ∀ v, DW c base v →
      WriterWP (up q more) c v (fun _ v' => DW c base v') :=
    fun q more hm v hv => hup q more hm c v hvc hth hv
  have hrep : ∀ v, WriterWP (replaceOrAdd last ins) c v (fun out v' =>
      (∃ more, out.ks = newKlongs c.i more ∧ (more.map Prod.fst).Nodup) ∧ v' = v) := by
    intro v
    have he : last = ⟨last.leaf, newKlongs c.i pairs⟩ := by rw [← hks]
    rw [he]
    exact writerWP_mono (writerWP_replaceOrAdd_map last.leaf pairs ins hnd c v)
      (fun _ _ h => ⟨h.2.1, h.2.2.2⟩)
  unfold handleFullWith
  repeat' (first
    | dwStep
    | (with_unfolding_none refine writerWP_mono (hrep _) ?_
       rintro _ _ ⟨_, rfl⟩)
    | (with_unfolding_none refine writerWP_mono (hup' _ _ (by simp) _ (by assumption)) ?_
       intro _ _ _)
    | split)

/-- `addKeys` after its node was read: the klongs go in only when `deadOver` lets
them through. -/
theorem dw_addKeys (base : View BVal) (x : NodeId) (ins : List (Nat × NodeId)) (n : KNode) (c : Ctx)
    (w : W) (hw : DW c base w) (hlk : w.nodes.lookup x = some n)
    (hn : DOK c.p n ∨ w.taken.contains x = true)
    (hd : deadOver c.p (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) n) = false) :
    WriterWP (addKeys x ins) c w (fun _ v => DW c base v) := by
  unfold addKeys
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c w hlk]
  refine writerWP_mono (dw_putNode base x _ c w hw ?_) (fun _ _ h => h.1)
  refine hn.imp_left (fun h => ⟨fun h0 => deadOver_false c.p _ hd h0, ?_⟩)
  exact klongsWf_fold_add n c.i ins h.2

/-- The cascade keeps `DW`: at most two klongs go into a node with room and at
most theta dead klongs with them, else into its split. -/
theorem dw_appendKlongs (base : View BVal) :
    ∀ (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)), ins.length ≤ 2 →
      KeepsDW base (appendKlongs depth x ins) := by
  intro depth
  induction depth with
  | zero =>
    intro x ins hins c w hvc hth hw
    rw [appendKlongs_step_dead]
    simp only [writerWP_bind, writerWP_read]
    refine writerWP_mono (dw_getNode base x c w hvc hw) ?_
    rintro n v ⟨hv, hn, hlk, _⟩
    try simp only []
    refine writerWP_if _ _ _ _ _ _ (fun _ => ?_) (fun _ => ?_)
    · exact dw_handleFullWith base _ 0 x ins _ false c (normKs_lastVersion n c.i) hins
        (fun _ _ _ _ _ _ _ _ => writerWP_throw _ _ _ _) v hvc hth hv
    · refine writerWP_if _ _ _ _ _ _ (fun _ => ?_) (fun hd => ?_)
      · exact dw_handleFullWith base _ 0 x ins _ true c (normKs_lastVersion n c.i) hins
          (fun _ _ _ _ _ _ _ _ => writerWP_throw _ _ _ _) v hvc hth hv
      · exact dw_addKeys base x ins n c v hv hlk hn (by simpa using hd)
  | succ d ih =>
    intro x ins hins c w hvc hth hw
    rw [appendKlongs_step_dead]
    simp only [writerWP_bind, writerWP_read]
    refine writerWP_mono (dw_getNode base x c w hvc hw) ?_
    rintro n v ⟨hv, hn, hlk, _⟩
    try simp only []
    refine writerWP_if _ _ _ _ _ _ (fun _ => ?_) (fun _ => ?_)
    · exact dw_handleFullWith base _ (d + 1) x ins _ false c (normKs_lastVersion n c.i) hins
        (fun q more hm => ih q more hm) v hvc hth hv
    · refine writerWP_if _ _ _ _ _ _ (fun _ => ?_) (fun hd => ?_)
      · exact dw_handleFullWith base _ (d + 1) x ins _ true c (normKs_lastVersion n c.i) hins
          (fun q more hm => ih q more hm) v hvc hth hv
      · exact dw_addKeys base x ins n c v hv hlk hn (by simpa using hd)

/-- A delete's or a merge's full node: its split from a last version, with no
klong to insert. -/
theorem dw_handleFull (base : View BVal) (depth : Nat) (x : NodeId) (last : KNode) (compact : Bool)
    (c : Ctx) (hlast : NormKs c.i last.ks) :
    ∀ w, ViewCoherent c base → (2 ≤ c.p.theta ∨ c.p.theta = 0) → DW c base w →
      WriterWP (handleFull depth x last compact) c w (fun _ v => DW c base v) := by
  unfold handleFull
  refine dw_handleFullWith base _ depth x [] last compact c hlast (by simp) ?_
  intro q more hm
  cases depth with
  | zero => exact fun _ _ _ _ _ => writerWP_throw _ _ _ _
  | succ d => exact dw_appendKlongs base d q more hm

end SIS.Tree
