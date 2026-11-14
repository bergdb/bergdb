/-
The upward delete at the writer's level (bergdb 024-12, TP10's `OpGetOK`;
024-22): the climb (`writerWP_climb`), the nodes below the stop node left out,
the stop node's klong deleted.
-/
import SIS.Tree.WriterGetUp
import SIS.Tree.ChildrenExist
import SIS.Tree.WriterTreeDelete

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- A node whose every key klong is deleted by its bitmap with compare value k's
bits: its live klongs are all of compare value k. -/
theorem allKeysIn_live_cv (n : KNode) (k : Nat)
    (h : n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf k)) = true) :
    ∀ c z, (c, z) ∈ n.live → c = k := by
  intro c z hm
  have hlk := lookup_of_mem_nodup _ (KNode.live_keys_nodup n) c z hm
  rw [KNode.live_lookup] at hlk
  obtain ⟨j, hj, hjd⟩ := keyLookup_some_kept n.lastBitmap c z n.ks hlk
  have hz : (Klong.key c z, j) ∈ n.ks.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hj
  by_cases hu : j ∈ bitsUnion n.lastBitmap (n.bitsOf k)
  · rcases (mem_bitsUnion_iff _ _ j).mp hu with h1 | h1
    · exact absurd h1 hjd
    · obtain ⟨y, hy⟩ := (KNode.mem_bitsOf_iff n k j).mp h1
      have h2 := List.mem_zipIdx_iff_getElem?.mp hy
      rw [hj] at h2
      simp only [Option.some.injEq, Klong.key.injEq] at h2
      exact h2.1
  · rw [KNode.allKeysIn_false_of_live_key n _ c z j hz hu] at h
    cases h

/-- The climb from depth t, all of the path's nodes known to the writer: no
change to its state; the stop node at most t; every node strictly between the
stop node and t has only the path's compare value live; every node it passes
that the transaction made can be taken back. -/
theorem writerWP_climb (c : Ctx) (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) :
    ∀ (t : Nat) (w : W), (∀ i, i ≤ t → (w.path[i]?).map (·.2) = some (X i)) →
      (∀ i, 0 < i → i ≤ t → w.path[i]? = some (some (K i), X i)) →
      (∀ i, i ≤ t → w.nodes.lookup (X i) = some (Nn i)) →
      WriterWP (climb t) c w (fun stop w' => w' = w ∧ stop ≤ t ∧
        (∀ i, stop < i → i < t →
          (Nn i).allKeysIn (bitsUnion (Nn i).lastBitmap ((Nn i).bitsOf (K (i + 1)))) = true) ∧
        (∀ j, stop < j → j ≤ t → (Nn j).firstTime = some c.i →
          (w.madeFor.lookup (X j)).isSome = true ∧ ((Nn (j - 1)).linkIndex (X j) (K j)).isSome = true) ∧
        (stop < t → (Nn stop).allKeysIn (bitsUnion (Nn stop).lastBitmap
          ((Nn stop).bitsOf (K (stop + 1)))) = true → stop = 0 ∧ (Nn 0).leaf = true) ∧
        (stop = t → t = 0 ∧ (Nn 0).leaf = true)) := by
  intro t
  induction t with
  | zero =>
    intro w hp _ hlk
    unfold climb
    simp only [writerWP_bind, writerWP_read]
    refine writerWP_pathNode_known 0 (X 0) c w (hp 0 (Nat.le_refl _)) _ ?_
    rw [writerWP_getNode_known _ _ c w (hlk 0 (Nat.le_refl _))]
    split
    · exact writerWP_throw _ _ _ _
    · rename_i hl
      simp only [writerWP_pure]
      refine ⟨by first | rfl | trivial, Nat.le_refl _, fun i h1 h2 => by omega,
        fun j h1 h2 => by omega, fun h => by omega, fun _ => ⟨by first | rfl | trivial, by simpa using hl⟩⟩
  | succ t ih =>
    intro w hp hk hlk
    unfold climb
    simp only [writerWP_bind, writerWP_read]
    refine writerWP_pathNode_known (t + 1) (X (t + 1)) c w (hp (t + 1) (Nat.le_refl _)) _ ?_
    rw [writerWP_getNode_known _ _ c w (hlk (t + 1) (Nat.le_refl _))]
    refine writerWP_pathNode_known t (X t) c w (hp t (by omega)) _ ?_
    refine writerWP_klongAt_known (t + 1) (K (t + 1)) (X (t + 1)) c w (hk (t + 1) (by omega)
      (Nat.le_refl _)) _ ?_
    -- the take-back check
    have hcont : ∀ (b : Bool), ((Nn (t + 1)).firstTime == some c.i && !b) = false →
        (b = ((w.madeFor.lookup (X (t + 1))).isSome &&
          ((Nn t).linkIndex (X (t + 1)) (K (t + 1))).isSome)) →
        WriterWP (do
          let pn ← getNode (X t)
          if pn.allKeysIn (bitsUnion pn.lastBitmap (pn.bitsOf (K (t + 1)))) = true then climb t
          else pure t) c w (fun stop w' => w' = w ∧ stop ≤ t + 1 ∧
            (∀ i, stop < i → i < t + 1 →
              (Nn i).allKeysIn (bitsUnion (Nn i).lastBitmap ((Nn i).bitsOf (K (i + 1)))) = true) ∧
            (∀ j, stop < j → j ≤ t + 1 → (Nn j).firstTime = some c.i →
              (w.madeFor.lookup (X j)).isSome = true ∧
                ((Nn (j - 1)).linkIndex (X j) (K j)).isSome = true) ∧
            (stop < t + 1 → (Nn stop).allKeysIn (bitsUnion (Nn stop).lastBitmap
              ((Nn stop).bitsOf (K (stop + 1)))) = true → stop = 0 ∧ (Nn 0).leaf = true) ∧
            (stop = t + 1 → t + 1 = 0 ∧ (Nn 0).leaf = true)) := by
      intro b hb hbv
      have hmade : (Nn (t + 1)).firstTime = some c.i →
          (w.madeFor.lookup (X (t + 1))).isSome = true ∧
            ((Nn t).linkIndex (X (t + 1)) (K (t + 1))).isSome = true := by
        intro hf
        have : b = true := by
          cases b with
          | true => rfl
          | false => simp [hf] at hb
        rw [hbv] at this
        simpa using this
      rw [writerWP_bind, writerWP_getNode_known _ _ c w (hlk t (by omega))]
      split
      · rename_i hall
        refine writerWP_mono (ih w (fun i hi => hp i (by omega)) (fun i h1 h2 => hk i h1 (by omega))
          (fun i hi => hlk i (by omega))) ?_
        rintro stop w' ⟨hw', hst, hall', hmade', hroot, hself⟩
        refine ⟨hw', by omega, ?_, ?_, ?_, fun h => by omega⟩
        · intro i h1 h2
          rcases Nat.lt_or_ge i t with h | h
          · exact hall' i h1 h
          · have : i = t := by omega
            subst this; exact hall
        · intro j h1 h2 hf
          rcases Nat.lt_or_ge j (t + 1) with h | h
          · exact hmade' j h1 (by omega) hf
          · have : j = t + 1 := by omega
            subst this
            exact hmade hf
        · intro h1 h2
          rcases Nat.lt_or_ge stop t with h | h
          · exact hroot h h2
          · have hst' : stop = t := by omega
            exact ⟨by have := (hself hst').1; omega, (hself hst').2⟩
      · rename_i hall
        simp only [writerWP_pure]
        refine ⟨by first | rfl | trivial, by omega, fun i h1 h2 => by omega, fun j h1 h2 hf => ?_,
          fun _ h => ?_, fun h => by omega⟩
        · have : j = t + 1 := by omega
          subst this
          exact hmade hf
        · exact absurd h hall
    unfold canTakeBack replacedBy
    try simp only [writerWP_bind, writerWP_get, writerWP_pure]
    rw [writerWP_getNode_known _ _ c w (hlk t (by omega))]
    split
    · simp only [writerWP_bind]; exact writerWP_throw _ _ _ _
    · rename_i hb
      exact hcont _ (Bool.eq_false_iff.mpr hb) rfl

/-! ## A bitmap with room -/

/-- A node whose live lookups are n's but cv's: its live klongs at t. -/
theorem liveAt_iff_of_delete_lookup (n n' : KNode) (t : Time) (cv : Nat)
    (hn : ∀ s, Klong.time s ∈ n.ks → s ≤ t) (hn' : ∀ s, Klong.time s ∈ n'.ks → s ≤ t)
    (hl : ∀ c, n'.live.lookup c = if c == cv then none else n.live.lookup c) :
    ∀ c z, (c, z) ∈ n'.liveAt t ↔ (c, z) ∈ n.liveAt t ∧ c ≠ cv := by
  intro c z
  constructor
  · intro h
    have := liveAt_sub_of_lookup n n' t cv hn hn' hl c z h
    exact ⟨this.2, this.1⟩
  · rintro ⟨h, hc⟩
    rw [KNode.liveAt_of_times n' t hn']
    rw [KNode.liveAt_of_times n t hn] at h
    apply bk_mem_of_lookup
    rw [hl c]
    have hb : (c == cv) = false := by simpa using hc
    rw [hb]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact lookup_of_mem_nodup _ (KNode.live_keys_nodup n) c z h

/-- A loop over a list whose every step yields and keeps an invariant indexed by
the rest of the list. -/
theorem writerWP_forIn_inv {α : Type} (c : Ctx) (I : List α → W → Prop)
    (f : α → PUnit → M (ForInStep PUnit))
    (hstep : ∀ a rest w, I (a :: rest) w →
      WriterWP (f a PUnit.unit) c w (fun r w' => r = ForInStep.yield PUnit.unit ∧ I rest w')) :
    ∀ (L : List α) (w : W), I L w → WriterWP (forIn L PUnit.unit f) c w (fun _ w' => I [] w') := by
  intro L
  induction L with
  | nil => intro w hw; simpa only [List.forIn_nil, writerWP_pure] using hw
  | cons a rest ih =>
    intro w hw
    rw [List.forIn_cons, writerWP_bind]
    refine writerWP_mono (hstep a rest w hw) ?_
    rintro r v ⟨hr, hv⟩
    subst hr
    exact ih v hv

/-- `unlink` of a node the writer has: only its node changes. -/
theorem writerWP_unlink_frameP (o : NodeId) (n : KNode) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup o = some n) :
    WriterWP (unlink o) c w (fun _ w' => w'.taken = w.taken ∧ w'.top = w.top ∧
      w'.next = w.next ∧ w'.vals = w.vals ∧ w'.path = w.path ∧ w'.madeFor = w.madeFor ∧
      ∀ y, y ≠ o → w'.nodes.lookup y = w.nodes.lookup y) := by
  unfold unlink
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known o n c w hlk]
  split
  · simp only [putNode, writerWP_modify]
    refine ⟨by first | rfl | trivial, by first | rfl | trivial, by first | rfl | trivial,
      by first | rfl | trivial, by first | rfl | trivial, by first | rfl | trivial, fun y hy => ?_⟩
    simp only [lookup_upsert, hy, ↓reduceIte]
  · simp only [writerWP_pure]
    exact ⟨by first | rfl | trivial, by first | rfl | trivial, by first | rfl | trivial,
      by first | rfl | trivial, by first | rfl | trivial, by first | rfl | trivial, fun _ _ => by first | rfl | trivial⟩

/-- A fold of `getNode` over nodes the writer has: no change. -/
theorem writerWP_foldlM_getNode (c : Ctx) (f : Nat → KNode → Nat) :
    ∀ (L : List (Option Nat × NodeId)) (s0 : Nat) (w : W),
      (∀ e ∈ L, ∃ n, w.nodes.lookup e.2 = some n) →
      WriterWP (L.foldlM (fun s e => do
        let n ← getNode e.2
        pure (f s n)) s0) c w (fun _ w' => w' = w) := by
  intro L
  induction L with
  | nil => intro s0 w _; simp only [List.foldlM_nil, writerWP_pure]
  | cons e rest ih =>
    intro s0 w h
    obtain ⟨n, hn⟩ := h e List.mem_cons_self
    simp only [List.foldlM_cons, writerWP_bind]
    rw [writerWP_getNode_known _ _ c w hn]
    simp only [writerWP_pure]
    exact ih _ w (fun e' he' => h e' (List.mem_cons_of_mem _ he'))

end SIS.Tree
