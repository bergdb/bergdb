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

set_option linter.unusedSimpArgs false in
/-- `appendDeleteKlong` of cv in node x with room, cv live: x's node is replaced
by one whose live klongs are x's but cv's; nothing else changes. -/
theorem writerWP_appendDeleteKlong_room_frame (x : NodeId) (depth cv : Nat) (n : KNode) (c : Ctx)
    (w : W) (hlk : w.nodes.lookup x = some n) (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ c.i)
    (hne : bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap)
    (hroom : n.size + 1 < c.p.M)
    (hdead1 : deadOver c.p (n.setAt (n.size - 1)
      (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))) = false)
    (hdead2 : deadOver c.p (n.add c.i (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))) = false) :
    WriterWP (appendDeleteKlong x depth cv) c w (fun _ w' =>
      w'.taken = w.taken ∧ w'.top = w.top ∧ w'.vals = w.vals ∧ w'.path = w.path ∧
      w'.next = w.next ∧ w'.madeFor = w.madeFor ∧
      ∃ n', w'.nodes = upsert w.nodes x n' ∧ n'.leaf = n.leaf ∧
        (∀ s, Klong.time s ∈ n'.ks → s ≤ c.i) ∧
        ∀ c', n'.live.lookup c' = if c' == cv then none else n.live.lookup c') := by
  have hroom' : decide (n.size + 1 < c.p.M) = true := by simpa using hroom
  unfold appendDeleteKlong
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c w hlk]
  split
  · exact writerWP_throw _ _ _ _
  · have hno : (bitsUnion n.lastBitmap (n.bitsOf cv) == n.lastBitmap) = false := by
      simpa using hne
    cases hgl : n.ks.getLast? with
    | none =>
      simp only [hno, hroom', hdead2, Bool.not_false, Bool.false_and, Bool.false_eq_true,
        ↓reduceIte, note, putNode, writerWP_bind, writerWP_modify, writerWP_pure, hgl]
      exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, _, rfl, KNode.add_leaf _ _ _,
        KNode.add_times n c.i _ (fun s h => by cases h) hnt, fun c' => n.add_delete_live_lookup c.i cv c'⟩
    | some k =>
      cases k with
      | del old =>
        cases hlt : (n.lastTime == some c.i)
        · simp only [hno, hroom', hdead2, hgl, hlt, Bool.not_false, Bool.true_and, Bool.and_false,
            Bool.false_eq_true, ↓reduceIte, note, putNode, writerWP_bind, writerWP_modify,
            writerWP_pure]
          exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, _, rfl, KNode.add_leaf _ _ _,
            KNode.add_times n c.i _ (fun s h => by cases h) hnt,
            fun c' => n.add_delete_live_lookup c.i cv c'⟩
        · simp only [hno, hdead1, hgl, hlt, Bool.not_false, Bool.true_and, Bool.and_true,
            Bool.false_eq_true, ↓reduceIte, note, putNode, writerWP_bind, writerWP_modify,
            writerWP_pure]
          exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, _, rfl, KNode.setAt_leaf _ _ _,
            KNode.setAt_last_del_times n c.i old _ hgl hnt,
            fun c' => n.setAt_delete_live_lookup cv c' old hgl⟩
      | _ =>
        simp only [hno, hroom', hdead2, hgl, Bool.not_false, Bool.false_and, Bool.false_eq_true,
          ↓reduceIte, note, putNode, writerWP_bind, writerWP_modify, writerWP_pure]
        exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, _, rfl, KNode.add_leaf _ _ _,
          KNode.add_times n c.i _ (fun s h => by cases h) hnt,
          fun c' => n.add_delete_live_lookup c.i cv c'⟩

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
    apply mem_of_lookup_nodup
    rw [hl c]
    have hb : (c == cv) = false := by simpa using hc
    rw [hb]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact lookup_of_mem_nodup _ (KNode.live_keys_nodup n) c z h

end SIS.Tree
