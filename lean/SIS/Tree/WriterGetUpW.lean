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
    (hw : klongsWf n.ks = true)
    (hne : bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap)
    (hroom : n.size + 1 < c.p.M)
    (hdead1 : deadOver c.p (n.setAt (n.size - 1)
      (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))) = false)
    (hdead2 : deadOver c.p (n.add c.i (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))) = false) :
    WriterWP (appendDeleteKlong x depth cv) c w (fun _ w' =>
      w'.taken = w.taken ∧ w'.top = w.top ∧ w'.vals = w.vals ∧ w'.path = w.path ∧
      w'.next = w.next ∧ w'.madeFor = w.madeFor ∧
      ∃ n', w'.nodes = upsert w.nodes x n' ∧ n'.leaf = n.leaf ∧ klongsWf n'.ks = true ∧
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
      exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, _, rfl, KNode.add_leaf _ _ _, KNode.add_delete_wf n c.i cv hw hne,
        KNode.add_times n c.i _ (fun s h => by cases h) hnt, fun c' => n.add_delete_live_lookup c.i cv c'⟩
    | some k =>
      cases k with
      | del old =>
        cases hlt : (n.lastTime == some c.i)
        · simp only [hno, hroom', hdead2, hgl, hlt, Bool.not_false, Bool.true_and, Bool.and_false,
            Bool.false_eq_true, ↓reduceIte, note, putNode, writerWP_bind, writerWP_modify,
            writerWP_pure]
          exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, _, rfl, KNode.add_leaf _ _ _, KNode.add_delete_wf n c.i cv hw hne,
            KNode.add_times n c.i _ (fun s h => by cases h) hnt,
            fun c' => n.add_delete_live_lookup c.i cv c'⟩
        · simp only [hno, hdead1, hgl, hlt, Bool.not_false, Bool.true_and, Bool.and_true,
            Bool.false_eq_true, ↓reduceIte, note, putNode, writerWP_bind, writerWP_modify,
            writerWP_pure]
          exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, _, rfl, KNode.setAt_leaf _ _ _, KNode.setAt_delete_wf n cv old hw hgl,
            KNode.setAt_last_del_times n c.i old _ hgl hnt,
            fun c' => n.setAt_delete_live_lookup cv c' old hgl⟩
      | _ =>
        simp only [hno, hroom', hdead2, hgl, Bool.not_false, Bool.false_and, Bool.false_eq_true,
          ↓reduceIte, note, putNode, writerWP_bind, writerWP_modify, writerWP_pure]
        exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, _, rfl, KNode.add_leaf _ _ _, KNode.add_delete_wf n c.i cv hw hne,
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

set_option linter.unusedSimpArgs false in
/-- The upward delete at the writer's level (deleteUpward's UP path): the key's
leaf X depth, with cv its only live compare value, emptied; the climb stops at an
inner node X stop with room whose klong to the chain is not the empty key's; no
node of the chain was made by the transaction; the merges off. Then the state
before root collapse reads the key as nothing and every other key as before, and
whatever root collapse then gives (`hcoll`) is what the delete gives. -/
theorem writerWP_deleteUpward_inner_get (c : Ctx) (base : View BVal) (X : Nat → NodeId)
    (Nn : Nat → KNode) (K : Nat → Nat) (depth cv : Nat) (pre : List Nat) (rk : NodeId)
    (w : W) (Q : W → Prop) (hdepth : 0 < depth) (hfuel : 1 ≤ c.p.fuel)
    (hp : ∀ i, i ≤ depth → (w.path[i]?).map (·.2) = some (X i))
    (hk : ∀ i, 0 < i → i ≤ depth → w.path[i]? = some (some (K i), X i))
    (hlk : ∀ i, i ≤ depth → w.nodes.lookup (X i) = some (Nn i))
    (htk : ∀ i, i ≤ depth → w.taken.contains (X i) = false)
    (htimes : ∀ i, i ≤ depth → ∀ s, Klong.time s ∈ (Nn i).ks → s ≤ c.i)
    (hdist : ∀ i i', i ≤ depth → i' ≤ depth → X i = X i' → i = i')
    (hne : bitsUnion (Nn depth).lastBitmap ((Nn depth).bitsOf cv) ≠ (Nn depth).lastBitmap)
    (hall : (Nn depth).allKeysIn (bitsUnion (Nn depth).lastBitmap ((Nn depth).bitsOf cv)) = true)
    (hleaf : (Nn depth).leaf = true)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hR : RangeOrder (wNode c.p base w) c.i w.top.rootKey)
    (hwf : ∀ x xn, TReach (wNode c.p base w) c.i w.top.rootKey x → wNode c.p base w x = some xn →
      klongsWf xn.ks = true)
    (hreach : ∀ i, i ≤ depth → TReach (wNode c.p base w) c.i w.top.rootKey (X i))
    (hlinkK : ∀ i, 0 < i → i ≤ depth → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i)
    (hnoval : ∀ i, i ≤ depth → wValue base w (X i) = none)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk) (hcv : cv ∉ pre)
    (hvisL : (X depth, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk)
    (huniq : ∀ key' x m, keyWf key' = true →
      (x, cv) ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
      (x, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk → wNode c.p base w x = some m →
      m.leaf = true → key' = pre ++ [cv])
    (hstopOK : ∀ s, s < depth → (∀ i, s < i → i < depth →
        (Nn i).allKeysIn (bitsUnion (Nn i).lastBitmap ((Nn i).bitsOf (K (i + 1)))) = true) →
      (Nn s).leaf = false ∧ K (s + 1) ≠ 0 ∧ (Nn s).size + 1 < c.p.M ∧
      deadOver c.p ((Nn s).setAt ((Nn s).size - 1)
        (.del (bitsUnion (Nn s).lastBitmap ((Nn s).bitsOf (K (s + 1)))))) = false ∧
      deadOver c.p ((Nn s).add c.i (.del (bitsUnion (Nn s).lastBitmap ((Nn s).bitsOf (K (s + 1)))))) =
        false ∧
      ∀ k, s < k → k ≤ depth → (Nn k).firstTime ≠ some c.i)
    (hmerges : c.p.merges = false)
    (hcoll : ∀ (seg stop : Nat) (w' : W) (sn' : KNode), stop < depth →
      (∀ i, stop < i → i < depth →
        (Nn i).allKeysIn (bitsUnion (Nn i).lastBitmap ((Nn i).bitsOf (K (i + 1)))) = true) →
      w'.taken = w.taken → w'.top = w.top → w'.vals = w.vals →
      (∀ y, y ≠ X stop → (∀ k, stop < k → k ≤ depth → y ≠ X k) → w'.nodes.lookup y = w.nodes.lookup y) →
      w'.nodes.lookup (X stop) = some sn' → sn'.leaf = (Nn stop).leaf → klongsWf sn'.ks = true →
      (∀ s, Klong.time s ∈ sn'.ks → s ≤ c.i) →
      (∀ c' z, (c', z) ∈ sn'.liveAt c.i ↔ (c', z) ∈ (Nn stop).liveAt c.i ∧ c' ≠ K (stop + 1)) →
      (∀ key', keyWf key' = true →
        wGet c.p c.i base w' key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key') →
      WriterWP (collapseRoot (pre ++ [cv]) seg c.p.fuel) c w' (fun _ w'' => Q w'')) :
    WriterWP (deleteUpward (X depth) depth cv (pre ++ [cv])) c w (fun _ w' => Q w') := by
  unfold deleteUpward
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known _ _ c w (hlk depth (Nat.le_refl _))]
  have hne' : (bitsUnion (Nn depth).lastBitmap ((Nn depth).bitsOf cv) == (Nn depth).lastBitmap) = false := by
    simpa using hne
  simp only [hne', hall, Bool.false_eq_true, ↓reduceIte, Bool.not_true]
  rw [writerWP_bind]
  refine writerWP_mono (writerWP_climb c X Nn K depth w hp hk hlk) ?_
  rintro stop w1 ⟨hw1, hst, hbetween, hmadeOK, hstopNode, hself⟩
  have hw1' := hw1.symm
  subst hw1'
  have hsd : stop ≠ depth := fun h => by have := (hself h).1; omega
  have hsd' : (stop == depth) = false := by simpa using hsd
  simp only [hsd', Bool.false_eq_true, ↓reduceIte]
  have hsD : stop < depth := by omega
  obtain ⟨hsl, hK0, hroom, hd1, hd2, hnone⟩ := hstopOK stop hsD hbetween
  rw [writerWP_bind]
  refine (writerWP_note_iff _ c w _).mpr ?_
  generalize hw0 : ({ w with trail := "up.climb" :: w.trail } : W) = w0
  have h0n : w0.nodes = w.nodes := by rw [← hw0]
  have h0p : w0.path = w.path := by rw [← hw0]
  have h0t : w0.taken = w.taken := by rw [← hw0]
  have h0top : w0.top = w.top := by rw [← hw0]
  have h0v : w0.vals = w.vals := by rw [← hw0]
  rw [writerWP_bind, writerWP_get, writerWP_bind]
  refine writerWP_mono (writerWP_foldlM_getNode c (fun s n => if n.leaf = true then s + 1 else s)
    (List.take stop w0.path) 0 w0 ?_) ?_
  · intro e he
    obtain ⟨i, hie⟩ := List.mem_iff_getElem?.mp he
    rw [List.getElem?_take] at hie
    split at hie
    · rename_i hi
      have h1 := hp i (by omega)
      rw [← h0p, hie] at h1
      simp only [Option.map_some, Option.some.injEq] at h1
      rw [h1, h0n]
      exact ⟨_, hlk i (by omega)⟩
    · cases hie
  rintro seg w0' hw0'
  have hw0'' := hw0'.symm
  subst hw0''
  -- the loop: the chain's nodes unlinked
  let I : List Nat → W → Prop := fun rem v =>
    v.taken = w0.taken ∧ v.top = w0.top ∧ v.vals = w0.vals ∧ v.path = w0.path ∧
    (∀ y, (∀ k, stop < k → k ≤ depth → y ≠ X k) → v.nodes.lookup y = w0.nodes.lookup y) ∧
    (∀ j ∈ rem, j < depth - stop ∧ v.nodes.lookup (X (depth - j)) = some (Nn (depth - j))) ∧
    rem.Nodup
  rw [writerWP_bind]
  refine writerWP_mono (writerWP_forIn_inv c I _ ?_ (List.range (depth - stop)) w0
    ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl, fun j hj => ⟨List.mem_range.mp hj, by
      rw [h0n]; exact hlk _ (by omega)⟩, List.nodup_range⟩) ?_
  · intro a rest v ⟨hvt, hvtop, hvv, hvp, hvn, hvrem, hnd⟩
    obtain ⟨ha, hva⟩ := hvrem a List.mem_cons_self
    simp only [writerWP_bind]
    refine writerWP_pathNode_known (depth - a) (X (depth - a)) c v
      (by rw [hvp, h0p]; exact hp _ (by omega)) _ ?_
    rw [writerWP_getNode_known _ _ c v hva]
    have hnm : ((Nn (depth - a)).firstTime == some c.i) = false := by
      simpa using hnone (depth - a) (by omega) (by omega)
    simp only [hnm, Bool.false_eq_true, ↓reduceIte, writerWP_bind]
    refine (writerWP_note_iff _ c v _).mpr ?_
    refine writerWP_mono (writerWP_unlink_frameP _ _ c _ hva) ?_
    rintro _ v2 ⟨h2t, h2top, _, h2v, h2p, _, h2l⟩
    simp only [writerWP_pure]
    refine ⟨by first | rfl | trivial, h2t.trans hvt, h2top.trans hvtop, h2v.trans hvv, h2p.trans hvp, fun y hy => ?_,
      fun j hj => ?_, (List.nodup_cons.mp hnd).2⟩
    · rw [h2l y (hy (depth - a) (by omega) (by omega)), hvn y hy]
    · obtain ⟨hj1, hj2⟩ := hvrem j (List.mem_cons_of_mem _ hj)
      refine ⟨hj1, ?_⟩
      have hja : j ≠ a := fun he => (List.nodup_cons.mp hnd).1 (he ▸ hj)
      rw [h2l _ (fun he => hja (by have := hdist _ _ (by omega) (by omega) he; omega))]
      exact hj2
  rintro _ w2 ⟨h2t, h2top, h2v, h2p, h2n, _, _⟩
  simp only [writerWP_bind]
  refine writerWP_pathNode_known stop (X stop) c w2 (by rw [h2p, h0p]; exact hp stop (by omega)) _ ?_
  refine writerWP_klongAt_known (stop + 1) (K (stop + 1)) (X (stop + 1)) c w2
    (by rw [h2p, h0p]; exact hk _ (by omega) (by omega)) _ ?_
  have hls2 : w2.nodes.lookup (X stop) = some (Nn stop) := by
    rw [h2n _ (fun k h1 h2 he => by have := hdist _ _ (by omega) (by omega) he; omega), h0n]
    exact hlk stop (by omega)
  rw [writerWP_getNode_known _ _ c w2 hls2]
  refine writerWP_ghOf_cached _ _ c w2 hls2 _ (fun gh => ?_)
  simp only [hsl, Bool.false_eq_true, ↓reduceIte]
  have hK0' : (K (stop + 1) != 0) = true := by simpa using hK0
  split
  · simp only [writerWP_bind]; exact writerWP_throw _ _ _ _
  simp only [hK0', ↓reduceIte, writerWP_bind, hmerges, Bool.false_eq_true]
  have hst_t : ∀ s', Klong.time s' ∈ (Nn stop).ks → s' ≤ c.i := htimes stop (by omega)
  have hsx : (K (stop + 1), X (stop + 1)) ∈ (Nn stop).liveAt c.i := by
    have := hlinkK (stop + 1) (by omega) (by omega); simpa using this
  have hneS : bitsUnion (Nn stop).lastBitmap ((Nn stop).bitsOf (K (stop + 1))) ≠ (Nn stop).lastBitmap := by
    apply KNode.delete_bitmap_changes_of_live
    rw [KNode.liveAt_of_times _ c.i hst_t] at hsx
    exact List.mem_map.mpr ⟨_, hsx, rfl⟩
  have hswf : klongsWf (Nn stop).ks = true := by
    have := hwf (X stop) (Nn stop) (hreach stop (by omega))
      (by simp only [wNode, htk stop (by omega), Bool.false_eq_true, ↓reduceIte, hlk stop (by omega)])
    exact this
  refine writerWP_mono (writerWP_appendDeleteKlong_room_frame (X stop) stop (K (stop + 1)) (Nn stop)
    c w2 hls2 hst_t hswf hneS hroom hd1 hd2) ?_
  rintro _ w3 ⟨h3t, h3top, h3v, _, _, _, n', h3n, hn'l, hn'w, hn't, hn'lk⟩
  have h3tw : w3.taken = w.taken := by rw [h3t, h2t, h0t]
  refine writerWP_mono (hcoll seg stop w3 n' hsD hbetween h3tw (by rw [h3top, h2top, h0top])
    (by rw [h3v, h2v, h0v])
    (by
      intro y hys hnc
      rw [h3n, lookup_upsert]
      simp only [hys, ↓reduceIte]
      rw [h2n y hnc, h0n])
    (by rw [h3n, lookup_upsert]; simp) hn'l hn'w hn't
    (liveAt_iff_of_delete_lookup (Nn stop) n' c.i (K (stop + 1)) hst_t hn't hn'lk) ?_) ?_
  · intro key' hkw
    have hV3 : wValue base w3 = wValue base w :=
      wValue_congr' base w3 w (by rw [h3t, h2t, h0t]) (by rw [h3v, h2v, h0v])
    have hone : ∀ i, stop < i → i < depth → ∀ c' z, (c', z) ∈ (Nn i).liveAt c.i → z = X (i + 1) := by
      intro i h1 h2 c' z hm
      have ht := htimes i (by omega)
      have hm' : (c', z) ∈ (Nn i).live := by rw [← KNode.liveAt_of_times _ c.i ht]; exact hm
      have hc := allKeysIn_live_cv (Nn i) (K (i + 1)) (hbetween i h1 h2) c' z hm'
      have hl := hlinkK (i + 1) (by omega) (by omega)
      rw [show i + 1 - 1 = i by omega] at hl
      rw [KNode.liveAt_of_times _ c.i ht] at hl
      have hnd := KNode.live_keys_nodup (Nn i)
      have e1 := lookup_some_of_mem hnd hm'
      have e2 := lookup_some_of_mem hnd hl
      rw [hc] at e1
      rw [e1] at e2
      exact Option.some.inj e2
    have honly : ∀ c' z, (c', z) ∈ (Nn depth).liveAt c.i → c' = cv := by
      intro c' z hm
      have hm' : (c', z) ∈ (Nn depth).live := by
        rw [← KNode.liveAt_of_times _ c.i (htimes depth (Nat.le_refl _))]; exact hm
      exact allKeysIn_live_cv (Nn depth) cv hall c' z hm'
    unfold wGet
    rw [hV3, h3top, h2top, h0top]
    exact getFromR_up_inner (wNode c.p base w) (wNode c.p base w3) (wValue base w) c.i c.p.fuel hfuel
      w.top.rootKey X Nn K stop depth hsD pre cv rk hT hR hwf (hreach stop (by omega))
      (fun i h1 h2 => by simp only [wNode, htk i h2, Bool.false_eq_true, ↓reduceIte, hlk i h2])
      (fun i h1 h2 => hlinkK i (by omega) h2) hone hleaf honly (fun i h1 h2 => hnoval i h2)
      (fun i h1 h2 he => by have := hdist i depth (by omega) (Nat.le_refl _) he; omega)
      hrk hcv hvisL huniq
      (by
        intro u hu hus hnc
        simp only [wNode, h3tw, h3n, lookup_upsert, hus, ↓reduceIte, h2n u hnc, h0n])
      n' hsl (by simp only [wNode, h3tw, htk stop (by omega), h3n, lookup_upsert, Bool.false_eq_true,
        ↓reduceIte])
      (by rw [hn'l]; exact hsl)
      (liveAt_iff_of_delete_lookup (Nn stop) n' c.i (K (stop + 1)) hst_t hn't hn'lk) key' hkw
  · intro _ w4 h4
    simp only [writerWP_pure]
    exact h4

end SIS.Tree
