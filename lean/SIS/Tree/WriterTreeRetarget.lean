/-
The merge's take-back of a node the transaction made (bergdb 024-22,
`OpTreeOK`): `retarget p src dst` points the klongs of the transaction in p that
name src to dst, so a live klong after is one before, or names dst where one
before named src (`KNode.retarget_liveAt`).
-/
import SIS.Tree.WriterTreeNewSeg

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The retarget map of one klong at its index. -/
def retargetStep (ti : Nat) (src dst : NodeId) (q : Klong × Nat) : Klong :=
  match q.1 with
  | .key cv y => if ti < q.2 && y == src then Klong.key cv dst else q.1
  | _ => q.1

theorem retargetKlongs_eq (ks : List Klong) (ti : Nat) (src dst : NodeId) :
    retargetKlongs ks ti src dst = ks.zipIdx.map (retargetStep ti src dst) := by
  unfold retargetKlongs retargetStep
  congr 1

/-- The prefix before a time of a list mapped klong by klong, time klongs kept:
the map of the prefix. -/
theorem takeWhile_zipIdx_map (p : Klong → Bool) (g : Klong × Nat → Klong)
    (hg : ∀ q, p (g q) = p q.1) :
    ∀ (l : List Klong) (s : Nat), ((l.zipIdx s).map g).takeWhile p = ((l.takeWhile p).zipIdx s).map g := by
  intro l
  induction l with
  | nil => intro s; rfl
  | cons a l ih =>
    intro s
    simp only [List.zipIdx_cons, List.map_cons, List.takeWhile_cons]
    rw [hg (a, s)]
    split
    · simp only [List.zipIdx_cons, List.map_cons]
      rw [ih (s + 1)]
    · rfl

theorem retargetStep_time (ti : Nat) (src dst : NodeId) (q : Klong × Nat) (u : Time) :
    retargetStep ti src dst q = .time u ↔ q.1 = .time u := by
  rcases q with ⟨k, i⟩
  cases k with
  | key cv y =>
    simp only [retargetStep]
    split <;> simp
  | time t => simp [retargetStep]
  | del b => simp [retargetStep]

theorem retargetStep_del (ti : Nat) (src dst : NodeId) (q : Klong × Nat) (b : List Nat) :
    retargetStep ti src dst q = .del b ↔ q.1 = .del b := by
  rcases q with ⟨k, i⟩
  cases k with
  | key cv y =>
    simp only [retargetStep]
    split <;> simp
  | time t => simp [retargetStep]
  | del b' => simp [retargetStep]

theorem lastBitmapOf_zipIdx_map (ti : Nat) (src dst : NodeId) :
    ∀ (l : List Klong) (s : Nat) (d : List Nat),
      ((l.zipIdx s).map (retargetStep ti src dst)).foldl (fun d k => match k with
        | .del b => b
        | _ => d) d = l.foldl (fun d k => match k with
        | .del b => b
        | _ => d) d := by
  intro l
  induction l with
  | nil => intro s d; rfl
  | cons a l ih =>
    intro s d
    simp only [List.zipIdx_cons, List.map_cons, List.foldl_cons]
    rw [ih]
    congr 1
    cases a with
    | key cv y =>
      by_cases hc : (decide (ti < s) && y == src) = true
      · simp only [retargetStep, hc, ↓reduceIte]
      · simp only [retargetStep, hc, Bool.false_eq_true, ↓reduceIte]
    | time t => rfl
    | del b => rfl

theorem zipIdx_map_zipIdx (g : Klong × Nat → Klong) :
    ∀ (l : List Klong) (s : Nat), ((l.zipIdx s).map g).zipIdx s = (l.zipIdx s).map (fun q => (g q, q.2)) := by
  intro l
  induction l with
  | nil => intro s; rfl
  | cons a l ih =>
    intro s
    simp only [List.zipIdx_cons, List.map_cons]
    rw [ih (s + 1)]

theorem keyLookupFold_retarget (del : List Nat) (c : Nat) (ti : Nat) (src dst : NodeId) :
    ∀ (xs : List (Klong × Nat)) (v v' : Option NodeId),
      (v' = v ∨ (v = some src ∧ v' = some dst)) →
      (xs.map (fun q => (retargetStep ti src dst q, q.2))).foldl (keyLookupStep del c) v' =
        xs.foldl (keyLookupStep del c) v ∨
      (xs.foldl (keyLookupStep del c) v = some src ∧
        (xs.map (fun q => (retargetStep ti src dst q, q.2))).foldl (keyLookupStep del c) v' = some dst) := by
  intro xs
  induction xs with
  | nil => intro v v' h; simpa using h
  | cons q qs ih =>
    intro v v' hv
    simp only [List.map_cons, List.foldl_cons]
    apply ih
    rcases q with ⟨k, i⟩
    cases k with
    | key a y =>
      simp only [retargetStep, keyLookupStep]
      by_cases hd : del.contains i = true
      · by_cases hc : (decide (ti < i) && y == src) = true
        · simp only [hc, ↓reduceIte, hd]; exact hv
        · simp only [hc, Bool.false_eq_true, ↓reduceIte, hd]; exact hv
      · have hd' : del.contains i = false := by simpa using hd
        by_cases hac : (a == c) = true
        · by_cases hc : (decide (ti < i) && y == src) = true
          · simp only [hc, ↓reduceIte, hd', Bool.false_eq_true, hac]
            simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
            rw [hc.2]
            simp
          · simp only [hc, Bool.false_eq_true, ↓reduceIte, hd', hac]
            simp
        · have hac' : (a == c) = false := by simpa using hac
          by_cases hc : (decide (ti < i) && y == src) = true
          · simp only [hc, ↓reduceIte, hd', Bool.false_eq_true, hac']; exact hv
          · simp only [hc, Bool.false_eq_true, ↓reduceIte, hd', hac']; exact hv
    | time t => exact hv
    | del b => exact hv

/-- A node retargeted: a live klong after is one before, or names dst where one
before named src. -/
theorem KNode.retarget_liveAt (n : KNode) (ti : Nat) (src dst : NodeId) (t : Time) (c : Nat)
    (z : NodeId) (h : (c, z) ∈ ({ n with ks := retargetKlongs n.ks ti src dst } : KNode).liveAt t) :
    (c, z) ∈ n.liveAt t ∨ (z = dst ∧ (c, src) ∈ n.liveAt t) := by
  have hn := KNode.liveAt_keys_nodup ({ n with ks := retargetKlongs n.ks ti src dst } : KNode) t
  have hl := lookup_of_mem_nodup _ hn c z h
  rw [KNode.liveAt_lookup] at hl
  have hp : ∀ q, (fun k => match k with
      | Klong.time x => decide (x ≤ t)
      | _ => true) (retargetStep ti src dst q) = (fun k => match k with
      | Klong.time x => decide (x ≤ t)
      | _ => true) q.1 := by
    intro q
    rcases q with ⟨k, i⟩
    cases k with
    | key cv y =>
      by_cases hc : (decide (ti < i) && y == src) = true
      · simp only [retargetStep, hc, ↓reduceIte]
      · simp only [retargetStep, hc, Bool.false_eq_true, ↓reduceIte]
    | time u => rfl
    | del b => rfl
  have hpre : prefixAt (retargetKlongs n.ks ti src dst) t =
      ((prefixAt n.ks t).zipIdx).map (retargetStep ti src dst) := by
    rw [retargetKlongs_eq]
    unfold prefixAt
    exact takeWhile_zipIdx_map _ _ hp n.ks 0
  have hdel : ({ n with ks := retargetKlongs n.ks ti src dst } : KNode).delAt t = n.delAt t := by
    unfold KNode.delAt
    simp only
    rw [hpre]
    unfold lastBitmapOf
    exact lastBitmapOf_zipIdx_map ti src dst _ 0 []
  simp only at hl
  rw [hpre, hdel] at hl
  unfold keyLookup at hl
  rw [zipIdx_map_zipIdx] at hl
  rcases keyLookupFold_retarget (n.delAt t) c ti src dst _ none none (Or.inl rfl) with h1 | ⟨h1, h2⟩
  · rw [hl] at h1
    left
    apply mem_of_lookup_nodup _ c z
    rw [KNode.liveAt_lookup]
    exact h1.symm
  · rw [hl] at h2
    simp only [Option.some.injEq] at h2
    right
    refine ⟨h2, ?_⟩
    apply mem_of_lookup_nodup _ c src
    rw [KNode.liveAt_lookup]
    exact h1

/-- `retarget` on a cached node: its node after is it, or it retargeted. -/
theorem writerWP_retarget_frame (p src dst : NodeId) (n : KNode) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup p = some n) :
    WriterWP (retarget p src dst) c w (fun _ w' => w'.taken = w.taken ∧ w'.top = w.top ∧
      w'.next = w.next ∧ (∀ y, y ≠ p → w'.nodes.lookup y = w.nodes.lookup y) ∧
      ∃ n', w'.nodes.lookup p = some n' ∧
        (n' = n ∨ ∃ ti, n' = { n with ks := retargetKlongs n.ks ti src dst })) := by
  unfold retarget
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known p n c w hlk]
  split
  · unfold putNode
    refine (writerWP_modify _ c w _).mpr ?_
    have hrk : ∃ n' : KNode, n' = { n with ks := retargetKlongs n.ks (n.lastTimeIndex.getD 0) src dst } :=
      ⟨_, rfl⟩
    obtain ⟨n', hn'⟩ := hrk
    refine ⟨rfl, rfl, rfl, fun y hy => ?_, n', ?_, Or.inr ⟨_, hn'⟩⟩
    · show (upsert w.nodes p _).lookup y = _
      rw [lookup_upsert]; simp [hy]
    · show (upsert w.nodes p _).lookup p = _
      rw [lookup_upsert, hn']; simp only [↓reduceIte]; rfl
  · refine (writerWP_pure _ c w _).mpr ?_
    exact ⟨rfl, rfl, rfl, fun _ _ => rfl, n, hlk, Or.inl rfl⟩

theorem writerWP_takenBack_iff (x : NodeId) (c : Ctx) (w : W) (post : Unit → W → Prop) :
    WriterWP (takenBack x) c w post ↔ post () { w with taken := x :: w.taken } :=
  writerWP_modify _ c w post

theorem writerWP_note_iff (s : String) (c : Ctx) (w : W) (post : Unit → W → Prop) :
    WriterWP (note s) c w post ↔ post () { w with trail := s :: w.trail } :=
  writerWP_modify _ c w post

/-- The merge's last loop: each node is taken back (its parent's klongs of the
transaction that name it name m1, which none live of them does) or unlinked;
the parent's live klongs are kept or fewer, and nothing else changes but the
nodes' lookups and their taking back. -/
theorem writerWP_mergeCleanup_frame (p m1 : NodeId) (t : Time) (c : Ctx) :
    ∀ (xs : List (NodeId × Bool)) (w : W) (n : KNode), (∀ q ∈ xs, q.1 ≠ p) →
    w.nodes.lookup p = some n → (∀ q ∈ xs, ∀ c', (c', q.1) ∉ n.liveAt t) →
    WriterWP (forIn xs PUnit.unit (fun q _ => if q.2 = true then (do
        retarget p q.1 m1
        takenBack q.1
        note "merge.takeback"
        pure (ForInStep.yield PUnit.unit)) else (do
        unlink q.1
        pure (ForInStep.yield PUnit.unit)))) c w
      (fun _ w' => w'.top = w.top ∧ w'.next = w.next ∧
        (∀ y, (∀ q ∈ xs, y ≠ q.1) → w'.taken.contains y = w.taken.contains y) ∧
        (∀ y, y ≠ p → (∀ q ∈ xs, y ≠ q.1) → w'.nodes.lookup y = w.nodes.lookup y) ∧
        ∃ n', w'.nodes.lookup p = some n' ∧ ∀ c' z, (c', z) ∈ n'.liveAt t → (c', z) ∈ n.liveAt t) := by
  intro xs
  induction xs with
  | nil =>
    intro w n _ hlk _
    rw [List.forIn_nil]
    refine (writerWP_pure _ c w _).mpr ?_
    exact ⟨rfl, rfl, fun _ _ => rfl, fun _ _ _ => rfl, n, hlk, fun _ _ h => h⟩
  | cons q qs ih =>
    intro w n hne hlk hno
    rw [List.forIn_cons]
    have hqp : q.1 ≠ p := hne q List.mem_cons_self
    have hrest : ∀ (w1 : W) (n1 : KNode), w1.top = w.top → w1.next = w.next →
        (∀ y, y ≠ q.1 → w1.taken.contains y = w.taken.contains y) →
        (∀ y, y ≠ p → y ≠ q.1 → w1.nodes.lookup y = w.nodes.lookup y) →
        w1.nodes.lookup p = some n1 → (∀ c' z, (c', z) ∈ n1.liveAt t → (c', z) ∈ n.liveAt t) →
        WriterWP (forIn qs PUnit.unit (fun q _ => if q.2 = true then (do
          retarget p q.1 m1
          takenBack q.1
          note "merge.takeback"
          pure (ForInStep.yield PUnit.unit)) else (do
          unlink q.1
          pure (ForInStep.yield PUnit.unit)))) c w1
        (fun _ w' => w'.top = w.top ∧ w'.next = w.next ∧
          (∀ y, (∀ q' ∈ q :: qs, y ≠ q'.1) → w'.taken.contains y = w.taken.contains y) ∧
          (∀ y, y ≠ p → (∀ q' ∈ q :: qs, y ≠ q'.1) → w'.nodes.lookup y = w.nodes.lookup y) ∧
          ∃ n', w'.nodes.lookup p = some n' ∧ ∀ c' z, (c', z) ∈ n'.liveAt t → (c', z) ∈ n.liveAt t) := by
      intro w1 n1 h1top h1next h1t h1l h1p h1sub
      refine writerWP_mono (ih w1 n1 (fun q' hq' => hne q' (List.mem_cons_of_mem _ hq')) h1p
        (fun q' hq' c' hm => hno q' (List.mem_cons_of_mem _ hq') c' (h1sub _ _ hm))) ?_
      intro _ w2 ⟨h2top, h2next, h2t, h2l, n2, h2p, h2sub⟩
      refine ⟨h2top.trans h1top, h2next.trans h1next, fun y hy => ?_, fun y hyp hy => ?_,
        n2, h2p, fun c' z hm => h1sub _ _ (h2sub _ _ hm)⟩
      · rw [h2t y (fun q' hq' => hy q' (List.mem_cons_of_mem _ hq')),
          h1t y (hy q List.mem_cons_self)]
      · rw [h2l y hyp (fun q' hq' => hy q' (List.mem_cons_of_mem _ hq')),
          h1l y hyp (hy q List.mem_cons_self)]
    by_cases hq2 : q.2 = true
    · simp only [writerWP_bind, hq2, ↓reduceIte]
      refine writerWP_mono (writerWP_retarget_frame p q.1 m1 n c w hlk) ?_
      intro _ w1 ⟨h1t, h1top, h1next, h1l, n1, h1p, h1n⟩
      refine (writerWP_takenBack_iff _ c w1 _).mpr ?_
      refine (writerWP_note_iff _ c _ _).mpr ?_
      refine (writerWP_pure _ c _ _).mpr ?_
      dsimp only
      refine hrest _ n1 ?_ ?_ ?_ ?_ ?_ ?_
      · exact h1top
      · exact h1next
      · intro y hy
        show (q.1 :: w1.taken).contains y = _
        rw [List.contains_cons, h1t]
        have : (y == q.1) = false := by simpa using hy
        simp [this]
      · intro y hyp _; exact h1l y hyp
      · exact h1p
      · intro c' z hm
        rcases h1n with he | ⟨ti, he⟩
        · rw [he] at hm; exact hm
        · rw [he] at hm
          rcases KNode.retarget_liveAt n ti q.1 m1 t c' z hm with h | ⟨_, h⟩
          · exact h
          · exact absurd h (hno q List.mem_cons_self c')
    · have hq2' : q.2 = false := by simpa using hq2
      simp only [writerWP_bind, hq2', Bool.false_eq_true, ↓reduceIte]
      refine writerWP_mono (writerWP_unlink_frame q.1 c w) ?_
      intro _ w1 ⟨h1t, h1top, h1next, h1l⟩
      refine (writerWP_pure _ c _ _).mpr ?_
      dsimp only
      apply hrest _ n h1top h1next
      · intro y _; rw [h1t]
      · intro y _ hy; exact h1l y hy
      · rw [h1l p (Ne.symm hqp)]; exact hlk
      · intro c' z hm; exact hm

end SIS.Tree
