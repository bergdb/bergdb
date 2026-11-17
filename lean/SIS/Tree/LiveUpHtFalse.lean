/-
`UpHtWalk` (LiveUpRoom.lean) is false for every context (bergdb 030-01, R2's
heights). It asks an invariant Ju that holds at every state of the heights'
walk (`HtJ0`), that every take-back keeps for any node, parent and compare value,
and that gives `HtInv`. But a take-back of x from parent q, at a state where a
third node z of the overlay also names x, leaves z naming a node taken back, so
`HtCache` fails at z: the checked copy's `checkFree` (`ht_takeBackChk`) is what
excludes that. The state below is such a state: three nodes of the transaction,
q and z inner nodes of height 1 that both name the empty leaf x of height 0, x
made by a split (`madeFor`). It meets `HtJ0` for every context, oracle and B.

So `liveDel_upRoom` and `liveDel_upRoom_live` hold with a premise that no Ju
meets (`not_exists_upHtWalk`): as stated, they never apply.
-/
import SIS.Tree.LiveUpRoom

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The inner node of the counterexample: one klong of time t naming x. -/
def upHtNq (t : Time) (x : NodeId) : KNode := { leaf := false, ks := [.time t, .key 0 x] }

/-- The empty leaf of the counterexample. -/
def upHtNx (t : Time) : KNode := { leaf := true, ks := [.time t] }

/-- The counterexample's state: x = B the empty leaf, q = B + 1 and z = B + 2
inner nodes naming it, x made by a split that replaced B + 3. -/
def upHtState (c : Ctx) (B : NodeId) : W :=
  { nodes := [(B + 2, upHtNq c.i B), (B + 1, upHtNq c.i B), (B, upHtNx c.i)]
    gh := [(B, 0, 0), (B + 1, 0, 1), (B + 2, 0, 1)]
    made := [⟨B, c.p.keyLevel 0 0, false⟩, ⟨B + 1, c.p.keyLevel 0 1, false⟩,
      ⟨B + 2, c.p.keyLevel 0 1, false⟩]
    madeFor := [(B, B + 3)]
    next := B + 3
    path := []
    top := { id := 0, ord := 0, time := 0, rootKey := B + 1, skips := [] }
    outside := [(B, 0, 0), (B + 1, 0, 1), (B + 2, 0, 1)] }

/-- The counterexample's state after the take-back of x from q. -/
def upHtAfter (c : Ctx) (B : NodeId) : W :=
  { upHtState c B with
    nodes := [(B + 2, upHtNq c.i B), (B + 1, upHtNq c.i (B + 3)), (B, upHtNx c.i)]
    taken := [B], trail := ["up.takeback"] }

theorem upHtNq_live (t : Time) (x : NodeId) : (upHtNq t x).live = [(0, x)] := by
  simp [upHtNq, KNode.live, KNode.lastVersion, KNode.lastVersionGivenDel, KNode.lastBitmap, lastBitmapOf,
    setCv, List.zipIdx]

/-- A live klong of a node's version before t is a key klong of the node. -/
theorem upHt_prev_key (n : KNode) (t : Time) (cv : Nat) (y : NodeId) (h : (cv, y) ∈ (n.toPrev t).live) :
    ∃ c0, Klong.key c0 y ∈ n.ks := by
  obtain ⟨c0, hc⟩ := live_key_mem _ cv y h
  exact ⟨c0, (List.takeWhile_sublist _).subset hc⟩

theorem upHtNq_ptr (t : Time) (x : NodeId) (cv y : NodeId)
    (h : (cv, y) ∈ (upHtNq t x).live ∨ ∃ s, (cv, y) ∈ ((upHtNq t x).toPrev s).live) : y = x := by
  obtain ⟨c0, hc0⟩ : ∃ c0, Klong.key c0 y ∈ (upHtNq t x).ks := by
    rcases h with h | ⟨s, h⟩
    · exact live_key_mem _ cv y h
    · exact upHt_prev_key _ s cv y h
  simp [upHtNq] at hc0
  exact hc0.2

theorem upHtState_takeBack (c : Ctx) (B : NodeId) :
    takeBack B (B + 1) 0 c (upHtState c B) = .ok ((), upHtAfter c B) := by
  have e1 : (B == B + 1) = false := by simp
  have e2 : (B + 1 == B + 2) = false := by simp
  have e3 : (B + 2 == B + 1) = false := by simp
  simp [e1, e2, e3, upHtAfter, takeBack, getNode, replacedBy, retarget, takenBack, note, putNode, upHtState,
    upHtNq, KNode.linkIndex, KNode.lastTime, KNode.lastBitmap, lastBitmapOf, KNode.lastTimeIndex, List.zipIdx, bind,
    ReaderT.bind, StateT.bind, MonadState.get, List.lookup, upsert, getThe, MonadStateOf.get, StateT.get, read,
    readThe, MonadReaderOf.read, ReaderT.read, pure, ReaderT.pure, StateT.pure, Except.pure, Except.bind, modify,
    modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, liftM, monadLift, MonadLift.monadLift]

/-- The counterexample's state is one of the heights' walk, for every context,
oracle and B. -/
theorem upHtState_htJ0 (c : Ctx) (H : NodeId → Nat → Prop) (B : NodeId) : HtJ0 c H B (upHtState c B) := by
  have hks : ∀ x n, (x, n) ∈ (upHtState c B).nodes →
      (x = B + 2 ∧ n = upHtNq c.i B) ∨ (x = B + 1 ∧ n = upHtNq c.i B) ∨ (x = B ∧ n = upHtNx c.i) := by
    intro x n h
    simpa [upHtState] using h
  have hgh : ∀ x g h, (x, g, h) ∈ (upHtState c B).gh →
      (x = B ∧ g = 0 ∧ h = 0) ∨ (x = B + 1 ∧ g = 0 ∧ h = 1) ∨ (x = B + 2 ∧ g = 0 ∧ h = 1) := by
    intro x g h hm
    simpa [upHtState] using hm
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp [upHtState]
  · simp [upHtState]
  · intro q hq
    simp [upHtState] at hq
    rcases hq with rfl | rfl | rfl <;> simp [upHtState] <;> omega
  · simp [upHtState]
  · intro x n g h hn hg
    rcases hks x n hn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hgh _ g h hg with ⟨he, rfl, rfl⟩ | ⟨he, rfl, rfl⟩ | ⟨he, rfl, rfl⟩ <;>
      first | omega | rfl
  · intro x g h hg
    right
    rcases hgh x g h hg with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      refine ⟨by omega, by simp [upHtState], fun _ => by simp [upHtState]⟩
  · intro x hx
    simp [upHtState] at hx
  · intro h
    simp [upHtState] at h
  · intro x n g h hn hg _
    have htk : ∀ y, (upHtState c B).taken.contains y = false := fun y => by simp [upHtState]
    rcases hks x n hn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals
      rcases hgh _ g h hg with ⟨he, rfl, rfl⟩ | ⟨he, rfl, rfl⟩ | ⟨he, rfl, rfl⟩ <;> (try omega)
    all_goals
      refine ⟨fun cv y hy => ⟨htk y, fun _ => ?_⟩, fun cv y hy => ⟨htk y, fun _ => ?_⟩, ?_⟩
    all_goals first
      | (intro t ht; simp [upHtNq, upHtNx] at ht; omega)
      | exact absurd rfl ‹(0 : Nat) ≠ 0›
      | (rw [upHtNq_ptr _ _ _ _ (Or.inl hy)]; exact Or.inl ⟨0, by simp [upHtState]⟩)
      | (rw [upHtNq_ptr _ _ _ _ (Or.inr ⟨_, hy⟩)]; exact Or.inl ⟨0, by simp [upHtState]⟩)
  · intro d a q cv y h1
    simp [upHtState] at h1
  · intro d a q h1
    simp [upHtState] at h1
  · simp [upHtState]
  · intro x hx
    simp [upHtState] at hx
  · intro d a q h1
    simp [upHtState] at h1
  · intro d a q hd
    simp [upHtState] at hd
  · intro q hq
    rcases hks q.1 q.2 hq with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> simp [upHtNq, upHtNx, klongsWf, List.zipIdx]

/-- After the take-back, z = B + 2 names x = B, which is taken back: no `HtInv`. -/
theorem upHtAfter_not_htInv (c : Ctx) (H : NodeId → Nat → Prop) (B : NodeId) :
    ¬ HtInv H B c (upHtAfter c B) := by
  intro hi
  have hN := hi.cache (B + 2) (upHtNq c.i B) 0 1 (by simp [upHtAfter]) (by simp [upHtAfter, upHtState])
    (by simp [upHtAfter])
  have := (hN.live 0 B (by rw [upHtNq_live]; simp)).1
  simp [upHtAfter] at this

/-- `UpHtWalk` is false for every context, oracle, B and invariant Ju: its take-back
step asks Ju kept by a take-back that leaves another node naming the node taken back. -/
theorem upHtWalk_false (c : Ctx) (H : NodeId → Nat → Prop) (B : NodeId) (Ju : W → Prop) :
    ¬ UpHtWalk c H B Ju := by
  rintro ⟨h0, -, ht, -, -, -, hh⟩
  exact upHtAfter_not_htInv c H B
    (hh _ (ht B (B + 1) 0 _ (h0 _ (upHtState_htJ0 c H B)) () _ (upHtState_takeBack c B)))

/-- No Ju meets `UpHtWalk`: the premise of `liveDel_upRoom` and `liveDel_upRoom_live`
is never met, at any run. -/
theorem not_exists_upHtWalk (c : Ctx) (H : NodeId → Nat → Prop) (B : NodeId) :
    ¬ ∃ Ju, UpHtWalk c H B Ju :=
  fun ⟨Ju, h⟩ => upHtWalk_false c H B Ju h

end SIS.Tree
