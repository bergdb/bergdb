/-
The contract package (bergdb 030-10): the rules for the steps of the model's
writer (`SIS.Tree.M`, a reader of the context, a state and an error): what
holds of every result of a step that gives no error (`WP`).

Copied from the old proofs (lean/SIS/Tree/WriterWP.lean, bergdb 024-12), which
this package does not import: the definition and the rules for `pure`,
`throw`, `bind`, `read`, `get`, `set`, `modify` and `if`.
-/
import Contract.Writer

namespace Contract

open SIS.Tree (M Ctx W)

/-- Every result of the step f from the state w that is no error meets the
postcondition. -/
def WP {α : Type} (f : M α) (c : Ctx) (w : W) (post : α → W → Prop) : Prop :=
  ∀ r w', f c w = .ok (r, w') → post r w'

theorem WP.mono {α : Type} {f : M α} {c : Ctx} {w : W} {post post' : α → W → Prop}
    (hf : WP f c w post) (hp : ∀ r v, post r v → post' r v) : WP f c w post' :=
  fun r v h => hp r v (hf r v h)

theorem wp_pure {α : Type} (r : α) (c : Ctx) (w : W) (post : α → W → Prop) :
    WP (pure r) c w post ↔ post r w := by
  simp [WP, pure, ReaderT.pure, StateT.pure, Except.pure]

theorem wp_throw {α : Type} (e : String) (c : Ctx) (w : W) (post : α → W → Prop) :
    WP (throw e) c w post := by
  simp [WP, throw, throwThe, MonadExceptOf.throw, liftM, monadLift,
    MonadLift.monadLift, StateT.lift, bind, Except.bind]

theorem wp_bind {α β : Type} (f : M α) (g : α → M β) (c : Ctx) (w : W) (post : β → W → Prop) :
    WP (f >>= g) c w post ↔ WP f c w (fun a w' => WP (g a) c w' post) := by
  unfold WP
  simp only [bind, ReaderT.bind, StateT.bind]
  cases hf : f c w with
  | error e => simp [Except.bind]
  | ok aw => cases aw; simp [Except.bind]

theorem wp_read (c : Ctx) (w : W) (post : Ctx → W → Prop) :
    WP read c w post ↔ post c w := by
  simp [WP, read, readThe, MonadReaderOf.read, ReaderT.read, pure,
    StateT.pure, Except.pure]

theorem wp_get (c : Ctx) (w : W) (post : W → W → Prop) :
    WP (MonadState.get : M W) c w post ↔ post w w := by
  simp [WP, MonadState.get, getThe, MonadStateOf.get, StateT.get, liftM,
    monadLift, MonadLift.monadLift, pure, Except.pure]

theorem wp_set (v : W) (c : Ctx) (w : W) (post : Unit → W → Prop) :
    WP (set v) c w post ↔ post () v := by
  simp [WP, set, MonadStateOf.set, StateT.set, liftM,
    monadLift, MonadLift.monadLift, pure, Except.pure]
  constructor
  · intro h; exact h ()
  · intro h r; cases r; exact h

theorem wp_modify (f : W → W) (c : Ctx) (w : W) (post : Unit → W → Prop) :
    WP (modify f) c w post ↔ post () (f w) := by
  simp [WP, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
    monadLift, MonadLift.monadLift, pure, Except.pure]
  constructor
  · intro h; exact h ()
  · intro h r; cases r; exact h

theorem wp_ite {α : Type} (b : Prop) [Decidable b] (f g : M α) (c : Ctx) (w : W)
    (post : α → W → Prop) (ht : b → WP f c w post) (hf : ¬ b → WP g c w post) :
    WP (if b then f else g) c w post := by
  by_cases h : b
  · simpa [h] using ht h
  · simpa [h] using hf h

end Contract
