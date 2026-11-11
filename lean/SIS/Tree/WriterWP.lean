import SIS.Tree.Exec

namespace SIS.Tree

open SIS SIS.Check

/-- Every successful result of an action meets its postcondition. -/
def WriterWP {α : Type} (f : M α) (c : Ctx) (w : W) (post : α → W → Prop) : Prop :=
  ∀ r w', f c w = .ok (r, w') → post r w'

theorem writerWP_mono {α : Type} {f : M α} {c : Ctx} {w : W}
    {post post' : α → W → Prop} (hf : WriterWP f c w post)
    (hp : ∀ r v, post r v → post' r v) : WriterWP f c w post' := by
  intro r v h
  exact hp r v (hf r v h)

theorem writerWP_pure {α : Type} (r : α) (c : Ctx) (w : W) (post : α → W → Prop) :
    WriterWP (pure r) c w post ↔ post r w := by
  simp [WriterWP, pure, ReaderT.pure, StateT.pure, Except.pure]

theorem writerWP_throw {α : Type} (e : String) (c : Ctx) (w : W) (post : α → W → Prop) :
    WriterWP (throw e) c w post := by
  simp [WriterWP, throw, throwThe, MonadExceptOf.throw, liftM, monadLift,
    MonadLift.monadLift, StateT.lift, bind, Except.bind]

theorem writerWP_bind {α β : Type} (f : M α) (g : α → M β)
    (c : Ctx) (w : W) (post : β → W → Prop) :
    WriterWP (f >>= g) c w post ↔
      WriterWP f c w (fun a w' => WriterWP (g a) c w' post) := by
  unfold WriterWP
  simp only [bind, ReaderT.bind, StateT.bind]
  cases hf : f c w with
  | error e => simp [Except.bind]
  | ok aw => cases aw; simp [Except.bind]

theorem writerWP_read (c : Ctx) (w : W) (post : Ctx → W → Prop) :
    WriterWP read c w post ↔ post c w := by
  simp [WriterWP, read, readThe, MonadReaderOf.read, ReaderT.read, pure,
    StateT.pure, Except.pure]

theorem writerWP_get (c : Ctx) (w : W) (post : W → W → Prop) :
    WriterWP get c w post ↔ post w w := by
  simp [WriterWP, get, getThe, MonadStateOf.get, StateT.get, liftM,
    monadLift, MonadLift.monadLift, pure, Except.pure]

theorem writerWP_set (v : W) (c : Ctx) (w : W) (post : Unit → W → Prop) :
    WriterWP (set v) c w post ↔ post () v := by
  simp [WriterWP, set, MonadStateOf.set, StateT.set, liftM,
    monadLift, MonadLift.monadLift, pure, Except.pure]
  constructor
  · intro h; exact h ()
  · intro h r; cases r; exact h

theorem writerWP_modify (f : W → W) (c : Ctx) (w : W) (post : Unit → W → Prop) :
    WriterWP (modify f) c w post ↔ post () (f w) := by
  simp [WriterWP, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
    monadLift, MonadLift.monadLift, pure, Except.pure]
  constructor
  · intro h; exact h ()
  · intro h r; cases r; exact h

theorem writerWP_if {α : Type} (b : Prop) [Decidable b] (f g : M α)
    (c : Ctx) (w : W) (post : α → W → Prop)
    (ht : b → WriterWP f c w post) (hf : ¬ b → WriterWP g c w post) :
    WriterWP (if b then f else g) c w post := by
  by_cases h : b
  · simpa [h] using ht h
  · simpa [h] using hf h

end SIS.Tree
