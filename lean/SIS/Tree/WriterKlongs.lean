import SIS.Tree.FlatKlongs
import SIS.Tree.WriterStateInvariant

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- Physical histories of the key nodes available to the writer. -/
def ViewKlongsWf (p : Params) (view : View BVal) : Prop :=
  ∀ x nd, view x = some nd → nd.isData = false → nd.level ≤ p.keyMax →
    klongsWf (klongsOf nd.hist) = true

def WriterKlongsWf (w : W) : Prop := ∀ q ∈ w.nodes, klongsWf q.2.ks = true

def KeepsKlongsWf {α : Type} (f : M α) : Prop :=
  ∀ c w, ViewKlongsWf c.p c.view → WriterKlongsWf w →
    WriterWP f c w (fun _ v => WriterKlongsWf v)

theorem writerKlongsWf_lookup (w : W) (hw : WriterKlongsWf w) (x : NodeId) (n : KNode)
    (hn : w.nodes.lookup x = some n) : klongsWf n.ks = true := by
  obtain ⟨pre, post, he, _⟩ := List.lookup_eq_some_iff.mp hn
  apply hw (x, n)
  rw [he]
  simp

theorem klongsWf_getNode (x : NodeId) (c : Ctx) (w : W)
    (hv : ViewKlongsWf c.p c.view) (hw : WriterKlongsWf w) :
    WriterWP (getNode x) c w (fun n v => WriterKlongsWf v ∧ klongsWf n.ks = true) := by
  unfold getNode
  simp only [writerWP_bind, writerWP_get]
  split
  · rename_i n hn
    simp only [writerWP_pure]
    exact ⟨hw, writerKlongsWf_lookup w hw x n hn⟩
  · simp only [writerWP_bind, writerWP_read]
    split
    · rename_i nd hn
      split
      · exact writerWP_throw _ _ _ _
      · rename_i hkind
        have hd : nd.isData = false := by cases hd : nd.isData <;> simp_all
        have hl : nd.level ≤ c.p.keyMax := by
          have hh : ¬ c.p.keyMax < nd.level := by
            intro h; simp [h] at hkind
          omega
        have hks := hv x nd hn hd hl
        simp only [writerWP_bind, writerWP_set, writerWP_pure]
        refine ⟨?_, hks⟩
        intro q hq
        rcases List.mem_append.mp hq with hq | hq
        · exact hw q hq
        · have heq := List.mem_singleton.mp hq
          subst q
          exact hks
    · exact writerWP_throw _ _ _ _

theorem klongsWf_putNode (x : NodeId) (n : KNode) (hn : klongsWf n.ks = true) :
    KeepsKlongsWf (putNode x n) := by
  intro c w _ hw
  simp only [putNode, writerWP_modify]
  intro q hq
  unfold upsert at hq
  split at hq
  · obtain ⟨a, ha, he⟩ := List.mem_map.mp hq
    split at he
    · cases he; exact hn
    · cases he; exact hw _ ha
  · rcases List.mem_append.mp hq with hq | hq
    · exact hw q hq
    · have he := List.mem_singleton.mp hq
      subst q; exact hn

theorem klongsWf_newKey (g h : Nat) (leaf : Bool) (ks : List Klong)
    (hks : klongsWf ks = true) : KeepsKlongsWf (newKey g h leaf ks) := by
  intro c w _ hw
  unfold newKey fresh
  wpSimplify
  split <;> wpSimplify
  all_goals
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hw q hq
    · have he := List.mem_singleton.mp hq
      subst q; exact hks

theorem klongsWf_fresh : KeepsKlongsWf fresh := by
  intro c w _ hw
  unfold fresh
  wpSimplify
  exact hw

theorem klongsWf_note (s : String) : KeepsKlongsWf (note s) := by
  intro c w _ hw
  simp only [note, writerWP_modify]
  exact hw

theorem klongsWf_takenBack (x : NodeId) : KeepsKlongsWf (takenBack x) := by
  intro c w _ hw
  simp only [takenBack, writerWP_modify]
  exact hw

theorem klongsWf_pathClear : KeepsKlongsWf pathClear := by
  intro c w _ hw
  simp only [pathClear, writerWP_modify]
  exact hw

theorem klongsWf_pathAdd (cv : Option Nat) (x : NodeId) : KeepsKlongsWf (pathAdd cv x) := by
  intro c w _ hw
  simp only [pathAdd, writerWP_modify]
  exact hw

theorem klongsWf_setMadeFor (x : NodeId) (old : Option NodeId) :
    KeepsKlongsWf (setMadeFor x old) := by
  intro c w _ hw
  unfold setMadeFor
  split
  · simp only [writerWP_modify]; exact hw
  · simpa only [writerWP_pure] using hw

theorem klongsWf_newValue (h : Nat) : KeepsKlongsWf (newValue h) := by
  intro c w _ hw
  unfold newValue fresh
  wpSimplify
  exact hw

theorem klongsWf_newSuperRoot (x : NodeId) : KeepsKlongsWf (newSuperRoot x) := by
  intro c w _ hw
  unfold newSuperRoot note fresh
  wpSimplify
  split <;> wpSimplify <;> exact hw

theorem writerWP_of_klongsWf {α : Type} {f : M α} (hf : KeepsKlongsWf f)
    (c : Ctx) (w : W) (post : α → W → Prop) (hv : ViewKlongsWf c.p c.view)
    (hw : WriterKlongsWf w) (hp : ∀ r v, WriterKlongsWf v → post r v) :
    WriterWP f c w post := writerWP_mono (hf c w hv hw) hp

macro "kwUse " h:term : tactic => `(tactic| (
  (with_unfolding_none refine writerWP_of_klongsWf $h _ _ _ ?kwView ?kwState ?kwPost)
  case kwView => assumption
  case kwState => assumption
  intro _ _ _))

macro "kwNode" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (getNode _) _ _ _)
  (refine writerWP_mono (klongsWf_getNode _ _ _ ?kwView ?kwState) ?kwPost)
  case kwView => assumption
  case kwState => assumption
  rintro _ _ ⟨_, _⟩))

macro "kwNeutral" : tactic => `(tactic| (
  intro c w hv hw
  repeat' first
    | wpSimplify
    | kwNode
    | exact writerWP_throw _ _ _ _
    | split
    | assumption
    | contradiction))

theorem klongsWf_ghOf (x : NodeId) : KeepsKlongsWf (ghOf x) := by unfold ghOf; kwNeutral
theorem klongsWf_replacedBy (x : NodeId) : KeepsKlongsWf (replacedBy x) := by unfold replacedBy; kwNeutral
theorem klongsWf_pathSize : KeepsKlongsWf pathSize := by unfold pathSize; kwNeutral
theorem klongsWf_pathNode (d : Nat) : KeepsKlongsWf (pathNode d) := by unfold pathNode; kwNeutral
theorem klongsWf_klongAt (d : Nat) : KeepsKlongsWf (klongAt d) := by unfold klongAt; kwNeutral

theorem klongsWf_parentAt (d : Nat) : KeepsKlongsWf (parentAt d) := by
  cases d with
  | zero => intro c w hv hw; simpa only [parentAt, writerWP_pure] using hw
  | succ d =>
    intro c w hv hw
    unfold parentAt
    simp only [writerWP_bind]
    kwUse (klongsWf_pathNode _)
    simpa only [writerWP_pure] using ‹WriterKlongsWf _›

theorem klongsWf_findRoot : KeepsKlongsWf findRoot := by
  intro c w hv hw
  unfold findRoot
  wpSimplify
  exact klongsWf_pathAdd none _ c w hv hw

syntax "kwKs" : tactic
macro_rules
  | `(tactic| kwKs) => `(tactic| first
    | assumption
    | ((with_unfolding_none guard_target = klongsWf [] = true)
       rfl)
    | ((with_unfolding_none guard_target = klongsWf (newKlongs _ _) = true)
       exact klongsWf_newKlongs _ _)
    | ((with_unfolding_none guard_target = klongsWf [.time _, .key _ _, .key _ _] = true)
       exact klongsWf_newKlongs _ [(_, _), (_, _)])
    | ((with_unfolding_none guard_target = klongsWf (KNode.add _ _ (.key _ _)).ks = true)
       apply KNode.add_key_wf; kwKs)
    | ((with_unfolding_none guard_target = klongsWf (KNode.repoint _ _ _).ks = true)
       rw [KNode.repoint_klongsWf]; kwKs)
    | ((with_unfolding_none guard_target = klongsWf (KNode.toPrev _ _).ks = true)
       apply KNode.toPrev_wf; kwKs)
    | ((with_unfolding_none guard_target = klongsWf (KNode.lastVersionGivenDel _ _ _).ks = true)
       exact KNode.lastVersionGivenDel_wf _ _ _)
    | ((with_unfolding_none guard_target = klongsWf (halves _ _ _ _).1.ks = true)
       exact (halves_flat_wf _ _ _ _ (by assumption)).1)
    | ((with_unfolding_none guard_target = klongsWf (halves _ _ _ _).2.1.ks = true)
       exact (halves_flat_wf _ _ _ _ (by assumption)).2)
    | ((with_unfolding_none guard_target = klongsWf (retargetKlongs _ _ _ _) = true)
       rw [klongsWf_retargetKlongs]; kwKs)
    | (apply flatKlongs_wf; assumption))

macro "kwStore" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (putNode _ _) _ _ _)
  (with_unfolding_none refine writerWP_of_klongsWf (klongsWf_putNode _ _ ?kwInput) _ _ _ ?kwView ?kwState ?kwPost)
  case kwInput => kwKs
  case kwView => assumption
  case kwState => assumption
  intro _ _ _))

macro "kwCreate" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (newKey _ _ _ _) _ _ _)
  (with_unfolding_none refine writerWP_of_klongsWf (klongsWf_newKey _ _ _ _ ?kwInput) _ _ _ ?kwView ?kwState ?kwPost)
  case kwInput => kwKs
  case kwView => assumption
  case kwState => assumption
  intro _ _ _))

macro "kwCore" : tactic => `(tactic| first
  | kwNode
  | kwStore
  | kwCreate
  | kwUse (klongsWf_pathAdd _ _)
  | kwUse (klongsWf_ghOf _)
  | kwUse (klongsWf_replacedBy _)
  | kwUse klongsWf_pathSize
  | kwUse (klongsWf_pathNode _)
  | kwUse (klongsWf_klongAt _)
  | kwUse (klongsWf_parentAt _)
  | kwUse klongsWf_findRoot
  | kwUse (klongsWf_note _)
  | kwUse klongsWf_fresh
  | kwUse (klongsWf_newValue _)
  | kwUse (klongsWf_newSuperRoot _)
  | kwUse (klongsWf_setMadeFor _ _)
  | kwUse (klongsWf_takenBack _)
  | kwUse klongsWf_pathClear
  | assumption
  | exact writerWP_throw _ _ _ _)

theorem klongsWf_fold_add (n : KNode) (t : Time) (ins : List (Nat × NodeId))
    (hn : klongsWf n.ks = true) :
    klongsWf (ins.foldl (fun n q => n.add t (.key q.1 q.2)) n).ks = true := by
  induction ins generalizing n with
  | nil => exact hn
  | cons q ins ih => exact ih _ (n.add_key_wf t q.1 q.2 hn)

theorem klongsWf_addKeys (x : NodeId) (ins : List (Nat × NodeId)) :
    KeepsKlongsWf (addKeys x ins) := by
  intro c w hv hw
  unfold addKeys
  wpSimplify
  kwNode
  exact klongsWf_putNode _ _ (klongsWf_fold_add _ _ _ (by assumption)) _ _ hv (by assumption)

/-- The time-split overwrite/append loop preserves well-formed klongs for
arbitrary insert lists, and makes no state change. -/
theorem writerWP_replaceOrAdd_wf (last : KNode) (ins : List (Nat × NodeId))
    (hlast : klongsWf last.ks = true) (c : Ctx) (w : W) :
    WriterWP (replaceOrAdd last ins) c w (fun out v => klongsWf out.ks = true ∧ v = w) := by
  unfold replaceOrAdd
  simp only [writerWP_bind, writerWP_read]
  induction ins generalizing last with
  | nil => simp only [List.foldlM_nil, writerWP_pure]; exact ⟨hlast, trivial⟩
  | cons q ins ih =>
    rw [List.foldlM_cons, writerWP_bind]
    cases hr : replaceKlong last.ks c.i q.1 q.2 with
    | error e => exact writerWP_throw _ _ _ _
    | ok result =>
      cases result with
      | none =>
        simp only [writerWP_pure]
        exact ih _ (last.add_key_wf _ _ _ hlast)
      | some ks =>
        simp only [writerWP_pure]
        exact ih {last with ks := ks} (replaceKlong_wf _ _ _ _ _ hlast hr)

macro "kwReplace" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (replaceOrAdd _ _) _ _ _)
  refine writerWP_mono (writerWP_replaceOrAdd_wf _ _ ?kwLast _ _) ?kwPost
  case kwLast => kwKs
  rintro out v ⟨hout, heq⟩
  subst v))

end SIS.Tree
