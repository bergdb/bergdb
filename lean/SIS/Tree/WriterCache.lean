import SIS.Tree.WriterKlongMergeParent

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

theorem writerWP_and {α : Type} {f : M α} {c : Ctx} {w : W}
    {post post' : α → W → Prop} (hf : WriterWP f c w post)
    (hg : WriterWP f c w post') :
    WriterWP f c w (fun r v => post r v ∧ post' r v) :=
  fun r v he => ⟨hf r v he, hg r v he⟩

/-- Cache loads and allocations keep every previously cached lookup. -/
def CacheExtends (before after : W) : Prop :=
  ∀ x n, before.nodes.lookup x = some n → after.nodes.lookup x = some n

def KeepsCache {α : Type} (f : M α) : Prop :=
  ∀ c w, WriterWP f c w (fun _ v => CacheExtends w v)

theorem cacheExtends_refl (w : W) : CacheExtends w w := by intro x n hn; exact hn

theorem cacheExtends_append (w : W) (ns : List (NodeId × KNode))
    (v : W) (he : v.nodes = w.nodes ++ ns) : CacheExtends w v := by
  intro x n hn
  rw [he, List.lookup_append, hn]
  rfl

theorem writerWP_getNode_extends (x : NodeId) (c : Ctx) (w : W) :
    WriterWP (getNode x) c w (fun n v => CacheExtends w v ∧ v.nodes.lookup x = some n) := by
  unfold getNode
  simp only [writerWP_bind, writerWP_get]
  split
  · rename_i n hn
    simp only [writerWP_pure]
    exact ⟨cacheExtends_refl w, hn⟩
  · rename_i hn
    simp only [writerWP_bind, writerWP_read]
    split
    · split
      · exact writerWP_throw _ _ _ _
      · simp only [writerWP_bind, writerWP_set, writerWP_pure]
        refine ⟨cacheExtends_append _ _ _ rfl, ?_⟩
        change (w.nodes ++ [(x, _)]).lookup x = _
        simp [List.lookup_append, hn]
    · exact writerWP_throw _ _ _ _

theorem cache_getNode (x : NodeId) : KeepsCache (getNode x) :=
  fun c w => writerWP_mono (writerWP_getNode_extends x c w) (fun _ _ h => h.1)

theorem cache_note (s : String) : KeepsCache (note s) := by
  intro c w
  simp only [note, writerWP_modify]
  exact cacheExtends_refl w

theorem cache_setMadeFor (x : NodeId) (old : Option NodeId) : KeepsCache (setMadeFor x old) := by
  intro c w
  unfold setMadeFor
  split
  · simp only [writerWP_modify]; exact cacheExtends_refl w
  · simp only [writerWP_pure]; exact cacheExtends_refl w

theorem cache_newKey (g h : Nat) (leaf : Bool) (ks : List Klong) :
    KeepsCache (newKey g h leaf ks) := by
  intro c w
  unfold newKey fresh
  wpSimplify
  split <;> wpSimplify <;> exact cacheExtends_append _ _ _ rfl

theorem writerWP_of_cache {α : Type} {f : M α} (hf : KeepsCache f)
    (c : Ctx) (w : W) (post : α → W → Prop)
    (hp : ∀ r v, CacheExtends w v → post r v) : WriterWP f c w post :=
  writerWP_mono (hf c w) hp

macro "cacheUse " h:term : tactic => `(tactic| (
  (with_unfolding_none refine writerWP_of_cache $h _ _ _ ?cachePost)
  intro _ _ _))

macro "cacheFinish" : tactic => `(tactic| (
  intro x n hn
  repeat' first
    | assumption
    | (apply_assumption; assumption)))

theorem cache_ghOf (x : NodeId) : KeepsCache (ghOf x) := by
  intro c w
  unfold ghOf
  repeat' first
    | wpSimplify
    | cacheUse (cache_getNode _)
    | exact writerWP_throw _ _ _ _
    | split
    | cacheFinish

theorem cache_pathNode (d : Nat) : KeepsCache (pathNode d) := by
  intro c w
  unfold pathNode
  repeat' first
    | wpSimplify
    | exact writerWP_throw _ _ _ _
    | split
    | exact cacheExtends_refl w

theorem cache_klongAt (d : Nat) : KeepsCache (klongAt d) := by
  intro c w
  unfold klongAt
  repeat' first
    | wpSimplify
    | exact writerWP_throw _ _ _ _
    | split
    | exact cacheExtends_refl w

theorem cache_replacedBy (x : NodeId) : KeepsCache (replacedBy x) := by
  intro c w
  unfold replacedBy
  wpSimplify
  exact cacheExtends_refl w

theorem cache_sibling (q : NodeId) (pn : KNode) (i : Nat) (inner : Bool) :
    KeepsCache (sibling q pn i inner) := by
  intro c w
  unfold sibling
  repeat' first
    | wpSimplify
    | cacheUse (cache_getNode _)
    | exact writerWP_throw _ _ _ _
    | wpSplit
    | split
    | cacheFinish

theorem klongsWf_sibling (q : NodeId) (pn : KNode) (i : Nat) (inner : Bool)
    (c : Ctx) (w : W) (hv : ViewKlongsWf c.p c.view) (hw : WriterKlongsWf w) :
    WriterWP (sibling q pn i inner) c w
      (fun result v => WriterKlongsWf v ∧ klongsWf result.2.ks = true) := by
  unfold sibling
  repeat' first
    | wpSimplify
    | kwCore
    | (constructor <;> assumption)
    | wpSplit
    | split
    | contradiction

theorem klongsWf_getNode_caches (x : NodeId) (c : Ctx) (w : W)
    (hv : ViewKlongsWf c.p c.view) (hw : WriterKlongsWf w) :
    WriterWP (getNode x) c w (fun n v => WriterKlongsWf v ∧
      klongsWf n.ks = true ∧ v.nodes.lookup x = some n) := by
  refine writerWP_mono (writerWP_and (klongsWf_getNode x c w hv hw)
    (writerWP_getNode_extends x c w)) ?_
  rintro n v ⟨⟨hkw, hn⟩, _, hcache⟩
  exact ⟨hkw, hn, hcache⟩

theorem klongsWf_getNode_cached (x q : NodeId) (pn : KNode) (c : Ctx) (w : W)
    (hv : ViewKlongsWf c.p c.view) (hw : WriterKlongsWf w)
    (hp : w.nodes.lookup q = some pn) :
    WriterWP (getNode x) c w (fun n v => WriterKlongsWf v ∧
      klongsWf n.ks = true ∧ v.nodes.lookup q = some pn) := by
  refine writerWP_mono (writerWP_and (klongsWf_getNode x c w hv hw)
    (cache_getNode x c w)) ?_
  rintro n v ⟨⟨hkw, hn⟩, hcache⟩
  exact ⟨hkw, hn, hcache q pn hp⟩

theorem klongsWf_sibling_cached (parent : NodeId) (cached : KNode)
    (q : NodeId) (pn : KNode) (i : Nat) (inner : Bool) (c : Ctx) (w : W)
    (hv : ViewKlongsWf c.p c.view) (hw : WriterKlongsWf w)
    (hp : w.nodes.lookup parent = some cached) :
    WriterWP (sibling q pn i inner) c w (fun result v => WriterKlongsWf v ∧
      klongsWf result.2.ks = true ∧ v.nodes.lookup parent = some cached) := by
  refine writerWP_mono (writerWP_and (klongsWf_sibling q pn i inner c w hv hw)
    (cache_sibling q pn i inner c w)) ?_
  rintro result v ⟨⟨hkw, hn⟩, hcache⟩
  exact ⟨hkw, hn, hcache parent cached hp⟩

theorem writerWP_of_klongsWf_cached {α : Type} {f : M α}
    (hf : KeepsKlongsWf f) (hcache : KeepsCache f) (q : NodeId) (pn : KNode)
    (c : Ctx) (w : W) (post : α → W → Prop) (hv : ViewKlongsWf c.p c.view)
    (hw : WriterKlongsWf w) (hp : w.nodes.lookup q = some pn)
    (hpost : ∀ r v, WriterKlongsWf v → v.nodes.lookup q = some pn → post r v) :
    WriterWP f c w post := by
  refine writerWP_mono (writerWP_and (hf c w hv hw) (hcache c w)) ?_
  rintro r v ⟨hkw, hc⟩
  exact hpost r v hkw (hc q pn hp)

end SIS.Tree
