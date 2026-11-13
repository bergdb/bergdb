/-
The heights walked through the writer (bergdb 024-22, step 4; TP7's (b)): the
primitive steps, with the books.
-/
import SIS.Tree.WriterHeightsRules

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

section Steps

variable (B : NodeId)

/-- A step that keeps the books and the walk's state, the path and the nodes
taken back. -/
def HtKeeps {α : Type} (f : M α) : Prop :=
  ∀ c w, ViewHtOK B c → Book B c w → HtInv B c w →
    WriterWP f c w (fun _ v => Book B c v ∧ HtInv B c v ∧ Kept w v ∧ v.path = w.path ∧
      v.taken = w.taken)

/-- Every field that the walk reads is kept. -/
def HtFrame {α : Type} (f : M α) : Prop :=
  ∀ c w, WriterWP f c w (fun _ v => v.nodes = w.nodes ∧ v.gh = w.gh ∧ v.path = w.path ∧
    v.taken = w.taken ∧ v.top.rootKey = w.top.rootKey)

theorem ht_keeps_of_frame {α : Type} {f : M α} (hbk : KeepsBook B f) (hf : HtFrame f) :
    HtKeeps B f := by
  intro c w hvo hb hi
  refine writerWP_mono (writerWP_and (hbk c w hvo.ids hb) (hf c w)) ?_
  rintro _ v ⟨⟨hb', hk'⟩, hn, hg, hp, ht, htop⟩
  exact ⟨hb', hi.frame v hn hg hp ht htop, hk', hp, ht⟩

theorem ht_writerWP {α : Type} {f : M α} (hf : HtKeeps B f) (c : Ctx) (w : W)
    (post : α → W → Prop) (hvo : ViewHtOK B c) (hb : Book B c w) (hi : HtInv B c w)
    (hp : ∀ r v, Book B c v → HtInv B c v → Kept w v → v.path = w.path → v.taken = w.taken →
      post r v) : WriterWP f c w post :=
  writerWP_mono (hf c w hvo hb hi) (fun r v h => hp r v h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2)

theorem ht_throw {α : Type} (e : String) : HtKeeps B (throw e : M α) := by
  intro c w _ _ _
  exact writerWP_throw _ _ _ _

macro "htFrameTac" : tactic => `(tactic| (
  intro c w
  repeat' first
    | (simp only [writerWP_bind, writerWP_get, writerWP_set, writerWP_pure, writerWP_modify,
        writerWP_read])
    | split
    | exact writerWP_throw _ _ _ _
    | trivial
    | (refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl)))

theorem htFrame_note (s : String) : HtFrame (note s) := by unfold note; htFrameTac
theorem htFrame_fresh : HtFrame fresh := by unfold fresh; htFrameTac
theorem htFrame_newValue (h : Nat) : HtFrame (newValue h) := by unfold newValue fresh; htFrameTac
theorem htFrame_setMadeFor (m : NodeId) (o : Option NodeId) : HtFrame (setMadeFor m o) := by
  unfold setMadeFor; htFrameTac

theorem ht_note (s : String) : HtKeeps B (note s) :=
  ht_keeps_of_frame B (book_note B s) (htFrame_note s)
theorem ht_fresh : HtKeeps B fresh := ht_keeps_of_frame B (book_fresh B) htFrame_fresh

/-- A new value: its id is fresh, so not taken back. -/
theorem ht_newValue (h : Nat) (c : Ctx) (w : W) (hvo : ViewHtOK B c) (hb : Book B c w)
    (hi : HtInv B c w) :
    WriterWP (newValue h) c w (fun x v => Book B c v ∧ HtInv B c v ∧ Kept w v ∧
      v.path = w.path ∧ v.taken = w.taken ∧ x = w.next) := by
  refine writerWP_mono (writerWP_and (book_newValue B h c w hvo.ids hb)
    (writerWP_and (htFrame_newValue h c w)
      (?_ : WriterWP (newValue h) c w (fun x _ => x = w.next)))) ?_
  · unfold newValue fresh
    simp only [writerWP_bind, writerWP_get, writerWP_set, writerWP_pure, writerWP_modify]
  · rintro x v ⟨⟨hb', hk'⟩, ⟨hn, hg, hp, ht, htop⟩, hx⟩
    exact ⟨hb', hi.frame v hn hg hp ht htop, hk', hp, ht, hx⟩

theorem ht_setMadeFor (m : NodeId) (o : Option NodeId) : HtKeeps B (setMadeFor m o) := by
  intro c w hvo hb hi
  refine writerWP_mono (writerWP_and (book_setMadeFor B m o c w hvo.ids hb)
    (htFrame_setMadeFor m o c w)) ?_
  rintro _ v ⟨⟨hb', hk'⟩, hn, hg, hp, ht, htop⟩
  exact ⟨hb', hi.frame v hn hg hp ht htop, hk', hp, ht⟩

/-- The counters of merges and space splits. -/
theorem ht_counter (c : Ctx) (w : W) (f : W → W) (post : Unit → W → Prop)
    (hn : (f w).nodes = w.nodes) (hg : (f w).gh = w.gh) (hp : (f w).path = w.path)
    (ht : (f w).taken = w.taken) (htop : (f w).top.rootKey = w.top.rootKey)
    (hbk : ∀ {c : Ctx} {w : W}, Book B c w → Book B c (f w)) (hb : Book B c w)
    (hi : HtInv B c w)
    (hq : ∀ v, Book B c v → HtInv B c v → Kept w v → v.path = w.path → v.taken = w.taken →
      post () v) :
    WriterWP (modify f) c w post := by
  rw [writerWP_modify]
  exact hq _ (hbk hb) (hi.frame _ hn hg hp ht htop) (Kept.same hn hg) hp ht

/-- The space root: a node not taken back. -/
theorem ht_newSuperRoot (y : NodeId) (c : Ctx) (w : W) (hvo : ViewHtOK B c) (hb : Book B c w)
    (hi : HtInv B c w) (hy : w.taken.contains y = false) :
    WriterWP (newSuperRoot y) c w (fun _ v => Book B c v ∧ HtInv B c v ∧ Kept w v ∧
      v.path = w.path ∧ v.taken = w.taken) := by
  refine writerWP_mono (writerWP_and (book_newSuperRoot B y c w hvo.ids hb)
    (?_ : WriterWP (newSuperRoot y) c w (fun _ v => v.nodes = w.nodes ∧ v.gh = w.gh ∧
      v.path = w.path ∧ v.taken = w.taken ∧ v.top.rootKey = y))) ?_
  · unfold newSuperRoot note fresh
    repeat' first
      | (simp only [writerWP_bind, writerWP_read, writerWP_get, writerWP_set, writerWP_pure,
          writerWP_modify])
      | split
      | (refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl)
  · rintro _ v ⟨⟨hb', hk'⟩, hn, hg, hp, ht, htop⟩
    have h0 : HtInv B c { w with top := { w.top with rootKey := y } } :=
      ⟨hi.cache, hi.path, hi.pathGh, hi.pathFree, hy, hi.takenAbove, hi.pathSome⟩
    exact ⟨hb', h0.frame v hn hg hp ht htop, hk', hp, ht⟩

/-- A read of key node x. -/
theorem ht_getNode (x : NodeId) (c : Ctx) (w : W) (hvo : ViewHtOK B c) (hb : Book B c w)
    (hi : HtInv B c w) :
    WriterWP (getNode x) c w (fun n v => Book B c v ∧ HtInv B c v ∧ Kept w v ∧
      v.nodes.lookup x = some n ∧ v.path = w.path ∧ v.taken = w.taken) := by
  refine writerWP_mono (writerWP_and (book_getNode B x c w hvo.ids hb)
    (?_ : WriterWP (getNode x) c w (fun _ v => HtInv B c v ∧ v.path = w.path ∧
      v.taken = w.taken))) ?_
  · unfold getNode
    simp only [writerWP_bind, writerWP_get]
    split
    · simp only [writerWP_pure]
      exact ⟨hi, by trivial, by trivial⟩
    · rename_i hn
      simp only [writerWP_bind, writerWP_read]
      split
      · rename_i nd hnd
        split
        · exact writerWP_throw _ _ _ _
        · rename_i hkind
          have hd : nd.isData = false := by cases hd : nd.isData <;> simp_all
          have hlv : nd.level ≤ c.p.keyMax := by
            have hh : ¬ c.p.keyMax < nd.level := by
              intro h; simp [h] at hkind
            omega
          simp only [writerWP_bind, writerWP_set, writerWP_pure]
          exact ⟨HtInv.load hb hvo hi x nd hnd hd hlv hn _ rfl rfl rfl rfl rfl, by trivial, by trivial⟩
      · exact writerWP_throw _ _ _ _
  · rintro n v ⟨⟨hb', hk', hl⟩, hi', hp, ht⟩
    exact ⟨hb', hi', hk', hl, hp, ht⟩

/-- The segment and the height of key node x. -/
theorem ht_ghOf (x : NodeId) (c : Ctx) (w : W) (hvo : ViewHtOK B c) (hb : Book B c w)
    (hi : HtInv B c w) :
    WriterWP (ghOf x) c w (fun r v => Book B c v ∧ HtInv B c v ∧ Kept w v ∧
      v.path = w.path ∧ v.taken = w.taken ∧ (x, r.1, r.2) ∈ v.gh ∧
      ∃ n, v.nodes.lookup x = some n ∧ n.leaf = (r.2 == 0)) := by
  unfold ghOf
  simp only [writerWP_bind]
  refine writerWP_mono (ht_getNode B x c w hvo hb hi) ?_
  rintro n v ⟨hb', hi', hle, hl, hp, ht⟩
  simp only [writerWP_get]
  split
  · rename_i r hr
    simp only [writerWP_pure]
    have hmem := bk_mem_of_lookup _ _ _ hr
    exact ⟨hb', hi', hle, hp, ht, hmem, n, hl, kd_leaf hb' hl hmem⟩
  · exact writerWP_throw _ _ _ _

/-- A store of key node x of the overlay, meeting `NodeHt` for its height. -/
theorem ht_putNode (x : NodeId) (n' : KNode) (c : Ctx) (w : W) (hb : Book B c w)
    (hi : HtInv B c w) (n0 : KNode) (hl : w.nodes.lookup x = some n0)
    (hleaf : n'.leaf = n0.leaf)
    (hks : ∀ g h, (x, g, h) ∈ w.gh → w.taken.contains x = false → NodeHt c w h n') :
    WriterWP (putNode x n') c w (fun _ v => Book B c v ∧ HtInv B c v ∧ Kept w v ∧
      v.path = w.path ∧ v.taken = w.taken ∧ v.nodes.lookup x = some n') := by
  refine writerWP_mono (writerWP_and (book_putNode B x n' c w hb ⟨n0, hl, hleaf⟩)
    (?_ : WriterWP (putNode x n') c w (fun _ v => HtInv B c v ∧ v.path = w.path ∧
      v.taken = w.taken ∧ v.nodes.lookup x = some n'))) ?_
  · simp only [putNode, writerWP_modify]
    refine ⟨HtInv.store hi x n' n0 hl hks _ rfl rfl rfl rfl rfl, by trivial, by trivial, ?_⟩
    show (upsert w.nodes x n').lookup x = some n'
    rw [bk_lookup_upsert _ x x n' n0 hl]
    simp
  · rintro _ v ⟨⟨hb', hk'⟩, hi', hp, ht, hlk⟩
    exact ⟨hb', hi', hk', hp, ht, hlk⟩

/-- A new key node meeting `NodeHt` for its height. -/
theorem ht_newKey (g h : Nat) (leaf : Bool) (ks : List Klong) (c : Ctx) (w : W)
    (hb : Book B c w) (hi : HtInv B c w) (hleaf : leaf = (h == 0))
    (hks : NodeHt c w h ⟨leaf, ks⟩) :
    WriterWP (newKey g h leaf ks) c w (fun x v => Book B c v ∧ HtInv B c v ∧ Kept w v ∧
      v.path = w.path ∧ v.taken = w.taken ∧ v.nodes.lookup x = some ⟨leaf, ks⟩ ∧
      (x, g, h) ∈ v.gh ∧ x = w.next ∧ x ∉ w.gh.map (·.1)) := by
  have hxg := kd_next_not hb
  refine writerWP_mono (writerWP_and (book_newKey B g h leaf ks c w hb hleaf)
    (?_ : WriterWP (newKey g h leaf ks) c w (fun x v => HtInv B c v ∧
      v.path = w.path ∧ v.taken = w.taken ∧ (x, g, h) ∈ v.gh ∧ x = w.next))) ?_
  · unfold newKey fresh
    simp only [writerWP_bind, writerWP_read, writerWP_get, writerWP_set, writerWP_pure]
    split
    · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
      refine ⟨HtInv.create hb hi g h ⟨leaf, ks⟩ hks _ ?_ ?_ ?_ ?_ ?_, ?_⟩
      all_goals first | rfl | simp
    · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
      refine ⟨HtInv.create hb hi g h ⟨leaf, ks⟩ hks _ ?_ ?_ ?_ ?_ ?_, ?_⟩
      all_goals first | rfl | simp
  · rintro x v ⟨⟨hb', hk', hlk⟩, hi', hp, ht, hg, hx⟩
    exact ⟨hb', hi', hk', hp, ht, hlk, hg, hx, by rw [hx]; exact hxg⟩

theorem ht_pathClear (c : Ctx) (w : W) (hvo : ViewHtOK B c) (hb : Book B c w)
    (hi : HtInv B c w) :
    WriterWP pathClear c w (fun _ v => Book B c v ∧ HtInv B c v ∧ Kept w v ∧
      v.path = [] ∧ v.taken = w.taken) := by
  refine writerWP_mono (writerWP_and (book_pathClear B c w hvo.ids hb)
    (?_ : WriterWP pathClear c w (fun _ v => v.nodes = w.nodes ∧ v.gh = w.gh ∧
      v.path = [] ∧ v.taken = w.taken ∧ v.top.rootKey = w.top.rootKey))) ?_
  · simp only [pathClear, writerWP_modify]
    exact ⟨by trivial, by trivial, by trivial, by trivial, by trivial⟩
  · rintro _ v ⟨⟨hb', hk'⟩, hn, hg, hp, ht, htop⟩
    exact ⟨hb', hi.clear v hn hg hp ht htop, hk', hp, ht⟩

/-- The space root starts an empty key access path. -/
theorem ht_findRoot (c : Ctx) (w : W) (hvo : ViewHtOK B c) (hb : Book B c w)
    (hi : HtInv B c w) (hp0 : w.path = []) :
    WriterWP findRoot c w (fun r v => Book B c v ∧ HtInv B c v ∧ Kept w v ∧
      v.path = [(none, r)] ∧ v.taken = w.taken) := by
  refine writerWP_mono (writerWP_and (book_findRoot B c w hvo.ids hb)
    (?_ : WriterWP findRoot c w (fun r v => v.nodes = w.nodes ∧ v.gh = w.gh ∧
      v.path = [(none, r)] ∧ v.taken = w.taken ∧ v.top.rootKey = w.top.rootKey ∧
      r = w.top.rootKey))) ?_
  · simp only [findRoot, pathAdd, writerWP_bind, writerWP_get, writerWP_modify, writerWP_pure]
    simp [hp0]
  · rintro r v ⟨⟨hb', hk'⟩, hn, hg, hp, ht, htop, hr⟩
    have h0 : HtInv B c { w with path := [(none, r)] } := by
      refine ⟨hi.cache, ?_, ?_, ?_, hi.rootFree, hi.takenAbove, ?_⟩
      · intro d a q cv y h1 h2
        have := (List.getElem?_eq_some_iff.mp h2).1
        simp at this
      · intro d a q h1 h2
        simp at h2
      · intro d a q h1
        have hd := (List.getElem?_eq_some_iff.mp h1).1
        simp only [List.length_singleton] at hd
        have : d = 0 := by omega
        subst this
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h1
        rw [← h1.2, hr]
        exact hi.rootFree
      · intro d a q h1
        have := (List.getElem?_eq_some_iff.mp h1).1
        simp at this
    exact ⟨hb', h0.frame v hn hg hp ht htop, hk', hp, ht⟩

/-- A node added to the key access path after its last node q, by a live klong
of q, with q's overlay node n. -/
theorem ht_pathAdd (cv : Nat) (y : NodeId) (c : Ctx) (w : W) (hvo : ViewHtOK B c)
    (hb : Book B c w) (hi : HtInv B c w) (a : Option Nat) (q : NodeId) (n : KNode)
    (hlast : w.path.getLast? = some (a, q)) (hq : w.nodes.lookup q = some n)
    (hlive : (cv, y) ∈ n.live) :
    WriterWP (pathAdd (some cv) y) c w (fun _ v => Book B c v ∧ HtInv B c v ∧ Kept w v ∧
      v.path = w.path ++ [(some cv, y)] ∧ v.taken = w.taken) := by
  have hqf : w.taken.contains q = false := by
    have hL : w.path ≠ [] := by intro h; rw [h] at hlast; simp at hlast
    rw [List.getLast?_eq_getElem?] at hlast
    exact hi.pathFree _ a q hlast
  obtain ⟨g0, h0, hm0⟩ := kd_tag_of_lookup hb hq
  have hN := hi.cache q n g0 h0 (bk_mem_of_lookup _ _ _ hq) hm0 hqf
  refine writerWP_mono (writerWP_and (book_pathAdd B (some cv) y c w hvo.ids hb)
    (?_ : WriterWP (pathAdd (some cv) y) c w (fun _ v => HtInv B c v ∧
      v.path = w.path ++ [(some cv, y)] ∧ v.taken = w.taken))) ?_
  · simp only [pathAdd, writerWP_modify]
    refine ⟨HtInv.add hi cv y (hN.1 cv y hlive).1 ?_ _ rfl rfl rfl rfl rfl, by trivial, by trivial⟩
    intro a' q' hl'
    rw [hlast] at hl'
    simp only [Option.some.injEq, Prod.mk.injEq] at hl'
    obtain ⟨rfl, rfl⟩ := hl'
    refine ⟨ht_mem_ids hm0, fun g h hg _ hh => ?_⟩
    obtain ⟨rfl, rfl⟩ := kd_tag_eq hb hm0 hg
    exact (hN.1 cv y hlive).2 hh
  · rintro _ v ⟨⟨hb', hk'⟩, hi', hp, ht⟩
    exact ⟨hb', hi', hk', hp, ht⟩

end Steps

end SIS.Tree
