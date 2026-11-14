/-
The writer's tree is a tree between operations (bergdb 024-22 and 024-12, for
TP33's `OpCountOK` and TP10's `OpGetOK`): from the writer's super root, through
its key nodes (`wNode`: its own copies, P's for the others, none for a node it
took back), at the transaction's time, no node is reached twice and nothing
links back to the space root (`WriterTreeOK`). A link is a live klong of a node:
a child of an inner node, the root of the next segment's tree, or a value; so a
value too is named once (the reads' TREE, `GetSplit.lean`'s `htree`).

The same of P between transactions is `TreeAt`. Proved here: the writer's first
state has the tree of P (`writerTreeOK_init`), P after the transaction has the
tree of the writer's last state, given the lift of the writer's key nodes,
and so every run within reach has it if every operation keeps it (`OpTreeOK`)
and the lift holds (TakeBackRun.lean). Every state between operations then has it
(`writerTreeOK_reached`), which `OpCountOK` and `OpGetOK` can take as a premise.
-/
import SIS.Tree.MergeNodeCountOps

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## Trees of key nodes -/

/-- A link at time t through the lookup `look`: the klong of compare value c is
live in key node x and names y (a child of an inner node, the root of the next
segment's tree, or a value). -/
def TLink (look : NodeId → Option KNode) (t : Time) (x : NodeId) (c : Nat) (y : NodeId) : Prop :=
  ∃ n, look x = some n ∧ (c, y) ∈ n.liveAt t

/-- The nodes reached from r by links. -/
inductive TReach (look : NodeId → Option KNode) (t : Time) (r : NodeId) : NodeId → Prop
  | root : TReach look t r r
  | link {x : NodeId} {c : Nat} {y : NodeId} :
      TReach look t r x → TLink look t x c y → TReach look t r y

/-- A tree from r: r is a key node; no node reached links to r; and a node is
named by one link at most of the nodes reached (one node, one klong). -/
structure TreeOK (look : NodeId → Option KNode) (t : Time) (r : NodeId) : Prop where
  rootKey : ∃ n, look r = some n
  rootFree : ∀ x c, TReach look t r x → ¬ TLink look t x c r
  oneLink : ∀ x c x' c' y, TReach look t r x → TReach look t r x' →
    TLink look t x c y → TLink look t x' c' y → x = x' ∧ c = c'

/-- The writer's tree at time t, over P: a tree from its super root's space
root. -/
def WriterTreeOK (p : Params) (P : Struct BVal) (t : Time) (w : W) : Prop :=
  TreeOK (wNode p (viewOf P) w) t w.top.rootKey

/-- P's key nodes at time t make a tree from its space root at t. -/
def TreeAt (p : Params) (P : Struct BVal) (t : Time) : Prop :=
  ∃ r, rootAt (viewOf P) t = some r ∧ TreeOK (knodeOf p (viewOf P)) t r

/-! ## Changing the time -/

theorem tLink_congr_time (look : NodeId → Option KNode) (t t' : Time)
    (h : ∀ x n, look x = some n → n.liveAt t = n.liveAt t') (x : NodeId) (c : Nat) (y : NodeId) :
    TLink look t x c y ↔ TLink look t' x c y := by
  constructor
  · rintro ⟨n, hn, hl⟩
    exact ⟨n, hn, by rw [← h x n hn]; exact hl⟩
  · rintro ⟨n, hn, hl⟩
    exact ⟨n, hn, by rw [h x n hn]; exact hl⟩

theorem tReach_congr_time (look : NodeId → Option KNode) (t t' : Time) (r : NodeId)
    (h : ∀ x n, look x = some n → n.liveAt t = n.liveAt t') (y : NodeId)
    (hy : TReach look t r y) : TReach look t' r y := by
  induction hy with
  | root => exact TReach.root
  | link _ hl ih => exact TReach.link ih ((tLink_congr_time look t t' h _ _ _).mp hl)

theorem treeOK_congr_time (look : NodeId → Option KNode) (t t' : Time) (r : NodeId)
    (h : ∀ x n, look x = some n → n.liveAt t = n.liveAt t') (ht : TreeOK look t r) :
    TreeOK look t' r := by
  have h' : ∀ x n, look x = some n → n.liveAt t' = n.liveAt t :=
    fun x n hx => (h x n hx).symm
  refine ⟨ht.rootKey, ?_, ?_⟩
  · intro x c hx hl
    exact ht.rootFree x c (tReach_congr_time look t' t r h' x hx)
      ((tLink_congr_time look t t' h x c r).mpr hl)
  · intro x c x' c' y hx hx' hl hl'
    exact ht.oneLink x c x' c' y (tReach_congr_time look t' t r h' x hx)
      (tReach_congr_time look t' t r h' x' hx')
      ((tLink_congr_time look t t' h x c y).mpr hl) ((tLink_congr_time look t t' h x' c' y).mpr hl')

/-- The same lookup, the same tree. -/
theorem treeOK_congr_look (look look' : NodeId → Option KNode) (t : Time) (r : NodeId)
    (h : look = look') (ht : TreeOK look t r) : TreeOK look' t r := by
  subst h; exact ht

/-! ## Changes that keep a tree -/

/-- Lookups that agree on the nodes one of them reaches reach the same nodes. -/
theorem tReach_of_agree (L L' : NodeId → Option KNode) (t : Time) (r : NodeId)
    (h : ∀ x, TReach L t r x → L' x = L x) : ∀ y, TReach L' t r y → TReach L t r y := by
  intro y hy
  induction hy with
  | root => exact TReach.root
  | @link x c y _ hl ih =>
    obtain ⟨n, hn, hc⟩ := hl
    rw [h x ih] at hn
    exact TReach.link ih ⟨n, hn, hc⟩

theorem tReach_to_agree (L L' : NodeId → Option KNode) (t : Time) (r : NodeId)
    (h : ∀ x, TReach L t r x → L' x = L x) : ∀ y, TReach L t r y → TReach L' t r y := by
  intro y hy
  induction hy with
  | root => exact TReach.root
  | @link x c y hx hl ih =>
    obtain ⟨n, hn, hc⟩ := hl
    rw [← h x hx] at hn
    exact TReach.link ih ⟨n, hn, hc⟩

/-- A change of nodes that the tree does not reach keeps the tree (a node made
and not yet linked, a node left out, a node read into the cache unchanged). -/
theorem treeOK_of_agree (L L' : NodeId → Option KNode) (t : Time) (r : NodeId)
    (ht : TreeOK L t r) (h : ∀ x, TReach L t r x → L' x = L x) : TreeOK L' t r := by
  have hb := tReach_of_agree L L' t r h
  have hlink : ∀ x c y, TReach L' t r x → TLink L' t x c y → TLink L t x c y := by
    intro x c y hx hl
    obtain ⟨n, hn, hc⟩ := hl
    rw [h x (hb x hx)] at hn
    exact ⟨n, hn, hc⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [h r TReach.root]; exact ht.rootKey
  · intro x c hx hl
    exact ht.rootFree x c (hb x hx) (hlink x c r hx hl)
  · intro x c x' c' y hx hx' hl hl'
    exact ht.oneLink x c x' c' y (hb x hx) (hb x' hx') (hlink x c y hx hl) (hlink x' c' y hx' hl')

/-- A change whose links, from the nodes it reaches, are links of the tree
(maybe of another compare value of the same node), one a node and target,
keeps the tree: a klong deleted, a value added or changed in a segment leaf, the
empty key given the pointer of the next klong (LE-b), a link dropped. -/
theorem treeOK_of_links (L L' : NodeId → Option KNode) (t : Time) (r : NodeId)
    (ht : TreeOK L t r) (hroot : ∃ n, L' r = some n)
    (hsub : ∀ x c y, TReach L' t r x → TLink L' t x c y → ∃ c0, TLink L t x c0 y)
    (hone : ∀ x c c' y, TReach L' t r x → TLink L' t x c y → TLink L' t x c' y → c = c') :
    TreeOK L' t r := by
  have hb : ∀ y, TReach L' t r y → TReach L t r y := by
    intro y hy
    induction hy with
    | root => exact TReach.root
    | @link x c y hx hl ih =>
      obtain ⟨c0, h0⟩ := hsub x c y hx hl
      exact TReach.link ih h0
  refine ⟨hroot, ?_, ?_⟩
  · intro x c hx hl
    obtain ⟨c0, h0⟩ := hsub x c r hx hl
    exact ht.rootFree x c0 (hb x hx) h0
  · intro x c x' c' y hx hx' hl hl'
    obtain ⟨c0, h0⟩ := hsub x c y hx hl
    obtain ⟨c0', h0'⟩ := hsub x' c' y hx' hl'
    have hxx := (ht.oneLink x c0 x' c0' y (hb x hx) (hb x' hx') h0 h0').1
    subst hxx
    exact ⟨rfl, hone x c c' y hx hl hl'⟩

/-- A regrouping below a node x of the tree: the old nodes (reached, each
named by x or by another old node) are replaced by new ones (not reached),
whose links go to new nodes or to nodes that old ones named, but not old; x's
links go to nodes it named that are not old, or to new nodes; every new node is
named once (by x or by a new node). Elsewhere the lookup is unchanged. A split
(a space split and the splits above it), a time split, a merge with its parent's
change: each is one. -/
theorem treeOK_regroup (L L' : NodeId → Option KNode) (t : Time) (r x : NodeId)
    (Old New : NodeId → Prop) (ht : TreeOK L t r) (hx : TReach L t r x) (hxOld : ¬ Old x)
    (hOld : ∀ o, Old o → TReach L t r o ∧ ∃ x0 c, (x0 = x ∨ Old x0) ∧ TLink L t x0 c o)
    (hNew : ∀ z, New z → ¬ TReach L t r z)
    (hsame : ∀ y, y ≠ x → ¬ New y → ¬ Old y → L' y = L y)
    (hxl : ∀ c y, TLink L' t x c y → (TLink L t x c y ∧ ¬ Old y) ∨ New y)
    (hzl : ∀ z c y, New z → TLink L' t z c y →
      New y ∨ ((∃ o c0, Old o ∧ TLink L t o c0 y) ∧ ¬ Old y))
    (hxone : ∀ c c' z, New z → TLink L' t x c z → TLink L' t x c' z → c = c')
    (hzone : ∀ z c z' c' y, New z → New z' → TLink L' t z c y → TLink L' t z' c' y →
      z = z' ∧ c = c')
    (hmix : ∀ c z z' c', New z → New z' → TLink L' t x c z → ¬ TLink L' t z' c' z)
    (hroot : ∃ n, L' r = some n) : TreeOK L' t r := by
  have hxNew : ¬ New x := fun h => hNew x h hx
  -- an old node is named in L only by x or an old node
  have hOldPar : ∀ o y c, Old o → TReach L t r y → TLink L t y c o → y = x ∨ Old y := by
    intro o y c ho hy hl
    obtain ⟨_, x0, c0, hx0, hl0⟩ := hOld o ho
    have hr0 : TReach L t r x0 := by
      rcases hx0 with h | h
      · rw [h]; exact hx
      · exact (hOld x0 h).1
    have := (ht.oneLink y c x0 c0 o hy hr0 hl hl0).1
    rw [this]; exact hx0
  -- what L' reaches
  have hb : ∀ y, TReach L' t r y → (TReach L t r y ∧ ¬ Old y) ∨ New y := by
    intro y hy
    induction hy with
    | root =>
      refine Or.inl ⟨TReach.root, fun ho => ?_⟩
      obtain ⟨_, x0, c0, hx0, hl0⟩ := hOld r ho
      have hr0 : TReach L t r x0 := by
        rcases hx0 with h | h
        · rw [h]; exact hx
        · exact (hOld x0 h).1
      exact ht.rootFree x0 c0 hr0 hl0
    | @link y0 c y _ hl ih =>
      rcases ih with ⟨hy0, hy0o⟩ | hy0n
      · by_cases hyx : y0 = x
        · rw [hyx] at hl
          rcases hxl c y hl with ⟨h, ho⟩ | h
          · exact Or.inl ⟨TReach.link hx h, ho⟩
          · exact Or.inr h
        · have hy0n : ¬ New y0 := fun h => hNew y0 h hy0
          obtain ⟨n, hn, hc⟩ := hl
          rw [hsame y0 hyx hy0n hy0o] at hn
          have hL : TLink L t y0 c y := ⟨n, hn, hc⟩
          refine Or.inl ⟨TReach.link hy0 hL, fun ho => ?_⟩
          rcases hOldPar y y0 c ho hy0 hL with h | h
          · exact hyx h
          · exact hy0o h
      · rcases hzl y0 c y hy0n hl with h | ⟨⟨o, c0, ho, hlo⟩, hyo⟩
        · exact Or.inr h
        · exact Or.inl ⟨TReach.link (hOld o ho).1 hlo, hyo⟩
  -- each link of L' from a node it reaches
  have hcls : ∀ y c v, TReach L' t r y → TLink L' t y c v →
      (y = x ∧ TLink L t x c v ∧ ¬ Old v) ∨ (y = x ∧ New v) ∨ (New y ∧ New v) ∨
      (New y ∧ ∃ o c0, Old o ∧ TLink L t o c0 v ∧ ¬ Old v) ∨
      (TReach L t r y ∧ ¬ Old y ∧ y ≠ x ∧ TLink L t y c v) := by
    intro y c v hy hl
    by_cases hyx : y = x
    · rw [hyx] at hl
      rcases hxl c v hl with ⟨h, ho⟩ | h
      · exact Or.inl ⟨hyx, h, ho⟩
      · exact Or.inr (Or.inl ⟨hyx, h⟩)
    · rcases hb y hy with ⟨hyL, hyo⟩ | hyn
      · have hy0n : ¬ New y := fun h => hNew y h hyL
        obtain ⟨n, hn, hc⟩ := hl
        rw [hsame y hyx hy0n hyo] at hn
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hyL, hyo, hyx, n, hn, hc⟩)))
      · rcases hzl y c v hyn hl with h | ⟨⟨o, c0, ho, hlo⟩, hvo⟩
        · exact Or.inr (Or.inr (Or.inl ⟨hyn, h⟩))
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hyn, o, c0, ho, hlo, hvo⟩)))
  refine ⟨hroot, ?_, ?_⟩
  · intro y c hy hl
    have hrL : TReach L t r r := TReach.root
    rcases hcls y c r hy hl with ⟨_, h, _⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, o, c0, ho, hlo, _⟩ |
        ⟨hyL, _, _, h⟩
    · exact ht.rootFree x c hx h
    · exact hNew r h hrL
    · exact hNew r h hrL
    · exact ht.rootFree o c0 (hOld o ho).1 hlo
    · exact ht.rootFree y c hyL h
  · intro y1 c1 y2 c2 v hy1 hy2 hl1 hl2
    have hc1 := hcls y1 c1 v hy1 hl1
    have hc2 := hcls y2 c2 v hy2 hl2
    -- a new target is named once
    by_cases hvn : New v
    · have hnotL : ∀ y c, TReach L t r y → ¬ TLink L t y c v :=
        fun y c hy hl => hNew v hvn (TReach.link hy hl)
      rcases hc1 with ⟨h1x, h1, _⟩ | ⟨h1x, _⟩ | ⟨h1n, _⟩ | ⟨_, o, c0, ho, hlo, _⟩ | ⟨h1L, _, _, h1⟩
      · exact absurd h1 (hnotL x c1 hx)
      · rcases hc2 with ⟨h2x, h2, _⟩ | ⟨h2x, _⟩ | ⟨h2n, _⟩ | ⟨_, o, c0, ho, hlo, _⟩ |
            ⟨h2L, _, _, h2⟩
        · exact absurd h2 (hnotL x c2 hx)
        · subst h1x; subst h2x
          exact ⟨rfl, hxone c1 c2 v hvn hl1 hl2⟩
        · subst h1x
          exact absurd hl2 (hmix c1 v y2 c2 hvn h2n hl1)
        · exact absurd hlo (hnotL o c0 (hOld o ho).1)
        · exact absurd h2 (hnotL y2 c2 h2L)
      · rcases hc2 with ⟨h2x, h2, _⟩ | ⟨h2x, _⟩ | ⟨h2n, _⟩ | ⟨_, o, c0, ho, hlo, _⟩ |
            ⟨h2L, _, _, h2⟩
        · exact absurd h2 (hnotL x c2 hx)
        · subst h2x
          exact absurd hl1 (hmix c2 v y1 c1 hvn h1n hl2)
        · exact hzone y1 c1 y2 c2 v h1n h2n hl1 hl2
        · exact absurd hlo (hnotL o c0 (hOld o ho).1)
        · exact absurd h2 (hnotL y2 c2 h2L)
      · exact absurd hlo (hnotL o c0 (hOld o ho).1)
      · exact absurd h1 (hnotL y1 c1 h1L)
    · -- an old target: the links of L under the links of L'
      have hsrc : ∀ y c, TReach L' t r y → TLink L' t y c v →
          (New y ∧ ∃ o c0, Old o ∧ TLink L t o c0 v) ∨ (TReach L t r y ∧ ¬ Old y ∧ TLink L t y c v) := by
        intro y c hy hl
        rcases hcls y c v hy hl with ⟨h1x, h1, _⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨h1n, o, c0, ho, hlo, _⟩ |
            ⟨h1L, h1o, _, h1⟩
        · rw [h1x]; exact Or.inr ⟨hx, hxOld, h1⟩
        · exact absurd h hvn
        · exact absurd h hvn
        · exact Or.inl ⟨h1n, o, c0, ho, hlo⟩
        · exact Or.inr ⟨h1L, h1o, h1⟩
      rcases hsrc y1 c1 hy1 hl1 with ⟨h1n, o1, c01, ho1, hlo1⟩ | ⟨h1L, h1o, h1⟩ <;>
        rcases hsrc y2 c2 hy2 hl2 with ⟨h2n, o2, c02, ho2, hlo2⟩ | ⟨h2L, h2o, h2⟩
      · exact hzone y1 c1 y2 c2 v h1n h2n hl1 hl2
      · have := (ht.oneLink o1 c01 y2 c2 v (hOld o1 ho1).1 h2L hlo1 h2).1
        rw [this] at ho1
        exact absurd ho1 h2o
      · have := (ht.oneLink y1 c1 o2 c02 v h1L (hOld o2 ho2).1 h1 hlo2).1
        rw [← this] at ho2
        exact absurd ho2 h1o
      · exact ht.oneLink y1 c1 y2 c2 v h1L h2L h1 h2

/-- A tree is kept, with nodes left behind, when the links of the new lookup from
the nodes of the old tree that are not left behind, and from new nodes, name new
nodes or are transfers of old links to nodes not left behind. So the nodes left
behind (a node replaced by a split, or merged) are reached no more, whatever
their links. -/
theorem treeOK_transfer_gone (L L' : NodeId → Option KNode) (t : Time) (r r' : NodeId)
    (New Gone : NodeId → Prop) (tr : NodeId → Nat → NodeId × Nat)
    (ht : TreeOK L t r) (hNew : ∀ z, New z → ¬ TReach L t r z)
    (hr' : (r' = r ∧ ¬ Gone r) ∨ (New r' ∧ ∀ y c, (TReach L t r y ∨ New y) → ¬ Gone y →
      ¬ TLink L' t y c r'))
    (hlinks : ∀ u c v, (TReach L t r u ∨ New u) → ¬ Gone u → TLink L' t u c v →
      New v ∨ (¬ Gone v ∧ ∃ y0 c0, TReach L t r y0 ∧ TLink L t y0 c0 v ∧ tr y0 c0 = (u, c)))
    (hnewOnce : ∀ u c u' c' z, (TReach L t r u ∨ New u) → ¬ Gone u →
      (TReach L t r u' ∨ New u') → ¬ Gone u' → New z →
      TLink L' t u c z → TLink L' t u' c' z → u = u' ∧ c = c')
    (hNewGone : ∀ z, New z → ¬ Gone z)
    (hroot : ∃ n, L' r' = some n) : TreeOK L' t r' := by
  have hb : ∀ y, TReach L' t r' y → (TReach L t r y ∨ New y) ∧ ¬ Gone y := by
    intro y hy
    induction hy with
    | root =>
      rcases hr' with ⟨h, hg⟩ | ⟨h, _⟩
      · rw [h]; exact ⟨Or.inl TReach.root, hg⟩
      · exact ⟨Or.inr h, hNewGone _ h⟩
    | @link u c v _ hl ih =>
      rcases hlinks u c v ih.1 ih.2 hl with h | ⟨hg, y0, c0, hy0, hl0, _⟩
      · exact ⟨Or.inr h, hNewGone v h⟩
      · exact ⟨Or.inl (TReach.link hy0 hl0), hg⟩
  refine ⟨hroot, ?_, ?_⟩
  · intro y c hy hl
    obtain ⟨hy1, hy2⟩ := hb y hy
    rcases hr' with ⟨h, _⟩ | ⟨_, h⟩
    · rw [h] at hl
      rcases hlinks y c r hy1 hy2 hl with hn | ⟨_, y0, c0, hy0, hl0, _⟩
      · exact hNew r hn TReach.root
      · exact ht.rootFree y0 c0 hy0 hl0
    · exact h y c hy1 hy2 hl
  · intro y1 c1 y2 c2 v hy1 hy2 hl1 hl2
    obtain ⟨h11, h12⟩ := hb y1 hy1
    obtain ⟨h21, h22⟩ := hb y2 hy2
    by_cases hvn : New v
    · exact hnewOnce y1 c1 y2 c2 v h11 h12 h21 h22 hvn hl1 hl2
    · rcases hlinks y1 c1 v h11 h12 hl1 with h | ⟨_, y01, c01, hy01, hl01, htr1⟩
      · exact absurd h hvn
      rcases hlinks y2 c2 v h21 h22 hl2 with h | ⟨_, y02, c02, hy02, hl02, htr2⟩
      · exact absurd h hvn
      obtain ⟨he, hc⟩ := ht.oneLink y01 c01 y02 c02 v hy01 hy02 hl01 hl02
      subst he; subst hc
      rw [htr1] at htr2
      simp only [Prod.mk.injEq] at htr2
      exact htr2

/-- A node reached from a node reached from r is reached from r. -/
theorem tReach_trans (L : NodeId → Option KNode) (t : Time) (r y : NodeId)
    (hy : TReach L t r y) : ∀ v, TReach L t y v → TReach L t r v := by
  intro v hv
  induction hv with
  | root => exact hy
  | link _ hl ih => exact TReach.link ih hl

/-- The tree below a child of the root (root collapse: the child takes the
root's place). -/
theorem treeOK_child (L : NodeId → Option KNode) (t : Time) (r y : NodeId) (c : Nat)
    (ht : TreeOK L t r) (hl : TLink L t r c y) (hy : ∃ n, L y = some n) : TreeOK L t y := by
  have hyr : TReach L t r y := TReach.link TReach.root hl
  have hsub := tReach_trans L t r y hyr
  -- r is not reached from y
  have hnr : ¬ TReach L t y r := by
    intro h
    cases h with
    | root => exact ht.rootFree r c TReach.root hl
    | link hz hl' => exact ht.rootFree _ _ (hsub _ hz) hl'
  refine ⟨hy, ?_, ?_⟩
  · intro z c' hz hl'
    have := (ht.oneLink z c' r c y (hsub z hz) TReach.root hl' hl).1
    rw [this] at hz
    exact hnr hz
  · intro x1 c1 x2 c2 v h1 h2 hl1 hl2
    exact ht.oneLink x1 c1 x2 c2 v (hsub x1 h1) (hsub x2 h2) hl1 hl2

/-! ## The first state, and the state after the transaction -/

/-- The writer's first state has P's tree at the time before: the same nodes,
the same live klongs (P has no entry after it), the same space root. -/
theorem writerTreeOK_init (p : Params) (ts : List Tx) (tx : Tx) (z : NodeId) (top : Top)
    (hz : lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z)
    (htop : topOf p (ctxOf p ts).view z = .ok top)
    (hT : TreeAt p (treeRun p ts) ts.length) :
    WriterTreeOK p (treeRun p ts) (ts.length + 1) (wInit tx top) := by
  obtain ⟨r, hr, ht⟩ := hT
  have hroot := rootAt_of_writerTop p ts z top hz htop
  rw [hr] at hroot
  simp only [Option.some.injEq] at hroot
  unfold WriterTreeOK
  have hlook : wNode p (viewOf (treeRun p ts)) (wInit tx top) = knodeOf p (viewOf (treeRun p ts)) := by
    funext x
    simp [wNode, wInit]
  rw [hlook]
  show TreeOK (knodeOf p (viewOf (treeRun p ts))) (ts.length + 1) top.rootKey
  rw [← hroot]
  have hP := treeRun_timesLE p ts
  apply treeOK_congr_time _ ts.length (ts.length + 1) r _ ht
  intro x n hx
  have hk := knodeOf_timesLE p (treeRun p ts) ts.length hP x n hx
  apply KNode.liveAt_eq_of_prefixAt
  rw [prefixAt_of_timesLE n.ks (ts.length + 1) (fun y hy => Nat.le_succ_of_le (hk y hy)),
    prefixAt_of_timesLE n.ks ts.length hk]

/-! ## By operation -/

/-- Each operation of a transaction within reach, from a state that its
earlier operations reach and that has the writer's tree, keeps it. Not proved:
every rule of the writer (the splits, the upward delete, LE-b, the merges,
root collapse). -/
def OpTreeOK (p : Params) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre op post, tx.ops = pre ++ op :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    WriterTreeOK p (treeRun p ts) (ts.length + 1) w →
    WriterWP (putKv op) (ctxOf p ts) w (fun _ w' =>
      WriterTreeOK p (treeRun p ts) (ts.length + 1) w')

/-- Every state that a prefix of the operations reaches has the writer's tree,
from the first state's and `OpTreeOK`. -/
theorem writerTreeOK_fold (p : Params) (ho : OpTreeOK p) (ts : List Tx) (tx : Tx)
    (hw : Within p (ts ++ [tx])) (z : NodeId) (top : Top)
    (hz : lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z)
    (htop : topOf p (ctxOf p ts).view z = .ok top) :
    ∀ todo done extra, tx.ops = done ++ todo ++ extra → ∀ r w,
      (done.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      WriterTreeOK p (treeRun p ts) (ts.length + 1) w →
      ∀ r' w', (todo.mapM putKv) (ctxOf p ts) w = .ok (r', w') →
      WriterTreeOK p (treeRun p ts) (ts.length + 1) w' := by
  intro todo
  induction todo with
  | nil =>
    intro done _ _ r w _ hT r' w' hrun
    simp only [List.mapM_nil, pure, ReaderT.pure, StateT.pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at hrun
    rw [← hrun.2]
    exact hT
  | cons op rest ih =>
    intro done extra hsplit r w hdone hT r' w' hrun
    obtain ⟨a, w1, r1, h1, h2⟩ := mapM_cons_run op rest _ w w' r' hrun
    have hT1 := ho ts tx hw z top hz htop done op (rest ++ extra) (by rw [hsplit]; simp) r w hdone
      hT a w1 h1
    have hdone' := mapM_snoc_run done op _ _ w w1 r a hdone h1
    exact ih (done ++ [op]) extra (by rw [hsplit]; simp) _ w1 hdone' hT1 r1 w' h2

/-- The writer's tree at every state between operations, from P's tree before
the transaction and `OpTreeOK`. -/
theorem writerTreeOK_reached (p : Params) (ho : OpTreeOK p) (ts : List Tx) (tx : Tx)
    (hw : Within p (ts ++ [tx])) (z : NodeId) (top : Top)
    (hz : lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z)
    (htop : topOf p (ctxOf p ts).view z = .ok top)
    (hT : TreeAt p (treeRun p ts) ts.length) (pre : List Tree.Op) (post : List Tree.Op)
    (hsplit : tx.ops = pre ++ post) (r : List Bool) (w : W)
    (hpre : (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w)) :
    WriterTreeOK p (treeRun p ts) (ts.length + 1) w :=
  writerTreeOK_fold p ho ts tx hw z top hz htop pre [] post (by simp [hsplit]) [] (wInit tx top)
    (by simp only [List.mapM_nil, pure, ReaderT.pure, StateT.pure, Except.pure])
    (writerTreeOK_init p ts tx z top hz htop hT) r w hpre

/-! ## Every run -/

/-- R(0)'s key nodes make a tree: its one key node, the primordial segment leaf,
has no live klong. -/
theorem treeAt_init (p : Params) : TreeAt p (initStruct p) 0 := by
  have hr : rootAt (viewOf (initStruct p)) 0 = some 1 := rfl
  have hk : knodeOf p (viewOf (initStruct p)) 1 =
      some { leaf := p.heightOf (p.keyLevel 0 0) == 0, ks := [.time 0] } := by
    have hl : ¬ p.keyMax < p.keyLevel 0 0 := by
      simp only [Params.keyLevel, Params.keyMax, Nat.sub_zero]; omega
    simp only [knodeOf, viewOf, initStruct, Struct.get?, List.lookup, root]
    simp only [show (1 == 0) = false from rfl, show (1 == 1) = true from rfl, hl, decide_false,
      Bool.or_false, Bool.false_eq_true, ↓reduceIte]
    rfl
  have hno : ∀ x c y, TReach (knodeOf p (viewOf (initStruct p))) 0 1 x →
      ¬ TLink (knodeOf p (viewOf (initStruct p))) 0 x c y := by
    intro x c y hx
    have h1 : x = 1 := by
      induction hx with
      | root => rfl
      | link _ hl ih =>
        subst ih
        obtain ⟨n, hn, hl'⟩ := hl
        rw [hk] at hn
        simp only [Option.some.injEq] at hn
        subst hn
        exact absurd hl' (by simp [KNode.liveAt, prefixAt, KNode.delAt, KNode.lastVersionGivenDel])
    subst h1
    rintro ⟨n, hn, hl⟩
    rw [hk] at hn
    simp only [Option.some.injEq] at hn
    subst hn
    exact absurd hl (by simp [KNode.liveAt, prefixAt, KNode.delAt, KNode.lastVersionGivenDel])
  refine ⟨1, hr, ⟨_, hk⟩, ?_, ?_⟩
  · intro x c hx hl
    exact hno x c 1 hx hl
  · intro x c x' c' y hx _ hl _
    exact absurd hl (hno x c y hx)

end SIS.Tree
