/-
The writer's tree is a tree between operations (bergdb 024-22 and 024-12, for
TP33's `OpCountOK` and TP10's `OpGetOK`): from the writer's super root, through
its key nodes (`wNode`: its own copies, P's for the others, none for a node it
took back), at the transaction's time, no node is reached twice and nothing
links back to the space root (`WriterTreeOK`). A link is a live klong of a node:
any in an inner node, a long segment's in a segment leaf (the walk of `nodesRoots`
and of the reads).

The same of P between transactions is `TreeAt`. Proved here: the writer's first
state has the tree of P (`writerTreeOK_init`), P after the transaction has the
tree of the writer's last state, given the lift of the writer's key nodes
(`treeAt_commit_of_lift`), and so every run within reach has it if every
operation keeps it (`OpTreeOK`, open: each rule of the writer) and the lift
holds (`treeAt_run`). Every state between operations then has it
(`writerTreeOK_reached`), which `OpCountOK` and `OpGetOK` can take as a premise.
-/
import SIS.Tree.MergeNodeCountOps

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## Trees of key nodes -/

/-- A link at time t through the lookup `look`: the klong of compare value c is
live in key node x and names y; in a segment leaf only a long segment's klong
(it names the root of the next segment's tree). -/
def TLink (look : NodeId → Option KNode) (t : Time) (x : NodeId) (c : Nat) (y : NodeId) : Prop :=
  ∃ n, look x = some n ∧ (c, y) ∈ n.liveAt t ∧ (n.leaf = true → segLen c = 7)

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
  · rintro ⟨n, hn, hl, hs⟩
    exact ⟨n, hn, by rw [← h x n hn]; exact hl, hs⟩
  · rintro ⟨n, hn, hl, hs⟩
    exact ⟨n, hn, by rw [h x n hn]; exact hl, hs⟩

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
    obtain ⟨n, hn, hc, hs⟩ := hl
    rw [h x ih] at hn
    exact TReach.link ih ⟨n, hn, hc, hs⟩

theorem tReach_to_agree (L L' : NodeId → Option KNode) (t : Time) (r : NodeId)
    (h : ∀ x, TReach L t r x → L' x = L x) : ∀ y, TReach L t r y → TReach L' t r y := by
  intro y hy
  induction hy with
  | root => exact TReach.root
  | @link x c y hx hl ih =>
    obtain ⟨n, hn, hc, hs⟩ := hl
    rw [← h x hx] at hn
    exact TReach.link ih ⟨n, hn, hc, hs⟩

/-- A change of nodes that the tree does not reach keeps the tree (a node made
and not yet linked, a node left out, a node read into the cache unchanged). -/
theorem treeOK_of_agree (L L' : NodeId → Option KNode) (t : Time) (r : NodeId)
    (ht : TreeOK L t r) (h : ∀ x, TReach L t r x → L' x = L x) : TreeOK L' t r := by
  have hb := tReach_of_agree L L' t r h
  have hlink : ∀ x c y, TReach L' t r x → TLink L' t x c y → TLink L t x c y := by
    intro x c y hx hl
    obtain ⟨n, hn, hc, hs⟩ := hl
    rw [h x (hb x hx)] at hn
    exact ⟨n, hn, hc, hs⟩
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

/-- A link from a node of the tree to a node z that the tree does not reach and
that has no link (a new segment leaf) keeps the tree; the lookup changes only
at the linking node. -/
theorem treeOK_attach (L L' : NodeId → Option KNode) (t : Time) (r x z : NodeId) (cz : Nat)
    (ht : TreeOK L t r) (hx : TReach L t r x) (hz : ¬ TReach L t r z)
    (hzl : ∀ c y, ¬ TLink L t z c y)
    (hother : ∀ y, y ≠ x → L' y = L y)
    (hlinks : ∀ c y, TLink L' t x c y → TLink L t x c y ∨ (c = cz ∧ y = z))
    (hroot : ∃ n, L' r = some n) : TreeOK L' t r := by
  have hzx : z ≠ x := fun he => hz (he ▸ hx)
  have hlink' : ∀ y c y', TLink L' t y c y' → TLink L t y c y' ∨ (y = x ∧ c = cz ∧ y' = z) := by
    intro y c y' hl
    by_cases hy : y = x
    · subst hy
      rcases hlinks c y' hl with h | h
      · exact Or.inl h
      · exact Or.inr ⟨rfl, h⟩
    · obtain ⟨n, hn, hc, hs⟩ := hl
      rw [hother y hy] at hn
      exact Or.inl ⟨n, hn, hc, hs⟩
  -- What L' reaches: what L reaches, and z.
  have hb : ∀ y, TReach L' t r y → TReach L t r y ∨ y = z := by
    intro y hy
    induction hy with
    | root => exact Or.inl TReach.root
    | @link y0 c y' _ hl ih =>
      rcases ih with ih | ih
      · rcases hlink' y0 c y' hl with h | ⟨_, _, h⟩
        · exact Or.inl (TReach.link ih h)
        · exact Or.inr h
      · rw [ih] at hl
        rcases hlink' z c y' hl with h | ⟨h, _, _⟩
        · exact absurd h (hzl c y')
        · exact absurd h hzx
  refine ⟨hroot, ?_, ?_⟩
  · intro y c hy hl
    rcases hb y hy with hy | hy
    · rcases hlink' y c r hl with h | ⟨_, _, h⟩
      · exact ht.rootFree y c hy h
      · exact hz (h ▸ TReach.root)
    · rw [hy] at hl
      rcases hlink' z c r hl with h | ⟨h, _, _⟩
      · exact hzl c r h
      · exact hzx h
  · intro y c y' c' v hy hy' hl hl'
    -- links from z do not exist
    have hnz : ∀ w0 c0, TReach L' t r w0 → TLink L' t w0 c0 v → TReach L t r w0 := by
      intro w0 c0 hw0 hl0
      rcases hb w0 hw0 with h | h
      · exact h
      · rw [h] at hl0
        rcases hlink' z c0 v hl0 with h | ⟨h, _, _⟩
        · exact absurd h (hzl c0 v)
        · exact absurd h hzx
    have hyL := hnz y c hy hl
    have hyL' := hnz y' c' hy' hl'
    rcases hlink' y c v hl with h1 | ⟨h1x, h1c, h1v⟩ <;>
      rcases hlink' y' c' v hl' with h2 | ⟨h2x, h2c, h2v⟩
    · exact ht.oneLink y c y' c' v hyL hyL' h1 h2
    · exact absurd (h2v ▸ TReach.link hyL h1) hz
    · exact absurd (h1v ▸ TReach.link hyL' h2) hz
    · exact ⟨h1x.trans h2x.symm, h1c.trans h2c.symm⟩

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

/-- With the lift of the writer's key nodes, P after the transaction has the
tree of the writer's last state. -/
theorem treeAt_commit_of_lift (p : Params) (hl : CommitLiftOK p) (ts : List Tx) (tx : Tx)
    (hw : Within p (ts ++ [tx])) (noops : List Bool) (w : W)
    (hrun : runOps p tx.base tx.ops (ts.length + 1)
      (view (treeSpec p) (treeRun p ts) ts.length) = .ok (noops, w))
    (hT : WriterTreeOK p (treeRun p ts) (ts.length + 1) w) :
    TreeAt p (treeRun p (ts ++ [tx])) (ts.length + 1) := by
  obtain ⟨hK, htaken, htopt⟩ := hl ts tx hw noops w hrun
  have hR := rootAt_commit_of_lift p ts tx hw noops w hrun hK htaken htopt
  refine ⟨w.top.rootKey, hR, ?_⟩
  exact treeOK_congr_look _ _ _ _ (funext hK).symm hT

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
        obtain ⟨n, hn, hl', _⟩ := hl
        rw [hk] at hn
        simp only [Option.some.injEq] at hn
        subst hn
        exact absurd hl' (by simp [KNode.liveAt, prefixAt, KNode.delAt, KNode.lastVersionGivenDel])
    subst h1
    rintro ⟨n, hn, hl, _⟩
    rw [hk] at hn
    simp only [Option.some.injEq] at hn
    subst hn
    exact absurd hl (by simp [KNode.liveAt, prefixAt, KNode.delAt, KNode.lastVersionGivenDel])
  refine ⟨1, hr, ⟨_, hk⟩, ?_, ?_⟩
  · intro x c hx hl
    exact hno x c 1 hx hl
  · intro x c x' c' y hx _ hl _
    exact absurd hl (hno x c y hx)

/-- Every run within reach has P's tree at its last time, if every operation
keeps the writer's tree and the lift holds. -/
theorem treeAt_run (p : Params) (ho : OpTreeOK p) (hl : CommitLiftOK p) :
    ∀ ts, Within p ts → TreeAt p (treeRun p ts) ts.length := by
  have hf : ∀ revts : List Tx, Within p revts.reverse →
      TreeAt p (treeRun p revts.reverse) revts.reverse.length := by
    intro revts
    induction revts with
    | nil =>
      intro _
      simpa [treeRun] using treeAt_init p
    | cons tx revts ih =>
      intro hw
      simp only [List.reverse_cons] at hw ⊢
      have hT := ih (within_snoc_prefix p revts.reverse tx hw)
      obtain ⟨noops, w, hrun⟩ := within_last_ok p revts.reverse tx hw
      obtain ⟨z, top, hz, htop, hops⟩ := runOps_ok p _ _ _ _ noops w hrun
      have hW := writerTreeOK_reached p ho revts.reverse tx hw z top hz htop hT tx.ops []
        (by simp) noops w hops
      have h := treeAt_commit_of_lift p hl revts.reverse tx hw noops w hrun hW
      simpa only [List.length_append, List.length_singleton] using h
  intro ts hw
  simpa using hf ts.reverse (by simpa using hw)

/-- The writer's tree at every state between the operations of a transaction
that ends a run within reach, if every operation keeps it and the lift holds:
the premise that `OpCountOK` and `OpGetOK` can take. -/
theorem writerTreeOK_between (p : Params) (ho : OpTreeOK p) (hl : CommitLiftOK p)
    (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx])) (z : NodeId) (top : Top)
    (hz : lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z)
    (htop : topOf p (ctxOf p ts).view z = .ok top) (pre post : List Tree.Op)
    (hsplit : tx.ops = pre ++ post) (r : List Bool) (w : W)
    (hpre : (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w)) :
    WriterTreeOK p (treeRun p ts) (ts.length + 1) w :=
  writerTreeOK_reached p ho ts tx hw z top hz htop
    (treeAt_run p ho hl ts (within_snoc_prefix p ts tx hw)) pre post hsplit r w hpre

/-! ## TP33 with the tree -/

/-- `OpCountOK` with the writer's tree as a premise: each operation from a state
that has the writer's tree changes the count by at most twice its space splits
less its merges into one node. Not proved. -/
def OpCountTreeOK (p : Params) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre op post, tx.ops = pre ++ op :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    WriterTreeOK p (treeRun p ts) (ts.length + 1) w →
    WriterWP (putKv op) (ctxOf p ts) w (fun _ w' =>
      wCount p (treeRun p ts) w' (ts.length + 1) + oneMerges w' + 2 * w.spaceSplits ≤
        wCount p (treeRun p ts) w (ts.length + 1) + oneMerges w + 2 * w'.spaceSplits)

theorem opCountOK_of_tree (p : Params) (hc : OpCountTreeOK p) (ho : OpTreeOK p)
    (hl : CommitLiftOK p) : OpCountOK p := by
  intro ts tx hw z top hz htop pre op post hsplit r w hpre
  exact hc ts tx hw z top hz htop pre op post hsplit r w hpre
    (writerTreeOK_between p ho hl ts tx hw z top hz htop pre (op :: post) hsplit r w hpre)

/-- TP33 from the count's step on the writer's tree, the writer's tree kept by
each operation, and the lift of the writer's key nodes. -/
theorem mergeAmortized_of_tree (p : Params)
    (h : MergeParamsOK p → OpCountTreeOK p ∧ OpTreeOK p ∧ CommitLiftOK p) : MergeAmortized p :=
  mergeAmortized_of_opCount_lift p (fun hp =>
    ⟨opCountOK_of_tree p (h hp).1 (h hp).2.1 (h hp).2.2, (h hp).2.2⟩)

end SIS.Tree
