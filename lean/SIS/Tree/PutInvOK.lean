import SIS.Tree.GetPutInv
import SIS.Tree.ApplyBridge
import SIS.Tree.FreshCache
import SIS.Tree.WriterPtrsRun
import SIS.Tree.GetCommit
import SIS.Tree.AllocationIds
import SIS.Tree.WriterBookMerge
import SIS.Tree.WriterKlongOps
import SIS.Tree.WriterGoodOps
import SIS.Tree.WriterTree

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! `PutInv` (bergdb 024-12, TP10; `GetPutInv.lean`) kept by the writer's
operations. `OpPutInvOK p R`: each operation of a transaction within reach,
after a run whose structure meets R, from a state that its earlier operations
reach and that meets `PutInv`, keeps `PutInv`, given the writer's tree after
it (cost's `OpTreeOK`). The quantifiers are those of `OpGetOKUnder`.

The parts of `PutInv` split in two:

* the global parts (`PutInvG`): klongs well formed and of no later time, ids
  below the next one, the next ones fresh, every live link of every node
  below the next id, no key node a value. They hold after every operation of
  the writer, whatever its rule (`putInvG_putKv`), from the books that tp7's
  writer lemmas keep (`PutBook`) and facts of P (`PutBase`);
* the parts about the tree: no reachable node taken back, the order at the
  leaves (`LeafOrderAt`). They are proved rule by rule. -/

/-- Each operation keeps `PutInv` (the writer's tree after it given). -/
def OpPutInvOK (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre op post, tx.ops = pre ++ op :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w →
    WriterWP (putKv op) (ctxOf p ts) w (fun _ w' =>
      WriterTreeOK p (treeRun p ts) (ts.length + 1) w' →
      PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w')

/-! ## The facts of P and the writer's books -/

/-- What the writer's run needs of P (the base) and of its view P@(i-1): ids
below the transaction's first id B; key nodes with well-formed klongs of no
later time that name ids below B; the view inside the base; tp7's `ViewGood`
and `ViewKlongsWf`. -/
structure PutBase (c : Ctx) (base : View BVal) (B : NodeId) : Prop where
  ids : ∀ x nd, base x = some nd → x < B
  knode : ∀ x n, knodeOf c.p base x = some n →
    klongsWf n.ks = true ∧ (∀ s, Klong.time s ∈ n.ks → s ≤ c.i) ∧
    ∀ cv y, Klong.key cv y ∈ n.ks → y < B
  coherent : ViewCoherent c base
  good : ViewGood B c
  wf : ViewKlongsWf c.p c.view

/-- The books of the writer's state that every rule keeps (tp7's and cost's
writer lemmas): klongs well formed, no klong of an earlier time changed, the
overlay's books, the ids allocated, the values made, ids below the next one,
the pointers to P or to nodes made. -/
structure PutBook (c : Ctx) (B : NodeId) (top0 : Top) (w : W) : Prop where
  klongs : WriterKlongsWf w
  good : CacheGood B c w
  book : Book B c w
  alloc : AllocatedIds B w
  commit : CommitInv top0 c w
  fresh : FreshCache B w
  ptrs : PtrsOK (fun y => y < B) c w

theorem putBase_ptrs (c : Ctx) (base : View BVal) (B : NodeId) (hB : PutBase c base B) :
    ViewPtrsOld (fun y => y < B) c.view :=
  ⟨fun x nd hx => hB.good.ids x nd hx, hB.good.ptrs⟩

/-- Every operation keeps the books; the next id grows, the overlay keeps its
nodes. -/
theorem putBook_putKv (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top) (op : Op)
    (hB : PutBase c base B) (w : W) (hw : PutBook c B top0 w) :
    WriterWP (putKv op) c w (fun _ w' => PutBook c B top0 w' ∧ w.next ≤ w'.next ∧ Kept w w') := by
  have h1 := klongsWf_putKv op c w hB.wf hw.klongs
  have h2 := good_putKv B op c w hB.good hw.good
  have h3 := book_putKv B op c w hB.good.ids hw.book
  have h4 := @state_putKv (allocatedIdsInvariant B) op c w hw.alloc
  have h5 := @state_putKv (commitInvariant top0) op c w hw.commit
  have h6 := freshCache_putKv (base := B) op c w hB.good.ids hw.fresh
  have h7 := ptrs_putKv (fun y => y < B) op c w (putBase_ptrs c base B hB) hw.ptrs
  intro r w' h
  exact ⟨⟨h1 r w' h, h2 r w' h, (h3 r w' h).1, h4 r w' h, h5 r w' h, (h6 r w' h).1,
    (h7 r w' h).1⟩, (h6 r w' h).2, (h3 r w' h).2⟩

/-- The books along the operations of a transaction. -/
theorem putBook_ops (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top) (ops : List Op)
    (hB : PutBase c base B) (w : W) (hw : PutBook c B top0 w) :
    WriterWP (ops.mapM putKv) c w (fun _ w' => PutBook c B top0 w') := by
  have h1 := klongsWf_ops ops c w hB.wf hw.klongs
  have h2 := good_ops B ops c w hB.good hw.good
  have h3 := book_ops B ops c w hB.good.ids hw.book
  have h4 := @state_ops (allocatedIdsInvariant B) ops c w hw.alloc
  have h5 := @state_ops (commitInvariant top0) ops c w hw.commit
  have h6 := freshCache_ops (base := B) ops c w hB.good.ids hw.fresh
  have h7 := ptrs_ops (fun y => y < B) ops c w (putBase_ptrs c base B hB) hw.ptrs
  intro r w' h
  exact ⟨h1 r w' h, h2 r w' h, (h3 r w' h).1, h4 r w' h, h5 r w' h, (h6 r w' h).1,
    (h7 r w' h).1⟩

/-! ## The global parts of `PutInv` -/

/-- The parts of `PutInv` that every state of the writer has, whatever rule
made it. The links are those of every node, not only of the reachable ones. -/
structure PutInvG (c : Ctx) (base : View BVal) (w : W) : Prop where
  wf : ∀ x xn, wNode c.p base w x = some xn → klongsWf xn.ks = true
  times : ∀ x xn, wNode c.p base w x = some xn → ∀ s, Klong.time s ∈ xn.ks → s ≤ c.i
  ids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
    (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next) ∧
    (∀ q ∈ w.vals, q.1 < w.next)
  fresh : ∀ z, w.next ≤ z → knodeOf c.p base z = none ∧ valueOf base z = none
  links : ∀ x xn cc z, wNode c.p base w x = some xn → (cc, z) ∈ xn.liveAt c.i → z < w.next
  keyNoValue : ∀ x xn, wNode c.p base w x = some xn → wValue base w x = none

/-- A node the writer's state reads: from its overlay, not taken back, or a
key node of the base not in the overlay. -/
theorem wNode_cases (p : Params) (base : View BVal) (w : W) (x : NodeId) (xn : KNode)
    (h : wNode p base w x = some xn) :
    w.taken.contains x = false ∧
      (w.nodes.lookup x = some xn ∨ (w.nodes.lookup x = none ∧ knodeOf p base x = some xn)) := by
  unfold wNode at h
  cases ht : w.taken.contains x with
  | true => rw [ht] at h; simp at h
  | false =>
    rw [ht] at h
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    refine ⟨rfl, ?_⟩
    cases hl : w.nodes.lookup x with
    | some n => rw [hl] at h; exact Or.inl h
    | none => rw [hl] at h; exact Or.inr ⟨rfl, h⟩

theorem valueOf_of_notData (base : View BVal) (x : NodeId) (nd : Node BVal)
    (hb : base x = some nd) (hd : nd.isData = false) : valueOf base x = none := by
  unfold valueOf; rw [hb]; simp [hd]

theorem base_none_of_ge (c : Ctx) (base : View BVal) (B : NodeId) (hB : PutBase c base B)
    (z : NodeId) (hz : B ≤ z) : base z = none := by
  cases hb : base z with
  | none => rfl
  | some nd => have := hB.ids z nd hb; omega

theorem putInvG_of_book (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top) (w : W)
    (hB : PutBase c base B) (hw : PutBook c B top0 w) : PutInvG c base w := by
  have hBn : B ≤ w.next := hw.fresh.1
  have hvalsMade : ∀ q ∈ w.vals, (⟨q.1, 0, true⟩ : NewNode) ∈ w.made := hw.commit.2.2.2.1
  have hvalsB : ∀ q ∈ w.vals, B ≤ q.1 := fun q hq => (hw.alloc.2.2 _ (hvalsMade q hq)).1
  -- no value is a key node of the overlay
  have hvalNode : ∀ x n, w.nodes.lookup x = some n → w.vals.lookup x = none := by
    intro x n hn
    cases hv : w.vals.lookup x with
    | none => rfl
    | some h =>
      exfalso
      have hxv : (x, h) ∈ w.vals := bk_mem_of_lookup _ _ _ hv
      have hmade := hvalsMade _ hxv
      have hxB := hvalsB _ hxv
      have hxn : (x, n) ∈ w.nodes := bk_mem_of_lookup _ _ _ hn
      have hxg : x ∈ w.gh.map (·.1) := by
        have : x ∈ w.nodes.map (·.1) := List.mem_map.mpr ⟨(x, n), hxn, rfl⟩
        rw [hw.book.ids] at this
        exact List.mem_reverse.mp this
      obtain ⟨⟨x', g, hh⟩, hq, hx'⟩ := List.mem_map.mp hxg
      simp only at hx'
      subst hx'
      rcases hw.book.tag x' g hh hq with ⟨nd, hnd, _, _, _, _⟩ | ⟨_, hk, _⟩
      · have := hB.good.ids x' nd hnd; omega
      · have he := made_unique B w hw.alloc _ _ hmade hk rfl
        simp at he
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x xn h
    rcases (wNode_cases _ _ _ _ _ h).2 with hl | ⟨_, hk⟩
    · exact writerKlongsWf_lookup w hw.klongs x xn hl
    · exact (hB.knode x xn hk).1
  · intro x xn h
    rcases (wNode_cases _ _ _ _ _ h).2 with hl | ⟨_, hk⟩
    · exact (cacheGood_lookup B c w hw.good x xn hl).times
    · exact (hB.knode x xn hk).2.1
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro z hz
      cases hl : w.nodes.lookup z with
      | none => rw [hl] at hz; cases hz
      | some n => exact freshCache_lookup_lt B w hw.fresh z n hl
    · intro z hz
      cases hv : c.view z with
      | none => rw [hv] at hz; cases hz
      | some nd => have := hB.good.ids z nd hv; omega
    · intro z hz
      exact hw.fresh.2.2.2 z (List.contains_iff_mem.mp hz)
    · exact hw.commit.2.2.2.2.2
  · intro z hz
    have hb := base_none_of_ge c base B hB z (by omega)
    constructor
    · unfold knodeOf; rw [hb]
    · unfold valueOf; rw [hb]
  · intro x xn cc z h hz
    have hk := KNode.liveAt_key_mem xn c.i cc z hz
    rcases (wNode_cases _ _ _ _ _ h).2 with hl | ⟨_, hkn⟩
    · rcases hw.ptrs.klongs (x, xn) (bk_mem_of_lookup _ _ _ hl) cc z hk with hz' | hz'
      · omega
      · obtain ⟨m, hm, he⟩ := List.mem_map.mp hz'
        rw [← he]
        exact (hw.alloc.2.2 m hm).2
    · have := (hB.knode x xn hkn).2.2 cc z hk; omega
  · intro x xn h
    obtain ⟨ht, hc⟩ := wNode_cases _ _ _ _ _ h
    unfold wValue
    rw [ht]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rcases hc with hl | ⟨_, hk⟩
    · rw [hvalNode x xn hl]
      -- the node is of the view or made by the transaction
      have hxn : (x, xn) ∈ w.nodes := bk_mem_of_lookup _ _ _ hl
      have hxg : x ∈ w.gh.map (·.1) := by
        have : x ∈ w.nodes.map (·.1) := List.mem_map.mpr ⟨(x, xn), hxn, rfl⟩
        rw [hw.book.ids] at this
        exact List.mem_reverse.mp this
      obtain ⟨⟨x', g, hh⟩, hq, hx'⟩ := List.mem_map.mp hxg
      simp only at hx'
      subst hx'
      rcases hw.book.tag x' g hh hq with ⟨nd, hnd, hd, _, _, _⟩ | ⟨hBx, _, _⟩
      · exact valueOf_of_notData base x' nd (hB.coherent x' nd hnd) hd
      · unfold valueOf; rw [base_none_of_ge c base B hB x' hBx]
    · obtain ⟨nd, hb, hd⟩ := knodeOf_view _ _ _ _ hk
      have hxB := hB.ids x nd hb
      have hvx : w.vals.lookup x = none := by
        cases hv : w.vals.lookup x with
        | none => rfl
        | some h' =>
          have := hvalsB _ (bk_mem_of_lookup _ _ _ hv); omega
      rw [hvx]
      exact valueOf_of_notData base x nd hb hd

/-- Every node the writer's state reads has an id below the next one. -/
theorem PutInvG.node_lt {c : Ctx} {base : View BVal} {w : W} (hG : PutInvG c base w)
    (x : NodeId) (xn : KNode) (h : wNode c.p base w x = some xn) : x < w.next := by
  rcases (wNode_cases _ _ _ _ _ h).2 with hl | ⟨_, hk⟩
  · exact hG.ids.1 x (by rw [hl]; rfl)
  · cases Nat.lt_or_ge x w.next with
    | inl hlt => exact hlt
    | inr hge => rw [(hG.fresh x hge).1] at hk; cases hk

/-- `PutInv` from its global parts, the tree, and its two parts about the
tree. -/
theorem putInv_of_parts (c : Ctx) (base : View BVal) (w : W) (hG : PutInvG c base w)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hu : ∀ x, ReachS (wNode c.p base w) c.i w.top.rootKey x → w.taken.contains x = false)
    (ho : ∀ q qn L n k1, ReachS (wNode c.p base w) c.i w.top.rootKey q →
      wNode c.p base w q = some qn → qn.leaf = false → wNode c.p base w L = some n →
      n.leaf = true → (k1, L) ∈ qn.live → LeafOrderAt qn k1 n) :
    PutInv c base w := by
  obtain ⟨rn, hrn⟩ := hT.rootKey
  exact ⟨hT, hG.wf, hG.times, ⟨hG.ids.1, hG.ids.2.1, hG.ids.2.2.1, hG.ids.2.2.2,
    hG.node_lt _ _ hrn⟩, hG.fresh, fun x xn cc z _ hn hz => hG.links x xn cc z hn hz, hu,
    hG.keyNoValue, ho⟩

/-! ## Reachability after a change -/

/-- The nodes reachable through a new reader N' are reachable through the old
one N or lie in a set S, if every live link of N' from a node of either kind
leads to a node of either kind. -/
theorem reachS_sub (N N' : NodeId → Option KNode) (t : Time) (r r' : NodeId)
    (S : NodeId → Prop) (hr : ReachS N t r r' ∨ S r')
    (hstep : ∀ x xn c z, (ReachS N t r x ∨ S x) → N' x = some xn → (c, z) ∈ xn.liveAt t →
      ReachS N t r z ∨ S z) :
    ∀ x, ReachS N' t r' x → ReachS N t r x ∨ S x := by
  intro x hx
  induction hx with
  | root => exact hr
  | step x n c z _ hn hc ih => exact hstep x n c z ih hn hc

/-- The node a segment tree's search visits after another one is named by the
`searchLte` of an inner node visited before it. -/
theorem eqVisits_parent_lte (N : NodeId → Option KNode) (t : Time) (cv : Nat) :
    ∀ (f : Nat) (x L : NodeId), (L, cv) ∈ eqVisits N t cv f x → L ≠ x →
      ∃ q qn fd, (q, cv) ∈ eqVisits N t cv f x ∧ N q = some qn ∧ qn.leaf = false ∧
        qn.searchLte t cv = some fd ∧ fd.y = L := by
  intro f
  induction f with
  | zero => intro x L h; simp [eqVisits] at h
  | succ f ih =>
    intro x L hL hLx
    simp only [eqVisits, List.mem_cons, Prod.mk.injEq, and_true] at hL
    rcases hL with hL | hL
    · exact absurd hL hLx
    cases hx : N x with
    | none => rw [hx] at hL; cases hL
    | some n =>
      rw [hx] at hL
      simp only at hL
      split at hL
      · cases hL
      · rename_i hnl
        have hnl' : n.leaf = false := by simpa using hnl
        cases hs : n.searchLte t cv with
        | none => rw [hs] at hL; cases hL
        | some fd =>
          rw [hs] at hL
          by_cases hfy : L = fd.y
          · subst hfy
            exact ⟨x, n, fd, by simp [eqVisits], hx, hnl', hs, rfl⟩
          · obtain ⟨q, qn, fd', hq, hqn, hql, hqs, hy⟩ := ih fd.y L hL hfy
            refine ⟨q, qn, fd', ?_, hqn, hql, hqs, hy⟩
            simp only [eqVisits, List.mem_cons, Prod.mk.injEq, and_true, hx]
            right
            simp only [hnl', Bool.false_eq_true, ↓reduceIte]
            rw [hs]
            exact hq

end SIS.Tree
