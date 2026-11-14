import SIS.Tree.PutInvOK
import SIS.Tree.PointersRun
import SIS.Tree.SegmentRange

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! `PutInv` at a transaction's first state (bergdb 024-12, TP10): from P's
links (tp7's `RunLinksOK`: TP4, klongs that give the histories, a history for
every key node), P's tree (cost's `TreeAt`) and TP7's invariant at the time
before (`InvOK`, whose walk gives each node of the tree its range of compare
values: the search tree's order at the leaves, `leafOrder_of_invOK`). The
writer's books hold at the first state and after every operation
(`putBook_init`, `putBook_reached`). -/

theorem within_snoc_fresh (p : Params) (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx])) :
    ∀ q ∈ treeRun p ts, q.1 < tx.base := by
  have h := (hw.2 ts.length (by simp)).1
  have hj : (ts ++ [tx])[ts.length]'(by simp) = tx := by simp
  have ht : (ts ++ [tx]).take ts.length = ts := by simp
  rw [hj, ht] at h
  exact h

theorem knodeOf_viewOf (p : Params) (P : Struct BVal) (x : NodeId) (n : KNode)
    (h : knodeOf p (viewOf P) x = some n) :
    ∃ nd, P.get? x = some nd ∧ nd.isData = false ∧ nd.level ≤ p.keyMax ∧
      n = ⟨p.heightOf nd.level == 0, klongsOf nd.hist⟩ := by
  unfold knodeOf viewOf at h
  cases hg : P.get? x with
  | none => rw [hg] at h; cases h
  | some nd =>
    rw [hg] at h
    simp only at h
    split at h
    · cases h
    · rename_i hk
      simp only [Option.some.injEq] at h
      have hd : nd.isData = false := by cases hd : nd.isData <;> simp_all
      have hl : nd.level ≤ p.keyMax := by
        have : ¬ p.keyMax < nd.level := by intro hl; simp [hl] at hk
        omega
      exact ⟨nd, rfl, hd, hl, h.symm⟩

/-- The facts of P that the writer's run needs, from P's links. -/
theorem putBase_of_run (p : Params) (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx]))
    (hR : RunLinksOK p (treeRun p ts) ts.length) :
    PutBase (ctxOf p ts) (viewOf (treeRun p ts)) tx.base := by
  obtain ⟨hP, hH, hN⟩ := hR
  have hfresh := within_snoc_fresh p ts tx hw
  have htimes : StructTimesLE (treeRun p ts) (ts.length + 1 - 1) := treeRun_timesLE p ts
  have hl : ViewLinksOK tx.base p (view (treeSpec p) (treeRun p ts) (ts.length + 1 - 1)) :=
    viewLinksOK_of p _ _ tx.base hfresh htimes hP hN
  refine ⟨?_, ?_, viewCoherent_ctxOf p ts, ?_, ?_⟩
  · intro x nd hx
    exact hfresh _ (mem_of_get? hx)
  · intro x n hx
    obtain ⟨nd, hg, hd, hlv, hn⟩ := knodeOf_viewOf p _ x n hx
    subst hn
    refine ⟨(hH x nd hg hd hlv).1, ?_, ?_⟩
    · intro s hs
      have := knodeOf_timesLE p (treeRun p ts) ts.length (treeRun_timesLE p ts) x _ hx s hs
      show s ≤ ts.length + 1
      omega
    · intro cv y hk
      obtain ⟨e, he, hv⟩ := klongsOf_key_mem nd.hist cv y hk
      have hy := hP _ (mem_of_get? hg) e he y (by rw [hv]; simp [bptrs])
      cases hgy : (treeRun p ts).get? y with
      | none => simp [hgy] at hy
      | some ny => exact hfresh _ (mem_of_get? hgy)
  · exact viewGood_of p (treeRun p ts) (ts.length + 1) tx.base (by omega) hfresh htimes hl
  · exact viewKlongsWf_rootless p _ (viewKlongsWf_of p (treeRun p ts) _ (treeRun_timesLE p ts) hH)

/-- The writer's books at its first state. -/
theorem putBook_init (p : Params) (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx]))
    (hR : RunLinksOK p (treeRun p ts) ts.length) (z : NodeId) (top : Top)
    (htop : topOf p (ctxOf p ts).view z = .ok top) :
    PutBook (ctxOf p ts) tx.base top (wInit tx top) := by
  have hfresh := within_snoc_fresh p ts tx hw
  have ht : top.time ≠ ts.length + 1 := by
    obtain ⟨nd, hv, e, he, het⟩ := topOf_time p _ z top htop
    simp only [ctxOf, rootless] at hv
    split at hv
    · cases hv
    · obtain ⟨nd0, _, hnd⟩ := view_some p _ _ _ _ hv
      subst hnd
      have := (List.mem_filter.mp he).2
      simp only [decide_eq_true_eq] at this
      omega
  obtain ⟨h1, h2, h3⟩ := topOf_old p (treeRun p ts) ts.length (treeRun_timesLE p ts) hR.1 z top htop
  have hlt : ∀ y, ((treeRun p ts).get? y).isSome = true → y < tx.base := by
    intro y hy
    cases hg : (treeRun p ts).get? y with
    | none => rw [hg] at hy; cases hy
    | some nd => exact hfresh _ (mem_of_get? hg)
  refine ⟨?_, ⟨Nat.le_refl _, ?_⟩, book_start tx.base _ top, ?_, ?_, ?_, ?_⟩
  · intro q hq; cases hq
  · intro q hq; cases hq
  · refine ⟨Nat.le_refl _, ?_, ?_⟩
    · simp [wInit]
    · intro n hn; cases hn
  · refine ⟨ht, fun _ => rfl, fun h => by simp [wInit] at h, by simp [wInit], by simp [wInit],
      by simp [wInit]⟩
  · exact ⟨Nat.le_refl _, by simp [wInit], by simp [wInit], by simp [wInit]⟩
  · exact ptrs_start (fun y => y < tx.base) (ctxOf p ts) tx.base top
      ⟨hlt _ h1, hlt _ h2, fun q hq => hlt _ (h3 q hq)⟩

/-- The writer's books at every state that a prefix of the operations reaches. -/
theorem putBook_reached (p : Params) (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx]))
    (hR : RunLinksOK p (treeRun p ts) ts.length) (z : NodeId) (top : Top)
    (htop : topOf p (ctxOf p ts).view z = .ok top) (pre : List Op) (r : List Bool) (w : W)
    (hpre : (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w)) :
    PutBook (ctxOf p ts) tx.base top w :=
  putBook_ops (ctxOf p ts) (viewOf (treeRun p ts)) tx.base top pre
    (putBase_of_run p ts tx hw hR) _ (putBook_init p ts tx hw hR z top htop) r w hpre

/-! ## The order at the leaves, from TP7's walk -/

/-- A key node with a walk of TP7's invariant without faults. -/
def WalkCtx (p : Params) (P : Struct BVal) (t : Time) (x : NodeId) : Prop :=
  ∃ f lo hi isRoot space, walk p (viewOf P) t (f + 1) x lo hi isRoot space = []

theorem walk_zero_ne (p : Params) (v : View BVal) (t : Time) (x lo : Nat) (hi : Option Nat)
    (isRoot space : Bool) : walk p v t 0 x lo hi isRoot space ≠ [] := by
  simp [walk]

theorem walk_succ_of_nil (p : Params) (v : View BVal) (t : Time) (f x lo : Nat) (hi : Option Nat)
    (isRoot space : Bool) (h : walk p v t f x lo hi isRoot space = []) :
    ∃ f', f = f' + 1 := by
  cases f with
  | zero => exact absurd h (walk_zero_ne p v t x lo hi isRoot space)
  | succ f' => exact ⟨f', rfl⟩

theorem liveAt_succ_of_timesLE (p : Params) (P : Struct BVal) (t : Time) (hP : StructTimesLE P t)
    (x : NodeId) (n : KNode) (hx : knodeOf p (viewOf P) x = some n) :
    n.liveAt (t + 1) = n.liveAt t := by
  have ht := knodeOf_timesLE p P t hP x n hx
  rw [KNode.liveAt_of_times n (t + 1) (fun s hs => Nat.le_succ_of_le (ht s hs)),
    KNode.liveAt_of_times n t ht]

/-- The child of a link of a walked node: a key node it names is walked, with
the range that the link and the next one give it (an inner node's child), or
as a new segment tree (a segment leaf's child). -/
theorem walk_child (p : Params) (P : Struct BVal) (t : Time) (f x lo : Nat) (hi : Option Nat)
    (isRoot space : Bool) (n : KNode) (hx : knodeOf p (viewOf P) x = some n)
    (hw : walk p (viewOf P) t (f + 1) x lo hi isRoot space = [])
    (cz : Nat × NodeId) (b : Option Nat) (hcb : (cz, b) ∈ childBounds (n.liveAt t) hi)
    (m : KNode) (hz : knodeOf p (viewOf P) cz.2 = some m) :
    walk p (viewOf P) t f cz.2 (if n.leaf then 0 else if cz.1 == 0 then lo else cz.1)
      (if n.leaf then none else b) n.leaf (if n.leaf then false else space) = [] := by
  obtain ⟨nd, hg, hd, _, hn⟩ := knodeOf_viewOf p P x n hx
  obtain ⟨ny, hgy, hdy, _, _⟩ := knodeOf_viewOf p P cz.2 m hz
  have hv : viewOf P x = some nd := hg
  have hvy : viewOf P cz.2 = some ny := hgy
  have hchild := List.flatMap_eq_nil_iff.mp
    (walk_child_faults_nil p (viewOf P) t f x lo hi isRoot space nd hv hd hw) (cz, b)
    (by subst hn; exact hcb)
  subst hn
  obtain ⟨c, y⟩ := cz
  simp only at hvy hgy ⊢
  simp only [walkChildFaults, hvy, hdy, Bool.false_eq_true, ↓reduceIte] at hchild
  cases hleaf : (p.heightOf nd.level == 0) with
  | true =>
    simp only [hleaf, ↓reduceIte] at hchild ⊢
    split at hchild
    · split at hchild
      · cases hchild
      · exact hchild
    · cases hchild
  | false =>
    simp only [hleaf, Bool.false_eq_true, ↓reduceIte] at hchild ⊢
    split at hchild
    · cases hchild
    · exact hchild

/-- Every key node reachable at time t + 1 from P's space root at t (P without
entries after t) has a walk without faults. -/
theorem walkCtx_of_reach (p : Params) (P : Struct BVal) (t : Time) (hP : StructTimesLE P t)
    (r : NodeId) (hr : rootAt (viewOf P) t = some r) (hI : InvOK p P t) :
    ∀ x, ReachS (knodeOf p (viewOf P)) (t + 1) r x →
      ∀ m, knodeOf p (viewOf P) x = some m → WalkCtx p P t x := by
  intro x hx
  induction hx with
  | root =>
    intro m _
    unfold InvOK faultsAt at hI
    rw [hr] at hI
    simp only at hI
    have hf : p.fuel = (p.G + 1) * (p.H + 2) + 1 + 1 := by unfold Params.fuel; omega
    rw [hf] at hI
    exact ⟨_, 0, none, true, true, hI⟩
  | step x n c z _ hn hc ih =>
    intro m hm
    obtain ⟨f, lo, hi, isRoot, space, hw⟩ := ih n hn
    rw [liveAt_succ_of_timesLE p P t hP x n hn] at hc
    obtain ⟨b, hb⟩ := childBounds_exists (n.liveAt t) hi (c, z) hc
    have h := walk_child p P t f x lo hi isRoot space n hn hw (c, z) b hb m hm
    obtain ⟨f', hf'⟩ := walk_succ_of_nil p _ t f _ _ _ _ _ h
    subst hf'
    exact ⟨f', _, _, _, _, h⟩

/-- TP7's walk gives the order at the leaves: below every reachable inner node
q, the compare values of a leaf child lie between q's klong to it and q's next
klong. -/
theorem leafOrder_of_invOK (p : Params) (P : Struct BVal) (t : Time) (hP : StructTimesLE P t)
    (r : NodeId) (hr : rootAt (viewOf P) t = some r) (hI : InvOK p P t) :
    ∀ q qn L n k1, ReachS (knodeOf p (viewOf P)) (t + 1) r q →
      knodeOf p (viewOf P) q = some qn → qn.leaf = false → knodeOf p (viewOf P) L = some n →
      n.leaf = true → (k1, L) ∈ qn.live → LeafOrderAt qn k1 n := by
  intro q qn L n k1 hq hqn hql hn hnl hk
  obtain ⟨f, lo, hi, isRoot, space, hw⟩ := walkCtx_of_reach p P t hP r hr hI q hq qn hqn
  have hqt := knodeOf_timesLE p P t hP q qn hqn
  have hnt := knodeOf_timesLE p P t hP L n hn
  have hk' : (k1, L) ∈ qn.liveAt t := by rw [KNode.liveAt_of_times qn t hqt]; exact hk
  obtain ⟨b, hb⟩ := childBounds_exists (qn.liveAt t) hi (k1, L) hk'
  have h := walk_child p P t f q lo hi isRoot space qn hqn hw (k1, L) b hb n hn
  simp only [hql, Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨f', hf'⟩ := walk_succ_of_nil p _ t f _ _ _ _ _ h
  subst hf'
  obtain ⟨nd, hg, hd, _, hnd⟩ := knodeOf_viewOf p P L n hn
  have hrange := walk_current_range p (viewOf P) t f' L _ b false space nd hg hd h
  rw [← hnd] at hrange
  have hsorted := KNode.liveAt_order qn t
  intro c' z hz
  have hz' : (c', z) ∈ n.liveAt t := by rw [KNode.liveAt_of_times n t hnt]; exact hz
  obtain ⟨hlow, hhigh⟩ := hrange (c', z) hz'
  simp only [hnl, ↓reduceIte] at hlow
  refine ⟨?_, ?_⟩
  · by_cases h0 : k1 = 0
    · omega
    · have : (k1 == 0) = false := by simpa using h0
      simp only [this, Bool.false_eq_true, ↓reduceIte] at hlow
      exact hlow
  · intro c'' z' hz'' hlt
    have hz''' : (c'', z') ∈ qn.liveAt t := by rw [KNode.liveAt_of_times qn t hqt]; exact hz''
    obtain ⟨upper, hub, hle⟩ := childBounds_next_le (qn.liveAt t) hi hsorted (k1, L) b hb
      (c'', z') hz''' hlt
    rw [hub] at hhigh
    simp only [UpperBound] at hhigh
    simp only at hle
    omega

/-! ## `PutInv` at the first state -/

/-- `PutInv` at a transaction's first state: from P's links (`RunLinksOK`),
P's tree (`TreeAt`) and TP7's invariant at the time before (`InvOK`). -/
theorem putInv_init (p : Params) (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx]))
    (hR : RunLinksOK p (treeRun p ts) ts.length) (hT : TreeAt p (treeRun p ts) ts.length)
    (hI : InvOK p (treeRun p ts) ts.length) (z : NodeId) (top : Top)
    (hz : lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z)
    (htop : topOf p (ctxOf p ts).view z = .ok top) :
    PutInv (ctxOf p ts) (viewOf (treeRun p ts)) (wInit tx top) := by
  have hB := putBase_of_run p ts tx hw hR
  have hG := putInvG_of_book _ _ _ _ _ hB (putBook_init p ts tx hw hR z top htop)
  have hTw := writerTreeOK_init p ts tx z top hz htop hT
  have hlook : wNode p (viewOf (treeRun p ts)) (wInit tx top) = knodeOf p (viewOf (treeRun p ts)) := by
    funext x
    simp [wNode, wInit]
  have hroot := rootAt_of_writerTop p ts z top hz htop
  refine putInv_of_parts _ _ _ hG hTw ?_ ?_
  · intro x _; simp [wInit]
  · intro q qn L n k1 hq hqn hql hn hnl hk
    change ReachS (wNode p (viewOf (treeRun p ts)) (wInit tx top)) (ts.length + 1)
      (wInit tx top).top.rootKey q at hq
    change wNode p (viewOf (treeRun p ts)) (wInit tx top) q = some qn at hqn
    change wNode p (viewOf (treeRun p ts)) (wInit tx top) L = some n at hn
    rw [hlook] at hq hqn hn
    exact leafOrder_of_invOK p (treeRun p ts) ts.length (treeRun_timesLE p ts) top.rootKey hroot
      hI q qn L n k1 hq hqn hql hn hnl hk

end SIS.Tree
