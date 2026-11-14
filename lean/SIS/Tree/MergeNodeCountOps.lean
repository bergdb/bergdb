/-
TP33's step for the merges into one node (`OneMergeStep`, bergdb 024-22) by
operation, as TP10's get is in `GetWriter.lean`: the count of non-root key nodes
taken on the writer's own tree (`wNode` over P@(i-1), from its super root, at
time i) is P@(i-1)'s before the first operation (`InitCountOK`, proved); each
operation changes it by at most twice its space splits less its merges into one
node (`OpCountOK`, open); and it is P@i's after the last (`CommitCountOK`), which
follows from the lift of the writer's key nodes (`CommitLiftOK`, open, TP10's
too). So TP33 follows from `OpCountOK` and `CommitLiftOK`
(`mergeAmortized_of_opCount_lift`). `OpCountOK` needs the writer's tree to be a
tree between operations (TP7 within a transaction).
-/
import SIS.Tree.MergeNodeCount
import SIS.Tree.GetCommit
import SIS.Tree.CacheGood

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The key nodes that are not segment roots, counted along the walk of
`nodesRoots` (each time the walk reaches one), from a lookup of key nodes. -/
def nrWalk (look : NodeId → Option KNode) (t : Time) : Nat → NodeId → Bool → Nat
  | 0, _, _ => 0
  | f + 1, x, isRoot =>
    match look x with
    | none => 0
    | some n =>
      (if isRoot then 0 else 1) + ((n.liveAt t).map (fun (c, y) =>
        if n.leaf then (if segLen c != 7 then 0 else nrWalk look t f y true)
        else nrWalk look t f y false)).sum

/-- The walk's count of nodes that are not segment roots is `nrWalk`. -/
theorem nodesRoots_countP (p : Params) (view : View BVal) (t : Time) (f : Nat) (x : NodeId)
    (b : Bool) :
    (nodesRoots p view t f x b).countP (fun q => !q.2) = nrWalk (knodeOf p view) t f x b := by
  induction f generalizing x b with
  | zero => simp [nodesRoots, nrWalk]
  | succ f ih =>
    simp only [nodesRoots, nrWalk]
    cases knodeOf p view x with
    | none => simp
    | some n =>
      simp only [List.countP_cons, List.countP_flatMap]
      have hm : (List.map ((List.countP fun (q : NodeId × Bool) => !q.2) ∘ fun (x : Nat × NodeId) =>
            match x with
            | (c, y) => if n.leaf = true then (if (segLen c != 7) = true then []
                else nodesRoots p view t f y true) else nodesRoots p view t f y false)
            (n.liveAt t)) =
          List.map (fun (x : Nat × NodeId) => match x with
            | (c, y) => if n.leaf = true then (if (segLen c != 7) = true then 0
                else nrWalk (knodeOf p view) t f y true) else nrWalk (knodeOf p view) t f y false)
            (n.liveAt t) := by
        apply List.map_congr_left
        intro q _
        rcases q with ⟨c, y⟩
        simp only [Function.comp]
        by_cases hl : n.leaf = true
        · by_cases hs : (segLen c != 7) = true
          · simp [hl, hs]
          · simp only [hl, hs, ite_true]
            exact ih y true
        · simp only [hl]
          exact ih y false
      rw [hm]
      cases b <;> simp <;> omega

/-- `nonRootCount` as `nrWalk` from the root at time t. -/
theorem nonRootCount_eq (p : Params) (P : Struct BVal) (t : Time) :
    nonRootCount p P t = match rootAt (viewOf P) t with
      | some r => nrWalk (knodeOf p (viewOf P)) t p.fuel r true
      | none => 0 := by
  unfold nonRootCount nodesRootsAt
  cases rootAt (viewOf P) t with
  | none => simp
  | some r => exact nodesRoots_countP p (viewOf P) t p.fuel r true

/-- The count of non-root key nodes on the writer's tree at time t: its nodes
over P, from its super root's root key node. -/
def wCount (p : Params) (P : Struct BVal) (w : W) (t : Time) : Nat :=
  nrWalk (wNode p (viewOf P) w) t p.fuel w.top.rootKey true

/-- The merges into one node so far. -/
def oneMerges (w : W) : Nat := w.merges - twoNotes w

/-- The writer's first state counts as P at the time before. Proved:
`initCountOK`. -/
def InitCountOK (p : Params) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    wCount p (treeRun p ts) (wInit tx top) (ts.length + 1) =
      nonRootCount p (treeRun p ts) ts.length

/-- Each operation of a transaction within reach, from a state that its
earlier operations reach, changes the writer's count by at most twice its space
splits less its merges into one node. Not proved: it needs the writer's tree to
be a tree between operations. -/
def OpCountOK (p : Params) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre op post, tx.ops = pre ++ op :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    WriterWP (putKv op) (ctxOf p ts) w (fun _ w' =>
      wCount p (treeRun p ts) w' (ts.length + 1) + oneMerges w' + 2 * w.spaceSplits ≤
        wCount p (treeRun p ts) w (ts.length + 1) + oneMerges w + 2 * w'.spaceSplits)

/-- The structure after a transaction counts at its time as the writer's last
state. From `CommitLiftOK`: `commitCountOK_of_lift`. -/
def CommitCountOK (p : Params) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → ∀ noops w,
    runOps p tx.base tx.ops (ts.length + 1) (view (treeSpec p) (treeRun p ts) ts.length) =
      .ok (noops, w) →
    nonRootCount p (treeRun p (ts ++ [tx])) (ts.length + 1) =
      wCount p (treeRun p ts) w (ts.length + 1)

/-! ## The walk's dependence on the nodes it reaches -/

/-! ## The first state -/

/-- The walk at two times is the same when every node looked up has the same
live klongs at both. -/
theorem nrWalk_congr_time (look : NodeId → Option KNode) (t t' : Time)
    (h : ∀ x n, look x = some n → n.liveAt t = n.liveAt t') :
    ∀ f x b, nrWalk look t f x b = nrWalk look t' f x b := by
  intro f
  induction f with
  | zero => intro x b; rfl
  | succ f ih =>
    intro x b
    simp only [nrWalk]
    cases hx : look x with
    | none => rfl
    | some n =>
      simp only
      rw [h x n hx]
      congr 2
      apply List.map_congr_left
      intro q _
      rcases q with ⟨c, y⟩
      simp only [ih]

/-- The live klongs depend on the time only through the prefix of the klongs. -/
theorem KNode.liveAt_eq_of_prefixAt (n : KNode) (t t' : Time)
    (h : prefixAt n.ks t = prefixAt n.ks t') : n.liveAt t = n.liveAt t' := by
  simp only [KNode.liveAt, KNode.delAt, h, KNode.lastVersionGivenDel, List.filterMap_cons]
  rfl

/-- The time klongs of a key node of P are at most the times of P's entries. -/
theorem knodeOf_timesLE (p : Params) (P : Struct BVal) (t : Time) (hP : StructTimesLE P t)
    (x : NodeId) (n : KNode) (hx : knodeOf p (viewOf P) x = some n) :
    ∀ y, Klong.time y ∈ n.ks → y ≤ t := by
  unfold knodeOf viewOf at hx
  cases hg : P.get? x with
  | none => rw [hg] at hx; cases hx
  | some nd =>
    rw [hg] at hx
    simp only at hx
    split at hx
    · cases hx
    · simp only [Option.some.injEq] at hx
      rw [← hx]
      intro y hy
      obtain ⟨e, he, het⟩ := klongsOf_time_mem nd.hist y hy
      rw [← het]
      exact hP (x, nd) (get?_mem P x nd hg) e he

/-- `InitCountOK`, proved: before the first operation the writer's count at
time i is P@(i-1)'s at i - 1. -/
theorem initCountOK (p : Params) : InitCountOK p := by
  intro ts tx _ z top hz htop
  have hroot := rootAt_of_writerTop p ts z top hz htop
  rw [nonRootCount_eq, hroot]
  simp only
  unfold wCount
  have hlook : wNode p (viewOf (treeRun p ts)) (wInit tx top) = knodeOf p (viewOf (treeRun p ts)) := by
    funext x
    simp [wNode, wInit]
  rw [hlook]
  have hP := treeRun_timesLE p ts
  apply nrWalk_congr_time
  intro x n hx
  have hk := knodeOf_timesLE p (treeRun p ts) ts.length hP x n hx
  apply KNode.liveAt_eq_of_prefixAt
  rw [prefixAt_eq_self n.ks (ts.length + 1) (fun y hy => Nat.le_succ_of_le (hk y hy)),
    prefixAt_eq_self n.ks ts.length hk]

/-! ## The operations -/

/-- Telescoping over the operations after a prefix. -/
theorem opCount_fold (p : Params) (ho : OpCountOK p) (ts : List Tx) (tx : Tx)
    (hw : Within p (ts ++ [tx])) (z : NodeId) (top : Top)
    (hz : lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z)
    (htop : topOf p (ctxOf p ts).view z = .ok top) :
    ∀ todo done, tx.ops = done ++ todo → ∀ r w,
      (done.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      ∀ r' w', (todo.mapM putKv) (ctxOf p ts) w = .ok (r', w') →
      wCount p (treeRun p ts) w' (ts.length + 1) + oneMerges w' + 2 * w.spaceSplits ≤
        wCount p (treeRun p ts) w (ts.length + 1) + oneMerges w + 2 * w'.spaceSplits := by
  intro todo
  induction todo with
  | nil =>
    intro done _ r w _ r' w' hrun
    simp only [List.mapM_nil, pure, ReaderT.pure, StateT.pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at hrun
    rw [← hrun.2]
    omega
  | cons op rest ih =>
    intro done hsplit r w hdone r' w' hrun
    obtain ⟨a, w1, r1, h1, h2⟩ := mapM_cons_run op rest _ w w' r' hrun
    have hstep := ho ts tx hw z top hz htop done op rest hsplit r w hdone a w1 h1
    have hdone' := mapM_snoc_run done op _ _ w w1 r a hdone h1
    have h3 := ih (done ++ [op]) (by rw [hsplit]; simp) _ w1 hdone' r1 w' h2
    omega

/-! ## The last state -/

/-- With the lift, the structure after the transaction has the writer's super
root's space root at its time (as in `commitGetOK_of_lift`). -/
theorem rootAt_commit_of_lift (p : Params) (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx]))
    (noops : List Bool) (w : W)
    (hrun : runOps p tx.base tx.ops (ts.length + 1)
      (view (treeSpec p) (treeRun p ts) ts.length) = .ok (noops, w))
    (hK : ∀ x, knodeOf p (viewOf (treeRun p (ts ++ [tx]))) x = wNode p (viewOf (treeRun p ts)) w x)
    (htaken : ∀ x ∈ w.taken, tx.base ≤ x)
    (htopt : w.newTop = true → w.taken.contains w.top.id = false) :
    rootAt (viewOf (treeRun p (ts ++ [tx]))) (ts.length + 1) = some w.top.rootKey := by
  have hbase : ∀ q ∈ treeRun p ts, q.1 < tx.base := by
    have h := (hw.2 ts.length (by simp)).1
    have hj : (ts ++ [tx])[ts.length]'(by simp) = tx := by simp
    have ht : (ts ++ [tx]).take ts.length = ts := by simp
    rw [hj, ht] at h
    exact h
  have halloc : AllocatedIds tx.base w := execW_allocatedIds p tx _ _ noops w hrun
  obtain ⟨z, top0, hz, htop, hinv⟩ := commitInv_of_runOps p ts tx noops w hrun
  obtain ⟨_, hnf, hnt, hvm, _, _⟩ := hinv
  have hroot0 := rootAt_of_writerTop p ts z top0 hz htop
  rw [treeRun_snoc_changes p ts tx noops w hrun] at hK ⊢
  generalize hP : treeRun p ts = P at hK hbase hroot0 ⊢
  generalize hi : ts.length + 1 = i at hK ⊢
  have hroot := treeRun_root p ts
  rw [hP] at hroot
  obtain ⟨ndr, hndr, hlr, hdr⟩ := hroot
  have noKey : ∀ x, knodeOf p (viewOf (P.apply i (changesOf i w))) x = none →
      w.taken.contains x = false → ∀ q ∈ w.nodes, q.1 ≠ x := by
    intro x hx ht q hq hqx
    rw [hK x] at hx
    simp only [wNode, ht, Bool.false_eq_true, ↓reduceIte] at hx
    cases hl : w.nodes.lookup x with
    | none =>
      have := List.lookup_eq_none_iff.mp hl q hq
      simp [hqx] at this
    | some n => rw [hl] at hx; cases hx
  have madeGe : ∀ m ∈ w.made, tx.base ≤ m.id := fun m hm => (halloc.2.2 m hm).1
  have hrt : w.taken.contains root = false := by
    cases h : w.taken.contains root with
    | false => rfl
    | true =>
      have := htaken root (by simpa using h)
      have hb0 : 0 < tx.base := hbase _ (get?_mem P root ndr hndr)
      simp only [root] at this
      omega
  have hkr : knodeOf p (viewOf (P.apply i (changesOf i w))) root = none := by
    have := rootLevel_gt p
    simp [knodeOf, viewOf, get?_apply_of_get? hndr, hlr, hdr, this]
  have noKeyRoot := noKey root hkr hrt
  have hradds : ∀ e ∈ addsFor (changesOf i w) i root,
      w.newTop = true ∧ e = ⟨i, .top w.top.id⟩ := by
    intro e he
    obtain ⟨het, hm⟩ := mem_addsFor.mp he
    rcases mem_changesOf_adds i w root e.val hm with ⟨q, hq, _, hqy⟩ | ⟨h', hh', _⟩ |
        ⟨hnt', hr⟩
    · exact absurd hqy (noKeyRoot q hq)
    · have := madeGe _ (hvm _ hh')
      have hb0 : 0 < tx.base := hbase _ (get?_mem P root ndr hndr)
      simp only [root] at this
      omega
    · rcases hr with ⟨_, hval⟩ | ⟨hyt, _⟩
      · refine ⟨hnt', ?_⟩
        cases e
        simp only at het hval
        rw [het, hval]
      · obtain ⟨m, hm, hmid, _, _⟩ := hnt hnt'
        have := madeGe m hm
        have hb0 : 0 < tx.base := hbase _ (get?_mem P root ndr hndr)
        rw [hmid, ← hyt] at this
        simp only [root] at this
        omega
  cases hnew : w.newTop with
  | true =>
    obtain ⟨m, hm, hmid, hmd, hml⟩ := hnt hnew
    have htt := htopt hnew
    have hge : tx.base ≤ w.top.id := hmid ▸ madeGe m hm
    have hPt := get?_none_of_ge P tx.base _ hbase hge
    have hNt := newNodeOf_changesOf_made tx.base i w halloc m hm (by rw [hmid]; exact htt)
    rw [hmid] at hNt
    have hkt : knodeOf p (viewOf (P.apply i (changesOf i w))) w.top.id = none := by
      have hml' : p.keyMax < m.level := hml
      simp [knodeOf, viewOf, get?_apply, hPt, hNt, hml']
    have noKeyTop := noKey _ hkt htt
    have hmems := top_mem_changesOf_adds i w hnew
    unfold rootAt topAt rootKeyOf viewOf
    rw [get?_apply_of_get? hndr]
    simp only
    rw [upTo_append]
    have hA : (addsFor (changesOf i w) i root).upTo i = addsFor (changesOf i w) i root :=
      List.filter_eq_self.mpr (fun e he => by
        rw [(mem_addsFor.mp he).1]; simp)
    rw [hA, getLast_append_const (ndr.hist.upTo i) (addsFor (changesOf i w) i root)
      ⟨i, .top w.top.id⟩
      (List.ne_nil_of_mem (a := (⟨i, .top w.top.id⟩ : Entry BVal)) (mem_addsFor.mpr ⟨rfl, hmems.1⟩))
      (fun e he => (hradds e he).2)]
    simp only [Option.bind_some]
    rw [get?_apply, hPt, hNt]
    simp only [Option.none_or, Option.map_some, Option.bind_some, List.nil_append]
    apply findSome_of_all
    · exact ⟨⟨i, .rootKey w.top.rootKey⟩, mem_addsFor.mpr ⟨rfl, hmems.2⟩, rfl⟩
    · intro e he
      obtain ⟨_, hm'⟩ := mem_addsFor.mp he
      rcases mem_changesOf_adds i w w.top.id e.val hm' with ⟨q, hq, _, hqy⟩ | ⟨h', hh', _⟩ |
          ⟨_, hr⟩
      · exact absurd hqy (noKeyTop q hq)
      · have := nodup_map_inj (·.id) w.made halloc.2.1 m _ hm (hvm _ hh') (by simp [hmid])
        rw [this] at hmd
        cases hmd
      · rcases hr with ⟨hyr, _⟩ | ⟨_, hv | ⟨j, z', hv⟩⟩
        · have hb0 : 0 < tx.base := hbase _ (get?_mem P root ndr hndr)
          simp only [root] at hyr; omega
        · right; rw [hv]
        · left; rw [hv]
  | false =>
    have htw := hnf hnew
    have hA : addsFor (changesOf i w) i root = [] :=
      List.eq_nil_iff_forall_not_mem.mpr (fun e he => by
        have := (hradds e he).1
        rw [hnew] at this
        cases this)
    have hshift := topAt_succ_of_timesLE P ts.length (by rw [← hP]; exact treeRun_timesLE p ts)
    rw [htw]
    unfold rootAt at hroot0 ⊢
    have htopEq : topAt (viewOf (P.apply i (changesOf i w))) i = topAt (viewOf P) ts.length := by
      rw [← hshift, hi]
      unfold topAt viewOf
      rw [get?_apply_of_get? hndr, hA, List.append_nil, hndr]
    rw [htopEq]
    cases hzt : topAt (viewOf P) ts.length with
    | none => rw [hzt] at hroot0; cases hroot0
    | some z' =>
      rw [hzt] at hroot0
      simp only [Option.bind_some] at hroot0 ⊢
      exact rootKeyOf_apply_some P i (changesOf i w) z' _ hroot0

/-- `CommitCountOK` from the lift of the writer's key nodes. -/
theorem commitCountOK_of_lift (p : Params) (hl : CommitLiftOK p) : CommitCountOK p := by
  intro ts tx hw noops w hrun
  obtain ⟨hK, htaken, htopt⟩ := hl ts tx hw noops w hrun
  have hR := rootAt_commit_of_lift p ts tx hw noops w hrun hK htaken htopt
  rw [nonRootCount_eq, hR]
  simp only
  unfold wCount
  rw [show knodeOf p (viewOf (treeRun p (ts ++ [tx]))) = wNode p (viewOf (treeRun p ts)) w from
    funext hK]

/-! ## TP33 -/

/-- TP33's step for the merges into one node from the three statements about
the writer. -/
theorem oneMergeStep_of_count (p : Params) (hi : InitCountOK p) (ho : OpCountOK p)
    (hc : CommitCountOK p) : OneMergeStep p := by
  intro ts tx hw noops w he
  have hrun : runOps p tx.base tx.ops (ts.length + 1)
      (view (treeSpec p) (treeRun p ts) ts.length) = .ok (noops, w) := he
  obtain ⟨z, top, hz, htop, hops⟩ := runOps_ok p _ _ _ _ noops w hrun
  have hfold := opCount_fold p ho ts tx hw z top hz htop tx.ops [] (by simp) [] (wInit tx top)
    (by simp only [List.mapM_nil, pure, ReaderT.pure, StateT.pure, Except.pure]) noops w hops
  have h0 := hi ts tx hw z top hz htop
  have h1 := hc ts tx hw noops w hrun
  have hm0 : oneMerges (wInit tx top) = 0 := by simp [oneMerges, wInit, twoNotes]
  have hs0 : (wInit tx top).spaceSplits = 0 := rfl
  rw [hm0, hs0, h0] at hfold
  rw [h1]
  unfold oneMerges at hfold
  omega

/-- TP33 (`MergeAmortized`) from the writer's step of the count by operation
and the lift of its key nodes (`CommitLiftOK`, which TP10's route needs too). -/
theorem mergeAmortized_of_opCount_lift (p : Params)
    (h : MergeParamsOK p → OpCountOK p ∧ CommitLiftOK p) : MergeAmortized p :=
  mergeAmortized_of_oneMergeStep p (fun hp =>
    oneMergeStep_of_count p (initCountOK p) (h hp).1 (commitCountOK_of_lift p (h hp).2))

end SIS.Tree
