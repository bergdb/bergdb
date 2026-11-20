/-
bergdb 030-29: the second half of `Dag.dirtyNodeBound` (Contract/DirtyBound.lean):
`addCollapses` and the fold of `countNode` over the walked nodes, deepest
first.

* `addCollapses_eq`: each record's klongs get the collapses of the records
  whose parent it is.
* `fold_count`: if each node's klongs, with what its children give it
  (`contrib`), are `Kf` of it, the fold deepest first counts, for each
  record, its new segment trees and, if it overflows, its parts and the new
  roots above a tree's root (`termJ`, with klongs `Kf`). A child is one
  deeper than its parent, so the fold meets it first; each record changes
  only its parent's klongs.
-/
import Contract.Proof.DnbJava

namespace Contract.DNB

/-! ## Klongs added -/

/-- Each record's klongs, a more. -/
def bump (a : NodeId → Nat) (w : Walked) : Walked := { w with klongs := w.klongs + a w.x }

theorem keeps_bump (a : NodeId → Nat) : Keeps (bump a) := fun _ => ⟨rfl, rfl, rfl, rfl⟩

theorem get?_map_keeps {ws : Walk} {f : Walked → Walked} (hf : ∀ w, (f w).x = w.x) (y : NodeId) :
    Walk.get? (ws.map f) y = (ws.get? y).map f := by
  unfold Walk.get?
  rw [List.find?_map]
  have e : ((fun w : Walked => w.x == y) ∘ f) = (fun w : Walked => w.x == y) := by
    funext w; simp [hf]
  rw [e]

theorem bump_bump (a a' : NodeId → Nat) (w : Walked) :
    bump a' (bump a w) = bump (fun y => a y + a' y) w := by
  simp [bump, Nat.add_assoc]

theorem bump_zero (w : Walked) : bump (fun _ => 0) w = w := by simp [bump]

theorem modify_bump (ws : Walk) (a : NodeId → Nat) (u : NodeId) (d : Nat) :
    Walk.modify (ws.map (bump a)) u (fun v => { v with klongs := v.klongs + d }) =
      ws.map (bump (fun y => a y + if y = u then d else 0)) := by
  unfold Walk.modify
  rw [List.map_map]
  apply List.map_congr_left
  intro w _
  simp only [Function.comp_apply, bump]
  by_cases h : w.x = u
  · simp [h, Nat.add_assoc]
  · simp [h]

/-- The sum over the records whose parent is y of v. -/
def sumUp (ws : Walk) (v : Walked → Nat) (y : NodeId) : Nat :=
  (ws.map (fun c => if c.up = some y then v c else 0)).sum

theorem sumUp_cons (c : Walked) (ws : Walk) (v : Walked → Nat) (y : NodeId) :
    sumUp (c :: ws) v y = (if c.up = some y then v c else 0) + sumUp ws v y := by
  simp [sumUp]

/-- **`addCollapses`**: each record's klongs get the collapses of the records
whose parent it is. -/
theorem addCollapses_eq (ws : Walk) :
    addCollapses ws = ws.map (bump (sumUp ws (·.collapses))) := by
  unfold addCollapses
  suffices h : ∀ (Q : Walk) (a : NodeId → Nat),
      Q.foldl (fun (acc : Walk) w => match w.up with
        | some u => acc.modify u (fun v => { v with klongs := v.klongs + w.collapses })
        | none => acc) (ws.map (bump a)) =
        ws.map (bump (fun y => a y + sumUp Q (·.collapses) y)) by
    have e0 : ws.map (bump (fun _ => 0)) = ws := by
      conv_rhs => rw [← List.map_id ws]
      exact List.map_congr_left (fun w _ => bump_zero w)
    have := h ws (fun _ => 0)
    rw [e0] at this
    simp only [Nat.zero_add] at this
    exact this
  intro Q
  induction Q with
  | nil => intro a; simp [sumUp]
  | cons c Q ih =>
    intro a
    rw [List.foldl_cons]
    cases hc : c.up with
    | none =>
      simp only
      rw [ih]
      congr 1
      funext w
      simp [bump, sumUp_cons, hc]
    | some u =>
      simp only
      rw [modify_bump, ih]
      congr 1
      funext w
      simp only [bump, sumUp_cons, hc, Option.some.injEq]
      by_cases h : w.x = u
      · simp [h, Nat.add_assoc]
      · simp [h, Ne.symm h]

/-! ## The fold, deepest first -/

/-- The parent of w is a walked inner node (Java's `upInner`). -/
def upInner (ws : Walk) (w : Walked) : Bool :=
  match w.up with
  | some u =>
    match ws.get? u with
    | some v => !v.leaf
    | none => false
  | none => false

/-- The overflows of w with K klongs. -/
def ovOf (b : Nat) (w : Walked) (K : Nat) : Nat := overflowsD b K w.size w.deleteBelow (some w.dead)

/-- The parts of w with K klongs, if it overflows. -/
def partsOf (b : Nat) (w : Walked) (K : Nat) : Nat := max (ovOf b w K + 1) (cutPartsBound b (w.size + K))

/-- What w with K klongs gives its parent's klongs. -/
def contrib (b : Nat) (ws : Walk) (w : Walked) (K : Nat) : Nat :=
  if ovOf b w K = 0 then 0 else if upInner ws w then partsOf b w K else ovOf b w K + 1

/-- The new segment trees of w. -/
def freshSum (b : Nat) (w : Walked) : Nat :=
  (w.fresh.map (fun q =>
    freshTreeBound b (q.2.foldl (fun m (k : Key) => max m k.length) 0 + 1) q.2 (w.freshLevel + 1))).sum

/-- What the fold counts for w with K klongs. -/
def termJ (b : Nat) (ws : Walk) (w : Walked) (K : Nat) : Nat :=
  freshSum b w + (if ovOf b w K = 0 then 0 else
    partsOf b w K + (if upInner ws w then 0 else max (ovOf b w K) (rootsAbove b (partsOf b w K))))

theorem upInner_map {ws : Walk} {f : Walked → Walked} (hf : Keeps f) (w : Walked) :
    upInner (ws.map f) (f w) = upInner ws w := by
  unfold upInner
  rw [(hf w).2.1]
  cases w.up with
  | none => rfl
  | some u =>
    simp only
    rw [get?_map_keeps (fun w => (hf w).1)]
    cases ws.get? u with
    | none => rfl
    | some v => simp [(hf v).2.2.2]

/-- **One step of the fold**: the record w of node w.x, with klongs K after
the klongs a added: the count gets `termJ`, and w's parent its `contrib`. -/
theorem countNode_step (b : Nat) (ws : Walk) (hnd : (ws.map (·.x)).Nodup) (a : NodeId → Nat)
    (cnt : Nat) {w : Walked} (hw : w ∈ ws) :
    countNode b (ws.map (bump a), cnt) w.x =
      (ws.map (bump (fun y => a y + if w.up = some y then contrib b ws w (w.klongs + a w.x) else 0)),
        cnt + termJ b ws w (w.klongs + a w.x)) := by
  have hget : Walk.get? (ws.map (bump a)) w.x = some (bump a w) := by
    rw [get?_map_keeps (fun w => (keeps_bump a w).1), Walk.get?_of_mem hw hnd]; rfl
  have hui : upInner (ws.map (bump a)) (bump a w) = upInner ws w := upInner_map (keeps_bump a) w
  set K := w.klongs + a w.x with hK
  unfold countNode
  simp only [hget]
  have hbw : (bump a w).klongs = K := rfl
  simp only [hbw]
  have hfs : ((bump a w).fresh.map (fun q => freshTreeBound b
      (q.2.foldl (fun m (k : Key) => max m k.length) 0 + 1) q.2 ((bump a w).freshLevel + 1))).sum =
      freshSum b w := rfl
  rw [hfs]
  have hov : overflowsD b K (bump a w).size (bump a w).deleteBelow (some (bump a w).dead) =
      ovOf b w K := rfl
  rw [hov]
  by_cases h0 : ovOf b w K = 0
  · simp only [h0, ite_true]
    refine Prod.ext ?_ ?_
    · simp only
      congr 2; funext y; simp [contrib, h0]
    · simp [termJ, h0]
  · simp only [h0, ite_false]
    have hparts : max (ovOf b w K + 1) (cutPartsBound b ((bump a w).size + K)) = partsOf b w K := rfl
    rw [hparts]
    have hbu : (bump a w).up = w.up := rfl
    rw [hbu]
    have hassoc : (fun v : Walked => { v with klongs := v.klongs + ovOf b w K + 1 }) =
        (fun v : Walked => { v with klongs := v.klongs + (ovOf b w K + 1) }) := by
      funext v; simp [Nat.add_assoc]
    -- the parent is not an inner node: the new roots counted, its leaf above gets ov + 1
    have hnotin : ∀ u, w.up = some u → upInner ws w = false →
        (Walk.modify (ws.map (bump a)) u fun v => { v with klongs := v.klongs + ovOf b w K + 1 },
          cnt + freshSum b w + partsOf b w K + max (ovOf b w K) (rootsAbove b (partsOf b w K))) =
        (ws.map (bump (fun y => a y + if w.up = some y then contrib b ws w K else 0)),
          cnt + termJ b ws w K) := by
      intro u hu hin
      rw [hassoc, modify_bump]
      refine Prod.ext ?_ ?_
      · simp only
        congr 2; funext y
        by_cases hy : y = u
        · simp [hy, hu, contrib, h0, hin]
        · simp [hy, hu, Ne.symm hy]
      · simp [termJ, h0, hin, Nat.add_assoc]
    cases hu : w.up with
    | none =>
      have hin : upInner ws w = false := by simp [upInner, hu]
      simp only [Bool.false_eq_true, ite_false]
      refine Prod.ext ?_ ?_
      · simp
      · simp [termJ, h0, hin, Nat.add_assoc]
    | some u =>
      simp only
      rw [get?_map_keeps (fun w => (keeps_bump a w).1)]
      cases hv : ws.get? u with
      | none =>
        have hin : upInner ws w = false := by simp [upInner, hu, hv]
        simp only [Option.map_none, Bool.false_eq_true, ite_false]
        have := hnotin u hu hin; rwa [hu] at this
      | some v =>
        have hin : upInner ws w = !v.leaf := by simp [upInner, hu, hv]
        have hvl : (bump a v).leaf = v.leaf := rfl
        simp only [Option.map_some, hvl]
        cases hl : v.leaf with
        | true =>
          simp only [Bool.not_true, Bool.false_eq_true, ite_false]
          have := hnotin u hu (by rw [hin, hl]; rfl); rwa [hu] at this
        | false =>
          simp only [Bool.not_false, ite_true, Option.getD_some]
          rw [modify_bump]
          have hin' : upInner ws w = true := by rw [hin, hl]; rfl
          refine Prod.ext ?_ ?_
          · simp only
            congr 2; funext y
            by_cases hy : y = u
            · simp [hy, contrib, h0, hin']
            · simp [hy, Ne.symm hy]
          · simp [termJ, h0, hin', Nat.add_assoc]

/-- The depth of node x's record. -/
def dOf (ws : Walk) (x : NodeId) : Nat := ((ws.get? x).map (·.depth)).getD 0

/-- What the records of the nodes Q give node y. -/
def addOf (b : Nat) (ws : Walk) (Kf : NodeId → Nat) (Q : List NodeId) (y : NodeId) : Nat :=
  (Q.map (fun q => match ws.get? q with
    | some c => if c.up = some y then contrib b ws c (Kf q) else 0
    | none => 0)).sum

/-- What the fold counts for node q. -/
def termOf (b : Nat) (ws : Walk) (Kf : NodeId → Nat) (q : NodeId) : Nat :=
  match ws.get? q with
  | some w => termJ b ws w (Kf q)
  | none => 0

theorem sum_ord {ws : Walk} (hnd : (ws.map (·.x)).Nodup) {ord : List NodeId}
    (hperm : ord.Perm (ws.map (·.x))) (g : NodeId → Walked → Nat) :
    (ord.map (fun q => match ws.get? q with
      | some c => g q c
      | none => 0)).sum = (ws.map (fun c => g c.x c)).sum := by
  rw [List.Perm.sum_nat (hperm.map _), List.map_map]
  congr 1
  apply List.map_congr_left
  intro c hc
  simp only [Function.comp_apply, Walk.get?_of_mem hc hnd]

/-- **The fold, deepest first**: if each record's klongs, with a0 and what the
records whose parent it is give it (`contrib` with klongs `Kf`), are `Kf` of
it, and every record is one deeper than its parent's, then the fold over the
walked nodes in an order deepest first counts `termJ` with klongs `Kf` for
each record. -/
theorem fold_count (b : Nat) (ws : Walk) (hnd : (ws.map (·.x)).Nodup) (Kf : NodeId → Nat)
    (a0 : NodeId → Nat)
    (hup : ∀ c ∈ ws, ∀ u, c.up = some u → ∃ v ∈ ws, v.x = u ∧ v.depth + 1 = c.depth)
    (hK : ∀ w ∈ ws, w.klongs + a0 w.x + sumUp ws (fun c => contrib b ws c (Kf c.x)) w.x = Kf w.x)
    (ord : List NodeId) (hperm : ord.Perm (ws.map (·.x)))
    (hsort : ord.Pairwise (fun x y => dOf ws y ≤ dOf ws x)) (cnt : Nat) :
    (ord.foldl (countNode b) (ws.map (bump a0), cnt)).2 =
      cnt + (ws.map (fun w => termJ b ws w (Kf w.x))).sum := by
  -- the klongs node x gets from the nodes after it in the order: none
  have hafter : ∀ Q R x, ord = Q ++ x :: R → addOf b ws Kf (x :: R) x = 0 := by
    intro Q R x hord
    have hp : (x :: R).Pairwise (fun x y => dOf ws y ≤ dOf ws x) := by
      rw [hord] at hsort; exact (List.pairwise_append.mp hsort).2.1
    have hle : ∀ q ∈ x :: R, dOf ws q ≤ dOf ws x := by
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact le_refl _
      · exact List.rel_of_pairwise_cons hp hq
    unfold addOf
    apply List.sum_eq_zero
    intro v hv
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hv
    cases hc : ws.get? q with
    | none => rfl
    | some c =>
      simp only
      split
      · rename_i hcu
        exfalso
        obtain ⟨hcm, hcx⟩ := Walk.get?_some hc
        obtain ⟨v', hv', hvx, hvd⟩ := hup c hcm x hcu
        have h1 : dOf ws q = c.depth := by simp [dOf, hc]
        have h2 : dOf ws x = v'.depth := by rw [← hvx]; simp [dOf, Walk.get?_of_mem hv' hnd]
        have := hle q hq
        omega
      · rfl
  have hall : ∀ y, addOf b ws Kf ord y = sumUp ws (fun c => contrib b ws c (Kf c.x)) y := by
    intro y
    unfold addOf sumUp
    exact sum_ord hnd hperm (fun q c => if c.up = some y then contrib b ws c (Kf q) else 0)
  suffices h : ∀ (R Q : List NodeId), ord = Q ++ R →
      (R.foldl (countNode b) (ws.map (bump (fun y => a0 y + addOf b ws Kf Q y)),
        cnt + (Q.map (termOf b ws Kf)).sum)).2 = cnt + (ord.map (termOf b ws Kf)).sum by
    have := h ord [] (by simp)
    simp only [addOf, List.map_nil, List.sum_nil, Nat.add_zero] at this
    rw [this]
    congr 1
    exact sum_ord hnd hperm (fun q c => termJ b ws c (Kf q))
  intro R
  induction R with
  | nil => intro Q hQ; simp [hQ]
  | cons x R ih =>
    intro Q hQ
    have hx : x ∈ ws.map (·.x) := hperm.subset (by rw [hQ]; simp)
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
    rw [List.foldl_cons, countNode_step b ws hnd _ _ hw]
    have hQx : addOf b ws Kf Q w.x = sumUp ws (fun c => contrib b ws c (Kf c.x)) w.x := by
      rw [← hall, hQ]
      unfold addOf
      rw [List.map_append, List.sum_append]
      have := hafter Q R w.x hQ
      unfold addOf at this
      omega
    have hKw : w.klongs + (a0 w.x + addOf b ws Kf Q w.x) = Kf w.x := by
      rw [hQx, ← Nat.add_assoc]; exact hK w hw
    rw [hKw]
    have e1 : (fun y => a0 y + addOf b ws Kf Q y +
        if w.up = some y then contrib b ws w (Kf w.x) else 0) =
        (fun y => a0 y + addOf b ws Kf (Q ++ [w.x]) y) := by
      funext y
      simp [addOf, List.map_append, List.sum_append, Walk.get?_of_mem hw hnd, Nat.add_assoc]
    have e2 : cnt + (Q.map (termOf b ws Kf)).sum + termJ b ws w (Kf w.x) =
        cnt + ((Q ++ [w.x]).map (termOf b ws Kf)).sum := by
      simp [termOf, List.map_append, List.sum_append, Walk.get?_of_mem hw hnd, Nat.add_assoc]
    rw [e1, e2]
    exact ih (Q ++ [w.x]) (by rw [hQ]; simp)

/-! ## Java's count by node -/

theorem links_up {s : Tree} {E : TreeFn} : ∀ (x : NodeId) (ys : List NodeId), Links s E x ys →
    ∀ y ∈ ys, ∃ u ∈ x :: ys, E.up y = some u ∧ E.dep y = E.dep u + 1
  | _, [], _ => by simp
  | x, y :: ys, ⟨_, hu, hd, hl⟩ => by
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact ⟨x, List.mem_cons_self, hu, hd⟩
    · obtain ⟨u, hu', h1, h2⟩ := links_up y ys hl z hz
      exact ⟨u, List.mem_cons_of_mem _ hu', h1, h2⟩

/-- The parent of a walked node is walked, one less deep. -/
theorem walked_up {s : Tree} {r : NodeId} {E : TreeFn} (hru : E.up r = none)
    {kd : List (Key × Bool)} (hk : ∀ k ∈ kd, PathOk s r E k.1) {y u : NodeId}
    (hy : walkedBy s r kd y = true) (hu : E.up y = some u) :
    walkedBy s r kd u = true ∧ E.dep y = E.dep u + 1 := by
  simp only [walkedBy, List.any_eq_true, decide_eq_true_eq] at hy ⊢
  obtain ⟨k, hk', hyk⟩ := hy
  simp only [pathOf, List.mem_cons] at hyk
  rcases hyk with rfl | hyk
  · rw [hru] at hu; cases hu
  · obtain ⟨u', hu', h1, h2⟩ := links_up r _ (hk k hk').links y hyk
    rw [hu] at h1
    cases h1
    exact ⟨⟨k, hk', hu'⟩, h2⟩

/-- Whether node y's parent is an inner node. -/
def TreeFn.upIn (E : TreeFn) (y : NodeId) : Bool :=
  match E.up y with
  | some u => !E.lf u
  | none => false

/-- **Java's count by node**: on the tree s (s0 read at t), with the root r,
for the keys kd whose paths are as `PathOk` says, and the list L of the
walked nodes: if each walked node's klongs (its record's, its children's
collapses after a delete, and what its children give it with klongs Kf)
are Kf of it, then `dirtyNodeBound` is the number of walked nodes, what
the fold counts for each with klongs Kf, and four times `mergeLevels` after
a delete. -/
theorem dnb_formula (b : Nat) {s0 s : Tree} {t : Time} (hs : s0.at t = s) {r : NodeId} {rn : KNode}
    (hroot : s.root = some r) (hr : getKey s r = some rn) {E : TreeFn}
    (hcl : ∀ y, E.lf y = true → E.col y = 0)
    (hci : ∀ y b, E.up b = some y → E.lf y = false → E.col y = E.col b + 1)
    (hrl : E.lf r = rn.leaf) (hru : E.up r = none) (hrd : E.dep r = 0)
    (kd : List (Key × Bool)) (hk : ∀ k ∈ kd, PathOk s r E k.1)
    (L : List NodeId) (hL : L.Nodup) (hLm : ∀ y, y ∈ L ↔ walkedBy s r kd y = true)
    (Kf : NodeId → Nat)
    (hK : ∀ y ∈ L, (recOf s r E y kd).klongs +
      (if kd.any (delLast s r) then
        (L.map (fun c => if E.up c = some y then (recOf s r E c kd).collapses else 0)).sum else 0) +
      (L.map (fun c => if E.up c = some y then
        (let w := recOf s r E c kd
         if ovOf b w (Kf c) = 0 then 0 else if E.upIn c then partsOf b w (Kf c) else ovOf b w (Kf c) + 1)
        else 0)).sum = Kf y) :
    dirtyNodeBound b s0 t kd = L.length +
      (L.map (fun y => let w := recOf s r E y kd
        freshSum b w + (if ovOf b w (Kf y) = 0 then 0 else partsOf b w (Kf y) +
          (if E.upIn y then 0 else max (ovOf b w (Kf y)) (rootsAbove b (partsOf b w (Kf y))))))).sum +
      (if kd.any (delLast s r) then
        4 * ((kd.filter (delLast s r)).map (fun k => E.dep (endOf s r k.1).1 + 3)).sum else 0) := by
  obtain ⟨⟨hnd, hget⟩, hn, had, hml⟩ := walkAll_eq hcl hci hr hrl hru hrd kd hk
  set W := (walkAll s r rn kd).1 with hW
  -- the walked nodes: W's, as L
  have hWm : ∀ y, y ∈ W.map (·.x) ↔ walkedBy s r kd y = true := by
    intro y
    constructor
    · intro h
      have : W.get? y ≠ none := fun h' => (Walk.get?_eq_none.mp h') h
      rw [hget] at this
      by_contra hc
      simp [hc] at this
    · intro h
      have : W.get? y = some (recOf s r E y kd) := by rw [hget]; simp [h]
      exact (Walk.get?_some this).2 ▸ List.mem_map_of_mem (Walk.get?_some this).1
  have hperm : (W.map (·.x)).Perm L :=
    (List.perm_ext_iff_of_nodup hnd hL).mpr (fun y => (hWm y).trans (hLm y).symm)
  have hrec : ∀ w ∈ W, w = recOf s r E w.x kd := by
    intro w hw
    have h1 := Walk.get?_of_mem hw hnd
    have hwk : walkedBy s r kd w.x = true := (hWm w.x).mp (List.mem_map_of_mem hw)
    rw [hget] at h1
    simp only [hwk, ite_true, Option.some.injEq] at h1
    exact h1.symm
  have hR : RecOk E W := recOk_of_get (walkedBy s r kd) hget hn
  have hwf : ∀ w ∈ W, w.up = E.up w.x ∧ w.depth = E.dep w.x ∧ w.leaf = E.lf w.x :=
    fun w hw => hR w.x w (Walk.get?_of_mem hw hnd)
  -- sums over W are sums over L
  have hsum : ∀ g : NodeId → Nat, (W.map (fun w => g w.x)).sum = (L.map g).sum := by
    intro g
    have : W.map (fun w => g w.x) = (W.map (·.x)).map g := by rw [List.map_map]; rfl
    rw [this]
    exact List.Perm.sum_nat (hperm.map g)
  have hconv : ∀ (F : Walked → Nat) (G : NodeId → Nat), (∀ c ∈ W, F c = G c.x) →
      (W.map F).sum = (L.map G).sum := by
    intro F G h
    rw [← hsum G]
    congr 1
    exact List.map_congr_left h
  have hupIn : ∀ w ∈ W, upInner W w = E.upIn w.x := by
    intro w hw
    have hwk : walkedBy s r kd w.x = true := (hWm w.x).mp (List.mem_map_of_mem hw)
    unfold upInner TreeFn.upIn
    rw [(hwf w hw).1]
    cases hu : E.up w.x with
    | none => rfl
    | some u =>
      obtain ⟨huw, _⟩ := walked_up hru hk hwk hu
      have hgu : W.get? u = some (recOf s r E u kd) := by rw [hget u, huw]; rfl
      obtain ⟨hm, hx⟩ := Walk.get?_some hgu
      simp only [hgu]
      rw [(hwf _ hm).2.2, hx]
  -- Java's order: the records by depth, deepest first
  set a0 : NodeId → Nat := fun y =>
    if kd.any (delLast s r) then sumUp W (·.collapses) y else 0 with ha0
  have hws : (if (walkAll s r rn kd).2.1 then addCollapses W else W) = W.map (bump a0) := by
    rw [had]
    by_cases hd : kd.any (delLast s r) = true
    · simp only [hd, ite_true, addCollapses_eq, ha0]
    · simp only [hd, Bool.false_eq_true, ite_false, ha0]
      conv_lhs => rw [← List.map_id W]
      exact List.map_congr_left (fun w _ => (bump_zero w).symm)
  have hupW : ∀ c ∈ W, ∀ u, c.up = some u → ∃ v ∈ W, v.x = u ∧ v.depth + 1 = c.depth := by
    intro c hc u hu
    have hck : walkedBy s r kd c.x = true := (hWm c.x).mp (List.mem_map_of_mem hc)
    rw [(hwf c hc).1] at hu
    obtain ⟨huw, hdep⟩ := walked_up hru hk hck hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ((hWm u).mpr huw)
    refine ⟨v, hv, rfl, ?_⟩
    rw [(hwf v hv).2.1, (hwf c hc).2.1, hdep]
  have hKW : ∀ w ∈ W, w.klongs + a0 w.x + sumUp W (fun c => contrib b W c (Kf c.x)) w.x = Kf w.x := by
    intro w hw
    have hwL : w.x ∈ L := (hLm w.x).mpr ((hWm w.x).mp (List.mem_map_of_mem hw))
    rw [← hK w.x hwL]
    have e1 : w.klongs = (recOf s r E w.x kd).klongs := by rw [← hrec w hw]
    have e2 : a0 w.x = (if kd.any (delLast s r) then
        (L.map (fun c => if E.up c = some w.x then (recOf s r E c kd).collapses else 0)).sum else 0) := by
      simp only [ha0]
      split
      · unfold sumUp
        apply hconv
        intro c hc
        rw [(hwf c hc).1]
        split
        · rw [← hrec c hc]
        · rfl
      · rfl
    have e3 : sumUp W (fun c => contrib b W c (Kf c.x)) w.x =
        (L.map (fun c => if E.up c = some w.x then
          (let w := recOf s r E c kd
           if ovOf b w (Kf c) = 0 then 0 else if E.upIn c then partsOf b w (Kf c) else ovOf b w (Kf c) + 1)
          else 0)).sum := by
      unfold sumUp
      apply hconv
      intro c hc
      rw [(hwf c hc).1]
      split
      · simp only
        rw [← hrec c hc, contrib, hupIn c hc]
      · rfl
    rw [e1, e2, e3]
  -- the order
  set ws0 := W.map (bump a0) with hws0
  set ord := (ws0.mergeSort (fun (a b : Walked) => decide (b.depth ≤ a.depth))).map (fun w : Walked => w.x)
    with hord
  have hx0 : ws0.map (·.x) = W.map (·.x) := by rw [hws0, List.map_map]; rfl
  have hperm' : ord.Perm (W.map (·.x)) := by
    rw [hord, ← hx0]; exact (List.mergeSort_perm _ _).map _
  have hsort' : ord.Pairwise (fun x y => dOf W y ≤ dOf W x) := by
    have hs0 := List.pairwise_mergeSort (le := fun (a b : Walked) => decide (b.depth ≤ a.depth))
      (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at *; omega)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) ws0
    rw [hord, List.pairwise_map]
    apply hs0.imp_of_mem
    intro a b ha hb hab
    simp only [decide_eq_true_eq] at hab
    rw [List.mem_mergeSort, hws0, List.mem_map] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    have h1 : dOf W (bump a0 a').x = a'.depth := by simp [bump, dOf, Walk.get?_of_mem ha' hnd]
    have h2 : dOf W (bump a0 b').x = b'.depth := by simp [bump, dOf, Walk.get?_of_mem hb' hnd]
    rw [h1, h2]; exact hab
  have hfold := fold_count b W hnd Kf a0 hupW hKW ord hperm' hsort' W.length
  -- Java's count
  unfold dirtyNodeBound
  rw [hs]
  simp only [hroot, hr]
  rw [← hW, hws]
  rw [show (List.foldl (countNode b) (ws0, W.length) (List.map (fun w => w.x)
    (ws0.mergeSort fun a b => decide (b.depth ≤ a.depth)))).2 = _ from hfold, had, hml]
  have hlen : W.length = L.length := by rw [← List.length_map (f := (·.x)), hperm.length_eq]
  rw [hlen]
  congr 2
  apply hconv
  intro c hc
  rw [termJ, hupIn c hc, ← hrec c hc]

end Contract.DNB
