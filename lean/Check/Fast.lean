/-
Fast versions of the model's definitions for the trace checker (bergdb item
001, WP C2). Each is proven equal to the model's definition, and the equality
is marked `@[csimp]`: the compiled checker runs the fast version wherever the
model's code calls the definition, while the definitions and the proofs about
them stay as they are. Not part of the trusted part; nothing here changes what
the model says.

What C1 measured (a medium trace, 500 transactions, 1,717 nodes): step 3,
`markOf`, took 99 percent of the time, since `marked` computes `reachable`,
and so the whole `reachList`, again for every node. P is a list, so every
`Struct.get?` scans it; the stream is a list too, so `Stream.lv` scans the
records from the end.
-/
import SIS.Proof.StreamLemmas
import Std.Data.HashMap
import Std.Data.HashSet

namespace SIS.Fast

open SIS

variable {V T : Type}

/-! ### P through a hash map -/

/-- The nodes of P by id, as `Struct.get?` finds them: the first entry of an id
wins, since it is inserted last. -/
def nodeMap (P : Struct V) : Std.HashMap NodeId (Node V) :=
  P.foldr (fun p m => m.insert p.1 p.2) {}

theorem nodeMap_get? (P : Struct V) (x : NodeId) : (nodeMap P)[x]? = P.get? x := by
  induction P with
  | nil => simp [nodeMap, Struct.get?]
  | cons p P ih =>
    obtain ⟨k, n⟩ := p
    unfold nodeMap at ih ⊢
    rw [List.foldr_cons, Std.HashMap.getElem?_insert, ih]
    simp only [Struct.get?, List.lookup_cons]
    by_cases h : k = x
    · subst h; simp
    · have h' : (x == k) = false := by simp; omega
      have h'' : (k == x) = false := by simp; omega
      simp [h', h'']

/-- `reachFrom`, with the lookups of P through a function. -/
def reachFromG (sp : Spec V T) (g : NodeId → Option (Node V)) (t : Time) (x : NodeId)
    (n : Node V) : List NodeId :=
  x :: (sp.live (n.hist.upTo t)).flatMap (fun y =>
    match g y with
    | some m => if m.level < n.level then reachFromG sp g t y m else []
    | none => [])
termination_by n.level

theorem reachFromG_eq (sp : Spec V T) (P : Struct V) (t : Time) :
    ∀ (b : Nat) (x : NodeId) (n : Node V), n.level < b →
      reachFromG sp (fun y => P.get? y) t x n = reachFrom sp P t x n := by
  intro b
  induction b with
  | zero => intro x n h; omega
  | succ b ih =>
    intro x n hb
    rw [reachFromG, reachFrom]
    congr 1
    congr 1
    funext y
    cases hy : P.get? y with
    | none => rfl
    | some m =>
      simp only
      split
      · exact ih y m (by omega)
      · rfl

theorem reachFromG_nodeMap (sp : Spec V T) (P : Struct V) (t : Time) (x : NodeId) (n : Node V) :
    reachFromG sp (fun y => (nodeMap P)[y]?) t x n = reachFrom sp P t x n := by
  have : (fun y => (nodeMap P)[y]?) = (fun y => P.get? y) := by
    funext y; exact nodeMap_get? P y
  rw [this]
  exact reachFromG_eq sp P t (n.level + 1) x n (by omega)

/-- `reachList` through the hash map of P. -/
def reachListFast (sp : Spec V T) (P : Struct V) (t : Time) : List NodeId :=
  let m := nodeMap P
  match m[root]? with
  | some n => reachFromG sp (fun y => m[y]?) t root n
  | none => []

@[csimp] theorem reachList_eq_fast : @reachList = @reachListFast := by
  funext V T sp P t
  unfold reachList reachListFast
  simp only
  rw [nodeMap_get?]
  cases P.get? root with
  | none => rfl
  | some n => exact (reachFromG_nodeMap sp P t root n).symm

/-! ### Duplicates and membership through hash sets -/

/-- `List.eraseDups` of node ids with a hash set of the ids seen. -/
def eraseDupsFast (l : List NodeId) : List NodeId :=
  (l.foldl (fun (acc : Array NodeId × Std.HashSet NodeId) x =>
    if acc.2.contains x then acc else (acc.1.push x, acc.2.insert x)) (#[], {})).1.toList

theorem eraseDupsFast_eq (l : List NodeId) : eraseDupsFast l = l.eraseDups := by
  -- The loop keeps: the array is the prefix without duplicates, the set holds the prefix.
  have key : ∀ (l pre : List NodeId) (a : Array NodeId) (s : Std.HashSet NodeId),
      a.toList = pre.eraseDups → (∀ y, s.contains y = pre.contains y) →
      (l.foldl (fun (acc : Array NodeId × Std.HashSet NodeId) x =>
        if acc.2.contains x then acc else (acc.1.push x, acc.2.insert x)) (a, s)).1.toList =
        (pre ++ l).eraseDups := by
    intro l
    induction l with
    | nil => intro pre a s ha _; simpa using ha
    | cons x l ih =>
      intro pre a s ha hs
      rw [List.foldl_cons]
      have hstep : (pre ++ x :: l) = (pre ++ [x]) ++ l := by simp
      rw [hstep]
      by_cases hx : s.contains x = true
      · have hmem : x ∈ pre := by rw [hs] at hx; simpa using hx
        simp only [hx, ite_true]
        apply ih (pre ++ [x]) a s
        · rw [ha, List.eraseDups_append]
          have : [x].removeAll pre = [] := by
            simp [List.removeAll, hmem]
          rw [this]; simp
        · intro y
          rw [hs, List.contains_append]
          by_cases hy : y = x
          · subst hy; simp [hmem]
          · simp [hy]
      · have hnmem : x ∉ pre := by rw [hs] at hx; simpa using hx
        simp only [hx, Bool.false_eq_true, ite_false]
        apply ih (pre ++ [x])
        · rw [Array.toList_push, ha, List.eraseDups_append]
          have : [x].removeAll pre = [x] := by
            simp [List.removeAll, hnmem]
          rw [this]; simp [List.eraseDups_cons]
        · intro y
          rw [Std.HashSet.contains_insert, hs, List.contains_append]
          by_cases hy : y = x
          · subst hy; simp
          · have h1 : (x == y) = false := by simp; omega
            simp [h1, hy]
  have := key l [] #[] {} (by simp) (by intro y; simp)
  simpa [eraseDupsFast] using this

/-- `allIds` with a hash set. -/
def allIdsFast (P : Struct V) : List NodeId := eraseDupsFast (P.map (·.1))

theorem allIds_eq_fast' (P : Struct V) : allIds P = allIdsFast P := by
  unfold allIds allIdsFast
  rw [eraseDupsFast_eq]

/-! ### Step 3: marking, with the reachable nodes computed once -/

/-- `markOf`: the reachable nodes are computed once, not again for every node,
and P, D and the changed nodes are looked up through hash maps and sets. -/
def markOfFast (sp : Spec V T) (P : Struct V) (c : Changes V) (D : Dirty) (i : Time) :
    List NodeId :=
  let m := nodeMap P
  let g := fun y => m[y]?
  let rl : Std.HashSet NodeId := Std.HashSet.ofList (match g root with
    | some n => reachFromG sp g i root n
    | none => [])
  let ds : Std.HashSet NodeId := Std.HashSet.ofList (D.map (·.1))
  let cs : Std.HashSet NodeId := Std.HashSet.ofList (c.new.map (·.id) ++ c.adds.map (·.1))
  ((allIdsFast P).filter (fun x =>
    (match g x with
     | some n => !n.isData
     | none => false) && !ds.contains x &&
    (rl.contains x && match g x with
      | some n => (reachFromG sp g i x n).any (fun z => cs.contains z)
      | none => false))).mergeSort (fun a b => decide (a ≤ b))

@[csimp] theorem markOf_eq_fast : @markOf = @markOfFast := by
  funext V T sp P c D i
  unfold markOf markOfFast marked reachable isIndex
  simp only
  rw [← allIds_eq_fast']
  congr 1
  apply List.filter_congr
  intro x _
  simp only [nodeMap_get?]
  have hrl : (match P.get? root with
      | some n => reachFromG sp (fun y => P.get? y) i root n
      | none => []) = reachList sp P i := by
    unfold reachList
    cases P.get? root with
    | none => rfl
    | some n => exact reachFromG_eq sp P i (n.level + 1) root n (by omega)
  rw [hrl, Std.HashSet.contains_ofList, Std.HashSet.contains_ofList]
  have hD : (D.map (·.1)).contains x = inD D x := by
    unfold inD
    apply Bool.eq_iff_iff.mpr
    simp [List.any_eq_true]
  rw [hD]
  cases hx : P.get? x with
  | none => simp
  | some n =>
    simp only
    rw [reachFromG_eq sp P i (n.level + 1) x n (by omega)]
    congr 1
    congr 1
    apply List.any_congr rfl
    intro z
    rw [Std.HashSet.contains_ofList]
    unfold changed
    apply Bool.eq_iff_iff.mpr
    simp [List.any_eq_true]

/-! ### Steps 2 and 6: writing versions, with the latest versions in a hash map -/

/-- The latest version of each node in S, as `Stream.lv` finds it: later
records win, and in a record the first version of a node. -/
def lvMap (S : Stream V T) : Std.HashMap NodeId (Version V) :=
  S.foldl (fun m R => R.vers.foldr (fun v m => m.insert v.node v) m) {}

theorem lvMap_record (vs : List (Version V)) (m : Std.HashMap NodeId (Version V)) (x : NodeId) :
    (vs.foldr (fun v m => m.insert v.node v) m)[x]? = (vs.find? (fun v => v.node == x)).or m[x]? := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
    rw [List.foldr_cons, Std.HashMap.getElem?_insert, ih, List.find?_cons]
    by_cases h : v.node = x
    · simp [h]
    · have h' : (v.node == x) = false := by simp [h]
      simp [h']

theorem lvMap_get? (S : Stream V T) (x : NodeId) : (lvMap S)[x]? = S.lv x := by
  have key : ∀ (S : Stream V T) (m : Std.HashMap NodeId (Version V)),
      (S.foldl (fun m R => R.vers.foldr (fun v m => m.insert v.node v) m) m)[x]? =
        (S.lv x).or m[x]? := by
    intro S
    induction S with
    | nil => intro m; simp [Stream.lv]
    | cons R S ih =>
      intro m
      rw [List.foldl_cons, ih, lvMap_record, lv_cons, Option.or_assoc]
  have := key S {}
  simpa [lvMap] using this

/-- `mkVersion`, with the latest versions through a function. -/
def mkVersionG (sp : Spec V T) (lvb : NodeId → Option (Version V)) (i : Nat) (x : NodeId)
    (n : Node V) : Version V :=
  { node := x, recNo := i, level := n.level, isData := n.isData, hist := n.hist,
    refs := (pointees sp n.hist).filterMap (fun y => (lvb y).map (fun w => (y, w.recNo))) }

/-- `writeAll`: the latest versions of the stream before the record through a
hash map, built once, and P through a hash map. -/
def writeAllFast (sp : Spec V T) (S : Stream V T) (i : Nat) (P : Struct V) (xs : List NodeId)
    (vs : List (Version V)) : List (Version V) :=
  let lm := lvMap S
  let pm := nodeMap P
  xs.foldl (fun vs x =>
    match pm[x]? with
    | some n => vs ++ [mkVersionG sp (fun y => (vs.find? (fun v => v.node == y)).or lm[y]?) i x n]
    | none => vs) vs

@[csimp] theorem writeAll_eq_fast : @writeAll = @writeAllFast := by
  funext V T sp S i P xs vs
  unfold writeAll writeAllFast
  simp only
  congr 1
  funext vs x
  rw [nodeMap_get?]
  cases P.get? x with
  | none => rfl
  | some n =>
    simp only [mkVersion, mkVersionG]
    congr 4
    funext y
    rw [lv_building, lvMap_get?]

/-! ### The step, compiled again

A `@[csimp]` equation changes the code compiled after it. The model's `step`
was compiled before these equations, with calls to the slow definitions; so
`stepFast` is `step` again, word for word, compiled here, with the fast
versions in place of `markOf` and `writeAll`, and the checker's calls of
`step` run it (`step_eq_fast`). -/

/-- `step` (SIS/Algorithm.lean), word for word. -/
def stepFast [DecidableEq V] (sp : Spec V T) (al : Algo V T) (db : DB V T) (tr : T) : DB V T :=
  let i := db.S.length
  let c := sp.exec tr i (view sp db.P (i - 1))
  let P := db.P.apply i c
  let vs0 := writeAll sp db.S i P ((c.new.filter (·.isData)).map (·.id)) []
  let gd3 := (if al.mark then markOf sp P c db.D i else gotDirtyOf sp (db.S.building vs0) P db.D i).filter
    (written sp)
  let D1 : Dirty := db.D ++ gd3.map (fun x => (x, i))
  let s : Nat := startupPos al db.S D1 i tr
  let taken := byLevel P ((D1.filter (fun e : NodeId × Nat => decide (e.2 ≤ s))).map (·.1))
  let D2 : Dirty := D1.filter (fun e : NodeId × Nat => decide (s < e.2))
  let vs := writeAll sp db.S i P taken vs0
  let S' : Stream V T := db.S.building vs
  let r7 := stillDirtyOf al S' P D2 i taken
  let R : Record V T :=
    { trans := some tr, sp := s, vers := vs, gd := gd3 ++ r7.2, top := topOf sp P S' s }
  { P := P, D := r7.1, S := db.S ++ [R] }

@[csimp] theorem step_eq_fast : @step = @stepFast := by
  funext V T _ sp al db tr
  rfl

end SIS.Fast
