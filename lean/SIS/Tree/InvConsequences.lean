import SIS.Tree.MergeProps

namespace SIS.Tree

open SIS SIS.Check

theorem keyNodeAt_eq_knodeOf (p : Params) (P : Struct BVal) (x : NodeId) :
    keyNodeAt p P x = knodeOf p (viewOf P) x := by
  unfold keyNodeAt knodeOf viewOf
  cases P.get? x with
  | none => rfl
  | some nd =>
    cases hd : nd.isData <;>
      by_cases hl : nd.level ≤ p.keyMax <;> simp_all

theorem mem_zip_left_witness {α β : Type} (xs : List α) (ys : List β)
    (hlen : xs.length ≤ ys.length) (a : α) (ha : a ∈ xs) :
    ∃ b, (a,b) ∈ xs.zip ys := by
  induction xs generalizing ys with
  | nil => simp at ha
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      rcases List.mem_cons.mp ha with rfl | ha
      · exact ⟨y,List.mem_cons_self⟩
      · obtain ⟨b,hb⟩ := ih ys (by simpa using hlen) ha
        exact ⟨b,List.mem_cons_of_mem _ hb⟩

def walkChildFaults (p : Params) (v : View BVal) (t f : Nat)
    (x : NodeId) (n : KNode) (g h lo : Nat) (space : Bool)
    (q : (Nat × NodeId) × Option Nat) : Faults :=
  let ((c,y),hi) := q
  if n.leaf then
    if segLen c == 7 then
      match v y with
      | some ny =>
        if ny.isData then [s!"KindsOK: segment leaf {x}: the long segment {c} names a value"]
        else if p.segOf ny.level != g + 1 then
          [s!"KindsOK: segment leaf {x}: {y} is not in the next segment"]
        else walk p v t f y 0 none true false
      | none => []
    else
      match v y with
      | some ny => if ny.isData then [] else [s!"KindsOK: segment leaf {x}: the short segment {c} names a key node"]
      | none => []
  else
    match v y with
    | some ny =>
      if ny.isData then [s!"KindsOK: inner node {x} names a value"]
      else if p.segOf ny.level != g || p.heightOf ny.level + 1 != h then
        [s!"KindsOK: inner node {x} at height {h}: child {y} at height {p.heightOf ny.level}, segment {p.segOf ny.level}"]
      else walk p v t f y (if c == 0 then lo else c) hi false space
    | none => []

theorem walk_child_faults_nil (p : Params) (v : View BVal) (t f : Nat)
    (x lo : Nat) (hi : Option Nat) (isRoot space : Bool) (nd : Node BVal)
    (hv : v x = some nd) (hd : nd.isData = false)
    (hw : walk p v t (f+1) x lo hi isRoot space = []) :
    let n : KNode := ⟨p.heightOf nd.level == 0,klongsOf nd.hist⟩
    ((n.liveAt t).zip ((n.liveAt t).drop 1 |>.map (fun q => some q.1) |>.append [hi])).flatMap
      (walkChildFaults p v t f x n (p.segOf nd.level) (p.heightOf nd.level) lo space) = [] := by
  rw [walk] at hw
  simp only [hv,hd,Bool.false_eq_true,↓reduceIte] at hw
  exact (List.eq_nil_of_append_eq_nil hw).2

theorem nodesRoots_map_fst (p : Params) (v : View BVal) (t f x : Nat) (isRoot : Bool) :
    (nodesRoots p v t f x isRoot).map Prod.fst = nodesAt p v t f x := by
  induction f generalizing x isRoot with
  | zero => rfl
  | succ f ih =>
    simp only [nodesRoots,nodesAt]
    cases hn : knodeOf p v x with
    | none => rfl
    | some n =>
      simp only [List.map_cons,List.map_flatMap]
      congr 1
      congr 1
      funext q
      rcases q with ⟨c,y⟩
      cases hl : n.leaf <;> cases hc : segLen c != 7 <;> simp [ih]

theorem walk_current_wf (p : Params) (v : View BVal) (t f : Nat)
    (x lo : Nat) (hi : Option Nat) (isRoot space : Bool) (nd : Node BVal)
    (hv : v x = some nd) (hd : nd.isData = false)
    (hw : walk p v t (f+1) x lo hi isRoot space = []) :
    klongsWf (klongsOf nd.hist) = true := by
  by_cases hf : klongsWf (klongsOf nd.hist) = true
  · exact hf
  · have hmem : s!"klongsWf: key node {x}" ∈ walk p v t (f+1) x lo hi isRoot space := by
      rw [walk]
      simp only [hv,hd,Bool.false_eq_true,↓reduceIte]
      simp [hf]
    simp [hw] at hmem

end SIS.Tree
