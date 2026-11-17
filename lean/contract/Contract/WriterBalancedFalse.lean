/-
The contract package (bergdb 030-16): 030-10's statement `WriterMeets`
(Writer.lean), in its first form, was false for a transaction with deletes.
Its balance rule, then `BalancedAll`, spoke of every key node of the map and
every key klong of an inner node, live or dead, as naming a key node one level
below, and the model's writer leaves a dead klong that names a node two levels
down. After this finding 030-10 restated the rule: `Balanced` (the
coordinator's decision of 2026-11-17), Shape.lean's BalancedOK, about the key
nodes reached from the space root and their live klongs. The theorem is kept
for the old form (`BalancedAllOld`, `balancedAllOld_false`): the writer accepts
the run, and the map of its last state does not meet the old form. The same
last state meets `Balanced` (`balanced_last`).

The run: node size 6, G = 0, H = 2 (merges and theta off, h = 3: `ParamsOK`);
the start tree of WriterExample.lean (key node 1, a segment leaf with the time
klong of 0, top node 2), on these parameters; one transaction at time 1 with
first id 3: the puts of the keys [64 j + 8] with value j for j = 0 to 13, then
the deletes of the keys [64 j + 8] for j = 3 to 6. After the last delete,
inner node 39 (level 3) holds the dead key klong (200, 1), and node 1 has
level 1. The take-back of the upward unlink points the stop node's klong of a
node it takes back to the node that node replaced, which a split of a root
made in the same transaction may make one level lower; then the bitmap deletes
that klong. The live klongs stay balanced (Shape.lean's BalancedOK).

The run is evaluated in the kernel (`decide +kernel`): `wbf_runOps` runs the
operations and checks each step's premises of `OpsRun`, and `wbf_unbal`
finds the klong. The kernel does not reduce `List.mergeSort`, so the
evaluation runs on copies of the writer's definitions with a structural sort
in its place, which equal the originals (section "The evaluation in the
kernel").
-/
import Contract.Proof.WriterRun
import Contract.Proof.WriterState

namespace Contract.WriterBalancedFalse

open Contract
open SIS (View)
open SIS.Check (BVal)

/-! ## The parameters and the start -/

/-- Node size 6, one segment level, heights 0 to 2; h = 3, merges and theta
off. -/
def p : MParams := { M := 6, G := 0, H := 2 }

theorem paramsOK : ParamsOK p := ⟨by decide, by decide, by decide⟩

/-- The primordial key node: a segment leaf of level 1 with a time klong of 0. -/
def leaf0 : KNode := { level := 1, leaf := true, ks := [.time 0] }

/-- The start tree: key node 1, the space root of time 0. -/
def s0 : Tree :=
  { obj := fun x => if x = 1 then some (.key leaf0) else none, roots := [(0, 1)] }

/-- Top node 2 of the start, of time 0, naming key node 1. -/
def zn0 : TopNode := { time := 0, root := 1, skips := [] }

def tp0 : Top := [(2, zn0)]

/-- Top node 2 in the abstract structure. -/
def top2 : SIS.Node BVal :=
  { level := p.topLevel 0, isData := false, hist := [⟨0, .rootKey 1⟩] }

/-- The view of the primordial structure without the root. -/
def v0 : View BVal := fun x =>
  if x = 1 then
    some { level := p.keyLevel 0 0, isData := false, hist := [⟨0, SIS.Tree.marker⟩] }
  else if x = 2 then some top2 else none

/-- The writer's super root at the start. -/
def t0 : SIS.Tree.Top := { id := 2, ord := 0, time := 0, rootKey := 1, skips := [] }

theorem top0 : SIS.Tree.topOf p v0 2 = .ok t0 := rfl

theorem wbf_s0_key {x : NodeId} {n : KNode} (h : s0.obj x = some (.key n)) :
    x = 1 ∧ n = leaf0 := by
  by_cases e : x = 1
  · subst e
    simp only [s0, ite_true, Option.some.injEq, Obj.key.injEq] at h
    exact ⟨rfl, h.symm⟩
  · simp [s0, e] at h

theorem before0 : Before p 1 3 s0 tp0 where
  inv := by decide
  tree := by decide
  balanced := by
    intro x _ n hx
    obtain ⟨-, rfl⟩ := wbf_s0_key hx
    exact ⟨by decide, by decide, fun h => absurd h (by decide)⟩
  books := {
    first := fun x n hx => by
      obtain ⟨-, rfl⟩ := wbf_s0_key hx
      exact ⟨0, [], rfl⟩
    times := fun x n hx => by
      obtain ⟨-, rfl⟩ := wbf_s0_key hx
      rfl
    rootTimes := by decide
    ids := fun x hx => by
      have h1 : x ≠ 1 := by omega
      have h2 : x ≠ 2 := by omega
      simp [s0, tp0, Top.node, h1, h2]
    roots := rfl
    skips := fun z zn h q hq => by
      simp only [tp0, List.getLast?_singleton, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      simp [zn0] at hq }

theorem shows0 : Shows p v0 2 s0 tp0 where
  key := by
    intro x _ n hx
    obtain ⟨rfl, rfl⟩ := wbf_s0_key hx
    exact ⟨_, rfl, rfl, rfl, by decide, by decide, rfl⟩
  top := ⟨t0, zn0, top0, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The old form of the balance rule -/

/-- The balance rule as 030-10 first stated it (`BalancedAll`), word for word:
every key klong of an inner node, live or dead, names a key node one level
below. -/
def BalancedAllOld (p : MParams) (s : Tree) : Prop :=
  ∀ x n, s.obj x = some (.key n) → 0 < n.level ∧ n.leaf = (p.heightOf n.level == 0) ∧
    (n.leaf = false → ∀ c y, Klong.key c y ∈ n.ks → ∃ m, s.obj y = some (.key m) ∧
      m.level + 1 = n.level)

/-! ## The transaction -/

/-- The key [64 j + 8]. -/
def key (j : Nat) : List Nat := [64 * j + 8]

/-- The puts of the keys for j = 0 to 13, then the deletes for j = 3 to 6. -/
def ops : List MOp :=
  (List.range 14).map (fun j => .put (key j) j) ++ [3, 4, 5, 6].map (fun j => .del (key j))

/-- The writer's context of the transaction at time 1. -/
def ctx : SIS.Tree.Ctx := { p := p, i := 1, view := v0 }

/-- The writer's state at the start of the transaction: first id 3. -/
def w0 : MW := { next := 3, top := t0 }

/-- The writer's run of the operations from w, with the premises of `OpsRun`
checked at each step: the last state, or none. -/
def wbf_runOps (c : SIS.Tree.Ctx) : MW → List MOp → Option MW
  | w, [] => some w
  | w, op :: rest =>
    if keyWf op.key then
      match SIS.Tree.putKv op c w with
      | .ok (_, w1) => if w1.outside.isEmpty then wbf_runOps c w1 rest else none
      | .error _ => none
    else none

theorem wbf_runOps_run (c : SIS.Tree.Ctx) :
    ∀ (w : MW) (l : List MOp) (w' : MW), wbf_runOps c w l = some w' → OpsRun c w l w'
  | w, [], w', h => by
    simp only [wbf_runOps, Option.some.injEq] at h
    subst h
    exact OpsRun.nil w
  | w, op :: rest, w', h => by
    simp only [wbf_runOps] at h
    split at h
    · rename_i hk
      split at h
      · rename_i b w1 hp
        split at h
        · rename_i ho
          exact OpsRun.cons w w1 w' op rest b hk hp (List.isEmpty_iff.mp ho)
            (wbf_runOps_run c w1 rest w' h)
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · exact absurd h (by simp)

/-- A key klong (c, y) of key node x of the tree T that the old form of the
balance rule refuses: x is an inner node and y is no key node one level below
it. -/
def wbf_unbal (T : Tree) (x : NodeId) (c : Nat) (y : NodeId) : Bool :=
  match T.obj x with
  | some (.key n) =>
    !n.leaf && n.ks.contains (.key c y) &&
      match T.obj y with
      | some (.key m) => m.level + 1 != n.level
      | _ => true
  | _ => false

theorem wbf_unbal_not {T : Tree} {x : NodeId} {c : Nat} {y : NodeId}
    (hb : BalancedAllOld p T) (hu : wbf_unbal T x c y = true) : False := by
  unfold wbf_unbal at hu
  split at hu
  · rename_i n hx
    obtain ⟨-, -, hk⟩ := hb x n hx
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_iff_mem] at hu
    obtain ⟨⟨hl, hc⟩, hy⟩ := hu
    obtain ⟨m, hm, hlev⟩ := hk hl c y hc
    rw [hm] at hy
    simp [hlev] at hy
  · exact absurd hu (by simp)

/-- The run, evaluated: the writer accepts the operations, and its last state
has a key klong that the old form refuses: the dead klong (200, 1) of node 39. -/
def wbf_check : Bool :=
  match wbf_runOps ctx w0 ops with
  | some w => wbf_unbal (treeOf 1 s0 w) 39 200 1
  | none => false

/-! ## The evaluation in the kernel

The kernel does not reduce `List.mergeSort` (well-founded recursion), which the
writer uses in a last version and a bitmap union. `wbf_ms` is the same sort by
structural recursion on fuel (`wbf_ms_eq`). `wbf_copyAll` copies every
definition that `wbf_check` reaches and that reaches `List.mergeSort`, as a
function of the sort (`wbf_copy.<name>`), with the equation that the copy at
`List.mergeSort` is the original (`wbf_copyEq.<name>`, by congruence). The copy at
`wbf_ms` is evaluated by the kernel. -/

/-- `List.merge` by structural recursion on fuel. -/
def wbf_merge {α : Type} (le : α → α → Bool) : Nat → List α → List α → List α
  | _, [], ys => ys
  | _, x :: xs, [] => x :: xs
  | 0, xs, ys => List.merge xs ys le
  | n + 1, x :: xs, y :: ys =>
    if le x y then x :: wbf_merge le n xs (y :: ys) else y :: wbf_merge le n (x :: xs) ys

theorem wbf_merge_eq {α : Type} (le : α → α → Bool) :
    ∀ n xs ys, wbf_merge le n xs ys = List.merge xs ys le
  | _, [], ys => by simp [wbf_merge]
  | _, x :: xs, [] => by simp [wbf_merge]
  | 0, _ :: _, _ :: _ => rfl
  | n + 1, x :: xs, y :: ys => by
    show (if le x y then x :: wbf_merge le n xs (y :: ys) else y :: wbf_merge le n (x :: xs) ys) = _
    rw [wbf_merge_eq le n, wbf_merge_eq le n, List.cons_merge_cons]

/-- `List.mergeSort` by structural recursion on fuel. -/
def wbf_sort {α : Type} (le : α → α → Bool) : Nat → List α → List α
  | _, [] => []
  | _, [a] => [a]
  | 0, xs => List.mergeSort xs le
  | n + 1, a :: b :: xs =>
    wbf_merge le (xs.length + 2)
      (wbf_sort le n ((a :: b :: xs).take ((xs.length + 3) / 2)))
      (wbf_sort le n ((a :: b :: xs).drop ((xs.length + 3) / 2)))

theorem wbf_sort_eq {α : Type} (le : α → α → Bool) :
    ∀ n xs, wbf_sort le n xs = List.mergeSort xs le
  | _, [] => by simp [wbf_sort]
  | _, [a] => by simp [wbf_sort]
  | 0, _ :: _ :: _ => rfl
  | n + 1, a :: b :: xs => by
    show wbf_merge le _ (wbf_sort le n _) (wbf_sort le n _) = _
    rw [wbf_merge_eq, wbf_sort_eq le n, wbf_sort_eq le n, List.mergeSort]
    simp

/-- The sort for the kernel. -/
def wbf_ms {α : Type} (xs : List α) (le : α → α → Bool) : List α :=
  wbf_sort le xs.length xs

theorem wbf_ms_eq : @List.mergeSort.{0} = @wbf_ms := by
  funext α xs le
  exact (wbf_sort_eq le xs.length xs).symm

open Lean Meta in
/-- Whether definition n reaches `List.mergeSort` through the values; the
definitions that do, in `order`, dependencies first. -/
partial def wbf_reach (env : Environment) (seen : IO.Ref (Std.HashMap Name Bool))
    (order : IO.Ref (Array Name)) (n : Name) : MetaM Bool := do
  if n == ``List.mergeSort then return true
  if let some b := (← seen.get)[n]? then return b
  seen.modify (·.insert n false)
  let some (.defnInfo d) := env.find? n | return false
  let mut r := false
  for c in d.value.getUsedConstants do
    if ← wbf_reach env seen order c then r := true
  seen.modify (·.insert n r)
  if r then order.modify (·.push n)
  return r

open Lean Meta in
/-- The copies of the definitions that `root` reaches and that reach
`List.mergeSort`, as functions of the sort, and their equations. -/
def wbf_copyAll (root : Name) : MetaM Unit := do
  let seen ← IO.mkRef ({} : Std.HashMap Name Bool)
  let order ← IO.mkRef #[]
  discard <| wbf_reach (← getEnv) seen order root
  let names ← order.get
  let inS : NameSet := names.foldl (·.insert ·) {}
  let ms := mkConst ``List.mergeSort [Level.zero]
  let msTy ← inferType ms
  let copyName (n : Name) : Name := `Contract.WriterBalancedFalse.wbf_copy ++ n
  let eqName (n : Name) : Name := `Contract.WriterBalancedFalse.wbf_copyEq ++ n
  for n in names do
    if (← getEnv).contains (copyName n) then continue
    let .defnInfo d ← getConstInfo n | throwError "not a definition: {n}"
    unless d.levelParams.isEmpty do throwError "universe parameters: {n}"
    let value ← withLocalDeclD `sort msTy fun s => do
      let v := d.value.replace fun e => match e with
        | .const c ls =>
          if c == ``List.mergeSort && ls == [Level.zero] then some s
          else if inS.contains c then some (mkApp (mkConst (copyName c)) s) else none
        | _ => none
      if v.getUsedConstants.contains ``List.mergeSort then throwError "a sort left in {n}"
      mkLambdaFVars #[s] v
    let hgt := match d.hints with
      | .regular h => h + 1
      | _ => 1
    let type ← mkArrow msTy d.type
    addDecl <| .defnDecl
      { name := copyName n, levelParams := [], type := type, value := value,
        hints := .regular hgt, safety := .safe }
    let deps := d.value.getUsedConstants.filter inS.contains
    let decls := deps.map fun c => (`x, fun _ => do return (← getConstInfo c).type)
    let proof ← withLocalDeclsD decls fun xs => do
      let body := d.value.replace fun e => match e with
        | .const c _ => (deps.findIdx? (· == c)).map (xs[·]!)
        | _ => none
      let mut h ← mkEqRefl (← mkLambdaFVars xs body)
      for c in deps do
        h ← mkCongr h (mkConst (eqName c))
      return h
    let eqType ← mkEq (mkConst n) (mkApp (mkConst (copyName n)) ms)
    addDecl <| .thmDecl { name := eqName n, levelParams := [], type := eqType, value := proof }

run_meta wbf_copyAll ``wbf_check

theorem wbf_check_true : wbf_check = true :=
  wbf_copyEq.Contract.WriterBalancedFalse.wbf_check.trans
    ((congrArg wbf_copy.Contract.WriterBalancedFalse.wbf_check wbf_ms_eq).trans
      (by decide +kernel))

/-! ## The last state meets `Balanced`

The same run, evaluated again: every node reached from the space root of the
map of the last state meets `Balanced`'s rule (`wbf_balB`). -/

/-- `Balanced`'s rule (Writer.lean) at node x of the tree T, computed: a key
node has a level above 0, is a segment leaf exactly at height 0, and if inner,
each live klong names a key node one level below. -/
def wbf_balB (T : Tree) (x : NodeId) : Bool :=
  match T.obj x with
  | some (.key n) =>
    decide (0 < n.level) && (n.leaf == (p.heightOf n.level == 0)) &&
      (n.leaf || (live n.ks).all (fun cy => match T.obj cy.2 with
          | some (.key m) => m.level + 1 == n.level
          | _ => false))
  | _ => true

/-- The run, evaluated: the writer accepts the operations, and every node
reached in the map of its last state meets the rule. -/
def wbf_check2 : Bool :=
  match wbf_runOps ctx w0 ops with
  | some w => (reach (treeOf 1 s0 w)).all (wbf_balB (treeOf 1 s0 w))
  | none => false

run_meta wbf_copyAll ``wbf_check2

theorem wbf_check2_true : wbf_check2 = true :=
  wbf_copyEq.Contract.WriterBalancedFalse.wbf_check2.trans
    ((congrArg wbf_copy.Contract.WriterBalancedFalse.wbf_check2 wbf_ms_eq).trans
      (by decide +kernel))

theorem wbf_balB_sound {T : Tree} {x : NodeId} {n : KNode} (h : wbf_balB T x = true)
    (hx : T.obj x = some (.key n)) :
    0 < n.level ∧ n.leaf = (p.heightOf n.level == 0) ∧
      (n.leaf = false → ∀ c y, (c, y) ∈ live n.ks → ∃ m, T.obj y = some (.key m) ∧
        m.level + 1 = n.level) := by
  unfold wbf_balB at h
  rw [hx] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true,
    List.all_eq_true] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  refine ⟨h0, h1, fun hl c y hm => ?_⟩
  rcases h2 with h2 | hlv
  · rw [hl] at h2
    cases h2
  have hy := hlv (c, y) hm
  simp only at hy
  split at hy
  · next m hm' => exact ⟨m, hm', by simpa using hy⟩
  · cases hy

/-! ## The statements -/

/-- The finding, for the old form of the balance rule: from the start tree with
its top, which meet `Before` and are shown to the writer by its view, the
writer accepts the operations (`OpsRun`), and the map of its last state does
not meet `BalancedAllOld`. So 030-10's statement in its first form was false. -/
theorem balancedAllOld_false :
    Before p 1 3 s0 tp0 ∧ Shows p v0 2 s0 tp0 ∧ SIS.Tree.topOf p v0 2 = .ok t0 ∧
      ∃ w, OpsRun ctx w0 ops w ∧ ¬ BalancedAllOld p (treeOf 1 s0 w) := by
  refine ⟨before0, shows0, top0, ?_⟩
  have hc := wbf_check_true
  unfold wbf_check at hc
  split at hc
  · rename_i w hw
    exact ⟨w, wbf_runOps_run ctx w0 ops w hw, fun hb => wbf_unbal_not hb hc⟩
  · exact absurd hc (by simp)

/-- The rule holds where the old form fails: the map of the last state of the
run meets `Balanced` (Writer.lean), and not `BalancedAllOld`. -/
theorem balanced_last :
    ∃ w, OpsRun ctx w0 ops w ∧ ¬ BalancedAllOld p (treeOf 1 s0 w) ∧
      Balanced p (treeOf 1 s0 w) := by
  have hc := wbf_check_true
  have hc2 := wbf_check2_true
  unfold wbf_check at hc
  unfold wbf_check2 at hc2
  split at hc
  · rename_i w hw
    rw [hw] at hc2
    simp only [List.all_eq_true] at hc2
    refine ⟨w, wbf_runOps_run ctx w0 ops w hw, fun hb => wbf_unbal_not hb hc, ?_⟩
    intro x hx n hn
    exact wbf_balB_sound (hc2 x hx) hn
  · exact absurd hc (by simp)

end Contract.WriterBalancedFalse
