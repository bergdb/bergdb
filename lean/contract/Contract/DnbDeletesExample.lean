/-
bergdb 030-36: the mixed-operation bound is not vacuous. At all four Java
node sizes, a two-transaction history first puts two keys, then deletes one
and puts a third. The deletion changes the live contents. The new history
bound applies with its fill and no-join premises proved, and one key node
is written in the second transaction.
-/
import Contract.Proof.DnbMain

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace Contract.PE.DnbDeletesExample

open DNB

def Supported (b : Nat) : Prop := b = 8 ∨ b = 14 ∨ b = 30 ∨ b = 62

theorem size_ge {b : Nat} (hb : Supported b) : 8 ≤ b := by
  rcases hb with rfl | rfl | rfl | rfl <;> decide

def cfJ (b : Nat) : Cfg := Cfg.java b 3 15

def firstOps : List Op := [.put [72] 5, .put [80] 6]
def secondOps : List Op := [.del [72], .put [88] 7]

theorem first_some {b : Nat} (hb : Supported b) :
    (peTx (cfJ b) 1 (startTree (cfJ b)) startTop startNext firstOps).isSome = true := by
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

def first (b : Nat) (hb : Supported b) : Out :=
  (peTx (cfJ b) 1 (startTree (cfJ b)) startTop startNext firstOps).get (first_some hb)

def state (b : Nat) (hb : Supported b) : Tree := (first b hb).tree (startTree (cfJ b))

theorem fill1 {b : Nat} (hb : Supported b) : FillOk b 15 (state b hb) := by
  rcases hb with rfl | rfl | rfl | rfl <;> unfold FillOk <;> decide +kernel

/-- The root is a leaf, computed independently of the proof condition. -/
def rootIsLeaf (s : Tree) : Bool :=
  match s.root with
  | none => false
  | some r => match DNB.getKey s r with
    | none => false
    | some n => n.leaf

theorem leaf1 {b : Nat} (hb : Supported b) : rootIsLeaf (state b hb) = true := by
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

theorem second_keys (b : Nat) : ∀ op ∈ secondOps, keyOk (cfJ b) op.key = true := by
  intro op hop
  simp only [secondOps, List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl <;> rfl

theorem second_length : ∀ op ∈ secondOps, op.key.length = 1 := by
  intro op hop
  simp only [secondOps, List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl <;> rfl

theorem noJoins1 {b : Nat} (hb : Supported b) : NoJoins (cfJ b) 2 (state b hb) secondOps := by
  have hl := leaf1 hb
  cases hr : (state b hb).root with
  | none => simp [NoJoins, hr]
  | some r =>
    cases hk : DNB.getKey (state b hb) r with
    | none => simp [rootIsLeaf, hr, hk] at hl
    | some n =>
      have hn : n.leaf = true := by simpa only [rootIsLeaf, hr, hk] using hl
      simpa only [NoJoins, hr] using noJoinsAt_leaf (cf := cfJ b) (i := 2)
        (fs := (state b hb).fuel r) (g := 0) hk hn second_length

theorem second_some {b : Nat} (hb : Supported b) :
    (peTx (cfJ b) 2 (state b hb) (first b hb).top (first b hb).next secondOps).isSome = true := by
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

def second (b : Nat) (hb : Supported b) : Out :=
  (peTx (cfJ b) 2 (state b hb) (first b hb).top (first b hb).next secondOps).get (second_some hb)

theorem history1 {b : Nat} (hb : Supported b) :
    PeHist (cfJ b) (startTree (cfJ b)) startTop startNext [firstOps]
      (state b hb) (first b hb).top (first b hb).next := by
  exact PeHist.step PeHist.start (Option.some_get (first_some hb)).symm

/-- The new top history theorem applies to a transaction that really deletes. -/
theorem bound {b : Nat} (hb : Supported b) :
    keyWrites (second b hb).ws ≤ dirtyNodeBound b (state b hb) 1 (opsKd secondOps) := by
  exact pe_dirtyNodeBound_noJoins_hist (size_ge hb) (history1 hb) (fill1 hb)
    (second_keys b) (noJoins1 hb) (Option.some_get (second_some hb)).symm

def rootHas (s : Tree) (c : Nat) : Bool :=
  match s.root with
  | none => false
  | some r => match DNB.getKey s r with
    | none => false
    | some n => ((live n.ks).lookup c).isSome

/-- One key node written, the old key present before and gone after, and
the new key present after. These facts do not use the bound theorem. -/
theorem changes {b : Nat} (hb : Supported b) :
    keyWrites (second b hb).ws = 1 ∧ rootHas (state b hb) 72 = true ∧
      rootHas ((second b hb).tree (state b hb)) 72 = false ∧
      rootHas ((second b hb).tree (state b hb)) 88 = true := by
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

/-- Deleting exactly the three entries of a leaf empties its plan, at
every fuel at which the call succeeds and for every accumulator. -/
theorem del3_empty {cf : Cfg} {s : Tree} {i : Time} {x a y0 y1 y2 : Nat} {n : KNode}
    (hk : getKey s x = some n)
    (hlv : live n.ks = [(a, y0), (a + 64, y1), (a + 128, y2)]) :
    ∀ (f : Nat) (acc : Acc) (v : VN) (acc' : Acc),
      plan cf i s f x 0 0 [.del [a], .del [a + 64], .del [a + 128]] acc = some (v, acc') →
      v.isEmpty = true := by
  intro f acc v acc' hp
  rcases f with _ | _ | _ | _ | _ | f
  all_goals simp only [plan, hk, beq_self_eq_true, ↓reduceIte, hlv] at hp
  all_goals simp [List.eraseDups_cons, applyGroups, segAt, Op.key, endsAt, removeEntry, mkNode, hk] at hp
  all_goals obtain ⟨rfl, rfl⟩ := hp
  all_goals rfl

/-- Two emptied child plans followed by an untouched child leave a lone
child after the filter, at every successful fuel and accumulator. -/
theorem two_drops {cf : Cfg} {s : Tree} {i : Time} {c0 c1 c2 x0 x1 x2 : Nat}
    {ops0 ops1 : List Op} (hn0 : ops0 ≠ []) (hn1 : ops1 ≠ [])
    (h0 : ∀ f a v a', plan cf i s f x0 0 0 ops0 a = some (v, a') → v.isEmpty = true)
    (h1 : ∀ f a v a', plan cf i s f x1 0 0 ops1 a = some (v, a') → v.isEmpty = true) :
    ∀ f a es a', planKids cf i s f 0 1 [(c0, x0), (c1, x1), (c2, x2)]
      [ops0, ops1, []] a = some (es, a') → (es.filter (fun e => !e.2.isEmpty)).length < 2 := by
  intro f a es a' hp
  have hn0' : ops0.isEmpty = false := by simpa using hn0
  have hn1' : ops1.isEmpty = false := by simpa using hn1
  cases f with
  | zero => simp [planKids] at hp
  | succ f =>
    simp only [planKids, hn0', Bool.false_eq_true, ↓reduceIte] at hp
    cases hpl0 : plan cf i s f x0 0 0 ops0 a with
    | none => rw [hpl0] at hp; cases hp
    | some q0 =>
      obtain ⟨v0, a0⟩ := q0
      rw [hpl0] at hp
      have he0 := h0 f a v0 a0 hpl0
      cases f with
      | zero => simp [planKids] at hp
      | succ f =>
        simp only [planKids, hn1', Bool.false_eq_true, ↓reduceIte] at hp
        cases hpl1 : plan cf i s f x1 0 0 ops1 a0 with
        | none => rw [hpl1] at hp; cases hp
        | some q1 =>
          obtain ⟨v1, a1⟩ := q1
          rw [hpl1] at hp
          dsimp only at hp
          have he1 := h1 f a0 v1 a1 hpl1
          cases hk : planKids cf i s f 0 1 [(c2, x2)] [[]] a1 with
          | none => rw [hk] at hp; cases hp
          | some q2 =>
            obtain ⟨tail, a2⟩ := q2
            rw [hk] at hp
            obtain ⟨htail, _⟩ := dnb_planKids_nil [(c2, x2)] f a1 tail a2 hk
            simp only [Option.some.injEq, Prod.mk.injEq] at hp
            obtain ⟨rfl, rfl⟩ := hp
            rw [htail]
            simp only [List.map_cons, List.map_nil, List.filter_cons, he0, he1,
              show (VN.old x2).isEmpty = false from rfl, Bool.not_true, Bool.not_false,
              Bool.false_eq_true, ↓reduceIte, List.length_cons]
            decide

/-- A space tree with three leaves, made by PE from the empty tree. -/
def growOps : List Op := (List.range 9).map (fun j => .put [64 * (j + 1) + 8] (j + 1))

theorem grow_some : (peTx (cfJ 8) 1 (startTree (cfJ 8)) startTop startNext growOps).isSome = true := by
  decide +kernel

def grown : Out := (peTx (cfJ 8) 1 (startTree (cfJ 8)) startTop startNext growOps).get grow_some
def grownTree : Tree := grown.tree (startTree (cfJ 8))
def collapseOps : List Op := (List.range 6).map (fun j => .del [64 * (j + 1) + 8])

theorem collapse_some :
    (peTx (cfJ 8) 2 grownTree grown.top grown.next collapseOps).isSome = true := by
  decide +kernel

def collapsed : Out := (peTx (cfJ 8) 2 grownTree grown.top grown.next collapseOps).get collapse_some

def grownRoot : KNode := ⟨50, false, [.time 1, .key 0 12, .key 264 13, .key 456 14]⟩
def grownLeaf0 : KNode := ⟨49, true, [.time 1, .key 72 3, .key 136 4, .key 200 5]⟩
def grownLeaf1 : KNode := ⟨49, true, [.time 1, .key 264 6, .key 328 7, .key 392 8]⟩

theorem grown_root : grownTree.root = some 15 := by decide +kernel
theorem grown_root_key : DNB.getKey grownTree 15 = some grownRoot := by decide +kernel
theorem grown_leaf0 : DNB.getKey grownTree 12 = some grownLeaf0 := by decide +kernel
theorem grown_leaf1 : DNB.getKey grownTree 13 = some grownLeaf1 := by decide +kernel

/-- The no-join premise holds for the root-collapse transaction, including
its quantifiers over all successful child-plan fuels and accumulators. -/
theorem collapse_noJoins : NoJoins (cfJ 8) 2 grownTree collapseOps := by
  have hfr : grownTree.fuel 15 = 51 := by decide +kernel
  simp only [NoJoins, grown_root]
  rw [hfr, NoJoinsAt, grown_root_key]
  change (∀ e ∈ [((0, 12), [.del [72], .del [136], .del [200]]),
      ((264, 13), [.del [264], .del [328], .del [392]]), ((456, 14), [])], e.2 ≠ [] →
      NoJoinsAt (cfJ 8) 2 grownTree 50 e.1.2 0 e.2) ∧ _
  constructor
  · intro e he hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · exact noJoinsAt_leaf grown_leaf0 rfl (by
        intro op hop; simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
        rcases hop with rfl | rfl | rfl <;> rfl)
    · exact noJoinsAt_leaf grown_leaf1 rfl (by
        intro op hop; simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
        rcases hop with rfl | rfl | rfl <;> rfl)
    · exact False.elim (hn rfl)
  · intro f h a es a' hsh hp
    have hh : h = 0 := by
      obtain ⟨n, _, hgk, hlev, _, _, _⟩ := shaped_getKey hsh
      change DNB.getKey grownTree 15 = some n at hgk
      rw [grown_root_key] at hgk
      obtain rfl : n = grownRoot := by injection hgk with he; exact he.symm
      simp only [grownRoot, cfJ, Cfg.java, Cfg.lev] at hlev
      omega
    subst hh
    left
    apply two_drops (ops0 := [.del [72], .del [136], .del [200]])
      (ops1 := [.del [264], .del [328], .del [392]]) (by simp) (by simp) ?_ ?_ f a es a' hp
    · exact del3_empty (a := 72) (y0 := 3) (y1 := 4) (y2 := 5) grown_leaf0 rfl
    · exact del3_empty (a := 264) (y0 := 6) (y1 := 7) (y2 := 8) grown_leaf1 rfl

/-- The general history theorem also supplies the bound for this collapse. -/
theorem collapse_bound : keyWrites collapsed.ws ≤ dirtyNodeBound 8 grownTree 1 (opsKd collapseOps) := by
  have hh : PeHist (cfJ 8) (startTree (cfJ 8)) startTop startNext [growOps]
      grownTree grown.top grown.next := PeHist.step PeHist.start (Option.some_get grow_some).symm
  have hfill : FillOk 8 15 grownTree := by unfold FillOk; decide +kernel
  have hkeys : ∀ op ∈ collapseOps, keyOk (cfJ 8) op.key = true := by
    intro op hop
    change op ∈ [.del [72], .del [136], .del [200], .del [264], .del [328], .del [392]] at hop
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  exact pe_dirtyNodeBound_noJoins_hist (by decide) hh hfill hkeys collapse_noJoins
    (Option.some_get collapse_some).symm

/-- The count is 152; use the proved walk/recursion equality before
reducing the structural count in the kernel. -/
theorem collapse_count : dirtyNodeBound 8 grownTree 1 (opsKd collapseOps) = 152 := by
  have hcf : (cfJ 8).Ok := cfgOk_java8 (by decide)
  have hI0 := (start_inv hcf).1
  have hI := (pe_step hcf (i := 1) (by decide) hI0 (Option.some_get grow_some).symm).2.2.2.2
  have hkeys : ∀ op ∈ collapseOps, keyOk (cfJ 8) op.key = true := by
    intro op hop
    change op ∈ [.del [72], .del [136], .del [200], .del [264], .del [328], .del [392]] at hop
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  change Inv (cfJ 8) 1 grownTree grown.top grown.next at hI
  have heq : dirtyNodeBound 8 grownTree 1 (opsKd collapseOps) = sbTop 8 grownTree collapseOps :=
    dirtyNodeBound_eq_sb 8 hI hkeys
  rw [heq]
  decide +kernel

/-- A concrete collapse: empty two children of an inner root; PE writes
no key node and keeps the remaining leaf as its space root. The actual
execution and Java's count are both reduced by the kernel here. -/
theorem collapse_case : rootIsLeaf grownTree = false ∧
    FillOk 8 15 grownTree ∧ rootIsLeaf (collapsed.tree grownTree) = true ∧
    keyWrites collapsed.ws = 0 ∧
    dirtyNodeBound 8 grownTree 1 (opsKd collapseOps) = 152 ∧
    keyWrites collapsed.ws ≤ dirtyNodeBound 8 grownTree 1 (opsKd collapseOps) := by
  rw [collapse_count]
  unfold FillOk
  decide +kernel

end Contract.PE.DnbDeletesExample
