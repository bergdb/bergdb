/-
bergdb 030-37: repeated leaf joins in histories from the empty tree, at
all four node sizes. Several children shrink to one entry; an untouched
neighbour is present. Each execution makes two leaf joins, including a
join with a group already joined, and meets the new history bound.
-/
import Contract.Proof.DnbMain

set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

namespace Contract.PE.DnbJoinsExample

open DNB

def Supported (b : Nat) : Prop := b = 8 ∨ b = 14 ∨ b = 30 ∨ b = 62
def cfg (b : Nat) : Cfg := Cfg.java b 3 15
def childCount (b : Nat) : Nat := if b = 8 then 4 else 3
def touchedCount (b : Nat) : Nat := if b = 8 then 3 else 2
def key (j : Nat) : Key := [64 * (j + 1) + 8]
def puts (b : Nat) : List Op :=
  (List.range (childCount b * (b / 2))).map (fun j => .put (key j) (j + 1))
def dels (b : Nat) : List Op := (List.range (touchedCount b)).flatMap (fun leaf =>
  (List.range (b / 2 - 1)).map (fun j => .del (key (leaf * (b / 2) + j))))

theorem grow_some {b : Nat} (hb : Supported b) :
    (peTx (cfg b) 1 (startTree (cfg b)) startTop startNext (puts b)).isSome = true := by
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

def grown (b : Nat) (hb : Supported b) : Out :=
  (peTx (cfg b) 1 (startTree (cfg b)) startTop startNext (puts b)).get (grow_some hb)
def tree (b : Nat) (hb : Supported b) : Tree := (grown b hb).tree (startTree (cfg b))

theorem fill {b : Nat} (hb : Supported b) : FillOk b 15 (tree b hb) := by
  rcases hb with rfl | rfl | rfl | rfl <;> unfold FillOk <;> decide +kernel

theorem height {b : Nat} (hb : Supported b) :
    ∀ r, (tree b hb).root = some r → htIn (cfg b) (tree b hb) r ≤ 1 := by
  have hh : (match (tree b hb).root with
    | none => 0
    | some r => htIn (cfg b) (tree b hb) r) ≤ 1 := by
    rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
  intro r hr
  simpa only [hr] using hh

theorem keys {b : Nat} (hb : Supported b) :
    ∀ op ∈ dels b, keyOk (cfg b) op.key = true := by
  have hh : (dels b).all (fun op => keyOk (cfg b) op.key) = true := by
    rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
  exact List.all_eq_true.mp hh

theorem ends (b : Nat) : ∀ op ∈ dels b, op.key.length = 1 := by
  intro op hop
  obtain ⟨leaf, _, he⟩ := List.mem_flatMap.mp hop
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp he
  rfl

theorem del_some {b : Nat} (hb : Supported b) :
    (peTx (cfg b) 2 (tree b hb) (grown b hb).top (grown b hb).next (dels b)).isSome = true := by
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

def deleted (b : Nat) (hb : Supported b) : Out :=
  (peTx (cfg b) 2 (tree b hb) (grown b hb).top (grown b hb).next (dels b)).get (del_some hb)

theorem history {b : Nat} (hb : Supported b) :
    PeHist (cfg b) (startTree (cfg b)) startTop startNext [puts b]
      (tree b hb) (grown b hb).top (grown b hb).next :=
  PeHist.step PeHist.start (Option.some_get (grow_some hb)).symm

theorem bound {b : Nat} (hb : Supported b) :
    keyWrites (deleted b hb).ws ≤ dirtyNodeBound b (tree b hb) 1 (opsKd (dels b)) := by
  have hcf : (cfg b).Ok := cfgOk_java8 (by rcases hb with rfl | rfl | rfl | rfl <;> decide)
  obtain ⟨h0, hs, ht⟩ := start_inv hcf
  have hI := (pe_meetsTop hcf h0 hs ht (history hb)).2
  exact pe_dirtyNodeBound_noInnerJoins_hist (by rcases hb with rfl | rfl | rfl | rfl <;> decide)
    (history hb) (fill hb) (keys hb) (noInnerJoins_shallow hI.shaped (height hb) (ends b))
      (Option.some_get (del_some hb)).symm

/-- The actual child plans before the root's rebalance. -/
def before (b : Nat) (hb : Supported b) : List (Nat × VN) :=
  (match (tree b hb).root with
  | none => none
  | some r => match getKey (tree b hb) r with
    | none => none
    | some n => (planKids (cfg b) 2 (tree b hb) fuel 0 1 (live n.ks)
      (route (segAt 0) (live n.ks) (dels b)) ⟨[], (grown b hb).next⟩).map
        (fun q : List (Nat × VN) × Acc => q.1)).getD []

def after (b : Nat) (hb : Supported b) : List (Nat × VN) :=
  (rebalance (cfg b) 2 (tree b hb) fuel 0 0 (before b hb)).getD []

/-- No child is empty, an untouched neighbour is present, and rebalance
reduces the list by exactly two: two actual leaf joins. -/
theorem two_joins {b : Nat} (hb : Supported b) :
    (before b hb).length = childCount b ∧
      (before b hb).all (fun e => !e.2.isEmpty) = true ∧
      (before b hb).any (fun e => match e.2 with | .old _ => true | _ => false) = true ∧
      (after b hb).length + 2 = (before b hb).length := by
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

end Contract.PE.DnbJoinsExample
