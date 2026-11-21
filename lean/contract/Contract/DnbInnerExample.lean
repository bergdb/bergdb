/-
bergdb 030-37: the inner join that invalidates the shortcut in 028-21,
in a history from the empty tree. A small node joins a non-small node,
remains small after the recursive leaf rebalance, and joins a second
non-small node. The history theorem supplies the dirty-node bound.
-/
import Contract.Proof.DnbMain

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace Contract.PE.DnbInnerExample

open DNB

def cf : Cfg := Cfg.java 30 2 15
def key (j : Nat) : Key := [64 * (j + 1) + 8]
def puts : List Op := (List.range 500).map (fun j => .put (key j) (j + 1))

theorem grow_some :
    (peTx cf 1 (startTree cf) startTop startNext puts).isSome = true := by decide +kernel

def grown : Out := (peTx cf 1 (startTree cf) startTop startNext puts).get grow_some
def tree : Tree := grown.tree (startTree cf)
def node (x : Nat) : KNode := (PE.getKey tree x).getD ⟨0, false, []⟩
def root : Nat := tree.root.getD 0

-- The left subtree retains one key. The middle subtree retains three
-- leaves, cut by the new puts into three, three and two parts.
def dels : List Op := (List.range 154).map (fun j => .del (key j)) ++
  (List.range 120).map (fun j => .del (key (200 + j)))
def extras : List Op := ([155, 170, 185] : List Nat).flatMap (fun j =>
  (List.range (if j = 185 then 14 else 16)).map (fun k =>
    .put [64 * (j + 1) + 8 + k + 1] (1000 + j + k)))
def ops : List Op := dels ++ extras

theorem fill : FillOk 30 15 tree := by unfold FillOk; decide +kernel

theorem height : ∀ r, tree.root = some r → htIn cf tree r ≤ 2 := by
  have hh : (match tree.root with | none => 0 | some r => htIn cf tree r) ≤ 2 := by decide +kernel
  intro r hr
  simpa only [hr] using hh

theorem keys : ∀ op ∈ ops, keyOk cf op.key = true := by
  have hh : ops.all (fun op => keyOk cf op.key) = true := by decide +kernel
  exact List.all_eq_true.mp hh

theorem ends : ∀ op ∈ ops, op.key.length = 1 := by
  have hh : ops.all (fun op => op.key.length == 1) = true := by decide +kernel
  intro op hop
  exact beq_iff_eq.mp (List.all_eq_true.mp hh op hop)

theorem step_some : (peTx cf 2 tree grown.top grown.next ops).isSome = true := by decide +kernel
def result : Out := (peTx cf 2 tree grown.top grown.next ops).get step_some

theorem history : PeHist cf (startTree cf) startTop startNext [puts] tree grown.top grown.next :=
  PeHist.step PeHist.start (Option.some_get grow_some).symm

theorem bound : keyWrites result.ws ≤ dirtyNodeBound 30 tree 1 (opsKd ops) := by
  have hcf : cf.Ok := cfgOk_java8 (by decide)
  obtain ⟨h0, hs, ht⟩ := start_inv hcf
  have hI := (pe_meetsTop hcf h0 hs ht history).2
  exact pe_dirtyNodeBound_twoJoinLevels_hist (by decide) history fill keys
    (noHigherJoins_shallow hI.shaped height ends) (Option.some_get step_some).symm

def before : List (Nat × VN) :=
  (planKids cf 2 tree fuel 0 2 (live (node root).ks)
    (route (segAt 0) (live (node root).ks) ops) ⟨[], grown.next⟩).map Prod.fst |>.getD []
def first : List (Nat × VN) :=
  (joinAt cf 2 tree 0 1 (fun J => rebalance cf 2 tree fuel 0 0 J) before 0).getD []
def after : List (Nat × VN) := (rebalance cf 2 tree (fuel + 1) 0 1 before).getD []

/-- Both neighbours are non-small. The first joined group has seven
entries, below m = 8, so the loop joins it with the second neighbour. -/
theorem repeated_non_small :
    cf.m = 8 ∧ ops.length = 320 ∧
    before.map (fun e => cntOf tree e.2) = [1, 8, 12] ∧
    findSmall cf before = some 0 ∧
    first.map (fun e => cntOf tree e.2) = [7, 12] ∧
    findSmall cf first = some 0 ∧
    after.length = 1 ∧
    before.any (fun e => match e.2 with | .old _ => true | _ => false) = true := by
  decide +kernel

end Contract.PE.DnbInnerExample
