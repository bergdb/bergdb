/-
bergdb 030-29: **Java's dirty-node bound bounds PE, for transactions of
puts.** The statement's definitions are in Contract/DirtyBoundStatement.lean
(`Cfg.java`, `FillOk`) and Contract/DirtyBound.lean (Java's count
`DNB.dirtyNodeBound`, `DNB.opsKd`, `DNB.keyWrites`).

`pe_dirtyNodeBound_puts`: from a state PE keeps at time t (`Inv`) whose tree
meets the writer's fill rules, for a transaction of puts that PE accepts at
any time i, the key nodes PE writes are at most Java's count of the
transaction on the tree at t (`Db.checkDirtyNodes` computes it at the lookup
time, the latest, which is t), at Java's parameters at node size b ≥ 8.

030-36 adds `pe_dirtyNodeBound_noJoins` and its history form, with puts
and deletes, empty child removal and root collapse, under the explicit
`NoJoins` condition; `pe_dirtyNodeBound_leaf` needs only a leaf space root
and one-segment operations, besides the existing state and fill premises.

The proof: Java's walk computes the count as one recursion over the tree,
`sbTop` (`dirtyNodeBound_eq_sb`, DnbWalk.lean, from TREE: each node reached
has one parent), and PE writes at most `sbTop`
(`pe_keyWrites_le_sb_puts`, DnbTop.lean, by induction on PE's plan:
DnbPlan.lean).
-/
import Contract.Proof.DnbWalk
import Contract.Proof.DnbTop
import Contract.Proof.DnbDelTop

namespace Contract.PE

open DNB

theorem keyOk_of_peTx_put {cf : Cfg} {i : Time} {s : Tree} {tp : Top} {next : NodeId}
    {ops : List Op} {o : Out} (hw : peTx cf i s tp next ops = some o) :
    ∀ k v, Op.put k v ∈ ops → keyOk cf k = true := by
  intro k v hkv
  have hok : opsOk cf (dropNoops cf ops) = true := by
    cases h : opsOk cf (dropNoops cf ops) with
    | true => rfl
    | false => simp [peTx, h] at hw
  unfold opsOk at hok
  have hm : Op.put k v ∈ dropNoops cf ops := by
    unfold dropNoops; rw [List.mem_filter]; exact ⟨hkv, rfl⟩
  exact List.all_eq_true.mp hok _ hm

/-- **Java's dirty-node bound bounds the key nodes PE writes, for a
transaction of puts.** -/
theorem pe_dirtyNodeBound_puts {b G H : Nat} (hb : 8 ≤ b) {t i : Time} {s : Tree} {tp : Top}
    {next : NodeId} {ops : List Op} {o : Out}
    (hI : Inv (Cfg.java b G H) t s tp next) (hfill : FillOk b H s)
    (hputs : ∀ op ∈ ops, ∃ k v, op = .put k v)
    (hw : peTx (Cfg.java b G H) i s tp next ops = some o) :
    keyWrites o.ws ≤ dirtyNodeBound b s t (opsKd ops) := by
  have hdel : ∀ op ∈ ops, opDel op = false := by
    intro op hop
    obtain ⟨k, v, rfl⟩ := hputs op hop
    rfl
  have hok : ∀ op ∈ ops, keyOk (Cfg.java b G H) op.key = true := by
    intro op hop
    obtain ⟨k, v, rfl⟩ := hputs op hop
    exact keyOk_of_peTx_put hw k v hop
  rw [dirtyNodeBound_eq_sb b hI hok]
  exact pe_keyWrites_le_sb_puts hb hI hfill hdel hw

/-- The dirty-node bound with puts and deletes, provided planned nonroot
children do not trigger joins (`NoJoins`). This extra premise excludes joins;
it is not a theorem for arbitrary admitted transactions. -/
theorem pe_dirtyNodeBound_noJoins {b G H : Nat} (hb : 8 ≤ b) {t i : Time} {s : Tree}
    {tp : Top} {next : NodeId} {ops : List Op} {o : Out}
    (hI : Inv (Cfg.java b G H) t s tp next) (hfill : FillOk b H s)
    (hkeys : ∀ op ∈ ops, keyOk (Cfg.java b G H) op.key = true)
    (hNo : NoJoins (Cfg.java b G H) i s ops)
    (hw : peTx (Cfg.java b G H) i s tp next ops = some o) :
    keyWrites o.ws ≤ dirtyNodeBound b s t (opsKd ops) := by
  rw [dirtyNodeBound_eq_sb b hI hkeys]
  exact pe_keyWrites_le_sb_noJoins hb hI hfill hkeys hNo hw

/-- The same conditional bound after any PE history from the empty tree.
The fill rules and no-underflow condition remain explicit premises. -/
theorem pe_dirtyNodeBound_noJoins_hist {b G H : Nat} (hb : 8 ≤ b)
    {txs : List (List Op)} {s : Tree} {tp : Top} {nx : NodeId} {ops : List Op} {o : Out}
    (hh : PeHist (Cfg.java b G H) (startTree (Cfg.java b G H)) startTop startNext txs s tp nx)
    (hfill : FillOk b H s)
    (hkeys : ∀ op ∈ ops, keyOk (Cfg.java b G H) op.key = true)
    (hNo : NoJoins (Cfg.java b G H) (txs.length + 1) s ops)
    (hw : peTx (Cfg.java b G H) (txs.length + 1) s tp nx ops = some o) :
    keyWrites o.ws ≤ dirtyNodeBound b s txs.length (opsKd ops) := by
  obtain ⟨h0, hst, htop⟩ := start_inv (cfgOk_java8 hb)
  have hI := (pe_meetsTop (cfgOk_java8 hb) h0 hst htop hh).2
  exact pe_dirtyNodeBound_noJoins hb hI hfill hkeys hNo hw

/-- On a space root that is a segment leaf, every mixed transaction of
one-segment keys has the bound, without the no-join premise. Its result may
cut the root and grow the tree. -/
theorem pe_dirtyNodeBound_leaf {b G H : Nat} (hb : 8 ≤ b) {t i : Time} {s : Tree}
    {tp : Top} {next : NodeId} {ops : List Op} {o : Out} {r : NodeId} {n : KNode}
    (hI : Inv (Cfg.java b G H) t s tp next) (hfill : FillOk b H s)
    (hr : s.root = some r) (hk : DNB.getKey s r = some n) (hl : n.leaf = true)
    (hkeys : ∀ op ∈ ops, keyOk (Cfg.java b G H) op.key = true)
    (he : ∀ op ∈ ops, op.key.length = 1)
    (hw : peTx (Cfg.java b G H) i s tp next ops = some o) :
    keyWrites o.ws ≤ dirtyNodeBound b s t (opsKd ops) := by
  apply pe_dirtyNodeBound_noJoins hb hI hfill hkeys ?_ hw
  simpa only [NoJoins, hr] using noJoinsAt_leaf (cf := Cfg.java b G H) (i := i)
    (fs := s.fuel r) (g := 0) hk hl he

/-- **The same for every history PE writes from the empty tree**: the next
transaction of puts, on a tree that meets the fill rules, writes at most
Java's count of it, read at the history's last time. -/
theorem pe_dirtyNodeBound_puts_hist {b G H : Nat} (hb : 8 ≤ b) {txs : List (List Op)} {s : Tree}
    {tp : Top} {nx : NodeId} {ops : List Op} {o : Out}
    (hh : PeHist (Cfg.java b G H) (startTree (Cfg.java b G H)) startTop startNext txs s tp nx)
    (hfill : FillOk b H s) (hputs : ∀ op ∈ ops, ∃ k v, op = .put k v)
    (hw : peTx (Cfg.java b G H) (txs.length + 1) s tp nx ops = some o) :
    keyWrites o.ws ≤ dirtyNodeBound b s txs.length (opsKd ops) := by
  have hcf : (Cfg.java b G H).Ok := ⟨by simp [Cfg.java, DNB.splitAbove]; omega,
    by simp [Cfg.java, DNB.splitAbove]; omega, by simp [Cfg.java, DNB.cutSize]; omega,
    by simp [Cfg.java, DNB.cutSize]; omega, by simp [Cfg.java, DNB.mergeCap]; omega,
    by simp [Cfg.java, DNB.mergeCap]; omega⟩
  obtain ⟨h0, hst, htop⟩ := start_inv hcf
  have hI := (pe_meetsTop hcf h0 hst htop hh).2
  exact pe_dirtyNodeBound_puts hb hI hfill hputs hw

end Contract.PE
