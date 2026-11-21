/-
bergdb 030-37: every PE history from the empty tree keeps DeadOK at all
key nodes, including obsolete nodes retained by the append-only tree.
-/
import Contract.Proof.DnbDeadTree

namespace Contract.PE

open DNB PeProof PeProof.Abs

/-- All allocated key nodes meet the dead-klong rule. -/
def AllDeadSafe (cf : Cfg) (s : Tree) : Prop :=
  ∀ x n, s.obj x = some (.key n) → DeadSafe cf n.ks

theorem start_allDeadSafe (cf : Cfg) : AllDeadSafe cf (startTree cf) := by
  intro x n hn
  by_cases hx : x = 1
  · subst x
    rw [startTree_obj1] at hn
    have he : n = ⟨cf.lev 0 0, true, [.time 0]⟩ := (Obj.key.inj (Option.some.inj hn)).symm
    subst n
    exact Or.inr (by change 0 ≤ cf.theta; exact Nat.zero_le _)
  · rw [startTree_obj_ne hx] at hn
    cases hn

/-- Every key write of a complete transaction meets DeadOK. -/
theorem pe_writes_dead_safe {b G H : Nat} (hb : 8 ≤ b) {i : Time} (hi : 1 ≤ i)
    {s : Tree} {tp : Top} {next : NodeId} {ops : List Op} {o : Out}
    (hI : Inv (Cfg.java b G H) (i - 1) s tp next)
    (hw : peTx (Cfg.java b G H) i s tp next ops = some o) :
    WritesDeadSafe (Cfg.java b G H) o.ws := by
  have hcf := cfgOk_java8 (G := G) (H := H) hb
  obtain ⟨hok, r, n, v, acc1, v', c0, r', acc2, hr, hn, hp, hsr, he, hout⟩ := peTx_spec hw
  have hi1 : i - 1 + 1 = i := by tomega
  have hsok : SOk (Cfg.java b G H) i s := hi1 ▸ hI.sok
  have hgood : Good s r 0 none := good_of_invOk hr hI.inv
  have hnd : (R s r).Nodup := by
    have hh := hI.tree
    unfold Contract.TreeOk at hh
    rwa [reach_eq_R hr] at hh
  obtain ⟨r0, hr0, hsh0⟩ := hI.shaped
  have hrr : r0 = r := by rw [hr] at hr0; exact (Option.some.inj hr0).symm
  subst r0
  have hobj : s.obj r = some (.key n) := getKey_obj hn
  have hht : htIn (Cfg.java b G H) s r = (Cfg.java b G H).htOf n.level := by simp [htIn, hobj]
  rw [← hht] at hp
  have hpre : SegPre (Cfg.java b G H) i s 0 (some r) (dropNoops (Cfg.java b G H) ops) ⟨[], next⟩ :=
    { sok := hsok
      fresh := hI.fresh
      ops := fun op hop => by
        have h1 := List.all_eq_true.mp hok op hop
        exact ⟨h1, key_ne_nil h1⟩
      root := fun r1 h => by cases h; exact ⟨hsh0, hgood, hnd⟩ }
  obtain ⟨runs, ho, hplan, hrunFill⟩ := f_old_dead hcf (f_all hcf fuel)
    (dead_f_all hcf fuel) hpre hsh0 hgood hnd hp
  have hsafe0 : WritesDeadSafe (Cfg.java b G H) ([] : List (NodeId × Obj)) := by
    intro p hp; cases hp
  have hsafe1 := chain_dead_safe hplan.chain hrunFill hsafe0
  have hsafe2 := seg_emit_dead hcf hsok hI.fresh ho hplan hsafe1 hsr he
  have hows : o.ws = acc2.ws := by rcases hout with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl
  exact hows.symm ▸ hsafe2

/-- A complete transaction preserves DeadOK at every allocated key node. -/
theorem pe_allDeadSafe_step {b G H : Nat} (hb : 8 ≤ b) {i : Time} (hi : 1 ≤ i)
    {s : Tree} {tp : Top} {next : NodeId} {ops : List Op} {o : Out}
    (hI : Inv (Cfg.java b G H) (i - 1) s tp next)
    (hsafe : AllDeadSafe (Cfg.java b G H) s)
    (hw : peTx (Cfg.java b G H) i s tp next ops = some o) :
    AllDeadSafe (Cfg.java b G H) (o.tree s) := by
  have hws := pe_writes_dead_safe hb hi hI hw
  intro x n hn
  change (match o.ws.lookup x with | some ob => some ob | none => s.obj x) = some (.key n) at hn
  cases hl : o.ws.lookup x with
  | none =>
    rw [hl] at hn
    exact hsafe x n hn
  | some ob =>
    rw [hl] at hn
    simp only [Option.some.injEq] at hn
    exact hws (x, ob) (lookup_mem hl) n hn

/-- The dead-klong rule holds after every history PE writes from empty. -/
theorem pe_allDeadSafe_hist {b G H : Nat} (hb : 8 ≤ b)
    {txs : List (List Op)} {s : Tree} {tp : Top} {nx : NodeId}
    (hh : PeHist (Cfg.java b G H) (startTree (Cfg.java b G H)) startTop startNext txs s tp nx) :
    AllDeadSafe (Cfg.java b G H) s := by
  induction hh with
  | start => exact start_allDeadSafe _
  | @step txs s tp nx ops o hist hw IH =>
    obtain ⟨h0, hs, ht⟩ := start_inv (cfgOk_java8 hb)
    have hI := (pe_meetsTop (cfgOk_java8 hb) h0 hs ht hist).2
    exact pe_allDeadSafe_step hb (Nat.succ_pos _) hI IH hw

end Contract.PE
