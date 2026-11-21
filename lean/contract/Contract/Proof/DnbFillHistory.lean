/-
bergdb 030-37: recursive occupancy through complete PE histories. This
proves RootsOK and FillOK at every live key node, through every segment;
the separate dead-klong condition of shapeFaults is not part of Filled.
-/
import Contract.Proof.DnbFillTree

namespace Contract.PE

open DNB PeProof PeProof.Abs

/-- The current space root and every live next-segment tree meet RootsOK
and FillOK. Unlike FillOk, this predicate asks only the occupancy rules
used by the dirty-bound proof. -/
def RootFilled (cf : Cfg) (s : Tree) : Prop :=
  ∀ r, s.root = some r → Filled cf s true r

theorem start_rootFilled (cf : Cfg) : RootFilled cf (startTree cf) := by
  intro r hr
  simp only [startTree_root, Option.some.injEq] at hr
  subst r
  refine Filled.key startTree_obj1 ?_ ?_ ?_ ?_
  · intro hl _; cases hl
  · intro _ hr; cases hr
  · intro c y hm; simp only [start_live] at hm; cases hm
  · intro c y hm; simp only [start_live] at hm; cases hm

/-- One complete PE transaction preserves all live occupancy rules.
The input and output are the states of the proved writer; joins have no
height restriction. -/
theorem pe_rootFilled_step {b G H : Nat} (hb : 8 ≤ b) {i : Time} (hi : 1 ≤ i)
    {s : Tree} {tp : Top} {next : NodeId} {ops : List Op} {o : Out}
    (hI : Inv (Cfg.java b G H) (i - 1) s tp next)
    (hfill : RootFilled (Cfg.java b G H) s)
    (hw : peTx (Cfg.java b G H) i s tp next ops = some o) : RootFilled (Cfg.java b G H) (o.tree s) := by
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
  obtain ⟨runs, ho, hplan, hrunFill⟩ := f_old_filled hcf (f_all hcf fuel)
    (fill_f_all hb fuel) hpre hsh0 hgood hnd hp
  have hVF := plan_vfill (java_params hb).1 hsh0 (hfill r hr) hp
  obtain ⟨W, hW, hfilled⟩ := seg_some_filled hb rfl hcf hsok hI.fresh ho hplan hVF
    (filled_view_payloads _ hsh0 (hfill r hr)) hrunFill hsr he
  have hws : acc2.ws = W := by simpa using hW.ws
  have hows : o.ws = W := by rcases hout with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> exact hws
  set T := o.tree s with hTdef
  have hTobj : T.obj = (applyWs s W o.roots).obj := by simp [hTdef, Out.tree, hows]
  have hafter : After s T W (R s r) := by
    have hh := applyWs_after (s := s) (roots := o.roots) (U := R s r) hW.nodup
    exact ⟨fun p hp => by rw [hTobj]; exact hh.ws p hp,
      fun z hz hz' => by rw [hTobj]; exact hh.keep z hz hz',
      fun z hz => by rw [hTobj]; exact hh.exist z hz⟩
  have hTroot : T.root = some r' := by
    rcases hout with ⟨heq, rfl⟩ | ⟨_, rfl⟩
    · show s.root = some r'
      rw [hr, heq]
    · show (s.roots ++ [(i, r')]).getLast?.map (·.2) = some r'
      simp
  intro z hz
  change T.root = some z at hz
  rw [hTroot] at hz
  have hz' : r' = z := Option.some.inj hz
  subst z
  exact hfilled T hafter

/-- The occupancy premise of the dirty-node proof holds after every
history PE writes from the empty tree, including arbitrary higher joins. -/
theorem pe_rootFilled_hist {b G H : Nat} (hb : 8 ≤ b)
    {txs : List (List Op)} {s : Tree} {tp : Top} {nx : NodeId}
    (hh : PeHist (Cfg.java b G H) (startTree (Cfg.java b G H)) startTop startNext txs s tp nx) :
    RootFilled (Cfg.java b G H) s := by
  induction hh with
  | start => exact start_rootFilled _
  | @step txs s tp nx ops o hist hw IH =>
    obtain ⟨h0, hs, ht⟩ := start_inv (cfgOk_java8 hb)
    have hI := (pe_meetsTop (cfgOk_java8 hb) h0 hs ht hist).2
    exact pe_rootFilled_step hb (Nat.succ_pos _) hI IH hw

end Contract.PE
