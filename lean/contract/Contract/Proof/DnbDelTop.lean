/-
bergdb 030-36: the transaction's key-write count, with deletes and the
explicit no-join premise, from the mixed-operation plan proof.
-/
import Contract.Proof.DnbDelPlan

namespace Contract.PE

open DNB PeProof

variable {i : Time} {s : Tree}

/-- The key-write bound for a nonempty mixed transaction whose child plans
do not trigger joins. Empty child removal and root collapse are allowed. -/
theorem pe_keyWrites_noJoins {b G H : Nat} (hb : 8 ≤ b) {t : Time} {tp : Top} {next : NodeId}
    {ops : List Op} {o : Out} (hI : Inv (Cfg.java b G H) t s tp next)
    (hsf : shapeFaults ⟨(Cfg.java b G H).H, (Cfg.java b G H).m, (Cfg.java b G H).theta⟩ s = [])
    (hkeys : ∀ op ∈ ops, keyOk (Cfg.java b G H) op.key = true)
    (hNo : NoJoins (Cfg.java b G H) i s ops) (hne : ops ≠ [])
    (hw : peTx (Cfg.java b G H) i s tp next ops = some o) :
    keyWrites o.ws ≤ sbTop b s ops := by
  have hdrop : dropNoops (Cfg.java b G H) ops = ops := by
    unfold dropNoops
    rw [List.filter_eq_self]
    intro op hop
    cases op with
    | put k v => rfl
    | del k => exact hkeys (.del k) hop
  unfold peTx at hw
  simp only [hdrop] at hw
  split at hw
  · cases hw
  · rename_i hok
    have hok' : opsOk (Cfg.java b G H) ops = true := by simpa using hok
    obtain ⟨r, hr, hsh⟩ := hI.shaped
    have hNroot : NoJoinsAt (Cfg.java b G H) i s (s.fuel r) r 0 ops := by
      simpa only [NoJoins, hr] using hNo
    rw [hr] at hw
    simp only at hw
    obtain ⟨n, hobj, hgk, hlev, hleaf, _, _⟩ := shaped_getKey hsh
    rw [hgk] at hw
    simp only at hw
    have hht : (Cfg.java b G H).htOf n.level = htIn (Cfg.java b G H) s r := by simp [htIn, hobj]
    rw [hht] at hw
    cases hpl : plan (Cfg.java b G H) i s fuel r 0 (htIn (Cfg.java b G H) s r) ops ⟨[], next⟩ with
    | none => rw [hpl] at hw; cases hw
    | some q =>
      obtain ⟨v, acc⟩ := q
      rw [hpl] at hw
      simp only at hw
      have hgood : Good s r 0 none := good_of_invOk hr hI.inv
      have hfill : Filled (Cfg.java b G H) s true r := filled_of_shapeFaults hsf hr
      have hpa : OpsD 0 ops := by
        intro op hop
        have h1 : keyOk (Cfg.java b G H) op.key = true := by
          unfold opsOk at hok'; exact List.all_eq_true.mp hok' op hop
        refine ⟨?_, keyOk_pos h1⟩
        simp only [keyOk, Bool.and_eq_true] at h1
        exact h1.1
      have hp := (plan_tree_noJoins (i := i) (s := s) (G := G) (H := H) hb fuel).1 r 0 _ ops ⟨[], next⟩ v acc
        true (s.fuel r) hsh ⟨0, none, hgood⟩ hfill hpa hne le_rfl hNroot hpl
      split at hw
      · rename_i rv hset
        split at hw
        · rename_i c r' acc2 hem
          have hk := space_stepD hb hsh hgood hfill hpl hp hset hem
          have hws : o.ws = acc2.ws := by
            split at hw
            · simp only [Option.some.injEq] at hw; rw [← hw]
            · simp only [Option.some.injEq] at hw; rw [← hw]; rfl
          rw [hws, keyWrites_eq_kw]
          have h0 : kw (⟨[], next⟩ : Acc) = 0 := rfl
          simp only [sbTop, hr]
          rw [ite_eq_right (by simpa using hne)]
          omega
        · cases hw
      · cases hw

/-- Include the empty transaction. -/
theorem pe_keyWrites_le_sb_noJoins {b G H : Nat} (hb : 8 ≤ b) {t : Time} {tp : Top}
    {next : NodeId} {ops : List Op} {o : Out} (hI : Inv (Cfg.java b G H) t s tp next)
    (hfill : FillOk b H s) (hkeys : ∀ op ∈ ops, keyOk (Cfg.java b G H) op.key = true)
    (hNo : NoJoins (Cfg.java b G H) i s ops)
    (hw : peTx (Cfg.java b G H) i s tp next ops = some o) :
    keyWrites o.ws ≤ sbTop b s ops := by
  by_cases hne : ops = []
  · subst hne
    rw [pe_keyWrites_nil hI hfill hw]
    exact Nat.zero_le _
  · exact pe_keyWrites_noJoins hb hI hfill hkeys hNo hne hw

/-- A leaf with operations ending at its segment has no child-tree calls
and hence satisfies the no-join condition. -/
theorem noJoinsAt_leaf {cf : Cfg} {i : Time} {s : Tree} {fs x g : Nat}
    {ops : List Op} {n : KNode} (hk : DNB.getKey s x = some n) (hl : n.leaf = true)
    (he : ∀ op ∈ ops, op.key.length = g + 1) : NoJoinsAt cf i s fs x g ops := by
  cases fs with
  | zero => trivial
  | succ fs =>
    simp only [NoJoinsAt, hk, hl, ↓reduceIte]
    intro cv _
    cases (live n.ks).lookup cv with
    | none => trivial
    | some y =>
      intro hn
      apply False.elim (hn ?_)
      unfold subsOf
      rw [List.filter_eq_nil_iff]
      intro op hop
      have hp := he op (List.mem_of_mem_filter hop)
      simp [endsAt, hp]

end Contract.PE
