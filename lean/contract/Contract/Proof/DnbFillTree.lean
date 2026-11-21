/-
bergdb 030-37: complete recursive occupancy preservation for planTree.
The old tree, fresh segments, root collapse, all joins, and the next
segments below the leaves are included.
-/
import Contract.Proof.DnbFillPrepare

namespace Contract.PE

open DNB PeProof PeProof.Abs PeProof.Keys

variable {cf : Cfg} {i : Time} {s : Tree}

theorem f_tail_filled {b G H : Nat} (hb : 8 ≤ b) (hjava : cf = Cfg.java b G H) (hcf : cf.Ok)
    {f g h : Nat} {root : Option NodeId} {E : List (Nat × NodeId)}
    {ops : List Op} {v : VN} {runs : List Run} {acc0 acc1 acc' : Acc} {res : Option NodeId}
    (hpre : SegPre cf i s g root ops acc0)
    (ho : OldSeg cf s g root E) (hp : PlanSeg cf i s g root E ops h v runs acc0 acc1)
    (hfillPlan : VFill cf i s g true h v)
    (hfillOld : ∀ p ∈ E, isLong p.1 = true → Filled cf s true p.2)
    (hfillRuns : ∀ r ∈ runs, RunFilled cf i s (E.lookup r.c) r)
    (ht : (match settleRoot cf i s f g v false with
      | none => none
      | some none => some (none, acc1)
      | some (some v') =>
        match emit cf i s v' acc1 with
        | some ([(_, y)], acc) => some (some y, acc)
        | _ => none) = some (res, acc')) : TreeFilled cf i s root acc0 acc' res := by
  split at ht
  · cases ht
  · simp only [Option.some.injEq, Prod.mk.injEq] at ht
    obtain ⟨rfl, rfl⟩ := ht
    intro W hw T hT y hy
    cases hy
  · rename_i v' hset
    split at ht
    · rename_i c0 y acc2 he
      simp only [Option.some.injEq, Prod.mk.injEq] at ht
      obtain ⟨rfl, rfl⟩ := ht
      obtain ⟨W, hW, hfill⟩ := seg_some_filled hb hjava hcf hpre.sok hpre.fresh ho hp
        hfillPlan hfillOld hfillRuns hset he
      intro W' hW' T hT z hz
      have heq := e_wokv_unique hW hW'
      subst W'
      cases hz
      exact hfill T hT
    · cases ht

theorem fill_f_step {b G H : Nat} (hb : 8 ≤ b) (hjava : cf = Cfg.java b G H) (hcf : cf.Ok)
    {f : Nat} (IF : FillTreeIH cf i s f) :
    ∀ (root : Option NodeId) (g : Nat) (ops : List Op) (acc : Acc) (res : Option NodeId)
      (acc' : Acc), SegPre cf i s g root ops acc →
      (∀ y, root = some y → Filled cf s true y) →
      planTree cf i s (f + 1) root g ops acc = some (res, acc') → TreeFilled cf i s root acc acc' res := by
  intro root g ops acc res acc' hpre hfill hpt
  have IH := f_all hcf (i := i) (s := s) f
  have hm2 : 2 ≤ cf.m := by rw [hjava]; exact (java_params hb).1
  unfold planTree at hpt
  cases root with
  | some r =>
    cases hgk : getKey s r with
    | none => simp [hgk] at hpt
    | some n =>
      cases hplan : plan cf i s f r g (cf.htOf n.level) ops acc with
      | none => simp [hgk, hplan] at hpt
      | some p =>
        obtain ⟨v, acc1⟩ := p
        simp only [hgk, hplan] at hpt
        obtain ⟨hsh, hg, hnd⟩ := hpre.root r rfl
        have hht : htIn cf s r = cf.htOf n.level := by unfold htIn; rw [getKey_obj hgk]
        rw [hht] at hsh
        obtain ⟨runs, ho, hp, hrunFill⟩ := f_old_filled hcf IH IF hpre hsh hg hnd hplan
        exact f_tail_filled hb hjava hcf hpre ho hp (plan_vfill hm2 hsh (hfill r rfl) hplan)
          (filled_view_payloads _ hsh (hfill r rfl)) hrunFill hpt
  | none =>
    cases hag : applyGroups cf i s f g [] ((ops.map (segAt g)).eraseDups) ops acc with
    | none => simp [hag] at hpt
    | some p =>
      obtain ⟨es, acc1⟩ := p
      cases hmk : mkNode cf i s none g 0 false (es.map (fun e => (e.1, VN.old e.2))) with
      | none => simp [hag, hmk] at hpt
      | some v =>
        simp only [hag, hmk, Option.map_some] at hpt
        obtain ⟨runs, ho, hp, hrunFill⟩ := f_new_filled hcf IH IF hpre hag hmk
        have hfillPlan : VFill cf i s g true 0 v := by
          apply mkNode_vfill_leaf ?_ (by simp) hmk
          intro e he
          obtain ⟨q, _, rfl⟩ := List.mem_map.mp he
          exact ⟨q.2, rfl⟩
        exact f_tail_filled hb hjava hcf hpre ho hp hfillPlan (by simp) hrunFill hpt

theorem fill_f_all {b G H : Nat} (hb : 8 ≤ b) :
    ∀ F, FillTreeIH (Cfg.java b G H) i s F := by
  intro F
  induction F with
  | zero => intro f hf; omega
  | succ F IH =>
    intro f hf root g ops acc res acc' hpre hfill hpt
    rcases Nat.lt_succ_iff_lt_or_eq.mp hf with hlt | rfl
    · exact IH f hlt root g ops acc res acc' hpre hfill hpt
    · cases f with
      | zero => simp [planTree] at hpt
      | succ f =>
        exact fill_f_step hb rfl (cfgOk_java8 hb) (fun ff hff => IH ff (by omega))
          root g ops acc res acc' hpre hfill hpt

/-- The recursive fill of a surviving segment root, in every after-state
of its actual writes, for any successful planTree execution. -/
theorem planTree_filled {b G H f g : Nat} (hb : 8 ≤ b) {root : Option NodeId}
    {ops : List Op} {acc acc' : Acc} {res : Option NodeId}
    (hpre : SegPre (Cfg.java b G H) i s g root ops acc)
    (hfill : ∀ y, root = some y → Filled (Cfg.java b G H) s true y)
    (hp : planTree (Cfg.java b G H) i s f root g ops acc = some (res, acc')) :
    TreeFilled (Cfg.java b G H) i s root acc acc' res :=
  fill_f_all hb (f + 1) f (Nat.lt_succ_self f) root g ops acc res acc' hpre hfill hp

end Contract.PE
