/-
bergdb 030-37: DeadOK for every key write of planTree, without a
restriction on joins or on the height of the tree.
-/
import Contract.Proof.DnbDeadPrepare

namespace Contract.PE

open DNB PeProof PeProof.Abs PeProof.Keys

variable {cf : Cfg} {i : Time} {s : Tree}

theorem seg_emit_dead (hcf : cf.Ok) {f g h : Nat} {root : Option NodeId}
    {E : List (Nat × NodeId)} {ops : List Op} {v v' : VN} {runs : List Run}
    {acc0 acc1 acc2 : Acc} {space : Bool} {c0 r' : NodeId}
    (hs : SOk cf i s) (hfresh : ∀ z, acc0.next ≤ z → s.obj z = none)
    (ho : OldSeg cf s g root E) (hp : PlanSeg cf i s g root E ops h v runs acc0 acc1)
    (hsafe : WritesDeadSafe cf acc1.ws)
    (hset : settleRoot cf i s f g v space = some (some v'))
    (he : emit cf i s v' acc1 = some ([(c0, r')], acc2)) : WritesDeadSafe cf acc2.ws := by
  have h01 : acc0.next ≤ acc1.next := chain_next hp.chain
  have hE's : (content h (absV s h v)).Pairwise CvLtA := e_content_sorted hp.wfe
  have hPs : (pays v).Pairwise CvLtA := hE's.sublist (pays_sublist h hp.vok)
  obtain ⟨h', hroot, hrok', heok', hB', _, _⟩ :=
    settle_root_own hcf (Or.inr hp.vok) hp.eok (e_hB hp hPs) hset
  have hvok' : VOk cf s g h' v' := settle_vok hcf hp.vok hset hrok'
  have hwfe' : WFE h' 0 none (fin s h' v') := Root.wf hroot 0 hp.wfe
  have hBnd := e_B_nodup ho hfresh (acc1.next - acc0.next)
  have hUnd : (Ui s v').Nodup :=
    e_subperm_nodup ((List.sublist_append_left _ _).subperm.trans hB') hBnd
  have hfresh1 : ∀ x, acc1.next ≤ x → s.obj x = none := fun x hx => hfresh x (le_trans h01 hx)
  exact emit_dead_main hcf hs h' hvok' heok' hUnd hfresh1
    (pieces_of_inord hcf heok' (wfe_inord hwfe')) he hsafe

theorem f_tail_dead (hcf : cf.Ok)
    {f g h : Nat} {root : Option NodeId} {E : List (Nat × NodeId)}
    {ops : List Op} {v : VN} {runs : List Run} {acc0 acc1 acc' : Acc} {res : Option NodeId}
    (hpre : SegPre cf i s g root ops acc0)
    (ho : OldSeg cf s g root E) (hp : PlanSeg cf i s g root E ops h v runs acc0 acc1)
    (hruns : ∀ r ∈ runs, RunDeadSafe cf r)
    (ht : (match settleRoot cf i s f g v false with
      | none => none
      | some none => some (none, acc1)
      | some (some v') =>
        match emit cf i s v' acc1 with
        | some ([(_, y)], acc) => some (some y, acc)
        | _ => none) = some (res, acc')) :
    WritesDeadSafe cf acc0.ws → WritesDeadSafe cf acc'.ws := by
  intro hs0
  have hs1 := chain_dead_safe hp.chain hruns hs0
  split at ht
  · cases ht
  · simp only [Option.some.injEq, Prod.mk.injEq] at ht
    exact ht.2 ▸ hs1
  · rename_i v' hset
    split at ht
    · rename_i c0 y acc2 he
      simp only [Option.some.injEq, Prod.mk.injEq] at ht
      obtain ⟨rfl, rfl⟩ := ht
      exact seg_emit_dead hcf hpre.sok hpre.fresh ho hp hs1 hset he
    · cases ht

theorem dead_f_step (hcf : cf.Ok) {f : Nat} (ID : DeadTreeIH cf i s f) :
    ∀ (root : Option NodeId) (g : Nat) (ops : List Op) (acc : Acc) (res : Option NodeId)
      (acc' : Acc), SegPre cf i s g root ops acc →
      planTree cf i s (f + 1) root g ops acc = some (res, acc') →
      WritesDeadSafe cf acc.ws → WritesDeadSafe cf acc'.ws := by
  intro root g ops acc res acc' hpre hpt
  have IH := f_all hcf (i := i) (s := s) f
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
        obtain ⟨runs, ho, hp, hruns⟩ := f_old_dead hcf IH ID hpre hsh hg hnd hplan
        exact f_tail_dead hcf hpre ho hp hruns hpt
  | none =>
    cases hag : applyGroups cf i s f g [] ((ops.map (segAt g)).eraseDups) ops acc with
    | none => simp [hag] at hpt
    | some p =>
      obtain ⟨es, acc1⟩ := p
      cases hmk : mkNode cf i s none g 0 false (es.map (fun e => (e.1, VN.old e.2))) with
      | none => simp [hag, hmk] at hpt
      | some v =>
        simp only [hag, hmk, Option.map_some] at hpt
        obtain ⟨runs, ho, hp, hruns⟩ := f_new_dead hcf IH ID hpre hag hmk
        exact f_tail_dead hcf hpre ho hp hruns hpt

theorem dead_f_all (hcf : cf.Ok) : ∀ F, DeadTreeIH cf i s F := by
  intro F
  induction F with
  | zero => intro f hf; omega
  | succ F IH =>
    intro f hf root g ops acc res acc' hpre hpt
    rcases Nat.lt_succ_iff_lt_or_eq.mp hf with hlt | rfl
    · exact IH f hlt root g ops acc res acc' hpre hpt
    · cases f with
      | zero => simp [planTree] at hpt
      | succ f =>
        exact dead_f_step hcf (fun ff hff => IH ff (by omega))
          root g ops acc res acc' hpre hpt

/-- Every written key node satisfies DeadOK; the initial write accumulator
may contain values and already safe key writes. -/
theorem planTree_dead_safe (hcf : cf.Ok) {f g : Nat} {root : Option NodeId}
    {ops : List Op} {acc acc' : Acc} {res : Option NodeId}
    (hpre : SegPre cf i s g root ops acc)
    (hp : planTree cf i s f root g ops acc = some (res, acc')) :
    WritesDeadSafe cf acc.ws → WritesDeadSafe cf acc'.ws :=
  dead_f_all hcf (f + 1) f (Nat.lt_succ_self f) root g ops acc res acc' hpre hp

end Contract.PE
