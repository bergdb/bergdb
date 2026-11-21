/-
bergdb 030-37: recursive DeadOK through emit and emitKids. The existing
realization proof supplies matching symbolic and actual final entries.
-/
import Contract.Proof.DnbDeadEmit

namespace Contract.PE

open DNB PeProof PeProof.Abs

variable {cf : Cfg} {i : Time} {s : Tree}

theorem emitKids_dead (hcf : cf.Ok) (hs : SOk cf i s) {g h : Nat}
    (IH : ∀ {v : VN} {acc : Acc} {E : List (Nat × NodeId)} {acc' : Acc},
      VOk cf s g h v → EOk cf i s g h v → (Ui s v).Nodup →
      (∀ x, acc.next ≤ x → s.obj x = none) →
      (∀ e ∈ finEnts 0 v (fin s h v), InOrd h e.2) →
      emit cf i s v acc = some (E, acc') → WritesDeadSafe cf acc.ws → WritesDeadSafe cf acc'.ws) :
    ∀ (es : List (Nat × VN)) {acc : Acc} {F0 : List (Nat × NodeId)} {acc1 : Acc},
      (∀ e ∈ es, VOk cf s g h e.2) → (∀ e ∈ es, EOk cf i s g h e.2) →
      (es.flatMap (fun e => Ui s e.2)).Nodup →
      (∀ x, acc.next ≤ x → s.obj x = none) →
      (∀ e ∈ es.flatMap (fun e => finEnts e.1 e.2 (fin s h e.2)), InOrd h e.2) →
      emitKids cf i s es acc = some (F0, acc1) →
      WritesDeadSafe cf acc.ws → WritesDeadSafe cf acc1.ws
  | [], acc, F0, acc1, _, _, _, _, _, he, hsafe => by
    rw [emitKids.eq_1] at he
    simp only [Option.some.injEq, Prod.mk.injEq] at he
    exact he.2 ▸ hsafe
  | (c, w) :: rest, acc, F0, acc1, hv, he', hnd, hfresh, hord, he, hsafe => by
    rw [emitKids.eq_2] at he
    cases hw : emit cf i s w acc with
    | none => rw [hw] at he; cases he
    | some r =>
    obtain ⟨E, accA⟩ := r
    rw [hw] at he
    simp only at he
    cases hr : emitKids cf i s rest accA with
    | none => rw [hr] at he; cases he
    | some r' =>
    obtain ⟨F, accB⟩ := r'
    rw [hr] at he
    simp only [Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    simp only [List.flatMap_cons] at hnd hord
    have hvw : VOk cf s g h w := hv (c, w) List.mem_cons_self
    have hew : EOk cf i s g h w := he' (c, w) List.mem_cons_self
    have hnd' := List.nodup_append.mp hnd
    have hordw : ∀ e ∈ finEnts 0 w (fin s h w), InOrd h e.2 := by
      intro e he
      obtain ⟨e', he', h2⟩ := mem_snd_of_rename (c := c) he
      rw [← finEnts_rename] at he'
      exact h2 ▸ hord e' (List.mem_append_left _ he')
    have hsafeA := IH hvw hew hnd'.1 hfresh hordw hw hsafe
    obtain ⟨W, hW, _⟩ := emit_main hcf hs h hvw hew hnd'.1 hfresh hordw hw
    have hfA : ∀ x, accA.next ≤ x → s.obj x = none := fun x hx =>
      hfresh x (by have := hW.next; nomega)
    exact emitKids_dead hcf hs IH rest
      (fun e he => hv e (List.mem_cons_of_mem _ he))
      (fun e he => he' e (List.mem_cons_of_mem _ he)) hnd'.2.1 hfA
      (fun e he => hord e (List.mem_append_right _ he)) hr hsafeA

theorem emit_dead_main (hcf : cf.Ok) (hs : SOk cf i s) {g : Nat} : ∀ (h : Nat) {v : VN} {acc : Acc}
    {E : List (Nat × NodeId)} {acc' : Acc},
    VOk cf s g h v → EOk cf i s g h v → (Ui s v).Nodup → (∀ x, acc.next ≤ x → s.obj x = none) →
    (∀ e ∈ finEnts 0 v (fin s h v), InOrd h e.2) → emit cf i s v acc = some (E, acc') →
    WritesDeadSafe cf acc.ws → WritesDeadSafe cf acc'.ws
  | 0, v, acc, E, acc', hv, he, hnd, hfresh, hord, hem, hsafe => by
    cases v with
    | old y =>
      rw [emit.eq_1] at hem
      simp only [Option.some.injEq, Prod.mk.injEq] at hem
      obtain ⟨rfl, rfl⟩ := hem
      exact hsafe
    | node b g' h' join es F dec =>
      obtain ⟨rfl, rfl⟩ := hv.ht
      have hv' := hv
      cases hv with
      | leaf hold hF _ =>
      rw [emit_node, emitKids_old es hold] at hem
      simp only [Option.bind_some, beq_self_eq_true, ite_true] at hem
      have hn : NH cf i s g' 0 b join es F dec [] acc :=
        ⟨hv', he, by rw [Ui_node]; simp, by rw [Ui_node] at hnd; simpa using hnd, by simp,
          hfresh, hord⟩
      exact node_emit_dead hcf hs hn (leaf_cres hold hF) hsafe hem
  | h + 1, v, acc, E, acc', hv, he, hnd, hfresh, hord, hem, hsafe => by
    cases v with
    | old y =>
      rw [emit.eq_1] at hem
      simp only [Option.some.injEq, Prod.mk.injEq] at hem
      obtain ⟨rfl, rfl⟩ := hem
      exact hsafe
    | node b g' h' join es F dec =>
      obtain ⟨rfl, rfl⟩ := hv.ht
      have hv' := hv
      have he' := he
      cases hv with
      | inner hk _ _ hF _ =>
      rw [emit_node] at hem
      cases hkr : emitKids cf i s es acc with
      | none => rw [hkr] at hem; cases hem
      | some r =>
      obtain ⟨F0, acc1⟩ := r
      rw [hkr] at hem
      simp only [Option.bind_some, Nat.add_one_ne_zero, beq_iff_eq, ite_false] at hem
      cases he with
      | node _ _ _ hke =>
      have hUi : Ui s (.node b g' (h + 1) join es F dec) =
          b.toList ++ es.flatMap (fun e => Ui s e.2) := by rw [Ui_node]; simp
      have hpays : pays (.node b g' (h + 1) join es F dec) = es.flatMap (fun e => pays e.2) := by
        rw [pays_node]; simp
      have hnd' : (b.toList ++ es.flatMap (fun e => Ui s e.2)).Nodup := hUi ▸ hnd
      have hordk := pieces_kids hcf he' hord
      have hordc : ∀ e ∈ es.flatMap (fun e => finEnts e.1 e.2 (fin s h e.2)), InOrd h e.2 := by
        intro e hm
        obtain ⟨e', hm', h2⟩ := mem_snd_of_rename (c := 0) hm
        exact h2 ▸ hordk e' hm'
      have hex : ∀ z ∈ es.flatMap (fun e => Ui s e.2), s.obj z ≠ none := by
        intro z hz
        obtain ⟨e, hm, hz⟩ := List.mem_flatMap.mp hz
        exact ui_exists h (hk e hm) (hke e hm (by omega)) z hz
      obtain ⟨W0, hW0, hsh0, hm0, hcv0, ht0⟩ := kids_spec hcf hs
        (fun hv he hnd hf ho hem => emit_main hcf hs h hv he hnd hf ho hem) es hk
        (fun e hm => hke e hm (by omega)) (List.nodup_append.mp hnd').2.1 hfresh hordc hkr
      have hsafe1 := emitKids_dead hcf hs
        (fun hv he hnd hf ho hem hs0 => emit_dead_main hcf hs h hv he hnd hf ho hem hs0)
        es hk (fun e hm => hke e hm (by omega)) (List.nodup_append.mp hnd').2.1
        hfresh hordc hkr hsafe
      have hc : CRes cf i s g' (h + 1) (.node b g' (h + 1) join es F dec)
          (es.flatMap (fun e => Ui s e.2)) acc acc1 W0 (renameHead 0 F0) F := by
        refine ⟨hW0, hsh0, ?_, renameHead_cvs 0 hcv0, ?_⟩
        · rw [hF]
          exact forall₂_renameHead 0 (fun _ _ h => ⟨rfl, h.2⟩) hm0
        · intro T PB hT
          rw [hpays] at hT
          obtain ⟨hh, hr, hwn, hrc⟩ := ht0 T PB hT
          refine ⟨forall₂_renameHead 0 (fun _ _ h => ⟨rfl, h.2⟩) hh, fun e hm => ?_, fun f hf => ?_,
            hwn, fun w hw => ?_⟩
          · obtain ⟨e', hm', h2⟩ := renameHead_mem hm
            obtain ⟨a, _, hrel⟩ := forall₂_exists hh e' hm'
            obtain ⟨n, hn, _⟩ := hrel.2.obj
            rw [← h2, hn]; simp
          · rw [renameHead_flatMap_snd, hpays]
            exact hr f (by rw [Cfg.lev_succ] at hf; omega)
          · obtain ⟨e, he, hr'⟩ := hrc w hw
            obtain ⟨e', he', h2⟩ := mem_snd_of_rename (c := 0) he
            exact ⟨e', he', by rw [h2]; exact hr'⟩
      have hn : NH cf i s g' (h + 1) b join es F dec (es.flatMap (fun e => Ui s e.2)) acc :=
        ⟨hv', he', hUi, hnd', hex, hfresh, hord⟩
      exact node_emit_dead hcf hs hn hc hsafe1 hem

end Contract.PE
