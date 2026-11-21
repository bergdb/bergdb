/-
bergdb 030-37: every successful old-tree plan has the structural virtual
fill conditions, without any restriction on joins or on transaction
contents. Next-segment payload fill and emit are separate obligations.
-/
import Contract.Proof.DnbFillRebalance

namespace Contract.PE

open DNB PeProof

variable {cf : Cfg} {i : Time} {s : Tree}

def PlanVFill (cf : Cfg) (i : Time) (s : Tree) (f : Nat) : Prop :=
  ∀ (x g h : Nat) (ops : List Op) (acc acc' : Acc) (v : VN) (isRoot : Bool),
    Shaped cf s g h x → Filled cf s isRoot x →
    plan cf i s f x g h ops acc = some (v, acc') → VFill cf i s g isRoot h v

def KidsVFill (cf : Cfg) (i : Time) (s : Tree) (f : Nat) : Prop :=
  ∀ (g h : Nat) (lv : List (Nat × NodeId)) (os : List (List Op)) (acc acc' : Acc)
    (es : List (Nat × VN)),
    (∀ c y, (c, y) ∈ lv → Shaped cf s g h y ∧ Filled cf s false y) →
    planKids cf i s f g (h + 1) lv os acc = some (es, acc') →
    ∀ e ∈ es, VFill cf i s g false h e.2

theorem plan_vfill_all (hm2 : 2 ≤ cf.m) :
    ∀ f, PlanVFill cf i s f ∧ KidsVFill cf i s f := by
  intro f
  induction f using Nat.strong_induction_on with
  | _ f IH =>
    cases f with
    | zero =>
      constructor
      · intro x g h ops acc acc' v root hs hf hp
        simp [plan] at hp
      · intro g h lv os acc acc' es hkids hp
        simp [planKids] at hp
    | succ f =>
      have IP := (IH f (by omega)).1
      have IK := (IH f (by omega)).2
      constructor
      · intro x g h ops acc acc' v root hs hf hp
        obtain ⟨n, hobj, hk, _, _, _, _⟩ := shaped_getKey hs
        have hbase : ∀ n', (some x).bind (getKey s) = some n' → root = false →
            cf.m ≤ (live n'.ks).length := by
          intro n' hn hr
          simp only [Option.bind_some, hk, Option.some.injEq] at hn
          cases hn
          exact (filled_key hf hobj).2.1 hm2 hr
        rw [plan.eq_def] at hp
        simp only at hp
        rw [hk] at hp
        cases h with
        | zero =>
          simp only [beq_self_eq_true, ↓reduceIte] at hp
          cases ha : applyGroups cf i s f g (live n.ks) ((ops.map (segAt g)).eraseDups) ops acc with
          | none => rw [ha] at hp; cases hp
          | some q =>
            obtain ⟨es, acc1⟩ := q
            rw [ha] at hp
            simp only at hp
            cases hm : mkNode cf i s (some x) g 0 false (es.map (fun e => (e.1, VN.old e.2))) with
            | none => rw [hm] at hp; cases hp
            | some w =>
              rw [hm] at hp
              simp only [Option.some.injEq, Prod.mk.injEq] at hp
              obtain ⟨rfl, rfl⟩ := hp
              apply mkNode_vfill_leaf ?_ hbase hm
              intro e he
              obtain ⟨q, _, rfl⟩ := List.mem_map.mp he
              exact ⟨q.2, rfl⟩
        | succ h =>
          simp only [Nat.add_one_ne_zero, beq_iff_eq, ↓reduceIte, Nat.add_sub_cancel] at hp
          have hleaf : n.leaf = false := by
            obtain ⟨n', ho', _, _, hl, _, _⟩ := shaped_getKey hs
            rw [hobj] at ho'; cases ho'; simpa using hl
          have hkids : ∀ c y, (c, y) ∈ live n.ks → Shaped cf s g h y ∧ Filled cf s false y := by
            intro c y hcy
            exact ⟨(shaped_inner hs hobj).2 c y hcy, (filled_key hf hobj).2.2.2 c y hcy hleaf⟩
          cases ha : planKids cf i s f g (h + 1) (live n.ks) (route (segAt g) (live n.ks) ops) acc with
          | none => rw [ha] at hp; cases hp
          | some q =>
            obtain ⟨es, acc1⟩ := q
            rw [ha] at hp
            simp only at hp
            have hes := IK g h _ _ acc acc1 es hkids ha
            cases hr : rebalance cf i s (f + 1) g h es with
            | none => rw [hr] at hp; cases hp
            | some es2 =>
              rw [hr] at hp
              simp only at hp
              obtain ⟨hc2, hn2, he2⟩ := rebalance_vfill hm2 (f + 1) g h es es2 hr hes
              cases hm : mkNode cf i s (some x) g (h + 1) false es2 with
              | none => rw [hm] at hp; cases hp
              | some w =>
                rw [hm] at hp
                simp only [Option.some.injEq, Prod.mk.injEq] at hp
                obtain ⟨rfl, rfl⟩ := hp
                exact mkNode_vfill_inner hc2 hn2 he2 hbase hm
      · intro g h lv os acc acc' es hkids hp
        cases lv with
        | nil =>
          simp only [planKids, Option.some.injEq, Prod.mk.injEq] at hp
          obtain ⟨rfl, rfl⟩ := hp
          simp
        | cons q lv =>
          obtain ⟨c, y⟩ := q
          cases os with
          | nil => simp [planKids] at hp
          | cons o os =>
            obtain ⟨hs, hf⟩ := hkids c y List.mem_cons_self
            have htail : ∀ c y, (c, y) ∈ lv → Shaped cf s g h y ∧ Filled cf s false y :=
              fun c y he => hkids c y (List.mem_cons_of_mem _ he)
            simp only [planKids, Nat.add_sub_cancel] at hp
            split at hp
            · cases ht : planKids cf i s f g (h + 1) lv os acc with
              | none => rw [ht] at hp; cases hp
              | some q =>
                obtain ⟨es1, acc1⟩ := q
                rw [ht] at hp
                simp only [Option.some.injEq, Prod.mk.injEq] at hp
                obtain ⟨rfl, rfl⟩ := hp
                intro e he
                rcases List.mem_cons.mp he with rfl | he
                · exact VFill.old hs hf
                · exact IK g h lv os acc acc1 es1 htail ht e he
            · cases ht : plan cf i s f y g h o acc with
              | none => rw [ht] at hp; cases hp
              | some q =>
                obtain ⟨w, acc1⟩ := q
                rw [ht] at hp
                simp only at hp
                cases htailp : planKids cf i s f g (h + 1) lv os acc1 with
                | none => rw [htailp] at hp; cases hp
                | some q =>
                  obtain ⟨es1, acc2⟩ := q
                  rw [htailp] at hp
                  simp only [Option.some.injEq, Prod.mk.injEq] at hp
                  obtain ⟨rfl, rfl⟩ := hp
                  intro e he
                  rcases List.mem_cons.mp he with rfl | he
                  · exact IP y g h o acc acc1 w false hs hf ht
                  · exact IK g h lv os acc1 acc2 es1 htail htailp e he

/-- No join restriction is needed for the virtual fill conditions of a
successful plan, including arbitrary higher inner joins. -/
theorem plan_vfill (hm2 : 2 ≤ cf.m) {f x g h : Nat} {ops : List Op} {acc acc' : Acc} {v : VN}
    {isRoot : Bool} (hs : Shaped cf s g h x) (hf : Filled cf s isRoot x)
    (hp : plan cf i s f x g h ops acc = some (v, acc')) : VFill cf i s g isRoot h v :=
  (plan_vfill_all hm2 f).1 x g h ops acc acc' v isRoot hs hf hp

end Contract.PE
