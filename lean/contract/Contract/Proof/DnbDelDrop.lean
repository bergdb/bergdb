/-
bergdb 030-36: dropping empty children without joining the others. Each
empty child consumes at least one counted delete; retained children keep
their compare value and give the parent at most the klongs counted for them.
-/
import Contract.Proof.DnbDelKids

namespace Contract.PE

open DNB PeProof

variable {cf : Cfg} {i : Time} {s : Tree}

def kept (es : List (Nat × VN)) : List (Nat × VN) := es.filter (fun e => !e.2.isEmpty)
def entries (es : List (Nat × VN)) : List (Nat × Option NodeId) := es.flatMap (fun e => ents e.1 e.2)
theorem entries_cons (e : Nat × VN) (es : List (Nat × VN)) :
    entries (e :: es) = ents e.1 e.2 ++ entries es := rfl

def childRs (b : Nat) (s : Tree) (fs g : Nat) (lv : List (Nat × NodeId))
    (os : List (List Op)) : List SR :=
  ((lv.zip os).filter (fun e => !e.2.isEmpty)).map (fun e => sbPlan b s fs e.1.2 g e.2 false)

theorem vcostL_renameHead (c : Nat) (es : List (Nat × VN)) :
    vcostL (renameHead c es) = vcostL es := by
  cases es <;> rfl

theorem removed_cons_le {α : Type} (q : Nat × NodeId) (lv : List (Nat × NodeId))
    (E F : List (Nat × α)) :
    (removedCvs (q :: lv) (E ++ F)).length ≤
      (if E.any (fun e => e.1 == q.1) then 0 else 1) + (removedCvs lv F).length := by
  simp only [removedCvs, List.filter_cons, List.any_append, List.length_map]
  have hsub : (lv.filter (fun e => !((E ++ F).any (fun e' => e'.1 == e.1)))).Sublist
      (lv.filter (fun e => !(F.any (fun e' => e'.1 == e.1)))) := by
    simpa only [List.filter_filter, List.any_append, Bool.not_or, Bool.and_comm] using
      (List.filter_sublist (l := lv.filter (fun e => !(F.any (fun e' => e'.1 == e.1))))
        (p := fun e => !(E.any (fun e' => e'.1 == e.1))))

  have := hsub.length_le
  split <;> split <;> simp_all <;> omega

theorem ents_any_head (c : Nat) (w : VN) : (ents c w).any (fun e => e.1 == c) = true := by
  cases w with
  | old y => simp [ents]
  | node base g h j es F dec =>
    cases dec with
    | same => cases base <;> simp [ents]
    | append => cases base <;> simp [ents]
    | parts k =>
      simp only [ents]
      split
      · have hh := partEnts_head c F k j
        cases he : partEnts c F k j with
        | nil => rw [he] at hh; cases hh
        | cons a r => rw [he] at hh; simp at hh; simp [hh]
      · simp

theorem child_ents_added_none {b c y g h : Nat} {lv : List (Nat × NodeId)} {w : VN}
    {acc acc' : Acc} {r : SR} (hl : lv.lookup c = some y)
    (hc : PlanSpecD b s g h y false w acc acc' r) :
    ∀ e ∈ ents c w, isAdded lv e = true → e.2 = none := by
  obtain ⟨n, es, Fl, dec, _, rfl, _, _, _⟩ := hc.shape
  cases dec with
  | parts k =>
    simp only [ents]
    split
    · exact fun e he _ => partEnts_none c Fl k false e he
    · intro e he _; simp only [List.mem_singleton] at he; subst he; rfl
  | same =>
    intro e he ha
    simp only [ents, List.mem_singleton] at he
    subst he
    rw [isAdded_some hl] at ha; cases ha
  | append =>
    intro e he ha
    simp only [ents, List.mem_singleton] at he
    subst he
    rw [isAdded_some hl] at ha; cases ha

structure DropOut (b : Nat) (cf : Cfg) (s : Tree) (fs g : Nat)
    (lvAll lv : List (Nat × NodeId)) (os : List (List Op))
    (es : List (Nat × VN)) (acc acc1 : Acc) : Prop where
  kw : kw acc1 + vcostL (kept es) + 4 * ((childRs b s fs g lv os).map (·.nd)).sum ≤
    kw acc + ((childRs b s fs g lv os).map (·.cnt)).sum
  lost : lv.length ≤ (kept es).length + ((childRs b s fs g lv os).map (·.nd)).sum
  added : ((entries (kept es)).filter (isAdded lvAll)).length ≤
    ((childRs b s fs g lv os).map (·.up)).sum
  len : (entries (kept es)).length ≤ lv.length + ((entries (kept es)).filter (isAdded lvAll)).length
  removed : (removedCvs lv (entries (kept es))).length ≤ ((childRs b s fs g lv os).map (·.nd)).sum
  same0 : ((childRs b s fs g lv os).map (·.nd)).sum = 0 →
    ((entries (kept es)).filter (isAdded lvAll)).length = 0 →
    entries (kept es) = lv.map (fun q => (q.1, some q.2))
  cvs0 : ((childRs b s fs g lv os).map (·.nd)).sum = 0 → (kept es).map (·.1) = lv.map (·.1)
  head0 : ((childRs b s fs g lv os).map (·.nd)).sum = 0 →
    (entries (kept es)).head?.map (·.1) = lv.head?.map (·.1)
  own : ∀ e ∈ entries (kept es), isAdded lvAll e = true → e.2 = none

/-- The children, allowing empty plans to be dropped. -/
theorem kids_drop {b g h F0 fs : Nat} {lvAll : List (Nat × NodeId)} (P : Nat → NodeId → List Op → Prop)
    (hchild : ∀ f < F0, ∀ c y o acc w acc', (c, y) ∈ lvAll → o ≠ [] → P c y o →
      plan cf i s f y g h o acc = some (w, acc') →
      PlanSpecD b s g h y false w acc acc' (sbPlan b s fs y g o false))
    (hm : 2 ≤ cf.m)
    (hfill : ∀ c y, (c, y) ∈ lvAll → ∀ n, DNB.getKey s y = some n → cf.m ≤ (live n.ks).length)
    (hlook : ∀ c y, (c, y) ∈ lvAll → lvAll.lookup c = some y) :
    ∀ (lv : List (Nat × NodeId)) (os : List (List Op)) (f : Nat) (acc : Acc)
      (es : List (Nat × VN)) (acc1 : Acc), lv ⊆ lvAll → (∀ cy o, (cy, o) ∈ lv.zip os → P cy.1 cy.2 o) → f ≤ F0 →
      planKids cf i s f g (h + 1) lv os acc = some (es, acc1) →
      DropOut b cf s fs g lvAll lv os es acc acc1
  | _, _, 0, _, _, _, _, _, _, hp => by simp [planKids] at hp
  | [], os, f + 1, acc, es, acc1, _, _, _, hp => by
    simp only [planKids, Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    exact ⟨by simp [kept, vcostL, childRs], by simp [kept, childRs], by simp [kept, entries, childRs],
      by simp [kept, entries], by simp [kept, entries, removedCvs, childRs], fun _ _ => rfl,
      fun _ => rfl, fun _ => rfl, by simp [kept, entries]⟩
  | (c, y) :: rest, [], f + 1, acc, es, acc1, _, _, _, hp => by simp [planKids] at hp
  | (c, y) :: rest, o :: os, f + 1, acc, es, acc1, hsub, hos, hf, hp => by
    have hmem : (c, y) ∈ lvAll := hsub List.mem_cons_self
    have hsub' : rest ⊆ lvAll := fun q hq => hsub (List.mem_cons_of_mem _ hq)
    have hos' : ∀ cy o', (cy, o') ∈ rest.zip os → P cy.1 cy.2 o' :=
      fun cy o' ho' => hos cy o' (List.mem_cons_of_mem _ ho')
    have hl := hlook c y hmem
    simp only [planKids, Nat.add_sub_cancel] at hp
    split at hp
    · rename_i hoe
      cases hk : planKids cf i s f g (h + 1) rest os acc with
      | none => rw [hk] at hp; cases hp
      | some q =>
        obtain ⟨es', acc2⟩ := q
        rw [hk] at hp
        simp only [Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp
        have ih := kids_drop P hchild hm hfill hlook rest os f acc es' acc2 hsub' hos' (by omega) hk
        have hz : childRs b s fs g ((c, y) :: rest) (o :: os) = childRs b s fs g rest os := by
          simp [childRs, hoe]
        have ha0 : isAdded lvAll (c, some y) = false := isAdded_some hl
        have hke : kept ((c, VN.old y) :: es') = (c, VN.old y) :: kept es' := by simp [kept, VN.isEmpty]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          (try simp only [hz])
        · rw [hke]; simp only [vcostL, vcost, zero_add]; exact ih.kw
        · rw [hke]; simp only [List.length_cons]; have := ih.lost; omega
        · simpa only [hke, entries_cons, ents, List.singleton_append, List.filter_cons,
            ha0, Bool.false_eq_true, ↓reduceIte] using ih.added
        · simp only [hke, entries_cons, ents, List.singleton_append, List.filter_cons,
            ha0, Bool.false_eq_true, ↓reduceIte, List.length_cons]
          have := ih.len; omega
        · have hr := removed_cons_le (c, y) rest (ents c (.old y)) (entries (kept es'))
          simp only [ents, List.any_cons, beq_self_eq_true, Bool.true_or, ↓reduceIte, zero_add] at hr
          exact le_trans hr ih.removed
        · intro hn ha
          simp only [hke, entries_cons, ents, List.singleton_append] at ha ⊢
          simp only [List.filter_cons, ha0, Bool.false_eq_true, ↓reduceIte] at ha
          rw [ih.same0 hn ha]; rfl
        · intro hn; simp [hke, ih.cvs0 hn]
        · intro _; simp [hke, entries, ents]
        · intro e he ha
          rw [hke, entries_cons, List.mem_append] at he
          rcases he with he | he
          · simp only [ents, List.mem_singleton] at he
            subst he
            rw [ha0] at ha; cases ha
          · exact ih.own e he ha
    · rename_i hoe
      have hone : o ≠ [] := by simpa using hoe
      cases hpl : plan cf i s f y g h o acc with
      | none => rw [hpl] at hp; cases hp
      | some q =>
        obtain ⟨w, acc2⟩ := q
        rw [hpl] at hp
        simp only at hp
        cases hk : planKids cf i s f g (h + 1) rest os acc2 with
        | none => rw [hk] at hp; cases hp
        | some q =>
          obtain ⟨es', acc3⟩ := q
          rw [hk] at hp
          simp only [Option.some.injEq, Prod.mk.injEq] at hp
          obtain ⟨rfl, rfl⟩ := hp
          have hc := hchild f (by omega) c y o acc w acc2 hmem hone (hos (c, y) o List.mem_cons_self) hpl
          have ih := kids_drop P hchild hm hfill hlook rest os f acc2 es' acc3 hsub' hos' (by omega) hk
          have hz : childRs b s fs g ((c, y) :: rest) (o :: os) =
              sbPlan b s fs y g o false :: childRs b s fs g rest os := by simp [childRs, hoe]
          obtain ⟨e1, e2, e3, e4⟩ := child_entsD hl hc
          obtain ⟨T, hT, hkw⟩ := hc.kw
          simp only [rootT, Bool.false_eq_true, false_and, ↓reduceIte, add_zero] at hkw
          have hempty : w.isEmpty = true → 1 ≤ (sbPlan b s fs y g o false).nd := by
            intro he
            obtain ⟨n, es0, F, dec, hn, rfl, _, hlen, _⟩ := hc.shape
            have hm' := hfill c y hmem n hn
            simp only [VN.isEmpty, List.isEmpty_iff] at he
            rw [he] at hlen
            simp only [List.length_nil] at hlen
            omega
          by_cases he : w.isEmpty = true
          · have hke : kept ((c, w) :: es') = kept es' := by simp [kept, he]
            have hnd1 := hempty he
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
              (try simp only [hz, List.map_cons, List.sum_cons])
            · rw [hke]; have := ih.kw; omega
            · rw [hke]; simp only [List.length_cons]; have := ih.lost; omega
            · rw [hke]; have := ih.added; omega
            · rw [hke]; simp only [List.length_cons]; have := ih.len; omega
            · rw [hke]
              have hr := removed_cons_le (c, y) rest [] (entries (kept es'))
              simp only [List.nil_append, List.any_nil, Bool.false_eq_true, ↓reduceIte] at hr
              have := ih.removed; omega
            · intro hn; omega
            · intro hn; omega
            · intro hn; omega
            · rw [hke]; exact ih.own
          · have he0 : w.isEmpty = false := by simpa using he
            have hke : kept ((c, w) :: es') = (c, w) :: kept es' := by simp [kept, he0]
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
              (try simp only [hz, List.map_cons, List.sum_cons])
            · rw [hke]; simp only [vcostL]; have := ih.kw; omega
            · rw [hke]; simp only [List.length_cons]; have := ih.lost; omega
            · simp only [hke, entries_cons, List.filter_append, List.length_append]
              have := ih.added; omega
            · simp only [hke, entries_cons, List.filter_append, List.length_append, List.length_cons]
              have := ih.len; omega
            · have hr := removed_cons_le (c, y) rest (ents c w) (entries (kept es'))
              rw [ents_any_head] at hr
              simp only [↓reduceIte, zero_add] at hr
              rw [hke, entries_cons]
              have := ih.removed
              exact le_trans hr (by omega)
            · intro hn ha
              simp only [hke, entries_cons, List.filter_append, List.length_append] at ha ⊢
              rw [e3 (by omega), ih.same0 (by omega) (by omega)]; rfl
            · intro hn; simp [hke, ih.cvs0 (by omega : ((childRs b s fs g rest os).map (·.nd)).sum = 0)]
            · intro _
              simp only [hke, entries_cons, List.head?_cons]
              rw [List.head?_append_of_ne_nil (ents c w) (ents_ne c w)]
              exact e4
            · intro e he ha
              rw [hke, entries_cons, List.mem_append] at he
              rcases he with he | he
              · exact child_ents_added_none hl hc e he ha
              · exact ih.own e he ha

end Contract.PE
