/-
bergdb 030-29: an inner node's children, for a transaction of puts. Each child
with operations is planned (`plan`), the others kept; what each planned child
writes and gives its parent is bounded by Java's count of it (`ChildSpec`, the
induction's claim one height down). Over the children (`kids_puts`): the key
nodes written, the parent's added entries (at most the klongs Java gives it),
its final list's length, that no compare value is removed, and that no child
is empty or small, so that `rebalance` joins nothing (`rebalance_id`).
-/
import Contract.Proof.DnbFresh

namespace Contract.PE

open DNB PeProof

variable {cf : Cfg} {i : Time} {s : Tree}

/-- What the induction gives of a child y planned with operations o into w, at
height h of segment g, against Java's count r of it (not a tree's root). -/
structure ChildSpec (b : Nat) (s : Tree) (g h : Nat) (y : NodeId) (w : VN) (acc acc' : Acc)
    (r : SR) : Prop where
  shape : ∃ n es Fl dec, DNB.getKey s y = some n ∧ w = .node (some y) g h false es Fl dec ∧
    (∀ k, dec = .parts k → 0 < r.ov ∧ k ≤ r.parts) ∧ (live n.ks).length ≤ Fl.length ∧ Fl ≠ []
  kw : kw acc' + vcost w ≤ kw acc + r.cnt
  nd : r.nd = 0
  up : r.up = if r.ov = 0 then 0 else r.parts
  parts : r.ov ≠ 0 → r.ov + 1 ≤ r.parts

theorem isAdded_some {lv : List (Nat × NodeId)} {c : Nat} {y : NodeId} (h : lv.lookup c = some y) :
    isAdded lv (c, some y) = false := by
  simp [isAdded, h]

theorem partEnts_none (cv : Nat) (F : List (Nat × Option NodeId)) (k : Nat) (join : Bool) :
    ∀ e ∈ partEnts cv F k join, e.2 = none := by
  unfold partEnts
  split
  · simp
  · intro e he
    simp only [List.mem_cons, List.mem_map] at he
    rcases he with rfl | ⟨_, _, rfl⟩ <;> rfl

theorem partEnts_head (cv : Nat) (F : List (Nat × Option NodeId)) (k : Nat) (join : Bool) :
    (partEnts cv F k join).head?.map (·.1) = some cv := by
  unfold partEnts; split <;> rfl

/-- One child's entries in its parent, against the parent's live list. -/
theorem child_ents {b : Nat} {lvAll : List (Nat × NodeId)} {c : Nat} {y : NodeId} {w : VN}
    {g h : Nat} {acc acc' : Acc} {r : SR} (hl : lvAll.lookup c = some y)
    (hc : ChildSpec b s g h y w acc acc' r) :
    ((ents c w).filter (isAdded lvAll)).length ≤ r.up ∧
      (ents c w).length ≤ 1 + ((ents c w).filter (isAdded lvAll)).length ∧
      (((ents c w).filter (isAdded lvAll)).length = 0 → ents c w = [(c, some y)]) ∧
      (ents c w).head?.map (·.1) = some c := by
  obtain ⟨n, es, Fl, dec, _, rfl, hdec, _, _⟩ := hc.shape
  cases dec with
  | parts k =>
    obtain ⟨hov, hk⟩ := hdec k rfl
    have hpl := hc.parts (by omega)
    rw [hc.up, ite_eq_right (by omega)]
    simp only [ents]
    split
    · rename_i hk2
      have hall : (partEnts c Fl k false).filter (isAdded lvAll) = partEnts c Fl k false := by
        rw [List.filter_eq_self]
        intro e he
        simp [isAdded, partEnts_none c Fl k false e he]
      rw [hall, partEnts_length c Fl (by omega) false]
      refine ⟨hk, by omega, fun h0 => by omega, partEnts_head c Fl k false⟩
    · have h1 : ([(c, none)] : List (Nat × Option NodeId)).filter (isAdded lvAll) = [(c, none)] := by
        simp [List.filter, isAdded]
      rw [h1]
      simp only [List.length_singleton, List.head?_cons, Option.map_some]
      refine ⟨by omega, by omega, fun h0 => by omega, trivial⟩
  | same => simp [ents, isAdded_some hl]
  | append => simp [ents, isAdded_some hl]

/-- What the children's list gives: see `kids_puts`. -/
structure KidsOut (b : Nat) (cf : Cfg) (s : Tree) (fs g : Nat) (lvAll lv : List (Nat × NodeId))
    (os : List (List Op)) (es : List (Nat × VN)) (acc acc1 : Acc) : Prop where
  kw : kw acc1 + vcostL es ≤ kw acc +
    ((((lv.zip os).filter (fun e => !e.2.isEmpty)).map (fun e => sbPlan b s fs e.1.2 g e.2 false)).map
      (·.cnt)).sum
  cvs : es.map (·.1) = lv.map (·.1)
  added : ((es.flatMap (fun e => ents e.1 e.2)).filter (isAdded lvAll)).length ≤
    ((((lv.zip os).filter (fun e => !e.2.isEmpty)).map (fun e => sbPlan b s fs e.1.2 g e.2 false)).map
      (·.up)).sum
  len : (es.flatMap (fun e => ents e.1 e.2)).length ≤
    lv.length + ((es.flatMap (fun e => ents e.1 e.2)).filter (isAdded lvAll)).length
  same : ((es.flatMap (fun e => ents e.1 e.2)).filter (isAdded lvAll)).length = 0 →
    es.flatMap (fun e => ents e.1 e.2) = lv.map (fun q => (q.1, some q.2))
  keep : ∀ q ∈ lv, (es.flatMap (fun e => ents e.1 e.2)).any (fun e => e.1 == q.1) = true
  small : ∀ e ∈ es, e.2.isEmpty = false ∧ (e.2.changed = true → 2 ≤ cf.m → cf.m ≤ e.2.size)
  nd : ((((lv.zip os).filter (fun e => !e.2.isEmpty)).map (fun e => sbPlan b s fs e.1.2 g e.2 false)).map
      (·.nd)).sum = 0
  head : (es.flatMap (fun e => ents e.1 e.2)).head?.map (·.1) = lv.head?.map (·.1)

/-- **The children, for puts.** -/
theorem kids_puts {b g h F0 fs : Nat} {lvAll : List (Nat × NodeId)} (P : List Op → Prop)
    (hchild : ∀ f < F0, ∀ c y o acc w acc', (c, y) ∈ lvAll → o ≠ [] → P o →
      plan cf i s f y g h o acc = some (w, acc') →
      ChildSpec b s g h y w acc acc' (sbPlan b s fs y g o false))
    (hfill : ∀ c y, (c, y) ∈ lvAll → ∀ n, DNB.getKey s y = some n →
      2 ≤ cf.m → cf.m ≤ (live n.ks).length)
    (hlook : ∀ c y, (c, y) ∈ lvAll → lvAll.lookup c = some y) :
    ∀ (lv : List (Nat × NodeId)) (os : List (List Op)) (f : Nat) (acc : Acc) (es : List (Nat × VN))
      (acc1 : Acc), lv ⊆ lvAll → (∀ o ∈ os, P o) → f ≤ F0 →
      planKids cf i s f g (h + 1) lv os acc = some (es, acc1) →
      KidsOut b cf s fs g lvAll lv os es acc acc1
  | _, _, 0, _, _, _, _, _, _, hp => by simp [planKids] at hp
  | [], os, f + 1, acc, es, acc1, _, _, _, hp => by
    simp only [planKids, Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    exact ⟨by simp [vcostL], rfl, by simp, by simp, fun _ => rfl, by simp, by simp, by simp, rfl⟩
  | (c, y) :: rest, [], f + 1, acc, es, acc1, _, _, _, hp => by simp [planKids] at hp
  | (c, y) :: rest, o :: os, f + 1, acc, es, acc1, hsub, hos, hf, hp => by
    have hos' : ∀ o' ∈ os, P o' := fun o' ho' => hos o' (List.mem_cons_of_mem _ ho')
    have hmem : (c, y) ∈ lvAll := hsub List.mem_cons_self
    have hsub' : rest ⊆ lvAll := fun q hq => hsub (List.mem_cons_of_mem _ hq)
    have hl := hlook c y hmem
    simp only [planKids, Nat.add_sub_cancel] at hp
    split at hp
    · -- untouched
      rename_i hoe
      cases hk : planKids cf i s f g (h + 1) rest os acc with
      | none => rw [hk] at hp; cases hp
      | some q =>
        obtain ⟨es', acc2⟩ := q
        rw [hk] at hp
        simp only [Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp
        have ih := kids_puts P hchild hfill hlook rest os f acc es' acc2 hsub' hos' (by omega) hk
        have hent : ents c (VN.old y) = [(c, some y)] := rfl
        have hadd0 : ([(c, some y)] : List (Nat × Option NodeId)).filter (isAdded lvAll) = [] := by
          simp [List.filter, isAdded_some hl]
        have hz : (List.zip ((c, y) :: rest) (o :: os)).filter (fun e => !e.2.isEmpty) =
            (rest.zip os).filter (fun e => !e.2.isEmpty) := by
          simp [List.zip_cons_cons, hoe]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [hz]; exact ih.nd, ?_⟩
        · rw [hz]; simp only [vcostL, vcost]; have := ih.kw; omega
        · simp [ih.cvs]
        · rw [hz]; simp only [List.flatMap_cons, hent, List.filter_append, hadd0, List.nil_append]
          exact ih.added
        · simp only [List.flatMap_cons, hent, List.filter_append, hadd0, List.nil_append,
            List.length_append, List.length_cons, List.length_nil]
          have := ih.len; omega
        · intro h0
          simp only [List.flatMap_cons, hent, List.filter_append, hadd0, List.nil_append] at h0 ⊢
          rw [ih.same h0]; rfl
        · intro q hq
          rcases List.mem_cons.mp hq with rfl | hq
          · simp [hent]
          · simp only [List.flatMap_cons, List.any_append, Bool.or_eq_true]
            exact Or.inr (ih.keep q hq)
        · intro e he
          rcases List.mem_cons.mp he with rfl | he
          · exact ⟨rfl, fun h => by simp [VN.changed] at h⟩
          · exact ih.small e he
        · simp [hent]
    · -- planned
      rename_i hoe
      have hone : o ≠ [] := by simpa using hoe
      cases hpl : plan cf i s f y g h o acc with
      | none => rw [hpl] at hp; cases hp
      | some q0 =>
        obtain ⟨w, acc2⟩ := q0
        rw [hpl] at hp
        simp only at hp
        cases hk : planKids cf i s f g (h + 1) rest os acc2 with
        | none => rw [hk] at hp; cases hp
        | some q =>
          obtain ⟨es', acc3⟩ := q
          rw [hk] at hp
          simp only [Option.some.injEq, Prod.mk.injEq] at hp
          obtain ⟨rfl, rfl⟩ := hp
          have hc := hchild f (by omega) c y o acc w acc2 hmem hone (hos o List.mem_cons_self) hpl
          have ih := kids_puts P hchild hfill hlook rest os f acc2 es' acc3 hsub' hos' (by omega) hk
          obtain ⟨e1, e2, e3, e4⟩ := child_ents hl hc
          have hz : (List.zip ((c, y) :: rest) (o :: os)).filter (fun e => !e.2.isEmpty) =
              ((c, y), o) :: (rest.zip os).filter (fun e => !e.2.isEmpty) := by
            simp [List.zip_cons_cons, hoe]
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hz]; simp only [vcostL, List.map_cons, List.sum_cons]; have := ih.kw; have := hc.kw; omega
          · simp [ih.cvs]
          · rw [hz]; simp only [List.flatMap_cons, List.filter_append, List.length_append, List.map_cons,
              List.sum_cons]
            have := ih.added; omega
          · simp only [List.flatMap_cons, List.filter_append, List.length_append, List.length_cons]
            have := ih.len; omega
          · intro h0
            simp only [List.flatMap_cons, List.filter_append, List.length_append] at h0 ⊢
            rw [e3 (by omega), ih.same (by omega)]; rfl
          · intro q hq
            rcases List.mem_cons.mp hq with rfl | hq
            · simp only [List.flatMap_cons, List.any_append, Bool.or_eq_true]
              left
              cases he : ents c w with
              | nil => exact absurd he (ents_ne _ _)
              | cons a r => rw [he] at e4; simp at e4; simp [e4]
            · simp only [List.flatMap_cons, List.any_append, Bool.or_eq_true]
              exact Or.inr (ih.keep q hq)
          · intro e he
            rcases List.mem_cons.mp he with rfl | he
            · obtain ⟨n, es2, Fl, dec, hgk, rfl, _, hlen, hFne⟩ := hc.shape
              refine ⟨by simp [VN.isEmpty, hFne], fun _ hm => ?_⟩
              have := hfill c y hmem n hgk hm
              simp only [VN.size]; omega
            · exact ih.small e he
          · rw [hz]; simp only [List.map_cons, List.sum_cons, hc.nd, ih.nd]
          · simp only [List.flatMap_cons, List.head?_cons]
            cases he : ents c w with
            | nil => exact absurd he (ents_ne _ _)
            | cons a r => rw [he] at e4; simp at e4; simp [e4]

/-- **No join among children that are neither empty nor small.** -/
theorem rebalance_id {f g h : Nat} {es es2 : List (Nat × VN)}
    (hs : ∀ e ∈ es, e.2.isEmpty = false ∧ (e.2.changed = true → 2 ≤ cf.m → cf.m ≤ e.2.size))
    (hr : rebalance cf i s (f + 1) g h es = some es2) : es2 = es := by
  have hf : es.filter (fun e => !e.2.isEmpty) = es := by
    rw [List.filter_eq_self]; intro e he; simp [(hs e he).1]
  simp only [rebalance, hf] at hr
  split at hr
  · simp only [Option.some.injEq] at hr; exact hr.symm
  · rename_i hm
    have hm2 : 2 ≤ cf.m := by simp [Cfg.merges] at hm; omega
    have hfs : findSmall cf es = none := by
      unfold findSmall
      rw [Option.map_eq_none_iff, List.find?_eq_none]
      intro p hp
      have he : p.1 ∈ es := List.mem_of_getElem? (mem_zipIdx_get hp).2
      have := (hs p.1 he).2
      cases hc : p.1.2.changed
      · simp
      · have := this hc hm2; simp; omega
    unfold joinLoop at hr
    split at hr
    · simp only [Option.some.injEq] at hr; exact hr.symm
    · rw [hfs] at hr; simp only [Option.some.injEq] at hr; exact hr.symm

end Contract.PE
