/-
bergdb 030-21, part 3: the size of a node that PE plans. A planned node's
final list F (`VN.size`) is no longer than the nodes reached from the node
planned plus the operations (`plan_size_le`); a new segment tree's planned
leaf no longer than the operations (`new_size_le`).

The steps:

* A. The abstract plan (`Plan`, 026-24): the planned node holds no more
  entries than the node before plus the operations (`Plan.length_le`): each
  operation adds at most one entry, and the routing gives each operation to
  one child.
* B. A planned virtual node's final list is no longer than what it holds
  read before any cut (`VOk.size_le`): a leaf's list is its entries; an inner
  node's entries are its children's parts, a child of k parts holding at
  least k entries (`DecOk`), and a child holding one at least.
* C. The node before holds no more entries than the nodes reached from it
  (`content_view_le_R`); the compare values touched are no more than the
  operations (`touched_length_le`).
-/
import Contract.Proof.PeSeg

namespace Contract.PE

open PeProof PeProof.Abs

variable {cf : Cfg} {i : Time} {s : Tree}

/-! ## Lists -/

theorem flatMap_length_mono {α β γ : Type} {f : α → List β} {g : α → List γ} :
    ∀ (l : List α), (∀ a ∈ l, (f a).length ≤ (g a).length) →
      (l.flatMap f).length ≤ (l.flatMap g).length
  | [], _ => by simp
  | a :: l, h => by
    simp only [List.flatMap_cons, List.length_append]
    have h1 := h a List.mem_cons_self
    have h2 := flatMap_length_mono l (fun b hb => h b (List.mem_cons_of_mem _ hb))
    omega

theorem flatMap_length_le_one {α β : Type} {f : α → List β} :
    ∀ (l : List α), (∀ a ∈ l, (f a).length ≤ 1) → (l.flatMap f).length ≤ l.length
  | [], _ => by simp
  | a :: l, h => by
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have h1 := h a List.mem_cons_self
    have h2 := flatMap_length_le_one l (fun b hb => h b (List.mem_cons_of_mem _ hb))
    omega

theorem length_le_flatMap {α β : Type} {g : α → List β} :
    ∀ (l : List α), (∀ a ∈ l, 1 ≤ (g a).length) → l.length ≤ (l.flatMap g).length
  | [], _ => by simp
  | a :: l, h => by
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have h1 := h a List.mem_cons_self
    have h2 := length_le_flatMap l (fun b hb => h b (List.mem_cons_of_mem _ hb))
    omega

theorem eraseDups_length_aux : ∀ (n : Nat) (l : List Nat), l.length ≤ n →
    l.eraseDups.length ≤ l.length
  | 0, l, h => by
    rw [List.eq_nil_of_length_eq_zero (by omega : l.length = 0), List.eraseDups_nil]
  | _ + 1, [], _ => by rw [List.eraseDups_nil]
  | n + 1, a :: as, h => by
    rw [List.eraseDups_cons, List.length_cons, List.length_cons]
    have h1 := List.length_filter_le (fun b => !b == a) as
    simp only [List.length_cons] at h
    have h2 := eraseDups_length_aux n (as.filter (fun b => !b == a)) (by omega)
    omega

/-- The compare values touched are no more than the operations. -/
theorem touched_length_le (g : Nat) (ops : List Contract.Op) : (touched g ops).length ≤ ops.length := by
  unfold touched
  have := eraseDups_length_aux _ (ops.map (segAt g)) le_rfl
  rw [List.length_map] at this
  exact this

/-! ## A. The abstract plan -/

theorem mput_length_le (c v : Nat) : ∀ m : List (Nat × Nat), (mput c v m).length ≤ m.length + 1
  | [] => by simp [mput]
  | (c', v') :: r => by
    unfold mput
    split
    · simp
    · split
      · simp
      · simp only [List.length_cons]
        have := mput_length_le c v r
        omega

theorem applyOp_length_le (m : List (Nat × Nat)) (o : Abs.Op) :
    (applyOp m o).length ≤ m.length + 1 := by
  cases o with
  | put c v => exact mput_length_le c v m
  | del c =>
    simp only [applyOp]
    have := List.length_filter_le (fun e => e.1 != c) m
    omega

/-- Each operation adds at most one entry. -/
theorem applyOps_length_le : ∀ (ops : List Abs.Op) (m : List (Nat × Nat)),
    (Abs.applyOps ops m).length ≤ m.length + ops.length
  | [], m => by simp [Abs.applyOps]
  | o :: ops, m => by
    have h1 := applyOps_length_le ops (applyOp m o)
    have h2 := applyOp_length_le m o
    show (Abs.applyOps ops (applyOp m o)).length ≤ m.length + (ops.length + 1)
    omega

theorem filter_split_length (c' : Nat) : ∀ ops : List Abs.Op,
    (ops.filter (fun o => decide (o.cv < c'))).length +
      (ops.filter (fun o => decide (c' ≤ o.cv))).length = ops.length
  | [] => rfl
  | o :: ops => by
    have := filter_split_length c' ops
    by_cases h : o.cv < c'
    · have h' : ¬ c' ≤ o.cv := by omega
      simp only [List.filter_cons, h, h', decide_true, decide_false, ite_true,
        Bool.false_eq_true, ite_false, List.length_cons]
      omega
    · have h' : c' ≤ o.cv := by omega
      simp only [List.filter_cons, h, h', decide_true, decide_false, ite_true,
        Bool.false_eq_true, ite_false, List.length_cons]
      omega

/-- The routing gives each operation to one child at most. -/
theorem route_sum_le {β : Type} : ∀ (ks : List (Nat × β)) (ops : List Abs.Op),
    ((PeProof.Abs.route ks ops).map List.length).sum ≤ ops.length
  | [], _ => by simp [PeProof.Abs.route]
  | [_], ops => by simp [PeProof.Abs.route]
  | _ :: (c', y) :: r, ops => by
    simp only [PeProof.Abs.route, List.map_cons, List.sum_cons]
    have h1 := route_sum_le ((c', y) :: r) (ops.filter (fun o => decide (c' ≤ o.cv)))
    have h2 := filter_split_length c' ops
    omega

theorem routed_length {h : Nat}
    (IH : ∀ (x : Node h) (o : List Abs.Op) (x' : Node h), Plan h x o x' →
      (content h x').length ≤ (content h x).length + o.length) :
    ∀ {ks : List (Nat × Node h)} {os : List (List Abs.Op)} {ks' : List (Nat × Node h)},
      Routed (Plan h) ks os ks' →
      (kidsContent h ks').length ≤ (kidsContent h ks).length + (os.map List.length).sum := by
  intro ks os ks' hr
  induction hr with
  | nil => simp [kidsContent]
  | keep c x ks os ks' _ ih =>
    simp only [kidsContent_cons, List.length_append, List.map_cons, List.sum_cons,
      List.length_nil]
    omega
  | plan c x o x' ks os ks' hp _ ih =>
    have := IH x o x' hp
    simp only [kidsContent_cons, List.length_append, List.map_cons, List.sum_cons]
    omega

/-- **The abstract plan adds at most one entry an operation**: the planned
node holds no more entries than the node before plus the operations. -/
theorem Plan.length_le : ∀ (h : Nat) (es : Node h) (ops : List Abs.Op) (es' : Node h),
    Plan h es ops es' → (content h es').length ≤ (content h es).length + ops.length
  | 0, es, ops, es', hp => by
    simp only [Plan] at hp
    subst hp
    exact applyOps_length_le ops es
  | h + 1, es, ops, es', hp => by
    obtain ⟨ks', ks'', hr, hs, _, he⟩ := hp
    have e1 : content (h + 1) es' = kidsContent h ks'' := by
      show kidsContent h (kids es') = _
      rw [he]
      exact renameHead_flatMap 0 (fun x => content h x) ks''
    have e2 : content (h + 1) es = kidsContent h (kids es) := rfl
    rw [e1, hs.kidsContent, e2]
    have h1 := routed_length (fun x o x' hp => Plan.length_le h x o x' hp) hr
    have h2 := route_sum_le (kids es) ops
    omega

/-! ## B. A planned virtual node's final list -/

/-- The entries a parent gets for a child: one, or k for a cut into k ≥ 2
parts of a final list of at least k entries. -/
theorem ents_node_length_le (c : Nat) (base : Option NodeId) (g h : Nat) (join : Bool)
    (es : List (Nat × VN)) (F : List (Nat × Option NodeId)) (dec : Dec) (hd : DecOk dec F) :
    (ents c (.node base g h join es F dec)).length ≤ max 1 F.length := by
  cases dec with
  | parts k =>
    simp only [ents]
    split
    · rename_i hk
      rw [partEnts_length c F (by omega)]
      have := hd k rfl hk
      omega
    · simp
  | same => cases base <;> simp [ents]
  | append => cases base <;> simp [ents]

/-- An untouched node of the program holds an entry. -/
theorem content_old_ne {g h : Nat} {y : NodeId} (hw : VOk cf s g h (.old y)) :
    content h (absV s h (.old y)) ≠ [] := by
  cases hw with
  | old hsh hg hv =>
    obtain ⟨lo, hi, hg⟩ := hg
    rw [absV_old]
    rcases (view_wfe h hg hsh).1 with h0 | hwf
    · exact absurd h0 hv
    · exact content_ne_nil h lo hi _ hwf

/-- A child's entries in its parent are no more than what it holds. -/
theorem ents_le_content {g h : Nat} (c : Nat) {w : VN} (hw : VOk cf s g h w)
    (hne : w.isEmpty = false) (ih : w.size ≤ (content h (absV s h w)).length) :
    (ents c w).length ≤ (content h (absV s h w)).length := by
  cases w with
  | old y =>
    have := List.length_pos_iff.mpr (content_old_ne hw)
    simp only [ents, List.length_cons, List.length_nil]
    omega
  | node base g' h' join es F dec =>
    have hd : DecOk dec F := by cases hw <;> assumption
    have h1 := ents_node_length_le c base g' h' join es F dec hd
    simp only [VN.isEmpty, List.isEmpty_eq_false_iff] at hne
    have h2 := List.length_pos_iff.mpr hne
    simp only [VN.size] at ih
    omega

/-- **A planned node's final list is no longer than what it holds**, read
before any cut. -/
theorem VOk.size_le {g h : Nat} {v : VN} (hv : VOk cf s g h v) :
    v.size ≤ (content h (absV s h v)).length := by
  induction hv with
  | old _ _ _ => simp [VN.size]
  | @leaf base join es F dec hk hF _ =>
    show F.length ≤ (es.map (fun e => (e.1, e.2.oid))).length
    rw [hF, List.length_map]
    apply flatMap_length_le_one
    intro e he
    obtain ⟨y, hy⟩ := hk e he
    rw [hy]
    simp [ents]
  | @inner h base join es F dec hk hne _ hF _ ih =>
    show F.length ≤ (kidsContent h (es.map (fun e => (e.1, absV s h e.2)))).length
    rw [hF, renameHead_length]
    simp only [kidsContent, List.flatMap_map]
    apply flatMap_length_mono
    intro e he
    exact ents_le_content e.1 (hk e he) (hne e he) (ih e he)

/-! ## C. The node before -/

theorem R_length_pos (s : Tree) (y : NodeId) : 1 ≤ (R s y).length := by
  unfold R
  generalize s.fuel y = f
  cases f <;> simp [reachAt]

/-- **The node before holds no more entries than the nodes reached from
it.** -/
theorem content_view_le_R : ∀ (h : Nat) {g : Nat} {y : NodeId} {lo : Nat} {hi : Option Nat},
    Good s y lo hi → Shaped cf s g h y → (content h (view h s y)).length ≤ (R s y).length
  | 0, g, y, lo, hi, hg, hsh => by
    obtain ⟨n, hobj, _, _, _, _⟩ := shaped_obj hsh
    have e1 : content 0 (view 0 s y) = live n.ks := view_zero hobj
    rw [e1, R_good hg hobj, List.length_cons]
    have := length_le_flatMap (g := fun cy => R s cy.2) (live n.ks)
      (fun a _ => R_length_pos s a.2)
    omega
  | h + 1, g, y, lo, hi, hg, hsh => by
    obtain ⟨n, hobj, _, hleaf, _, _⟩ := shaped_obj hsh
    have hleaf' : n.leaf = false := by simpa using hleaf
    have hkids : ∀ c z, (c, z) ∈ live n.ks → Shaped cf s g h z := by
      cases hsh with
      | inner hobj' _ _ _ _ _ hk =>
        rw [hobj] at hobj'
        obtain rfl : n = _ := by injection hobj' with h1; injection h1
        exact hk
    rw [content_view_succ hobj, R_good hg hobj, List.length_cons]
    have := flatMap_length_mono (live n.ks) (fun cy hcy => by
      obtain ⟨pre, post, he⟩ := List.append_of_mem hcy
      have hgc : Good s cy.2 (max lo cy.1) (nextHi post hi) := by
        cases hg with
        | mk _ _ _ n' hobj' _ _ _ _ _ _ hkid =>
          rw [hobj] at hobj'
          obtain rfl : n = n' := by injection hobj' with h1; injection h1
          exact hkid hleaf' pre cy.1 cy.2 post he
      exact content_view_le_R h hgc (hkids cy.1 cy.2 hcy))
    omega

/-! ## The planned node's size -/

/-- A planned node's final list is no longer than the nodes reached from the
node planned plus the operations. -/
theorem plan_size_le (hcf : cf.Ok) {f : Nat} {x : NodeId} {g h : Nat} {ops : List Contract.Op}
    {acc : Acc} {v : VN} {acc' : Acc} {lo : Nat} {hi : Option Nat}
    (hp : plan cf i s f x g h ops acc = some (v, acc')) (hsh : Shaped cf s g h x)
    (hg : Good s x lo hi) : v.size ≤ (R s x).length + ops.length := by
  obtain ⟨sops, hpl, hcv, hv⟩ := plan_inst hcf hp hsh hg
  have h1 := hv.size_le
  have h2 := Plan.length_le h _ _ _ hpl
  have h3 := content_view_le_R h hg hsh
  have h4 : sops.length = (touched g ops).length := by rw [← hcv, List.length_map]
  have h5 := touched_length_le g ops
  omega

/-- A new segment tree's planned leaf: no longer than the operations. -/
theorem new_size_le {f g : Nat} {ops : List Contract.Op} {acc : Acc}
    {es : List (Nat × NodeId)} {acc' : Acc} {v : VN}
    (ha : applyGroups cf i s f g [] ((ops.map (segAt g)).eraseDups) ops acc = some (es, acc'))
    (hm : mkNode cf i s none g 0 false (es.map (fun e => (e.1, VN.old e.2))) = some v) :
    v.size ≤ ops.length := by
  have hsize : v.size = es.length := by
    unfold mkNode at hm
    simp only [beq_self_eq_true, ite_true] at hm
    split at hm
    · cases hm
    · simp only [Option.some.injEq] at hm
      subst hm
      show (List.flatMap (fun e => ents e.1 e.2) (es.map (fun e => (e.1, VN.old e.2)))).length = _
      rw [List.flatMap_map]
      simp [ents]
  obtain ⟨hs1, hs2⟩ := applyGroups_spec f g _ _ ops acc es acc' ha List.Pairwise.nil
  have he : Abs.applyOps (finalOps (touched g ops) es) [] = es :=
    applyOps_finalOps _ _ _ List.Pairwise.nil hs1 hs2
  have h1 := applyOps_length_le (finalOps (touched g ops) es) []
  rw [he] at h1
  have h2 : (finalOps (touched g ops) es).length = (touched g ops).length := by
    unfold finalOps; rw [List.length_map]
  have h3 := touched_length_le g ops
  simp only [List.length_nil] at h1
  omega

end Contract.PE
