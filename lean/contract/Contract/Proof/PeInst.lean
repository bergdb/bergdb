/-
bergdb 030-21: PE's writer (Contract/PeWriter.lean) is an instance of
026-24's relations on the abstract tree (PeAbs.lean, PeAbsOrder.lean,
PeAbsRoot.lean; 026-24, section 3): what the program plans, rebalances,
settles at the root and cuts at emit are steps of `Plan`, `Sett` and
`Root`, so 026-24's `Plan.keys`, `Plan.wf`, `Root.keys` and `Root.wf`
hold for the program's runs.

* `VOk`: what every virtual node the program works with satisfies: an
  untouched node shaped as PE's trees, sound (`Good`) and nonempty; a
  planned leaf whose children are payload ids; a planned inner node whose
  children are `VOk` one height down and not empty, whose first entry is
  the empty key; the final list F each child's parts (`ents`); a cut into
  k ≥ 2 parts of at least k entries.
* `mat`: emit's materialization of a planned node's children (each child
  as written one level down, then cut into its parts) is a settle of its
  children (`Sett`), and they are nonempty.
* `settle_root`: `settleRoot` is an instance of `Root` (`settle_root_none`:
  a root settled into no tree held nothing).
* `plan_inst`: `plan` is an instance of `Plan`, by operations on exactly
  the compare values that the operations touch (`touched`): the leaf's
  operations applied (`applyGroups_spec`, `applyOps_finalOps`), the
  children routed (`planKids_spec`), `rebalance` a settle
  (`rebalance_spec`); `plan_new_inst` for a new segment tree, and
  `plan_settle`, plan then the root settled.

The premises are facts of the tree before (`Shaped`, `Good`), of the
parameters (`Cfg.Ok`), and of the program's run (its result `some`).
-/
import Contract.Proof.PeDefs

namespace Contract.PE

open PeProof PeProof.Abs

variable {cf : Cfg} {i : Time} {s : Tree}

/-! ## Settle: transitivity and context -/

theorem _root_.PeProof.Step.ctx {α : Type} {inner : Bool} {es es' : Ents α} (h : Step inner es es')
    (pre post : Ents α) : Step inner (pre ++ es ++ post) (pre ++ es' ++ post) := by
  cases h with
  | drop p q c => simpa using Step.drop (inner := inner) (pre ++ p) (q ++ post) c
  | join p q cL cR L R hL => simpa using Step.join (inner := inner) (pre ++ p) (q ++ post) cL cR L R hL
  | cut p q c Ps hne hPs => simpa using Step.cut (inner := inner) (pre ++ p) (q ++ post) c Ps hne hPs

theorem _root_.PeProof.Abs.Sett.ctx {h : Nat} {ks ks' : List (Nat × Node h)} (hs : Sett h ks ks') :
    ∀ (pre post : List (Nat × Node h)), Sett h (pre ++ ks ++ post) (pre ++ ks' ++ post) := by
  induction hs with
  | refl h ks => exact fun pre post => Sett.refl h _
  | step h ks ks' ks'' hst _ ih =>
    exact fun pre post => Sett.step h _ _ _ (hst.ctx pre post) (ih pre post)
  | down h p q c J J' ks'' hJ _ _ ih =>
    intro pre post
    have := Sett.down h (pre ++ p) (q ++ post) c J J' (pre ++ ks'' ++ post) hJ
      (by simpa using ih pre post)
    simpa using this

theorem _root_.PeProof.Abs.Sett.trans {h : Nat} {a b : List (Nat × Node h)} (hab : Sett h a b) :
    ∀ {c : List (Nat × Node h)}, Sett h b c → Sett h a c := by
  induction hab with
  | refl => exact id
  | step h ks ks' ks'' hst _ ih => exact fun hc => Sett.step h _ _ _ hst (ih hc)
  | down h p q c J J' ks'' hJ _ _ ih => exact fun hc => Sett.down h p q c J J' _ hJ (ih hc)

/-- Each entry settled on its own: the list settled. -/
theorem sett_flatMap {h : Nat} {X : Type} (A : X → Nat × Node h) (B : X → List (Nat × Node h)) :
    ∀ (L : List X), (∀ x ∈ L, Sett h [A x] (B x)) → Sett h (L.map A) (L.flatMap B)
  | [], _ => Sett.refl h _
  | x :: L, hL => by
    have h1 : Sett h ([] ++ [A x] ++ L.map A) ([] ++ B x ++ L.map A) :=
      (hL x List.mem_cons_self).ctx [] (L.map A)
    have h2 : Sett h (B x ++ L.map A ++ []) (B x ++ L.flatMap B ++ []) :=
      (sett_flatMap A B L (fun y hy => hL y (List.mem_cons_of_mem _ hy))).ctx (B x) []
    simp only [List.nil_append, List.append_nil, List.singleton_append] at h1 h2
    simpa using h1.trans h2

/-! ## The decision -/

/-- A decision of k ≥ 2 parts cuts a list of at least k entries. -/
def DecOk (dec : Dec) (F : List (Nat × Option NodeId)) : Prop :=
  ∀ k, dec = .parts k → 2 ≤ k → k ≤ F.length

theorem nParts_le (cap n : Nat) : nParts cap n ≤ max n 1 := by
  unfold nParts
  simp only
  split
  · omega
  · obtain ⟨c', hc'⟩ : ∃ c', max cap 1 = c' + 1 := ⟨max cap 1 - 1, by omega⟩
    rw [hc']
    have : (n + (c' + 1) - 1) / (c' + 1) ≤ n := by
      apply Nat.div_le_of_le_mul
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · omega
      · have : c' ≤ c' * n := Nat.le_mul_of_pos_right c' hn
        rw [Nat.add_mul, Nat.one_mul]
        omega
    omega

theorem cutParts_ok (hcf : cf.Ok) (n : Nat) : 2 ≤ cutParts cf n → cutParts cf n ≤ n := by
  unfold cutParts
  have := hcf.h1
  split
  · omega
  · have := nParts_le cf.cap n
    intro _
    omega

/-- Every decision of PE is one: a cut into k ≥ 2 parts has at least k
entries to cut. -/
theorem decideNode_ok (hcf : cf.Ok) (base : Option KNode) (join : Bool)
    (F : List (Nat × Option NodeId)) : DecOk (decideNode cf i base join F) F := by
  intro k hk h2
  unfold decideNode at hk
  have hp : ∀ n, Dec.parts n = Dec.parts k → n = k := fun n h => by injection h
  cases base with
  | none =>
    simp only at hk
    have := hp _ hk
    subst this
    cases join
    · exact cutParts_ok hcf _ h2
    · have := nParts_le cf.c F.length
      simp only [ite_true] at h2 ⊢
      omega
  | some n =>
    simp only at hk
    split at hk
    · cases hk
    · split at hk
      · split at hk
        · split at hk
          · have := hp _ hk; omega
          · have := hp _ hk; subst this; exact cutParts_ok hcf _ h2
        · cases hk
      · have := hp _ hk; subst this; exact cutParts_ok hcf _ h2

/-! ## The virtual nodes the program makes -/

/-- Entries of virtual nodes read as abstract children of height h, each
before its cut. -/
def absK (s : Tree) (h : Nat) (es : List (Nat × VN)) : List (Nat × Node h) :=
  es.map (fun e => (e.1, absV s h e.2))

/-- What every virtual node of segment g at height h that the program works
with satisfies: an untouched node of the tree before, or a planned one. -/
inductive VOk (cf : Cfg) (s : Tree) (g : Nat) : Nat → VN → Prop where
  /-- An untouched node: shaped as PE's trees at height h, sound for the
  contract with some range (`Good`), and with a live klong. -/
  | old {h : Nat} {y : NodeId} :
      Shaped cf s g h y → (∃ lo hi, Good s y lo hi) → view h s y ≠ [] → VOk cf s g h (.old y)
  /-- A planned segment leaf: its entries' children are payload ids (untouched
  values, or values and next segments' roots that the transaction made); its
  final list is its entries; a cut into k ≥ 2 parts has at least k entries. -/
  | leaf {base : Option NodeId} {join : Bool} {es : List (Nat × VN)}
      {F : List (Nat × Option NodeId)} {dec : Dec} :
      (∀ e ∈ es, ∃ y, e.2 = .old y) →
      F = es.flatMap (fun e => ents e.1 e.2) →
      DecOk dec F →
      VOk cf s g 0 (.node base g 0 join es F dec)
  /-- A planned inner node at height h + 1: each child one height down
  (`VOk` at h); no child empty (`VN.isEmpty`); its first entry the empty
  key; its final list its children's parts (`ents`), the first with the
  empty key; a cut into k ≥ 2 parts has at least k entries. -/
  | inner {h : Nat} {base : Option NodeId} {join : Bool} {es : List (Nat × VN)}
      {F : List (Nat × Option NodeId)} {dec : Dec} :
      (∀ e ∈ es, VOk cf s g h e.2) →
      (∀ e ∈ es, e.2.isEmpty = false) →
      renameHead 0 es = es →
      F = renameHead 0 (es.flatMap (fun e => ents e.1 e.2)) →
      DecOk dec F →
      VOk cf s g (h + 1) (.node base g (h + 1) join es F dec)

/-! ## Lengths and heads -/

theorem fin_old (h : Nat) (y : NodeId) : fin s h (.old y) = absV s h (.old y) := by
  cases h <;> rfl

theorem renameHead_length {α : Type} (c : Nat) (l : List (Nat × α)) :
    (renameHead c l).length = l.length := by
  cases l with
  | nil => rfl
  | cons a r => rfl

theorem renameHead_map {α β : Type} (c : Nat) (f : α → β) (l : List (Nat × α)) :
    (renameHead c l).map (fun e => (e.1, f e.2)) = renameHead c (l.map (fun e => (e.1, f e.2))) := by
  cases l with
  | nil => rfl
  | cons a r => rfl

theorem renameHead_ne {α : Type} (c : Nat) {l : List (Nat × α)} (hl : l ≠ []) :
    renameHead c l ≠ [] := by
  cases l with
  | nil => exact absurd rfl hl
  | cons a r => simp [renameHead]

theorem renameHead_mem {α : Type} {c : Nat} {l : List (Nat × α)} {e : Nat × α}
    (he : e ∈ renameHead c l) : ∃ e' ∈ l, e'.2 = e.2 := by
  cases l with
  | nil => simp [renameHead] at he
  | cons a r =>
    simp only [renameHead, List.mem_cons] at he
    rcases he with rfl | he
    · exact ⟨a, List.mem_cons_self, rfl⟩
    · exact ⟨e, List.mem_cons_of_mem _ he, rfl⟩

theorem cutEnts_length {α : Type} (inner : Bool) (c : Nat) (Ps : List (List (Nat × α))) :
    (cutEnts inner c Ps).length = Ps.length := by
  cases Ps with
  | nil => rfl
  | cons P Ps => simp [cutEnts]

theorem cutEnts_ne {α : Type} (inner : Bool) (c : Nat) (Ps : List (List (Nat × α)))
    (hne : ∀ P ∈ Ps, P ≠ []) : ∀ e ∈ cutEnts inner c Ps, e.2 ≠ [] := by
  cases Ps with
  | nil => simp [cutEnts]
  | cons P Ps =>
    intro e he
    simp only [cutEnts, List.mem_cons, List.mem_map] at he
    rcases he with rfl | ⟨Q, hQ, rfl⟩
    · exact hne P List.mem_cons_self
    · have := hne Q (List.mem_cons_of_mem _ hQ)
      cases inner
      · exact this
      · exact renameHead_ne 0 this

theorem partEnts_length (cv : Nat) (F : List (Nat × Option NodeId)) {k : Nat} (hk : 1 ≤ k)
    (join : Bool) : (partEnts cv F k join).length = k := by
  unfold partEnts
  have hl : (cutList F (partSizes F.length k join)).length = k := by
    rw [cutList_length, partSizes_length]
  split
  · rename_i h0; rw [h0] at hl; simp at hl; omega
  · rename_i P rest h0; rw [h0] at hl; simpa using hl

theorem finEnts_length {h : Nat} (c : Nat) (w : VN) (fv : Node h) :
    (finEnts c w fv).length = (ents c w).length := by
  cases w with
  | old y => rfl
  | node base g' h' join es F dec =>
    cases dec with
    | parts k =>
      simp only [finEnts, ents]
      split
      · rename_i hk
        rw [cutEnts_length, cutList_length, partSizes_length, partEnts_length c F (by omega)]
      · rfl
    | same => cases base <;> rfl
    | append => cases base <;> rfl

theorem ents_ne (c : Nat) (w : VN) : ents c w ≠ [] := by
  cases w with
  | old y => simp [ents]
  | node base g' h' join es F dec =>
    cases dec with
    | parts k =>
      simp only [ents]
      split
      · unfold partEnts; split <;> simp
      · simp
    | same => cases base <;> simp [ents]
    | append => cases base <;> simp [ents]

theorem flatMap_ents_nil {es : List (Nat × VN)} (h : es.flatMap (fun e => ents e.1 e.2) = []) :
    es = [] := by
  cases es with
  | nil => rfl
  | cons e r =>
    simp only [List.flatMap_cons, List.append_eq_nil_iff] at h
    exact absurd h.1 (ents_ne _ _)

/-- A planned node is written as many entries as its final list has. -/
theorem fin_length {g h : Nat} {base : Option NodeId} {g' h' : Nat} {join : Bool}
    {es : List (Nat × VN)} {F : List (Nat × Option NodeId)} {dec : Dec}
    (hv : VOk cf s g h (.node base g' h' join es F dec)) :
    (fin s h (.node base g' h' join es F dec)).length = F.length := by
  cases hv with
  | leaf hold hF _ =>
    subst hF
    show (es.map (fun e => (e.1, e.2.oid))).length = _
    rw [List.length_map, List.length_flatMap]
    have : ∀ e ∈ es, (ents e.1 e.2).length = 1 := by
      intro e he
      obtain ⟨y, hy⟩ := hold e he
      rw [hy]; rfl
    rw [List.map_congr_left (g := fun _ => 1) this]
    simp
  | inner _ _ _ hF _ =>
    subst hF
    show (renameHead 0 (es.flatMap (fun e => finEnts e.1 e.2 (fin s _ e.2)))).length = _
    rw [renameHead_length, renameHead_length, List.length_flatMap, List.length_flatMap]
    congr 1
    apply List.map_congr_left
    intro e _
    exact finEnts_length _ _ _

/-- A virtual node that is not empty reads as a nonempty abstract node. -/
theorem absV_ne {g h : Nat} {w : VN} (hw : VOk cf s g h w) (hne : w.isEmpty = false) :
    absV s h w ≠ [] := by
  cases hw with
  | old _ _ hv => cases h <;> exact hv
  | leaf _ hF _ =>
    simp only [VN.isEmpty, List.isEmpty_eq_false_iff] at hne
    intro h0
    apply hne
    rw [hF]
    have : (_ : List (Nat × VN)) = [] := List.map_eq_nil_iff.mp h0
    rw [this]; rfl
  | inner _ _ _ hF _ =>
    simp only [VN.isEmpty, List.isEmpty_eq_false_iff] at hne
    intro h0
    apply hne
    rw [hF]
    have : (_ : List (Nat × VN)) = [] := List.map_eq_nil_iff.mp h0
    rw [this]; rfl

/-- ... and is written as a nonempty node. -/
theorem fin_ne {g h : Nat} {w : VN} (hw : VOk cf s g h w) (hne : w.isEmpty = false) :
    fin s h w ≠ [] := by
  cases w with
  | old y => rw [fin_old]; exact absV_ne hw hne
  | node base g' h' join es F dec =>
    intro h0
    have := fin_length hw
    rw [h0] at this
    simp only [VN.isEmpty, List.isEmpty_eq_false_iff] at hne
    exact hne (List.eq_nil_of_length_eq_zero this.symm)

theorem view_ne_of {h : Nat} {z : NodeId} {m : KNode} (hm : s.obj z = some (.key m))
    (hl : live m.ks ≠ []) : view h s z ≠ [] := by
  cases h with
  | zero => simp only [view, hm]; exact hl
  | succ h =>
    simp only [view, hm]
    intro h0
    exact hl (List.map_eq_nil_iff.mp h0)

theorem view_succ {h : Nat} {y : NodeId} {n : KNode} (hobj : s.obj y = some (.key n)) :
    kids (view (h + 1) s y) = (live n.ks).map (fun cy => (cy.1, view h s cy.2)) := by
  simp only [view, hobj]; rfl

theorem view_zero {y : NodeId} {n : KNode} (hobj : s.obj y = some (.key n)) :
    view 0 s y = live n.ks := by
  simp only [view, hobj]; rfl

/-- The children of an untouched inner node are nonempty. -/
theorem view_kids_ne {g h : Nat} {y : NodeId} (hw : VOk cf s g (h + 1) (.old y)) :
    ∀ e ∈ kids (view (h + 1) s y), e.2 ≠ [] := by
  cases hw with
  | old hsh hg _ =>
    obtain ⟨lo, hi, hg⟩ := hg
    cases hsh with
    | inner hobj hleaf _ _ _ _ _ =>
      cases hg with
      | mk _ _ _ n' hobj' _ _ _ _ hkey _ _ =>
        rw [hobj] at hobj'
        obtain rfl : _ = n' := by injection hobj' with h1; injection h1
        rw [view_succ hobj]
        intro e he
        obtain ⟨⟨c, z⟩, hm, rfl⟩ := List.mem_map.mp he
        obtain ⟨m, hm1, _, hm3⟩ := hkey c z hm (fun hl => by rw [hleaf] at hl; cases hl)
        exact view_ne_of hm1 hm3

theorem finEnts_cut {h : Nat} (c : Nat) {base : Option NodeId} {g' h' : Nat} {join : Bool}
    {es : List (Nat × VN)} {F : List (Nat × Option NodeId)} {k : Nat} (hk : 2 ≤ k) (fv : Node h) :
    finEnts c (.node base g' h' join es F (.parts k)) fv =
      cutEnts (h != 0) c (cutList fv (partSizes fv.length k join)) := by
  simp [finEnts, hk]

theorem finEnts_one {h : Nat} (c : Nat) (w : VN) (fv : Node h)
    (hw : ∀ base g' h' join es F k, w = .node base g' h' join es F (.parts k) → k < 2) :
    finEnts c w fv = [(c, fv)] := by
  cases w with
  | old y => rfl
  | node base g' h' join es F dec =>
    cases dec with
    | parts k =>
      have := hw base g' h' join es F k rfl
      simp [finEnts]; omega
    | same => rfl
    | append => rfl

/-- emit's cut of one child into its parts is a step of settle. -/
theorem cut_sett {g h : Nat} (c : Nat) {w : VN} (hw : VOk cf s g h w) :
    Sett h [(c, fin s h w)] (finEnts c w (fin s h w)) ∧
    (w.isEmpty = false → ∀ e ∈ finEnts c w (fin s h w), e.2 ≠ []) ∧
    (finEnts c w (fin s h w)).head?.map (·.1) = some c := by
  by_cases hcut : ∃ base g' h' join es F k, w = .node base g' h' join es F (.parts k) ∧ 2 ≤ k
  · obtain ⟨base, g', h', join, es, F, k, rfl, hk⟩ := hcut
    have hlen := fin_length hw
    have hdec : DecOk (.parts k) F := by cases hw <;> assumption
    generalize hfv : fin s h (.node base g' h' join es F (.parts k)) = fv at hlen ⊢
    have hkn : k ≤ fv.length := by rw [hlen]; exact hdec k rfl hk
    obtain ⟨h1, h2, _, h4⟩ := cut_spec fv (k := k) (by omega) hkn join
    rw [finEnts_cut c hk fv]
    refine ⟨?_, fun _ => cutEnts_ne _ _ _ h2, ?_⟩
    · have hPs : cutList fv (partSizes fv.length k join) ≠ [] := by
        intro h0; rw [h0] at h4; simp at h4; omega
      have hst := Step.cut (inner := h != 0) [] [] c _ h2 hPs
      rw [h1] at hst
      exact Sett.step h _ _ _ (by simpa using hst) (Sett.refl _ _)
    · cases hc : cutList fv (partSizes fv.length k join) with
      | nil => rw [hc] at h4; simp at h4; omega
      | cons P Ps => rfl
  · rw [finEnts_one c w _ (fun base g' h' join es F k hw' => by
      by_contra hk; exact hcut ⟨base, g', h', join, es, F, k, hw', by omega⟩)]
    refine ⟨Sett.refl _ _, fun hne e he => ?_, rfl⟩
    simp only [List.mem_singleton] at he
    subst he
    exact fin_ne hw hne

theorem renameHead_flatMap_head {β γ : Type} (es : List (Nat × β)) (B : Nat × β → List (Nat × γ))
    (hh : renameHead 0 es = es) (hB : ∀ e ∈ es, (B e).head?.map (·.1) = some e.1) :
    renameHead 0 (es.flatMap B) = es.flatMap B := by
  cases es with
  | nil => rfl
  | cons e r =>
    obtain ⟨c, y⟩ := e
    have hc : c = 0 := by
      simp only [renameHead, List.cons.injEq, Prod.mk.injEq] at hh; omega
    subst hc
    have := hB (0, y) List.mem_cons_self
    rw [List.flatMap_cons]
    cases hb : B (0, y) with
    | nil => rw [hb] at this; cases this
    | cons a t =>
      rw [hb] at this
      obtain ⟨a1, a2⟩ := a
      simp only [List.head?_cons, Option.map_some, Option.some.injEq] at this
      subst this
      rfl

/-- **Materialization**: a virtual node of height h + 1 as emit writes it is
its children before any cut, settled: each planned child materialized one
level down (`Sett.down`), then cut into its parts (`Step.cut`); and its
written children are nonempty. -/
theorem mat {g : Nat} : ∀ (h : Nat) (v : VN), VOk cf s g (h + 1) v →
    Sett h (kids (absV s (h + 1) v)) (kids (fin s (h + 1) v)) ∧
      ∀ e ∈ kids (fin s (h + 1) v), e.2 ≠ [] := by
  intro h
  induction h with
  | zero =>
    intro v hv
    cases hv with
    | old hsh hg hne =>
      exact ⟨Sett.refl _ _, view_kids_ne (VOk.old hsh hg hne)⟩
    | @inner _ base join es F dec hk hne hhead hF hdec =>
      have hB : ∀ e ∈ es, (finEnts e.1 e.2 (fin s 0 e.2)).head?.map (·.1) = some e.1 :=
        fun e he => (cut_sett e.1 (hk e he)).2.2
      show Sett 0 (absK s 0 es) (renameHead 0 (es.flatMap (fun e => finEnts e.1 e.2 (fin s 0 e.2)))) ∧
        ∀ e ∈ renameHead 0 (es.flatMap (fun e => finEnts e.1 e.2 (fin s 0 e.2))), e.2 ≠ []
      rw [renameHead_flatMap_head es _ hhead hB]
      refine ⟨sett_flatMap _ _ es (fun e he => (cut_sett e.1 (hk e he)).1), ?_⟩
      intro e he
      obtain ⟨e', he', hm⟩ := List.mem_flatMap.mp he
      exact (cut_sett e'.1 (hk e' he')).2.1 (hne e' he') e hm
  | succ h ih =>
    intro v hv
    cases hv with
    | old hsh hg hne =>
      exact ⟨Sett.refl _ _, view_kids_ne (VOk.old hsh hg hne)⟩
    | @inner _ base join es F dec hk hne hhead hF hdec =>
      have hB : ∀ e ∈ es, (finEnts e.1 e.2 (fin s (h + 1) e.2)).head?.map (·.1) = some e.1 :=
        fun e he => (cut_sett e.1 (hk e he)).2.2
      show Sett (h + 1) (absK s (h + 1) es)
          (renameHead 0 (es.flatMap (fun e => finEnts e.1 e.2 (fin s (h + 1) e.2)))) ∧
        ∀ e ∈ renameHead 0 (es.flatMap (fun e => finEnts e.1 e.2 (fin s (h + 1) e.2))), e.2 ≠ []
      rw [renameHead_flatMap_head es _ hhead hB]
      refine ⟨sett_flatMap _ _ es (fun e he => ?_), ?_⟩
      · refine Sett.trans ?_ (cut_sett e.1 (hk e he)).1
        cases hw : e.2 with
        | old y => rw [fin_old]; exact Sett.refl _ _
        | node base' g' h' join' es' F' dec' =>
          have hv' := hk e he
          rw [hw] at hv'
          exact Sett.down h [] [] e.1 _ _ _ (ih _ hv').1 (Sett.refl _ _)
      · intro e he
        obtain ⟨e', he', hm⟩ := List.mem_flatMap.mp he
        exact (cut_sett e'.1 (hk e' he')).2.1 (hne e' he') e hm

/-! ## A virtual node made -/

theorem mkNode_inner {base : Option NodeId} {g h : Nat} {join : Bool} {es0 : List (Nat × VN)}
    {v : VN} (hcf : cf.Ok) (hm : mkNode cf i s base g (h + 1) join es0 = some v)
    (hk : ∀ e ∈ es0, VOk cf s g h e.2) (hne : ∀ e ∈ es0, e.2.isEmpty = false) :
    (∃ F dec, v = .node base g (h + 1) join (renameHead 0 es0) F dec) ∧ VOk cf s g (h + 1) v := by
  have hk' : ∀ e ∈ renameHead 0 es0, VOk cf s g h e.2 := fun e he => by
    obtain ⟨e', he', h2⟩ := renameHead_mem he; rw [← h2]; exact hk e' he'
  have hne' : ∀ e ∈ renameHead 0 es0, e.2.isEmpty = false := fun e he => by
    obtain ⟨e', he', h2⟩ := renameHead_mem he; rw [← h2]; exact hne e' he'
  have hh : renameHead 0 (renameHead 0 es0) = renameHead 0 es0 := renameHead_renameHead 0 0 es0
  unfold mkNode at hm
  simp only [Nat.add_one_ne_zero, beq_iff_eq, ite_false] at hm
  cases base with
  | some b =>
    simp only at hm
    split at hm
    · simp only [Option.some.injEq] at hm
      subst hm
      exact ⟨⟨_, _, rfl⟩, VOk.inner hk' hne' hh rfl (decideNode_ok hcf _ _ _)⟩
    · cases hm
  | none =>
    simp only at hm
    split at hm
    · cases hm
    · simp only [Option.some.injEq] at hm
      subst hm
      exact ⟨⟨_, _, rfl⟩, VOk.inner hk' hne' hh rfl (decideNode_ok hcf _ _ _)⟩

theorem mkNode_leaf {base : Option NodeId} {g : Nat} {join : Bool} {es0 : List (Nat × VN)}
    {v : VN} (hcf : cf.Ok) (hm : mkNode cf i s base g 0 join es0 = some v)
    (hk : ∀ e ∈ es0, ∃ y, e.2 = .old y) :
    (∃ F dec, v = .node base g 0 join es0 F dec) ∧ VOk cf s g 0 v := by
  unfold mkNode at hm
  simp only [beq_self_eq_true, ite_true] at hm
  cases base with
  | some b =>
    simp only at hm
    split at hm
    · simp only [Option.some.injEq] at hm
      subst hm
      exact ⟨⟨_, _, rfl⟩, VOk.leaf hk rfl (decideNode_ok hcf _ _ _)⟩
    · cases hm
  | none =>
    simp only at hm
    split at hm
    · cases hm
    · simp only [Option.some.injEq] at hm
      subst hm
      exact ⟨⟨_, _, rfl⟩, VOk.leaf hk rfl (decideNode_ok hcf _ _ _)⟩

/-! ## The root settled alone -/

/-- A root to settle at height h: an untouched node shaped as PE's trees
(possibly empty: the space root of an empty tree), or a virtual node that
the program made. -/
def RootOk (cf : Cfg) (s : Tree) (g h : Nat) (v : VN) : Prop :=
  (∃ y, v = .old y ∧ Shaped cf s g h y) ∨ VOk cf s g h v

theorem VOk.ht {g h : Nat} {base : Option NodeId} {g' h' : Nat} {join : Bool}
    {es : List (Nat × VN)} {F : List (Nat × Option NodeId)} {dec : Dec}
    (hv : VOk cf s g h (.node base g' h' join es F dec)) : h' = h ∧ g' = g := by
  cases hv <;> exact ⟨rfl, rfl⟩

theorem es_nil_of_F {g h : Nat} {base : Option NodeId} {g' h' : Nat} {join : Bool}
    {es : List (Nat × VN)} {F : List (Nat × Option NodeId)} {dec : Dec}
    (hv : VOk cf s g h (.node base g' h' join es F dec)) (hF : F = []) : es = [] := by
  cases hv with
  | leaf _ hF' _ => rw [hF'] at hF; exact flatMap_ents_nil hF
  | inner _ _ _ hF' _ =>
    rw [hF'] at hF
    cases hl : List.flatMap (fun e => ents e.1 e.2) es with
    | nil => exact flatMap_ents_nil hl
    | cons a r => rw [hl] at hF; cases a; simp [renameHead] at hF

/-- A virtual node settled as it is: done (a leaf), or its children
materialized (`Root.down`), then done. -/
theorem root_here {g h : Nat} {v : VN} (hv : VOk cf s g h v) : Root h (absV s h v) h (fin s h v) := by
  cases h with
  | zero => exact Root.done 0 _
  | succ h => exact Root.down h _ _ (h + 1) _ (mat h v hv).1 (Root.done _ _)

/-- **The root settled alone is an instance of `Root`**: if `settleRoot`
gives v' for a root v of height h (an untouched node shaped as PE's trees,
or a virtual node the program made), then the root read before any cut
settles (`Root`) into v' as emit writes it, at some height h', and v' is
again such a root. -/
theorem settle_root (hcf : cf.Ok) : ∀ (f g : Nat) (space : Bool) (h : Nat) (v v' : VN),
    RootOk cf s g h v → settleRoot cf i s f g v space = some (some v') →
    ∃ h', Root h (absV s h v) h' (fin s h' v') ∧ RootOk cf s g h' v'
  | 0, _, _, _, _, _, _, hs => by simp [settleRoot] at hs
  | f + 1, g, space, h, v, v', hv, hs => by
    unfold settleRoot at hs
    cases v with
    | old y =>
      have hsh : Shaped cf s g h y := by
        rcases hv with ⟨y', hy, hsh⟩ | hv
        · cases hy; exact hsh
        · cases hv with
          | old hsh _ _ => exact hsh
      simp only at hs
      have hdone : ∃ h', Root h (absV s h (.old y)) h' (fin s h' (.old y)) ∧
          RootOk cf s g h' (.old y) := ⟨h, by rw [fin_old]; exact Root.done _ _, hv⟩
      cases hgk : getKey s y with
      | none => rw [hgk] at hs; cases hs
      | some n =>
        rw [hgk] at hs
        simp only at hs
        have hobj : s.obj y = some (.key n) := by
          unfold getKey at hgk
          split at hgk
          · rename_i n' h0; cases hgk; exact h0
          · cases hgk
        split at hs
        · rename_i c z hl
          split at hs
          · simp only [Option.some.injEq] at hs; subst hs; exact hdone
          · rename_i hleaf
            cases hsh with
            | leaf hobj' hleaf' _ _ _ =>
              rw [hobj] at hobj'
              obtain rfl : n = _ := by injection hobj' with h1; injection h1
              exact absurd hleaf' hleaf
            | @inner _ h'' _ n' hobj' _ _ _ _ _ hkids =>
              rw [hobj] at hobj'
              obtain rfl : n = n' := by injection hobj' with h1; injection h1
              have hz : Shaped cf s g h'' z := hkids c z (by rw [hl]; simp)
              obtain ⟨h', hR, hok⟩ := settle_root hcf f g space h'' (.old z) v' (Or.inl ⟨z, rfl, hz⟩) hs
              refine ⟨h', ?_, hok⟩
              have : absV s (h'' + 1) (.old y) = ofKids [(c, absV s h'' (.old z))] := by
                show view (h'' + 1) s y = _
                have := view_succ (h := h'') hobj
                rw [hl] at this
                rw [show view (h'' + 1) s y = kids (view (h'' + 1) s y) from rfl, this]
                cases h'' <;> rfl
              rw [this]
              exact Root.collapse h'' c _ h' _ hR
        · simp only [Option.some.injEq] at hs; subst hs; exact hdone
    | node base g' hv' join es F dec =>
      have hvok : VOk cf s g h (.node base g' hv' join es F dec) := by
        rcases hv with ⟨y', hy, _⟩ | hv
        · cases hy
        · exact hv
      obtain ⟨hh1, hh2⟩ := hvok.ht
      subst hv' g'
      simp only at hs
      split at hs
      · -- nothing left
        rename_i hF
        have hF' : F = [] := List.isEmpty_iff.mp hF
        have hes := es_nil_of_F hvok hF'
        subst hes
        split at hs
        · cases hs
        · split at hs
          · simp only [Option.some.injEq] at hs; subst hs
            exact ⟨h, root_here hvok, Or.inr hvok⟩
          · rename_i hh
            obtain ⟨h'', rfl⟩ : ∃ h'', h = h'' + 1 := ⟨h - 1, by simp at hh; omega⟩
            cases hm : mkNode cf i s none g 0 false [] with
            | none => rw [hm] at hs; cases hs
            | some w =>
              rw [hm] at hs
              simp only [Option.map_some, Option.some.injEq] at hs
              subst hs
              obtain ⟨⟨F2, dec2, rfl⟩, hw⟩ := mkNode_leaf hcf hm (by simp)
              exact ⟨0, Root.empty h'', Or.inr hw⟩
      · split at hs
        · -- one child: collapse
          rename_i hF hone
          simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hone
          obtain ⟨hh, _⟩ := hone
          obtain ⟨h'', rfl⟩ : ∃ h'', h = h'' + 1 := ⟨h - 1, by omega⟩
          split at hs
          · rename_i c ch
            cases hvok with
            | inner hk _ _ _ _ =>
              obtain ⟨h', hR, hok⟩ :=
                settle_root hcf f g space h'' ch v' (Or.inr (hk (c, ch) (by simp))) hs
              exact ⟨h', Root.collapse h'' c _ h' _ hR, hok⟩
          · cases hs
        · rename_i hF _
          have hdone : ∃ h', Root h (absV s h (.node base g h join es F dec)) h'
              (fin s h' (.node base g h join es F dec)) ∧
              RootOk cf s g h' (.node base g h join es F dec) :=
            ⟨h, root_here hvok, Or.inr hvok⟩
          split at hs
          · rename_i k
            split at hs
            · -- a new root above
              cases hm : mkNode cf i s none g (h + 1) false [(0, .node base g h join es F (.parts k))] with
              | none => rw [hm] at hs; cases hs
              | some r =>
                rw [hm] at hs
                simp only at hs
                have hne : (VN.node base g h join es F (.parts k)).isEmpty = false := by
                  simp only [VN.isEmpty]; simpa using hF
                obtain ⟨⟨F2, dec2, rfl⟩, hr⟩ := mkNode_inner hcf hm
                  (by intro e he; simp at he; subst he; exact hvok)
                  (by intro e he; simp at he; subst he; exact hne)
                obtain ⟨h', hR, hok⟩ := settle_root hcf f g space (h + 1) _ v' (Or.inr hr) hs
                refine ⟨h', Root.up h _ [(0, absV s h (.node base g h join es F (.parts k)))] h' _
                  (Sett.refl _ _) ?_ hR, hok⟩
                intro e he
                simp only [List.mem_singleton] at he
                subst he
                exact absV_ne hvok hne
            · simp only [Option.some.injEq] at hs; subst hs; exact hdone
          · simp only [Option.some.injEq] at hs; subst hs; exact hdone

/-! ## Rebalance is a settle -/

/-- Children of height h for a settle: each one the program can make, none
empty. -/
def KOk (cf : Cfg) (s : Tree) (g h : Nat) (es : List (Nat × VN)) : Prop :=
  ∀ e ∈ es, VOk cf s g h e.2 ∧ e.2.isEmpty = false

theorem absV_old (h : Nat) (y : NodeId) : absV s h (.old y) = view h s y := by
  cases h <;> rfl

theorem renameHead_self {α : Type} {c : Nat} {l : List (Nat × α)}
    (hl : l.head?.map (·.1) = some c) : renameHead c l = l := by
  cases l with
  | nil => cases hl
  | cons a r =>
    obtain ⟨a1, a2⟩ := a
    simp only [List.head?_cons, Option.map_some, Option.some.injEq] at hl
    subst hl; rfl

theorem head_of_renameHead {α : Type} {c : Nat} {l : List (Nat × α)} (hl : renameHead c l = l)
    (hne : l ≠ []) : l.head?.map (·.1) = some c := by
  cases l with
  | nil => exact absurd rfl hne
  | cons a r =>
    obtain ⟨a1, a2⟩ := a
    simp only [renameHead, List.cons.injEq, Prod.mk.injEq] at hl
    simp [hl.1.1]

theorem head_fst_eq {α : Type} (A B C : List (Nat × α)) (c : Nat) (x y : α) :
    (A ++ (c, x) :: B).head?.map (·.1) = (A ++ (c, y) :: C).head?.map (·.1) := by
  cases A <;> rfl

theorem split_at2 {α : Type} {l : List α} {il : Nat} {a b : α} (ha : l[il]? = some a)
    (hb : l[il + 1]? = some b) : l = l.take il ++ a :: b :: l.drop (il + 2) := by
  obtain ⟨h1, h1'⟩ := List.getElem?_eq_some_iff.mp ha
  obtain ⟨h2, h2'⟩ := List.getElem?_eq_some_iff.mp hb
  have e1 := List.drop_eq_getElem_cons h1
  have e2 := List.drop_eq_getElem_cons h2
  rw [h1'] at e1
  rw [h2'] at e2
  rw [e2] at e1
  conv_lhs => rw [← List.take_append_drop il l, e1]

theorem absK_append (h : Nat) (A B : List (Nat × VN)) :
    absK s h (A ++ B) = absK s h A ++ absK s h B := by
  simp [absK]

/-- The children of an untouched inner node, as the program reads them:
the first the empty key, each one it can work with. -/
theorem old_kids {g h : Nat} {y : NodeId} {n : KNode} (hobj : s.obj y = some (.key n))
    (hsh : Shaped cf s g (h + 1) y) (hg : ∃ lo hi, Good s y lo hi) :
    (live n.ks).head?.map (·.1) = some 0 ∧ ∀ c z, (c, z) ∈ live n.ks → VOk cf s g h (.old z) := by
  obtain ⟨lo, hi, hg⟩ := hg
  cases hsh with
  | inner hobj' hleaf _ _ _ hhead hkids =>
    rw [hobj] at hobj'
    obtain rfl : n = _ := by injection hobj' with h1; injection h1
    cases hg with
    | mk _ _ _ n' hobj'' _ _ _ _ hkey _ hkid =>
      rw [hobj] at hobj''
      obtain rfl : n = n' := by injection hobj'' with h1; injection h1
      refine ⟨hhead, fun c z hm => VOk.old (hkids c z hm) ?_ ?_⟩
      · obtain ⟨pre, post, he⟩ := List.append_of_mem hm
        exact ⟨_, _, hkid hleaf pre c z post he⟩
      · obtain ⟨m, hm1, _, hm3⟩ := hkey c z hm (fun hl => by rw [hleaf] at hl; cases hl)
        exact view_ne_of hm1 hm3

theorem getKey_obj {y : NodeId} {n : KNode} (h : getKey s y = some n) : s.obj y = some (.key n) := by
  unfold getKey at h
  split at h
  · rename_i h0; cases h; exact h0
  · cases h

/-- An inner child opened for a join: its entries. -/
theorem openEs_succ {g h : Nat} {w : VN} {esW : List (Nat × VN)} (hw : VOk cf s g (h + 1) w)
    (ho : openEs s w = some esW) :
    KOk cf s g h esW ∧ renameHead 0 esW = esW ∧ kids (absV s (h + 1) w) = absK s h esW := by
  cases hw with
  | @old _ y hsh hg hne =>
    simp only [openEs] at ho
    cases hgk : getKey s y with
    | none => rw [hgk] at ho; cases ho
    | some n =>
      rw [hgk] at ho
      simp only [Option.some.injEq] at ho
      subst ho
      have hobj := getKey_obj hgk
      obtain ⟨hhead, hkids⟩ := old_kids hobj hsh hg
      refine ⟨fun e he => ?_, renameHead_self (by
        cases hl : live n.ks with
        | nil => rw [hl] at hhead; cases hhead
        | cons a r => rw [hl] at hhead; simpa using hhead), ?_⟩
      · obtain ⟨⟨c, z⟩, hm, rfl⟩ := List.mem_map.mp he
        exact ⟨hkids c z hm, rfl⟩
      · show kids (view (h + 1) s y) = _
        rw [view_succ hobj]
        simp only [absK, List.map_map]
        apply List.map_congr_left
        intro q _
        simp [absV_old]
  | inner hk hne hhead _ _ =>
    simp only [openEs, Option.some.injEq] at ho
    subst ho
    exact ⟨fun e he => ⟨hk e he, hne e he⟩, hhead, rfl⟩

/-- A leaf child opened for a join: its entries. -/
theorem openEs_zero {g : Nat} {w : VN} {esW : List (Nat × VN)} (hw : VOk cf s g 0 w)
    (ho : openEs s w = some esW) :
    (∀ e ∈ esW, ∃ y, e.2 = .old y) ∧ absV s 0 w = esW.map (fun e => (e.1, e.2.oid)) := by
  cases hw with
  | @old _ y hsh hg hne =>
    simp only [openEs] at ho
    cases hgk : getKey s y with
    | none => rw [hgk] at ho; cases ho
    | some n =>
      rw [hgk] at ho
      simp only [Option.some.injEq] at ho
      subst ho
      refine ⟨fun e he => ?_, ?_⟩
      · obtain ⟨q, _, rfl⟩ := List.mem_map.mp he
        exact ⟨q.2, rfl⟩
      · show view 0 s y = _
        rw [view_zero (getKey_obj hgk), List.map_map]
        conv_lhs => rw [← List.map_id (live n.ks)]
        apply List.map_congr_left
        intro q _
        rfl
  | leaf hold _ _ =>
    simp only [openEs, Option.some.injEq] at ho
    subst ho
    exact ⟨hold, rfl⟩

theorem absV_empty {g h : Nat} {w : VN} (hw : VOk cf s g h w) (he : w.isEmpty = true) :
    absV s h w = [] := by
  cases w with
  | old y => cases he
  | node base g' h' join es F dec =>
    simp only [VN.isEmpty, List.isEmpty_iff] at he
    have := es_nil_of_F hw he
    subst this
    cases h <;> rfl

/-- The empty children dropped: steps of settle. -/
theorem filter_sett {g h : Nat} : ∀ (es : List (Nat × VN)), (∀ e ∈ es, VOk cf s g h e.2) →
    Sett h (absK s h es) (absK s h (es.filter (fun e => !e.2.isEmpty)))
  | [], _ => Sett.refl _ _
  | e :: r, hk => by
    have ih := filter_sett r (fun e he => hk e (List.mem_cons_of_mem _ he))
    by_cases he : e.2.isEmpty = true
    · have h0 := absV_empty (hk e List.mem_cons_self) he
      rw [List.filter_cons_of_neg (by simp [he])]
      refine Sett.step h _ (absK s h r) _ ?_ ih
      have := Step.drop (inner := h != 0) [] (absK s h r) e.1
      simp only [List.nil_append] at this
      simp only [absK, List.map_cons]
      rw [h0]
      exact this
    · rw [List.filter_cons_of_pos (by simpa using he)]
      have := ih.ctx [(e.1, absV s h e.2)] []
      simpa [absK] using this

theorem filter_head {es : List (Nat × VN)} (hne : ∀ e ∈ es, e.2.isEmpty = false) :
    es.filter (fun e => !e.2.isEmpty) = es := by
  rw [List.filter_eq_self]
  intro e he
  simp [hne e he]

/-- One join at the leaf level: a step of settle. -/
theorem join_core_zero (hcf : cf.Ok) {g : Nat} {es : List (Nat × VN)} {il : Nat} {l r : Nat × VN}
    {esL esR : List (Nat × VN)} {v : VN} (hl : es[il]? = some l) (hr : es[il + 1]? = some r)
    (hoL : openEs s l.2 = some esL) (hoR : openEs s r.2 = some esR)
    (hm : mkNode cf i s none g 0 true (esL ++ esR) = some v) (hes : KOk cf s g 0 es) :
    Sett 0 (absK s 0 es) (absK s 0 (es.take il ++ [(l.1, v)] ++ es.drop (il + 2))) ∧
      KOk cf s g 0 (es.take il ++ [(l.1, v)] ++ es.drop (il + 2)) ∧
      (es.take il ++ [(l.1, v)] ++ es.drop (il + 2)).head?.map (·.1) = es.head?.map (·.1) := by
  have hsplit := split_at2 hl hr
  have hlk := hes l (by rw [hsplit]; simp)
  have hrk := hes r (by rw [hsplit]; simp)
  obtain ⟨hL1, hL2⟩ := openEs_zero hlk.1 hoL
  obtain ⟨hR1, hR2⟩ := openEs_zero hrk.1 hoR
  have hLne : absV s 0 l.2 ≠ [] := absV_ne hlk.1 hlk.2
  obtain ⟨⟨F, dec, rfl⟩, hv⟩ := mkNode_leaf hcf hm (by
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact hL1 e he
    · exact hR1 e he)
  have hvabs : absV s 0 (VN.node none g 0 true (esL ++ esR) F dec) =
      absV s 0 l.2 ++ eff false (r.1, absV s 0 r.2) := by
    show (esL ++ esR).map (fun e => (e.1, e.2.oid)) = _
    rw [hL2, hR2, List.map_append]; rfl
  have hvne : (VN.node none g 0 true (esL ++ esR) F dec).isEmpty = false := by
    cases h0 : (VN.node none g 0 true (esL ++ esR) F dec).isEmpty
    · rfl
    · have := absV_empty hv h0
      rw [hvabs] at this
      exact absurd (List.append_eq_nil_iff.mp this).1 hLne
  generalize hA : es.take il = A at hsplit ⊢
  generalize hB : es.drop (il + 2) = B at hsplit ⊢
  subst hsplit
  refine ⟨?_, ?_, ?_⟩
  · have hst := Step.join (inner := false) (absK s 0 A) (absK s 0 B)
      l.1 r.1 (absV s 0 l.2) (absV s 0 r.2) hLne
    refine Sett.step 0 _ _ _ ?_ (Sett.refl _ _)
    simp only [absK, List.map_append, List.map_cons, List.map_nil] at hst ⊢
    rw [hvabs]
    simpa using hst
  · intro e he
    simp only [List.mem_append, List.mem_singleton] at he
    rcases he with (he | rfl) | he
    · exact hes e (by simp [he])
    · exact ⟨hv, hvne⟩
    · exact hes e (by simp [he])
  · simp only [List.append_assoc, List.singleton_append]
    exact head_fst_eq _ _ _ _ _ _

theorem joinAt_zero (hcf : cf.Ok) {g : Nat} {down : List (Nat × VN) → Option (List (Nat × VN))}
    {es es' : List (Nat × VN)} {ix : Nat} (hj : joinAt cf i s g 0 down es ix = some es')
    (hes : KOk cf s g 0 es) :
    Sett 0 (absK s 0 es) (absK s 0 es') ∧ KOk cf s g 0 es' ∧
      es'.head?.map (·.1) = es.head?.map (·.1) := by
  unfold joinAt at hj
  simp only at hj
  split at hj
  · rename_i l r hl hr
    split at hj
    · rename_i esL esR hoL hoR
      simp only [beq_self_eq_true, ite_true] at hj
      cases hm : mkNode cf i s none g 0 true (esL ++ esR) with
      | none => rw [hm] at hj; cases hj
      | some v =>
        rw [hm] at hj
        simp only [Option.some.injEq] at hj
        subst hj
        exact join_core_zero hcf hl hr hoL hoR hm hes
    · cases hj
  · cases hj

theorem absK_renameHead (h c : Nat) (es : List (Nat × VN)) :
    absK s h (renameHead c es) = renameHead c (absK s h es) := renameHead_map c _ es

/-- One join of two inner children, its list rebalanced one level down by
`down`: a step of settle (`Step.join`) and a settle one level down
(`Sett.down`). -/
theorem join_core_succ (hcf : cf.Ok) {g h : Nat} {es : List (Nat × VN)} {il : Nat}
    {l r : Nat × VN} {esL esR J' : List (Nat × VN)} {v : VN} (hl : es[il]? = some l)
    (hr : es[il + 1]? = some r) (hoL : openEs s l.2 = some esL) (hoR : openEs s r.2 = some esR)
    (hdown : KOk cf s g h (esL ++ renameHead r.1 esR) →
      Sett h (absK s h (esL ++ renameHead r.1 esR)) (absK s h J') ∧ KOk cf s g h J' ∧
        J'.head?.map (·.1) = (esL ++ renameHead r.1 esR).head?.map (·.1))
    (hm : mkNode cf i s none g (h + 1) true J' = some v) (hes : KOk cf s g (h + 1) es) :
    Sett (h + 1) (absK s (h + 1) es) (absK s (h + 1) (es.take il ++ [(l.1, v)] ++ es.drop (il + 2))) ∧
      KOk cf s g (h + 1) (es.take il ++ [(l.1, v)] ++ es.drop (il + 2)) ∧
      (es.take il ++ [(l.1, v)] ++ es.drop (il + 2)).head?.map (·.1) = es.head?.map (·.1) := by
  have hsplit := split_at2 hl hr
  have hlk := hes l (by rw [hsplit]; simp)
  have hrk := hes r (by rw [hsplit]; simp)
  obtain ⟨hL1, hL2, hL3⟩ := openEs_succ hlk.1 hoL
  obtain ⟨hR1, _, hR3⟩ := openEs_succ hrk.1 hoR
  have hLne : absV s (h + 1) l.2 ≠ [] := absV_ne hlk.1 hlk.2
  have hesL : esL ≠ [] := by
    rintro rfl
    apply hLne
    have : kids (absV s (h + 1) l.2) = [] := by rw [hL3]; rfl
    exact this
  have hJk : KOk cf s g h (esL ++ renameHead r.1 esR) := by
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact hL1 e he
    · obtain ⟨e', he', h2⟩ := renameHead_mem he
      rw [← h2]; exact hR1 e' he'
  obtain ⟨hd1, hd2, hd3⟩ := hdown hJk
  have hJh : (esL ++ renameHead r.1 esR).head?.map (·.1) = some 0 := by
    have := head_of_renameHead hL2 hesL
    cases esL with
    | nil => exact absurd rfl hesL
    | cons a t => simpa using this
  have hJ' : renameHead 0 J' = J' := renameHead_self (by rw [hd3, hJh])
  obtain ⟨⟨F, dec, rfl⟩, hv⟩ := mkNode_inner hcf hm (fun e he => (hd2 e he).1)
    (fun e he => (hd2 e he).2)
  have hvabs : kids (absV s (h + 1) (VN.node none g (h + 1) true (renameHead 0 J') F dec)) =
      absK s h J' := by
    show absK s h (renameHead 0 J') = _
    rw [hJ']
  have hvne : (VN.node none g (h + 1) true (renameHead 0 J') F dec).isEmpty = false := by
    cases h0 : (VN.node none g (h + 1) true (renameHead 0 J') F dec).isEmpty
    · rfl
    · have h1 := absV_empty hv h0
      have h2 : kids (absV s (h + 1) (VN.node none g (h + 1) true (renameHead 0 J') F dec)) = [] := by
        rw [h1]; rfl
      rw [hvabs] at h2
      have : J' = [] := by
        cases J' with
        | nil => rfl
        | cons a t => simp [absK] at h2
      rw [this] at hd3
      rw [hJh] at hd3
      cases hd3
  have hjoin : kids (absV s (h + 1) l.2 ++ eff true (r.1, absV s (h + 1) r.2)) =
      absK s h (esL ++ renameHead r.1 esR) := by
    rw [absK_append, absK_renameHead, ← hL3, ← hR3]
    rfl
  generalize hA : es.take il = A at hsplit ⊢
  generalize hB : es.drop (il + 2) = B at hsplit ⊢
  subst hsplit
  refine ⟨?_, ?_, ?_⟩
  · have hst := Step.join (inner := true) (absK s (h + 1) A) (absK s (h + 1) B)
      l.1 r.1 (absV s (h + 1) l.2) (absV s (h + 1) r.2) hLne
    refine Sett.step (h + 1) _ _ _ (by simpa [absK] using hst) ?_
    refine Sett.down h (absK s (h + 1) A) (absK s (h + 1) B) l.1 _
      (absV s (h + 1) (VN.node none g (h + 1) true (renameHead 0 J') F dec)) _ ?_ ?_
    · rw [hjoin, hvabs]; exact hd1
    · simpa [absK] using Sett.refl (h + 1) _
  · intro e he
    simp only [List.mem_append, List.mem_singleton] at he
    rcases he with (he | rfl) | he
    · exact hes e (by simp [he])
    · exact ⟨hv, hvne⟩
    · exact hes e (by simp [he])
  · simp only [List.append_assoc, List.singleton_append]
    exact head_fst_eq _ _ _ _ _ _

theorem joinAt_succ (hcf : cf.Ok) {g h : Nat} {down : List (Nat × VN) → Option (List (Nat × VN))}
    (hdown : ∀ J J', down J = some J' → KOk cf s g h J →
      Sett h (absK s h J) (absK s h J') ∧ KOk cf s g h J' ∧ J'.head?.map (·.1) = J.head?.map (·.1))
    {es es' : List (Nat × VN)} {ix : Nat} (hj : joinAt cf i s g (h + 1) down es ix = some es')
    (hes : KOk cf s g (h + 1) es) :
    Sett (h + 1) (absK s (h + 1) es) (absK s (h + 1) es') ∧ KOk cf s g (h + 1) es' ∧
      es'.head?.map (·.1) = es.head?.map (·.1) := by
  unfold joinAt at hj
  simp only at hj
  split at hj
  · rename_i l r hl hr
    split at hj
    · rename_i esL esR hoL hoR
      simp only [show (h + 1 == 0) = false by simp, Bool.false_eq_true, ite_false] at hj
      cases hd : down (esL ++ renameHead r.1 esR) with
      | none => rw [hd] at hj; cases hj
      | some J' =>
        rw [hd] at hj
        simp only at hj
        cases hm : mkNode cf i s none g (h + 1) true J' with
        | none => rw [hm] at hj; cases hj
        | some v =>
          rw [hm] at hj
          simp only [Option.some.injEq] at hj
          subst hj
          exact join_core_succ hcf hl hr hoL hoR (hdown _ _ hd) hm hes
    · cases hj
  · cases hj

/-- The loop of joins: a settle. -/
theorem joinLoop_spec {g h : Nat} {down : List (Nat × VN) → Option (List (Nat × VN))}
    (hjoin : ∀ es ix es', joinAt cf i s g h down es ix = some es' → KOk cf s g h es →
      Sett h (absK s h es) (absK s h es') ∧ KOk cf s g h es' ∧
        es'.head?.map (·.1) = es.head?.map (·.1)) :
    ∀ (n : Nat) (es es' : List (Nat × VN)), joinLoop cf i s g h down n es = some es' →
      KOk cf s g h es → Sett h (absK s h es) (absK s h es') ∧ KOk cf s g h es' ∧
        es'.head?.map (·.1) = es.head?.map (·.1)
  | 0, es, es', hl, hk => by
    simp only [joinLoop, Option.some.injEq] at hl
    subst hl
    exact ⟨Sett.refl _ _, hk, rfl⟩
  | n + 1, es, es', hl, hk => by
    simp only [joinLoop] at hl
    split at hl
    · simp only [Option.some.injEq] at hl; subst hl; exact ⟨Sett.refl _ _, hk, rfl⟩
    · split at hl
      · simp only [Option.some.injEq] at hl; subst hl; exact ⟨Sett.refl _ _, hk, rfl⟩
      · rename_i ix _
        cases hj : joinAt cf i s g h down es ix with
        | none => rw [hj] at hl; cases hl
        | some es1 =>
          rw [hj] at hl
          simp only at hl
          obtain ⟨a1, a2, a3⟩ := hjoin es ix es1 hj hk
          obtain ⟨b1, b2, b3⟩ := joinLoop_spec hjoin n es1 es' hl a2
          exact ⟨a1.trans b1, b2, b3.trans a3⟩

/-- **Rebalance is a settle**: the children rebalanced are the children
before, settled (`Sett`): an empty child dropped (`Step.drop`), a join
(`Step.join`), a joined list of inner nodes rebalanced one level down
(`Sett.down`). The children after are nonempty and each one the program
can make; and the first compare value is kept if no child was empty. -/
theorem rebalance_spec (hcf : cf.Ok) {g : Nat} : ∀ (f h : Nat) (es0 es2 : List (Nat × VN)),
    rebalance cf i s f g h es0 = some es2 → (∀ e ∈ es0, VOk cf s g h e.2) →
    Sett h (absK s h es0) (absK s h es2) ∧ KOk cf s g h es2 ∧
      ((∀ e ∈ es0, e.2.isEmpty = false) → es2.head?.map (·.1) = es0.head?.map (·.1))
  | 0, _, _, _, hr, _ => by simp [rebalance] at hr
  | f + 1, h, es0, es2, hr, hk => by
    unfold rebalance at hr
    simp only at hr
    have hs1 := filter_sett es0 hk
    have hk1 : KOk cf s g h (es0.filter (fun e => !e.2.isEmpty)) := by
      intro e he
      rw [List.mem_filter] at he
      exact ⟨hk e he.1, by simpa using he.2⟩
    have hh1 : (∀ e ∈ es0, e.2.isEmpty = false) →
        (es0.filter (fun e => !e.2.isEmpty)).head?.map (·.1) = es0.head?.map (·.1) := by
      intro hne; rw [filter_head hne]
    split at hr
    · simp only [Option.some.injEq] at hr
      subst hr
      exact ⟨hs1, hk1, hh1⟩
    · have hjoin : ∀ es ix es', joinAt cf i s g h (fun J => rebalance cf i s f g (h - 1) J) es ix =
          some es' → KOk cf s g h es →
          Sett h (absK s h es) (absK s h es') ∧ KOk cf s g h es' ∧
            es'.head?.map (·.1) = es.head?.map (·.1) := by
        intro es ix es' hj hes
        cases h with
        | zero => exact joinAt_zero hcf hj hes
        | succ h' =>
          refine joinAt_succ hcf (fun J J' hd hJ => ?_) hj hes
          obtain ⟨a1, a2, a3⟩ := rebalance_spec hcf f h' J J' hd (fun e he => (hJ e he).1)
          exact ⟨a1, a2, a3 (fun e he => (hJ e he).2)⟩
      obtain ⟨b1, b2, b3⟩ := joinLoop_spec hjoin _ _ _ hr hk1
      exact ⟨hs1.trans b1, b2, fun hne => b3.trans (hh1 hne)⟩

/-! ## The leaf: the operations applied -/

theorem lookup_cons' {α : Type} (a k : Nat) (b : α) (es : List (Nat × α)) :
    ((k, b) :: es).lookup a = if a = k then some b else es.lookup a := by
  simp only [List.lookup_cons]
  by_cases h : a = k
  · subst h; simp
  · rw [beq_false_of_ne h]; simp [h]

theorem setEntry_lookup {α : Type} (c : Nat) (v : α) :
    ∀ (l : List (Nat × α)) (a : Nat), (setEntry c v l).lookup a = if a = c then some v else l.lookup a
  | [], a => by simp [setEntry, lookup_cons']
  | (c', v') :: r, a => by
    unfold setEntry
    split
    · simp only [lookup_cons']
    · split
      · rename_i h1 h2
        subst h2
        by_cases h3 : a = c <;> simp [lookup_cons', h3]
      · rw [lookup_cons', lookup_cons', setEntry_lookup c v r a]
        rename_i h1 h2
        by_cases h3 : a = c <;> by_cases h4 : a = c' <;> simp [h3, h4] <;> omega

theorem mem_setEntry {α : Type} {c : Nat} {v : α} {e : Nat × α} :
    ∀ {l : List (Nat × α)}, e ∈ setEntry c v l → e = (c, v) ∨ e ∈ l
  | [], h => by simp [setEntry] at h; exact Or.inl h
  | (c', v') :: r, h => by
    unfold setEntry at h
    split at h
    · simp only [List.mem_cons] at h
      rcases h with h | h | h
      · exact Or.inl h
      · exact Or.inr (by simp [h])
      · exact Or.inr (by simp [h])
    · split at h
      · simp only [List.mem_cons] at h
        rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (by simp [h])
      · simp only [List.mem_cons] at h
        rcases h with h | h
        · exact Or.inr (by simp [h])
        · rcases mem_setEntry h with h | h
          · exact Or.inl h
          · exact Or.inr (by simp [h])

theorem setEntry_sorted {α : Type} (c : Nat) (v : α) : ∀ {l : List (Nat × α)},
    l.Pairwise CvLtA → (setEntry c v l).Pairwise CvLtA
  | [], _ => by simp [setEntry]
  | (c', v') :: r, h => by
    rw [List.pairwise_cons] at h
    unfold setEntry
    split
    · rename_i h1
      refine List.pairwise_cons.mpr ⟨fun b hb => ?_, List.pairwise_cons.mpr h⟩
      rcases List.mem_cons.mp hb with rfl | hb
      · exact h1
      · have := h.1 b hb; simp only [CvLtA] at this ⊢; omega
    · split
      · rename_i h1 h2
        subst h2
        exact List.pairwise_cons.mpr ⟨fun b hb => h.1 b hb, h.2⟩
      · rename_i h1 h2
        refine List.pairwise_cons.mpr ⟨fun b hb => ?_, setEntry_sorted c v h.2⟩
        rcases mem_setEntry hb with rfl | hb
        · show c' < c; omega
        · exact h.1 b hb

theorem filter_lookup {α : Type} (c : Nat) :
    ∀ (l : List (Nat × α)) (a : Nat), (l.filter (fun e => e.1 != c)).lookup a =
      if a = c then none else l.lookup a
  | [], a => by simp
  | (c', v') :: r, a => by
    rw [List.filter_cons]
    by_cases hc : c' = c
    · subst c'
      simp only [bne_self_eq_false, Bool.false_eq_true, ite_false]
      rw [filter_lookup c r a, lookup_cons']
      by_cases h3 : a = c <;> simp [h3]
    · simp only [bne_iff_ne, ne_eq, hc, not_false_eq_true, ite_true]
      rw [lookup_cons', lookup_cons', filter_lookup c r a]
      by_cases h3 : a = c <;> by_cases h4 : a = c' <;> simp [h3, h4] <;> omega

theorem removeEntry_lookup {α : Type} (c : Nat) (l : List (Nat × α)) (a : Nat) :
    (removeEntry c l).lookup a = if a = c then none else l.lookup a := filter_lookup c l a

theorem foldl_inv {β γ : Type} (P : β → Prop) (st : β → γ → β) (hst : ∀ q x, P q → P (st q x)) :
    ∀ (L : List γ) (q : β), P q → P (L.foldl st q)
  | [], _, h => h
  | x :: L, q, h => foldl_inv P st hst L (st q x) (hst q x h)

/-- **The leaf's operations**: `applyGroups` keeps the list in order and
changes only the compare values of its groups. -/
theorem applyGroups_spec : ∀ (f g : Nat) (es0 : List (Nat × NodeId)) (cvs : List Nat)
    (ops : List Contract.Op) (acc : Acc) (es : List (Nat × NodeId)) (acc' : Acc),
    applyGroups cf i s f g es0 cvs ops acc = some (es, acc') → es0.Pairwise CvLtA →
    es.Pairwise CvLtA ∧ ∀ c, c ∉ cvs → es.lookup c = es0.lookup c
  | 0, _, _, _, _, _, _, _, h, _ => by simp [applyGroups] at h
  | f + 1, g, es0, [], ops, acc, es, acc', h, hs => by
    simp only [applyGroups, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact ⟨hs, fun _ _ => rfl⟩
  | f + 1, g, es0, cv :: cvs, ops, acc, es, acc', h, hs => by
    unfold applyGroups at h
    simp only at h
    generalize hq : List.foldl _ (es0, acc) _ = q at h
    have hq1 : q.1.Pairwise CvLtA ∧ ∀ c, c ≠ cv → q.1.lookup c = es0.lookup c := by
      rw [← hq]
      refine foldl_inv (fun q : List (Nat × NodeId) × Acc =>
        q.1.Pairwise CvLtA ∧ ∀ c, c ≠ cv → q.1.lookup c = es0.lookup c) _ ?_ _ _ ⟨hs, fun _ _ => rfl⟩
      intro q' op hq'
      cases op with
      | put k hv =>
        refine ⟨setEntry_sorted _ _ hq'.1, fun c hc => ?_⟩
        rw [setEntry_lookup, ite_eq_right hc]
        exact hq'.2 c hc
      | del k =>
        refine ⟨hq'.1.filter _, fun c hc => ?_⟩
        show (removeEntry cv q'.1).lookup c = _
        rw [removeEntry_lookup, ite_eq_right hc]
        exact hq'.2 c hc
    obtain ⟨es1, acc1⟩ := q
    simp only at h hq1
    have fin1 : ∀ es2 : List (Nat × NodeId), es2.Pairwise CvLtA →
        (∀ c, c ≠ cv → es2.lookup c = es1.lookup c) → ∀ acc2,
        applyGroups cf i s f g es2 cvs ops acc2 = some (es, acc') →
        es.Pairwise CvLtA ∧ ∀ c, c ∉ cv :: cvs → es.lookup c = es0.lookup c := by
      intro es2 hs2 hl2 acc2 h2
      obtain ⟨a1, a2⟩ := applyGroups_spec f g es2 cvs ops acc2 es acc' h2 hs2
      refine ⟨a1, fun c hc => ?_⟩
      simp only [List.mem_cons, not_or] at hc
      rw [a2 c hc.2, hl2 c hc.1, hq1.2 c hc.1]
    split at h
    · exact fin1 es1 hq1.1 (fun _ _ => rfl) _ h
    · split at h
      · cases h
      · rename_i y acc2 _
        exact fin1 _ (setEntry_sorted _ _ hq1.1) (fun c hc => by
          rw [setEntry_lookup, ite_eq_right hc]) _ h
      · rename_i acc2 _
        exact fin1 _ (hq1.1.filter _) (fun c hc => by
          show (removeEntry cv es1).lookup c = _
          rw [removeEntry_lookup, ite_eq_right hc]) _ h

theorem mput_lookup (c v : Nat) :
    ∀ (l : List (Nat × Nat)) (a : Nat), (Abs.mput c v l).lookup a = if a = c then some v else l.lookup a
  | [], a => by simp [Abs.mput]
  | (c', v') :: r, a => by
    unfold Abs.mput
    split
    · simp only [lookup_cons']
    · split
      · rename_i h1 h2
        subst h2
        by_cases h3 : a = c <;> simp [lookup_cons', h3]
      · rw [lookup_cons', lookup_cons', mput_lookup c v r a]
        rename_i h1 h2
        by_cases h3 : a = c <;> by_cases h4 : a = c' <;> simp [h3, h4] <;> omega

theorem lookup_mem {α : Type} {a : Nat} {v : α} :
    ∀ {l : List (Nat × α)}, l.lookup a = some v → (a, v) ∈ l
  | [], h => by simp at h
  | (c, w) :: r, h => by
    rw [lookup_cons'] at h
    split at h
    · rename_i hc; subst hc; cases h; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookup_mem h)

theorem lookup_none_of_lt {α : Type} {a : Nat} :
    ∀ {l : List (Nat × α)}, (∀ e ∈ l, a < e.1) → l.lookup a = none
  | [], _ => rfl
  | (c, w) :: r, h => by
    rw [lookup_cons', ite_eq_right (by have := h (c, w) List.mem_cons_self; simp at this; omega)]
    exact lookup_none_of_lt (fun e he => h e (List.mem_cons_of_mem _ he))

/-- Two lists in order with the same lookups are the same. -/
theorem eq_of_lookup {α : Type} : ∀ (m es : List (Nat × α)), m.Pairwise CvLtA → es.Pairwise CvLtA →
    (∀ c, m.lookup c = es.lookup c) → m = es
  | [], [], _, _, _ => rfl
  | [], (b, y) :: es, _, _, h => by
    have := h b; rw [lookup_cons', ite_eq_left rfl] at this; simp at this
  | (a, x) :: m, [], _, _, h => by
    have := h a; rw [lookup_cons', ite_eq_left rfl] at this; simp at this
  | (a, x) :: m, (b, y) :: es, hm, hes, h => by
    rw [List.pairwise_cons] at hm hes
    have hab : a = b := by
      have h1 := h a
      have h2 := h b
      rw [lookup_cons', ite_eq_left rfl, lookup_cons'] at h1
      rw [lookup_cons', lookup_cons', ite_eq_left rfl] at h2
      by_contra hne
      rw [ite_eq_right hne] at h1
      rw [ite_eq_right (Ne.symm hne)] at h2
      have m1 := hes.1 _ (lookup_mem h1.symm)
      have m2 := hm.1 _ (lookup_mem h2)
      simp only [CvLtA] at m1 m2
      omega
    subst hab
    have hxy : x = y := by
      have h1 := h a
      rw [lookup_cons', ite_eq_left rfl, lookup_cons', ite_eq_left rfl] at h1
      cases h1; rfl
    subst hxy
    congr 1
    refine eq_of_lookup m es hm.2 hes.2 (fun c => ?_)
    by_cases hc : c = a
    · subst hc
      rw [lookup_none_of_lt (fun e he => hm.1 e he), lookup_none_of_lt (fun e he => hes.1 e he)]
    · have := h c
      rw [lookup_cons', lookup_cons', ite_eq_right hc, ite_eq_right hc] at this
      exact this

/-- The final operations of a leaf, applied to its list before, give its
list after, if the list after is in order and differs from it only at
the compare values of T. -/
theorem applyOps_finalOps : ∀ (T : List Nat) (m es : List (Nat × Nat)), m.Pairwise CvLtA →
    es.Pairwise CvLtA → (∀ c, c ∉ T → es.lookup c = m.lookup c) → Abs.applyOps (finalOps T es) m = es
  | [], m, es, hm, hes, h => (eq_of_lookup m es hm hes (fun c => (h c (by simp)).symm))
  | t :: T, m, es, hm, hes, h => by
    show Abs.applyOps (finalOps T es) (Abs.applyOp m (match es.lookup t with
      | some y => Abs.Op.put t y
      | none => Abs.Op.del t)) = es
    apply applyOps_finalOps T _ es _ hes
    · intro c hc
      cases ht : es.lookup t with
      | some y =>
        simp only [Abs.applyOp]
        rw [mput_lookup]
        split
        · rename_i hct; subst hct; exact ht
        · rename_i hct; exact h c (by simp [hc, hct])
      | none =>
        simp only [Abs.applyOp]
        rw [filter_lookup]
        split
        · rename_i hct; subst hct; exact ht
        · rename_i hct; exact h c (by simp [hc, hct])
    · cases es.lookup t with
      | some y => exact mput_sorted t y hm
      | none => exact hm.filter _

theorem finalOps_cv (T : List Nat) (es : List (Nat × Nat)) :
    (finalOps T es).map Abs.Op.cv = T := by
  unfold finalOps
  rw [List.map_map]
  conv_rhs => rw [← List.map_id T]
  apply List.map_congr_left
  intro c _
  simp only [Function.comp_apply]
  split <;> rfl

/-! ## The compare values touched -/

theorem nodup_eraseDups_aux : ∀ (n : Nat) (l : List Nat), l.length ≤ n → l.eraseDups.Nodup
  | 0, l, h => by
    rw [List.eq_nil_of_length_eq_zero (by omega : l.length = 0), List.eraseDups_nil]
    exact List.nodup_nil
  | _ + 1, [], _ => by rw [List.eraseDups_nil]; exact List.nodup_nil
  | n + 1, a :: as, h => by
    rw [List.eraseDups_cons]
    refine List.nodup_cons.mpr ⟨?_, nodup_eraseDups_aux n _ ?_⟩
    · rw [List.mem_eraseDups]; simp
    · have := List.length_filter_le (fun b => !b == a) as
      simp only [List.length_cons] at h
      omega

theorem nodup_touched (g : Nat) (ops : List Contract.Op) : (touched g ops).Nodup :=
  nodup_eraseDups_aux _ _ (le_refl _)

theorem mem_touched {g c : Nat} {ops : List Contract.Op} :
    c ∈ touched g ops ↔ ∃ op ∈ ops, segAt g op = c := by
  unfold touched
  rw [List.mem_eraseDups, List.mem_map]

theorem touched_nil (g : Nat) : touched g [] = [] := rfl

theorem eraseDups_filter_aux (q : Nat → Bool) : ∀ (n : Nat) (L : List Nat), L.length ≤ n →
    (L.filter q).eraseDups = L.eraseDups.filter q
  | 0, L, h => by
    rw [List.eq_nil_of_length_eq_zero (by omega : L.length = 0)]
    simp [List.eraseDups_nil]
  | _ + 1, [], _ => by simp [List.eraseDups_nil]
  | n + 1, a :: as, h => by
    have hlen : (as.filter (fun b => !b == a)).length ≤ n := by
      have := List.length_filter_le (fun b => !b == a) as
      simp only [List.length_cons] at h
      omega
    rw [List.eraseDups_cons, List.filter_cons]
    by_cases hq : q a = true
    · rw [ite_eq_left hq, List.eraseDups_cons, List.filter_cons_of_pos hq,
        ← eraseDups_filter_aux q n _ hlen, List.filter_comm]
    · rw [ite_eq_right hq, List.filter_cons_of_neg hq, ← eraseDups_filter_aux q n _ hlen]
      congr 1
      rw [List.filter_comm]
      symm
      apply List.filter_eq_self.mpr
      intro b hb
      have := (List.mem_filter.mp hb).2
      cases hba : (b == a)
      · rfl
      · rw [beq_iff_eq] at hba
        subst hba
        exact absurd this hq

/-- The compare values touched by the operations of a range: those of the
range. -/
theorem touched_filter (g : Nat) (q : Nat → Bool) (ops : List Contract.Op) :
    touched g (ops.filter (fun o => q (segAt g o))) = (touched g ops).filter q := by
  unfold touched
  rw [← eraseDups_filter_aux q _ _ le_rfl, List.filter_map]
  rfl

/-- Operations of two ranges, each in the order of its compare values in T,
interleaved in the order of T. -/
theorem interleave (c' : Nat) : ∀ (T : List Nat) (A B : List Abs.Op),
    A.map Abs.Op.cv = T.filter (fun c => decide (c < c')) →
    B.map Abs.Op.cv = T.filter (fun c => decide (c' ≤ c)) →
    ∃ S : List Abs.Op, S.map Abs.Op.cv = T ∧ S.filter (fun o => decide (o.cv < c')) = A ∧
      S.filter (fun o => decide (c' ≤ o.cv)) = B
  | [], A, B, hA, hB => by
    simp only [List.filter_nil, List.map_eq_nil_iff] at hA hB
    subst hA; subst hB
    exact ⟨[], rfl, rfl, rfl⟩
  | t :: T, A, B, hA, hB => by
    by_cases ht : t < c'
    · rw [List.filter_cons_of_pos (by simpa using ht)] at hA
      rw [List.filter_cons_of_neg (by simpa using ht)] at hB
      cases A with
      | nil => simp at hA
      | cons a A' =>
        simp only [List.map_cons, List.cons.injEq] at hA
        obtain ⟨S, h1, h2, h3⟩ := interleave c' T A' B hA.2 hB
        refine ⟨a :: S, by simp [h1, hA.1], ?_, ?_⟩
        · rw [List.filter_cons_of_pos (by simpa [hA.1] using ht), h2]
        · rw [List.filter_cons_of_neg (by simp [hA.1]; omega), h3]
    · rw [List.filter_cons_of_neg (by simpa using ht)] at hA
      rw [List.filter_cons_of_pos (by simp; omega)] at hB
      cases B with
      | nil => simp at hB
      | cons b B' =>
        simp only [List.map_cons, List.cons.injEq] at hB
        obtain ⟨S, h1, h2, h3⟩ := interleave c' T A B' hA hB.2
        refine ⟨b :: S, by simp [h1, hB.1], ?_, ?_⟩
        · rw [List.filter_cons_of_neg (by simp [hB.1]; omega), h2]
        · rw [List.filter_cons_of_pos (by simp [hB.1]; omega), h3]

/-! ## The children planned: routed -/

/-- What `plan` gives at fuel f, for the induction: an instance of `Plan`
whose operations touch the compare values of the operations, and a node
`VOk`. -/
def PlanOk (cf : Cfg) (i : Time) (s : Tree) (f : Nat) : Prop :=
  ∀ (x : NodeId) (g h : Nat) (ops : List Contract.Op) (acc : Acc) (v : VN) (acc' : Acc)
    (lo : Nat) (hi : Option Nat),
    plan cf i s f x g h ops acc = some (v, acc') → Shaped cf s g h x → Good s x lo hi →
    ∃ sops : List Abs.Op, Plan h (view h s x) sops (absV s h v) ∧
      sops.map Abs.Op.cv = touched g ops ∧ VOk cf s g h v

theorem planKids_nil : ∀ (f g h : Nat) (os : List (List Contract.Op)) (acc : Acc)
    (es : List (Nat × VN)) (acc' : Acc), planKids cf i s f g h [] os acc = some (es, acc') → es = []
  | 0, _, _, _, _, _, _, hp => by simp [planKids] at hp
  | f + 1, _, _, _, _, _, _, hp => by
    simp only [planKids, Option.some.injEq, Prod.mk.injEq] at hp
    exact hp.1.symm

/-- **The children planned are routed**: `planKids` with the program's
`route` is an instance of `Routed (Plan h)` with 026-24's `route`, for the
children's operations interleaved in the order of the compare values the
operations touch (each child's within its range, as the program routed
them). -/
theorem planKids_spec {g h : Nat} : ∀ (F : Nat) (lv : List (Nat × NodeId)) (ops : List Contract.Op)
    (acc : Acc) (es : List (Nat × VN)) (acc' : Acc),
    (∀ f' < F, PlanOk cf i s f') → lv ≠ [] →
    planKids cf i s F g (h + 1) lv (Contract.PE.route (segAt g) lv ops) acc = some (es, acc') →
    (∀ c y, (c, y) ∈ lv → VOk cf s g h (.old y)) →
    ∃ sops : List Abs.Op,
      Routed (Plan h) (lv.map (fun cy => (cy.1, view h s cy.2)))
        (PeProof.Abs.route (lv.map (fun cy => (cy.1, view h s cy.2))) sops) (absK s h es) ∧
      sops.map Abs.Op.cv = touched g ops ∧ (∀ e ∈ es, VOk cf s g h e.2)
  | 0, _, _, _, _, _, _, _, hp, _ => by simp [planKids] at hp
  | _, [], _, _, _, _, _, hne, _, _ => absurd rfl hne
  | F + 1, [(c, y)], ops, acc, es, acc', IH, _, hp, hk => by
    have hy := hk c y (by simp)
    obtain ⟨hsh, ⟨lo, hi, hg⟩, _⟩ : Shaped cf s g h y ∧ (∃ lo hi, Good s y lo hi) ∧ view h s y ≠ [] := by
      cases hy with
      | old a b c => exact ⟨a, b, c⟩
    simp only [Contract.PE.route, planKids, Nat.add_sub_cancel] at hp
    split at hp
    · rename_i hops
      cases hp2 : planKids cf i s F g (h + 1) [] [] acc with
      | none => rw [hp2] at hp; cases hp
      | some q =>
        rw [hp2] at hp
        obtain ⟨es2, acc2⟩ := q
        simp only [Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, _⟩ := hp
        have := planKids_nil _ _ _ _ _ _ _ hp2
        subst this
        have hops' : ops = [] := List.isEmpty_iff.mp hops
        subst hops'
        refine ⟨[], ?_, rfl, ?_⟩
        · simp only [List.map_cons, List.map_nil, PeProof.Abs.route, absK, absV_old]
          exact Routed.keep c _ [] [] [] Routed.nil
        · intro e he; simp at he; subst he; exact hy
    · cases hp1 : plan cf i s F y g h ops acc with
      | none => rw [hp1] at hp; cases hp
      | some q =>
        rw [hp1] at hp
        obtain ⟨v, acc1⟩ := q
        simp only at hp
        cases hp2 : planKids cf i s F g (h + 1) [] [] acc1 with
        | none => rw [hp2] at hp; cases hp
        | some q =>
          rw [hp2] at hp
          obtain ⟨es2, acc2⟩ := q
          simp only [Option.some.injEq, Prod.mk.injEq] at hp
          obtain ⟨rfl, _⟩ := hp
          have := planKids_nil _ _ _ _ _ _ _ hp2
          subst this
          obtain ⟨sops, hpl, hcv, hv⟩ := IH F (by omega) y g h ops acc v acc1 lo hi hp1 hsh hg
          refine ⟨sops, ?_, hcv, ?_⟩
          · simp only [List.map_cons, List.map_nil, PeProof.Abs.route, absK]
            exact Routed.plan c _ sops _ [] [] [] hpl Routed.nil
          · intro e he; simp at he; subst he; exact hv
  | F + 1, (c, y) :: (c', y') :: r, ops, acc, es, acc', IH, _, hp, hk => by
    have hy := hk c y (by simp)
    obtain ⟨hsh, ⟨lo, hi, hg⟩, _⟩ : Shaped cf s g h y ∧ (∃ lo hi, Good s y lo hi) ∧ view h s y ≠ [] := by
      cases hy with
      | old a b c => exact ⟨a, b, c⟩
    have hk' : ∀ c y, (c, y) ∈ (c', y') :: r → VOk cf s g h (.old y) :=
      fun c y h => hk c y (List.mem_cons_of_mem _ h)
    have IH' : ∀ f' < F, PlanOk cf i s f' := fun f' h => IH f' (by omega)
    have ht1 := touched_filter g (fun c => decide (c < c')) ops
    have ht2 := touched_filter g (fun c => decide (c' ≤ c)) ops
    simp only [Contract.PE.route] at hp
    simp only [planKids, Nat.add_sub_cancel] at hp
    generalize ho1 : ops.filter (fun o => decide (segAt g o < c')) = o1 at hp ht1
    generalize ho2 : ops.filter (fun o => decide (c' ≤ segAt g o)) = o2 at hp ht2
    split at hp
    · rename_i hops
      have ho1' : o1 = [] := List.isEmpty_iff.mp hops
      subst ho1'
      have ho2' : o2 = ops := by
        rw [← ho2]
        apply List.filter_eq_self.mpr
        intro op hop
        have := List.filter_eq_nil_iff.mp ho1 op hop
        simp at this ⊢
        omega
      subst ho2'
      cases hp2 : planKids cf i s F g (h + 1) ((c', y') :: r)
          (Contract.PE.route (segAt g) ((c', y') :: r) o2) acc with
      | none => rw [hp2] at hp; cases hp
      | some q =>
        rw [hp2] at hp
        obtain ⟨es2, acc2⟩ := q
        simp only [Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, _⟩ := hp
        obtain ⟨sops, hr, hcv, hv⟩ := planKids_spec F ((c', y') :: r) o2 acc es2 acc2 IH'
          (by simp) hp2 hk'
        have hge : ∀ o ∈ sops, c' ≤ o.cv := by
          intro o ho
          have hm : o.cv ∈ touched g o2 := by rw [← hcv]; exact List.mem_map_of_mem ho
          obtain ⟨op, hop, he⟩ := mem_touched.mp hm
          have := List.filter_eq_nil_iff.mp ho1 op hop
          simp at this
          omega
        refine ⟨sops, ?_, hcv, ?_⟩
        · simp only [List.map_cons, PeProof.Abs.route, absK, absV_old] at hr ⊢
          rw [List.filter_eq_nil_iff.mpr (fun o ho => by have := hge o ho; simp; omega),
            List.filter_eq_self.mpr (fun o ho => by have := hge o ho; simpa using this)]
          exact Routed.keep c _ _ _ _ hr
        · intro e he
          simp only [List.mem_cons] at he
          rcases he with rfl | he
          · exact hy
          · exact hv e he
    · cases hp1 : plan cf i s F y g h o1 acc with
      | none => rw [hp1] at hp; cases hp
      | some q =>
        rw [hp1] at hp
        obtain ⟨v, acc1⟩ := q
        simp only at hp
        cases hp2 : planKids cf i s F g (h + 1) ((c', y') :: r)
            (Contract.PE.route (segAt g) ((c', y') :: r) o2) acc1 with
        | none => rw [hp2] at hp; cases hp
        | some q =>
          rw [hp2] at hp
          obtain ⟨es2, acc2⟩ := q
          simp only [Option.some.injEq, Prod.mk.injEq] at hp
          obtain ⟨rfl, _⟩ := hp
          obtain ⟨sops1, hpl, hcv1, hv1⟩ := IH F (by omega) y g h o1 acc v acc1 lo hi hp1 hsh hg
          obtain ⟨sops, hr, hcv, hv⟩ := planKids_spec F ((c', y') :: r) o2 acc1 es2 acc2 IH'
            (by simp) hp2 hk'
          obtain ⟨S, hS1, hS2, hS3⟩ := interleave c' (touched g ops) sops1 sops
            (by rw [hcv1, ht1]) (by rw [hcv, ht2])
          refine ⟨S, ?_, hS1, ?_⟩
          · simp only [List.map_cons, PeProof.Abs.route, absK] at hr ⊢
            rw [hS2, hS3]
            exact Routed.plan c _ sops1 _ _ _ _ hpl hr
          · intro e he
            simp only [List.mem_cons] at he
            rcases he with rfl | he
            · exact hv1
            · exact hv e he

/-! ## Plan is an instance of `Plan` -/

theorem plan_ok (hcf : cf.Ok) : ∀ f, PlanOk cf i s f := by
  intro f
  refine Nat.strong_induction_on f ?_
  intro f IH x g h ops acc v acc' lo hi hp hsh hg
  cases f with
  | zero => simp [plan] at hp
  | succ f =>
    unfold plan at hp
    cases hgk : getKey s x with
    | none => rw [hgk] at hp; cases hp
    | some n =>
      rw [hgk] at hp
      simp only at hp
      have hobj := getKey_obj hgk
      split at hp
      · -- a segment leaf: the operations applied
        rename_i hh
        have hh0 : h = 0 := by simpa using hh
        subst hh0
        cases ha : applyGroups cf i s f g (live n.ks) ((ops.map (segAt g)).eraseDups) ops acc with
        | none => rw [ha] at hp; cases hp
        | some q =>
          rw [ha] at hp
          obtain ⟨es, acc1⟩ := q
          simp only at hp
          cases hm : mkNode cf i s (some x) g 0 false (es.map (fun e => (e.1, VN.old e.2))) with
          | none => rw [hm] at hp; cases hp
          | some w =>
            rw [hm] at hp
            simp only [Option.some.injEq, Prod.mk.injEq] at hp
            obtain ⟨rfl, _⟩ := hp
            obtain ⟨⟨F, dec, rfl⟩, hv⟩ := mkNode_leaf hcf hm (by
              intro e he
              obtain ⟨q, _, rfl⟩ := List.mem_map.mp he
              exact ⟨q.2, rfl⟩)
            have hsorted : (live n.ks).Pairwise CvLtA := live_sorted n.ks
            obtain ⟨hs1, hs2⟩ := applyGroups_spec f g _ _ ops acc es acc1 ha hsorted
            refine ⟨finalOps (touched g ops) es, ?_, by rw [finalOps_cv], hv⟩
            have habs : absV s 0 (VN.node (some x) g 0 false (es.map (fun e => (e.1, VN.old e.2))) F dec) =
                es := by
              show (es.map (fun e => (e.1, VN.old e.2))).map (fun e => (e.1, e.2.oid)) = es
              rw [List.map_map]
              conv_rhs => rw [← List.map_id es]
              apply List.map_congr_left
              intro e _
              rfl
            show absV s 0 _ = Abs.applyOps (finalOps (touched g ops) es) (view 0 s x)
            rw [view_zero hobj, habs]
            exact (applyOps_finalOps _ _ _ hsorted hs1 hs2).symm
      · -- an inner node: the children planned, rebalanced
        rename_i hh
        obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by simp at hh; omega⟩
        simp only [Nat.add_sub_cancel] at hp
        cases hpk : planKids cf i s f g (h' + 1) (live n.ks)
            (Contract.PE.route (segAt g) (live n.ks) ops) acc with
        | none => rw [hpk] at hp; cases hp
        | some q =>
          rw [hpk] at hp
          obtain ⟨es, acc1⟩ := q
          simp only at hp
          cases hr : rebalance cf i s (f + 1) g h' es with
          | none => rw [hr] at hp; cases hp
          | some es2 =>
            rw [hr] at hp
            simp only at hp
            cases hm : mkNode cf i s (some x) g (h' + 1) false es2 with
            | none => rw [hm] at hp; cases hp
            | some w =>
              rw [hm] at hp
              simp only [Option.some.injEq, Prod.mk.injEq] at hp
              obtain ⟨rfl, _⟩ := hp
              obtain ⟨hhead, hkids⟩ := old_kids hobj hsh ⟨lo, hi, hg⟩
              have hne : live n.ks ≠ [] := by
                intro h0; rw [h0] at hhead; cases hhead
              obtain ⟨sops, hrt, hcv, hvk⟩ := planKids_spec f (live n.ks) ops acc es acc1
                (fun f' h => IH f' (by omega)) hne hpk hkids
              obtain ⟨hs, hk2, _⟩ := rebalance_spec hcf (f + 1) h' es es2 hr hvk
              obtain ⟨⟨F, dec, rfl⟩, hv⟩ := mkNode_inner hcf hm (fun e he => (hk2 e he).1)
                (fun e he => (hk2 e he).2)
              refine ⟨sops, ?_, hcv, hv⟩
              show ∃ ks' ks'', Routed (Plan h') (kids (view (h' + 1) s x))
                  (PeProof.Abs.route (kids (view (h' + 1) s x)) sops) ks' ∧ Sett h' ks' ks'' ∧
                  (∀ e ∈ ks'', e.2 ≠ []) ∧ kids (absV s (h' + 1) _) = renameHead 0 ks''
              rw [view_succ hobj]
              refine ⟨absK s h' es, absK s h' es2, hrt, hs, ?_, ?_⟩
              · intro e he
                obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
                exact absV_ne (hk2 e' he').1 (hk2 e' he').2
              · show absK s h' (renameHead 0 es2) = _
                exact absK_renameHead _ _ _

/-- **Plan is an instance of 026-24's `Plan`**: if `plan` gives v for key
node x of segment g at height h, shaped as PE's trees and sound for the
contract (`Good`), then x read as an abstract node (`view`) is planned
(`Plan`) into v read before any cut (`absV`), by operations `sops` whose
compare values are those the operations touch, in the order of their first
operation (`touched`), and v is one of the program's nodes (`VOk`). -/
theorem plan_inst (hcf : cf.Ok) {f : Nat} {x : NodeId} {g h : Nat} {ops : List Contract.Op}
    {acc : Acc} {v : VN} {acc' : Acc} {lo : Nat} {hi : Option Nat}
    (hp : plan cf i s f x g h ops acc = some (v, acc')) (hsh : Shaped cf s g h x)
    (hg : Good s x lo hi) :
    ∃ sops : List Abs.Op, Plan h (view h s x) sops (absV s h v) ∧
      sops.map Abs.Op.cv = touched g ops ∧ VOk cf s g h v :=
  plan_ok hcf f x g h ops acc v acc' lo hi hp hsh hg

/-- A new segment tree (`planTree` with no root yet): an empty leaf planned
(`Plan 0 []`) into the leaf that `applyGroups` and `mkNode` make. -/
theorem plan_new_inst (hcf : cf.Ok) {f g : Nat} {ops : List Contract.Op} {acc : Acc}
    {es : List (Nat × NodeId)} {acc' : Acc} {v : VN}
    (ha : applyGroups cf i s f g [] ((ops.map (segAt g)).eraseDups) ops acc = some (es, acc'))
    (hm : mkNode cf i s none g 0 false (es.map (fun e => (e.1, VN.old e.2))) = some v) :
    ∃ sops : List Abs.Op, Plan 0 [] sops (absV s 0 v) ∧ sops.map Abs.Op.cv = touched g ops ∧
      VOk cf s g 0 v := by
  obtain ⟨⟨F, dec, rfl⟩, hv⟩ := mkNode_leaf hcf hm (by
    intro e he
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp he
    exact ⟨q.2, rfl⟩)
  obtain ⟨hs1, hs2⟩ := applyGroups_spec f g _ _ ops acc es acc' ha List.Pairwise.nil
  refine ⟨finalOps (touched g ops) es, ?_, by rw [finalOps_cv], hv⟩
  have habs : absV s 0 (VN.node none g 0 false (es.map (fun e => (e.1, VN.old e.2))) F dec) = es := by
    show (es.map (fun e => (e.1, VN.old e.2))).map (fun e => (e.1, e.2.oid)) = es
    rw [List.map_map]
    conv_rhs => rw [← List.map_id es]
    apply List.map_congr_left
    intro e _
    rfl
  show absV s 0 _ = Abs.applyOps (finalOps (touched g ops) es) []
  rw [habs]
  exact (applyOps_finalOps _ _ _ List.Pairwise.nil hs1 hs2).symm

/-- Plan, then the root settled alone: the node of the tree before is
planned (`Plan`), and the planned root settles (`Root`) into what emit
writes. -/
theorem plan_settle (hcf : cf.Ok) {f f' : Nat} {x : NodeId} {g h : Nat} {ops : List Contract.Op}
    {acc : Acc} {v : VN} {acc' : Acc} {lo : Nat} {hi : Option Nat} {space : Bool} {v' : VN}
    (hp : plan cf i s f x g h ops acc = some (v, acc')) (hsh : Shaped cf s g h x)
    (hg : Good s x lo hi) (hs : settleRoot cf i s f' g v space = some (some v')) :
    ∃ (sops : List Abs.Op) (h' : Nat), Plan h (view h s x) sops (absV s h v) ∧
      sops.map Abs.Op.cv = touched g ops ∧ Root h (absV s h v) h' (fin s h' v') ∧
      RootOk cf s g h' v' := by
  obtain ⟨sops, hpl, hcv, hv⟩ := plan_inst hcf hp hsh hg
  obtain ⟨h', hR, hok⟩ := settle_root hcf f' g space h v v' (Or.inr hv) hs
  exact ⟨sops, h', hpl, hcv, hR, hok⟩

/-- A root that settles into no tree (`settleRoot` gives `some none`: a
segment's tree that is not the space root, left empty) holds nothing. -/
theorem settle_root_none (hcf : cf.Ok) : ∀ (f g : Nat) (space : Bool) (h : Nat) (v : VN),
    RootOk cf s g h v → settleRoot cf i s f g v space = some none → content h (absV s h v) = []
  | 0, _, _, _, _, _, hs => by simp [settleRoot] at hs
  | f + 1, g, space, h, v, hv, hs => by
    unfold settleRoot at hs
    cases v with
    | old y =>
      have hsh : Shaped cf s g h y := by
        rcases hv with ⟨y', hy, hsh⟩ | hv
        · cases hy; exact hsh
        · cases hv with
          | old hsh _ _ => exact hsh
      simp only at hs
      cases hgk : getKey s y with
      | none => rw [hgk] at hs; cases hs
      | some n =>
        rw [hgk] at hs
        simp only at hs
        have hobj := getKey_obj hgk
        split at hs
        · rename_i c z hl
          split at hs
          · cases hs
          · rename_i hleaf
            cases hsh with
            | leaf hobj' hleaf' _ _ _ =>
              rw [hobj] at hobj'
              obtain rfl : n = _ := by injection hobj' with h1; injection h1
              exact absurd hleaf' hleaf
            | @inner _ h'' _ n' hobj' _ _ _ _ _ hkids =>
              rw [hobj] at hobj'
              obtain rfl : n = n' := by injection hobj' with h1; injection h1
              have hz : Shaped cf s g h'' z := hkids c z (by rw [hl]; simp)
              have ih := settle_root_none hcf f g space h'' (.old z) (Or.inl ⟨z, rfl, hz⟩) hs
              show kidsContent h'' (kids (view (h'' + 1) s y)) = []
              rw [view_succ hobj, hl]
              simpa [kidsContent, absV_old] using ih
        · cases hs
    | node base g' hv' join es F dec =>
      have hvok : VOk cf s g h (.node base g' hv' join es F dec) := by
        rcases hv with ⟨y', hy, _⟩ | hv
        · cases hy
        · exact hv
      obtain ⟨hh1, hh2⟩ := hvok.ht
      subst hv' g'
      simp only at hs
      split at hs
      · rename_i hF
        have hes := es_nil_of_F hvok (List.isEmpty_iff.mp hF)
        subst hes
        cases h <;> rfl
      · split at hs
        · rename_i hF hone
          simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hone
          obtain ⟨hh, _⟩ := hone
          obtain ⟨h'', rfl⟩ : ∃ h'', h = h'' + 1 := ⟨h - 1, by omega⟩
          split at hs
          · rename_i c ch
            cases hvok with
            | inner hk _ _ _ _ =>
              have ih := settle_root_none hcf f g space h'' ch (Or.inr (hk (c, ch) (by simp))) hs
              show kidsContent h'' (absK s h'' [(c, ch)]) = []
              simpa [kidsContent, absK] using ih
          · cases hs
        · rename_i hF _
          split at hs
          · rename_i k
            split at hs
            · cases hm : mkNode cf i s none g (h + 1) false [(0, .node base g h join es F (.parts k))] with
              | none => rw [hm] at hs; cases hs
              | some r =>
                rw [hm] at hs
                simp only at hs
                have hne : (VN.node base g h join es F (.parts k)).isEmpty = false := by
                  simp only [VN.isEmpty]; simpa using hF
                obtain ⟨⟨F2, dec2, rfl⟩, hr⟩ := mkNode_inner hcf hm
                  (by intro e he; simp at he; subst he; exact hvok)
                  (by intro e he; simp at he; subst he; exact hne)
                have ih := settle_root_none hcf f g space (h + 1) _ (Or.inr hr) hs
                have : content (h + 1) (absV s (h + 1)
                    (VN.node none g (h + 1) false (renameHead 0 [(0, VN.node base g h join es F (.parts k))])
                      F2 dec2)) = content h (absV s h (.node base g h join es F (.parts k))) := by
                  show kidsContent h (absK s h [(0, _)]) = _
                  simp [kidsContent, absK]
                rw [← this]; exact ih
            · cases hs
          · cases hs

end Contract.PE
