/-
The writer's tree kept by a merge into one node (bergdb 024-22, `OpTreeOK`):
two siblings l and r under p, both reached, are replaced by a new node m1 with
their live klongs (`mergeList`: in an inner node the right one's first klong
gets r's compare value in p); p's klong of l names m1 and r's compare value is
deleted (`treeOK_mergeOneAfter`). And no node of a tree links to itself
(`TreeOK.no_self_link`).
-/
import SIS.Tree.WriterTreeRepoint

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- In a tree a node reached and not the root is linked from a reached node
other than itself. -/
theorem tReach_parent (L : NodeId → Option KNode) (t : Time) (r : NodeId) :
    ∀ x, TReach L t r x → x = r ∨ ∃ y c, TReach L t r y ∧ y ≠ x ∧ TLink L t y c x := by
  intro x hx
  induction hx with
  | root => exact Or.inl rfl
  | @link y c x hy hl ih =>
    by_cases hyx : y = x
    · subst hyx; exact ih
    · exact Or.inr ⟨y, c, hy, hyx, hl⟩

/-- No node of a tree links to itself. -/
theorem TreeOK.no_self_link {L : NodeId → Option KNode} {t : Time} {r : NodeId}
    (ht : TreeOK L t r) (x : NodeId) (c : Nat) (hx : TReach L t r x) : ¬ TLink L t x c x := by
  intro hl
  rcases tReach_parent L t r x hx with h | ⟨y, c', hy, hyx, hl'⟩
  · subst h; exact ht.rootFree x c hx hl
  · exact hyx (ht.oneLink y c' x c x hy hx hl' hl).1

theorem mem_renameHead_old (c : Nat) (l : List (Nat × NodeId)) (q : Nat × NodeId)
    (h : q ∈ renameHead c l) : (q.1 = c ∧ ∃ c0, l.head? = some (c0, q.2)) ∨ q ∈ l.tail := by
  cases l with
  | nil => simp [renameHead] at h
  | cons a rest =>
    rcases a with ⟨a1, a2⟩
    simp only [renameHead, List.mem_cons] at h
    rcases h with h | h
    · subst h; exact Or.inl ⟨rfl, a1, rfl⟩
    · exact Or.inr h

/-- A merged pair comes from the left node's live klongs, or the right one's,
renamed at its head in an inner node. -/
theorem mem_mergeList (inner : Bool) (cR : Nat) (lvL lvR : List (Nat × NodeId)) (c : Nat)
    (z : NodeId) (h : (c, z) ∈ mergeList inner cR lvL lvR) :
    (c, z) ∈ lvL ∨ (c, z) ∈ lvR.tail ∨ (∃ c0, lvR.head? = some (c0, z) ∧
      c = (if inner then cR else c0)) := by
  unfold mergeList at h
  rcases List.mem_append.mp h with h | h
  · exact Or.inl h
  · cases inner with
    | true =>
      simp only [↓reduceIte] at h
      rcases mem_renameHead_old cR lvR (c, z) h with ⟨hc, c0, hh⟩ | ht
      · exact Or.inr (Or.inr ⟨c0, hh, by simpa using hc⟩)
      · exact Or.inr (Or.inl ht)
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      cases lvR with
      | nil => cases h
      | cons a rest =>
        rcases List.mem_cons.mp h with h | h
        · subst h; exact Or.inr (Or.inr ⟨c, rfl, by simp⟩)
        · exact Or.inr (Or.inl h)

/-- The tree after a merge into one node: siblings l and rr under p, named by
p's live klongs cL and cR, replaced by the new node m1 whose live klongs are
among their merged klongs; p's live klongs after are cL naming m1 and its others
but cL's and cR's; nothing else changes but l and rr, which are left behind. -/
theorem treeOK_mergeOneAfter (N N' : NodeId → Option KNode) (t : Time) (r p l rr m1 : NodeId)
    (pn ln rn pn' mn : KNode) (inner : Bool) (cL cR : Nat)
    (hT : TreeOK N t r) (hp : TReach N t r p) (hpn : N p = some pn)
    (hl : (cL, l) ∈ pn.liveAt t) (hrr : (cR, rr) ∈ pn.liveAt t) (hc : cL ≠ cR)
    (hln : N l = some ln) (hrn : N rr = some rn)
    (hlt : ∀ s, Klong.time s ∈ ln.ks → s ≤ t) (hrt : ∀ s, Klong.time s ∈ rn.ks → s ≤ t)
    (hm1 : N m1 = none) (hm1f : ∀ u c, TReach N t r u → ¬ TLink N t u c m1)
    (hN'm1 : N' m1 = some mn)
    (hmn : ∀ c z, (c, z) ∈ mn.liveAt t → (c, z) ∈ mergeList inner cR ln.live rn.live)
    (hN'p : N' p = some pn')
    (hpn' : ∀ c z, (c, z) ∈ pn'.liveAt t →
      (c = cL ∧ z = m1) ∨ ((c, z) ∈ pn.liveAt t ∧ c ≠ cL ∧ c ≠ cR))
    (hother : ∀ y, y ≠ p → y ≠ l → y ≠ rr → y ≠ m1 → N' y = N y) :
    TreeOK N' t r := by
  have hlink_l : TLink N t p cL l := ⟨pn, hpn, hl⟩
  have hlink_r : TLink N t p cR rr := ⟨pn, hpn, hrr⟩
  have hlR : TReach N t r l := TReach.link hp hlink_l
  have hrR : TReach N t r rr := TReach.link hp hlink_r
  have hpl : p ≠ l := fun h => hT.no_self_link p cL hp (by rw [← h] at hlink_l; exact hlink_l)
  have hpr : p ≠ rr := fun h => hT.no_self_link p cR hp (by rw [← h] at hlink_r; exact hlink_r)
  have hlr : l ≠ rr := fun h => hc (hT.oneLink p cL p cR l hp hp hlink_l (by rw [h]; exact hlink_r)).2
  have hm1R : ¬ TReach N t r m1 := not_reach_fresh N t r m1 hT hm1 hm1f
  have hne : ∀ x m, N x = some m → x ≠ m1 := fun x m hx he => by rw [he, hm1] at hx; cases hx
  have hpm := hne p pn hpn
  have hlm := hne l ln hln
  have hrm := hne rr rn hrn
  -- who names l and rr
  have hnames : ∀ u c z, TReach N t r u → TLink N t u c z → (z = l ∨ z = rr) → u = p := by
    intro u c z hu hlk hz
    rcases hz with hz | hz
    · rw [hz] at hlk; exact (hT.oneLink u c p cL l hu hp hlk hlink_l).1
    · rw [hz] at hlk; exact (hT.oneLink u c p cR rr hu hp hlk hlink_r).1
  have hlL : ln.liveAt t = ln.live := KNode.liveAt_of_times ln t hlt
  have hrL : rn.liveAt t = rn.live := KNode.liveAt_of_times rn t hrt
  -- the head of the right node's live klongs
  have hrnodup := KNode.live_keys_nodup rn
  let c0R : Option Nat := rn.live.head?.map (·.1)
  apply treeOK_transfer_gone N N' t r r (fun z => z = m1) (fun z => z = l ∨ z = rr)
    (fun u c => if u = l then (m1, c) else if u = rr then
      (m1, if inner = true ∧ some c = c0R then cR else c) else (u, c)) hT
  · intro z hz; rw [hz]; exact hm1R
  · refine Or.inl ⟨rfl, fun h => ?_⟩
    rcases h with h | h
    · exact hT.rootFree p cL hp (by rw [h]; exact hlink_l)
    · exact hT.rootFree p cR hp (by rw [h]; exact hlink_r)
  · intro u c z hu hug hlk
    obtain ⟨m, hm, hcm⟩ := hlk
    have hul : u ≠ l := fun h => hug (Or.inl h)
    have hur : u ≠ rr := fun h => hug (Or.inr h)
    have hold : ∀ y0 c0, TReach N t r y0 → TLink N t y0 c0 z → y0 ≠ p → ¬ (z = l ∨ z = rr) :=
      fun y0 c0 hy0 hl0 hy0p hz => hy0p (hnames y0 c0 z hy0 hl0 hz)
    by_cases hum : u = m1
    · rw [hum, hN'm1] at hm
      simp only [Option.some.injEq] at hm
      subst hm
      have hmem := hmn c z hcm
      rcases mem_mergeList inner cR ln.live rn.live c z hmem with h | h | ⟨c0, hh, hcc⟩
      · have hlk : TLink N t l c z := ⟨ln, hln, by rw [hlL]; exact h⟩
        exact Or.inr ⟨hold l c hlR hlk (Ne.symm hpl), l, c, hlR, hlk, by simp [hum]⟩
      · have hmem' : (c, z) ∈ rn.live := List.mem_of_mem_tail h
        have hlk : TLink N t rr c z := ⟨rn, hrn, by rw [hrL]; exact hmem'⟩
        refine Or.inr ⟨hold rr c hrR hlk (Ne.symm hpr), rr, c, hrR, hlk, ?_⟩
        have hnh : ¬ (some c = c0R) := by
          intro hh
          cases hlv : rn.live with
          | nil => rw [hlv] at h; cases h
          | cons a rest =>
            rw [hlv] at h hrnodup
            simp only [c0R, hlv, List.head?_cons, Option.map_some, Option.some.injEq] at hh
            simp only [List.tail_cons] at h
            simp only [List.map_cons, List.nodup_cons] at hrnodup
            exact hrnodup.1 (by rw [← hh]; exact List.mem_map.mpr ⟨(c, z), h, rfl⟩)
        simp [hum, Ne.symm hlr, hnh]
      · have hmem' : (c0, z) ∈ rn.live := List.mem_of_mem_head? hh
        have hlk : TLink N t rr c0 z := ⟨rn, hrn, by rw [hrL]; exact hmem'⟩
        refine Or.inr ⟨hold rr c0 hrR hlk (Ne.symm hpr), rr, c0, hrR, hlk, ?_⟩
        have hc0 : some c0 = c0R := by simp [c0R, hh]
        cases inner with
        | true => simp [hum, Ne.symm hlr, hc0, hcc]
        | false => simp [hum, Ne.symm hlr, hcc]
    · by_cases hup : u = p
      · rw [hup, hN'p] at hm
        simp only [Option.some.injEq] at hm
        subst hm
        rcases hpn' c z hcm with ⟨_, hz⟩ | ⟨hmem, hcl, hcr⟩
        · exact Or.inl hz
        · have hlk : TLink N t p c z := ⟨pn, hpn, hmem⟩
          refine Or.inr ⟨fun hz => ?_, p, c, hp, hlk, by simp [hpl, hpr, hup]⟩
          rcases hz with hz | hz
          · rw [hz] at hlk; exact hcl (hT.oneLink p c p cL l hp hp hlk hlink_l).2
          · rw [hz] at hlk; exact hcr (hT.oneLink p c p cR rr hp hp hlk hlink_r).2
      · rw [hother u hup hul hur hum] at hm
        have huR : TReach N t r u := by
          rcases hu with h | h
          · exact h
          · exact absurd h hum
        have hlk : TLink N t u c z := ⟨m, hm, hcm⟩
        exact Or.inr ⟨hold u c huR hlk hup, u, c, huR, hlk, by simp [hul, hur]⟩
  · intro u c u' c' z hu hug hu' hug' hz hl1 hl2
    rw [hz] at hl1 hl2
    have hone : ∀ x d, (TReach N t r x ∨ x = m1) → ¬ (x = l ∨ x = rr) →
        TLink N' t x d m1 → x = p ∧ d = cL := by
      intro x d hx hxg hlk
      obtain ⟨m, hm, hcm⟩ := hlk
      by_cases hxm : x = m1
      · rw [hxm, hN'm1] at hm
        simp only [Option.some.injEq] at hm
        subst hm
        rcases mem_mergeList inner cR ln.live rn.live d m1 (hmn d m1 hcm) with h | h | ⟨c0, hh, _⟩
        · exact absurd ⟨ln, hln, by rw [hlL]; exact h⟩ (hm1f l d hlR)
        · exact absurd ⟨rn, hrn, by rw [hrL]; exact List.mem_of_mem_tail h⟩ (hm1f rr d hrR)
        · exact absurd ⟨rn, hrn, by rw [hrL]; exact List.mem_of_mem_head? hh⟩ (hm1f rr c0 hrR)
      · by_cases hxp : x = p
        · rw [hxp, hN'p] at hm
          simp only [Option.some.injEq] at hm
          subst hm
          rcases hpn' d m1 hcm with ⟨hd, _⟩ | ⟨hmem, _, _⟩
          · exact ⟨hxp, hd⟩
          · exact absurd ⟨pn, hpn, hmem⟩ (hm1f p d hp)
        · have hxl : x ≠ l := fun h => hxg (Or.inl h)
          have hxr : x ≠ rr := fun h => hxg (Or.inr h)
          rw [hother x hxp hxl hxr hxm] at hm
          have hxR : TReach N t r x := by
            rcases hx with h | h
            · exact h
            · exact absurd h hxm
          exact absurd ⟨m, hm, hcm⟩ (hm1f x d hxR)
    obtain ⟨h1, h2⟩ := hone u c hu hug hl1
    obtain ⟨h3, h4⟩ := hone u' c' hu' hug' hl2
    exact ⟨h1.trans h3.symm, h2.trans h4.symm⟩
  · intro z hz hzg
    rw [hz] at hzg
    rcases hzg with h | h
    · exact hlm h.symm
    · exact hrm h.symm
  · by_cases hrp : r = p
    · rw [hrp, hN'p]; exact ⟨_, rfl⟩
    · have hrl : r ≠ l := fun h => hT.rootFree p cL hp (by rw [h]; exact hlink_l)
      have hrr' : r ≠ rr := fun h => hT.rootFree p cR hp (by rw [h]; exact hlink_r)
      obtain ⟨rm, hrm⟩ := hT.rootKey
      have hrm1 := hne r rm hrm
      rw [hother r hrp hrl hrr' hrm1]
      exact ⟨rm, hrm⟩

/-! ## Root collapse -/

/-- The space root replaced by its one child (root collapse at the space root):
the tree from the child, whatever becomes of the old root. -/
theorem treeOK_collapseSpace (L L' : NodeId → Option KNode) (t : Time) (r y : NodeId) (c : Nat)
    (ht : TreeOK L t r) (hl : TLink L t r c y) (hy : ∃ n, L y = some n)
    (hother : ∀ x, x ≠ r → L' x = L x) : TreeOK L' t y := by
  have hty := treeOK_child L t r y c ht hl hy
  have hyr : TReach L t r y := TReach.link TReach.root hl
  have hsub := tReach_trans L t r y hyr
  -- the old root is not reached from y
  have hnr : ∀ x, TReach L t y x → x ≠ r := by
    intro x hx hxr
    rw [hxr] at hx
    cases hx with
    | root => exact ht.rootFree r c TReach.root hl
    | link hz hl' => exact ht.rootFree _ _ (hsub _ hz) hl'
  exact treeOK_of_agree L L' t y hty (fun x hx => hother x (hnr x hx))

/-- A segment root replaced by its one child: the segment leaf's klong k naming
the root names the child; the root is left behind. -/
theorem treeOK_collapseSegment (L L' : NodeId → Option KNode) (t : Time) (r0 lf rt y : NodeId)
    (k c : Nat) (ln ln' rn : KNode) (ht : TreeOK L t r0)
    (hlf : TReach L t r0 lf) (hln : L lf = some ln) (hk : (k, rt) ∈ ln.liveAt t)
    (hrn : L rt = some rn) (hy : (c, y) ∈ rn.liveAt t)
    (hln' : L' lf = some ln')
    (hlinks : ∀ c' z, (c', z) ∈ ln'.liveAt t → (c' = k ∧ z = y) ∨ ((c', z) ∈ ln.liveAt t ∧ c' ≠ k))
    (hother : ∀ x, x ≠ lf → x ≠ rt → L' x = L x) : TreeOK L' t r0 := by
  have hlk : TLink L t lf k rt := ⟨ln, hln, hk⟩
  have hrtR : TReach L t r0 rt := TReach.link hlf hlk
  have hry : TLink L t rt c y := ⟨rn, hrn, hy⟩
  have hlfrt : lf ≠ rt := fun h => ht.no_self_link lf k hlf (by rw [← h] at hlk; exact hlk)
  have hrty : rt ≠ y := fun h => ht.no_self_link rt c hrtR (by rw [← h] at hry; exact hry)
  have hnamert : ∀ u c', TReach L t r0 u → TLink L t u c' rt → u = lf ∧ c' = k :=
    fun u c' hu hl' => ht.oneLink u c' lf k rt hu hlf hl' hlk
  apply treeOK_transfer_gone L L' t r0 r0 (fun _ => False) (fun z => z = rt)
    (fun u c' => if u = rt ∧ c' = c then (lf, k) else (u, c')) ht (fun _ h => h.elim)
  · refine Or.inl ⟨rfl, fun h => ht.rootFree lf k hlf (by rw [h]; exact hlk)⟩
  · intro u c' z hu hug hl'
    have huR : TReach L t r0 u := by
      rcases hu with h | h
      · exact h
      · exact h.elim
    obtain ⟨m, hm, hcm⟩ := hl'
    by_cases hul : u = lf
    · rw [hul, hln'] at hm
      simp only [Option.some.injEq] at hm
      subst hm
      rcases hlinks c' z hcm with ⟨hck, hz⟩ | ⟨hmem, hck⟩
      · refine Or.inr ⟨by rw [hz]; exact Ne.symm hrty, rt, c, hrtR, by rw [hz]; exact hry, ?_⟩
        simp [hul, hck]
      · have hl0 : TLink L t lf c' z := ⟨ln, hln, hmem⟩
        refine Or.inr ⟨fun hzr => ?_, lf, c', hlf, hl0, ?_⟩
        · rw [hzr] at hl0
          exact hck (hnamert lf c' hlf hl0).2
        · simp [hul, hlfrt]
    · rw [hother u hul hug] at hm
      have hl0 : TLink L t u c' z := ⟨m, hm, hcm⟩
      refine Or.inr ⟨fun hzr => ?_, u, c', huR, hl0, ?_⟩
      · rw [hzr] at hl0
        exact hul (hnamert u c' huR hl0).1
      · simp [hug]
  · intro _ _ _ _ z _ _ _ _ hz
    exact hz.elim
  · intro _ h; exact h.elim
  · by_cases hr : r0 = lf
    · rw [hr, hln']; exact ⟨_, rfl⟩
    · have hrrt : r0 ≠ rt := fun h => ht.rootFree lf k hlf (by rw [h]; exact hlk)
      rw [hother r0 hr hrrt]; exact ht.rootKey

end SIS.Tree
