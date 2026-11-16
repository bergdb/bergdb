/-
The hole at the delete's changed node (bergdb 030-01, steps 5 and 6; the stall
point R1 at the leaf's change): after a delete's bitmap into its leaf L, the
merges' descent at L's cached segment and height finds L (`holeAtW_leaf`), so
the merges' loop starts at the hole.

The descent reads by segments: `SegRd` asks of the reads that a node has a
segment and a height, is a leaf exactly at height 0, and names nodes of its
segment if it is inner and of the next by a long segment if it is a leaf; the
books and the kinds' walk give it (`segRd_of`). Along the key's descent the
segment grows by one at each segment leaf (`dsrFold_seg`), so L's cached segment
is the space root's plus the number of the key's segments above L's tree. A
successful descent has a segment below the key's length, so that number is L's
segment: the space root's segment is not needed. The descent then follows the
key's search, which the delete's walk made (`dsrFold_of_segRootR`,
`lteP_of_eqVisits`), and at height 0 it stops at the leaf (`dhP_zero_of_lteP`).
-/
import SIS.Tree.LiveHolePilot

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## The reads' segments -/

/-- What the descents need of the reads: a node read has a segment and a height,
is a leaf exactly at height 0, and its klongs name nodes of its segment if it is
inner, of the next segment by a long segment if it is a leaf. -/
def SegRd (Rd : NodeId → Option KNode) (Gh : NodeId → Option (Nat × Nat)) : Prop :=
  ∀ y n, Rd y = some n → ∃ g h, Gh y = some (g, h) ∧ n.leaf = (h == 0) ∧
    ∀ c z g' h', Klong.key c z ∈ n.ks → Gh z = some (g', h') →
      (h ≠ 0 → g' = g) ∧ (h = 0 → segLen c = 7 → g' = g + 1)

/-- A node that the kinds give segment g has segment g in the writer's reads. -/
theorem rdG_seg_of_isKeySeg {K : KindOracle} {B : NodeId} {c : Ctx} {v : W} (hb : Book B c v)
    (hvk : ViewKinds K B c) {z : NodeId} {g g' h' : Nat} (hz : IsKeySeg K v z g)
    (hG : rdG c v z = some (g', h')) : g' = g := by
  cases hl : v.nodes.lookup z with
  | some m =>
    rw [rdG_of_lookup c v z m hl] at hG
    have hmem : (z, g', h') ∈ v.gh := bk_mem_of_lookup _ _ _ hG
    rcases hz with ⟨h1, hm1⟩ | hK
    · have := lookup_of_mem_nodup _ hb.nodup z (g, h1) hm1
      rw [this] at hG
      exact (Prod.mk.inj (Option.some.inj hG)).1.symm
    · rcases hb.tag z g' h' hmem with ⟨nd, hv, hd, hlv, hg, _⟩ | ⟨hBz, _⟩
      · exact hvk.seg z g' g (by rw [hg]; exact hvk.node z nd hv hd hlv) hK
      · have := hvk.old z g hK
        omega
  | none =>
    cases hv : c.view z with
    | none => simp [rdG, hl, hv] at hG
    | some nd =>
      by_cases hkind : (nd.isData || decide (c.p.keyMax < nd.level)) = true
      · simp [rdG, hl, hv, hkind] at hG
      · simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hkind
        have hd : nd.isData = false := by simpa using hkind.1
        have hlv : nd.level ≤ c.p.keyMax := by have := hkind.2; omega
        have hG' : rdG c v z = some (c.p.segOf nd.level, c.p.heightOf nd.level) := by
          simp [rdG, hl, hv, hd, hkind.2]
        rw [hG'] at hG
        have e := (Prod.mk.inj (Option.some.inj hG)).1
        rw [← e]
        rcases hz with ⟨h1, hm1⟩ | hK
        · obtain ⟨m, hm⟩ := kd_lookup_of_tag hb hm1
          rw [hl] at hm
          cases hm
        · exact hvk.seg z _ g (hvk.node z nd hv hd hlv) hK

/-- The books and the kinds' walk give the reads' segments. -/
theorem segRd_of (K : KindOracle) (B : NodeId) (c : Ctx) (v : W) (hb : Book B c v) (hk : KdInv K B v)
    (hvk : ViewKinds K B c) : SegRd (rdN c v) (rdG c v) := by
  intro y n hn
  cases hl : v.nodes.lookup y with
  | some m =>
    rw [rdN_of_lookup c v y m hl] at hn
    cases hn
    obtain ⟨g, h, hm⟩ := kd_tag_of_lookup hb hl
    have hG : rdG c v y = some (g, h) := by
      rw [rdG_of_lookup c v y _ hl]
      exact lookup_of_mem_nodup _ hb.nodup y (g, h) hm
    refine ⟨g, h, hG, kd_leaf hb hl hm, fun c' z g' h' hkz hGz => ?_⟩
    have hkk := kd_cache_node hk hl hm c' z hkz
    exact ⟨fun h0 => rdG_seg_of_isKeySeg hb hvk (hkk.1 h0) hGz,
      fun h0 h7 => rdG_seg_of_isKeySeg hb hvk ((hkk.2 h0).1 h7) hGz⟩
  | none =>
    cases hv : c.view y with
    | none => simp [rdN, hl, hv] at hn
    | some nd =>
      by_cases hkind : (nd.isData || decide (c.p.keyMax < nd.level)) = true
      · simp [rdN, hl, hv, hkind] at hn
      · simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hkind
        have hd : nd.isData = false := by simpa using hkind.1
        have hlv : nd.level ≤ c.p.keyMax := by have := hkind.2; omega
        have hn' : rdN c v y = some { leaf := c.p.heightOf nd.level == 0, ks := klongsOf nd.hist } := by
          simp [rdN, hl, hv, hd, hkind.2]
        rw [hn'] at hn
        cases hn
        refine ⟨c.p.segOf nd.level, c.p.heightOf nd.level, by simp [rdG, hl, hv, hd, hkind.2], rfl, ?_⟩
        intro c' z g' h' hkz hGz
        have hkl := hvk.klongs y nd hv hd hlv c' z hkz
        exact ⟨fun h0 => rdG_seg_of_isKeySeg hb hvk (Or.inr (hkl.1 h0)) hGz,
          fun h0 h7 => rdG_seg_of_isKeySeg hb hvk (Or.inr ((hkl.2 h0).1 h7)) hGz⟩

/-! ## The segments along the descents -/

/-- `descendLte` stays in its segment. -/
theorem lteP_seg (Rd : NodeId → Option KNode) (Gh : NodeId → Option (Nat × Nat)) (hs : SegRd Rd Gh)
    (t : Time) (cv : Nat) : ∀ f x a ext g, lteP Rd t cv f x = some (a, ext) →
      (∀ n, Rd x = some n → ∃ h, Gh x = some (g, h)) → ∃ h, Gh a = some (g, h) := by
  intro f
  induction f with
  | zero => intro x a ext g h; simp [lteP] at h
  | succ f ih =>
    intro x a ext g h hx
    obtain ⟨n, hRx, ⟨_, rfl, rfl⟩ | ⟨hnl, fd, ext', hfd, hr, rfl⟩⟩ := lteP_succ_some Rd t cv f x a ext h
    · exact hx n hRx
    · obtain ⟨hx0, hGx⟩ := hx n hRx
      obtain ⟨g0, h0, hG0, hl0, hk⟩ := hs x n hRx
      have e := Prod.mk.inj (Option.some.inj (hGx.symm.trans hG0))
      have hh0 : h0 ≠ 0 := by
        intro he
        rw [he] at hl0
        rw [hnl] at hl0
        cases hl0
      refine ih fd.y a ext' g hr (fun m hm => ?_)
      obtain ⟨g1, h1, hG1, _⟩ := hs fd.y m hm
      have hmem : Klong.key fd.c fd.y ∈ n.ks :=
        KNode.liveAt_key_mem n t fd.c fd.y (KNode.searchLte_mem n t _ fd hfd)
      have := (hk fd.c fd.y g1 h1 hmem hG1).1 hh0
      rw [this, ← e.1] at hG1
      exact ⟨h1, hG1⟩

/-- `descendToSegmentRoot`'s loop goes one segment down at each of its long
segments. -/
theorem dsrFold_seg (Rd : NodeId → Option KNode) (Gh : NodeId → Option (Nat × Nat)) (hs : SegRd Rd Gh)
    (t : Time) (fuel : Nat) : ∀ (cvs : List Nat) (x : NodeId) (ps : List (Option Nat × NodeId))
      (r : NodeId) (P : List (Option Nat × NodeId)) (g : Nat), (∀ c ∈ cvs, segLen c = 7) →
      cvs.foldl (dsrStep Rd t fuel) (some (x, ps)) = some (r, P) →
      (∀ n, Rd x = some n → ∃ h, Gh x = some (g, h)) →
      ∀ m, Rd r = some m → ∃ h, Gh r = some (g + cvs.length, h) := by
  intro cvs
  induction cvs with
  | nil =>
    intro x ps r P g _ h hx m hm
    simp only [List.foldl, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    simpa using hx m hm
  | cons cv rest ih =>
    intro x ps r P g hcvs h hx m hm
    simp only [List.foldl] at h
    cases hst : dsrStep Rd t fuel (some (x, ps)) cv with
    | none => rw [hst, dsrFold_none] at h; cases h
    | some acc =>
      rw [hst] at h
      obtain ⟨leaf, ext, n, fd, hl, hRl, hfd, rfl⟩ := dsrStep_some Rd t fuel x ps cv acc hst
      obtain ⟨⟨n0, hRl0, hn0l⟩, _⟩ := lteP_leaf Rd t cv fuel x leaf ext hl
      rw [hRl] at hRl0
      cases hRl0
      obtain ⟨hl1, hGl⟩ := lteP_seg Rd Gh hs t cv fuel x leaf ext g hl hx
      obtain ⟨g2, h2, hG2, hl2, hk⟩ := hs leaf n hRl
      have e := Prod.mk.inj (Option.some.inj (hGl.symm.trans hG2))
      have hh2 : h2 = 0 := by
        rw [hn0l] at hl2
        simpa using hl2.symm
      have hc : fd.c = cv := KNode.searchEq_c n t cv fd hfd
      have hmem : Klong.key fd.c fd.y ∈ n.ks := kd_searchEq_mem n t cv fd hfd
      have hres := ih fd.y _ r P (g + 1) (fun c hc' => hcvs c (List.mem_cons_of_mem cv hc')) h
        (fun m1 hm1 => by
          obtain ⟨g1, h1, hG1, _⟩ := hs fd.y m1 hm1
          have := (hk fd.c fd.y g1 h1 hmem hG1).2 hh2 (by rw [hc]; exact hcvs cv List.mem_cons_self)
          rw [this, ← e.1] at hG1
          exact ⟨h1, hG1⟩) m hm
      obtain ⟨h3, hG3⟩ := hres
      refine ⟨h3, ?_⟩
      rw [hG3]
      simp only [List.length_cons, Option.some.injEq, Prod.mk.injEq, and_true]
      omega

/-! ## The descents follow the key's search -/

/-- The search of a segment tree, the reads agreeing with N on its nodes but its
leaf L, where they read a leaf: `descendLte` ends at L. -/
theorem lteP_of_eqVisits (N Rd : NodeId → Option KNode) (t : Time) (cv : Nat) (L : NodeId)
    (hRL : ∃ n', Rd L = some n' ∧ n'.leaf = true) :
    ∀ f x, (L, cv) ∈ eqVisits N t cv f x →
      (∀ q ∈ eqVisits N t cv f x, ∀ m, N q.1 = some m → q.1 ≠ L → Rd q.1 = some m) →
      ∃ ext, lteP Rd t cv f x = some (L, ext) := by
  intro f
  induction f with
  | zero => intro x h; simp [eqVisits] at h
  | succ f ih =>
    intro x h hag
    by_cases hx : x = L
    · rw [hx]
      obtain ⟨n', hn', hl'⟩ := hRL
      exact ⟨[], by simp [lteP, hn', hl']⟩
    · have hag' := hag
      simp only [eqVisits, List.mem_cons] at h hag'
      rcases h with h | h
      · exact absurd (Prod.mk.inj h).1.symm hx
      · cases hN : N x with
        | none => simp [hN] at h
        | some m =>
          have hRx := hag' (x, cv) (Or.inl rfl) m hN hx
          cases hml : m.leaf with
          | true => simp [hN, hml] at h
          | false =>
            cases hfd : m.searchLte t cv with
            | none => simp [hN, hml, hfd] at h
            | some fd =>
              simp only [hN, hml, hfd, Bool.false_eq_true, ↓reduceIte] at h hag'
              obtain ⟨ext, he⟩ := ih fd.y h (fun q hq => hag' q (Or.inr hq))
              exact ⟨(some fd.c, fd.y) :: ext, by simp [lteP, hRx, hml, hfd, he]⟩

/-- `getEqR` as `descendLte` and the leaf's search, the reads agreeing with N at
the nodes it visits (`AgreeAt`). -/
theorem lteP_of_getEqR (N Rd : NodeId → Option KNode) (t : Time) (cv : Nat) :
    ∀ f x y, getEqR N t cv f x = some y → (∀ q ∈ eqVisits N t cv f x, AgreeAt N Rd t q.1 q.2) →
      ∃ leaf ext n fd, lteP Rd t cv f x = some (leaf, ext) ∧
        Rd leaf = some n ∧ n.searchEq t cv = some fd ∧ fd.y = y := by
  intro f
  induction f with
  | zero => intro x y h; simp [getEqR] at h
  | succ f ih =>
    intro x y h hag
    have hax := hag (x, cv) (by simp [eqVisits])
    simp only [getEqR] at h
    cases hN : N x with
    | none => simp [hN] at h
    | some m =>
      cases hml : m.leaf with
      | true =>
        simp only [hN, hml, ↓reduceIte, Option.map_eq_some_iff] at h
        obtain ⟨fd, hfd, hy⟩ := h
        rcases hax with hax | ⟨n1, n2, h1, h2, _, hl2, hs⟩
        · have hRx : Rd x = some m := by rw [← hax, hN]
          exact ⟨x, [], m, fd, by simp [lteP, hRx, hml], hRx, hfd, hy⟩
        · rw [hN] at h1
          cases h1
          rw [hfd] at hs
          simp only [Option.map_some] at hs
          obtain ⟨fd2, hfd2, hy2⟩ := Option.map_eq_some_iff.mp hs.symm
          exact ⟨x, [], n2, fd2, by simp [lteP, h2, hl2], h2, hfd2, by rw [hy2, hy]⟩
      | false =>
        have hRx : Rd x = some m := by
          rcases hax with hax | ⟨n1, n2, h1, _, hl1, _⟩
          · rw [← hax, hN]
          · rw [hN] at h1; cases h1; rw [hml] at hl1; cases hl1
        cases hfd : m.searchLte t cv with
        | none => simp [hN, hml, hfd] at h
        | some fd =>
          simp only [hN, hml, hfd, Bool.false_eq_true, ↓reduceIte] at h
          have hag2 : ∀ q ∈ eqVisits N t cv f fd.y, AgreeAt N Rd t q.1 q.2 := by
            intro q hq
            apply hag q
            simp only [eqVisits, List.mem_cons, hN, hml, hfd, Bool.false_eq_true, ↓reduceIte]
            exact Or.inr hq
          obtain ⟨leaf, ext, n, fd', he, hRl, hfd', hy⟩ := ih fd.y y h hag2
          exact ⟨leaf, (some fd.c, fd.y) :: ext, n, fd', by simp [lteP, hRx, hml, hfd, he], hRl, hfd', hy⟩

/-- `descendToSegmentRoot`'s loop follows `segRootR`, the reads agreeing with N
at the nodes that the key's reading visits in its first segments. -/
theorem dsrFold_of_segRootR (N Rd : NodeId → Option KNode) (t : Time) (fuel : Nat) (cv : Nat) :
    ∀ (pre : List Nat) (x : NodeId) (ps : List (Option Nat × NodeId)) (rk : NodeId),
      (∀ q ∈ fromVisits N t fuel (pre ++ [cv]) x, q.2 ≠ cv → AgreeAt N Rd t q.1 q.2) → cv ∉ pre →
      segRootR N t fuel pre x = some rk →
      ∃ P, pre.foldl (dsrStep Rd t fuel) (some (x, ps)) = some (rk, P) := by
  intro pre
  induction pre with
  | nil =>
    intro x ps rk _ _ h
    simp only [segRootR, Option.some.injEq] at h
    subst h
    exact ⟨ps, rfl⟩
  | cons c rest ih =>
    intro x ps rk hag hcv h
    have hc : c ≠ cv := fun h' => hcv (by simp [h'])
    have hne : rest ++ [cv] ≠ [] := by simp
    obtain ⟨d, rest', he⟩ : ∃ d rest', rest ++ [cv] = d :: rest' := by
      cases h' : rest ++ [cv] with
      | nil => exact absurd h' hne
      | cons d rest' => exact ⟨d, rest', rfl⟩
    have hvis : ∀ q ∈ fromVisits N t fuel (c :: d :: rest') x, q.2 ≠ cv → AgreeAt N Rd t q.1 q.2 :=
      fun q hq => hag q (by rw [List.cons_append, he]; exact hq)
    simp only [fromVisits] at hvis
    have h1 : ∀ q ∈ eqVisits N t c fuel x, AgreeAt N Rd t q.1 q.2 := by
      intro q hq
      apply hvis q (List.mem_append_left _ hq)
      have := fromVisits_cv_mem N t fuel [c] x q (by simpa [fromVisits] using hq)
      simp at this
      rw [this]; exact hc
    simp only [segRootR] at h
    cases hg : getEqR N t c fuel x with
    | none => rw [hg] at h; cases h
    | some y =>
      rw [hg] at h
      simp only at h
      split at h
      · obtain ⟨leaf, ext, n, fd, hl, hRl, hfd, hy⟩ := lteP_of_getEqR N Rd t c fuel x y hg h1
        have hst : dsrStep Rd t fuel (some (x, ps)) c = some (y, ps ++ ext ++ [(some fd.c, fd.y)]) := by
          simp [dsrStep, hl, hRl, hfd, hy]
        simp only [List.foldl]
        rw [hst]
        refine ih y _ rk ?_ (fun h' => hcv (List.mem_cons_of_mem c h')) h
        intro q hq hq2
        apply hvis q _ hq2
        apply List.mem_append_right
        rw [hg]
        simp only
        rw [← he]
        exact hq
      · cases h

/-! ## The key's reading stays on the walk's path -/

theorem PathFromLen.cons' {N : NodeId → Option KNode} {t : Time} {x y z : NodeId} {c k : Nat}
    (hl : TLink N t x c y) (h : PathFromLen N t y z k) : PathFromLen N t x z (k + 1) := by
  induction h with
  | refl => exact PathFromLen.link (PathFromLen.refl _) hl
  | link _ hl2 ih => exact PathFromLen.link ih hl2

theorem PathFromLen.trans' {N : NodeId → Option KNode} {t : Time} {x y : NodeId} {a : Nat}
    (h1 : PathFromLen N t x y a) : ∀ {z b}, PathFromLen N t y z b → PathFromLen N t x z (a + b) := by
  intro z b h2
  induction h2 with
  | refl => exact h1
  | link _ hl ih => exact PathFromLen.link ih hl

/-- The nodes that a segment tree's search visits lead to the leaf it ends at. -/
theorem eqVisits_reach_leaf (N : NodeId → Option KNode) (t : Time) (cv : Nat) (L : NodeId)
    (n : KNode) (hL : N L = some n) (hnl : n.leaf = true) :
    ∀ f x, (L, cv) ∈ eqVisits N t cv f x → ∀ q ∈ eqVisits N t cv f x, ∃ k, PathFromLen N t q.1 L k := by
  intro f
  induction f with
  | zero => intro x h; simp [eqVisits] at h
  | succ f ih =>
    intro x h q hq
    by_cases hx : x = L
    · rw [hx] at hq
      simp only [eqVisits, List.mem_cons, hL, hnl, ↓reduceIte, List.not_mem_nil, or_false] at hq
      rw [hq]
      exact ⟨0, PathFromLen.refl _⟩
    · simp only [eqVisits, List.mem_cons] at h hq
      rcases h with h | h
      · exact absurd (Prod.mk.inj h).1.symm hx
      · cases hN : N x with
        | none => simp [hN] at h
        | some m =>
          cases hml : m.leaf with
          | true => simp [hN, hml] at h
          | false =>
            cases hfd : m.searchLte t cv with
            | none => simp [hN, hml, hfd] at h
            | some fd =>
              simp only [hN, hml, hfd, Bool.false_eq_true, ↓reduceIte] at h hq
              rcases hq with rfl | hq
              · cases f with
                | zero => simp [eqVisits] at h
                | succ f' =>
                  obtain ⟨k, hk⟩ := ih fd.y h (fd.y, cv) (by simp [eqVisits])
                  exact ⟨k + 1, PathFromLen.cons' ⟨m, hN, KNode.searchLte_mem m t _ fd hfd⟩ hk⟩
              · exact ih fd.y h q hq

/-- The nodes that a key's reading visits lead to the leaf of its last segment. -/
theorem fromVisits_reach_leaf (N : NodeId → Option KNode) (t : Time) (fuel cv : Nat) (L : NodeId)
    (n : KNode) (hL : N L = some n) (hnl : n.leaf = true)
    (hwf : ∀ x m, N x = some m → klongsWf m.ks = true) :
    ∀ (pre : List Nat) (r rk : NodeId), segRootR N t fuel pre r = some rk →
      (L, cv) ∈ eqVisits N t cv fuel rk →
      ∀ q ∈ fromVisits N t fuel (pre ++ [cv]) r, ∃ k, PathFromLen N t q.1 L k := by
  intro pre
  induction pre with
  | nil =>
    intro r rk hrk hL' q hq
    simp only [segRootR, Option.some.injEq] at hrk
    subst hrk
    simp only [List.nil_append, fromVisits] at hq
    exact eqVisits_reach_leaf N t cv L n hL hnl fuel r hL' q hq
  | cons c rest ih =>
    intro r rk hrk hL' q hq
    have hne : rest ++ [cv] ≠ [] := by simp
    obtain ⟨d, rest', he⟩ : ∃ d rest', rest ++ [cv] = d :: rest' := by
      cases h' : rest ++ [cv] with
      | nil => exact absurd h' hne
      | cons d rest' => exact ⟨d, rest', rfl⟩
    simp only [segRootR] at hrk
    cases hg : getEqR N t c fuel r with
    | none => rw [hg] at hrk; cases hrk
    | some y =>
      rw [hg] at hrk
      simp only at hrk
      split at hrk
      · rw [List.cons_append, he] at hq
        simp only [fromVisits] at hq
        rw [hg] at hq
        simp only at hq
        have ihy := ih y rk hrk hL'
        rw [he] at ihy
        rcases List.mem_append.mp hq with hq | hq
        · -- q is in the first segment: it leads to the leaf, whose search gives y
          obtain ⟨L', n', hL'v, hL'n, hL'l, hs⟩ := getEqR_some_visit N t c fuel r y hg
          obtain ⟨k1, hk1⟩ := eqVisits_reach_leaf N t c L' n' hL'n hL'l fuel r hL'v q hq
          obtain ⟨fd, hfd, hy⟩ := Option.map_eq_some_iff.mp hs
          have hlk : TLink N t L' c y := by
            refine ⟨n', hL'n, ?_⟩
            have := KNode.searchEq_mem n' t c fd (hwf L' n' hL'n) hfd
            rw [hy] at this
            exact this
          have hfuel : 0 < fuel := by
            cases fuel with
            | zero => simp [eqVisits] at hL'v
            | succ f => omega
          obtain ⟨k2, hk2⟩ := ihy (y, d) (by
            obtain ⟨f', rfl⟩ : ∃ f', fuel = f' + 1 := ⟨fuel - 1, by omega⟩
            cases rest' with
            | nil => simp [fromVisits, eqVisits]
            | cons _ _ => simp [fromVisits, eqVisits])
          exact ⟨k1 + 1 + k2, PathFromLen.trans' (PathFromLen.link hk1 hlk) hk2⟩
        · exact ihy q hq
      · cases hrk

/-- A reached node that leads to a node of a path from the root is on that path. -/
theorem nodeAt_of_reach (N : NodeId → Option KNode) (t : Time) (r : NodeId) (hT : TreeOK N t r)
    (P : List (Option Nat × NodeId)) (hlf : LinkedFrom N t r P) :
    ∀ q z k, PathFromLen N t q z k → TReach N t r q → ∀ j, j ≤ P.length → z = nodeAt r P j →
      k ≤ j ∧ q = nodeAt r P (j - k) := by
  intro q z k h
  induction h with
  | refl => intro _ j _ hz; exact ⟨Nat.zero_le _, by rw [hz]; rfl⟩
  | @link y c z' k hk hl ih =>
    intro hq j hj hz
    obtain ⟨a, ha⟩ := TReach.pathLen hq
    have hyR : TReach N t r y := (PathLen.append ha hk).reach
    cases j with
    | zero =>
      exfalso
      have hz0 : z' = r := by rw [hz]; simp [nodeAt]
      rw [hz0] at hl
      exact hT.rootFree y c hyR hl
    | succ j =>
      obtain ⟨k', n', _, hn', hl'⟩ := LinkedFrom.get N t r P hlf j (by omega)
      have hpR : TReach N t r (nodeAt r P j) := (LinkedFrom.pathLen N t r P hlf j (by omega)).reach
      have he := (hT.oneLink y c (nodeAt r P j) k' z' hyR hpR hl (by rw [hz]; exact ⟨n', hn', hl'⟩)).1
      obtain ⟨h1, h2⟩ := ih hq j (by omega) he
      refine ⟨by omega, ?_⟩
      rw [h2]
      congr 1
      omega

/-- At height 0 the merges' descent is `descendLte`. -/
theorem dhP_zero_of_lteP (Rd : NodeId → Option KNode) (Gh : NodeId → Option (Nat × Nat))
    (hs : SegRd Rd Gh) (t : Time) (cv : Nat) :
    ∀ f x a ext, lteP Rd t cv f x = some (a, ext) → dhP Rd Gh t cv 0 f x = some ext := by
  intro f
  induction f with
  | zero => intro x a ext h; simp [lteP] at h
  | succ f ih =>
    intro x a ext h
    obtain ⟨n, hRx, ⟨hnl, _, hex⟩ | ⟨hnl, fd, ext', hfd, hr, rfl⟩⟩ := lteP_succ_some Rd t cv f x a ext h
    · obtain ⟨g, h0, hG, hl0, _⟩ := hs x n hRx
      have : h0 = 0 := by rw [hnl] at hl0; simpa using hl0.symm
      subst this
      rw [hex]
      simp [dhP, hRx, hG]
    · obtain ⟨g, h0, hG, hl0, _⟩ := hs x n hRx
      have hh0 : h0 ≠ 0 := by
        intro he
        rw [he, hnl] at hl0
        cases hl0
      have he := ih fd.y a ext' hr
      simp [dhP, hRx, hG, hh0, hnl, hfd, he]

/-! ## The hole at the leaf -/

theorem path_last_map (l : List (Option Nat × NodeId)) (y : NodeId)
    (h : (l.map (·.2)).getLast? = some y) : (l[l.length - 1]?).map (·.2) = some y := by
  rw [← List.getElem?_map]
  rw [List.getLast?_eq_getElem?, List.length_map] at h
  exact h

theorem getLast_map_append (P ext : List (Option Nat × NodeId)) (rk L : NodeId)
    (hP : (P.map (·.2)).getLast? = some rk) (he : (rk :: ext.map (·.2)).getLast? = some L) :
    ((P ++ ext).map (·.2)).getLast? = some L := by
  rw [List.map_append]
  cases ext with
  | nil =>
    simp only [List.map_nil, List.getLast?_singleton, Option.some.injEq] at he
    subst he
    simpa using hP
  | cons e ext' =>
    rw [List.getLast?_append]
    simp only [List.map_cons, List.getLast?_cons_cons] at he ⊢
    rw [he]
    rfl

/-- The hole at the leaf (bergdb 030-01, step 5; R1 at the leaf's change): at a
state whose reads have their segments, where the key's descent through its
first segments reaches rk and the search of its last segment's tree from rk
ends at L, the merges' descent at L's segment and height finds L. -/
theorem holeAtW_leaf (c : Ctx) (v : W) (pre : List Nat) (cv : Nat) (rk L : NodeId) (g0 h0 : Nat)
    (hs : SegRd (rdN c v) (rdG c v)) (hcvs : ∀ c' ∈ pre, segLen c' = 7)
    (hdsr : ∃ P, pre.foldl (dsrStep (rdN c v) c.i c.p.fuel)
      (some (v.top.rootKey, [(none, v.top.rootKey)])) = some (rk, P))
    (hlte : ∃ ext, lteP (rdN c v) c.i cv c.p.fuel rk = some (L, ext))
    (hgL : rdG c v L = some (g0, h0)) :
    HoleAtW (pre ++ [cv]) g0 h0 c v L := by
  intro d v' hrun
  obtain ⟨root', P0, cv', ext', hd1, hk, hdh, hpath, hdd, _⟩ :=
    writerWP_descendToHeight_rd (pre ++ [cv]) g0 h0 c v d v' hrun
  obtain ⟨P, hP⟩ := hdsr
  obtain ⟨ext, hext⟩ := hlte
  -- L's segment is the space root's plus pre's length
  obtain ⟨s, hroot⟩ : ∃ s, ∀ n, rdN c v v.top.rootKey = some n →
      ∃ h, rdG c v v.top.rootKey = some (s, h) := by
    cases hr : rdN c v v.top.rootKey with
    | none => exact ⟨0, fun n hn => by cases hn⟩
    | some n =>
      obtain ⟨g, h, hG, _⟩ := hs _ n hr
      exact ⟨g, fun n' _ => ⟨h, hG⟩⟩
  have hseg_rk := dsrFold_seg _ _ hs c.i c.p.fuel pre _ _ rk P s hcvs hP hroot
  have hseg_L := lteP_seg _ _ hs c.i cv c.p.fuel rk L ext (s + pre.length) hext hseg_rk
  obtain ⟨hL, hGL⟩ := hseg_L
  rw [hgL] at hGL
  cases hGL
  have hlt : s + pre.length < (pre ++ [cv]).length := by
    have := (List.getElem?_eq_some_iff.mp hk).1
    exact this
  simp only [List.length_append, List.length_singleton] at hlt
  have hs0 : s = 0 := by omega
  subst hs0
  simp only [Nat.zero_add] at hd1 hk hdh ⊢
  -- the descent through pre is the walk's
  have htake : (pre ++ [cv]).take pre.length = pre := List.take_left' rfl
  unfold dsrP at hd1
  rw [htake, hP] at hd1
  cases hd1
  have hcv : cv' = cv := by
    rw [List.getElem?_append_right (Nat.le_refl _)] at hk
    simpa using hk.symm
  subst hcv
  -- height 0 at the leaf
  obtain ⟨⟨nL, hRL, hLl⟩, hlast⟩ := lteP_leaf _ c.i cv' c.p.fuel rk L ext hext
  obtain ⟨g1, h1, hG1, hl1, _⟩ := hs L nL hRL
  have e1 := Prod.mk.inj (Option.some.inj (hgL.symm.trans hG1))
  have hh0 : h0 = 0 := by rw [e1.2]; rw [hLl] at hl1; simpa using hl1.symm
  subst hh0
  rw [dhP_zero_of_lteP _ _ hs c.i cv' c.p.fuel rk L ext hext] at hdh
  cases hdh
  rw [hpath, hdd]
  apply path_last_map
  have hP' := (dsrFold_shape (rdN c v) c.i c.p.fuel pre _ _ rk _ hP (by simp)).1
  exact getLast_map_append _ _ rk L hP' hlast

end SIS.Tree
