/-
The tree model (bergdb 024-12, TP7): the kinds of the nodes that the klongs
of the writer's overlay name, continued from SIS/Tree/WriterKindsRules.lean:
the tactics of the walk, a full node's replacement (`handleFullWith`) and
`appendKlongs`.
-/
import SIS.Tree.WriterKindsRules

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## Helpers -/

theorem KdLe.gh' {w v : W} {e : NodeId × Nat × Nat} (h : e ∈ w.gh) (hk : KdLe w v) : e ∈ v.gh :=
  hk.1.2 e h

/-- A new root above x and y of segment g. -/
theorem kd_root3 {K : KindOracle} {w : W} {x y : NodeId} {g h h' : Nat} (t : Time) (sc : Nat)
    (hx : (x, g, h) ∈ w.gh) (hy : (y, g, h') ∈ w.gh) (h'' : Nat) :
    kdKs (KindKlong K w g (h'' + 1)) [.time t, .key 0 x, .key sc y] := by
  refine kdKs_cons_time t (kdKs_cons_key ?_ (kdKs_cons_key ?_ (kdKs_nil _)))
  · exact ⟨fun _ => kd_isKey hx, fun h0 => absurd h0 (Nat.succ_ne_zero _)⟩
  · exact ⟨fun _ => kd_isKey hy, fun h0 => absurd h0 (Nat.succ_ne_zero _)⟩

/-- The loop of a time split: no state changes, and its klongs are those of
`last` and `ins`. -/
theorem kd_replaceOrAdd (P : Nat → NodeId → Prop) (last : KNode) (ins : List (Nat × NodeId))
    (c : Ctx) (w : W) (hl : kdKs P last.ks) (hi : kdPairs P ins) :
    WriterWP (replaceOrAdd last ins) c w (fun l v => v = w ∧ kdKs P l.ks) := by
  unfold replaceOrAdd
  simp only [writerWP_bind, writerWP_read]
  induction ins generalizing last with
  | nil => simp only [List.foldlM_nil, writerWP_pure]; exact ⟨by trivial, hl⟩
  | cons q ins ih =>
    have hq := hi q List.mem_cons_self
    have hr : kdPairs P ins := fun e he => hi e (List.mem_cons_of_mem _ he)
    rw [List.foldlM_cons, writerWP_bind]
    cases hrk : replaceKlong last.ks c.i q.1 q.2 with
    | error e => exact writerWP_throw _ _ _ _
    | ok result =>
      cases result with
      | none =>
        simp only [writerWP_pure]
        exact ih _ (kdKs_add_key _ hl hq) hr
      | some ks =>
        simp only [writerWP_pure]
        exact ih { last with ks := ks } (kdKs_replaceKlong hrk hl hq) hr

/-- A store of a node of the overlay read at an earlier state. -/
theorem kd_putNode_of (K : KindOracle) (B x : NodeId) (n' : KNode) (c : Ctx) (vr vt w : W)
    (n0 : KNode) (hb : Book B c w) (hi : KdInv K B w) (hl : vr.nodes.lookup x = some n0)
    (hkr : KdLe vr w) (hleaf : n'.leaf = n0.leaf) (g h : Nat) (hm : (x, g, h) ∈ vt.gh)
    (hkt : KdLe vt w) (hks : kdKs (KindKlong K w g h) n'.ks) :
    WriterWP (putNode x n') c w (fun _ v => Book B c v ∧ KdInv K B v ∧ KdLe w v ∧
      v.path = w.path ∧ v.madeFor = w.madeFor ∧ v.nodes.lookup x = some n') := by
  obtain ⟨n1, hn1, hl1⟩ := hkr.1.lookup hl
  exact kd_putNode K B x n' c w hb hi n1 hn1 (hleaf.trans hl1.symm) g h (KdLe.gh' hm hkt) hks

theorem kd_made_some {K : KindOracle} {w : W} {x y : NodeId} {g h h' : Nat}
    (hx : (x, g, h) ∈ w.gh) (hy : (y, g, h') ∈ w.gh) :
    ∀ o', some x = some o' → ∃ g h, (y, g, h) ∈ w.gh ∧ IsKeySeg K w o' g := by
  intro o' ho
  cases ho
  exact ⟨g, h', hy, kd_isKey hx⟩

theorem kd_made_rep {K : KindOracle} {B : NodeId} {w : W} (hi : KdInv K B w) {x y : NodeId}
    {g h h' : Nat} {r : Option NodeId} (hr : ∀ o, r = some o → (x, o) ∈ w.madeFor)
    (hx : (x, g, h) ∈ w.gh) (hy : (y, g, h') ∈ w.gh) :
    ∀ o', r = some o' → ∃ g h, (y, g, h) ∈ w.gh ∧ IsKeySeg K w o' g := by
  intro o' ho
  exact ⟨g, h', hy, hi.made (x, o') (hr o' ho) g h hx⟩

theorem kd_path_at {w v : W} {d : Nat} {e : Option Nat × NodeId} (h : w.path[d]? = some e)
    (hpv : v.path = w.path) : v.path[d]? = some e := by rw [hpv]; exact h

theorem kd_k1_eq {w v : W} {d : Nat} {a : Option Nat} {x y : NodeId} {k k1 : Nat}
    (hpx : w.path[d]? = some (a, x)) (hak : a = some k) (hy : v.path[d]? = some (some k1, y))
    (hpv : v.path = w.path) : k1 = k := by
  rw [hpv, hpx, hak] at hy
  simp only [Option.some.injEq, Prod.mk.injEq] at hy
  exact hy.1.symm

theorem kdPairs_nil' {P : Nat → NodeId → Prop} : kdPairs P [] := by
  intro q hq; cases hq

theorem kdPairs_cons {P : Nat → NodeId → Prop} {c : Nat} {y : NodeId} {l : List (Nat × NodeId)}
    (h1 : P c y) (h2 : kdPairs P l) : kdPairs P ((c, y) :: l) := by
  intro q hq
  rcases List.mem_cons.mp hq with hq | hq
  · subst hq; exact h1
  · exact h2 q hq

/-- A node read as inner has a height above 0. -/
theorem kd_h_ne {B : NodeId} {c : Ctx} {vr : W} {q : NodeId} {pn : KNode} {gq hq : Nat}
    (hf : ¬ pn.leaf = true) (hl : vr.nodes.lookup q = some pn) (hb : Book B c vr)
    (hm : (q, gq, hq) ∈ vr.gh) : hq ≠ 0 := by
  have := kd_leaf hb hl hm
  intro h0
  subst h0
  simp at this
  exact hf this

/-- The klong that `linkIndex` found, pointed to y. -/
theorem kd_repoint_ok {K : KindOracle} {w : W} {n : KNode} {x y : NodeId} {g h k j : Nat}
    (hj : n.linkIndex x k = some j) (hk : KindKlong K w g h k y) :
    ∀ cv z, n.ks[j]? = some (.key cv z) → KindKlong K w g h cv y := by
  intro cv z hz
  rw [kd_linkIndex_some n x k j hj] at hz
  simp only [Option.some.injEq, Klong.key.injEq] at hz
  rw [← hz.1]
  exact hk

/-- The klongs of a node read at an earlier state, for its entry in `gh`. -/
theorem kd_cache_at {K : KindOracle} {B : NodeId} {vr v : W} {x : NodeId} {n : KNode} {g h : Nat}
    (hl : vr.nodes.lookup x = some n) (hi : KdInv K B vr) (hm : (x, g, h) ∈ vr.gh)
    (hk : KdLe vr v) : kdKs (KindKlong K v g h) n.ks :=
  kdKs_mono (kd_cache_node hi hl hm) hk

/-! ## The tactics of the walk -/

/-- `KdLe a b` along the chain of the steps' hypotheses `KdLe v1 v2`. -/
syntax "kdChain" : tactic
macro_rules
  | `(tactic| kdChain) => `(tactic| first
    | exact KdLe.refl _
    | assumption
    | (refine KdLe.trans ?kdL (by assumption); kdChain))

/-- `v.path = w.path` along the chain of the steps' hypotheses. -/
syntax "kdPathEq" : tactic
macro_rules
  | `(tactic| kdPathEq) => `(tactic| first
    | rfl
    | assumption
    | (refine Eq.trans (by assumption) ?kdP; kdPathEq))

/-- An entry of `gh` at an earlier state. -/
macro "kdTag" : tactic => `(tactic| first
  | assumption
  | exact KdLe.gh' (by assumption) (by kdChain))

macro "kdState" : tactic => `(tactic| first
  | assumption
  | exact book_spaceSplits (by assumption) _
  | exact book_merges (by assumption) _)

macro "kdUse " h:term : tactic => `(tactic| (
  (with_unfolding_none refine' kd_writerWP _ _ $h _ _ _ ?kdView ?kdKinds ?kdBook ?kdInv ?kdPost)
  case kdView => assumption
  case kdKinds => assumption
  case kdBook => assumption
  case kdInv => assumption
  intro _ _ _ _ _ _ _))

macro "kdNode" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (getNode _) _ _ _)
  (refine writerWP_mono (kd_getNode ?kdK ?kdB _ _ _ ?kdView ?kdKinds ?kdBook ?kdInv) ?kdPost)
  case kdView => assumption
  case kdKinds => assumption
  case kdBook => assumption
  case kdInv => assumption
  rintro _ _ ⟨_, _, _, _, _, _⟩
  obtain ⟨_, _, _⟩ := kd_tag_of_lookup (by assumption) (by assumption)))

macro "kdGh" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (ghOf _) _ _ _)
  (refine writerWP_mono (kd_ghOf ?kdK ?kdB _ _ _ ?kdView ?kdKinds ?kdBook ?kdInv) ?kdPost)
  case kdView => assumption
  case kdKinds => assumption
  case kdBook => assumption
  case kdInv => assumption
  rintro ⟨_, _⟩ _ ⟨_, _, _, _, _, _, _, _, _⟩))

/-- Reads that change nothing. -/
macro "kdRead" : tactic => `(tactic| first
  | ((with_unfolding_none guard_target = WriterWP pathSize _ _ _)
     refine writerWP_mono (kd_pathSize _ _) ?kdPost
     rintro _ _ ⟨hkdEq, _⟩
     subst hkdEq)
  | ((with_unfolding_none guard_target = WriterWP (pathNode _) _ _ _)
     refine writerWP_mono (kd_pathNode _ _ _) ?kdPost
     rintro _ _ ⟨hkdEq, _⟩
     subst hkdEq)
  | ((with_unfolding_none guard_target = WriterWP (klongAt _) _ _ _)
     refine writerWP_mono (kd_klongAt _ _ _) ?kdPost
     rintro _ _ ⟨hkdEq, _⟩
     subst hkdEq)
  | ((with_unfolding_none guard_target = WriterWP (parentAt _) _ _ _)
     refine writerWP_mono (kd_parentAt _ _ _) ?kdPost
     rintro _ _ ⟨hkdEq, _⟩
     subst hkdEq)
  | ((with_unfolding_none guard_target = WriterWP (replacedBy _) _ _ _)
     refine writerWP_mono (kd_replacedBy _ _ _) ?kdPost
     rintro _ _ ⟨hkdEq, _⟩
     subst hkdEq))

macro "kdCnt" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (modify _) _ _ _)
  (refine kd_counter ?kdK ?kdB _ _ _ _ rfl rfl rfl rfl rfl rfl ?kdBk ?kdBook ?kdInv ?kdPost)
  case kdBk => intro _ _ hbk; first | exact book_spaceSplits hbk _ | exact book_merges hbk _
  case kdBook => assumption
  case kdInv => assumption
  intro _ _ _ _ _ _))

/-- Closes a postcondition. -/
macro "kdDone" : tactic => `(tactic| (
  (with_unfolding_none guard_target = Book _ _ _ ∧ KdInv _ _ _ ∧ KdLe _ _ ∧ _)
  refine ⟨by kdState, by assumption, by kdChain, by kdPathEq⟩))

/-- Klongs of the right kind for a node's entry. -/
syntax "kdKsTac" : tactic
macro_rules
  | `(tactic| kdKsTac) => `(tactic| first
    | exact kdKs_nil _
    | exact kdKs_mono (by assumption) (by kdChain)
    | exact (kdKs_halves _ _ (kd_free_of_leaf (by assumption)) (kdKs_mono (by assumption) (by kdChain))
        (kdPairs_mono (by assumption) (by kdChain))).1
    | exact (kdKs_halves _ _ (kd_free_of_leaf (by assumption)) (kdKs_mono (by assumption) (by kdChain))
        (kdPairs_mono (by assumption) (by kdChain))).2
    | exact kd_root3 _ _ (by kdTag) (by kdTag) _
    | exact kd_cache_at (by assumption) (by assumption) (by kdTag) (by kdChain)
    | exact kdKs_toPrev _ (kd_cache_at (by assumption) (by assumption) (by kdTag) (by kdChain))
    | exact kdKs_setAt_del _ _ (kd_cache_at (by assumption) (by assumption) (by kdTag) (by kdChain))
    | exact kdKs_add_del _ _ (kd_cache_at (by assumption) (by assumption) (by kdTag) (by kdChain))
    | exact kdKs_lastVersionGivenDel _ _
        (kd_cache_at (by assumption) (by assumption) (by kdTag) (by kdChain))
    | exact kdKs_renameKey _ (kd_free (by assumption)) (by assumption)
        (kdKs_lastVersionGivenDel _ _
          (kd_cache_at (by assumption) (by assumption) (by kdTag) (by kdChain)))
    | (split <;> kdKsTac))

macro "kdStore" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (putNode _ _) _ _ _)
  (refine writerWP_mono (kd_putNode_of ?kdK ?kdB _ _ _ ?kdVr ?kdVt _ ?kdN ?kdBook ?kdInv ?kdLook ?kdKr ?kdLeaf ?kdG ?kdH ?kdTagM ?kdKt ?kdKs) ?kdPost)
  case kdBook => kdState
  case kdInv => assumption
  case kdLook => assumption
  case kdKr => kdChain
  case kdLeaf => bkLeaf
  case kdTagM => assumption
  case kdKt => kdChain
  case kdKs => kdKsTac
  rintro _ _ ⟨_, _, _, _, _, _⟩))

/-- The leaf flag of a new node is that of its height. -/
macro "kdHeight" : tactic => `(tactic| first
  | assumption
  | rfl
  | (simp only [Bool.not_not]; assumption)
  | simp)

macro "kdCreate" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (newKey _ _ _ _) _ _ _)
  (refine writerWP_mono (kd_newKey ?kdK ?kdB _ _ _ _ _ _ ?kdBook ?kdInv ?kdH ?kdKs) ?kdPost)
  case kdBook => kdState
  case kdInv => assumption
  case kdH => kdHeight
  case kdKs => kdKsTac
  rintro _ _ ⟨_, _, _, _, _, _, _, _⟩))

/-- A made node of x's segment and the node x replaced, or x. -/
macro "kdMadeTac" : tactic => `(tactic| first
  | exact kd_made_some (by kdTag) (by kdTag)
  | exact kd_made_rep (by assumption) (by assumption) (by kdTag) (by kdTag))

macro "kdMade" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (setMadeFor _ _) _ _ _)
  (refine writerWP_mono (kd_setMadeFor ?kdK ?kdB _ _ _ _ ?kdView ?kdBook ?kdInv ?kdM) ?kdPost)
  case kdView => assumption
  case kdBook => kdState
  case kdInv => assumption
  case kdM => kdMadeTac
  rintro _ _ ⟨_, _, _, _⟩))

/-- The steps of the walk without the state's changes (`modify` is `kdCnt`'s). -/
macro "kdSimp" : tactic => `(tactic|
  simp only [writerWP_bind, writerWP_read, writerWP_get, writerWP_pure])

macro "kdRepl" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (replaceOrAdd _ _) _ _ _)
  (refine writerWP_mono (kd_replaceOrAdd _ _ _ _ _ (kdKs_mono (by assumption) (by kdChain))
    (kdPairs_mono (by assumption) (by kdChain))) ?kdPost)
  rintro _ _ ⟨hkdEq, _⟩
  subst hkdEq))

/-- The klong of the path's entry at depth d + 1: the one known at the start. -/
macro "kdK1 " hpx:term:max hak:term:max : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (klongAt _) _ _ _)
  refine writerWP_mono (kd_klongAt _ _ _) ?kdPost
  rintro _ _ ⟨hkdEq, _, hkdY⟩
  subst hkdEq
  have hkdK := kd_k1_eq $hpx $hak hkdY (by kdPathEq)
  subst hkdK))

/-- A klong given to the parent q of x: it names x's replacement, of x's
segment, with q's klong of x, or another compare value if q is inner. -/
macro "kdParentKl " hx:term:max hxk:term:max : tactic => `(tactic| first
  | exact kd_swap (by kdState) (by assumption) (by assumption) (KdLe.gh' $hx (by kdChain))
      (KindKlong.kdMono $hxk (by kdChain)) (kd_isKey (by kdTag))
  | exact kd_swap_inner (by kdState) (by assumption) (by assumption)
      (kd_h_ne (by assumption) (by assumption) (by assumption) (by kdTag))
      (KdLe.gh' $hx (by kdChain)) (KindKlong.kdMono $hxk (by kdChain)) (kd_isKey (by kdTag)))

macro "kdUpH " hup:term:max hpe:term:max hqm:term:max hx:term:max hxk:term:max : tactic => `(tactic| (
  (refine writerWP_mono ($hup _ _ _ _ ?kdView ?kdKinds ?kdBook ?kdInv ?kdPathQ ?kdMore) ?kdPost)
  case kdView => assumption
  case kdKinds => assumption
  case kdBook => kdState
  case kdInv => assumption
  case kdPathQ => exact ⟨_, kd_path_at $hpe (by kdPathEq)⟩
  case kdMore =>
    refine ⟨_, _, KdLe.gh' $hqm (by kdChain), ?kdPairs⟩
    repeat' (first | exact kdPairs_nil' | refine kdPairs_cons ?_ ?_)
    all_goals kdParentKl $hx $hxk
  rintro _ _ ⟨_, _, _, _⟩))

/-- The store of q's klong of x pointed to x's replacement. -/
macro "kdStoreRep " hqm:term:max hx:term:max hxk:term:max : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (putNode _ (KNode.repoint _ _ _)) _ _ _)
  (refine writerWP_mono (kd_putNode_of ?kdK ?kdB _ _ _ ?kdVr ?kdVt _ ?kdN ?kdBook ?kdInv ?kdLook ?kdKr ?kdLeaf ?kdG ?kdH ?kdTagM ?kdKt ?kdKs) ?kdPost)
  case kdBook => kdState
  case kdInv => assumption
  case kdLook => assumption
  case kdKr => kdChain
  case kdLeaf => bkLeaf
  case kdTagM => exact $hqm
  case kdKt => kdChain
  case kdKs =>
    exact kdKs_repoint _ (kd_cache_node (by assumption) (by assumption) (by kdTag))
      (kd_repoint_ok (by assumption) (by kdParentKl $hx $hxk))
  rintro _ _ ⟨_, _, _, _, _, _⟩))

macro "kdCore" : tactic => `(tactic| first
  | kdRepl
  | kdDone
  | kdNode
  | kdGh
  | kdRead
  | kdStore
  | kdCreate
  | kdMade
  | kdUse (kd_note _ _ _)
  | kdUse (kd_fresh _ _)
  | kdUse (kd_newSuperRoot _ _ _)
  | kdCnt
  | exact writerWP_throw _ _ _ _)

/-! ## A full node's replacement -/

/-- What `appendKlongs` one level up does for `handleFullWith`: for the parent
q, the path's node at depth d, and klongs of the right kind for it, it keeps
the state and the path. -/
def KdUp (K : KindOracle) (B : NodeId) (up : NodeId → List (Nat × NodeId) → M Unit) (d : Nat) :
    Prop :=
  ∀ q more c w, ViewIdsBelow B c.view → ViewKinds K B c → Book B c w → KdInv K B w →
    (∃ a, w.path[d]? = some (a, q)) →
    (∃ g h, (q, g, h) ∈ w.gh ∧ kdPairs (KindKlong K w g h) more) →
    WriterWP (up q more) c w (fun _ v => Book B c v ∧ KdInv K B v ∧ KdLe w v ∧ v.path = w.path)

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 20000 in
theorem kd_handleFullWith (K : KindOracle) (B : NodeId) (up : NodeId → List (Nat × NodeId) → M Unit)
    (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)) (last : KNode) (compact : Bool)
    (c : Ctx) (w : W) (hv : ViewIdsBelow B c.view) (hk : ViewKinds K B c) (hb : Book B c w)
    (hi : KdInv K B w) (g h : Nat) (hx : (x, g, h) ∈ w.gh) (a : Option Nat)
    (hpx : w.path[depth]? = some (a, x))
    (hlast : kdKs (KindKlong K w g h) last.ks) (hins : kdPairs (KindKlong K w g h) ins)
    (hup : ∀ e, depth = e + 1 → KdUp K B up e) :
    WriterWP (handleFullWith up depth x ins last compact) c w
      (fun _ v => Book B c v ∧ KdInv K B v ∧ KdLe w v ∧ v.path = w.path) := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (kd_getNode K B x c w hv hk hb hi) ?_
  rintro n w1 ⟨hb1, hi1, hle1, hl1, hp1, -⟩
  have hx1 := KdLe.gh' hx hle1
  have hnl : n.leaf = (h == 0) := kd_leaf hb1 hl1 hx1
  refine writerWP_mono (kd_ghOf K B x c w1 hv hk hb1 hi1) ?_
  rintro ⟨g', h'⟩ w2 ⟨hb2, hi2, hle2, hp2, -, hm2, -⟩
  obtain ⟨rfl, rfl⟩ := kd_tag_eq hb2 (KdLe.gh' hx1 hle2) hm2
  clear hm2
  refine writerWP_mono (kd_parentAt depth c w2) ?_
  rintro parent _ ⟨rfl, hpar0, hpar1⟩
  cases depth with
  | zero =>
    obtain rfl := hpar0 rfl
    clear hpar1 hup
    repeat' first
      | kdSimp
      | kdCore
      | wpSplit
      | split
      | contradiction
  | succ e =>
    obtain ⟨a', q, rfl, hpe⟩ := hpar1 e rfl
    clear hpar0
    have hpe0 : w.path[e]? = some (a', q) := by rw [← hp1, ← hp2]; exact hpe
    have hqg : q ∈ w.gh.map (·.1) :=
      hi.pathGh e a' q hpe0 (List.getElem?_eq_some_iff.mp hpx).1
    obtain ⟨⟨q', gq, hq⟩, hqm, hqe⟩ := List.mem_map.mp hqg
    simp only at hqe
    subst hqe
    have hkl : ∀ k, a = some k → KindKlong K w gq hq k x :=
      fun k hk => hi.path e a' q' k x hpe0 (by rw [hpx, hk]) gq hq hqm
    obtain ⟨k, hak⟩ : ∃ k, a = some k := by
      cases a with
      | none => exact absurd rfl (hi.pathSome e none x hpx)
      | some k => exact ⟨k, rfl⟩
    have hxk : KindKlong K w gq hq k x := hi.path e a' q' k x hpe0 (by rw [hpx, hak]) gq hq hqm
    have hup' := hup e rfl
    clear hup
    repeat' first
      | kdSimp
      | kdK1 hpx hak
      | kdStoreRep hqm hx hxk
      | kdCore
      | kdUpH hup' hpe0 hqm hx hxk
      | wpSplit
      | split
      | contradiction

/-! ## `appendKlongs` -/

theorem kd_addKeys (K : KindOracle) (B : NodeId) (x : NodeId) (ins : List (Nat × NodeId))
    (c : Ctx) (w : W) (hv : ViewIdsBelow B c.view) (hk : ViewKinds K B c) (hb : Book B c w)
    (hi : KdInv K B w) (g h : Nat) (hx : (x, g, h) ∈ w.gh)
    (hins : kdPairs (KindKlong K w g h) ins) :
    WriterWP (addKeys x ins) c w
      (fun _ v => Book B c v ∧ KdInv K B v ∧ KdLe w v ∧ v.path = w.path) := by
  unfold addKeys
  kdSimp
  refine writerWP_mono (kd_getNode K B x c w hv hk hb hi) ?_
  rintro n w1 ⟨hb1, hi1, hle1, hl1, hp1, -⟩
  refine writerWP_mono (kd_putNode K B x _ c w1 hb1 hi1 n hl1 (bk_foldl_add_leaf _ _ _) g h
    (KdLe.gh' hx hle1)
    (kdKs_addFold _ (kd_cache_node hi1 hl1 (KdLe.gh' hx hle1)) (kdPairs_mono hins hle1))) ?_
  rintro _ v ⟨hb2, hi2, hle2, hp2, -, -⟩
  exact ⟨hb2, hi2, hle1.trans hle2, hp2.trans hp1⟩

/-- `appendKlongs` at x, the path's node at `depth`, with klongs of the right
kind for x. -/
theorem kd_appendKlongs (K : KindOracle) (B : NodeId) (depth : Nat) :
    ∀ (x : NodeId) (ins : List (Nat × NodeId)) (c : Ctx) (w : W), ViewIdsBelow B c.view →
      ViewKinds K B c → Book B c w → KdInv K B w →
      (∃ g h, (x, g, h) ∈ w.gh ∧ kdPairs (KindKlong K w g h) ins) →
      (∃ a, w.path[depth]? = some (a, x)) →
      WriterWP (appendKlongs depth x ins) c w
        (fun _ v => Book B c v ∧ KdInv K B v ∧ KdLe w v ∧ v.path = w.path) := by
  induction depth with
  | zero =>
    intro x ins c w hv hk hb hi ⟨g, h, hx, hins⟩ ⟨a, hpx⟩
    rw [appendKlongs_step_dead]
    kdSimp
    refine writerWP_mono (kd_getNode K B x c w hv hk hb hi) ?_
    rintro n w1 ⟨hb1, hi1, hle1, hl1, hp1, -⟩
    have hx1 := KdLe.gh' hx hle1
    have hlv := kdKs_lastVersion c.i (kd_cache_node hi1 hl1 hx1)
    have hpx1 : w1.path[0]? = some (a, x) := by rw [hp1]; exact hpx
    have hfin : ∀ cp, WriterWP (handleFullWith (fun _ _ => throw "corrupt: a split's parent above depth 0")
        0 x ins (n.lastVersion c.i) cp) c w1
        (fun _ v => Book B c w ∧ KdInv K B v ∧ KdLe w v ∧ v.path = w.path ∧ Book B c v) := by
      intro cp
      refine writerWP_mono (kd_handleFullWith K B _ 0 x ins _ cp c w1 hv hk hb1 hi1 g h hx1 a hpx1
        hlv (kdPairs_mono hins hle1) (fun e he => by cases he)) ?_
      rintro _ v ⟨hb2, hi2, hle2, hp2⟩
      exact ⟨hb, hi2, hle1.trans hle2, hp2.trans hp1, hb2⟩
    split
    · exact writerWP_mono (hfin false) (fun _ v h => ⟨h.2.2.2.2, h.2.1, h.2.2.1, h.2.2.2.1⟩)
    · split
      · exact writerWP_mono (hfin true) (fun _ v h => ⟨h.2.2.2.2, h.2.1, h.2.2.1, h.2.2.2.1⟩)
      · refine writerWP_mono (kd_addKeys K B x ins c w1 hv hk hb1 hi1 g h hx1
          (kdPairs_mono hins hle1)) ?_
        rintro _ v ⟨hb2, hi2, hle2, hp2⟩
        exact ⟨hb2, hi2, hle1.trans hle2, hp2.trans hp1⟩
  | succ d ih =>
    intro x ins c w hv hk hb hi ⟨g, h, hx, hins⟩ ⟨a, hpx⟩
    rw [appendKlongs_step_dead]
    kdSimp
    refine writerWP_mono (kd_getNode K B x c w hv hk hb hi) ?_
    rintro n w1 ⟨hb1, hi1, hle1, hl1, hp1, -⟩
    have hx1 := KdLe.gh' hx hle1
    have hlv := kdKs_lastVersion c.i (kd_cache_node hi1 hl1 hx1)
    have hpx1 : w1.path[d + 1]? = some (a, x) := by rw [hp1]; exact hpx
    have hup : ∀ e, d + 1 = e + 1 → KdUp K B (fun q more => appendKlongs d q more) e := by
      intro e he
      cases he
      intro q more c' w' hv' hk' hb' hi' hpq hmore
      exact ih q more c' w' hv' hk' hb' hi' hmore hpq
    have hfin : ∀ cp, WriterWP (handleFullWith (fun q more => appendKlongs d q more)
        (d + 1) x ins (n.lastVersion c.i) cp) c w1
        (fun _ v => Book B c v ∧ KdInv K B v ∧ KdLe w v ∧ v.path = w.path) := by
      intro cp
      refine writerWP_mono (kd_handleFullWith K B _ (d + 1) x ins _ cp c w1 hv hk hb1 hi1 g h hx1 a
        hpx1 hlv (kdPairs_mono hins hle1) hup) ?_
      rintro _ v ⟨hb2, hi2, hle2, hp2⟩
      exact ⟨hb2, hi2, hle1.trans hle2, hp2.trans hp1⟩
    split
    · exact hfin false
    · split
      · exact hfin true
      · refine writerWP_mono (kd_addKeys K B x ins c w1 hv hk hb1 hi1 g h hx1
          (kdPairs_mono hins hle1)) ?_
        rintro _ v ⟨hb2, hi2, hle2, hp2⟩
        exact ⟨hb2, hi2, hle1.trans hle2, hp2.trans hp1⟩

end SIS.Tree
