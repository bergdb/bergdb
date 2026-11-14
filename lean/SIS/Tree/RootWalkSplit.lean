/-
The walk of the kinds with the space root (`KrInv`: `KdInv` and `RootK`, the
writer's space root a key node), a copy of the kinds walk (WriterKinds*.lean)
whose names begin with kr; `newSuperRoot` takes a key node.

The tree model (bergdb 024-12, TP7): the kinds of the nodes that the klongs
of the writer's overlay name, continued from SIS/Tree/WriterKindsRules.lean:
the tactics of the walk, a full node's replacement (`handleFullWith`) and
`appendKlongs`.
-/
import SIS.Tree.RootWalkRules

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## Helpers -/

theorem KrLe.gh' {w v : W} {e : NodeId × Nat × Nat} (h : e ∈ w.gh) (hk : KrLe w v) : e ∈ v.gh :=
  hk.1.2 e h

/-- A new root above x and y of segment g. -/
theorem kr_root3 {K : KindOracle} {w : W} {x y : NodeId} {g h h' : Nat} (t : Time) (sc : Nat)
    (hx : (x, g, h) ∈ w.gh) (hy : (y, g, h') ∈ w.gh) (h'' : Nat) :
    krKs (KindKlong K w g (h'' + 1)) [.time t, .key 0 x, .key sc y] := by
  refine krKs_cons_time t (krKs_cons_key ?_ (krKs_cons_key ?_ (krKs_nil _)))
  · exact ⟨fun _ => kr_isKey hx, fun h0 => absurd h0 (Nat.succ_ne_zero _)⟩
  · exact ⟨fun _ => kr_isKey hy, fun h0 => absurd h0 (Nat.succ_ne_zero _)⟩

/-- The loop of a time split: no state changes, and its klongs are those of
`last` and `ins`. -/
theorem kr_replaceOrAdd (P : Nat → NodeId → Prop) (last : KNode) (ins : List (Nat × NodeId))
    (c : Ctx) (w : W) (hl : krKs P last.ks) (hi : krPairs P ins) :
    WriterWP (replaceOrAdd last ins) c w (fun l v => v = w ∧ krKs P l.ks) := by
  unfold replaceOrAdd
  simp only [writerWP_bind, writerWP_read]
  induction ins generalizing last with
  | nil => simp only [List.foldlM_nil, writerWP_pure]; exact ⟨by trivial, hl⟩
  | cons q ins ih =>
    have hq := hi q List.mem_cons_self
    have hr : krPairs P ins := fun e he => hi e (List.mem_cons_of_mem _ he)
    rw [List.foldlM_cons, writerWP_bind]
    cases hrk : replaceKlong last.ks c.i q.1 q.2 with
    | error e => exact writerWP_throw _ _ _ _
    | ok result =>
      cases result with
      | none =>
        simp only [writerWP_pure]
        exact ih _ (krKs_add_key _ hl hq) hr
      | some ks =>
        simp only [writerWP_pure]
        exact ih { last with ks := ks } (krKs_replaceKlong hrk hl hq) hr

/-- A store of a node of the overlay read at an earlier state. -/
theorem kr_putNode_of (K : KindOracle) (B x : NodeId) (n' : KNode) (c : Ctx) (vr vt w : W)
    (n0 : KNode) (hb : Book B c w) (hi : KrInv K B w) (hl : vr.nodes.lookup x = some n0)
    (hkr : KrLe vr w) (hleaf : n'.leaf = n0.leaf) (g h : Nat) (hm : (x, g, h) ∈ vt.gh)
    (hkt : KrLe vt w) (hks : krKs (KindKlong K w g h) n'.ks) :
    WriterWP (putNode x n') c w (fun _ v => Book B c v ∧ KrInv K B v ∧ KrLe w v ∧
      v.path = w.path ∧ v.madeFor = w.madeFor ∧ v.nodes.lookup x = some n') := by
  obtain ⟨n1, hn1, hl1⟩ := hkr.1.lookup hl
  exact kr_putNode K B x n' c w hb hi n1 hn1 (hleaf.trans hl1.symm) g h (KrLe.gh' hm hkt) hks

theorem kr_made_some {K : KindOracle} {w : W} {x y : NodeId} {g h h' : Nat}
    (hx : (x, g, h) ∈ w.gh) (hy : (y, g, h') ∈ w.gh) :
    ∀ o', some x = some o' → ∃ g h, (y, g, h) ∈ w.gh ∧ IsKeySeg K w o' g := by
  intro o' ho
  cases ho
  exact ⟨g, h', hy, kr_isKey hx⟩

theorem kr_made_rep {K : KindOracle} {B : NodeId} {w : W} (hi : KrInv K B w) {x y : NodeId}
    {g h h' : Nat} {r : Option NodeId} (hr : ∀ o, r = some o → (x, o) ∈ w.madeFor)
    (hx : (x, g, h) ∈ w.gh) (hy : (y, g, h') ∈ w.gh) :
    ∀ o', r = some o' → ∃ g h, (y, g, h) ∈ w.gh ∧ IsKeySeg K w o' g := by
  intro o' ho
  exact ⟨g, h', hy, hi.made (x, o') (hr o' ho) g h hx⟩

theorem kr_path_at {w v : W} {d : Nat} {e : Option Nat × NodeId} (h : w.path[d]? = some e)
    (hpv : v.path = w.path) : v.path[d]? = some e := by rw [hpv]; exact h

theorem kr_k1_eq {w v : W} {d : Nat} {a : Option Nat} {x y : NodeId} {k k1 : Nat}
    (hpx : w.path[d]? = some (a, x)) (hak : a = some k) (hy : v.path[d]? = some (some k1, y))
    (hpv : v.path = w.path) : k1 = k := by
  rw [hpv, hpx, hak] at hy
  simp only [Option.some.injEq, Prod.mk.injEq] at hy
  exact hy.1.symm

theorem krPairs_nil' {P : Nat → NodeId → Prop} : krPairs P [] := by
  intro q hq; cases hq

theorem krPairs_cons {P : Nat → NodeId → Prop} {c : Nat} {y : NodeId} {l : List (Nat × NodeId)}
    (h1 : P c y) (h2 : krPairs P l) : krPairs P ((c, y) :: l) := by
  intro q hq
  rcases List.mem_cons.mp hq with hq | hq
  · subst hq; exact h1
  · exact h2 q hq

/-- A node read as inner has a height above 0. -/
theorem kr_h_ne {B : NodeId} {c : Ctx} {vr : W} {q : NodeId} {pn : KNode} {gq hq : Nat}
    (hf : ¬ pn.leaf = true) (hl : vr.nodes.lookup q = some pn) (hb : Book B c vr)
    (hm : (q, gq, hq) ∈ vr.gh) : hq ≠ 0 := by
  have := kr_leaf hb hl hm
  intro h0
  subst h0
  simp at this
  exact hf this

/-- The klong that `linkIndex` found, pointed to y. -/
theorem kr_repoint_ok {K : KindOracle} {w : W} {n : KNode} {x y : NodeId} {g h k j : Nat}
    (hj : n.linkIndex x k = some j) (hk : KindKlong K w g h k y) :
    ∀ cv z, n.ks[j]? = some (.key cv z) → KindKlong K w g h cv y := by
  intro cv z hz
  rw [kr_linkIndex_some n x k j hj] at hz
  simp only [Option.some.injEq, Klong.key.injEq] at hz
  rw [← hz.1]
  exact hk

/-- The klongs of a node read at an earlier state, for its entry in `gh`. -/
theorem kr_cache_at {K : KindOracle} {B : NodeId} {vr v : W} {x : NodeId} {n : KNode} {g h : Nat}
    (hl : vr.nodes.lookup x = some n) (hi : KrInv K B vr) (hm : (x, g, h) ∈ vr.gh)
    (hk : KrLe vr v) : krKs (KindKlong K v g h) n.ks :=
  krKs_mono (kr_cache_node hi hl hm) hk

/-! ## The tactics of the walk -/

/-- `KrLe a b` along the chain of the steps' hypotheses `KrLe v1 v2`. -/
syntax "krChain" : tactic
macro_rules
  | `(tactic| krChain) => `(tactic| first
    | exact KrLe.refl _
    | assumption
    | (refine KrLe.trans ?krL (by assumption); krChain))

/-- `v.path = w.path` along the chain of the steps' hypotheses. -/
syntax "krPathEq" : tactic
macro_rules
  | `(tactic| krPathEq) => `(tactic| first
    | rfl
    | assumption
    | (refine Eq.trans (by assumption) ?krP; krPathEq))

/-- An entry of `gh` at an earlier state. -/
macro "krTag" : tactic => `(tactic| first
  | assumption
  | exact KrLe.gh' (by assumption) (by krChain))

macro "krState" : tactic => `(tactic| first
  | assumption
  | exact book_spaceSplits (by assumption) _
  | exact book_merges (by assumption) _)

macro "krUse " h:term : tactic => `(tactic| (
  (with_unfolding_none refine' kr_writerWP _ _ $h _ _ _ ?krView ?krKinds ?krBook ?krInv ?krPost)
  case krView => assumption
  case krKinds => assumption
  case krBook => assumption
  case krInv => assumption
  intro _ _ _ _ _ _ _))

macro "krNode" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (getNode _) _ _ _)
  (refine writerWP_mono (kr_getNode ?krK ?krB _ _ _ ?krView ?krKinds ?krBook ?krInv) ?krPost)
  case krView => assumption
  case krKinds => assumption
  case krBook => assumption
  case krInv => assumption
  rintro _ _ ⟨_, _, _, _, _, _⟩
  obtain ⟨_, _, _⟩ := kr_tag_of_lookup (by assumption) (by assumption)))

macro "krGh" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (ghOf _) _ _ _)
  (refine writerWP_mono (kr_ghOf ?krK ?krB _ _ _ ?krView ?krKinds ?krBook ?krInv) ?krPost)
  case krView => assumption
  case krKinds => assumption
  case krBook => assumption
  case krInv => assumption
  rintro ⟨_, _⟩ _ ⟨_, _, _, _, _, _, _, _, _⟩))

/-- Reads that change nothing. -/
macro "krRead" : tactic => `(tactic| first
  | ((with_unfolding_none guard_target = WriterWP pathSize _ _ _)
     refine writerWP_mono (kr_pathSize _ _) ?krPost
     rintro _ _ ⟨hkdEq, _⟩
     subst hkdEq)
  | ((with_unfolding_none guard_target = WriterWP (pathNode _) _ _ _)
     refine writerWP_mono (kr_pathNode _ _ _) ?krPost
     rintro _ _ ⟨hkdEq, _⟩
     subst hkdEq)
  | ((with_unfolding_none guard_target = WriterWP (klongAt _) _ _ _)
     refine writerWP_mono (kr_klongAt _ _ _) ?krPost
     rintro _ _ ⟨hkdEq, _⟩
     subst hkdEq)
  | ((with_unfolding_none guard_target = WriterWP (parentAt _) _ _ _)
     refine writerWP_mono (kr_parentAt _ _ _) ?krPost
     rintro _ _ ⟨hkdEq, _⟩
     subst hkdEq)
  | ((with_unfolding_none guard_target = WriterWP (replacedBy _) _ _ _)
     refine writerWP_mono (kr_replacedBy _ _ _) ?krPost
     rintro _ _ ⟨hkdEq, _⟩
     subst hkdEq))

macro "krCnt" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (modify _) _ _ _)
  (refine kr_counter ?krK ?krB _ _ _ _ rfl rfl rfl rfl rfl rfl rfl ?krBk ?krBook ?krInv ?krPost)
  case krBk => intro _ _ hbk; first | exact book_spaceSplits hbk _ | exact book_merges hbk _
  case krBook => assumption
  case krInv => assumption
  intro _ _ _ _ _ _))

/-- Closes a postcondition. -/
macro "krDone" : tactic => `(tactic| (
  (with_unfolding_none guard_target = Book _ _ _ ∧ KrInv _ _ _ ∧ KrLe _ _ ∧ _)
  refine ⟨by krState, by assumption, by krChain, by krPathEq⟩))

/-- Klongs of the right kind for a node's entry. -/
syntax "krKsTac" : tactic
macro_rules
  | `(tactic| krKsTac) => `(tactic| first
    | exact krKs_nil _
    | exact krKs_mono (by assumption) (by krChain)
    | exact (krKs_halves _ _ (kr_free_of_leaf (by assumption)) (krKs_mono (by assumption) (by krChain))
        (krPairs_mono (by assumption) (by krChain))).1
    | exact (krKs_halves _ _ (kr_free_of_leaf (by assumption)) (krKs_mono (by assumption) (by krChain))
        (krPairs_mono (by assumption) (by krChain))).2
    | exact kr_root3 _ _ (by krTag) (by krTag) _
    | exact kr_cache_at (by assumption) (by assumption) (by krTag) (by krChain)
    | exact krKs_toPrev _ (kr_cache_at (by assumption) (by assumption) (by krTag) (by krChain))
    | exact krKs_setAt_del _ _ (kr_cache_at (by assumption) (by assumption) (by krTag) (by krChain))
    | exact krKs_add_del _ _ (kr_cache_at (by assumption) (by assumption) (by krTag) (by krChain))
    | exact krKs_lastVersionGivenDel _ _
        (kr_cache_at (by assumption) (by assumption) (by krTag) (by krChain))
    | exact krKs_renameKey _ (kr_free (by assumption)) (by assumption)
        (krKs_lastVersionGivenDel _ _
          (kr_cache_at (by assumption) (by assumption) (by krTag) (by krChain)))
    | (split <;> krKsTac))

macro "krStore" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (putNode _ _) _ _ _)
  (refine writerWP_mono (kr_putNode_of ?krK ?krB _ _ _ ?krVr ?krVt _ ?krN ?krBook ?krInv ?krLook ?krKr ?krLeaf ?krG ?krH ?krTagM ?krKt ?krKs) ?krPost)
  case krBook => krState
  case krInv => assumption
  case krLook => assumption
  case krKr => krChain
  case krLeaf => bkLeaf
  case krTagM => assumption
  case krKt => krChain
  case krKs => krKsTac
  rintro _ _ ⟨_, _, _, _, _, _⟩))

/-- The leaf flag of a new node is that of its height. -/
macro "krHeight" : tactic => `(tactic| first
  | assumption
  | rfl
  | (simp only [Bool.not_not]; assumption)
  | simp)

macro "krCreate" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (newKey _ _ _ _) _ _ _)
  (refine writerWP_mono (kr_newKey ?krK ?krB _ _ _ _ _ _ ?krBook ?krInv ?krH ?krKs) ?krPost)
  case krBook => krState
  case krInv => assumption
  case krH => krHeight
  case krKs => krKsTac
  rintro _ _ ⟨_, _, _, _, _, _, _, _⟩))

/-- A made node of x's segment and the node x replaced, or x. -/
macro "krMadeTac" : tactic => `(tactic| first
  | exact kr_made_some (by krTag) (by krTag)
  | exact kr_made_rep (by assumption) (by assumption) (by krTag) (by krTag))

macro "krMade" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (setMadeFor _ _) _ _ _)
  (refine writerWP_mono (kr_setMadeFor ?krK ?krB _ _ _ _ ?krView ?krBook ?krInv ?krM) ?krPost)
  case krView => assumption
  case krBook => krState
  case krInv => assumption
  case krM => krMadeTac
  rintro _ _ ⟨_, _, _, _⟩))

/-- The steps of the walk without the state's changes (`modify` is `krCnt`'s). -/
macro "krSimp" : tactic => `(tactic|
  simp only [writerWP_bind, writerWP_read, writerWP_get, writerWP_pure])

macro "krRepl" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (replaceOrAdd _ _) _ _ _)
  (refine writerWP_mono (kr_replaceOrAdd _ _ _ _ _ (krKs_mono (by assumption) (by krChain))
    (krPairs_mono (by assumption) (by krChain))) ?krPost)
  rintro _ _ ⟨hkdEq, _⟩
  subst hkdEq))

/-- The klong of the path's entry at depth d + 1: the one known at the start. -/
macro "krK1 " hpx:term:max hak:term:max : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (klongAt _) _ _ _)
  refine writerWP_mono (kr_klongAt _ _ _) ?krPost
  rintro _ _ ⟨hkdEq, _, hkdY⟩
  subst hkdEq
  have hkdK := kr_k1_eq $hpx $hak hkdY (by krPathEq)
  subst hkdK))

/-- A klong given to the parent q of x: it names x's replacement, of x's
segment, with q's klong of x, or another compare value if q is inner. -/
macro "krParentKl " hx:term:max hxk:term:max : tactic => `(tactic| first
  | exact kr_swap (by krState) (by assumption) (by assumption) (KrLe.gh' $hx (by krChain))
      (KindKlong.krMono $hxk (by krChain)) (kr_isKey (by krTag))
  | exact kr_swap_inner (by krState) (by assumption) (by assumption)
      (kr_h_ne (by assumption) (by assumption) (by assumption) (by krTag))
      (KrLe.gh' $hx (by krChain)) (KindKlong.krMono $hxk (by krChain)) (kr_isKey (by krTag)))

macro "krUpH " hup:term:max hpe:term:max hqm:term:max hx:term:max hxk:term:max : tactic => `(tactic| (
  (refine writerWP_mono ($hup _ _ _ _ ?krView ?krKinds ?krBook ?krInv ?krPathQ ?krMore) ?krPost)
  case krView => assumption
  case krKinds => assumption
  case krBook => krState
  case krInv => assumption
  case krPathQ => exact ⟨_, kr_path_at $hpe (by krPathEq)⟩
  case krMore =>
    refine ⟨_, _, KrLe.gh' $hqm (by krChain), ?krPairs⟩
    repeat' (first | exact krPairs_nil' | refine krPairs_cons ?_ ?_)
    all_goals krParentKl $hx $hxk
  rintro _ _ ⟨_, _, _, _⟩))

/-- The store of q's klong of x pointed to x's replacement. -/
macro "krStoreRep " hqm:term:max hx:term:max hxk:term:max : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (putNode _ (KNode.repoint _ _ _)) _ _ _)
  (refine writerWP_mono (kr_putNode_of ?krK ?krB _ _ _ ?krVr ?krVt _ ?krN ?krBook ?krInv ?krLook ?krKr ?krLeaf ?krG ?krH ?krTagM ?krKt ?krKs) ?krPost)
  case krBook => krState
  case krInv => assumption
  case krLook => assumption
  case krKr => krChain
  case krLeaf => bkLeaf
  case krTagM => exact $hqm
  case krKt => krChain
  case krKs =>
    exact krKs_repoint _ (kr_cache_node (by assumption) (by assumption) (by krTag))
      (kr_repoint_ok (by assumption) (by krParentKl $hx $hxk))
  rintro _ _ ⟨_, _, _, _, _, _⟩))

/-- A new space root: a node made by the step (an entry of `gh`). -/
macro "krSuper" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (newSuperRoot _) _ _ _)
  (refine writerWP_mono (kr_newSuperRoot ?krK ?krB _ _ _ ?krView ?krKinds ?krBook ?krInv ?krY) ?krPost)
  case krView => assumption
  case krKinds => assumption
  case krBook => krState
  case krInv => assumption
  case krY => exact ⟨_, Or.inl ⟨_, by krTag⟩⟩
  rintro _ _ ⟨_, _, _, _, _⟩))

macro "krCore" : tactic => `(tactic| first
  | krRepl
  | krDone
  | krNode
  | krGh
  | krRead
  | krStore
  | krCreate
  | krMade
  | krUse (kr_note _ _ _)
  | krUse (kr_fresh _ _)
  | krSuper
  | krCnt
  | exact writerWP_throw _ _ _ _)

/-! ## A full node's replacement -/

/-- What `appendKlongs` one level up does for `handleFullWith`: for the parent
q, the path's node at depth d, and klongs of the right kind for it, it keeps
the state and the path. -/
def KrUp (K : KindOracle) (B : NodeId) (up : NodeId → List (Nat × NodeId) → M Unit) (d : Nat) :
    Prop :=
  ∀ q more c w, ViewIdsBelow B c.view → ViewKinds K B c → Book B c w → KrInv K B w →
    (∃ a, w.path[d]? = some (a, q)) →
    (∃ g h, (q, g, h) ∈ w.gh ∧ krPairs (KindKlong K w g h) more) →
    WriterWP (up q more) c w (fun _ v => Book B c v ∧ KrInv K B v ∧ KrLe w v ∧ v.path = w.path)

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 20000 in
theorem kr_handleFullWith (K : KindOracle) (B : NodeId) (up : NodeId → List (Nat × NodeId) → M Unit)
    (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)) (last : KNode) (compact : Bool)
    (c : Ctx) (w : W) (hv : ViewIdsBelow B c.view) (hk : ViewKinds K B c) (hb : Book B c w)
    (hi : KrInv K B w) (g h : Nat) (hx : (x, g, h) ∈ w.gh) (a : Option Nat)
    (hpx : w.path[depth]? = some (a, x))
    (hlast : krKs (KindKlong K w g h) last.ks) (hins : krPairs (KindKlong K w g h) ins)
    (hup : ∀ e, depth = e + 1 → KrUp K B up e) :
    WriterWP (handleFullWith up depth x ins last compact) c w
      (fun _ v => Book B c v ∧ KrInv K B v ∧ KrLe w v ∧ v.path = w.path) := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (kr_getNode K B x c w hv hk hb hi) ?_
  rintro n w1 ⟨hb1, hi1, hle1, hl1, hp1, -⟩
  have hx1 := KrLe.gh' hx hle1
  have hnl : n.leaf = (h == 0) := kr_leaf hb1 hl1 hx1
  refine writerWP_mono (kr_ghOf K B x c w1 hv hk hb1 hi1) ?_
  rintro ⟨g', h'⟩ w2 ⟨hb2, hi2, hle2, hp2, -, hm2, -⟩
  obtain ⟨rfl, rfl⟩ := kr_tag_eq hb2 (KrLe.gh' hx1 hle2) hm2
  clear hm2
  refine writerWP_mono (kr_parentAt depth c w2) ?_
  rintro parent _ ⟨rfl, hpar0, hpar1⟩
  cases depth with
  | zero =>
    obtain rfl := hpar0 rfl
    clear hpar1 hup
    repeat' first
      | krSimp
      | krCore
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
      | krSimp
      | krK1 hpx hak
      | krStoreRep hqm hx hxk
      | krCore
      | krUpH hup' hpe0 hqm hx hxk
      | wpSplit
      | split
      | contradiction

/-! ## `appendKlongs` -/

theorem kr_addKeys (K : KindOracle) (B : NodeId) (x : NodeId) (ins : List (Nat × NodeId))
    (c : Ctx) (w : W) (hv : ViewIdsBelow B c.view) (hk : ViewKinds K B c) (hb : Book B c w)
    (hi : KrInv K B w) (g h : Nat) (hx : (x, g, h) ∈ w.gh)
    (hins : krPairs (KindKlong K w g h) ins) :
    WriterWP (addKeys x ins) c w
      (fun _ v => Book B c v ∧ KrInv K B v ∧ KrLe w v ∧ v.path = w.path) := by
  unfold addKeys
  krSimp
  refine writerWP_mono (kr_getNode K B x c w hv hk hb hi) ?_
  rintro n w1 ⟨hb1, hi1, hle1, hl1, hp1, -⟩
  refine writerWP_mono (kr_putNode K B x _ c w1 hb1 hi1 n hl1 (bk_foldl_add_leaf _ _ _) g h
    (KrLe.gh' hx hle1)
    (krKs_addFold _ (kr_cache_node hi1 hl1 (KrLe.gh' hx hle1)) (krPairs_mono hins hle1))) ?_
  rintro _ v ⟨hb2, hi2, hle2, hp2, -, -⟩
  exact ⟨hb2, hi2, hle1.trans hle2, hp2.trans hp1⟩

/-- `appendKlongs` at x, the path's node at `depth`, with klongs of the right
kind for x. -/
theorem kr_appendKlongs (K : KindOracle) (B : NodeId) (depth : Nat) :
    ∀ (x : NodeId) (ins : List (Nat × NodeId)) (c : Ctx) (w : W), ViewIdsBelow B c.view →
      ViewKinds K B c → Book B c w → KrInv K B w →
      (∃ g h, (x, g, h) ∈ w.gh ∧ krPairs (KindKlong K w g h) ins) →
      (∃ a, w.path[depth]? = some (a, x)) →
      WriterWP (appendKlongs depth x ins) c w
        (fun _ v => Book B c v ∧ KrInv K B v ∧ KrLe w v ∧ v.path = w.path) := by
  induction depth with
  | zero =>
    intro x ins c w hv hk hb hi ⟨g, h, hx, hins⟩ ⟨a, hpx⟩
    rw [appendKlongs_step_dead]
    krSimp
    refine writerWP_mono (kr_getNode K B x c w hv hk hb hi) ?_
    rintro n w1 ⟨hb1, hi1, hle1, hl1, hp1, -⟩
    have hx1 := KrLe.gh' hx hle1
    have hlv := krKs_lastVersion c.i (kr_cache_node hi1 hl1 hx1)
    have hpx1 : w1.path[0]? = some (a, x) := by rw [hp1]; exact hpx
    have hfin : ∀ cp, WriterWP (handleFullWith (fun _ _ => throw "corrupt: a split's parent above depth 0")
        0 x ins (n.lastVersion c.i) cp) c w1
        (fun _ v => Book B c w ∧ KrInv K B v ∧ KrLe w v ∧ v.path = w.path ∧ Book B c v) := by
      intro cp
      refine writerWP_mono (kr_handleFullWith K B _ 0 x ins _ cp c w1 hv hk hb1 hi1 g h hx1 a hpx1
        hlv (krPairs_mono hins hle1) (fun e he => by cases he)) ?_
      rintro _ v ⟨hb2, hi2, hle2, hp2⟩
      exact ⟨hb, hi2, hle1.trans hle2, hp2.trans hp1, hb2⟩
    split
    · exact writerWP_mono (hfin false) (fun _ v h => ⟨h.2.2.2.2, h.2.1, h.2.2.1, h.2.2.2.1⟩)
    · split
      · exact writerWP_mono (hfin true) (fun _ v h => ⟨h.2.2.2.2, h.2.1, h.2.2.1, h.2.2.2.1⟩)
      · refine writerWP_mono (kr_addKeys K B x ins c w1 hv hk hb1 hi1 g h hx1
          (krPairs_mono hins hle1)) ?_
        rintro _ v ⟨hb2, hi2, hle2, hp2⟩
        exact ⟨hb2, hi2, hle1.trans hle2, hp2.trans hp1⟩
  | succ d ih =>
    intro x ins c w hv hk hb hi ⟨g, h, hx, hins⟩ ⟨a, hpx⟩
    rw [appendKlongs_step_dead]
    krSimp
    refine writerWP_mono (kr_getNode K B x c w hv hk hb hi) ?_
    rintro n w1 ⟨hb1, hi1, hle1, hl1, hp1, -⟩
    have hx1 := KrLe.gh' hx hle1
    have hlv := krKs_lastVersion c.i (kr_cache_node hi1 hl1 hx1)
    have hpx1 : w1.path[d + 1]? = some (a, x) := by rw [hp1]; exact hpx
    have hup : ∀ e, d + 1 = e + 1 → KrUp K B (fun q more => appendKlongs d q more) e := by
      intro e he
      cases he
      intro q more c' w' hv' hk' hb' hi' hpq hmore
      exact ih q more c' w' hv' hk' hb' hi' hmore hpq
    have hfin : ∀ cp, WriterWP (handleFullWith (fun q more => appendKlongs d q more)
        (d + 1) x ins (n.lastVersion c.i) cp) c w1
        (fun _ v => Book B c v ∧ KrInv K B v ∧ KrLe w v ∧ v.path = w.path) := by
      intro cp
      refine writerWP_mono (kr_handleFullWith K B _ (d + 1) x ins _ cp c w1 hv hk hb1 hi1 g h hx1 a
        hpx1 hlv (krPairs_mono hins hle1) hup) ?_
      rintro _ v ⟨hb2, hi2, hle2, hp2⟩
      exact ⟨hb2, hi2, hle1.trans hle2, hp2.trans hp1⟩
    split
    · exact hfin false
    · split
      · exact hfin true
      · refine writerWP_mono (kr_addKeys K B x ins c w1 hv hk hb1 hi1 g h hx1
          (krPairs_mono hins hle1)) ?_
        rintro _ v ⟨hb2, hi2, hle2, hp2⟩
        exact ⟨hb2, hi2, hle1.trans hle2, hp2.trans hp1⟩

end SIS.Tree
