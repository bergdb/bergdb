/-
The heights walked through the writer (bergdb 024-22, step 4; TP7's (b)),
continued: the tactics of the walk, a full node's replacement
(`handleFullWith`), `addKeys` and `appendKlongs`.
-/
import SIS.Tree.WriterHeightsSplit

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

variable {H : NodeId → Nat → Prop}

/-! ## The steps with `HtLe` -/

section Wrap

variable (B : NodeId)

theorem hw_getNode (x : NodeId) (c : Ctx) (w : W) (hvo : ViewHtOK H B c) (hb : Book B c w)
    (hi : HtInv H B c w) :
    WriterWP (getNode x) c w (fun n v => Book B c v ∧ HtInv H B c v ∧ HtLe w v ∧
      v.nodes.lookup x = some n ∧ v.path = w.path) :=
  writerWP_mono (ht_getNode B x c w hvo hb hi)
    (fun _ _ h => ⟨h.1, h.2.1, ⟨h.2.2.1, h.2.2.2.2.2⟩, h.2.2.2.1, h.2.2.2.2.1⟩)

theorem hw_ghOf (x : NodeId) (c : Ctx) (w : W) (hvo : ViewHtOK H B c) (hb : Book B c w)
    (hi : HtInv H B c w) :
    WriterWP (ghOf x) c w (fun r v => Book B c v ∧ HtInv H B c v ∧ HtLe w v ∧
      v.path = w.path ∧ (x, r.1, r.2) ∈ v.gh ∧
      ∃ n, v.nodes.lookup x = some n ∧ n.leaf = (r.2 == 0)) :=
  writerWP_mono (ht_ghOf B x c w hvo hb hi)
    (fun _ _ h => ⟨h.1, h.2.1, ⟨h.2.2.1, h.2.2.2.2.1⟩, h.2.2.2.1, h.2.2.2.2.2⟩)

theorem hw_keeps {α : Type} {f : M α} (hf : HtKeeps B H f) (c : Ctx) (w : W)
    (hvo : ViewHtOK H B c) (hb : Book B c w) (hi : HtInv H B c w) :
    WriterWP f c w (fun _ v => Book B c v ∧ HtInv H B c v ∧ HtLe w v ∧ v.path = w.path) :=
  writerWP_mono (hf c w hvo hb hi)
    (fun _ _ h => ⟨h.1, h.2.1, ⟨h.2.2.1, h.2.2.2.2⟩, h.2.2.2.1⟩)

theorem ht_free_of_fresh {c : Ctx} {w : W} (hb : Book B c w) {x : NodeId}
    (hx : x ∉ w.gh.map (·.1)) : w.taken.contains x = false := by
  cases h : w.taken.contains x with
  | false => rfl
  | true =>
    have := hb.taken x (by simpa using h)
    exact absurd this hx

theorem hw_newKey (g h : Nat) (leaf : Bool) (ks : List Klong) (c : Ctx) (w : W)
    (hb : Book B c w) (hi : HtInv H B c w) (hleaf : leaf = (h == 0))
    (hks : NodeHt c H w h ⟨leaf, ks⟩) :
    WriterWP (newKey g h leaf ks) c w (fun x v => Book B c v ∧ HtInv H B c v ∧ HtLe w v ∧
      v.path = w.path ∧ v.nodes.lookup x = some ⟨leaf, ks⟩ ∧ (x, g, h) ∈ v.gh ∧
      v.taken.contains x = false ∧ x ∉ w.gh.map (·.1)) :=
  writerWP_mono (ht_newKey B g h leaf ks c w hb hi hleaf hks)
    (fun x v hh => ⟨hh.1, hh.2.1, ⟨hh.2.2.1, hh.2.2.2.2.1⟩, hh.2.2.2.1, hh.2.2.2.2.2.1,
      hh.2.2.2.2.2.2.1, by rw [hh.2.2.2.2.1]; exact ht_free_of_fresh B hb hh.2.2.2.2.2.2.2.2,
      hh.2.2.2.2.2.2.2.2⟩)

theorem hw_newSuperRoot (y : NodeId) (c : Ctx) (w : W) (hvo : ViewHtOK H B c) (hb : Book B c w)
    (hi : HtInv H B c w) (hy : w.taken.contains y = false) :
    WriterWP (newSuperRoot y) c w (fun _ v => Book B c v ∧ HtInv H B c v ∧ HtLe w v ∧
      v.path = w.path) :=
  writerWP_mono (ht_newSuperRoot B y c w hvo hb hi hy)
    (fun _ _ h => ⟨h.1, h.2.1, ⟨h.2.2.1, h.2.2.2.2⟩, h.2.2.2.1⟩)

theorem hw_counter (c : Ctx) (w : W) (f : W → W) (post : Unit → W → Prop)
    (hn : (f w).nodes = w.nodes) (hg : (f w).gh = w.gh) (hp : (f w).path = w.path)
    (ht : (f w).taken = w.taken) (htop : (f w).top.rootKey = w.top.rootKey)
    (hbk : ∀ {c : Ctx} {w : W}, Book B c w → Book B c (f w)) (hb : Book B c w)
    (hi : HtInv H B c w)
    (hq : ∀ v, Book B c v → HtInv H B c v → HtLe w v → v.path = w.path → post () v) :
    WriterWP (modify f) c w post :=
  ht_counter B c w f post hn hg hp ht htop hbk hb hi
    (fun v h1 h2 h3 h4 h5 => hq v h1 h2 ⟨h3, h5⟩ h4)

end Wrap

theorem ht_free_le {w v : W} {y : NodeId} (h : w.taken.contains y = false) (hle : HtLe w v) :
    v.taken.contains y = false := by rw [hle.2]; exact h

theorem ht_P_mk {c : Ctx} {v : W} {y : NodeId} {g h cv : Nat}
    (hy : v.taken.contains y = false) (hm : (y, g, h) ∈ v.gh) : HtP c H v (h + 1) cv y :=
  ⟨hy, fun _ => Or.inl ⟨g, by simpa using hm⟩⟩

/-- A pair for a parent of height hq, one above h, or a segment leaf. -/
theorem ht_P_par {c : Ctx} {v : W} {y : NodeId} {g h hq cv : Nat} (hqh : hq ≠ 0 → hq = h + 1)
    (hy : v.taken.contains y = false) (hm : (y, g, h) ∈ v.gh) : HtP c H v hq cv y := by
  refine ⟨hy, fun h0 => ?_⟩
  rw [hqh h0]
  exact Or.inl ⟨g, by simpa using hm⟩

/-- A node of the overlay read at an earlier state meets `NodeHt` for its height. -/
theorem ht_cache_at {B : NodeId} {c : Ctx} {vr v : W} {x : NodeId} {n : KNode} {g h : Nat}
    (hl : vr.nodes.lookup x = some n) (hi : HtInv H B c vr) (hm : (x, g, h) ∈ vr.gh)
    (hf : vr.taken.contains x = false) (hk : HtLe vr v) : NodeHt c H v h n :=
  (hi.cache x n g h (bk_mem_of_lookup _ _ _ hl) hm hf).htMono hk

/-- The key klongs of a node's last version are its live klongs. -/
theorem ht_lastVersion_key {n : KNode} {t : Time} {del : List Nat} {cv : Nat} {y : NodeId}
    (h : Klong.key cv y ∈ (n.lastVersionGivenDel t del).ks) :
    Klong.key cv y ∈ (n.lastVersionGivenDel 0 del).ks := by
  unfold KNode.lastVersionGivenDel at h ⊢
  simp only [List.mem_cons] at h ⊢
  rcases h with h | h
  · cases h
  · exact Or.inr h

theorem ht_mem_live_of_key {n : KNode} {cv : Nat} {y : NodeId}
    (h : Klong.key cv y ∈ (n.lastVersion 0).ks) : (cv, y) ∈ n.live := by
  unfold KNode.live
  exact List.mem_filterMap.mpr ⟨_, h, rfl⟩

/-- A node's last version has the klongs of the right height of a node that
meets `NodeHt`. -/
theorem htKs_lastVersion {c : Ctx} {w : W} {h : Nat} {n : KNode} (hn : NodeHt c H w h n) (t : Time) :
    kdKs (HtP c H w h) (n.lastVersion t).ks := by
  intro cv y hm
  exact hn.1 cv y (ht_mem_live_of_key (ht_lastVersion_key hm))

/-! ## The tactics of the walk -/

/-- `HtLe a b` along the chain of the steps' hypotheses `HtLe v1 v2`. -/
syntax "htChain" : tactic
macro_rules
  | `(tactic| htChain) => `(tactic| first
    | exact HtLe.refl _
    | assumption
    | (refine HtLe.trans ?htL (by assumption); htChain))

syntax "htPathEq" : tactic
macro_rules
  | `(tactic| htPathEq) => `(tactic| first
    | rfl
    | assumption
    | (refine Eq.trans (by assumption) ?htP; htPathEq))

macro "htTag" : tactic => `(tactic| first
  | assumption
  | exact HtLe.gh' (by assumption) (by htChain))

macro "htFree" : tactic => `(tactic| first
  | assumption
  | exact ht_free_le (by assumption) (by htChain))

macro "htState" : tactic => `(tactic| first
  | assumption
  | exact book_spaceSplits (by assumption) _
  | exact book_merges (by assumption) _)

macro "htNode" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (getNode _) _ _ _)
  (refine writerWP_mono (hw_getNode (H := ?htO) ?htB _ _ _ ?htView ?htBook ?htInv) ?htPost)
  case htView => assumption
  case htBook => htState
  case htInv => assumption
  rintro _ _ ⟨_, _, _, _, _⟩))

macro "htGh" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (ghOf _) _ _ _)
  (refine writerWP_mono (hw_ghOf (H := ?htO) ?htB _ _ _ ?htView ?htBook ?htInv) ?htPost)
  case htView => assumption
  case htBook => htState
  case htInv => assumption
  rintro ⟨_, _⟩ _ ⟨_, _, _, _, _, _⟩))

macro "htRead" : tactic => `(tactic| first
  | ((with_unfolding_none guard_target = WriterWP pathSize _ _ _)
     refine writerWP_mono (kd_pathSize _ _) ?htPost
     rintro _ _ ⟨hhtEq, _⟩
     subst hhtEq)
  | ((with_unfolding_none guard_target = WriterWP (pathNode _) _ _ _)
     refine writerWP_mono (kd_pathNode _ _ _) ?htPost
     rintro _ _ ⟨hhtEq, _⟩
     subst hhtEq)
  | ((with_unfolding_none guard_target = WriterWP (replacedBy _) _ _ _)
     refine writerWP_mono (kd_replacedBy _ _ _) ?htPost
     rintro _ _ ⟨hhtEq, _⟩
     subst hhtEq))

macro "htCnt" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (modify _) _ _ _)
  (refine hw_counter (H := ?htO) ?htB _ _ _ _ rfl rfl rfl rfl rfl ?htBk ?htBook ?htInv ?htPost)
  case htBk => intro _ _ hbk; first | exact book_spaceSplits hbk _ | exact book_merges hbk _
  case htBook => htState
  case htInv => assumption
  intro _ _ _ _ _))

macro "htUse " h:term : tactic => `(tactic| (
  (with_unfolding_none refine writerWP_mono (hw_keeps (H := ?htO) ?htB $h _ _ ?htView ?htBook ?htInv) ?htPost)
  case htView => assumption
  case htBook => htState
  case htInv => assumption
  rintro _ _ ⟨_, _, _, _⟩))

macro "htDone" : tactic => `(tactic| (
  (with_unfolding_none guard_target = Book _ _ _ ∧ HtInv _ _ _ _ ∧ HtLe _ _ ∧ _)
  refine ⟨by htState, by assumption, by htChain, by htPathEq⟩))

/-- Klongs of the right height for a node's entry. -/
syntax "htNodeTac" : tactic
macro_rules
  | `(tactic| htNodeTac) => `(tactic| first
    | ((with_unfolding_none guard_target = NodeHt _ _ _ _ ⟨_, []⟩)
       exact nodeHt_nil _ _ _ _)
    | ((with_unfolding_none guard_target = NodeHt _ _ _ _ (halves _ _ _ _).1)
       exact (nodeHt_halves (by assumption) _ _ _ (htKs_mono (by assumption) (by htChain))
        (htPairs_mono (by assumption) (by htChain)) (by assumption)).1)
    | ((with_unfolding_none guard_target = NodeHt _ _ _ _ (halves _ _ _ _).2.1)
       exact (nodeHt_halves (by assumption) _ _ _ (htKs_mono (by assumption) (by htChain))
        (htPairs_mono (by assumption) (by htChain)) (by assumption)).2)
    | ((with_unfolding_none guard_target = NodeHt _ _ _ _ ⟨false, [.time _, .key 0 _, .key _ _]⟩)
       exact nodeHt_root (by assumption) _ (ht_P_mk (by htFree) (by htTag))
        (ht_P_mk (by htFree) (by htTag)))
    | ((with_unfolding_none guard_target = NodeHt _ _ _ _ (KNode.toPrev _ _))
       exact nodeHt_toPrev (ht_cache_at (by assumption) (by assumption) (by htTag) (by htFree)
        (by htChain)))
    | exact nodeHt_flat (by assumption) (by assumption) (htKs_mono (by assumption) (by htChain)))

macro "htStore" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (putNode _ _) _ _ _)
  (refine writerWP_mono (ht_putNode_of (H := ?htO) ?htB _ _ _ ?htVr ?htVt _ ?htN ?htBook ?htInv ?htLook ?htKr ?htLeaf ?htG ?htH ?htTagM ?htKt ?htKs) ?htPost)
  case htBook => htState
  case htInv => assumption
  case htLook => assumption
  case htKr => htChain
  case htLeaf => bkLeaf
  case htTagM => assumption
  case htKt => htChain
  case htKs => htNodeTac
  rintro _ _ ⟨_, _, _, _, _⟩))

macro "htCreate" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (newKey _ _ _ _) _ _ _)
  (refine writerWP_mono (hw_newKey (H := ?htO) ?htB _ _ _ _ _ _ ?htBook ?htInv ?htH ?htKs) ?htPost)
  case htBook => htState
  case htInv => assumption
  case htH => kdHeight
  case htKs => htNodeTac
  rintro _ _ ⟨_, _, _, _, _, _, _, _⟩))

macro "htSuper" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (newSuperRoot _) _ _ _)
  (refine writerWP_mono (hw_newSuperRoot (H := ?htO) ?htB _ _ _ ?htView ?htBook ?htInv ?htY) ?htPost)
  case htView => assumption
  case htBook => htState
  case htInv => assumption
  case htY => htFree
  rintro _ _ ⟨_, _, _, _⟩))

macro "htCore" : tactic => `(tactic| first
  | htDone
  | htNode
  | htGh
  | htRead
  | htStore
  | htCreate
  | htSuper
  | htUse (ht_setMadeFor _ _ _)
  | htUse (ht_note _ _)
  | htUse (ht_fresh _)
  | htCnt
  | exact writerWP_throw _ _ _ _)

theorem ht_P_zero {c : Ctx} {v : W} {y : NodeId} {hq cv : Nat}
    (hy : v.taken.contains y = false) (h0 : hq = 0) : HtP c H v hq cv y :=
  ⟨hy, fun h' => absurd h0 h'⟩

theorem ht_hq_zero {B : NodeId} {c : Ctx} {vr : W} {q : NodeId} {pn : KNode} {gq hq : Nat}
    (hf : pn.leaf = true) (hl : vr.nodes.lookup q = some pn) (hb : Book B c vr)
    (hm : (q, gq, hq) ∈ vr.gh) : hq = 0 := by
  have := kd_leaf hb hl hm
  rw [hf] at this
  cases hq with
  | zero => rfl
  | succ k => simp at this

theorem ht_ptr_mem' {n : KNode} {i : Nat} {y : NodeId} (h : n.ptr? i = some y) :
    ∃ cv, n.ks[i]? = some (.key cv y) := kd_ptr_mem h

/-- What `appendKlongs` one level up does for `handleFullWith`: for the parent
q, the path's node at depth d, and klongs of the right height for it, it keeps
the state and the path. -/
def HtUp (H : NodeId → Nat → Prop) (B : NodeId) (up : NodeId → List (Nat × NodeId) → M Unit) (d : Nat) : Prop :=
  ∀ q more c w, ViewHtOK H B c → 0 < c.i → Book B c w → HtInv H B c w →
    (∃ a, w.path[d]? = some (a, q)) →
    (∃ g h, (q, g, h) ∈ w.gh ∧ kdPairs (HtP c H w h) more) →
    WriterWP (up q more) c w (fun _ v => Book B c v ∧ HtInv H B c v ∧ HtLe w v ∧ v.path = w.path)

macro "htK1 " hpx:term:max hak:term:max : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (klongAt _) _ _ _)
  refine writerWP_mono (kd_klongAt _ _ _) ?htPost
  rintro _ _ ⟨hhtEq, _, hhtY⟩
  subst hhtEq
  have hhtK := kd_k1_eq $hpx $hak hhtY (by htPathEq)
  subst hhtK))

macro "htUpP " hup:term:max hpe:term:max hqm:term:max hqh:term:max : tactic => `(tactic| (
  (refine writerWP_mono ($hup _ _ _ _ ?htView ?htPos ?htBook ?htInv ?htPathQ ?htMore) ?htPost)
  case htView => assumption
  case htPos => assumption
  case htBook => htState
  case htInv => assumption
  case htPathQ => exact ⟨_, kd_path_at $hpe (by htPathEq)⟩
  case htMore =>
    refine ⟨_, _, HtLe.gh' $hqm (by htChain), ?htPairs⟩
    repeat' (first | exact kdPairs_nil' | refine kdPairs_cons ?_ ?_)
    all_goals exact ht_P_par $hqh (by htFree) (by htTag)
  rintro _ _ ⟨_, _, _, _⟩))

macro "htUpZ " hup:term:max hpe:term:max hqm:term:max hq0:term:max : tactic => `(tactic| (
  (refine writerWP_mono ($hup _ _ _ _ ?htView ?htPos ?htBook ?htInv ?htPathQ ?htMore) ?htPost)
  case htView => assumption
  case htPos => assumption
  case htBook => htState
  case htInv => assumption
  case htPathQ => exact ⟨_, kd_path_at $hpe (by htPathEq)⟩
  case htMore =>
    refine ⟨_, _, HtLe.gh' $hqm (by htChain), ?htPairs⟩
    repeat' (first | exact kdPairs_nil' | refine kdPairs_cons ?_ ?_)
    all_goals exact ht_P_zero (by htFree) $hq0
  rintro _ _ ⟨_, _, _, _⟩))

/-- The store of the segment leaf's klong of x pointed to x's replacement. -/
macro "htStoreRep " hqm:term:max hq0:term:max : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (putNode _ (KNode.repoint _ _ _)) _ _ _)
  (refine writerWP_mono (ht_putNode_of (H := ?htO) ?htB _ _ _ ?htVr _ _ ?htN ?htBook ?htInv ?htLook ?htKr ?htLeaf _ _ $hqm ?htKt ?htKs) ?htPost)
  case htBook => htState
  case htInv => assumption
  case htLook => assumption
  case htKr => htChain
  case htLeaf => bkLeaf
  case htKt => htChain
  case htKs =>
    exact nodeHt_repoint (ht_cache_at (by assumption) (by assumption) (HtLe.gh' $hqm (by htChain))
      (by htFree) (by htChain)) _ _ (fun _ => ht_P_zero (by htFree) $hq0)
  rintro _ _ ⟨_, _, _, _, _⟩))

theorem ht_hq_zero2 {B : NodeId} {c : Ctx} {vr : W} {q : NodeId} {pn : KNode} {gq hq : Nat}
    (hl : vr.nodes.lookup q = some pn) (hb : Book B c vr) (hm : (q, gq, hq) ∈ vr.gh)
    (hf : pn.leaf = true) : hq = 0 := ht_hq_zero hf hl hb hm

macro "htSimp" : tactic => `(tactic|
  simp only [writerWP_bind, writerWP_read, writerWP_get, writerWP_pure])

macro "htRepl" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (replaceOrAdd _ _) _ _ _)
  (refine writerWP_mono (ht_replaceOrAdd _ _ _ _ _ (htKs_mono (by assumption) (by htChain))
    (htPairs_mono (by assumption) (by htChain)) (by assumption)) ?htPost)
  rintro _ _ ⟨hhtEq, _, _⟩
  subst hhtEq))

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 20000 in
/-- A full node's replacement keeps the heights, for x the path's node at
depth and a last version and klongs of the right height for x. -/
theorem ht_handleFullWith (B : NodeId) (up : NodeId → List (Nat × NodeId) → M Unit)
    (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)) (last : KNode) (compact : Bool)
    (c : Ctx) (w : W) (hvo : ViewHtOK H B c) (hpos : 0 < c.i) (hb : Book B c w)
    (hi : HtInv H B c w) (g h : Nat) (hx : (x, g, h) ∈ w.gh) (a : Option Nat)
    (hpx : w.path[depth]? = some (a, x)) (hflat : FlatAt c.i last.ks)
    (hlast : kdKs (HtP c H w h) last.ks) (hins : kdPairs (HtP c H w h) ins)
    (hup : ∀ e, depth = e + 1 → HtUp H B up e) :
    WriterWP (handleFullWith up depth x ins last compact) c w
      (fun _ v => Book B c v ∧ HtInv H B c v ∧ HtLe w v ∧ v.path = w.path) := by
  have hxf : w.taken.contains x = false := hi.pathFree depth a x hpx
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (hw_getNode B x c w hvo hb hi) ?_
  rintro n w1 ⟨hb1, hi1, hle1, hl1, hp1⟩
  have hx1 := HtLe.gh' hx hle1
  have hnl : n.leaf = (h == 0) := kd_leaf hb1 hl1 hx1
  refine writerWP_mono (hw_ghOf B x c w1 hvo hb1 hi1) ?_
  rintro ⟨g', h'⟩ w2 ⟨hb2, hi2, hle2, hp2, hm2, -⟩
  obtain ⟨rfl, rfl⟩ := kd_tag_eq hb2 (HtLe.gh' hx1 hle2) hm2
  clear hm2
  refine writerWP_mono (kd_parentAt depth c w2) ?_
  rintro parent _ ⟨rfl, hpar0, hpar1⟩
  cases depth with
  | zero =>
    obtain rfl := hpar0 rfl
    clear hpar1 hup
    repeat' first
      | htSimp
      | htCore
      | htRepl
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
    have hqf : w.taken.contains q' = false := hi.pathFree e a' q' hpe0
    obtain ⟨k, hak⟩ : ∃ k, a = some k := by
      cases a with
      | none => exact absurd rfl (hi.pathSome e none x hpx)
      | some k => exact ⟨k, rfl⟩
    have hqh : hq ≠ 0 → hq = h + 1 := by
      intro h0
      have hh := hi.path e a' q' k x hpe0 (by rw [hpx, hak]) gq hq hqm hqf h0
      have := hasHt_tag hb hvo.heights hx hh
      omega
    have hup' := hup e rfl
    clear hup
    by_cases hq0 : hq = 0
    · repeat' first
        | htSimp
        | htK1 hpx hak
        | htStoreRep hqm hq0
        | htCore
        | htRepl
        | htUpZ hup' hpe0 hqm hq0
        | wpSplit
        | split
        | contradiction
    · repeat' first
        | exact absurd (ht_hq_zero2 (q := q') (by assumption) (by htState) (HtLe.gh' hqm (by htChain))
            (by assumption)) hq0
        | htSimp
        | htK1 hpx hak
        | htCore
        | htRepl
        | htUpP hup' hpe0 hqm hqh
        | wpSplit
        | split
        | contradiction

/-! ## `appendKlongs` -/

theorem ht_addKeys (B : NodeId) (x : NodeId) (ins : List (Nat × NodeId))
    (c : Ctx) (w : W) (hvo : ViewHtOK H B c) (hpos : 0 < c.i) (hb : Book B c w)
    (hi : HtInv H B c w) (g h : Nat) (hx : (x, g, h) ∈ w.gh) (hxf : w.taken.contains x = false)
    (hins : kdPairs (HtP c H w h) ins) :
    WriterWP (addKeys x ins) c w
      (fun _ v => Book B c v ∧ HtInv H B c v ∧ HtLe w v ∧ v.path = w.path) := by
  unfold addKeys
  htSimp
  refine writerWP_mono (hw_getNode B x c w hvo hb hi) ?_
  rintro n w1 ⟨hb1, hi1, hle1, hl1, hp1⟩
  have hx1 := HtLe.gh' hx hle1
  refine writerWP_mono (ht_putNode_of B x _ c w1 w1 w1 n hb1 hi1 hl1 (HtLe.refl _)
    (bk_foldl_add_leaf _ _ _) g h hx1 (HtLe.refl _)
    (nodeHt_addFold hpos (ht_cache_at hl1 hi1 hx1 (ht_free_le hxf hle1) (HtLe.refl _)) ins
      (htPairs_mono hins hle1))) ?_
  rintro _ v ⟨hb2, hi2, hle2, hp2, -⟩
  exact ⟨hb2, hi2, hle1.trans hle2, hp2.trans hp1⟩

/-- `appendKlongs` at x, the path's node at `depth`, with klongs of the right
height for x. -/
theorem ht_appendKlongs (B : NodeId) (depth : Nat) :
    ∀ (x : NodeId) (ins : List (Nat × NodeId)) (c : Ctx) (w : W), ViewHtOK H B c → 0 < c.i →
      Book B c w → HtInv H B c w →
      (∃ g h, (x, g, h) ∈ w.gh ∧ kdPairs (HtP c H w h) ins) →
      (∃ a, w.path[depth]? = some (a, x)) →
      WriterWP (appendKlongs depth x ins) c w
        (fun _ v => Book B c v ∧ HtInv H B c v ∧ HtLe w v ∧ v.path = w.path) := by
  induction depth with
  | zero =>
    intro x ins c w hvo hpos hb hi ⟨g, h, hx, hins⟩ ⟨a, hpx⟩
    have hxf : w.taken.contains x = false := hi.pathFree 0 a x hpx
    rw [appendKlongs_step_dead]
    htSimp
    refine writerWP_mono (hw_getNode B x c w hvo hb hi) ?_
    rintro n w1 ⟨hb1, hi1, hle1, hl1, hp1⟩
    have hx1 := HtLe.gh' hx hle1
    have hN := ht_cache_at hl1 hi1 hx1 (ht_free_le hxf hle1) (HtLe.refl _)
    have hlv := htKs_lastVersion hN c.i
    have hpx1 : w1.path[0]? = some (a, x) := by rw [hp1]; exact hpx
    have hfin : ∀ cp, WriterWP (handleFullWith (fun _ _ => throw "corrupt: a split's parent above depth 0")
        0 x ins (n.lastVersion c.i) cp) c w1
        (fun _ v => Book B c v ∧ HtInv H B c v ∧ HtLe w v ∧ v.path = w.path) := by
      intro cp
      refine writerWP_mono (ht_handleFullWith B _ 0 x ins _ cp c w1 hvo hpos hb1 hi1 g h hx1 a hpx1
        (KNode.lastVersion_flatAt n c.i) hlv (htPairs_mono hins hle1) (fun e he => by cases he)) ?_
      rintro _ v ⟨hb2, hi2, hle2, hp2⟩
      exact ⟨hb2, hi2, hle1.trans hle2, hp2.trans hp1⟩
    split
    · exact hfin false
    · split
      · exact hfin true
      · refine writerWP_mono (ht_addKeys B x ins c w1 hvo hpos hb1 hi1 g h hx1
          (ht_free_le hxf hle1) (htPairs_mono hins hle1)) ?_
        rintro _ v ⟨hb2, hi2, hle2, hp2⟩
        exact ⟨hb2, hi2, hle1.trans hle2, hp2.trans hp1⟩
  | succ d ih =>
    intro x ins c w hvo hpos hb hi ⟨g, h, hx, hins⟩ ⟨a, hpx⟩
    have hxf : w.taken.contains x = false := hi.pathFree (d + 1) a x hpx
    rw [appendKlongs_step_dead]
    htSimp
    refine writerWP_mono (hw_getNode B x c w hvo hb hi) ?_
    rintro n w1 ⟨hb1, hi1, hle1, hl1, hp1⟩
    have hx1 := HtLe.gh' hx hle1
    have hN := ht_cache_at hl1 hi1 hx1 (ht_free_le hxf hle1) (HtLe.refl _)
    have hlv := htKs_lastVersion hN c.i
    have hpx1 : w1.path[d + 1]? = some (a, x) := by rw [hp1]; exact hpx
    have hup : ∀ e, d + 1 = e + 1 → HtUp H B (fun q more => appendKlongs d q more) e := by
      intro e he
      cases he
      intro q more c' w' hvo' hpos' hb' hi' hpq hmore
      exact ih q more c' w' hvo' hpos' hb' hi' hmore hpq
    have hfin : ∀ cp, WriterWP (handleFullWith (fun q more => appendKlongs d q more)
        (d + 1) x ins (n.lastVersion c.i) cp) c w1
        (fun _ v => Book B c v ∧ HtInv H B c v ∧ HtLe w v ∧ v.path = w.path) := by
      intro cp
      refine writerWP_mono (ht_handleFullWith B _ (d + 1) x ins _ cp c w1 hvo hpos hb1 hi1 g h hx1 a
        hpx1 (KNode.lastVersion_flatAt n c.i) hlv (htPairs_mono hins hle1) hup) ?_
      rintro _ v ⟨hb2, hi2, hle2, hp2⟩
      exact ⟨hb2, hi2, hle1.trans hle2, hp2.trans hp1⟩
    split
    · exact hfin false
    · split
      · exact hfin true
      · refine writerWP_mono (ht_addKeys B x ins c w1 hvo hpos hb1 hi1 g h hx1
          (ht_free_le hxf hle1) (htPairs_mono hins hle1)) ?_
        rintro _ v ⟨hb2, hi2, hle2, hp2⟩
        exact ⟨hb2, hi2, hle1.trans hle2, hp2.trans hp1⟩

end SIS.Tree
