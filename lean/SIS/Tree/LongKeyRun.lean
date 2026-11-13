import SIS.Tree.FreshCache
import SIS.Tree.KeyWellFormed
import SIS.Tree.ScanFuelBound
import SIS.Tree.InvInit

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- Arbitrarily long representable keys, with a final empty segment. -/
def longKey : Nat → Key
  | 0 => [0]
  | n + 1 => 56 :: longKey n

theorem longKey_ne_nil (n : Nat) : longKey n ≠ [] := by cases n <;> simp [longKey]

theorem longKey_length (n : Nat) : (longKey n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [longKey, List.length_cons, ih]

theorem longKey_wf (n : Nat) : keyWf (longKey n) = true := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
    cases n with
    | zero => decide +kernel
    | succ n =>
      change keyWf (56 :: 56 :: longKey n) = true
      exact (keyWf_cons_cons 56 56 (longKey n)).mpr
        ⟨by decide, by decide, by decide, ih⟩

macro "runPure" : tactic => `(tactic|
  simp only [ReaderT.run, StateT.run, bind, ReaderT.bind, StateT.bind, Except.bind,
    pure, ReaderT.pure, StateT.pure, Except.pure,
    read, readThe, MonadReaderOf.read, ReaderT.read,
    get, MonadState.get, getThe, MonadStateOf.get, StateT.get,
    set, MonadStateOf.set, StateT.set,
    modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
    liftM, monadLift, MonadLift.monadLift])

theorem getNode_cached_run (c : Ctx) (w : W) (x : NodeId) (n : KNode)
    (hn : w.nodes.lookup x = some n) : getNode x c w = .ok (n, w) := by
  unfold getNode
  runPure
  simp only [hn]
  rfl

theorem descendLte_cached_leaf_run (c : Ctx) (w : W) (x : NodeId) (n : KNode)
    (hn : w.nodes.lookup x = some n) (hleaf : n.leaf = true) (cv f : Nat) :
    descendLte cv (f + 1) x c w = .ok (x, w) := by
  unfold descendLte
  runPure
  rw [getNode_cached_run c w x n hn]
  simp only [Except.bind, hleaf, ↓reduceIte]
  rfl

theorem ghOf_cached_run (c : Ctx) (w : W) (x : NodeId) (n : KNode) (g h : Nat)
    (hn : w.nodes.lookup x = some n) (hg : w.gh.lookup x = some (g, h)) :
    ghOf x c w = .ok ((g, h), w) := by
  unfold ghOf
  runPure
  rw [getNode_cached_run c w x n hn]
  runPure
  simp only [hg]
  rfl

/-- The result of extending an empty segment path by a fresh leaf. -/
def longKeyStep (c : Ctx) (w : W) (x : NodeId) (n : KNode) (g cv : Nat) : W :=
  { w with
    nodes := upsert (w.nodes ++ [(w.next, ⟨true, []⟩)]) x (n.add c.i (.key cv w.next))
    gh := (w.next, g + 1, 0) :: w.gh
    made := w.made ++ [⟨w.next, c.p.keyLevel (g + 1) 0, false⟩]
    next := w.next + 2
    trail := "segment.new" :: w.trail }

theorem setNode_fresh_run (c : Ctx) (w : W) (x : NodeId) (n : KNode) (g cv : Nat)
    (hn : w.nodes.lookup x = some n) (hleaf : n.leaf = true)
    (hg : w.gh.lookup x = some (g, 0)) (hsearch : n.searchEq c.i cv = none)
    (hroom : n.size + 1 < c.p.M) (hlevel : g + 1 ≤ c.p.G) :
    setNode x cv true c w = .ok (some w.next, longKeyStep c w x n g cv) := by
  unfold setNode
  runPure
  have hf : 0 < c.p.fuel := by
    unfold Params.fuel
    omega
  cases hfu : c.p.fuel with
  | zero => omega
  | succ f =>
    rw [descendLte_cached_leaf_run c w x n hn hleaf cv f]
    simp only [Except.bind]
    rw [getNode_cached_run c w x n hn]
    simp only [Except.bind, hsearch, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    runPure
    rw [ghOf_cached_run c w x n g 0 hn hg]
    simp only [Except.bind]
    unfold note newKey fresh putNode
    runPure
    simp only [Nat.not_lt_of_ge hlevel, Nat.not_lt_zero, decide_false, Bool.false_or,
      Bool.false_eq_true, ↓reduceIte, hroom]
    rfl

theorem longKeyStep_ready (c : Ctx) (w : W) (x : NodeId) (n : KNode) (g cv : Nat)
    (hw : FreshCache 0 w) (hx : x < w.next) :
    FreshCache 0 (longKeyStep c w x n g cv) ∧
      (longKeyStep c w x n g cv).nodes.lookup w.next = some ⟨true, []⟩ ∧
      (longKeyStep c w x n g cv).gh.lookup w.next = some (g + 1, 0) := by
  have hnone : w.nodes.lookup w.next = none := by
    cases hh : w.nodes.lookup w.next with
    | none => rfl
    | some found => have hlt := freshCache_lookup_lt 0 w hw w.next found hh; omega
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨by simp [longKeyStep], ?_, ?_, ?_⟩
    · apply upsert_ids_below
      · intro q hq
        rcases List.mem_append.mp hq with hq | hq
        · have hlt := hw.2.1 q hq
          change q.1 < w.next + 2
          omega
        · have he : q = (w.next, ⟨true, []⟩) := List.mem_singleton.mp hq
          subst q
          change w.next < w.next + 2
          omega
      · change x < w.next + 2
        omega
    · intro q hq
      change q ∈ (w.next, g + 1, 0) :: w.gh at hq
      rcases List.mem_cons.mp hq with rfl | hq
      · change w.next < w.next + 2
        omega
      · have hlt := hw.2.2.1 q hq
        change q.1 < w.next + 2
        omega
    · intro y hy
      have hlt := hw.2.2.2 y hy
      change y < w.next + 2
      omega
  · change (upsert (w.nodes ++ [(w.next, ⟨true, []⟩)]) x _).lookup w.next = _
    rw [upsert_lookup_other _ w.next x _ (by omega)]
    simp [List.lookup_append, hnone]
  · simp [longKeyStep]

def longKeyFinish (c : Ctx) (w : W) (x : NodeId) (n : KNode) (cv value : Nat) : W :=
  { w with
    nodes := upsert w.nodes x (n.add c.i (.key cv w.next)),
    vals := w.vals ++ [(w.next, value)],
    made := w.made ++ [⟨w.next, 0, true⟩],
    next := w.next + 2 }

theorem setValue_cached_put_run (c : Ctx) (w : W) (x : NodeId) (n : KNode)
    (hn : w.nodes.lookup x = some n) (hleaf : n.leaf = true)
    (hroom : n.size + 1 < c.p.M) (hTheta : c.p.theta = 0)
    (cv value : Nat) (key : Key) :
    setValue x cv key (some value) c w = .ok (false, longKeyFinish c w x n cv value) := by
  unfold setValue
  runPure
  have hf : 0 < c.p.fuel := by unfold Params.fuel; omega
  cases hfu : c.p.fuel with
  | zero => omega
  | succ f =>
    rw [descendLte_cached_leaf_run c w x n hn hleaf cv f]
    runPure
    unfold newValue fresh
    runPure
    let after : W := { w with
      next := w.next + 2, vals := w.vals ++ [(w.next, value)],
      made := w.made ++ [⟨w.next, 0, true⟩] }
    have hload := getNode_cached_run c after x n (show after.nodes.lookup x = some n from hn)
    rw [hload]
    runPure
    simp only [hroom, deadOver, hTheta, beq_self_eq_true, Bool.not_true,
      Bool.false_and, Bool.not_false, Bool.true_and, ↓reduceIte]
    unfold putNode
    runPure
    rfl

theorem putSegs_nonterminal (key : Key) (value : Option Nat) (cv : Nat) (rest : Key)
    (hne : rest ≠ []) (x : NodeId) :
    putSegs key value (cv :: rest) x = (do
      match ← setNode x cv value.isSome with
      | none => pure true
      | some y => putSegs key value rest y) := by
  cases rest with
  | nil => exact (hne rfl).elim
  | cons c rest => rfl

/-- Inserting this key along an empty path succeeds at every finite depth;
its intermediate segment nodes stay inside the supplied level bound. -/
theorem putSegs_longKey_empty_success (c : Ctx) (key : Key) (value n : Nat)
    (w : W) (x g : Nat) (hw : FreshCache 0 w)
    (hn : w.nodes.lookup x = some ⟨true, []⟩)
    (hg : w.gh.lookup x = some (g, 0))
    (hM : 2 ≤ c.p.M) (hTheta : c.p.theta = 0) (hG : g + n ≤ c.p.G) :
    ∃ v, putSegs key (some value) (longKey n) x c w = .ok (false, v) ∧
      v.outside = w.outside := by
  induction n generalizing w x g with
  | zero =>
    refine ⟨longKeyFinish c w x ⟨true, []⟩ 0 value, ?_, rfl⟩
    exact setValue_cached_put_run c w x ⟨true, []⟩ hn rfl (by change 1 < c.p.M; omega)
      hTheta 0 value key
  | succ n ih =>
    have hx := freshCache_lookup_lt 0 w hw x ⟨true, []⟩ hn
    let v := longKeyStep c w x ⟨true, []⟩ g 56
    obtain ⟨hv, hnode, hgh⟩ := longKeyStep_ready c w x ⟨true, []⟩ g 56 hw hx
    obtain ⟨u, hrun, hout⟩ := ih v w.next (g + 1) hv hnode hgh (by omega)
    refine ⟨u, ?_, hout⟩
    rw [longKey, putSegs_nonterminal key (some value) 56 (longKey n) (longKey_ne_nil n)]
    runPure
    simp only [Option.isSome_some]
    rw [setNode_fresh_run c w x ⟨true, []⟩ g 56 hn rfl hg (by rfl)
      (by change 1 < c.p.M; omega) (by omega)]
    runPure
    exact hrun

theorem putSegs_longKey_initial_success (c : Ctx) (key : Key) (value len : Nat)
    (w : W) (x g : Nat) (n : KNode) (hw : FreshCache 0 w)
    (hn : w.nodes.lookup x = some n) (hleaf : n.leaf = true)
    (hg : w.gh.lookup x = some (g, 0)) (hsearch : n.searchEq c.i 56 = none)
    (hroom : n.size + 1 < c.p.M) (hTheta : c.p.theta = 0) (hG : g + len ≤ c.p.G) :
    ∃ v, putSegs key (some value) (longKey len) x c w = .ok (false, v) ∧
      v.outside = w.outside := by
  cases len with
  | zero => exact ⟨_, setValue_cached_put_run c w x n hn hleaf hroom hTheta 0 value key, rfl⟩
  | succ len =>
    have hx := freshCache_lookup_lt 0 w hw x n hn
    let v := longKeyStep c w x n g 56
    obtain ⟨hv, hnode, hgh⟩ := longKeyStep_ready c w x n g 56 hw hx
    obtain ⟨u, hrun, hout⟩ := putSegs_longKey_empty_success c key value len v w.next (g + 1)
      hv hnode hgh (by omega) hTheta (by omega)
    refine ⟨u, ?_, hout⟩
    rw [longKey, putSegs_nonterminal key (some value) 56 (longKey len) (longKey_ne_nil len)]
    runPure
    simp only [Option.isSome_some]
    rw [setNode_fresh_run c w x n g 56 hn hleaf hg hsearch hroom (by omega)]
    runPure
    exact hrun

theorem view_initial_eq_viewOf (p : Params) :
    view (treeSpec p) (initStruct p) 0 = viewOf (initStruct p) := by
  funext x
  simp only [view, reachable, init_reach]
  by_cases h0 : x = 0
  · subst x
    simp [viewOf, initStruct, Struct.get?, root, History.upTo, List.lookup_cons]
  by_cases h1 : x = 1
  · subst x
    simp [viewOf, initStruct, Struct.get?, root, History.upTo, List.lookup_cons]
  by_cases h2 : x = 2
  · subst x
    simp [viewOf, initStruct, Struct.get?, root, History.upTo, List.lookup_cons]
  simp [viewOf, initStruct, Struct.get?, root, h0, h1, h2, List.lookup_cons]
  simp only [beq_eq_false_iff_ne.mpr h0, beq_eq_false_iff_ne.mpr h1,
    beq_eq_false_iff_ne.mpr h2]

def longKeyParams (n : Nat) : Params := ({ M := 8, G := n, H := 0 } : Params).withMerges

def longKeyTx (n : Nat) : Tx := { base := 100, ops := [.put (longKey n) 1] }

def longKeyTop : Top := ⟨2, 0, 0, 1, []⟩

def longKeyLoaded : W :=
  { next := 100, top := longKeyTop, path := [(none, 1)],
    nodes := [(1, ⟨true, [.time 0]⟩)], gh := [(1, 0, 0)] }

def longKeyCtx (len : Nat) : Ctx :=
  { p := longKeyParams len, i := 1,
    view := rootless (viewOf (initStruct (longKeyParams len))) }

theorem getNode_initial_load_run (len : Nat) :
    getNode 1 (longKeyCtx len)
      { next := 100, top := longKeyTop, path := [(none, 1)] } =
      .ok (⟨true, [.time 0]⟩, longKeyLoaded) := by
  unfold getNode
  runPure
  simp only [List.lookup_nil]
  runPure
  simp [longKeyCtx, rootless, viewOf, init_get_key, root, longKeyParams, Params.withMerges,
    Params.keyMax, Params.keyLevel, Params.heightOf, Params.segOf, klongsOf, marker,
    longKeyLoaded]
  runPure
  simp
  omega

theorem descendLte_initial_load_run (len cv f : Nat) :
    descendLte cv (f + 1) 1 (longKeyCtx len)
      { next := 100, top := longKeyTop, path := [(none, 1)] } =
      .ok (1, longKeyLoaded) := by
  unfold descendLte
  runPure
  rw [getNode_initial_load_run len]
  rfl

theorem putSegs_same_descent (c : Ctx) (w v : W) (x : NodeId) (key segs : Key)
    (value : Option Nat)
    (hd : ∀ cv, descendLte cv c.p.fuel x c w = descendLte cv c.p.fuel x c v) :
    putSegs key value segs x c w = putSegs key value segs x c v := by
  cases segs with
  | nil => rfl
  | cons cv rest =>
    cases rest with
    | nil =>
      unfold putSegs setValue
      runPure
      rw [hd cv]
    | cons d rest =>
      unfold putSegs
      runPure
      unfold setNode
      runPure
      rw [hd cv]

theorem putKv_longKey_success (len : Nat) :
    ∃ v, putKv (.put (longKey len) 1) (longKeyCtx len)
      { next := 100, top := longKeyTop } = .ok (false, v) ∧ v.outside = [] := by
  have hw : FreshCache 0 longKeyLoaded := by simp [FreshCache, longKeyLoaded]
  have hn : longKeyLoaded.nodes.lookup 1 = some ⟨true, [.time 0]⟩ := by rfl
  have hg : longKeyLoaded.gh.lookup 1 = some (0, 0) := by rfl
  have hs : (⟨true, [.time 0]⟩ : KNode).searchEq (longKeyCtx len).i 56 = none := by rfl
  obtain ⟨v, hv, ho⟩ := putSegs_longKey_initial_success (longKeyCtx len) (longKey len) 1 len
    longKeyLoaded 1 0 ⟨true, [.time 0]⟩ hw hn rfl hg hs (by change 2 < 8; decide) rfl
    (by change 0 + len ≤ len; omega)
  refine ⟨v, ?_, ho⟩
  unfold putKv pathClear findRoot pathAdd
  runPure
  change putSegs (longKey len) (some 1) (longKey len) 1 (longKeyCtx len)
    { next := 100, top := longKeyTop, path := [(none, 1)] } = .ok (false, v)
  rw [putSegs_same_descent (longKeyCtx len)
    { next := 100, top := longKeyTop, path := [(none, 1)] } longKeyLoaded 1
    (longKey len) (longKey len) (some 1) ?_]
  · exact hv
  · intro cv
    have hf : 0 < (longKeyCtx len).p.fuel := by unfold Params.fuel; omega
    cases hfu : (longKeyCtx len).p.fuel with
    | zero => omega
    | succ f =>
      rw [descendLte_initial_load_run len cv f,
        descendLte_cached_leaf_run (longKeyCtx len) longKeyLoaded 1 _ hn rfl cv f]

theorem longKeyParams_ok (len : Nat) : MergeParamsOK (longKeyParams len) :=
  mergeParamsOK_withMerges _ (by change 8 ≤ 8; decide)

theorem longKey_execW_success (len : Nat) :
    ∃ v, execW (longKeyParams len) (longKeyTx len) 1
      (view (treeSpec (longKeyParams len)) (initStruct (longKeyParams len)) 0) =
      .ok ([false], v) := by
  obtain ⟨v, hv, ho⟩ := putKv_longKey_success len
  refine ⟨v, ?_⟩
  unfold execW runOps
  rw [view_initial_eq_viewOf]
  have hz : lastTop (viewOf (initStruct (longKeyParams len))) = some 2 := rfl
  have ht : topOf (longKeyParams len)
      (rootless (viewOf (initStruct (longKeyParams len)))) 2 = .ok longKeyTop := by
    simp [topOf, rootless, viewOf, init_get_top, root, Params.ordOf, Params.topLevel,
      longKeyTop]
  unfold runOpsFrom
  simp only [hz, ht]
  simp only [longKeyTx, List.mapM_cons, List.mapM_nil]
  runPure
  dsimp only [longKeyCtx] at hv
  rw [hv]
  simp [boundsOK, ho]

theorem longKeyHistory_within (len : Nat) : Within (longKeyParams len) [longKeyTx len] := by
  constructor
  · intro tx htx
    have he : tx = longKeyTx len := List.mem_singleton.mp htx
    subst tx
    exact ⟨rfl, by simpa [Tx.wf, longKeyTx, Op.key] using longKey_wf len⟩
  · intro j hj
    have hj0 : j = 0 := by simpa using Nat.lt_one_iff.mp hj
    subst j
    constructor
    · intro q hq
      change q ∈ initStruct (longKeyParams len) at hq
      rcases mem_init _ q hq with rfl | rfl | rfl <;> simp [longKeyTx, root]
    · obtain ⟨v, hv⟩ := longKey_execW_success len
      change isOk (exec? (longKeyParams len) (longKeyTx len) 1
        (view (treeSpec (longKeyParams len)) (initStruct (longKeyParams len)) 0)) = true
      change isOk ((execW (longKeyParams len) (longKeyTx len) 1
        (view (treeSpec (longKeyParams len)) (initStruct (longKeyParams len)) 0)).map
        (fun r => changesOf 1 r.2)) = true
      rw [hv]
      rfl

theorem longKey_reference (len : Nat) :
    refScan [longKeyTx len] 1 {} 1 = [(longKey len, 1)] := by
  have he : [longKey len].eraseDups = [longKey len] := rfl
  simp [refScan, refKvs, refGet, longKeyTx, Op.key, inRange, he]

/-- TP11 needs its premise on the length of keys: without it the scan is wrong,
with encoded keys and valid merge parameters, on a run of one put of a key of
`scanFuel + 1` segments, since the scan's fixed fuel cannot return a first key
with more segments than that fuel. -/
theorem scan_needs_keyBound :
    ¬ ∀ ts, Within (longKeyParams scanFuel) ts → ∀ t ≤ ts.length,
      ∀ (req : ScanReq) (limit : Nat), req.wf = true →
        (scan (longKeyParams scanFuel) (viewOf (treeRun (longKeyParams scanFuel) ts))
          t req limit).map (fun kv => (kv.key, kv.h)) = refScan ts t req limit := by
  intro hs
  have hk : (longKey scanFuel, 1) ∈ refScan [longKeyTx scanFuel] 1 {} 1 := by
    rw [longKey_reference]
    exact List.mem_cons_self
  have he := hs [longKeyTx scanFuel] (longKeyHistory_within scanFuel) 1 (by decide) {} 1
    (by rfl)
  have hb := scanEq_first_key_length (longKeyParams scanFuel) [longKeyTx scanFuel] 1 he
    (longKey scanFuel) 1 hk
  rw [longKey_length] at hb
  omega

end SIS.Tree
