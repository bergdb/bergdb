import SIS.Tree.GetFinal
import SIS.Tree.RangeRun
import SIS.Tree.GetFuel
import SIS.Tree.OverlayLift

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! The assembly of TP10 and TP11 (bergdb 024-12): `getOK_scanOK_of_open` gives
`GetOK` and `ScanOK` (Props.lean, unchanged) from TP7 and the named open pieces.

* TP7 (`InvPreserved`), a run premise R that every run within reach meets and
  that gives the run's links, P's tree and TP7's invariant, and tp7's lift
  (`OverlayLiftOKUnder`).
* The writer's tree (`OpTreeOK`, cost), `PutInv` (`OpPutInvOK`, putinv) and the
  walk's ranges (`OpRangeOK`, putinv) at every operation.
* The fuel premise along transactions within reach (`TxSegFitsOK`): every state
  between operations has every path inside one segment tree shorter than the
  fuel.
* The operation cases (`OpGetCaseOK` of each case below): from a state between
  operations that meets `PutInv` and `RangeOrder`, the operation changes the
  reading by itself alone when the state after it meets the fuel premise. The
  cases cover every operation (`opCase_cover`). -/

/-! ## The fuel premise along a transaction -/

/-- Every state that a prefix of a transaction within reach reaches has every
path inside one segment tree shorter than the fuel. -/
def TxSegFitsOK (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre post, tx.ops = pre ++ post → ∀ r w,
    (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    SegFits (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) (p.fuel - 1) w.top.rootKey

/-! ## The operation cases -/

/-- An operation case P: from a state between operations of a transaction within
reach that meets `PutInv`, `RangeOrder` and P, the operation changes the reading
by itself alone, when the state after it meets the fuel premise. -/
def OpGetCaseOK (p : Params) (R : Struct BVal → Time → Prop)
    (P : Ctx → View BVal → W → Op → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre op post, tx.ops = pre ++ op :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w →
    RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey →
    P (ctxOf p ts) (viewOf (treeRun p ts)) w op →
    WriterWP (putKv op) (ctxOf p ts) w (fun _ w' =>
      SegFits (wNode p (viewOf (treeRun p ts)) w') (ts.length + 1) (p.fuel - 1) w'.top.rootKey →
      ∀ key, keyWf key = true →
        runGet p ts w' key = if op.key == key then op.value else runGet p ts w key)

/-- The leaf L, node n, of the key pre ++ [cv] in the writer's state: the
segment root rk of the prefix, and L the leaf its descent for cv ends at. -/
def KeyLeaf (c : Ctx) (base : View BVal) (w : W) (pre : List Nat) (cv : Nat) (L : NodeId)
    (n : KNode) : Prop :=
  ∃ rk, segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk ∧
    (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk ∧
    wNode c.p base w L = some n ∧ n.leaf = true

/-- Room in the leaf for a put's klong of cv: the writer adds it there. -/
def PutRoom (c : Ctx) (w : W) (cv : Nat) (n : KNode) : Prop :=
  n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv w.next)) = false

/-- Room in the leaf for a delete's bitmap of cv: the writer puts it there. -/
def DelRoom (c : Ctx) (cv : Nat) (n : KNode) : Prop :=
  ((∃ old, n.ks.getLast? = some (.del old)) ∧ n.lastTime = some c.i ∧
      deadOver c.p (n.setAt (n.size - 1) (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))) = false) ∨
    (¬ ((∃ old, n.ks.getLast? = some (.del old)) ∧ n.lastTime = some c.i) ∧ n.size + 1 < c.p.M ∧
      deadOver c.p (n.add c.i (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))) = false)

/-- (1) A put whose key's leaf is there and has room for its klong. -/
def PutLeafRoomCase (c : Ctx) (base : View BVal) (w : W) (op : Op) : Prop :=
  ∃ pre cv h L n, op = .put (pre ++ [cv]) h ∧ KeyLeaf c base w pre cv L n ∧ PutRoom c w cv n

/-- (2) A put whose key's leaf is there and full: the cascade of splits. -/
def PutLeafFullCase (c : Ctx) (base : View BVal) (w : W) (op : Op) : Prop :=
  ∃ pre cv h L n, op = .put (pre ++ [cv]) h ∧ KeyLeaf c base w pre cv L n ∧ ¬ PutRoom c w cv n

/-- (3) A put whose key has no leaf yet: new segments. -/
def PutNewSegCase (c : Ctx) (base : View BVal) (w : W) (op : Op) : Prop :=
  ∃ key h, op = .put key h ∧ ¬ ∃ pre cv L n, key = pre ++ [cv] ∧ KeyLeaf c base w pre cv L n

/-- (4) A delete with the merges on. -/
def DelMergeCase (c : Ctx) (_base : View BVal) (_w : W) (op : Op) : Prop :=
  ∃ key, op = .del key ∧ c.p.merges = true

/-- (5) A delete, the merges off, of a key that has no leaf: nothing to delete. -/
def DelNoLeafCase (c : Ctx) (base : View BVal) (w : W) (op : Op) : Prop :=
  ∃ key, op = .del key ∧ c.p.merges = false ∧ ¬ ∃ pre cv L n, key = pre ++ [cv] ∧ KeyLeaf c base w pre cv L n

/-- (6) A delete, the merges off, whose bitmap changes nothing (a noop). -/
def DelNoopCase (c : Ctx) (base : View BVal) (w : W) (op : Op) : Prop :=
  ∃ pre cv L n, op = .del (pre ++ [cv]) ∧ c.p.merges = false ∧ KeyLeaf c base w pre cv L n ∧
    bitsUnion n.lastBitmap (n.bitsOf cv) = n.lastBitmap

/-- (7) A delete, the merges off, that empties its leaf: the upward delete. -/
def DelEmptyCase (c : Ctx) (base : View BVal) (w : W) (op : Op) : Prop :=
  ∃ pre cv L n, op = .del (pre ++ [cv]) ∧ c.p.merges = false ∧ KeyLeaf c base w pre cv L n ∧
    bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
    n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = true

/-- (8) A delete, the merges off, whose leaf keeps a live klong and has room for
the bitmap. -/
def DelRoomCase (c : Ctx) (base : View BVal) (w : W) (op : Op) : Prop :=
  ∃ pre cv L n, op = .del (pre ++ [cv]) ∧ c.p.merges = false ∧ KeyLeaf c base w pre cv L n ∧
    bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
    n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = false ∧ DelRoom c cv n

/-- (9) A delete, the merges off, whose leaf keeps a live klong and is full:
the leaf splits, with the cascade above. -/
def DelFullCase (c : Ctx) (base : View BVal) (w : W) (op : Op) : Prop :=
  ∃ pre cv L n, op = .del (pre ++ [cv]) ∧ c.p.merges = false ∧ KeyLeaf c base w pre cv L n ∧
    bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
    n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = false ∧ ¬ DelRoom c cv n

/-- Every operation from every state is in one of the cases. -/
theorem opCase_cover (c : Ctx) (base : View BVal) (w : W) (op : Op) :
    PutLeafRoomCase c base w op ∨ PutLeafFullCase c base w op ∨ PutNewSegCase c base w op ∨
    DelMergeCase c base w op ∨ DelNoLeafCase c base w op ∨ DelNoopCase c base w op ∨
    DelEmptyCase c base w op ∨ DelRoomCase c base w op ∨ DelFullCase c base w op := by
  cases op with
  | put key h =>
    by_cases hk : ∃ pre cv L n, key = pre ++ [cv] ∧ KeyLeaf c base w pre cv L n
    · obtain ⟨pre, cv, L, n, hkey, hl⟩ := hk
      subst hkey
      by_cases hr : PutRoom c w cv n
      · exact Or.inl ⟨pre, cv, h, L, n, rfl, hl, hr⟩
      · exact Or.inr (Or.inl ⟨pre, cv, h, L, n, rfl, hl, hr⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨key, h, rfl, hk⟩))
  | del key =>
    cases hm : c.p.merges with
    | true => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨key, rfl, hm⟩)))
    | false =>
      by_cases hk : ∃ pre cv L n, key = pre ++ [cv] ∧ KeyLeaf c base w pre cv L n
      · obtain ⟨pre, cv, L, n, hkey, hl⟩ := hk
        subst hkey
        by_cases hb : bitsUnion n.lastBitmap (n.bitsOf cv) = n.lastBitmap
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨pre, cv, L, n, rfl, hm, hl, hb⟩)))))
        · cases ha : n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) with
          | true =>
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              ⟨pre, cv, L, n, rfl, hm, hl, hb, ha⟩))))))
          | false =>
            by_cases hr : DelRoom c cv n
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨pre, cv, L, n, rfl, hm, hl, hb, ha, hr⟩)))))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                ⟨pre, cv, L, n, rfl, hm, hl, hb, ha, hr⟩)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨key, rfl, hm, hk⟩))))

/-! ## The assembly -/

/-- `OpGetPutInvOK` from the fuel premise along transactions, the writer's tree,
`PutInv`, the walk's ranges and the nine operation cases. -/
theorem opGetPutInvOK_of_cases (p : Params) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRT : ∀ P t, R P t → TreeAt p P t)
    (hRI : ∀ P t, R P t → InvOK p P t)
    (ho : OpTreeOK p) (hP : OpPutInvOK p R) (hO : OpRangeOK p R) (hfit : TxSegFitsOK p R)
    (c1 : OpGetCaseOK p R PutLeafRoomCase) (c2 : OpGetCaseOK p R PutLeafFullCase)
    (c3 : OpGetCaseOK p R PutNewSegCase) (c4 : OpGetCaseOK p R DelMergeCase)
    (c5 : OpGetCaseOK p R DelNoLeafCase) (c6 : OpGetCaseOK p R DelNoopCase)
    (c7 : OpGetCaseOK p R DelEmptyCase) (c8 : OpGetCaseOK p R DelRoomCase)
    (c9 : OpGetCaseOK p R DelFullCase) :
    OpGetPutInvOK p R := by
  intro ts tx hw hr z top hz htop pre op post hsplit r w hpre hPI
  have hPIall := putInv_reached p R hRL ho hP ts tx hw hr (hRT _ _ hr) (hRI _ _ hr) z top hz htop
  have hRO := rangeOrder_reached p R hO ts tx hw hr (hRI _ _ hr) z top hz htop hPIall
    (fun pre' post' hs r' w' h => writerTreeOK_reached p ho ts tx hw z top hz htop (hRT _ _ hr) pre' post'
      hs r' w' h) pre (op :: post) hsplit r w hpre
  have hcase : ∀ P : Ctx → View BVal → W → Op → Prop, OpGetCaseOK p R P →
      P (ctxOf p ts) (viewOf (treeRun p ts)) w op →
      WriterWP (putKv op) (ctxOf p ts) w (fun _ w' => ∀ key, keyWf key = true →
        runGet p ts w' key = if op.key == key then op.value else runGet p ts w key) := by
    intro P hc hPc a w' hrun
    exact hc ts tx hw hr z top hz htop pre op post hsplit r w hpre hPI hRO hPc a w' hrun
      (hfit ts tx hw hr z top hz htop (pre ++ [op]) post (by rw [hsplit]; simp) (r ++ [a]) w'
        (mapM_snoc_run pre op _ _ w w' r a hpre hrun))
  rcases opCase_cover (ctxOf p ts) (viewOf (treeRun p ts)) w op with
    h | h | h | h | h | h | h | h | h
  · exact hcase _ c1 h
  · exact hcase _ c2 h
  · exact hcase _ c3 h
  · exact hcase _ c4 h
  · exact hcase _ c5 h
  · exact hcase _ c6 h
  · exact hcase _ c7 h
  · exact hcase _ c8 h
  · exact hcase _ c9 h

/-- TP10 and TP11 from TP7 and the named open pieces: the run premise R (with
the run's links, P's tree and TP7's invariant), the writer's tree, `PutInv`, the
walk's ranges, the fuel premise along transactions, tp7's lift, and the nine
operation cases. -/
theorem getOK_scanOK_of_open (p : Params) (hinv : InvPreserved p) (R : Struct BVal → Time → Prop)
    (hR : ∀ ts, Within p ts → R (treeRun p ts) ts.length)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRT : ∀ P t, R P t → TreeAt p P t)
    (hRI : ∀ P t, R P t → InvOK p P t)
    (ho : OpTreeOK p) (hP : OpPutInvOK p R) (hO : OpRangeOK p R) (hfit : TxSegFitsOK p R)
    (hl : OverlayLiftOKUnder p R)
    (c1 : OpGetCaseOK p R PutLeafRoomCase) (c2 : OpGetCaseOK p R PutLeafFullCase)
    (c3 : OpGetCaseOK p R PutNewSegCase) (c4 : OpGetCaseOK p R DelMergeCase)
    (c5 : OpGetCaseOK p R DelNoLeafCase) (c6 : OpGetCaseOK p R DelNoopCase)
    (c7 : OpGetCaseOK p R DelEmptyCase) (c8 : OpGetCaseOK p R DelRoomCase)
    (c9 : OpGetCaseOK p R DelFullCase) :
    GetOK p ∧ ScanOK p := by
  have hg := opGetPutInvOK_of_cases p R hRL hRT hRI ho hP hO hfit c1 c2 c3 c4 c5 c6 c7 c8 c9
  exact ⟨getOK_of_putInv p hinv R hR hRL hRT hRI ho hP hg hl,
    scanOK_of_putInv p hinv R hR hRL hRT hRI ho hP hg hl⟩

/-- The run premise of the assembly: the run's links, P's tree and TP7's
invariant. -/
def RunOK (p : Params) (P : Struct BVal) (t : Time) : Prop :=
  RunLinksOK p P t ∧ TreeAt p P t ∧ InvOK p P t

/-- `getOK_scanOK_of_open` with the run premise `RunOK`: tp7's lift is proved
for it (`overlayLiftOKUnder_links`); left are the run's links and P's tree at
every run within reach, besides the pieces of `getOK_scanOK_of_open`. -/
theorem getOK_scanOK_of_open_runOK (p : Params) (hinv : InvPreserved p)
    (hlinks : ∀ ts, Within p ts → RunLinksOK p (treeRun p ts) ts.length)
    (htree : ∀ ts, Within p ts → TreeAt p (treeRun p ts) ts.length)
    (ho : OpTreeOK p) (hP : OpPutInvOK p (RunOK p)) (hO : OpRangeOK p (RunOK p))
    (hfit : TxSegFitsOK p (RunOK p))
    (c1 : OpGetCaseOK p (RunOK p) PutLeafRoomCase) (c2 : OpGetCaseOK p (RunOK p) PutLeafFullCase)
    (c3 : OpGetCaseOK p (RunOK p) PutNewSegCase) (c4 : OpGetCaseOK p (RunOK p) DelMergeCase)
    (c5 : OpGetCaseOK p (RunOK p) DelNoLeafCase) (c6 : OpGetCaseOK p (RunOK p) DelNoopCase)
    (c7 : OpGetCaseOK p (RunOK p) DelEmptyCase) (c8 : OpGetCaseOK p (RunOK p) DelRoomCase)
    (c9 : OpGetCaseOK p (RunOK p) DelFullCase) :
    GetOK p ∧ ScanOK p :=
  getOK_scanOK_of_open p hinv (RunOK p)
    (fun ts hw => ⟨hlinks ts hw, htree ts hw, (hinv ts hw ts.length (Nat.le_refl _)).1⟩)
    (fun _ _ h => h.1) (fun _ _ h => h.2.1) (fun _ _ h => h.2.2) ho hP hO hfit
    (overlayLiftOKUnder_mono p (RunOK p) _ (fun _ _ h => h.1) (overlayLiftOKUnder_links p))
    c1 c2 c3 c4 c5 c6 c7 c8 c9

/-! ## The premises are not void

A transaction within reach after the empty run, twelve puts into a segment
below the key 120 with node size 8 (the second segment's tree splits): the run
meets `Within`'s conditions, and every state between its operations meets the
fuel premise (a Bool form of `SegFits`, the depth of every segment tree reached
at most fuel - 1). So the hypotheses of `TxSegFitsOK` and `OpGetCaseOK` are met
by a run, and `TxSegFitsOK` holds on it. -/

/-- The nodes reached from r in f rounds of live links. -/
def asmReach (N : NodeId → Option KNode) (t : Time) (r : NodeId) : Nat → List NodeId
  | 0 => [r]
  | f + 1 =>
    let s := asmReach N t r f
    s ++ ((s.flatMap (fun x => match N x with
      | some n => (n.liveAt t).map (·.2)
      | none => [])).eraseDups.filter (fun y => !s.contains y))

/-- The depth of x's segment tree, f rounds deep (`SegDepthLe` as a number). -/
def asmDepth (N : NodeId → Option KNode) (t : Time) : Nat → NodeId → Nat
  | 0, _ => 0
  | f + 1, x => match N x with
    | none => 0
    | some n => if n.leaf then 0 else (n.liveAt t).foldl (fun m q => max m (1 + asmDepth N t f q.2)) 0

/-- `SegFits N t (fuel - 1) r` as a Bool, over the nodes reached in 30 rounds. -/
def asmFitsB (p : Params) (N : NodeId → Option KNode) (t : Time) (r : NodeId) : Bool :=
  (asmReach N t r 30).all (fun x => decide (asmDepth N t 30 x ≤ p.fuel - 1))

/-- `Within p [tx]` and the fuel premise at every state between tx's operations. -/
def asmCheck (p : Params) (tx : Tx) : Bool :=
  let ts : List Tx := []
  let v := view (treeSpec p) (treeRun p ts) ts.length
  tx.sorted && tx.wf && (treeRun p ts).all (fun q => decide (q.1 < tx.base)) &&
  isOk (exec? p tx (ts.length + 1) v) &&
  match lastTop v with
  | none => false
  | some z =>
    match topOf p (ctxOf p ts).view z with
    | .error _ => false
    | .ok top =>
      (List.range (tx.ops.length + 1)).all (fun k =>
        match ((tx.ops.take k).mapM putKv) (ctxOf p ts) (wInit tx top) with
        | .ok (_, w) => asmFitsB p (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey
        | .error _ => false)

def asmP : Params := {M := 8, G := 1, H := 2}
def asmTx : Tx := {base := 1000, ops := (List.range 12).map (fun j => .put [120, 64*j+8] (j+1))}

#guard asmCheck asmP asmTx

end SIS.Tree
