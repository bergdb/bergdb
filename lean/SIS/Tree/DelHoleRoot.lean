/-
Root collapse's check proved (bergdb 024-12, section 1). `hchk`'s `checkRoot`
passes at every state of root collapse inside a delete, from the delete's loop
invariant with the take-back's facts (`DelInvJ`) and the books of the
transaction's first id at `afterDelete`'s call. The premise is now
`OpDelChk6OKL`: the writer's delete runs as the copy that checks, at each call
of `afterDelete`, that `DelInvJ` and the books hold and that the merges' loop
from there runs as its copy with the merge's `checkFree` (`afterDeleteJ`), and
then runs the writer's `afterDelete`. `opDelChk5OKR_of_chk6` gives
`OpDelChk5OKR` from it:

* root collapse with the check runs as without it from every state of the
  collapse's invariant (`rwp_collapseRoot_chkJ`): `checkRoot_ok_of_J2` at each
  take-back, from the path that `descendToSegmentRoot` leaves
  (`checkRoot_ok_of_segDesc`);
* so at every state that passes `afterDeleteJ`'s check, `afterDelete` runs as
  `afterDeleteChk` (`rwp_afterDelete_of_J`, the merges' loop keeping `DelInvJ`
  and the books), and the delete with `afterDeleteJ` as `putKvDelChk5`
  (`rwp_putKvDP`, `putKvDelChk5_eq`).
-/
import SIS.Tree.DelHole

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## The copy with the check at `afterDelete`'s calls -/

open Classical in
/-- `afterDelete` from a state of J only, where the merges' loop runs as its
copy with the merge's `checkFree`. -/
noncomputable def afterDeleteJ (J : W → Prop) (key : Key) (g h : Nat) : M Unit := do
  let c ← read
  let v ← (MonadState.get : M W)
  if J v ∧ RWP (mergeUp key g c.p.fuel h false) (mergeUpChk key g c.p.fuel h false) c v then
    afterDelete key g h
  else throw "check: the state at a call of afterDelete"

/-- The delete with `afterDeleteJ J` at `afterDelete`'s calls. -/
noncomputable def putKvDelChk6 (J : W → Prop) (key : Key) : M Bool := putKvDP (afterDeleteJ J) key

/-- The state at a call of `afterDelete` in the delete of `key` from w0: the
delete's loop invariant with the take-back's facts (`DelInvJ`) and the books of
the transaction's first id. -/
def DelHoleJ (p : Params) (ts : List Tx) (tx : Tx) (top : Top) (w0 : W) (key : Key) (v : W) : Prop :=
  DelInvJ (ctxOf p ts) (viewOf (treeRun p ts)) w0 key (p.fuel + 1) (kindOracleOf p (treeRun p ts))
    tx.base tx.base v ∧ PutBook (ctxOf p ts) tx.base top v

/-- `OpDelChk5OKR` with `putKvDelChk6`: at the deletes of the runs of R, the
delete runs as its copy that checks `DelHoleJ` and the merges' loop at each call
of `afterDelete`, root collapse without a check. -/
def OpDelChk6OKR (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre key post, tx.ops = pre ++ Op.del key :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w →
    RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey →
    LiveCounts p (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey →
    HtInv (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) w →
    J2At p (treeRun p ts) (ts.length + 1) tx.base w →
    ∀ r' v, putKv (.del key) (ctxOf p ts) w = .ok (r', v) →
      putKvDelChk6 (DelHoleJ p ts tx top w key) key (ctxOf p ts) w = .ok (r', v)

/-- `OpDelChk6OKR` at the induction's runs. -/
def OpDelChk6OKL (p : Params) : Prop := OpDelChk6OKR p (RunTreeQ p (LatestQD p))

/-! ## Root collapse's check -/

theorem rwp_throw_bind {α β : Type} (e : String) (k : α → M β) (g : M β) (c : Ctx) (w : W) :
    RWP ((throw e : M α) >>= k) g c w := by
  intro x hx
  obtain ⟨a, w', h1, _⟩ := (m_bind_ok _ _ c w x).mp hx
  exact ((writerWP_throw e c w (fun _ _ => False)) a w' h1).elim

theorem rwp_check_right {β : Type} {f : M β} {chk : M Unit} {k : Unit → M β} {c : Ctx} {v : W}
    (hc : chk c v = .ok ((), v)) (h : RWP f (k ()) c v) : RWP f (chk >>= k) c v := by
  intro x hx
  exact (m_bind_ok chk k c v x).mpr ⟨(), v, hc, h x hx⟩

/-- Every successful run of f from w whose end state is in C is one of g (bergdb
025-05: the checked copies for the runs that end below a fuel). -/
def RWPC {α : Type} (f g : M α) (c : Ctx) (w : W) (C : W → Prop) : Prop :=
  ∀ x, f c w = .ok x → C x.2 → g c w = .ok x

theorem rwp_of_rwpc {α : Type} {f g : M α} {c : Ctx} {w : W} {C : W → Prop}
    (h : RWPC f g c w C) (hC : ∀ v, C v) : RWP f g c w :=
  fun x hx => h x hx (hC x.2)

theorem rwpc_refl {α : Type} (f : M α) (c : Ctx) (w : W) (C : W → Prop) : RWPC f f c w C :=
  fun _ h _ => h

theorem rwpc_bind {α β : Type} {m : M α} {k1 k2 : α → M β} {c : Ctx} {w : W} {C : W → Prop}
    (P : α → W → Prop) (hm : WriterWP m c w P) (hk : ∀ a w', P a w' → RWPC (k1 a) (k2 a) c w' C) :
    RWPC (m >>= k1) (m >>= k2) c w C := by
  intro x h hC
  obtain ⟨a, w', h1, h2⟩ := (m_bind_ok m k1 c w x).mp h
  exact (m_bind_ok m k2 c w x).mpr ⟨a, w', h1, hk a w' (hm a w' h1) x h2 hC⟩

theorem rwpc_bind2 {α β : Type} {m1 m2 : M α} {k1 k2 : α → M β} {c : Ctx} {w : W} {C : W → Prop}
    (P : α → W → Prop) (h12 : RWP m1 m2 c w) (hm : WriterWP m1 c w P)
    (hk : ∀ a w', P a w' → RWPC (k1 a) (k2 a) c w' C) : RWPC (m1 >>= k1) (m2 >>= k2) c w C := by
  intro x h hC
  obtain ⟨a, w', h1, h2⟩ := (m_bind_ok m1 k1 c w x).mp h
  exact (m_bind_ok m2 k2 c w x).mpr ⟨a, w', h12 _ h1, hk a w' (hm a w' h1) x h2 hC⟩

theorem rwpc_read {β : Type} {k1 k2 : Ctx → M β} {c : Ctx} {w : W} {C : W → Prop}
    (h : RWPC (k1 c) (k2 c) c w C) : RWPC (read >>= k1) (read >>= k2) c w C :=
  rwpc_bind (fun a v => a = c ∧ v = w) ((writerWP_read c w _).mpr ⟨rfl, rfl⟩)
    (fun a v ⟨ha, hv⟩ => by subst ha; subst hv; exact h)

theorem rwpc_ite {β : Type} {b : Prop} [Decidable b] {f1 f2 g1 g2 : M β} {c : Ctx} {w : W}
    {C : W → Prop} (h1 : b → RWPC f1 g1 c w C) (h2 : ¬ b → RWPC f2 g2 c w C) :
    RWPC (if b then f1 else f2) (if b then g1 else g2) c w C := by
  by_cases hb : b
  · simp only [hb, ↓reduceIte]; exact h1 hb
  · simp only [hb, ↓reduceIte]; exact h2 hb

theorem rwpc_throw_bind {α β : Type} (e : String) (k : α → M β) (g : M β) (c : Ctx) (w : W)
    (C : W → Prop) : RWPC ((throw e : M α) >>= k) g c w C :=
  fun x hx _ => rwp_throw_bind e k g c w x hx

theorem rwpc_check_right {β : Type} {f : M β} {chk : M Unit} {k : Unit → M β} {c : Ctx} {v : W}
    {C : W → Prop} (hc : ∀ x, f c v = .ok x → C x.2 → chk c v = .ok ((), v)) (h : RWPC f (k ()) c v C) :
    RWPC f (chk >>= k) c v C := by
  intro x hx hC
  exact (m_bind_ok chk k c v x).mpr ⟨(), v, hc x hx hC, h x hx hC⟩

/-- `rwp_collapseRoot_chk` for the runs that end in a state of C (bergdb 025-05): the
check is asked only at states of C, which C holds at when it holds at the end of the
rest of the run (`hgrow`). -/
theorem rwp_collapseRoot_chkQ (key : Key) (seg : Nat) (c : Ctx) (Inv : W → Prop)
    (Pd : NodeId → W → Prop) (C : W → Prop) (hS : CollSteps key seg c Inv Pd)
    (hgrow : ∀ x v d only f, Inv v →
      WriterWP (takeBackRoot x d only >>= fun _ => collapseRoot key seg f) c v (fun _ v' => C v' → C v))
    (hchk : ∀ x v n, Inv v → C v → Pd x v → v.nodes.lookup x = some n → n.firstTime = some c.i →
      checkRoot x (v.path.length - 1) c v = .ok ((), v)) :
    ∀ fuel v, Inv v → RWPC (collapseRoot key seg fuel) (collapseRootChk key seg fuel) c v C := by
  intro fuel
  induction fuel with
  | zero => intro v _; unfold collapseRoot collapseRootChk; exact rwpc_refl _ _ _ _
  | succ f ih =>
    intro v hI
    unfold collapseRoot collapseRootChk
    refine rwpc_read ?_
    refine rwpc_bind (fun x v' => Inv v' ∧ Pd x v') (hS.desc v hI) ?_
    rintro x v1 ⟨hI1, hP1⟩
    refine rwpc_bind _ (hS.get x v1 hI1 hP1) ?_
    rintro n v2 ⟨hI2, hP2, hl2, _⟩
    by_cases hleaf : n.leaf = true
    · simp only [hleaf, ↓reduceIte]; exact rwpc_refl _ _ _ _
    · have hleaf' : n.leaf = false := by simpa using hleaf
      simp only [hleaf', Bool.false_eq_true, ↓reduceIte]
      refine rwpc_bind (fun r v' => r = v2.madeFor.lookup x ∧ v' = v2)
        (by unfold replacedBy; simp only [writerWP_bind, writerWP_get, writerWP_pure, and_self]) ?_
      rintro rb v3 ⟨hrb, hv3⟩
      subst v3; subst rb
      refine rwpc_ite (fun _ => rwpc_refl _ _ _ _) (fun hmr => ?_)
      cases honly : n.onlyLiveKlong with
      | none => exact rwpc_refl _ _ _ _
      | some only =>
        refine rwpc_ite (fun _ => rwpc_throw_bind _ _ _ _ _ _) (fun hcv => ?_)
        have hcv' : n.cv? only = some 0 := by simpa using hcv
        refine rwpc_bind (fun s v' => s = v2.path.length ∧ v' = v2)
          (by unfold pathSize; simp only [writerWP_bind, writerWP_get, writerWP_pure, and_self]) ?_
        rintro s v4 ⟨hs, hv4⟩
        subst v4; subst s
        by_cases hmade : (n.firstTime == some c.i) = true
        · have hm : n.firstTime = some c.i := by simpa using hmade
          have hrb : (v2.madeFor.lookup x).isSome = true := by
            simp only [hmade, Bool.true_and, Option.isNone_iff_eq_none] at hmr
            cases h : v2.madeFor.lookup x with
            | none => exact absurd h hmr
            | some _ => rfl
          simp only [hmade, ↓reduceIte]
          refine rwpc_check_right (fun y hy hCy => hchk x v2 n hI2
            (hgrow x v2 _ only f hI2 y.1 y.2 hy hCy) hP2 hl2 hm) ?_
          exact rwpc_bind (fun _ v' => Inv v') (hS.stepT x v2 n only hI2 hP2 hl2 hleaf' hm hrb honly hcv')
            (fun _ v3 h3 => ih v3 h3)
        · have hm : n.firstTime ≠ some c.i := by simpa using hmade
          simp only [hmade, Bool.false_eq_true, ↓reduceIte]
          exact rwpc_bind (fun _ v' => Inv v') (hS.stepR x v2 n only hI2 hP2 hl2 hleaf' hm honly hcv')
            (fun _ v3 h3 => ih v3 h3)

/-- Root collapse with the check runs as without it from every state of an
invariant that the loop's steps keep, where the check passes before each
take-back. -/
theorem rwp_collapseRoot_chk (key : Key) (seg : Nat) (c : Ctx) (Inv : W → Prop)
    (Pd : NodeId → W → Prop)
    (hdesc : ∀ v, Inv v → WriterWP (descendToSegmentRoot key seg) c v (fun x v' => Inv v' ∧ Pd x v'))
    (hget : ∀ x v, Inv v → Pd x v → WriterWP (getNode x) c v (fun n v' =>
      Inv v' ∧ Pd x v' ∧ v'.nodes.lookup x = some n ∧ v'.path = v.path))
    (hstepT : ∀ x v n only, Inv v → Pd x v → v.nodes.lookup x = some n → n.leaf = false →
      n.firstTime = some c.i → (v.madeFor.lookup x).isSome = true →
      n.onlyLiveKlong = some only → n.cv? only = some 0 →
      WriterWP (takeBackRoot x (v.path.length - 1) only) c v (fun _ v' => Inv v'))
    (hstepR : ∀ x v n only, Inv v → Pd x v → v.nodes.lookup x = some n → n.leaf = false →
      n.firstTime ≠ some c.i →
      n.onlyLiveKlong = some only → n.cv? only = some 0 →
      WriterWP (replaceRoot x (v.path.length - 1) only) c v (fun _ v' => Inv v'))
    (hchk : ∀ x v n, Inv v → Pd x v → v.nodes.lookup x = some n → n.firstTime = some c.i →
      checkRoot x (v.path.length - 1) c v = .ok ((), v)) :
    ∀ fuel v, Inv v → RWP (collapseRoot key seg fuel) (collapseRootChk key seg fuel) c v :=
  fun fuel v hI => rwp_of_rwpc (rwp_collapseRoot_chkQ key seg c Inv Pd (fun _ => True)
    ⟨hdesc, hget, hstepT, hstepR⟩ (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun x v n hI _ hP hl hm => hchk x v n hI hP hl hm) fuel v hI) (fun _ => trivial)
set_option maxHeartbeats 1600000 in
/-- `checkRoot` passes before root collapse takes back x, a node that the
transaction made, at the end of the path that `descendToSegmentRoot` left, at a
state of the collapse's invariant with the books and the take-back's facts of one
first id B (`checkRoot_ok_of_J2`). -/
theorem checkRoot_ok_of_segDesc (c : Ctx) (base : View BVal) (w0 : W) (f : Nat) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (v : W) (hI : CollGetInvF c base w0 v f)
    (hR : RangeOrder (wNode c.p base v) c.i v.top.rootKey) (hb : PutBook c B top0 v) (hbk : Book B c v)
    (hJ : TakeJ2 c base B v) (x : NodeId) (n : KNode) (hP : SegDesc c base x v)
    (hlk : v.nodes.lookup x = some n) (hft : n.firstTime = some c.i) :
    checkRoot x (v.path.length - 1) c v = .ok ((), v) := by
  obtain ⟨hx, ps, hvp, hlf, hend, _, _⟩ := hP
  have hT := hI.1.1
  have hu := hI.1.2.1
  have hPI := (putInv_after_step c base v B top0 hB hb hT (fun y hy => hu y (reachS_tReach _ _ _ _ hy)) hR).1
  have hnd : (v.nodes.map Prod.fst).Nodup := by rw [hbk.ids]; exact ht_nodup_reverse hbk.nodup
  have hxt : v.taken.contains x = false := hu x hx
  have hwx : wNode c.p base v x = some n := by
    simp only [wNode, hxt, Bool.false_eq_true, ↓reduceIte, hlk]
  have hXD : nodeAt v.top.rootKey ps ps.length = x := by rw [nodeAt_last, hend]
  have hgetP := LinkedFrom.get _ _ _ ps hlf
  have hXN : ∀ i, i ≤ ps.length → wNode c.p base v (nodeAt v.top.rootKey ps i) =
      some ((wNode c.p base v (nodeAt v.top.rootKey ps i)).getD n) := by
    intro i hi
    rcases Nat.lt_or_ge i ps.length with hlt | hge
    · obtain ⟨_, n', _, h2, _⟩ := hgetP i hlt
      rw [h2]; rfl
    · have : i = ps.length := by omega
      subst this
      rw [hXD, hwx]; rfl
  have hKP : ∀ i, 0 < i → i ≤ ps.length →
      ps[i - 1]? = some (some (((ps[i - 1]?).bind (·.1)).getD 0), nodeAt v.top.rootKey ps i) ∧
      (((ps[i - 1]?).bind (·.1)).getD 0, nodeAt v.top.rootKey ps i) ∈
        ((wNode c.p base v (nodeAt v.top.rootKey ps (i - 1))).getD n).liveAt c.i := by
    intro i h1 h2
    obtain ⟨k, n', e1, e2, e3⟩ := hgetP (i - 1) (by omega)
    have hi : i - 1 + 1 = i := by omega
    rw [hi] at e1 e3
    rw [e1, e2]
    exact ⟨rfl, e3⟩
  have hpX : ∀ i, i ≤ ps.length → (v.path[i]?).map (·.2) = some (nodeAt v.top.rootKey ps i) := by
    intro i hi
    have hl : i < (v.top.rootKey :: ps.map (·.2)).length := by simp; omega
    rw [hvp, ← List.getElem?_map, List.map_cons, List.getElem?_eq_getElem hl]
    simp [nodeAt, List.getElem?_eq_getElem hl]
  have hpK : ∀ i, 0 < i → i ≤ ps.length →
      v.path[i]? = some (some (((ps[i - 1]?).bind (·.1)).getD 0), nodeAt v.top.rootKey ps i) := by
    intro i h1 h2
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [hvp, List.getElem?_cons_succ]
    exact (hKP (j + 1) h1 h2).1
  have hlen : v.path.length - 1 = ps.length := by rw [hvp]; simp
  rw [hlen, ← hXD]
  exact checkRoot_ok_of_J2 c base v B hB.good hPI hJ hb.good hnd (fun i => nodeAt v.top.rootKey ps i)
    (fun i => (wNode c.p base v (nodeAt v.top.rootKey ps i)).getD n)
    (fun i => ((ps[i - 1]?).bind (·.1)).getD 0) ps.length (by simp [nodeAt]) hXN
    (fun i h1 h2 => (hKP i h1 h2).2) hpX hpK n (by rw [hXD]; exact hlk) hft

/-- `rwp_collapseRoot_chkJ` for a condition C as `writerWP_collapseRoot_collJW` (bergdb
025-05, route P): the steps by `collSteps_JW`, the check by `checkRoot_ok_of_segDesc`. -/
theorem rwp_collapseRoot_chkJW (fuelR : Nat) (hfR : 2 ≤ fuelR) (key : Key) (seg : Nat) (c : Ctx)
    (base : View BVal) (hvc : ViewCoherent c base) (w0 : W) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (KO : KindOracle) (hv : ViewIdsBelow B c.view)
    (hk : ViewKinds KO B c) (hICEk : ICEFromKinds c base KO B) (hsa2 : 2 ≤ c.p.splitAbove)
    (C : W → Prop) (hC : ∀ v v', v.next ≤ v'.next → C v' → C v)
    (hfits : ∀ v x n only, C v → CollGetInvF c base w0 v fuelR →
      RangeOrder (wNode c.p base v) c.i v.top.rootKey → SegDesc c base x v →
      v.nodes.lookup x = some n → n.leaf = false → n.firstTime ≠ some c.i →
      n.onlyLiveKlong = some only → n.cv? only = some 0 →
      WriterWP (replaceRoot x (v.path.length - 1) only) c v
        (fun _ v' => C v' → TreeOK (wNode c.p base v') c.i v'.top.rootKey → PutInvG c base v' →
          SegFits (wNode c.p base v') c.i (fuelR - 1) v'.top.rootKey))
    (hpos : 0 < c.i) (hRJ : ReplaceRootFullJ2OKC c base fuelR B) :
    ∀ fuel v, CollInvJW c base w0 fuelR C B top0 KO B B v →
      RWPC (collapseRoot key seg fuel) (collapseRootChk key seg fuel) c v C :=
  rwp_collapseRoot_chkQ key seg c _ _ C
    (collSteps_JW fuelR hfR key seg c base hvc w0 B top0 hB KO B hv hk hICEk hsa2 C hC hfits B hpos hRJ)
    (fun x v d only f hI => by
      rw [writerWP_bind]
      refine writerWP_mono (freshCache_takeBackRoot x d only c v hB.good.ids hI.1) ?_
      rintro _ v1 ⟨hf1, hle1⟩
      refine writerWP_mono (freshCache_collapseRoot key seg f c v1 hB.good.ids hf1) ?_
      rintro _ v2 ⟨_, hle2⟩ hC2
      exact hC v v2 (Nat.le_trans hle1 hle2) hC2)
    (fun x v n hI hCv hP hlk hft => by
      obtain ⟨hI', hR, hb, hbk, _, hJ, _⟩ := hI.2 hCv
      exact checkRoot_ok_of_segDesc c base w0 fuelR B top0 hB v hI' hR hb hbk hJ x n (hP hCv) hlk hft)

/-- Root collapse with the check runs as without it from every state of
`writerWP_collapseRoot_collJC`'s invariant with one first id B for the books, the
kinds' books and the take-back's facts: that lemma's steps, and
`checkRoot_ok_of_segDesc` before each take-back. -/
theorem rwp_collapseRoot_chkJ (fuelR : Nat) (hfR : 2 ≤ fuelR) (key : Key) (seg : Nat) (c : Ctx)
    (base : View BVal) (hvc : ViewCoherent c base) (w0 : W) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (KO : KindOracle) (hv : ViewIdsBelow B c.view)
    (hk : ViewKinds KO B c) (hICEk : ICEFromKinds c base KO B) (hsa2 : 2 ≤ c.p.splitAbove)
    (hfits : ∀ v x n only, CollGetInvF c base w0 v fuelR →
      RangeOrder (wNode c.p base v) c.i v.top.rootKey → SegDesc c base x v →
      v.nodes.lookup x = some n → n.leaf = false → n.firstTime ≠ some c.i →
      n.onlyLiveKlong = some only → n.cv? only = some 0 →
      WriterWP (replaceRoot x (v.path.length - 1) only) c v
        (fun _ v' => SegFits (wNode c.p base v') c.i (fuelR - 1) v'.top.rootKey))
    (hpos : 0 < c.i) (hRJ : ReplaceRootFullJ2OKC c base fuelR B) :
    ∀ fuel v, CollGetInvF c base w0 v fuelR → RangeOrder (wNode c.p base v) c.i v.top.rootKey →
      PutBook c B top0 v → Book B c v → KdInv KO B v → TakeJ2 c base B v → B ≤ v.next →
      RWP (collapseRoot key seg fuel) (collapseRootChk key seg fuel) c v := by
  intro fuel v hI hR hb hbk hik hJ hBn
  exact rwp_of_rwpc (rwp_collapseRoot_chkJW fuelR hfR key seg c base hvc w0 B top0 hB KO hv hk hICEk hsa2
    (fun _ => True) (fun _ _ _ _ => trivial)
    (fun v x n only _ hI hR hP hlk hxl hm honly hcv => writerWP_mono
      (hfits v x n only hI hR hP hlk hxl hm honly hcv) (fun _ _ hf _ _ _ => hf))
    hpos hRJ fuel v ⟨hb.fresh, fun _ => ⟨hI, hR, hb, hbk, hik, hJ, hBn⟩⟩) (fun _ => trivial)
/-- The merges' loop keeps the books. -/
theorem putBook_mergeUp (key : Key) (g fuel h : Nat) (merged : Bool) (c : Ctx) (base : View BVal)
    (B : NodeId) (top0 : Top) (hB : PutBase c base B) (w : W) (hw : PutBook c B top0 w) :
    WriterWP (mergeUp key g fuel h merged) c w (fun _ w' => PutBook c B top0 w') :=
  putBook_of_keeps _ c base B top0 hB w hw (klongsWf_mergeUp key g fuel h merged)
    (good_mergeUp B key g fuel h merged) (book_mergeUp B key g fuel h merged)
    (@state_mergeUp (allocatedIdsInvariant B) key g fuel h merged)
    (@state_mergeUp (commitInvariant top0) key g fuel h merged)
    (freshCache_mergeUp key g fuel h merged) (ptrs_mergeUp _ key g fuel h merged)

set_option maxHeartbeats 1600000 in
/-- `afterDelete` runs as `afterDeleteChk` from a state with `DelInvJ` and the
books of one first id B, where the merges' loop runs as its checked copy: the
merges' loop keeps both (`writerWP_mergeUp_delJ`, `putBook_mergeUp`), and root
collapse runs as its checked copy (`rwp_collapseRoot_chkJ`). -/
theorem rwp_afterDelete_of_J (key : Key) (g h : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (fuelR : Nat) (hfR : 2 ≤ fuelR) (hM : MergeStepOK c base fuelR)
    (hC : CollapseFitsOK c base fuelR) (KO : KindOracle) (B : NodeId) (hv : ViewIdsBelow B c.view)
    (hk : ViewKinds KO B c) (hICEk : ICEFromKinds c base KO B) (hsa2 : 2 ≤ c.p.splitAbove)
    (hcap : 1 ≤ c.p.mergeMax) (hpos : 0 < c.i) (hRJ : ReplaceRootFullJ2OKC c base fuelR B)
    (top0 : Top) (hB : PutBase c base B) (w0 : W) (k0 : Key) (v : W)
    (hJ : DelInvJ c base w0 k0 fuelR KO B B v) (hb : PutBook c B top0 v)
    (hmu : RWP (mergeUp key g c.p.fuel h false) (mergeUpChk key g c.p.fuel h false) c v) :
    RWP (afterDelete key g h) (afterDeleteChk key g h) c v := by
  unfold afterDelete afterDeleteChk
  refine rwp_read ?_
  refine rwp_ite (fun _ => ?_) (fun _ => rwp_refl _ _ _)
  refine rwp_bind2 (fun _ v1 => DelInvJ c base w0 k0 fuelR KO B B v1 ∧ PutBook c B top0 v1) hmu
    (writerWP_and (writerWP_mergeUp_delJ key g c base hvc fuelR hfR hM KO B hv hk hICEk hsa2 hcap B hpos
      w0 k0 c.p.fuel h false v hJ) (putBook_mergeUp key g c.p.fuel h false c base B top0 hB v hb)) ?_
  rintro r v1 ⟨hJ1, hb1⟩
  refine rwp_ite (fun _ => ?_) (fun _ => rwp_refl _ _ _)
  obtain ⟨⟨⟨hP, _, hR, hICE, hF, _, _⟩, hbk, hik⟩, hJ', hBn⟩ := hJ1
  have hCI : CollGetInvF c base v1 v1 fuelR := by
    refine ⟨⟨hP.tree, fun y hy => hP.untaken y (tReach_reachS _ _ _ _ hy),
      fun y yn _ h => hP.times y yn h, fun y yn cc z hy hyn hl hc => hICE y yn cc z hy hyn hl hc⟩,
      fun _ => rfl, hF, fun y yn _ h => hP.wf y yn h, fun y yn _ h => hP.keyNoValue y yn h⟩
  exact rwp_collapseRoot_chkJ fuelR hfR key g c base hvc v1 B top0 hB KO hv hk hICEk hsa2 (hC v1) hpos hRJ
    c.p.fuel v1 hCI hR hb1 hbk hik hJ' hBn

/-- At every state, `afterDeleteJ J` runs as `afterDeleteChk` when every state of
J lets `afterDelete` run as `afterDeleteChk` where the merges' loop runs as its
checked copy. -/
theorem rwp_afterDeleteJ (J : W → Prop) (key : Key) (g h : Nat) (c : Ctx)
    (hJ : ∀ v, J v → RWP (mergeUp key g c.p.fuel h false) (mergeUpChk key g c.p.fuel h false) c v →
      RWP (afterDelete key g h) (afterDeleteChk key g h) c v) (v : W) :
    RWP (afterDeleteJ J key g h) (afterDeleteChk key g h) c v := by
  intro x hx
  unfold afterDeleteJ at hx
  obtain ⟨a, v1, h1, h2⟩ := (m_bind_ok _ _ c v x).mp hx
  obtain ⟨ha, hv1⟩ := ((writerWP_read c v (fun a w' => a = c ∧ w' = v)).mpr ⟨rfl, rfl⟩) a v1 h1
  subst a; subst v1
  obtain ⟨b, v2, h3, h4⟩ := (m_bind_ok _ _ c v x).mp h2
  obtain ⟨hb, hv2⟩ := ((writerWP_get c v (fun b w' => b = v ∧ w' = v)).mpr ⟨rfl, rfl⟩) b v2 h3
  subst b; subst v2
  split at h4
  · rename_i hc
    exact hJ v hc.1 hc.2 x h4
  · exact ((writerWP_throw _ c v (fun _ _ => False)) _ _ h4).elim

set_option maxHeartbeats 1600000 in
/-- `OpDelChk5OKR` from `OpDelChk6OKR`, given that `afterDelete` runs as its checked
copy at the calls with `DelHoleJ` where the merges' loop does (`hAD`; bergdb 025-05). -/
theorem opDelChk5OKR_of_chk6G (p : Params) (R : Struct BVal → Time → Prop)
    (hAD : ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
      lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
      topOf p (ctxOf p ts).view z = .ok top →
      ∀ pre key post, tx.ops = pre ++ Op.del key :: post →
      ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w →
      HtInv (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) w →
      ∀ (key' : Key) (g h : Nat) (v : W), DelHoleJ p ts tx top w key v →
      RWP (mergeUp key' g (ctxOf p ts).p.fuel h false) (mergeUpChk key' g (ctxOf p ts).p.fuel h false)
        (ctxOf p ts) v →
      RWP (afterDelete key' g h) (afterDeleteChk key' g h) (ctxOf p ts) v)
    (h6 : OpDelChk6OKR p R) : OpDelChk5OKR p R := by
  intro ts tx hw hr z top hz htop pre key post hs r w hpre hI hRO hL hH hJ r' v he
  have h6' := h6 ts tx hw hr z top hz htop pre key post hs r w hpre hI hRO hL hH hJ r' v he
  rw [putKvDelChk5_eq]
  refine rwp_putKvDP (afterDeleteJ (DelHoleJ p ts tx top w key)) afterDeleteChk (ctxOf p ts) ?_ key w _ h6'
  intro key' g h v'
  refine rwp_afterDeleteJ _ key' g h (ctxOf p ts) ?_ v'
  intro v'' hJ'' hmu
  exact hAD ts tx hw hr z top hz htop pre key post hs r w hpre hI hH key' g h v'' hJ'' hmu

/-- `OpDelChk5OKR` from `OpDelChk6OKR`, given the merges' fuel (`MergeStepOK`,
from `hMSF`) and the collapse's (`CollapseFitsOK`, `hCoF`): root collapse's
check is proved. -/
theorem opDelChk5OKR_of_chk6 (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove) (hcap : 1 ≤ p.mergeMax)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRP : ∀ P t, R P t → PointersOK P)
    (hRK : ∀ P t, R P t → KindsAllOK p P)
    (hMS : ∀ ts, MergeStepOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hCo : ∀ ts, CollapseFitsOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (h6 : OpDelChk6OKR p R) : OpDelChk5OKR p R := by
  refine opDelChk5OKR_of_chk6G p R ?_ h6
  intro ts tx hw hr z top hz htop pre key post hs r w hpre _ _ key' g h v'' ⟨hJ'', hb''⟩ hmu
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  obtain ⟨hv, hk, _, _⟩ := kd_contextR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top pre (Op.del key :: post)
    hs r w hpre
  have hICEk : ICEFromKinds (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base :=
    fun v hb hi hun => innerChildren_of_kinds p (treeRun p ts) tx.base (ctxOf p ts) v rfl (hRK _ _ hr)
      (hRP _ _ hr) hb hi.cache hun
  have hfR : 2 ≤ p.fuel + 1 := by unfold Params.fuel; omega
  exact rwp_afterDelete_of_J key' g h (ctxOf p ts) _ (viewCoherent_ctxOf p ts) (p.fuel + 1) hfR (hMS ts) (hCo ts)
    _ tx.base hv hk hICEk (by simpa [ctxOf] using hsa2) (by simpa [ctxOf] using hcap) (by simp [ctxOf])
    (replaceRootFullJ2OKC_run p hsa2 ts tx.base) top hB w key v'' hJ'' hb'' hmu
end SIS.Tree
