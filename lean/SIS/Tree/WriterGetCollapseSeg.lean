/-
Root collapse at a segment root keeps every reading (bergdb 024-12, TP10's
`OpGetOK`; 024-22): the segment leaf's klong that named the root x names x's
child instead, which reads every rest of a key as x did (`getFromR_subst`,
`getFromR_collapse_reach`).
-/
import SIS.Tree.WriterGetCollapse
import SIS.Tree.WriterTreeCollapseSeg
import SIS.Tree.FuelPaths

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- A node reached in a tree roots a tree. -/
theorem treeOK_reached (N : NodeId → Option KNode) (t : Time) (r : NodeId) (hT : TreeOK N t r) :
    ∀ x, TReach N t r x → (∃ n, N x = some n) → TreeOK N t x := by
  intro x hx
  induction hx with
  | root => intro _; exact hT
  | @link u c z hu hl ih =>
    intro hz
    obtain ⟨un, hun, _⟩ := hl
    exact treeOK_child N t u z c (ih ⟨un, hun⟩) ⟨un, hun, by assumption⟩ hz

/-- `getFromR_collapse` with N' agreeing with N only on what R reaches. -/
theorem getFromR_collapse_reach (N N' : NodeId → Option KNode) (V : NodeId → Option Nat) (t : Time)
    (fuel : Nat) (R y : NodeId) (n : KNode) (hT : TreeOK N t R) (hRn : N R = some n)
    (hRl : n.leaf = false) (hlive : ∀ c z, (c, z) ∈ n.live ↔ c = 0 ∧ z = y)
    (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ t)
    (hother : ∀ x, ReachS N t R x → x ≠ R → N' x = N x)
    (hwf : ∀ x xn, ReachS N t R x → N x = some xn → klongsWf xn.ks = true)
    (hdepth : PathsFit N t R fuel) :
    ∀ key, getFromR N' V t fuel key y = getFromR N V t fuel key R := by
  obtain ⟨f, hf⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by have := hdepth R 0 PathLen.root; omega⟩
  have hRy : (0, y) ∈ n.liveAt t := by
    rw [KNode.liveAt_of_times n t hnt]; exact (hlive 0 y).mpr ⟨rfl, rfl⟩
  have hlink : TLink N t R 0 y := ⟨n, hRn, hRy⟩
  have hyR : y ≠ R := fun h => hT.rootFree R 0 TReach.root (by rw [h] at hlink; exact hlink)
  have hlinks : ∀ x xn c z, ReachS N t R x → N x = some xn → (c, z) ∈ xn.liveAt t →
      ¬ (fun u => u = R) z := by
    intro x xn c z hx hxn hm hz
    exact hT.rootFree x c (reachS_tReach N t R x hx) (by rw [← hz]; exact ⟨xn, hxn, hm⟩)
  have hsame : ∀ x, ReachS N t R x → ¬ (fun u => u = R) x → N' x = N x :=
    fun x hx hxR => hother x hx hxR
  have hyS : ReachS N t R y := tReach_reachS N t R y (TReach.link TReach.root hlink)
  have hfirst : ∀ c, getEqR N' t c fuel y = getEqR N t c fuel R := by
    intro c
    rw [getEqR_avoid N N' t R (fun u => u = R) hsame hlinks c fuel y hyS hyR, hf,
      getEqR_fuel_succ N t R c f y 1 (PathLen.link PathLen.root hlink)
        (fun z k hz => by have := hdepth z k hz; omega)]
    simp only [getEqR, hRn, hRl, Bool.false_eq_true, ↓reduceIte]
    have hs := KNode.searchLte_of_max n t hnt c 0 y ((hlive 0 y).mpr ⟨rfl, rfl⟩) (by omega)
      (fun q hq _ => by have := ((hlive q.1 q.2).mp hq).1; omega)
    cases hfd : n.searchLte t c with
    | none => rw [hfd] at hs; cases hs
    | some fd =>
      rw [hfd] at hs
      simp only [Option.map_some, Option.some.injEq] at hs
      simp only [hs]
  exact getFromR_newRoot_sim N N' V t fuel R y (fun u => u = R) hfirst hwf hsame hlinks

/-! ## A leaf's klong to x named to x's child -/

/-- The search of a key's compare value in N' where leaf L's klong k names y'
instead of x, and no other reached node names x: what N finds, with x replaced
by y'. -/
theorem getEqR_subst (N N' : NodeId → Option KNode) (t : Time) (r0 L x y' : NodeId) (k : Nat)
    (ln ln' : KNode) (hL : N L = some ln) (hL' : N' L = some ln') (hll : ln.leaf = true)
    (hll' : ln'.leaf = true)
    (hs : ∀ c, c ≠ k → (ln'.searchEq t c).map (·.y) = (ln.searchEq t c).map (·.y))
    (hk : (ln.searchEq t k).map (·.y) = some x) (hk' : (ln'.searchEq t k).map (·.y) = some y')
    (hother : ∀ u, u ≠ L → u ≠ x → N' u = N u)
    (hnox : ∀ u un, ReachS N t r0 u → N u = some un → ∀ c z, (c, z) ∈ un.liveAt t → z = x →
      u = L ∧ c = k)
    (hwf : ∀ u un, ReachS N t r0 u → N u = some un → klongsWf un.ks = true) (cv : Nat) :
    ∀ f u, ReachS N t r0 u → u ≠ x →
      getEqR N' t cv f u = (getEqR N t cv f u).map (fun z => if z = x then y' else z) := by
  intro f
  induction f with
  | zero => intro u _ _; rfl
  | succ f ih =>
    intro u hu hux
    by_cases huL : u = L
    · subst huL
      simp only [getEqR, hL, hL', hll, hll', ↓reduceIte]
      by_cases hc : cv = k
      · subst hc
        rw [hk, hk']
        simp
      · rw [hs cv hc]
        cases hfd : ln.searchEq t cv with
        | none => rfl
        | some fd =>
          have hm := KNode.searchEq_mem ln t cv fd (hwf u ln hu hL) hfd
          have hne : fd.y ≠ x := fun he => hc (hnox u ln hu hL cv fd.y hm he).2
          simp [hne]
    · rw [getEqR, getEqR, hother u huL hux]
      cases hN : N u with
      | none => rfl
      | some un =>
        simp only
        split
        · cases hfd : un.searchEq t cv with
          | none => rfl
          | some fd =>
            have hm := KNode.searchEq_mem un t cv fd (hwf u un hu hN) hfd
            have hne : fd.y ≠ x := fun he => huL (hnox u un hu hN cv fd.y hm he).1
            simp [hne]
        · cases hfd : un.searchLte t cv with
          | none => rfl
          | some fd =>
            have hm := KNode.searchLte_mem un t cv fd hfd
            have hne : fd.y ≠ x := fun he => huL (hnox u un hu hN fd.c fd.y hm he).1
            exact ih fd.y (ReachS.step u un fd.c fd.y hu hN hm) hne

/-- Every key reads in N' as in N, where leaf L's klong k names y' instead of x,
no other reached node names x, and every rest of a key reads from y' in N' as
from x in N. -/
theorem getFromR_subst (N N' : NodeId → Option KNode) (V : NodeId → Option Nat) (t : Time)
    (fuel : Nat) (r0 L x y' : NodeId) (k : Nat) (ln ln' : KNode) (hL : N L = some ln)
    (hL' : N' L = some ln') (hll : ln.leaf = true) (hll' : ln'.leaf = true)
    (hs : ∀ c, c ≠ k → (ln'.searchEq t c).map (·.y) = (ln.searchEq t c).map (·.y))
    (hk : (ln.searchEq t k).map (·.y) = some x) (hk' : (ln'.searchEq t k).map (·.y) = some y')
    (hother : ∀ u, u ≠ L → u ≠ x → N' u = N u)
    (hnox : ∀ u un, ReachS N t r0 u → N u = some un → ∀ c z, (c, z) ∈ un.liveAt t → z = x →
      u = L ∧ c = k)
    (hwf : ∀ u un, ReachS N t r0 u → N u = some un → klongsWf un.ks = true)
    (hsome : (N' y').isSome = (N x).isSome) (hV : V y' = V x)
    (hsub : ∀ rest, getFromR N' V t fuel rest y' = getFromR N V t fuel rest x) :
    ∀ key u, ReachS N t r0 u → u ≠ x → getFromR N' V t fuel key u = getFromR N V t fuel key u := by
  have hsomeL : ∀ u, u ≠ x → (N' u).isSome = (N u).isSome := by
    intro u hux
    by_cases huL : u = L
    · rw [huL, hL, hL']; rfl
    · rw [hother u huL hux]
  intro key
  induction key with
  | nil => intro u _ _; rfl
  | cons cv rest ih =>
    intro u hu hux
    have he := getEqR_subst N N' t r0 L x y' k ln ln' hL hL' hll hll' hs hk hk' hother hnox hwf cv
      fuel u hu hux
    cases rest with
    | nil =>
      simp only [getFromR]
      rw [he]
      cases hg : getEqR N t cv fuel u with
      | none => rfl
      | some z =>
        by_cases hz : z = x
        · subst hz; simp [hV]
        · simp [hz]
    | cons d rest' =>
      simp only [getFromR]
      rw [he]
      cases hg : getEqR N t cv fuel u with
      | none => rfl
      | some z =>
        by_cases hz : z = x
        · subst hz
          simp only [Option.map_some, ↓reduceIte]
          rw [hsome, hsub]
        · simp only [Option.map_some, hz, ↓reduceIte]
          rw [hsomeL z hz, ih z (getEqR_reach N t r0 cv hwf fuel u z hu hg) hz]

/-- The reading after a collapse at a segment root x below the leaf L: L's klong
k to x names x's only child y instead (its other live klongs kept), x is
unreached; every key reads as before, given the fuel for the tree. -/
theorem getFromR_segCollapse (N N' : NodeId → Option KNode) (V : NodeId → Option Nat) (t : Time)
    (fuel : Nat) (r L x y : NodeId) (k : Nat) (ln ln' n : KNode) (hT : TreeOK N t r)
    (hLr : TReach N t r L) (hL : N L = some ln) (hL' : N' L = some ln') (hll : ln.leaf = true)
    (hll' : ln'.leaf = true) (hlnwf : klongsWf ln.ks = true) (hlnwf' : klongsWf ln'.ks = true)
    (hlnt : ∀ s, Klong.time s ∈ ln.ks → s ≤ t) (hlnt' : ∀ s, Klong.time s ∈ ln'.ks → s ≤ t)
    (hlook : ∀ c, ln'.live.lookup c = if k == c then some y else ln.live.lookup c)
    (hk : (k, x) ∈ ln.liveAt t) (hx : N x = some n) (hxl : n.leaf = false)
    (hlive : ∀ c z, (c, z) ∈ n.live ↔ c = 0 ∧ z = y) (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ t)
    (hy : ∃ m, N y = some m)
    (hother : ∀ u, u ≠ L → u ≠ x → N' u = N u)
    (hwf : ∀ u un, ReachS N t r u → N u = some un → klongsWf un.ks = true)
    (hfit : PathsFit N t r fuel) (hV : V y = V x) :
    ∀ key, getFromR N' V t fuel key r = getFromR N V t fuel key r := by
  have hlkL : TLink N t L k x := ⟨ln, hL, hk⟩
  have hxR : TReach N t r x := TReach.link hLr hlkL
  have hxr : r ≠ x := fun h => hT.rootFree L k hLr (by rw [h]; exact hlkL)
  have hyx : (0, y) ∈ n.liveAt t := by
    rw [KNode.liveAt_of_times n t hnt]; exact (hlive 0 y).mpr ⟨rfl, rfl⟩
  have hlxy : TLink N t x 0 y := ⟨n, hx, hyx⟩
  have hyR : TReach N t r y := TReach.link hxR hlxy
  -- nothing x reaches is L
  have hnoL : ∀ u, TReach N t x u → u ≠ L := by
    intro u hu huL
    rw [huL] at hu
    obtain ⟨a, ha⟩ := hu.pathLen
    exact hT.no_cycle hxR (k := a + 1) (by omega) (PathFromLen.link ha.toFrom hlkL)
  have hxL : x ≠ L := fun h => hnoL x TReach.root h
  have hyx' : y ≠ x := fun h => hT.no_self_link x 0 hxR (by rw [h] at hlxy; exact hlxy)
  have hyL : y ≠ L := hnoL y (TReach.link TReach.root hlxy)
  have hlkLive : ∀ c, (ln'.searchEq t c).map (·.y) = ln'.live.lookup c :=
    KNode.searchEq_live ln' t hlnwf' hlnt'
  have hlkLive0 : ∀ c, (ln.searchEq t c).map (·.y) = ln.live.lookup c :=
    KNode.searchEq_live ln t hlnwf hlnt
  have hkx : ln.live.lookup k = some x := by
    rw [KNode.liveAt_of_times ln t hlnt] at hk
    exact lookup_some_of_mem (KNode.live_keys_nodup ln) hk
  obtain ⟨a, ha⟩ := hxR.pathLen
  intro key
  refine getFromR_subst N N' V t fuel r L x y k ln ln' hL hL' hll hll' ?_ ?_ ?_ hother ?_ hwf ?_ hV ?_
    key r ReachS.root hxr
  · intro c hc
    rw [hlkLive, hlkLive0, hlook c]
    have : (k == c) = false := by simpa using (Ne.symm hc)
    simp [this]
  · rw [hlkLive0, hkx]
  · rw [hlkLive, hlook k]; simp
  · intro u un hu hun c z hm hz
    rw [hz] at hm
    exact hT.oneLink u c L k x (reachS_tReach N t r u hu) hLr ⟨un, hun, hm⟩ hlkL
  · obtain ⟨m, hm⟩ := hy
    rw [hother y hyL hyx', hm, hx]; rfl
  · intro rest
    exact getFromR_collapse_reach N N' V t fuel x y n
      (treeOK_reached N t r hT x hxR ⟨n, hx⟩) hx hxl hlive hnt
      (fun u hu hux => hother u (hnoL u (reachS_tReach N t x u hu)) hux)
      (fun u un hu hun => hwf u un (by
        obtain ⟨b, hb⟩ := (reachS_tReach N t x u hu).pathLen
        exact tReach_reachS N t r u (ha.append hb.toFrom).reach) hun)
      (by
        intro z kk hz
        have := hfit z (a + kk) (ha.append hz.toFrom)
        have h0 : 0 < a := by
          rcases Nat.eq_zero_or_pos a with h | h
          · subst h
            cases ha with
            | root => exact absurd rfl hxr
          · exact h
        omega) rest

/-! ## The writer's collapse steps at a segment root -/

/-- `takeBackRoot` at a segment root x that the transaction made, below the
segment leaf `leaf`: the leaf's klong k names x's child in place, x is taken
back; every key reads as before. -/
theorem writerWP_takeBackRoot_seg_get (x : NodeId) (d only : Nat) (n : KNode) (leaf : NodeId)
    (ln : KNode) (k : Nat) (c : Ctx) (base : View BVal) (w : W)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hlf : TReach (wNode c.p base w) c.i w.top.rootKey leaf)
    (hlkL : w.nodes.lookup leaf = some ln) (hLt : w.taken.contains leaf = false)
    (hlnt : ∀ s, Klong.time s ∈ ln.ks → s ≤ c.i) (hlnwf : klongsWf ln.ks = true)
    (hlnl : ln.leaf = true) (hk : (k, x) ∈ ln.liveAt c.i)
    (hlkx : w.nodes.lookup x = some n) (hxt : w.taken.contains x = false)
    (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ c.i) (honly : n.onlyLiveKlong = some only)
    (hcv : n.cv? only = some 0) (hxl : n.leaf = false)
    (hpd : (w.path[d]?).map (·.2) = some leaf) (hpk : w.path[d + 1]? = some (some k, x))
    (hwf : ∀ u un, ReachS (wNode c.p base w) c.i w.top.rootKey u → wNode c.p base w u = some un →
      klongsWf un.ks = true)
    (hfit : PathsFit (wNode c.p base w) c.i w.top.rootKey c.p.fuel)
    (hnoval : ∀ u un, wNode c.p base w u = some un → wValue base w u = none)
    (hchild : ∀ cc z, (cc, z) ∈ n.liveAt c.i → ∃ m, wNode c.p base w z = some m) :
    WriterWP (takeBackRoot x (d + 1) only) c w (fun _ w' =>
      ∀ key, wGet c.p c.i base w' key = wGet c.p c.i base w key) := by
  have hwL : wNode c.p base w leaf = some ln := by
    simp only [wNode, hLt, Bool.false_eq_true, ↓reduceIte, hlkL]
  have hwx : wNode c.p base w x = some n := by
    simp only [wNode, hxt, Bool.false_eq_true, ↓reduceIte, hlkx]
  have hlx : leaf ≠ x := fun h => hT.no_self_link leaf k hlf ⟨ln, hwL, by rw [h]; exact hk⟩
  unfold takeBackRoot
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c w hlkx]
  cases hp : n.ptr? only with
  | none => exact writerWP_throw _ _ _ _
  | some child =>
    obtain ⟨c0, hk0, hlv⟩ := onlyLiveKlong_live_iff n only child honly hp
    have hc0 : c0 = 0 := by
      have h1 : n.cv? only = some c0 := by simp [KNode.cv?, hk0]
      rw [h1] at hcv; simpa using hcv
    subst hc0
    simp only [note, writerWP_bind, writerWP_modify]
    refine writerWP_pathNode_known d leaf c _ (by exact hpd) _ ?_
    rw [writerWP_getNode_known leaf ln c _ (by simpa using hlkL)]
    refine writerWP_klongAt_known (d + 1) k x c _ (by exact hpk) _ ?_
    split
    · rename_i j hj
      split
      · exact writerWP_throw _ _ _ _
      · simp only [putNode, writerWP_bind, writerWP_modify]
        refine (writerWP_takenBack_iff x c _ _).mpr ?_
        simp only
        have hLt' : (x :: w.taken).contains leaf = false := by
          rw [List.contains_cons]
          have : (leaf == x) = false := by simpa using hlx
          rw [this, Bool.false_or]; exact hLt
        have hyt : ∀ y, y ≠ x → (x :: w.taken).contains y = w.taken.contains y := by
          intro y hyx
          rw [List.contains_cons]
          have : (y == x) = false := by simpa using hyx
          simp [this]
        obtain ⟨m, hm⟩ := hchild 0 child (by
          rw [KNode.liveAt_of_times n c.i hnt]; exact (hlv 0 child).mpr ⟨rfl, rfl⟩)
        have hfin : ∀ w' : W, w'.vals = w.vals → w'.taken = x :: w.taken →
            w'.nodes = upsert w.nodes leaf (ln.repoint j child) → w'.top = w.top →
            ∀ key, wGet c.p c.i base w' key = wGet c.p c.i base w key := by
          intro w' h'v h't h'n h'top key
          have hV : wValue base w' = wValue base w :=
            wValue_eq_of_taken base w w' h'v (fun z => z = x) (fun z hz => by rw [h't]; exact hyt z hz)
              (fun z hz => by rw [hz]; exact ⟨hxt, hnoval x n hwx⟩)
          unfold wGet
          rw [hV, h'top]
          refine getFromR_segCollapse (wNode c.p base w) _ (wValue base w) c.i c.p.fuel w.top.rootKey
            leaf x child k ln (ln.repoint j child) n hT hlf hwL ?_ hlnl
            (by rw [mrg_repoint_leaf]; exact hlnl)
            hlnwf (by rw [KNode.repoint_klongsWf]; exact hlnwf) hlnt
            (KNode.repoint_times ln j child c.i hlnt)
            (KNode.repoint_live_lookup ln x child k j hj) hk hwx hxl hlv hnt ⟨m, hm⟩ ?_ hwf hfit ?_ key
          · simp only [wNode, h't, hLt', Bool.false_eq_true, ↓reduceIte, h'n, lookup_upsert]
          · intro y hyl hyx
            simp only [wNode, h't, hyt y hyx, h'n, lookup_upsert, hyl, ↓reduceIte]
          · rw [hnoval child m hm, hnoval x n hwx]
        exact hfin _ rfl rfl rfl rfl
    · exact writerWP_throw _ _ _ _

/-- `replaceRoot` at a segment root x below the segment leaf `leaf` with room:
x is unlinked, the leaf gets a klong k to x's child; every key reads as before. -/
theorem writerWP_replaceRoot_seg_get (x : NodeId) (d only : Nat) (n : KNode) (leaf : NodeId)
    (ln : KNode) (k : Nat) (c : Ctx) (base : View BVal) (w : W)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hlf : TReach (wNode c.p base w) c.i w.top.rootKey leaf)
    (hlkL : w.nodes.lookup leaf = some ln) (hLt : w.taken.contains leaf = false)
    (hlnwf : klongsWf ln.ks = true) (hlnt : ∀ s, Klong.time s ∈ ln.ks → s ≤ c.i)
    (hlnl : ln.leaf = true) (hk : (k, x) ∈ ln.liveAt c.i)
    (hlkx : w.nodes.lookup x = some n) (hxt : w.taken.contains x = false)
    (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ c.i) (honly : n.onlyLiveKlong = some only)
    (hcv : n.cv? only = some 0) (hxl : n.leaf = false)
    (hpd : (w.path[d]?).map (·.2) = some leaf) (hpk : w.path[d + 1]? = some (some k, x))
    (hroom : ln.size + 1 + 1 ≤ c.p.M)
    (hdead : ∀ y, deadOver c.p (ln.add c.i (.key k y)) = false)
    (hwf : ∀ u un, ReachS (wNode c.p base w) c.i w.top.rootKey u → wNode c.p base w u = some un →
      klongsWf un.ks = true)
    (hfit : PathsFit (wNode c.p base w) c.i w.top.rootKey c.p.fuel)
    (hnoval : ∀ u un, wNode c.p base w u = some un → wValue base w u = none)
    (hchild : ∀ cc z, (cc, z) ∈ n.liveAt c.i → ∃ m, wNode c.p base w z = some m) :
    WriterWP (replaceRoot x (d + 1) only) c w (fun _ w' =>
      ∀ key, wGet c.p c.i base w' key = wGet c.p c.i base w key) := by
  have hwL : wNode c.p base w leaf = some ln := by
    simp only [wNode, hLt, Bool.false_eq_true, ↓reduceIte, hlkL]
  have hwx : wNode c.p base w x = some n := by
    simp only [wNode, hxt, Bool.false_eq_true, ↓reduceIte, hlkx]
  have hlx : leaf ≠ x := fun h => hT.no_self_link leaf k hlf ⟨ln, hwL, by rw [h]; exact hk⟩
  unfold replaceRoot
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c w hlkx]
  cases hp : n.ptr? only with
  | none => exact writerWP_throw _ _ _ _
  | some child =>
    obtain ⟨c0, hk0, hlv⟩ := onlyLiveKlong_live_iff n only child honly hp
    have hc0 : c0 = 0 := by
      have h1 : n.cv? only = some c0 := by simp [KNode.cv?, hk0]
      rw [h1] at hcv; simpa using hcv
    subst hc0
    simp only [note, writerWP_bind, writerWP_modify]
    refine writerWP_pathNode_known d leaf c _ (by exact hpd) _ ?_
    refine writerWP_klongAt_known (d + 1) k x c _ (by exact hpk) _ ?_
    refine writerWP_mono (writerWP_unlink_frameV x c _) ?_
    intro _ w1 ⟨h1t, h1top, _, h1v, h1l⟩
    have hlk1 : w1.nodes.lookup leaf = some ln := by rw [h1l leaf hlx]; exact hlkL
    refine writerWP_mono (writerWP_appendKlongs_room d leaf ln k child c w1 hlk1 hroom (hdead _)) ?_
    intro _ w2 h2
    subst h2
    intro key
    have hV : wValue base { w1 with nodes := upsert w1.nodes leaf (ln.add c.i (.key k child)) } =
        wValue base w := wValue_congr' base _ w h1t h1v
    obtain ⟨m, hm⟩ := hchild 0 child (by
      rw [KNode.liveAt_of_times n c.i hnt]; exact (hlv 0 child).mpr ⟨rfl, rfl⟩)
    unfold wGet
    rw [hV]
    simp only
    rw [h1top]
    refine getFromR_segCollapse (wNode c.p base w) _ (wValue base w) c.i c.p.fuel w.top.rootKey
      leaf x child k ln (ln.add c.i (.key k child)) n hT hlf hwL ?_ hlnl
      (by rw [KNode.add_leaf]; exact hlnl) hlnwf (KNode.add_key_wf ln c.i k child hlnwf) hlnt
      (KNode.add_times ln c.i (.key k child) (fun s h => by cases h) hlnt)
      (fun cc => KNode.add_key_live_lookup_of_wf ln c.i k cc child hlnwf) hk hwx hxl hlv hnt ⟨m, hm⟩
      ?_ hwf hfit ?_ key
    · simp only [wNode, h1t, hLt, Bool.false_eq_true, ↓reduceIte, lookup_upsert]
    · intro y hyl hyx
      simp only [wNode, h1t, lookup_upsert, hyl, ↓reduceIte, h1l y hyx]
    · rw [hnoval child m hm, hnoval x n hwx]

end SIS.Tree
