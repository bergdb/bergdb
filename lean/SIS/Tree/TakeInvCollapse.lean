/-
Root collapse keeps the take-back's (B) (bergdb 024-12, TP4; TakeBackRun.lean):
prover cost's loop `writerWP_collapseRoot_coll` with J = `TakeJ`, (B) at
node-map level (`LiveReachedN`) and two facts of the nodes before the
transaction that its steps need: their klongs before the transaction's time
name nodes below B (`OldBelowN`), and they have a first time before it
(`OldStartN`, so a node made by the transaction is at or above B). The root that
gives way is taken back (`takeBackRoot`) or keeps its klongs before the
transaction (`unlink`, `unlinked_live_below`).
-/
import SIS.Tree.TakeInvTree
import SIS.Tree.WriterKindsRules

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The nodes below B have a first time before t. -/
def OldStartN (N : NodeId → Option KNode) (t : Time) (B : NodeId) : Prop :=
  ∀ q qn, N q = some qn → q < B → ∃ s, s < t ∧ qn.firstTime = some s

/-- What root collapse keeps of (B): `LiveReachedN`, `OldBelowN`, `OldStartN`. -/
def TakeJ (c : Ctx) (base : View BVal) (B : NodeId) (v : W) : Prop :=
  LiveReachedN (wNode c.p base v) c.i v.top.rootKey B ∧ OldBelowN (wNode c.p base v) c.i B ∧
  OldStartN (wNode c.p base v) c.i B

theorem takeJ_of_readsAs (c : Ctx) (base : View BVal) (B : NodeId) (v v' : W)
    (h : TakeJ c base B v) (hr : ReadsAs c.p base v v') : TakeJ c base B v' := by
  unfold TakeJ
  rw [hr.1, hr.2.1]
  exact h

/-- A node of the transaction's time t is at or above B. -/
theorem ge_of_firstTime (N : NodeId → Option KNode) (t : Time) (B : NodeId) (hO : OldStartN N t B)
    (q : NodeId) (qn : KNode) (hq : N q = some qn) (hf : qn.firstTime = some t) : B ≤ q := by
  rcases Nat.lt_or_ge q B with h | h
  · obtain ⟨s, hs, hf'⟩ := hO q qn hq h
    rw [hf] at hf'
    cases hf'
    omega
  · exact h

/-- `unlink` of a cached node: its klongs of the transaction dropped if its last
time is the transaction's, nothing else changed. -/
theorem writerWP_unlink_fate (x : NodeId) (n : KNode) (c : Ctx) (w : W)
    (hx : w.nodes.lookup x = some n) :
    WriterWP (unlink x) c w (fun _ v => v.taken = w.taken ∧ v.top = w.top ∧ v.vals = w.vals ∧
      v.nodes.lookup x = some (if n.lastTime == some c.i then n.toPrev (c.i - 1) else n) ∧
      (∀ y, y ≠ x → v.nodes.lookup y = w.nodes.lookup y)) := by
  unfold unlink
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c w hx]
  split
  · rename_i h
    simp only [putNode, writerWP_modify]
    refine ⟨trivial, trivial, trivial, ?_, ?_⟩
    · simp only [lookup_upsert, ↓reduceIte]
    · intro y hy
      simp only [lookup_upsert, hy, ↓reduceIte]
  · rename_i h
    simp only [writerWP_pure]
    refine ⟨trivial, trivial, trivial, ?_, fun _ _ => trivial⟩
    exact hx

/-! ## Live klongs of a repointed or extended leaf -/

theorem KNode.repoint_liveAt_new (n : KNode) (x y : NodeId) (k j : Nat) (t : Time)
    (hj : n.linkIndex x k = some j) (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t) :
    (k, y) ∈ (n.repoint j y).liveAt t := by
  rw [KNode.liveAt_of_times _ t (KNode.repoint_times n j y t ht)]
  apply mem_of_lookup_nodup
  rw [KNode.repoint_live_lookup n x y k j hj k]
  simp

theorem KNode.repoint_liveAt_keep (n : KNode) (x y : NodeId) (k j : Nat) (t : Time)
    (hj : n.linkIndex x k = some j) (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t) (c : Nat) (z : NodeId)
    (hz : (c, z) ∈ n.liveAt t) (hck : c ≠ k) : (c, z) ∈ (n.repoint j y).liveAt t := by
  rw [KNode.liveAt_of_times _ t (KNode.repoint_times n j y t ht)]
  rw [KNode.liveAt_of_times n t ht] at hz
  apply mem_of_lookup_nodup
  rw [KNode.repoint_live_lookup n x y k j hj c]
  have hb : (k == c) = false := by simpa using Ne.symm hck
  rw [hb]
  simpa using lookup_of_mem_nodup _ (KNode.live_keys_nodup _) c z hz

theorem KNode.add_liveAt_new (n : KNode) (k : Nat) (y : NodeId) (t : Time)
    (hw : klongsWf n.ks = true) (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t) :
    (k, y) ∈ (n.add t (.key k y)).liveAt t := by
  rw [KNode.liveAt_of_times _ t (KNode.add_times n t (.key k y) (fun s h => by cases h) ht)]
  apply mem_of_lookup_nodup
  rw [KNode.add_key_live_lookup_of_wf n t k k y hw]
  simp

theorem KNode.add_liveAt_keep (n : KNode) (k : Nat) (y : NodeId) (t : Time)
    (hw : klongsWf n.ks = true) (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t) (c : Nat) (z : NodeId)
    (hz : (c, z) ∈ n.liveAt t) (hck : c ≠ k) : (c, z) ∈ (n.add t (.key k y)).liveAt t := by
  rw [KNode.liveAt_of_times _ t (KNode.add_times n t (.key k y) (fun s h => by cases h) ht)]
  rw [KNode.liveAt_of_times n t ht] at hz
  apply mem_of_lookup_nodup
  rw [KNode.add_key_live_lookup_of_wf n t k c y hw]
  have hb : (k == c) = false := by simpa using Ne.symm hck
  rw [hb]
  simpa using lookup_of_mem_nodup _ (KNode.live_keys_nodup _) c z hz

/-! ## The steps at a segment root -/

/-- `takeBackRoot` at a segment root x that the transaction made, below the
segment leaf `leaf` of the path, keeps `TakeJ` (cost's
`writerWP_takeBackRoot_seg_coll`). -/
theorem writerWP_takeBackRoot_seg_take (x : NodeId) (d only : Nat) (n : KNode) (leaf : NodeId)
    (ln : KNode) (k : Nat) (c : Ctx) (base : View BVal) (w0 v : W) (hI : CollGetInv c base w0 v)
    (B : NodeId) (hJ : TakeJ c base B v)
    (hlf : TReach (wNode c.p base v) c.i v.top.rootKey leaf)
    (hlkL : v.nodes.lookup leaf = some ln) (hlnl : ln.leaf = true) (hk : (k, x) ∈ ln.liveAt c.i)
    (hlkx : v.nodes.lookup x = some n) (honly : n.onlyLiveKlong = some only)
    (hcv : n.cv? only = some 0) (hxl : n.leaf = false) (hmade : n.firstTime = some c.i)
    (hpd : (v.path[d]?).map (·.2) = some leaf) (hpk : v.path[d + 1]? = some (some k, x)) :
    WriterWP (takeBackRoot x (d + 1) only) c v (fun _ v' => TakeJ c base B v') := by
  have hLt : v.taken.contains leaf = false := hI.1.2.1 leaf hlf
  have hwL : wNode c.p base v leaf = some ln := by
    simp only [wNode, hLt, Bool.false_eq_true, ↓reduceIte, hlkL]
  have hxR : TReach (wNode c.p base v) c.i v.top.rootKey x := TReach.link hlf ⟨ln, hwL, hk⟩
  have hxt : v.taken.contains x = false := hI.1.2.1 x hxR
  have hwx : wNode c.p base v x = some n := by
    simp only [wNode, hxt, Bool.false_eq_true, ↓reduceIte, hlkx]
  have hlnt := hI.1.2.2.1 leaf ln hlf hwL
  have hlnwf := hI.2.2.2.1 leaf ln hlf hwL
  have hnt := hI.1.2.2.1 x n hxR hwx
  have hT := hI.1.1
  have hlx : leaf ≠ x := fun h => hT.no_self_link leaf k hlf ⟨ln, hwL, by rw [h]; exact hk⟩
  have hwfS : ∀ u un, ReachS (wNode c.p base v) c.i v.top.rootKey u → wNode c.p base v u = some un →
      klongsWf un.ks = true := fun u un hu hun => hI.2.2.2.1 u un (reachS_tReach _ _ _ _ hu) hun
  unfold takeBackRoot
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c v hlkx]
  cases hp : n.ptr? only with
  | none => exact writerWP_throw _ _ _ _
  | some child =>
    obtain ⟨c0, hk0, hlv⟩ := onlyLiveKlong_live_iff n only child honly hp
    have hc0 : c0 = 0 := by
      have h1 : n.cv? only = some c0 := by simp [KNode.cv?, hk0]
      rw [h1] at hcv; simpa using hcv
    subst hc0
    have hcl : (0, child) ∈ n.liveAt c.i := by
      rw [KNode.liveAt_of_times n c.i hnt]; exact (hlv 0 child).mpr ⟨rfl, rfl⟩
    have hchR : TReach (wNode c.p base v) c.i v.top.rootKey child := TReach.link hxR ⟨n, hwx, hcl⟩
    obtain ⟨m, hm⟩ := hI.1.2.2.2 x n 0 child hxR hwx hxl hcl
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
        have hLt' : (x :: v.taken).contains leaf = false := by
          rw [List.contains_cons]
          have : (leaf == x) = false := by simpa using hlx
          rw [this, Bool.false_or]; exact hLt
        have hyt : ∀ y, y ≠ x → (x :: v.taken).contains y = v.taken.contains y := by
          intro y hyx
          rw [List.contains_cons]
          have : (y == x) = false := by simpa using hyx
          simp [this]
        have hfin : ∀ w' : W, w'.vals = v.vals → w'.taken = x :: v.taken →
            w'.nodes = upsert v.nodes leaf (ln.repoint j child) → w'.top = v.top →
            TakeJ c base B w' := by
          intro w' h'v h't h'n h'top
          have hL' : wNode c.p base w' leaf = some (ln.repoint j child) := by
            simp only [wNode, h't, hLt', Bool.false_eq_true, ↓reduceIte, h'n, lookup_upsert]
          have hoth : ∀ y, y ≠ leaf → y ≠ x → wNode c.p base w' y = wNode c.p base v y := by
            intro y hyl hyx
            simp only [wNode, h't, hyt y hyx, h'n, lookup_upsert, hyl, ↓reduceIte]
          have hX : wNode c.p base w' x = none := by simp [wNode, h't]
          have hjk := kd_linkIndex_some ln x k j hj
          have hBx : B ≤ x := ge_of_firstTime _ _ _ hJ.2.2 x n hwx hmade
          have hlen : (prefixAt ln.ks (c.i - 1)).length ≤ j := by
            rcases Nat.lt_or_ge j (prefixAt ln.ks (c.i - 1)).length with hlt | hge
            · have := hJ.2.1 leaf ln hwL k x (mem_prefixAt_of_lt ln.ks _ j _ hlt hjk)
              omega
            · exact hge
          have hpre : prefixAt (ln.repoint j child).ks (c.i - 1) = prefixAt ln.ks (c.i - 1) := by
            unfold KNode.repoint
            rw [hjk]
            exact prefixAt_set_late ln.ks (c.i - 1) j k child hlen
              (fun k0 h0 => by rw [hjk] at h0; cases h0; exact ⟨k, x, rfl⟩)
          refine ⟨?_, ?_, ?_⟩
          · rw [h'top]
            exact liveReachedN_segCollapse (wNode c.p base v) (wNode c.p base w') c.i v.top.rootKey leaf
              x child B ln (ln.repoint j child) n k hT hlf hwL hk hwx
              (fun c' z hz => by
                rw [KNode.liveAt_of_times n c.i hnt] at hz
                exact ((hlv c' z).mp hz).2)
              hL' (KNode.repoint_liveAt_new ln x child k j c.i hj hlnt)
              (fun c' z hz hck => KNode.repoint_liveAt_keep ln x child k j c.i hj hlnt c' z hz hck)
              hoth hJ.1 (fun xn2 h => by rw [hX] at h; cases h)
          · intro z zn hz cv y hky
            by_cases hzl : z = leaf
            · rw [hzl, hL'] at hz
              cases hz
              rw [hpre] at hky
              exact hJ.2.1 leaf ln hwL cv y hky
            · by_cases hzx : z = x
              · rw [hzx, hX] at hz; cases hz
              · rw [hoth z hzl hzx] at hz
                exact hJ.2.1 z zn hz cv y hky
          · intro z zn hz hzB
            by_cases hzl : z = leaf
            · rw [hzl, hL'] at hz
              cases hz
              rw [KNode.firstTime_repoint]
              exact hJ.2.2 leaf ln hwL (by rw [← hzl]; exact hzB)
            · by_cases hzx : z = x
              · rw [hzx, hX] at hz; cases hz
              · rw [hoth z hzl hzx] at hz
                exact hJ.2.2 z zn hz hzB
        exact hfin _ rfl rfl rfl rfl
    · exact writerWP_throw _ _ _ _

/-- `replaceRoot` at a segment root x below the segment leaf `leaf` of the
path, the leaf with room for the klong to x's child, keeps `TakeJ` (cost's
`writerWP_replaceRoot_seg_coll`). -/
theorem writerWP_replaceRoot_seg_take (x : NodeId) (d only : Nat) (n : KNode) (leaf : NodeId)
    (ln : KNode) (k : Nat) (c : Ctx) (base : View BVal) (w0 v : W) (hI : CollGetInv c base w0 v)
    (B : NodeId) (hpos : 0 < c.i) (hJ : TakeJ c base B v)
    (hlf : TReach (wNode c.p base v) c.i v.top.rootKey leaf)
    (hlkL : v.nodes.lookup leaf = some ln) (hlnl : ln.leaf = true) (hk : (k, x) ∈ ln.liveAt c.i)
    (hlkx : v.nodes.lookup x = some n) (honly : n.onlyLiveKlong = some only)
    (hcv : n.cv? only = some 0) (hxl : n.leaf = false)
    (hpd : (v.path[d]?).map (·.2) = some leaf) (hpk : v.path[d + 1]? = some (some k, x))
    (hroom : ln.size + 1 + 1 ≤ c.p.M)
    (hdead : ∀ y, deadOver c.p (ln.add c.i (.key k y)) = false) :
    WriterWP (replaceRoot x (d + 1) only) c v (fun _ v' => TakeJ c base B v') := by
  have hLt : v.taken.contains leaf = false := hI.1.2.1 leaf hlf
  have hwL : wNode c.p base v leaf = some ln := by
    simp only [wNode, hLt, Bool.false_eq_true, ↓reduceIte, hlkL]
  have hxR : TReach (wNode c.p base v) c.i v.top.rootKey x := TReach.link hlf ⟨ln, hwL, hk⟩
  have hxt : v.taken.contains x = false := hI.1.2.1 x hxR
  have hwx : wNode c.p base v x = some n := by
    simp only [wNode, hxt, Bool.false_eq_true, ↓reduceIte, hlkx]
  have hlnt := hI.1.2.2.1 leaf ln hlf hwL
  have hlnwf := hI.2.2.2.1 leaf ln hlf hwL
  have hnt := hI.1.2.2.1 x n hxR hwx
  have hT := hI.1.1
  have hlx : leaf ≠ x := fun h => hT.no_self_link leaf k hlf ⟨ln, hwL, by rw [h]; exact hk⟩
  have hwfS : ∀ u un, ReachS (wNode c.p base v) c.i v.top.rootKey u → wNode c.p base v u = some un →
      klongsWf un.ks = true := fun u un hu hun => hI.2.2.2.1 u un (reachS_tReach _ _ _ _ hu) hun
  unfold replaceRoot
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c v hlkx]
  cases hp : n.ptr? only with
  | none => exact writerWP_throw _ _ _ _
  | some child =>
    obtain ⟨c0, hk0, hlv⟩ := onlyLiveKlong_live_iff n only child honly hp
    have hc0 : c0 = 0 := by
      have h1 : n.cv? only = some c0 := by simp [KNode.cv?, hk0]
      rw [h1] at hcv; simpa using hcv
    subst hc0
    have hcl : (0, child) ∈ n.liveAt c.i := by
      rw [KNode.liveAt_of_times n c.i hnt]; exact (hlv 0 child).mpr ⟨rfl, rfl⟩
    have hchR : TReach (wNode c.p base v) c.i v.top.rootKey child := TReach.link hxR ⟨n, hwx, hcl⟩
    obtain ⟨m, hm⟩ := hI.1.2.2.2 x n 0 child hxR hwx hxl hcl
    simp only [note, writerWP_bind, writerWP_modify]
    refine writerWP_pathNode_known d leaf c _ (by exact hpd) _ ?_
    refine writerWP_klongAt_known (d + 1) k x c _ (by exact hpk) _ ?_
    refine writerWP_mono (writerWP_unlink_fate x n c _ (by simpa using hlkx)) ?_
    intro _ w1 ⟨h1t, h1top, h1v, h1x, h1l⟩
    have hlk1 : w1.nodes.lookup leaf = some ln := by rw [h1l leaf hlx]; exact hlkL
    refine writerWP_mono (writerWP_appendKlongs_room d leaf ln k child c w1 hlk1 hroom (hdead _)) ?_
    intro _ w2 h2
    subst h2
    have hL' : wNode c.p base { w1 with nodes := upsert w1.nodes leaf (ln.add c.i (.key k child)) } leaf =
        some (ln.add c.i (.key k child)) := by
      simp only [wNode, h1t, hLt, Bool.false_eq_true, ↓reduceIte, lookup_upsert]
    have hoth : ∀ y, y ≠ leaf → y ≠ x →
        wNode c.p base { w1 with nodes := upsert w1.nodes leaf (ln.add c.i (.key k child)) } y =
          wNode c.p base v y := by
      intro y hyl hyx
      simp only [wNode, h1t, lookup_upsert, hyl, ↓reduceIte, h1l y hyx]
    have hX : wNode c.p base { w1 with nodes := upsert w1.nodes leaf (ln.add c.i (.key k child)) } x =
        some (if n.lastTime == some c.i then n.toPrev (c.i - 1) else n) := by
      simp only [wNode, h1t, hxt, Bool.false_eq_true, ↓reduceIte, lookup_upsert, Ne.symm hlx, h1x]
    have hnwf := hI.2.2.2.1 x n hxR hwx
    refine ⟨?_, ?_, ?_⟩
    · show LiveReachedN _ c.i w1.top.rootKey B
      rw [show w1.top.rootKey = v.top.rootKey by rw [h1top]]
      exact liveReachedN_segCollapse (wNode c.p base v) _ c.i v.top.rootKey leaf
        x child B ln (ln.add c.i (.key k child)) n k hT hlf hwL hk hwx
        (fun c' z hz => by
          rw [KNode.liveAt_of_times n c.i hnt] at hz
          exact ((hlv c' z).mp hz).2)
        hL' (KNode.add_liveAt_new ln k child c.i hlnwf hlnt)
        (fun c' z hz hck => KNode.add_liveAt_keep ln k child c.i hlnwf hlnt c' z hz hck)
        hoth hJ.1 (fun xn2 h => by
          rw [hX] at h
          cases h
          exact unlinked_live_below n c.i B hpos (hJ.2.1 x n hwx) hnwf hnt)
    · intro z zn hz cv y hky
      by_cases hzl : z = leaf
      · rw [hzl, hL'] at hz
        cases hz
        rw [KNode.prefixAt_add ln c.i _ hpos] at hky
        exact hJ.2.1 leaf ln hwL cv y hky
      · by_cases hzx : z = x
        · rw [hzx, hX] at hz
          cases hz
          apply hJ.2.1 x n hwx cv y
          split at hky
          · simpa [KNode.toPrev, prefixAt_idem] using hky
          · exact hky
        · rw [hoth z hzl hzx] at hz
          exact hJ.2.1 z zn hz cv y hky
    · intro z zn hz hzB
      by_cases hzl : z = leaf
      · rw [hzl, hL'] at hz
        cases hz
        obtain ⟨s, hs, hf⟩ := hJ.2.2 leaf ln hwL (by rw [← hzl]; exact hzB)
        exact ⟨s, hs, KNode.firstTime_add_some ln c.i _ s hf⟩
      · by_cases hzx : z = x
        · rw [hzx, hX] at hz
          cases hz
          obtain ⟨s, hs, hf⟩ := hJ.2.2 x n hwx (by rw [← hzx]; exact hzB)
          refine ⟨s, hs, ?_⟩
          split
          · exact KNode.firstTime_toPrev n (c.i - 1) s hf (by omega)
          · exact hf
        · rw [hoth z hzl hzx] at hz
          exact hJ.2.2 z zn hz hzB


/-! ## The steps at the space root, and the loop -/

theorem writerWP_replaceRoot_spaceT (x : NodeId) (only : Nat) (n : KNode) (child : NodeId) (c : Ctx)
    (w : W) (hlk : w.nodes.lookup x = some n) (hptr : n.ptr? only = some child) :
    WriterWP (replaceRoot x 0 only) c w (fun _ w' => w'.top.rootKey = child ∧ w'.taken = w.taken ∧
      w'.vals = w.vals ∧
      w'.nodes.lookup x = some (if n.lastTime == some c.i then n.toPrev (c.i - 1) else n) ∧
      ∀ y, y ≠ x → w'.nodes.lookup y = w.nodes.lookup y) := by
  unfold replaceRoot
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c w hlk]
  rw [hptr]
  simp only [note, writerWP_bind, writerWP_modify]
  refine writerWP_mono (writerWP_unlink_fate x n c _ (by simpa using hlk)) ?_
  intro _ w1 ⟨h1t, _, h1v, h1x, h1l⟩
  refine writerWP_mono (writerWP_newSuperRoot_frameV child c w1) ?_
  intro _ w2 ⟨h2r, h2t, h2n, h2v⟩
  exact ⟨h2r, by rw [h2t, h1t], by rw [h2v, h1v], by rw [h2n, h1x],
    fun y hy => by rw [h2n, h1l y hy]⟩

/-- The collapse steps at the space root keep `TakeJ`. -/
theorem writerWP_rootStep_space_take (x : NodeId) (only : Nat) (n : KNode) (c : Ctx)
    (base : View BVal) (w0 v : W) (hI : CollGetInv c base w0 v) (B : NodeId) (hpos : 0 < c.i)
    (hJ : TakeJ c base B v) (hx : x = v.top.rootKey)
    (hlkx : v.nodes.lookup x = some n) (honly : n.onlyLiveKlong = some only)
    (hcv : n.cv? only = some 0) (hxl : n.leaf = false) :
    WriterWP (takeBackRoot x 0 only) c v (fun _ v' => TakeJ c base B v') ∧
    WriterWP (replaceRoot x 0 only) c v (fun _ v' => TakeJ c base B v') := by
  have hxt : v.taken.contains x = false := by rw [hx]; exact hI.1.2.1 _ TReach.root
  have hwx : wNode c.p base v x = some n := by
    simp only [wNode, hxt, Bool.false_eq_true, ↓reduceIte, hlkx]
  have hroot : wNode c.p base v v.top.rootKey = some n := by rw [← hx]; exact hwx
  have hnt := hI.1.2.2.1 _ n TReach.root hroot
  have hnwf := hI.2.2.2.1 _ n TReach.root hroot
  -- the facts after a step, from the root's node after it
  have hfin : ∀ child, n.ptr? only = some child → ∀ w3 : W, w3.top.rootKey = child →
      (∀ z, z ≠ x → wNode c.p base w3 z = wNode c.p base v z) →
      (∀ xn2, wNode c.p base w3 x = some xn2 → (∀ c' z, (c', z) ∈ xn2.liveAt c.i → z < B) ∧
        (∀ cv y, Klong.key cv y ∈ prefixAt xn2.ks (c.i - 1) → y < B) ∧
        (x < B → ∃ s, s < c.i ∧ xn2.firstTime = some s)) →
      TakeJ c base B w3 := by
    intro child hptr w3 h3top hN2 hx2
    obtain ⟨c0, _, hlv⟩ := onlyLiveKlong_live_iff n only child honly hptr
    refine ⟨?_, ?_, ?_⟩
    · rw [h3top]
      refine liveReachedN_spaceCollapse (wNode c.p base v) (wNode c.p base w3) c.i v.top.rootKey child
        B n hroot ?_ (fun z hz => hN2 z (by rw [hx]; exact hz)) hJ.1
        (fun xn2 h => (hx2 xn2 (by rw [hx]; exact h)).1)
      intro c' z hz
      rw [KNode.liveAt_of_times n c.i hnt] at hz
      exact ((hlv c' z).mp hz).2
    · intro z zn hz cv y hky
      by_cases hzx : z = x
      · rw [hzx] at hz
        exact (hx2 zn hz).2.1 cv y hky
      · rw [hN2 z hzx] at hz
        exact hJ.2.1 z zn hz cv y hky
    · intro z zn hz hzB
      by_cases hzx : z = x
      · rw [hzx] at hz hzB
        exact (hx2 zn hz).2.2 hzB
      · rw [hN2 z hzx] at hz
        exact hJ.2.2 z zn hz hzB
  constructor
  · cases hp : n.ptr? only with
    | none =>
      unfold takeBackRoot
      simp only [writerWP_bind, writerWP_read]
      rw [writerWP_getNode_known _ n c v hlkx, hp]
      exact writerWP_throw _ _ _ _
    | some child =>
      refine writerWP_mono (writerWP_takeBackRoot_spaceV _ only n child c v hlkx hp) ?_
      intro _ w3 ⟨h3top, h3t, h3n, _⟩
      have hX : wNode c.p base w3 x = none := by simp [wNode, h3t]
      refine hfin child hp w3 h3top (fun z hz => ?_) (fun xn2 h => by rw [hX] at h; cases h)
      have : w3.taken.contains z = v.taken.contains z := by
        rw [h3t, List.contains_cons]
        have : (z == x) = false := by simpa using hz
        simp [this]
      simp only [wNode, this, h3n]
  · cases hp : n.ptr? only with
    | none =>
      unfold replaceRoot
      simp only [writerWP_bind, writerWP_read]
      rw [writerWP_getNode_known _ n c v hlkx, hp]
      exact writerWP_throw _ _ _ _
    | some child =>
      refine writerWP_mono (writerWP_replaceRoot_spaceT _ only n child c v hlkx hp) ?_
      intro _ w3 ⟨h3top, h3t, _, h3x, h3l⟩
      have hX : wNode c.p base w3 x = some (if n.lastTime == some c.i then n.toPrev (c.i - 1) else n) := by
        simp only [wNode, h3t, hxt, Bool.false_eq_true, ↓reduceIte, h3x]
      refine hfin child hp w3 h3top (fun z hz => by simp only [wNode, h3t, h3l z hz]) ?_
      intro xn2 h
      rw [hX] at h
      cases h
      refine ⟨unlinked_live_below n c.i B hpos (hJ.2.1 x n hwx) hnwf hnt, ?_, ?_⟩
      · intro cv y hky
        apply hJ.2.1 x n hwx cv y
        split at hky
        · simpa [KNode.toPrev, prefixAt_idem] using hky
        · exact hky
      · intro hxB
        obtain ⟨s, hs, hf⟩ := hJ.2.2 x n hwx hxB
        refine ⟨s, hs, ?_⟩
        split
        · exact KNode.firstTime_toPrev n (c.i - 1) s hf (by omega)
        · exact hf

/-- Root collapse at any segment keeps `CollGetInv` and `TakeJ`, given room in
the segment leaf above each segment root that is replaced (cost's
`writerWP_collapseRoot_coll` with J = `TakeJ`). -/
theorem writerWP_collapseRoot_take (key : Key) (seg : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (w0 : W) (B : NodeId) (hpos : 0 < c.i)
    (hroom : ∀ v x n leaf ln k, CollGetInv c base w0 v → TakeJ c base B v → SegDesc c base x v →
      v.nodes.lookup x = some n → n.leaf = false → n.firstTime ≠ some c.i →
      TReach (wNode c.p base v) c.i v.top.rootKey leaf → v.nodes.lookup leaf = some ln →
      ln.leaf = true → (k, x) ∈ ln.liveAt c.i →
      ln.size + 1 + 1 ≤ c.p.M ∧ ∀ y, deadOver c.p (ln.add c.i (.key k y)) = false) :
    ∀ fuel v, CollGetInv c base w0 v → TakeJ c base B v →
      WriterWP (collapseRoot key seg fuel) c v (fun _ v' => CollGetInv c base w0 v' ∧
        TakeJ c base B v') := by
  refine writerWP_collapseRoot_coll key seg c base hvc w0 (TakeJ c base B)
    (fun v v' hJ hr => takeJ_of_readsAs c base B v v' hJ hr) hroom ?_ ?_
  · intro v x n only hI hJ hP hlk hxl hm honly hcv
    obtain ⟨_, ps, hvp, hlf, hend, hcache, hlast⟩ := hP
    rcases hlast with hps | ⟨ps0, k, L, ln, hps, hL, hLn, hLl⟩
    · subst hps
      have hx : x = v.top.rootKey := by rw [← hend]; rfl
      rw [hvp]
      exact (writerWP_rootStep_space_take x only n c base w0 v hI B hpos hJ hx hlk honly hcv hxl).1
    · subst hps
      obtain ⟨hLr, hLlk, hk, hlen, hpd, hpk⟩ := segDesc_seg c base x v ps0 k L ln hvp hlf hcache hL hLn
      rw [hlen]
      exact writerWP_takeBackRoot_seg_take x ps0.length only n L ln k c base w0 v hI B hJ hLr hLlk hLl
        hk hlk honly hcv hxl hm hpd hpk
  · intro v x n only hI hJ hP hlk hxl hm honly hcv
    have hP0 := hP
    obtain ⟨_, ps, hvp, hlf, hend, hcache, hlast⟩ := hP
    rcases hlast with hps | ⟨ps0, k, L, ln, hps, hL, hLn, hLl⟩
    · subst hps
      have hx : x = v.top.rootKey := by rw [← hend]; rfl
      rw [hvp]
      exact (writerWP_rootStep_space_take x only n c base w0 v hI B hpos hJ hx hlk honly hcv hxl).2
    · subst hps
      obtain ⟨hLr, hLlk, hk, hlen, hpd, hpk⟩ := segDesc_seg c base x v ps0 k L ln hvp hlf hcache hL hLn
      obtain ⟨hroom1, hdead⟩ := hroom v x n L ln k hI hJ hP0 hlk hxl hm hLr hLlk hLl hk
      rw [hlen]
      exact writerWP_replaceRoot_seg_take x ps0.length only n L ln k c base w0 v hI B hpos hJ hLr hLlk
        hLl hk hlk honly hcv hxl hpd hpk hroom1 hdead

end SIS.Tree
