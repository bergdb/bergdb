/-
Root collapse's step with the live counts (bergdb 030-01, step 4): a step at a
segment root x, the only hole, inner with one live klong, the empty key's, ends
with the live counts (`CollapseStepLiveOK`), but where x is a segment root that
existed before the transaction and its segment leaf is full (`replaceRoot`'s
cascade at the leaf; `CollapseSegFullLiveOK`, an obligation here). At the
space root (`liveEdges_collapseSpace`) and below a segment leaf with room or in
place (`liveEdges_collapseSeg`) the node maps are LiveCollapse.lean's.
-/
import SIS.Tree.LiveCollapse

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

set_option maxHeartbeats 4000000 in
/-- `takeBackRoot` at a segment root x that is the only hole, below the segment
leaf `leaf`: the leaf's klong names x's child in place, x is taken back, and the
live counts hold. -/
theorem writerWP_takeBackRoot_segL (x : NodeId) (d only : Nat) (n : KNode) (leaf : NodeId)
    (ln : KNode) (k : Nat) (c : Ctx) (base : View BVal) (v : W) (Hl : NodeId → Prop)
    (hm : c.p.merges = true) (hmb : 2 ≤ c.p.mergeBelow)
    (hT : TreeOK (wNode c.p base v) c.i v.top.rootKey)
    (hX : LiveEdgesH c.p (wNode c.p base v) c.i v.top.rootKey Hl) (hHl : ∀ y, Hl y → y = x)
    (hlf : TReach (wNode c.p base v) c.i v.top.rootKey leaf) (hLt : v.taken.contains leaf = false)
    (hlkL : v.nodes.lookup leaf = some ln) (hlnl : ln.leaf = true) (hk : (k, x) ∈ ln.liveAt c.i)
    (hlnt : ∀ s, Klong.time s ∈ ln.ks → s ≤ c.i)
    (hlkx : v.nodes.lookup x = some n) (hxt : v.taken.contains x = false)
    (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ c.i) (honly : n.onlyLiveKlong = some only)
    (hxl : n.leaf = false)
    (hpd : (v.path[d]?).map (·.2) = some leaf) (hpk : v.path[d + 1]? = some (some k, x)) :
    WriterWP (takeBackRoot x (d + 1) only) c v
      (fun _ v' => LiveEdges c.p (wNode c.p base v') c.i v'.top.rootKey) := by
  have hwL : wNode c.p base v leaf = some ln := by
    simp only [wNode, hLt, Bool.false_eq_true, ↓reduceIte, hlkL]
  have hwx : wNode c.p base v x = some n := by
    simp only [wNode, hxt, Bool.false_eq_true, ↓reduceIte, hlkx]
  have hlx : leaf ≠ x := fun h => hT.no_self_link leaf k hlf ⟨ln, hwL, by rw [h]; exact hk⟩
  unfold takeBackRoot
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c v hlkx]
  cases hp : n.ptr? only with
  | none => exact writerWP_throw _ _ _ _
  | some child =>
    obtain ⟨c0, _, hlv⟩ := onlyLiveKlong_live_iff n only child honly hp
    have hcl : (c0, child) ∈ n.liveAt c.i := by
      rw [KNode.liveAt_of_times n c.i hnt]; exact (hlv c0 child).mpr ⟨rfl, rfl⟩
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
        have hfin : ∀ w' : W, w'.taken = x :: v.taken →
            w'.nodes = upsert v.nodes leaf (ln.repoint j child) → w'.top = v.top →
            LiveEdges c.p (wNode c.p base w') c.i w'.top.rootKey := by
          intro w' h't h'n h'top
          have hL' : wNode c.p base w' leaf = some (ln.repoint j child) := by
            simp only [wNode, h't, hLt', Bool.false_eq_true, ↓reduceIte, h'n, lookup_upsert]
          have hoth : ∀ y, y ≠ leaf → y ≠ x → wNode c.p base w' y = wNode c.p base v y := by
            intro y hyl hyx
            simp only [wNode, h't, hyt y hyx, h'n, lookup_upsert, hyl, ↓reduceIte]
          have hlinks : ∀ c' z, (c', z) ∈ (ln.repoint j child).liveAt c.i →
              (c' = k ∧ z = child) ∨ ((c', z) ∈ ln.liveAt c.i ∧ c' ≠ k) := by
            intro c' z hmm
            rw [KNode.liveAt_of_times _ c.i (KNode.repoint_times ln j child c.i hlnt)] at hmm
            have hlk := lookup_of_mem_nodup _ (KNode.live_keys_nodup _) c' z hmm
            rw [KNode.repoint_live_lookup ln x child k j hj c'] at hlk
            by_cases hck : k = c'
            · subst hck; simp at hlk; exact Or.inl ⟨rfl, hlk.symm⟩
            · have hb : (k == c') = false := by simpa using hck
              rw [hb] at hlk
              simp only [Bool.false_eq_true, ↓reduceIte] at hlk
              refine Or.inr ⟨?_, Ne.symm hck⟩
              rw [KNode.liveAt_of_times ln c.i hlnt]
              exact bk_mem_of_lookup _ c' z hlk
          rw [h'top]
          exact liveEdges_collapseSeg c.p (wNode c.p base v) (wNode c.p base w') c.i v.top.rootKey leaf x
            child ln (ln.repoint j child) n k c0 Hl hT hX hHl hlf hwL hlnl hk hwx hxl hcl hm hmb hL'
            (bk_repoint_leaf ln j child) hlinks (repoint_liveAt_length ln x child k j c.i hj hlnt) hoth
        exact hfin _ rfl rfl rfl
    · exact writerWP_throw _ _ _ _

set_option maxHeartbeats 4000000 in
/-- `replaceRoot` at a segment root x that is the only hole, below the segment
leaf `leaf` with room for x's child's klong: x is unlinked, the leaf gets a
klong of k naming x's child, and the live counts hold. -/
theorem writerWP_replaceRoot_segL_room (x : NodeId) (d only : Nat) (n : KNode) (leaf : NodeId)
    (ln : KNode) (k : Nat) (c : Ctx) (base : View BVal) (v : W) (Hl : NodeId → Prop)
    (hm : c.p.merges = true) (hmb : 2 ≤ c.p.mergeBelow)
    (hT : TreeOK (wNode c.p base v) c.i v.top.rootKey)
    (hX : LiveEdgesH c.p (wNode c.p base v) c.i v.top.rootKey Hl) (hHl : ∀ y, Hl y → y = x)
    (hlf : TReach (wNode c.p base v) c.i v.top.rootKey leaf) (hLt : v.taken.contains leaf = false)
    (hlkL : v.nodes.lookup leaf = some ln) (hlnl : ln.leaf = true) (hk : (k, x) ∈ ln.liveAt c.i)
    (hlnt : ∀ s, Klong.time s ∈ ln.ks → s ≤ c.i) (hlnwf : klongsWf ln.ks = true)
    (hlkx : v.nodes.lookup x = some n) (hxt : v.taken.contains x = false)
    (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ c.i) (honly : n.onlyLiveKlong = some only)
    (hxl : n.leaf = false)
    (hpd : (v.path[d]?).map (·.2) = some leaf) (hpk : v.path[d + 1]? = some (some k, x))
    (hroom : ln.size + 2 ≤ c.p.M) (hdead : ∀ y, deadOver c.p (ln.add c.i (.key k y)) = false) :
    WriterWP (replaceRoot x (d + 1) only) c v
      (fun _ v' => LiveEdges c.p (wNode c.p base v') c.i v'.top.rootKey) := by
  have hwL : wNode c.p base v leaf = some ln := by
    simp only [wNode, hLt, Bool.false_eq_true, ↓reduceIte, hlkL]
  have hwx : wNode c.p base v x = some n := by
    simp only [wNode, hxt, Bool.false_eq_true, ↓reduceIte, hlkx]
  have hlx : leaf ≠ x := fun h => hT.no_self_link leaf k hlf ⟨ln, hwL, by rw [h]; exact hk⟩
  unfold replaceRoot
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c v hlkx]
  cases hp : n.ptr? only with
  | none => exact writerWP_throw _ _ _ _
  | some child =>
    obtain ⟨c0, _, hlv⟩ := onlyLiveKlong_live_iff n only child honly hp
    have hcl : (c0, child) ∈ n.liveAt c.i := by
      rw [KNode.liveAt_of_times n c.i hnt]; exact (hlv c0 child).mpr ⟨rfl, rfl⟩
    simp only [note, writerWP_bind, writerWP_modify]
    refine writerWP_pathNode_known d leaf c _ (by exact hpd) _ ?_
    refine writerWP_klongAt_known (d + 1) k x c _ (by exact hpk) _ ?_
    refine writerWP_mono (writerWP_unlink_seg x n c base _ (by simpa using hlkx) (by simpa using hxt)) ?_
    rintro _ w1 ⟨h1t, h1top, _, _, _, h1l, _⟩
    have hlk1 : w1.nodes.lookup leaf = some ln := by rw [h1l leaf hlx]; simpa using hlkL
    refine writerWP_mono (writerWP_appendKlongs_addKeys d leaf ln [(k, child)] c w1 hlk1
      (by simpa using hroom) (by simpa using hdead child)) ?_
    intro _ w' hw'
    have hfold : ([(k, child)].foldl (fun n (cv, y) => n.add c.i (.key cv y)) ln) =
        ln.add c.i (.key k child) := rfl
    have h'n : w'.nodes = upsert w1.nodes leaf (ln.add c.i (.key k child)) := by rw [hw', hfold]
    have h't : w'.taken = w1.taken := by rw [hw']
    have h'top : w'.top = w1.top := by rw [hw']
    have hL' : wNode c.p base w' leaf = some (ln.add c.i (.key k child)) := by
      have ht : w'.taken.contains leaf = false := by rw [h't, h1t]; exact hLt
      simp only [wNode, ht, Bool.false_eq_true, ↓reduceIte, h'n, lookup_upsert]
    have hoth : ∀ y, y ≠ leaf → y ≠ x → wNode c.p base w' y = wNode c.p base v y := by
      intro y hyl hyx
      simp only [wNode, h't, h1t, h'n, lookup_upsert, hyl, ↓reduceIte, h1l y hyx]
    have hat := KNode.add_times ln c.i (.key k child) (fun s h => by cases h) hlnt
    have hlinks : ∀ c' z, (c', z) ∈ (ln.add c.i (.key k child)).liveAt c.i →
        (c' = k ∧ z = child) ∨ ((c', z) ∈ ln.liveAt c.i ∧ c' ≠ k) := by
      intro c' z hmm
      rw [KNode.liveAt_of_times _ c.i hat] at hmm
      have hlk := lookup_of_mem_nodup _ (KNode.live_keys_nodup _) c' z hmm
      rw [KNode.add_key_live_lookup_of_wf ln c.i k c' child hlnwf] at hlk
      by_cases hck : k = c'
      · subst hck; simp at hlk; exact Or.inl ⟨rfl, hlk.symm⟩
      · have hb : (k == c') = false := by simpa using hck
        rw [hb] at hlk
        simp only [Bool.false_eq_true, ↓reduceIte] at hlk
        refine Or.inr ⟨?_, Ne.symm hck⟩
        rw [KNode.liveAt_of_times ln c.i hlnt]
        exact bk_mem_of_lookup _ c' z hlk
    rw [h'top, h1top]
    exact liveEdges_collapseSeg c.p (wNode c.p base v) _ c.i v.top.rootKey leaf x child ln
      (ln.add c.i (.key k child)) n k c0 Hl hT hX hHl hlf hwL hlnl hk hwx hxl hcl hm hmb hL'
      (addKeys_leaf c.i [(k, child)] ln) hlinks (addKeys_liveAt_length c.i [(k, child)] ln hlnwf hlnt)
      hoth

/-- A collapse step at the space root x, the only hole: x's child becomes the
space root, and the live counts hold. -/
theorem writerWP_rootStep_spaceL (x : NodeId) (only : Nat) (n : KNode) (c : Ctx) (base : View BVal)
    (v : W) (Hl : NodeId → Prop) (hm : c.p.merges = true) (hmb : 2 ≤ c.p.mergeBelow)
    (hT : TreeOK (wNode c.p base v) c.i v.top.rootKey)
    (hX : LiveEdgesH c.p (wNode c.p base v) c.i v.top.rootKey Hl) (hHl : ∀ y, Hl y → y = x)
    (hxr : x = v.top.rootKey) (hlkx : v.nodes.lookup x = some n) (hxt : v.taken.contains x = false)
    (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ c.i) (honly : n.onlyLiveKlong = some only)
    (hxl : n.leaf = false) :
    WriterWP (takeBackRoot x 0 only) c v
      (fun _ v' => LiveEdges c.p (wNode c.p base v') c.i v'.top.rootKey) ∧
    WriterWP (replaceRoot x 0 only) c v
      (fun _ v' => LiveEdges c.p (wNode c.p base v') c.i v'.top.rootKey) := by
  have hwx : wNode c.p base v v.top.rootKey = some n := by
    rw [← hxr]; simp only [wNode, hxt, Bool.false_eq_true, ↓reduceIte, hlkx]
  have hHl' : ∀ y, Hl y → y = v.top.rootKey := fun y hy => (hHl y hy).trans hxr
  cases hp : n.ptr? only with
  | none =>
    constructor
    · unfold takeBackRoot
      simp only [writerWP_bind, writerWP_read]
      rw [writerWP_getNode_known x n c v hlkx, hp]
      exact writerWP_throw _ _ _ _
    · unfold replaceRoot
      simp only [writerWP_bind, writerWP_read]
      rw [writerWP_getNode_known x n c v hlkx, hp]
      exact writerWP_throw _ _ _ _
  | some child =>
    obtain ⟨c0, _, hlv⟩ := onlyLiveKlong_live_iff n only child honly hp
    have hcl : (c0, child) ∈ n.liveAt c.i := by
      rw [KNode.liveAt_of_times n c.i hnt]; exact (hlv c0 child).mpr ⟨rfl, rfl⟩
    constructor
    · refine writerWP_mono (writerWP_takeBackRoot_spaceV x only n child c v hlkx hp) ?_
      rintro _ v' ⟨htop', ht', hn', _⟩
      rw [htop']
      refine liveEdges_collapseSpace c.p (wNode c.p base v) (wNode c.p base v') c.i v.top.rootKey child n
        c0 Hl hT hX hHl' hwx hxl hcl hm hmb (fun z hz => ?_)
      have hzx : z ≠ x := by rw [hxr]; exact hz
      have hc : (x :: v.taken).contains z = v.taken.contains z := by
        rw [List.contains_cons]
        have : (z == x) = false := by simpa using hzx
        simp [this]
      simp only [wNode, ht', hc, hn']
    · refine writerWP_mono (writerWP_replaceRoot_spaceV x only n child c v hlkx hp) ?_
      rintro _ v' ⟨htop', ht', _, hl'⟩
      rw [htop']
      refine liveEdges_collapseSpace c.p (wNode c.p base v) (wNode c.p base v') c.i v.top.rootKey child n
        c0 Hl hT hX hHl' hwx hxl hcl hm hmb (fun z hz => ?_)
      have hzx : z ≠ x := by rw [hxr]; exact hz
      simp only [wNode, ht', hl' z hzx]

/-- The collapse's step at a segment root that existed before the transaction,
below a segment leaf that has no room for one more klong or would compact:
`replaceRoot`'s cascade at the leaf (bergdb 030-01, step 4's rest; an
obligation here). -/
def CollapseSegFullLiveOK (c : Ctx) (base : View BVal) (B : NodeId) : Prop :=
  ∀ (x : NodeId) (v : W) (n : KNode) (only : Nat) (w0 : W) (F : Nat) (top0 : Top)
    (Hl : NodeId → Prop) (d : Nat) (leaf : NodeId) (ln : KNode) (k : Nat),
    CollGetInvF c base w0 v F → RangeOrder (wNode c.p base v) c.i v.top.rootKey →
    PutBook c B top0 v → SegDesc c base x v →
    LiveEdgesH c.p (wNode c.p base v) c.i v.top.rootKey Hl → (∀ y, Hl y → y = x) →
    v.nodes.lookup x = some n → n.leaf = false → n.onlyLiveKlong = some only →
    n.cv? only = some 0 → n.firstTime ≠ some c.i →
    (v.path[d]?).map (·.2) = some leaf → v.path[d + 1]? = some (some k, x) →
    v.path.length - 1 = d + 1 →
    v.nodes.lookup leaf = some ln → ln.leaf = true →
    ¬ (ln.size + 2 ≤ c.p.M ∧ ∀ y, deadOver c.p (ln.add c.i (.key k y)) = false) →
    WriterWP (replaceRoot x (d + 1) only) c v
      (fun _ v' => LiveEdges c.p (wNode c.p base v') c.i v'.top.rootKey)

set_option maxHeartbeats 4000000 in
/-- The collapse's step (bergdb 030-01, step 4): proved at the space root, for a
root the transaction made (taken back in place), and for a segment root whose
leaf has room; the rest is `CollapseSegFullLiveOK`. -/
theorem collapseStepLiveOK_of (c : Ctx) (base : View BVal) (B : NodeId) (hm : c.p.merges = true)
    (hMP : MergeParamsOK c.p) (hF : CollapseSegFullLiveOK c base B) : CollapseStepLiveOK c base B := by
  intro x v n only w0 F top0 Hl hCI hR hpb hsd hX hHl hl hleaf honly hcv
  have hmb : 2 ≤ c.p.mergeBelow := hMP.1
  have hT := hCI.1.1
  have hU := hCI.1.2.1
  have htimes := hCI.1.2.2.1
  have hwf := hCI.2.2.2.1
  obtain ⟨hxR, ps, hvp, hlf, hend, hcache, hlast⟩ := id hsd
  have hxt : v.taken.contains x = false := hU x hxR
  have hwx : wNode c.p base v x = some n := by
    simp only [wNode, hxt, Bool.false_eq_true, ↓reduceIte, hl]
  have hnt := htimes x n hxR hwx
  rcases hlast with hps | ⟨ps0, k, L, ln, hps, hL, hLn, hLl⟩
  · have hxr : x = v.top.rootKey := by rw [← hend, hps]; rfl
    have hd0 : v.path.length - 1 = 0 := by rw [hvp, hps]; rfl
    rw [hd0]
    have hsp := writerWP_rootStep_spaceL x only n c base v Hl hm hmb hT hX hHl hxr hl hxt hnt honly hleaf
    exact ⟨fun _ _ => hsp.1, fun _ => hsp.2⟩
  · rw [hps] at hvp hlf hcache
    obtain ⟨hLR, hlkL, hk, hlen, hpd, hpk⟩ :=
      segDesc_seg c base x v ps0 k L ln hvp hlf hcache hL hLn
    have hLt : v.taken.contains L = false := hU L hLR
    have hlnt := htimes L ln hLR hLn
    have hlnwf := hwf L ln hLR hLn
    rw [hlen]
    refine ⟨fun _ _ => writerWP_takeBackRoot_segL x ps0.length only n L ln k c base v Hl hm hmb hT hX hHl
      hLR hLt hlkL hLl hk hlnt hl hxt hnt honly hleaf hpd hpk, fun hmade => ?_⟩
    by_cases hroom : ln.size + 2 ≤ c.p.M ∧ ∀ y, deadOver c.p (ln.add c.i (.key k y)) = false
    · exact writerWP_replaceRoot_segL_room x ps0.length only n L ln k c base v Hl hm hmb hT hX hHl hLR
        hLt hlkL hLl hk hlnt hlnwf hl hxt hnt honly hleaf hpd hpk hroom.1 hroom.2
    · exact hF x v n only w0 F top0 Hl ps0.length L ln k hCI hR hpb hsd hX hHl hl hleaf honly hcv hmade
        hpd hpk hlen hlkL hLl hroom

/-- `afterDelete` with the hole (bergdb 030-01, steps 3 and 4): from the call's
facts (`DelInvJAE`, `PutBook`, `HtInv`, `LiveHoleW key g 0`), every run ends with
the live counts, given the merges with a full or compacting parent
(`MergeLiveFullOK`), root collapse's step at a segment root whose leaf is full
(`CollapseSegFullLiveOK`) and R3 after the merges' loop. -/
theorem writerWP_afterDelete_liveRF (key : Key) (g : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (hm : c.p.merges = true) (hMP : MergeParamsOK c.p) (KO : KindOracle)
    (B : NodeId) (hv : ViewIdsBelow B c.view) (hk : ViewKinds KO B c)
    (hICEk : ICEFromKinds c base KO B) (hsa2 : 2 ≤ c.p.splitAbove) (hcap : 1 ≤ c.p.mergeMax)
    (hpos : 0 < c.i) {H : NodeId → Nat → Prop} (hvo : ViewHtOK H B c)
    (hkw : ViewKlongsWf c.p c.view) (top0 : Top) (hB : PutBase c base B)
    (hF : MergeLiveFullOK c base B H) (hCF : CollapseSegFullLiveOK c base B)
    (v : W) (hJ : DelInvJAE c base KO B B v) (hpb : PutBook c B top0 v) (hhi : HtInv H B c v)
    (hLH : LiveHoleW key g 0 c base v)
    (hR3 : WriterWP (mergeUp key g c.p.fuel 0 false) c v
      (fun merged v' => merged = true → R3At key g c v')) :
    WriterWP (afterDelete key g 0) c v
      (fun _ v' => LiveEdges c.p (wNode c.p base v') c.i v'.top.rootKey) :=
  writerWP_afterDelete_liveR key g c base hvc hm KO B hv hk hICEk hsa2 hcap hpos hvo hkw top0 hB
    (mergeLiveOK_of_full c base hvc hm hMP hvo hF) (collapseStepLiveOK_of c base B hm hMP hCF) v hJ hpb hhi
    hLH hR3

end SIS.Tree
