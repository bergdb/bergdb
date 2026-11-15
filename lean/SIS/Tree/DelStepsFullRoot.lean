/-
A delete into a full leaf that is the space root (bergdb 024-12, TP7 and TP10,
case (4)): the root's split with latest's `writerWP_handleFull_rootVReach` and
`writerWP_handleFull_rootShape`. The take-back's facts (`DelFullRootJ2OK`) and
the reading's (`DelFullRootStepOK`, the ranges by `writerWP_delRootSplit_range`).
-/
import SIS.Tree.DelStepsFullGet
import SIS.Tree.MergeRootShape

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The split's parent step at the space root throws. -/
def rootUp : NodeId → List (Nat × NodeId) → M Unit :=
  fun _ _ => throw "corrupt: a split's parent above depth 0"

theorem keepsState_rootUp [inv : WriterStateInvariant] (q : NodeId) (more : List (Nat × NodeId)) :
    KeepsState (rootUp q more) := fun c w _ => writerWP_throw _ c w _

set_option maxHeartbeats 3200000 in
/-- `handleFull` of the space root L with a last version that keeps the root's
children (or they are no nodes, `hkeep`) keeps `TakeJ2`, and B stays at most
the next id: on `writerWP_handleFull_rootVReach`'s premises, `last` a time klong
with key klongs of distinct compare values. -/
theorem writerWP_handleFull_root_j2 (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (B : NodeId) (hpos : 0 < c.i) (L : NodeId) (n last : KNode) (compact : Bool)
    (w : W) (hJ : TakeJ2 c base B w) (hBn : B ≤ w.next)
    (hvnx : ∀ y ∈ w.vals.map (·.1), y < w.next)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hlwf : klongsWf last.ks = true) (hlt : ∀ s, Klong.time s ∈ last.ks → s ≤ c.i)
    (hlastV : (⟨n.leaf, last.ks⟩ : KNode).lastVersion c.i = last)
    (hlen2 : c.p.splitAbove < last.size → 2 ≤ (⟨n.leaf, last.ks⟩ : KNode).live.length)
    (hpairs : ∃ pairs, last.ks = newKlongs c.i pairs ∧ (pairs.map Prod.fst).Nodup)
    (hlk : w.nodes.lookup L = some n) (htk : w.taken.contains L = false)
    (hrk : w.top.rootKey = L)
    (hS5 : ∀ z, w.next ≤ z → w.nodes.lookup z = none ∧ w.taken.contains z = false ∧
      knodeOf c.p base z = none)
    (hS6 : ∀ u c' z, TLink (wNode c.p base w) c.i u c' z → z < w.next)
    (hW : ∀ z zn, wNode c.p base w z = some zn → klongsWf zn.ks = true)
    (hV : TreeOK (updN (wNode c.p base w) L ⟨n.leaf, last.ks⟩) c.i w.top.rootKey)
    (hvx : ∀ c' z, (c', z) ∈ (⟨n.leaf, last.ks⟩ : KNode).liveAt c.i → z < w.next)
    (hnwf : klongsWf n.ks = true) (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ c.i)
    (hkeep : ∀ cc u, (cc, u) ∈ n.liveAt c.i →
      (∃ c', (c', u) ∈ (⟨n.leaf, last.ks⟩ : KNode).liveAt c.i) ∨ wNode c.p base w u = none) :
    WriterWP (handleFullWith rootUp 0 L [] last compact) c w
      (fun _ w' => TakeJ2 c base B w' ∧ B ≤ w'.next) := by
  have hLn : L < w.next := by
    rcases Nat.lt_or_ge L w.next with h | h
    · exact h
    · rw [(hS5 L h).1] at hlk; cases hlk
  have hwL : wNode c.p base w L = some n := by
    simp only [wNode, htk, Bool.false_eq_true, ↓reduceIte, hlk]
  have hlevel := writerWP_handleFull_rootVReach 2 (Nat.le_refl _) c base hvc rootUp L n last compact hlwf hlt
    hlastV hlen2 w hlk htk hrk hS5 hS6 hW hV hvx
  have hshape := writerWP_handleFull_rootShape c rootUp L n last compact (fun _ => L) (fun _ => 0)
    (fun _ => n) rfl rfl hpairs hlastV hlen2 w hlk hLn (fun z hz => (hS5 z hz).1)
  have hcache := @state_handleFullWith_compact (cachedFromInvariant w) rootUp 0 L [] last compact
    (fun q more => @keepsState_rootUp (cachedFromInvariant w) q more) c w (cachedFrom_refl _ c)
  have hnext := @state_handleFullWith_compact (nextFromInvariant w) rootUp 0 L [] last compact
    (fun q more => @keepsState_rootUp (nextFromInvariant w) q more) c w (Nat.le_refl _)
  refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and hlevel hshape) hcache) hnext) ?_
  rintro _ w7 ⟨⟨⟨⟨_, ht7, hv7, _, _, _, _, hRB8, hRB9, hRB10, _⟩, hSP7, _⟩, hca7⟩, hn7⟩
  have hN6 : ∀ i, 0 ≤ i → i ≤ 0 → wNode c.p base w ((fun _ => L) i) = some ((fun _ => n) i) :=
    fun _ _ _ => hwL
  obtain ⟨_, hfr7, _, hsh⟩ := hSP7
  have hN76 : ∀ z, z < w.next → (∀ i, 0 ≤ i → i ≤ 0 → z ≠ (fun _ => L) i) →
      wNode c.p base w7 z = wNode c.p base w z := by
    intro z hz hnc
    simp only [wNode, ht7, hfr7 z hz hnc]
  obtain ⟨hD7, hO7, hS7, hM7, hV7⟩ := j2rest_cascade2 (wNode c.p base w) (wNode c.p base w7) c.i
    w.top.rootKey B (w.vals.map (·.1)) (fun _ => L) (fun _ => n) 0 0 w.next hpos hT hJ.2.1 hJ.2.2.1
    hJ.2.2.2.1 hJ.2.2.2.2.1 hJ.2.2.2.2.2 hN6 (fun _ _ _ => hnwf) (fun _ _ _ => hnt)
    (fun _ _ _ => by rw [hrk]; exact TReach.root) hvnx hN76
    (by
      intro z zn hz hz'
      have htz : w7.taken.contains z = false := by
        rw [ht7]
        rcases hz' with h | ⟨i, _, _, hzi⟩
        · exact (hS5 z h).2.1
        · rw [hzi]; exact htk
      have hlk7 : w7.nodes.lookup z = some zn := by
        unfold wNode at hz
        rw [htz] at hz
        simp only [Bool.false_eq_true, ↓reduceIte] at hz
        cases hl : w7.nodes.lookup z with
        | some m => rw [hl] at hz; exact hz
        | none =>
          exfalso
          rw [hl] at hz
          rcases hz' with h | ⟨i, _, _, hzi⟩
          · rw [(hS5 z h).2.2] at hz; cases hz
          · skip
            have := hca7 L (by rw [hlk]; rfl)
            rw [← hzi, hl] at this; cases this
      exact cascadeShapeJ2_of c (wNode c.p base w) B _ (fun _ => L) (fun _ => 0) (fun _ => n) 0 0 [] _
        hJ.2.2.2.1 hJ.2.2.2.2.1 hN6 (fun _ _ _ => hnt) hBn (by simp) (by simp) z zn hz' (hsh z zn hlk7 hz'))
  -- (B): a node of the transaction's time is reached
  have hTt7 : TtReachedN (wNode c.p base w7) c.i w7.top.rootKey := by
    intro q qn hq hm
    by_cases hqL : q = L
    · subst hqL
      rcases hRB9 with h | ⟨_, h, _⟩
      · exact h
      · exfalso
        rw [h] at hq
        cases hq
        exact time_not_mem_toPrev n c.i hpos hm
    by_cases hqn : w.next ≤ q
    · refine hRB10 q hqn ?_
      have htz : w7.taken.contains q = false := by rw [ht7]; exact (hS5 q hqn).2.1
      unfold wNode at hq
      rw [htz] at hq
      simp only [Bool.false_eq_true, ↓reduceIte] at hq
      cases hl : w7.nodes.lookup q with
      | some _ => rfl
      | none => rw [hl, (hS5 q hqn).2.2] at hq; cases hq
    rw [hN76 q (by omega) (fun _ _ _ => hqL)] at hq
    have hTN := hJ.1 q qn hq hm
    rcases reach_updN_keep (wNode c.p base w) c.i w.top.rootKey L n ⟨n.leaf, last.ks⟩ hwL hkeep q hTN with h | h
    · exact hRB8 q h hqL
    · rw [h] at hq; cases hq
  refine ⟨?_, Nat.le_trans hBn hn7⟩
  unfold TakeJ2
  rw [hv7]
  exact ⟨hTt7, hD7, hO7, hS7, hM7, hV7⟩

/-- The last version of a full leaf without cv, its facts for the splits. -/
theorem delLast_split_facts (c : Ctx) (n : KNode) (cv : Nat) (hsa2 : 2 ≤ c.p.splitAbove)
    (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ c.i) (last : KNode)
    (hlast : n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv)) = last) :
    (⟨n.leaf, last.ks⟩ : KNode) = last ∧ klongsWf last.ks = true ∧ (∀ s, Klong.time s ∈ last.ks → s ≤ c.i) ∧
    (⟨n.leaf, last.ks⟩ : KNode).lastVersion c.i = last ∧
    (c.p.splitAbove < last.size → 2 ≤ (⟨n.leaf, last.ks⟩ : KNode).live.length) ∧
    (∃ pairs, last.ks = newKlongs c.i pairs ∧ (pairs.map Prod.fst).Nodup) ∧
    (∀ c' z, (c', z) ∈ last.liveAt c.i ↔ (c', z) ∈ n.liveAt c.i ∧ c' ≠ cv) ∧
    (∀ c', last.live.lookup c' = if c' == cv then none else n.live.lookup c') := by
  obtain ⟨hleq, hlt, _⟩ := delLast_facts n c.i cv
  have hdl : ∀ c', last.live.lookup c' = if c' == cv then none else n.live.lookup c' :=
    fun c' => by rw [← hlast]; exact KNode.delete_live_lookup n c.i cv c'
  obtain ⟨pairs, hks, hsorted⟩ := n.lastVersionGivenDel_order c.i (bitsUnion n.lastBitmap (n.bitsOf cv))
  rw [hlast] at hleq hlt hks
  have hiff := liveAt_iff_of_delete_lookup n last c.i cv hnt hlt hdl
  have hks' : last.ks = newKlongs c.i pairs := by rw [hks]; rfl
  have hsize : last.size = pairs.length + 1 := by simp [KNode.size, hks', newKlongs]
  have hlive : (⟨n.leaf, last.ks⟩ : KNode).live = pairs := by
    rw [hks']; exact KNode.live_newKlongs_sorted _ _ _ hsorted
  refine ⟨hleq, by rw [hks']; exact klongsWf_newKlongs c.i pairs, hlt, ?_, ?_,
    ⟨pairs, hks', List.pairwise_map.mpr (hsorted.imp (by intro a b hab; omega))⟩, hiff, hdl⟩
  · have hlastEq : last = ⟨n.leaf, newKlongs c.i pairs⟩ := by rw [← hks', hleq]
    rw [hleq, hlastEq, KNode.lastVersion_newKlongs_sorted _ _ _ hsorted]
  · intro h; rw [hlive]; omega

/-- `DelFullRootJ2OK` for the transaction after every run: the root's split by
`writerWP_handleFull_root_j2`. -/
theorem delFullRootJ2OK_ctx (p : Params) (hsa2 : 2 ≤ p.splitAbove) (ts : List Tx) (B : NodeId) :
    DelFullRootJ2OK (ctxOf p ts) (viewOf (treeRun p ts)) B := by
  intro w hI hG hRO hJ hBn X K Nn hP cv n hNd hnl hne hfull hcvN
  have hvc := viewCoherent_ctxOf p ts
  have hpos : 0 < (ctxOf p ts).i := by simp [ctxOf]
  obtain ⟨_, _, hS2, _, h0⟩ := hP
  have hlk : w.nodes.lookup (X 0) = some n := by rw [← hNd]; exact (hS2 0 (Nat.le_refl _)).1
  have htk : w.taken.contains (X 0) = false := (hS2 0 (Nat.le_refl _)).2
  have hwL : wNode p (viewOf (treeRun p ts)) w (X 0) = some n := by
    simp only [wNode, htk, Bool.false_eq_true, ↓reduceIte, hlk]
  have hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ (ctxOf p ts).i := hI.times _ _ hwL
  obtain ⟨hleq, hlwf, hlt, hlastV, hlen2, hpairs, hiff, _⟩ := delLast_split_facts (ctxOf p ts) n cv hsa2 hnt _ rfl
  have hS5 : ∀ z, w.next ≤ z → w.nodes.lookup z = none ∧ w.taken.contains z = false ∧
      knodeOf (ctxOf p ts).p (viewOf (treeRun p ts)) z = none := by
    intro z hz
    refine ⟨?_, ?_, (hI.fresh z hz).1⟩
    · cases h' : w.nodes.lookup z with
      | none => rfl
      | some _ => have := hI.ids.1 z (by rw [h']; rfl); omega
    · cases h' : w.taken.contains z with
      | false => rfl
      | true => have := hI.ids.2.2.1 z h'; omega
  refine writerWP_appendDeleteKlong_full_of (X 0) 0 cv n (ctxOf p ts) w hlk hne hfull _ ?_
  intro compact s
  exact writerWP_handleFull_root_j2 (ctxOf p ts) _ hvc B hpos (X 0) n _ compact
    ({ w with trail := s :: w.trail } : W) hJ hBn
    (by
      intro y hy
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hy
      have := hI.ids.2.2.2.1 _ he
      simpa using this)
    hI.tree hlwf hlt hlastV hlen2 hpairs hlk htk h0.symm hS5
    (fun u c' z ⟨un, hun, hl⟩ => hG.links u un c' z hun hl) hI.wf
    (by
      rw [hleq]
      exact treeOK_of_node_shrink _ _ _ _ (X 0) n _ hI.tree hwL (updN_self _ _ _)
        (fun y hy => by simp only [updN, hy, ↓reduceIte]; rfl) (fun c' z h => ((hiff c' z).mp h).1))
    (by
      intro c' z hz
      rw [hleq] at hz
      exact hG.links _ n c' z hwL ((hiff c' z).mp hz).1)
    (hI.wf _ _ hwL) hnt
    (by
      intro cc u hm
      rw [hleq]
      by_cases hc : cc = cv
      · rw [hc] at hm; exact Or.inr (hcvN u hm)
      · exact Or.inl ⟨cc, (hiff cc u).mpr ⟨hm, hc⟩⟩)

set_option maxHeartbeats 3200000 in
/-- `DelFullRootStepOKT`: `delFullRootStepOK_ctx` with no fit at the start, the
reading where the start fits (bergdb 025-05, step 7). -/
theorem delFullRootStepOKT_ctx (p : Params) (ts : List Tx) :
    DelFullRootStepOKT (ctxOf p ts) (viewOf (treeRun p ts)) := by
  intro w hI hG hRO hsa2 X K Nn hP pre cv rk hkey hrk hvisL huniq hnl hne hfull
  have hvc := viewCoherent_ctxOf p ts
  obtain ⟨_, _, hS2, _, h0⟩ := hP
  generalize hc : ctxOf p ts = c at *
  generalize hbase : viewOf (treeRun p ts) = base at *
  generalize hL : X 0 = L at *
  generalize hn : Nn 0 = n at *
  have hfuel : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  have hlk : w.nodes.lookup L = some n := by
    have := (hS2 0 (Nat.le_refl _)).1; rwa [hL, hn] at this
  have htk : w.taken.contains L = false := by
    have := (hS2 0 (Nat.le_refl _)).2; rwa [hL] at this
  have hrk0 : w.top.rootKey = L := h0.symm
  have hwL : wNode c.p base w L = some n := by
    simp only [wNode, htk, Bool.false_eq_true, ↓reduceIte, hlk]
  have hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ c.i := hI.times _ _ hwL
  have hnwf : klongsWf n.ks = true := hI.wf _ _ hwL
  have hS5 : ∀ z, w.next ≤ z → w.nodes.lookup z = none ∧ w.taken.contains z = false ∧
      knodeOf c.p base z = none := by
    intro z hz
    refine ⟨?_, ?_, (hI.fresh z hz).1⟩
    · cases h' : w.nodes.lookup z with
      | none => rfl
      | some _ => have := hI.ids.1 z (by rw [h']; rfl); omega
    · cases h' : w.taken.contains z with
      | false => rfl
      | true => have := hI.ids.2.2.1 z h'; omega
  refine writerWP_appendDeleteKlong_full_of L 0 cv n c w hlk hne hfull _ ?_
  intro compact s
  have hrange := writerWP_delRootSplit_range c base hvc rootUp L n cv compact hnl hsa2 hnt
    ({ w with trail := s :: w.trail } : W) hlk htk hrk0 hI.tree hS5
    (fun u c' z ⟨un, hun, hl⟩ => hG.links u un c' z hun hl) hRO
  generalize hlast : n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv)) = last at hrange ⊢
  obtain ⟨hleq, hlwf, hlt, hlastV, hlen2, _, hiff, hdl⟩ := delLast_split_facts c n cv hsa2 hnt last hlast
  have hsub : ∀ c' z, (c', z) ∈ last.liveAt c.i → (c', z) ∈ n.liveAt c.i :=
    fun c' z h => ((hiff c' z).mp h).1
  have hlevel := writerWP_handleFull_rootVReach (c.p.fuel + 1) (by omega) c base hvc rootUp L n last compact
    hlwf hlt hlastV hlen2 ({ w with trail := s :: w.trail } : W) hlk htk hrk0 hS5
    (fun u c' z ⟨un, hun, hl⟩ => hG.links u un c' z hun hl) hI.wf
    (by
      rw [hleq]
      exact treeOK_of_node_shrink _ _ _ _ L n _ hI.tree hwL (updN_self _ _ _)
        (fun y hy => by simp only [updN, hy, ↓reduceIte]; rfl) hsub)
    (by
      intro c' z hz
      rw [hleq] at hz
      exact hG.links _ n c' z hwL (hsub c' z hz))
  have hnext := @state_handleFullWith_compact (nextFromInvariant w) rootUp 0 L [] last compact
    (fun q more => @keepsState_rootUp (nextFromInvariant w) q more) c
    ({ w with trail := s :: w.trail } : W) (Nat.le_refl _)
  -- the virtual state with the leaf's last version
  generalize hw3 : ({ w with nodes := upsert w.nodes L last } : W) = w3
  have hN3 : ∀ y, wNode c.p base w3 y = if y = L then some last else wNode c.p base w y := by
    intro y
    rw [← hw3]
    by_cases hy : y = L
    · subst hy
      simp only [wNode, htk, Bool.false_eq_true, ↓reduceIte, lookup_upsert]
    · simp only [wNode, lookup_upsert, hy, ↓reduceIte]
  have hN3u : wNode c.p base w3 = updN (wNode c.p base w) L last := by
    funext y
    rw [hN3 y]
    by_cases hy : y = L
    · subst hy; simp [updN]
    · simp [updN, hy]
  have h3top : w3.top = w.top := by rw [← hw3]
  have hV3 : wValue base w3 = wValue base w := by
    rw [← hw3]; exact wValue_congr' base _ w rfl rfl
  have hvL : wNode c.p base w3 L = some last := by rw [hN3]; simp
  have hvo : ∀ y, y ≠ L → wNode c.p base w3 y = wNode c.p base w y := by
    intro y hy; rw [hN3 y]; simp [hy]
  have hl' : last.leaf = n.leaf := by rw [← hleq]
  have hRS : ∀ u, ReachS (wNode c.p base w3) c.i w3.top.rootKey u →
      ReachS (wNode c.p base w) c.i w.top.rootKey u := by
    rw [h3top]
    apply reachS_closed _ _ _ (fun y => ReachS (wNode c.p base w) c.i w.top.rootKey y) ReachS.root
    intro y yn cc z hy hyn hz
    by_cases hyx : y = L
    · subst hyx
      rw [hvL] at hyn; cases hyn
      exact ReachS.step _ _ cc z hy hwL (hsub cc z hz)
    · rw [hvo y hyx] at hyn
      exact ReachS.step y yn cc z hy hyn hz
  have hF3 : SegFits (wNode c.p base w) c.i (c.p.fuel - 1) w.top.rootKey → SegFits (wNode c.p base w3) c.i (c.p.fuel - 1) w3.top.rootKey :=
    fun hF => segFits_transfer _ _ c.i _ _ _ hF hRS (fun u un' _ hun' hl => by
      by_cases hu : u = L
      · subst hu; rw [hvL] at hun'; cases hun'; rw [hl', hnl] at hl; cases hl
      · rw [hvo u hu] at hun'
        exact ⟨un', hun', hl, fun c' y hy => ⟨c', hy⟩⟩)
  have hread3 : SegFits (wNode c.p base w) c.i (c.p.fuel - 1) w.top.rootKey → ∀ key', keyWf key' = true →
      wGetAt c.p c.i base w3 (c.p.fuel + 1) key' =
        if pre ++ [cv] == key' then none else wGetAt c.p c.i base w (c.p.fuel + 1) key' := by
    intro hF key' hk'
    have hwf3 : ∀ x xn, ReachS (wNode c.p base w3) c.i w3.top.rootKey x → wNode c.p base w3 x = some xn →
        klongsWf xn.ks = true := by
      intro x xn _ h
      by_cases hx : x = L
      · subst hx; rw [hvL] at h; cases h; exact hlwf
      · rw [hvo x hx] at h; exact hI.wf x xn h
    have hwfw : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x → wNode c.p base w x = some xn →
        klongsWf xn.ks = true := fun x xn _ h => hI.wf x xn h
    rw [wGetAt_eq_wGet c base w3 _ (by omega) hwf3 (hF3 hF), wGetAt_eq_wGet c base w _ (by omega) hwfw hF]
    obtain ⟨hown, hother⟩ := wGet_leaf_change_seg c.p base c.i w w3 L pre cv rk n last
      hfuel h3top (fun x hx => (hvo x hx).symm) hwL hvL hnl (by rw [hl']; exact hnl)
      (fun c' hc' => by
        rw [KNode.searchEq_live _ c.i hnwf hnt, KNode.searchEq_live last c.i hlwf hlt, hdl c']
        have hb : (c' == cv) = false := by simpa using hc'
        rw [hb]; rfl)
      hrk (keyWf_last_notin pre cv hkey) hvisL huniq
      (fun _ _ _ _ y _ _ _ _ _ => by rw [hV3])
    by_cases hk : pre ++ [cv] = key'
    · subst hk
      simp only [beq_self_eq_true, ↓reduceIte]
      rw [hown, KNode.searchEq_live last c.i hlwf hlt, hdl cv]
      simp
    · have hk2 : (pre ++ [cv] == key') = false := by simpa using hk
      simp only [hk2, Bool.false_eq_true, ↓reduceIte]
      exact hother key' hk' (fun h => hk h.symm)
  refine writerWP_mono (writerWP_and (writerWP_and hrange hlevel) hnext) ?_
  rintro _ v ⟨⟨⟨hTv, hreachv, hRv⟩, ⟨_, htv, hvv, _, _, hRead, _⟩⟩, hnv⟩
  refine ⟨hTv, htv, hvv, hnv, hreachv, hRv, ?_⟩
  intro hF hFv key' hk'
  have hVal : ∀ z, (w.next ≤ z ∨ z = L) → wValue base v z = none := by
    intro z hz
    rw [wValue_congr' base v w htv hvv]
    rcases hz with hz | rfl
    · have htz : w.taken.contains z = false := (hS5 z hz).2.1
      have hvz : w.vals.lookup z = none := by
        cases h' : w.vals.lookup z with
        | none => rfl
        | some _ =>
          have hm := lookup_some_mem h'
          have := hI.ids.2.2.2.1 _ hm
          simp only at this; omega
      simp only [wValue, htz, Bool.false_eq_true, ↓reduceIte, hvz, (hI.fresh z hz).2]
    · exact hI.keyNoValue _ _ hwL
  have hR := hRead (wValue base v) hVal (Or.inl (by simpa using hFv)) key'
  have h1 : wGetAt c.p c.i base v (c.p.fuel + 1) key' = wGetAt c.p c.i base w3 (c.p.fuel + 1) key' := by
    unfold wGetAt
    rw [hR, hN3u, h3top, hV3, ← wValue_congr' base v w htv hvv, hleq]
    rfl
  rw [h1]
  exact hread3 hF key' hk'



/-- `DelFullRootStepOK`: the reading's facts after a delete into a full leaf that
is the space root, from the root's split (`writerWP_delRootSplit_range` for the
tree, the reached nodes and the ranges; `writerWP_handleFull_rootVReach` for the
reading), for the transaction after every run. -/
theorem delFullRootStepOK_ctx (p : Params) (ts : List Tx) :
    DelFullRootStepOK (ctxOf p ts) (viewOf (treeRun p ts)) :=
  delFullRootStepOK_of_T _ _ (delFullRootStepOKT_ctx p ts)end SIS.Tree
