/-
A full node's split whose parent has room, with the hole (bergdb 030-01, step 3's
rest), continued: the copy's cached segment and height are the node's
(`writerWP_handleFull_timeRoom_gh`), for R1 at the next round.
-/
import SIS.Tree.LiveRedirectDescent

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- `ghOf` of a cached node returns its entry in `gh`. -/
theorem writerWP_ghOf_cachedL (x : NodeId) (n : KNode) (c : Ctx) (w : W)
    (hn : w.nodes.lookup x = some n) (post : Nat × Nat → W → Prop)
    (hp : ∀ gh, w.gh.lookup x = some gh → post gh w) :
    WriterWP (ghOf x) c w post := by
  unfold ghOf
  simp only [writerWP_bind]
  rw [writerWP_getNode_known x n c w hn]
  simp only [writerWP_get]
  split
  · rename_i v hv
    simp only [writerWP_pure]; exact hp _ hv
  · exact writerWP_throw _ _ _ _

/-- `writerWP_handleFullWith_time_up_last'` with the copy's entry in `gh`: the
node's own. -/
theorem writerWP_handleFullWith_time_up_last_gh (d' : Nat) (x q : NodeId) (n qn : KNode) (k1 : Nat)
    (last : KNode) (compact : Bool) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup x = some n) (hlq : w.nodes.lookup q = some qn)
    (hfirst : n.firstTime ≠ some c.i)
    (hcs : (!compact && decide (last.size > c.p.splitAbove)) = false)
    (hpq : (w.path[d']?).map (·.2) = some q) (hpk : w.path[d' + 1]? = some (some k1, x))
    (Q : W → Prop)
    (hup : ∀ (gh : Nat × Nat), w.gh.lookup x = some gh → ∀ w1 : W,
        w1.nodes = w.nodes ++ [(w.next, ⟨n.leaf, last.ks⟩)] → w1.gh = (w.next, gh.1, gh.2) :: w.gh →
        w1.taken = w.taken → w1.top = w.top → w1.path = w.path → w1.next = w.next + 2 →
        WriterWP (appendKlongs d' q [(k1, w.next)]) c w1 (fun _ w2 =>
          WriterWP (do let m ← getNode x; putNode x (m.toPrev (c.i - 1))) c w2 (fun _ w3 => Q w3))) :
    WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) x []
      last compact) c w (fun _ w' => Q w') := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c w hlk]
  refine writerWP_ghOf_cachedL x n c w hlk _ (fun gh hgh => ?_)
  have hnew : (n.firstTime == some c.i) = false := by simpa using hfirst
  simp only [hnew]
  unfold parentAt pathNode
  simp only [writerWP_bind, writerWP_get]
  cases hp : w.path[d']? with
  | none => rw [hp] at hpq; cases hpq
  | some e =>
    rw [hp] at hpq
    simp only [Option.map_some, Option.some.injEq] at hpq
    simp only [writerWP_pure]
    rw [hpq]
    simp only [writerWP_bind]
    rw [writerWP_getNode_known q qn c w hlq]
    simp only [writerWP_pure, hcs, Bool.false_eq_true, ↓reduceIte]
    split
    · simp only [note, writerWP_bind, writerWP_modify]
      refine writerWP_mono (writerWP_replaceOrAdd_nil last c _) ?_
      rintro l w1 ⟨hw1, hl⟩
      subst w1 hl
      split <;>
      · simp only [newKey, fresh, setMadeFor, klongAt, writerWP_bind, writerWP_modify,
          writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
        split <;>
        · simp only [writerWP_bind, writerWP_modify, writerWP_pure, hpk]
          exact hup gh hgh _ rfl rfl rfl rfl rfl rfl
    · simp only [writerWP_bind]
      refine writerWP_mono (writerWP_replaceOrAdd_nil last c _) ?_
      rintro l w1 ⟨hw1, hl⟩
      subst w1 hl
      split <;>
      · simp only [newKey, fresh, setMadeFor, klongAt, note, writerWP_bind, writerWP_modify,
          writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
        split <;>
        · simp only [writerWP_bind, writerWP_modify, writerWP_pure, hpk]
          exact hup gh hgh _ rfl rfl rfl rfl rfl rfl

set_option maxHeartbeats 4000000 in
/-- `writerWP_handleFull_timeRoom_live` with the copy's entry in `gh`: x's. -/
theorem writerWP_handleFull_timeRoom_liveGh (d' : Nat) (x q : NodeId) (n qn : KNode) (k1 : Nat)
    (last : KNode) (compact : Bool) (c : Ctx) (base : View BVal) (w : W)
    (hlk : w.nodes.lookup x = some n) (hxt : w.taken.contains x = false)
    (hlq : w.nodes.lookup q = some qn) (hqt : w.taken.contains q = false) (hqx : q ≠ x)
    (hxn : x < w.next) (hqn : q < w.next)
    (hfirst : n.firstTime ≠ some c.i)
    (hcs : (!compact && decide (last.size > c.p.splitAbove)) = false)
    (hpq : (w.path[d']?).map (·.2) = some q) (hpk : w.path[d' + 1]? = some (some k1, x))
    (hqwf : klongsWf qn.ks = true) (hqtm : ∀ s, Klong.time s ∈ qn.ks → s ≤ c.i)
    (hroom : qn.size + 2 ≤ c.p.M) (hdead : deadOver c.p (qn.add c.i (.key k1 w.next)) = false)
    (hk : (k1, x) ∈ qn.liveAt c.i)
    (hT : TreeOK (updN (wNode c.p base w) x ⟨n.leaf, last.ks⟩) c.i w.top.rootKey)
    (hqR : TReach (updN (wNode c.p base w) x ⟨n.leaf, last.ks⟩) c.i w.top.rootKey q)
    (hnx : wNode c.p base w w.next = none) (hnl : w.nodes.lookup w.next = none)
    (hnt : w.taken.contains w.next = false)
    (hfreshT : ∀ u c', TReach (updN (wNode c.p base w) x ⟨n.leaf, last.ks⟩) c.i w.top.rootKey u →
      ¬ TLink (updN (wNode c.p base w) x ⟨n.leaf, last.ks⟩) c.i u c' w.next)
    (hV : LiveEdgesH c.p (updN (wNode c.p base w) x ⟨n.leaf, last.ks⟩) c.i w.top.rootKey
      (fun z => z = x)) :
    WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) x [] last compact) c w
      (fun _ w' => LiveEdgesH c.p (wNode c.p base w') c.i w'.top.rootKey (fun z => z = w.next) ∧
        (∀ z, z ≠ q → z ≠ x → z ≠ w.next → w'.nodes.lookup z = w.nodes.lookup z) ∧
        w'.nodes.lookup w.next = some ⟨n.leaf, last.ks⟩ ∧
        w'.nodes.lookup q = some (qn.add c.i (.key k1 w.next)) ∧
        w'.taken = w.taken ∧ w'.top = w.top ∧ w'.path = w.path ∧ w'.next = w.next + 2 ∧
        w'.gh.lookup w.next = w.gh.lookup x ∧ (∀ u, u ≠ w.next → w'.gh.lookup u = w.gh.lookup u)) := by
  have hqy : q ≠ w.next := by omega
  have hxy : x ≠ w.next := by omega
  refine writerWP_handleFullWith_time_up_last_gh d' x q n qn k1 last compact c w hlk hlq hfirst hcs hpq hpk
    _ ?_
  intro gh hgh w1 h1n h1gh h1t h1top h1path h1next
  have hlq1 : w1.nodes.lookup q = some qn := by
    rw [h1n, lookup_append_single_ne _ _ _ _ hqy]; exact hlq
  refine writerWP_mono (writerWP_appendKlongs_addKeys d' q qn [(k1, w.next)] c w1 hlq1
    (by simpa using hroom) (by simpa using hdead)) ?_
  intro _ w2 hw2
  have h2n : w2.nodes = upsert w1.nodes q (qn.add c.i (.key k1 w.next)) := by rw [hw2]; rfl
  have h2t : w2.taken = w1.taken := by rw [hw2]
  have h2top : w2.top = w1.top := by rw [hw2]
  have h2path : w2.path = w1.path := by rw [hw2]
  have h2next : w2.next = w1.next := by rw [hw2]
  have h2gh : w2.gh = w1.gh := by rw [hw2]
  have hlx2 : w2.nodes.lookup x = some n := by
    rw [h2n, lookup_upsert, if_neg (Ne.symm hqx), h1n, lookup_append_single_ne _ _ _ _ hxy]; exact hlk
  rw [writerWP_bind, writerWP_getNode_known x n c w2 hlx2]
  simp only [putNode, writerWP_modify]
  have key : ∀ w3 : W, w3.nodes = upsert w2.nodes x (n.toPrev (c.i - 1)) → w3.taken = w2.taken →
      w3.top = w2.top → w3.path = w2.path → w3.next = w2.next → w3.gh = w2.gh →
      LiveEdgesH c.p (wNode c.p base w3) c.i w3.top.rootKey (fun z => z = w.next) ∧
        (∀ z, z ≠ q → z ≠ x → z ≠ w.next → w3.nodes.lookup z = w.nodes.lookup z) ∧
        w3.nodes.lookup w.next = some ⟨n.leaf, last.ks⟩ ∧
        w3.nodes.lookup q = some (qn.add c.i (.key k1 w.next)) ∧
        w3.taken = w.taken ∧ w3.top = w.top ∧ w3.path = w.path ∧ w3.next = w.next + 2 ∧
        w3.gh.lookup w.next = w.gh.lookup x ∧ (∀ u, u ≠ w.next → w3.gh.lookup u = w.gh.lookup u) := by
    intro w3 h3n h3t0 h3top0 h3path0 h3next0 h3gh
    have h3t : w3.taken = w.taken := by rw [h3t0, h2t, h1t]
    have h3top : w3.top = w.top := by rw [h3top0, h2top, h1top]
    have h3path : w3.path = w.path := by rw [h3path0, h2path, h1path]
    have h3next : w3.next = w.next + 2 := by rw [h3next0, h2next, h1next]
    have hlook : ∀ z, z ≠ q → z ≠ x → z ≠ w.next → w3.nodes.lookup z = w.nodes.lookup z := by
      intro z hzq hzx hzy
      rw [h3n, lookup_upsert, if_neg hzx, h2n, lookup_upsert, if_neg hzq, h1n,
        lookup_append_single_ne _ _ _ _ hzy]
    have hly : w3.nodes.lookup w.next = some ⟨n.leaf, last.ks⟩ := by
      rw [h3n, lookup_upsert, if_neg (Ne.symm hxy), h2n, lookup_upsert, if_neg (Ne.symm hqy), h1n,
        lookup_append_single_self]
      exact hnl
    -- the tree after: x's copy named by q's klong k1 instead, x left behind
    have hVq : updN (wNode c.p base w) x ⟨n.leaf, last.ks⟩ q = some qn := by
      rw [updN_ne _ _ _ _ hqx]; simp only [wNode, hqt, Bool.false_eq_true, ↓reduceIte, hlq]
    have hq3t : w3.taken.contains q = false := by rw [h3t]; exact hqt
    have hy3t : w3.taken.contains w.next = false := by rw [h3t]; exact hnt
    have hlq3 : w3.nodes.lookup q = some (qn.add c.i (.key k1 w.next)) := by
      rw [h3n, lookup_upsert, if_neg hqx, h2n, lookup_upsert]; simp
    have hN'y : wNode c.p base w3 w.next = some ⟨n.leaf, last.ks⟩ := by
      simp only [wNode, hy3t, Bool.false_eq_true, ↓reduceIte, hly]
    have hN'q : wNode c.p base w3 q = some (qn.add c.i (.key k1 w.next)) := by
      simp only [wNode, hq3t, Bool.false_eq_true, ↓reduceIte, hlq3]
    have hN' : ∀ z, z ≠ q → z ≠ x → z ≠ w.next →
        wNode c.p base w3 z = updN (wNode c.p base w) x ⟨n.leaf, last.ks⟩ z := by
      intro z hzq hzx hzy
      rw [updN_ne _ _ _ _ hzx]
      simp only [wNode, h3t, hlook z hzq hzx hzy]
    have hat := KNode.add_times qn c.i (.key k1 w.next) (fun s h => by cases h) hqtm
    have hq' : ∀ c' z, (c', z) ∈ (qn.add c.i (.key k1 w.next)).liveAt c.i →
        (c' = k1 ∧ z = w.next) ∨ ((c', z) ∈ qn.liveAt c.i ∧ c' ≠ k1) := by
      intro c' z hmm
      rw [KNode.liveAt_of_times _ c.i hat] at hmm
      have hlk' := lookup_of_mem_nodup _ (KNode.live_keys_nodup _) c' z hmm
      rw [KNode.add_key_live_lookup_of_wf qn c.i k1 c' w.next hqwf] at hlk'
      by_cases hck : k1 = c'
      · subst hck; simp at hlk'; exact Or.inl ⟨rfl, hlk'.symm⟩
      · have hb : (k1 == c') = false := by simpa using hck
        rw [hb] at hlk'
        simp only [Bool.false_eq_true, ↓reduceIte] at hlk'
        refine Or.inr ⟨?_, Ne.symm hck⟩
        rw [KNode.liveAt_of_times qn c.i hqtm]
        exact bk_mem_of_lookup _ c' z hlk'
    have hgh3 : w3.gh = (w.next, gh.1, gh.2) :: w.gh := by rw [h3gh, h2gh, h1gh]
    refine ⟨?_, hlook, hly, hlq3, h3t, h3top, h3path, h3next, by rw [hgh3, hgh]; simp, fun u hu => ?_⟩
    rotate_left
    · rw [hgh3, List.lookup_cons]
      have : (u == w.next) = false := by simpa using hu
      simp [this]
    rw [h3top]
    exact liveEdgesH_redirect c.p _ (wNode c.p base w3) c.i w.top.rootKey q x w.next qn
      (qn.add c.i (.key k1 w.next)) ⟨n.leaf, last.ks⟩ k1 hT hV hqR hVq hk (updN_self _ _ _)
      (by rw [updN_ne _ _ _ _ (Ne.symm hxy)]; exact hnx) hfreshT hN'y hN'q (KNode.add_leaf _ _ _) hq'
      (addKeys_liveAt_length c.i [(k1, w.next)] qn hqwf hqtm) hN'

  exact key _ rfl rfl rfl rfl rfl rfl


end SIS.Tree
