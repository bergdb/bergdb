/-
A full node's split whose parent has room, with the hole (bergdb 030-01, step 3's
rest, R4's narrower lemma): no cascade. A time split moves the hole to the
node's copy, which the parent's klong names instead (`liveEdgesH_redirect`).
-/
import SIS.Tree.LiveCollapseFull

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- A node x, the only hole, named by q's live klong k1, is replaced by a fresh
node y of x's klongs: q's klong k1 names y instead, and x is left behind. The
hole is y after. -/
theorem liveEdgesH_redirect (p : Params) (V N' : NodeId → Option KNode) (t : Time)
    (r q x y : NodeId) (qn qn' xl : KNode) (k1 : Nat)
    (hT : TreeOK V t r) (h : LiveEdgesH p V t r (fun z => z = x))
    (hq : TReach V t r q) (hqn : V q = some qn) (hk : (k1, x) ∈ qn.liveAt t) (hxn : V x = some xl)
    (hyV : V y = none) (hyf : ∀ u c, TReach V t r u → ¬ TLink V t u c y)
    (hN'y : N' y = some xl) (hN'q : N' q = some qn') (hq'l : qn'.leaf = qn.leaf)
    (hq' : ∀ c z, (c, z) ∈ qn'.liveAt t → (c = k1 ∧ z = y) ∨ ((c, z) ∈ qn.liveAt t ∧ c ≠ k1))
    (hq'len : (qn.liveAt t).length ≤ (qn'.liveAt t).length)
    (hN' : ∀ z, z ≠ q → z ≠ x → z ≠ y → N' z = V z) :
    LiveEdgesH p N' t r (fun z => z = y) := by
  have hlkx : TLink V t q k1 x := ⟨qn, hqn, hk⟩
  have hxR : TReach V t r x := TReach.link hq hlkx
  have hxr : x ≠ r := fun he => hT.rootFree q k1 hq (by rw [← he]; exact hlkx)
  have hqx : q ≠ x := fun he => hT.no_self_link q k1 hq ⟨qn, hqn, by rw [← he] at hk; exact hk⟩
  have hyx : y ≠ x := fun he => by rw [he, hxn] at hyV; cases hyV
  have hyq : y ≠ q := fun he => by rw [he, hqn] at hyV; cases hyV
  have hyr : y ≠ r := by
    intro he; obtain ⟨m, hm⟩ := hT.rootKey; rw [← he, hyV] at hm; cases hm
  have honlyx : ∀ u c, TReach V t r u → TLink V t u c x → u = q ∧ c = k1 :=
    fun u c hu hl => hT.oneLink u c q k1 x hu hq hl hlkx
  obtain ⟨dq, hdq⟩ := TReach.pathLen hq
  -- a child of x: not q, not x, not y
  have hchild : ∀ c z, (c, z) ∈ xl.liveAt t → z ≠ q ∧ z ≠ x ∧ z ≠ y := by
    intro c z hz
    have hl : TLink V t x c z := ⟨xl, hxn, hz⟩
    refine ⟨fun he => ?_, fun he => hT.no_self_link x c hxR (by rw [he] at hl; exact hl),
      fun he => hyf x c hxR (by rw [← he]; exact hl)⟩
    have h2 : PathLen V t r z (dq + 1 + 1) := PathLen.link (PathLen.link hdq hlkx) hl
    rw [he] at h2
    have := PathLen.depth_unique hT _ _ _ hdq h2
    omega
  have hxne : xl.liveAt t ≠ [] := (h.2 q qn k1 x xl hq hqn hk hxn).2 rfl
  have hreach : ∀ u, TReach N' t r u → (TReach V t r u ∧ u ≠ x ∧ u ≠ y) ∨ u = y := by
    intro u hu
    induction hu with
    | root => exact Or.inl ⟨TReach.root, Ne.symm hxr, Ne.symm hyr⟩
    | @link u c z _ hl ih =>
      obtain ⟨m, hm', hc⟩ := hl
      rcases ih with ⟨huR, hux, huy⟩ | huy
      · by_cases huq : u = q
        · subst huq
          rw [hN'q] at hm'
          cases hm'
          rcases hq' c z hc with ⟨_, hz⟩ | ⟨hold, hck⟩
          · exact Or.inr hz
          · have hl0 : TLink V t u c z := ⟨qn, hqn, hold⟩
            refine Or.inl ⟨TReach.link huR hl0, fun he => hck (honlyx u c huR (by rw [← he]; exact hl0)).2,
              fun he => hyf u c huR (by rw [← he]; exact hl0)⟩
        · rw [hN' u huq hux huy] at hm'
          have hl0 : TLink V t u c z := ⟨m, hm', hc⟩
          exact Or.inl ⟨TReach.link huR hl0, fun he => huq (honlyx u c huR (by rw [← he]; exact hl0)).1,
            fun he => hyf u c huR (by rw [← he]; exact hl0)⟩
      · subst huy
        rw [hN'y] at hm'
        cases hm'
        obtain ⟨_, hzx, hzy⟩ := hchild c z hc
        exact Or.inl ⟨TReach.link hxR ⟨xl, hxn, hc⟩, hzx, hzy⟩
  refine ⟨fun rn hrn => ?_, fun u un c z zn hu hun hc hzn => ?_⟩
  · by_cases hrq : r = q
    · rw [hrq, hN'q] at hrn
      cases hrn
      have hq0 := h.1 qn (by rw [hrq]; exact hqn)
      have hqne : qn.liveAt t ≠ [] := by intro h0; rw [h0] at hk; cases hk
      refine ⟨fun hE => ?_, fun hn hl' => ?_⟩
      · have h0 : (qn'.liveAt t).length = 0 := by rw [hE]; rfl
        exact absurd (List.eq_nil_of_length_eq_zero (by omega)) hqne
      · have := hq0.2 (by rw [hrq]; exact hqx) (by rw [← hq'l]; exact hl')
        omega
    · rw [hN' r hrq (Ne.symm hxr) (Ne.symm hyr)] at hrn
      exact ⟨(h.1 rn hrn).1, fun _ => (h.1 rn hrn).2 (Ne.symm hxr)⟩
  · refine ⟨fun hzy => ?_, fun hzy => ?_⟩
    rotate_left
    · rw [hzy, hN'y] at hzn; cases hzn; exact hxne
    rcases hreach u hu with ⟨huR, hux, huy⟩ | huy
    · by_cases huq : u = q
      · subst huq
        rw [hN'q] at hun
        cases hun
        rcases hq' c z hc with ⟨_, hz⟩ | ⟨hold, hck⟩
        · exact absurd hz hzy
        · have hl0 : TLink V t u c z := ⟨qn, hqn, hold⟩
          have hzx : z ≠ x := fun he => hck (honlyx u c huR (by rw [← he]; exact hl0)).2
          have hzu : z ≠ u := fun he => hT.no_self_link u c huR ⟨qn, hqn, by rw [he] at hold; exact hold⟩
          rw [hN' z hzu hzx hzy] at hzn
          exact childOK_grow p t qn _ zn zn ((h.2 u qn c z zn huR hqn hold hzn).1 hzx) hq'l rfl
            (Nat.le_refl _)
      · rw [hN' u huq hux huy] at hun
        by_cases hzq : z = q
        · subst hzq
          rw [hN'q] at hzn
          cases hzn
          exact childOK_grow p t un un qn _ ((h.2 u un c z qn huR hun hc hqn).1 hqx) rfl hq'l hq'len
        · have hl0 : TLink V t u c z := ⟨un, hun, hc⟩
          have hzx : z ≠ x := fun he => huq (honlyx u c huR (by rw [← he]; exact hl0)).1
          rw [hN' z hzq hzx hzy] at hzn
          exact (h.2 u un c z zn huR hun hc hzn).1 hzx
    · subst huy
      rw [hN'y] at hun
      cases hun
      obtain ⟨hzq, hzx, _⟩ := hchild c z hc
      rw [hN' z hzq hzx hzy] at hzn
      exact (h.2 x xl c z zn hxR hxn hc hzn).1 hzx

set_option maxHeartbeats 4000000 in
/-- A full node x that the transaction did not make, split in time with a last
version `last` given, below a parent q with room for the copy's klong: if the
tree with x's node replaced by `last` has the hole at x, the tree after has it at
the copy, the new id; nothing else changes but q and x. -/
theorem writerWP_handleFull_timeRoom_live (d' : Nat) (x q : NodeId) (n qn : KNode) (k1 : Nat)
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
        w'.taken = w.taken ∧ w'.top = w.top ∧ w'.path = w.path ∧ w'.next = w.next + 2) := by
  have hqy : q ≠ w.next := by omega
  have hxy : x ≠ w.next := by omega
  refine writerWP_handleFullWith_time_up_last' d' x q n qn k1 last compact c w hlk hlq hfirst hcs hpq hpk
    _ ?_
  intro w1 h1n h1t h1top h1path h1next _
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
  have hlx2 : w2.nodes.lookup x = some n := by
    rw [h2n, lookup_upsert, if_neg (Ne.symm hqx), h1n, lookup_append_single_ne _ _ _ _ hxy]; exact hlk
  rw [writerWP_bind, writerWP_getNode_known x n c w2 hlx2]
  simp only [putNode, writerWP_modify]
  have key : ∀ w3 : W, w3.nodes = upsert w2.nodes x (n.toPrev (c.i - 1)) → w3.taken = w2.taken →
      w3.top = w2.top → w3.path = w2.path → w3.next = w2.next →
      LiveEdgesH c.p (wNode c.p base w3) c.i w3.top.rootKey (fun z => z = w.next) ∧
        (∀ z, z ≠ q → z ≠ x → z ≠ w.next → w3.nodes.lookup z = w.nodes.lookup z) ∧
        w3.nodes.lookup w.next = some ⟨n.leaf, last.ks⟩ ∧
        w3.nodes.lookup q = some (qn.add c.i (.key k1 w.next)) ∧
        w3.taken = w.taken ∧ w3.top = w.top ∧ w3.path = w.path ∧ w3.next = w.next + 2 := by
    intro w3 h3n h3t0 h3top0 h3path0 h3next0
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
    refine ⟨?_, hlook, hly, hlq3, h3t, h3top, h3path, h3next⟩
    rw [h3top]
    exact liveEdgesH_redirect c.p _ (wNode c.p base w3) c.i w.top.rootKey q x w.next qn
      (qn.add c.i (.key k1 w.next)) ⟨n.leaf, last.ks⟩ k1 hT hV hqR hVq hk (updN_self _ _ _)
      (by rw [updN_ne _ _ _ _ (Ne.symm hxy)]; exact hnx) hfreshT hN'y hN'q (KNode.add_leaf _ _ _) hq'
      (addKeys_liveAt_length c.i [(k1, w.next)] qn hqwf hqtm) hN'

  exact key _ rfl rfl rfl rfl rfl

end SIS.Tree
