import SIS.Tree.PutInvDelRoot
import SIS.Tree.WriterTreeSegRoot

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! `PutInv` kept by the upward delete that empties a segment's tree of one
leaf (bergdb 024-12, TP10; `Dag.deleteUpward`, UP): the key's segment root L,
a leaf that existed before the transaction, loses its last live klong; the
climb stops at the segment leaf q above, which keeps a live klong; L loses its
klongs of the transaction (`unlink`), q gets a bitmap deleting k1, its klong
to L; the merges off (`putInv_del_up_segRoot`). The parts about the tree:
L is reached no more (`putInvT_drop`). -/

theorem writerWP_del_segRoot_leaf (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre0 : List Nat) (k1 cv : Nat) (rq L : NodeId) (n : KNode) (w : W)
    (hrq : segRootR (wNode c.p base w) c.i c.p.fuel pre0 w.top.rootKey = some rq)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre0 ++ [k1, cv]) w.top.rootKey,
      w.taken.contains q.1 = false)
    (hidn : ∀ z, (w.nodes.lookup z).isSome = true → z < w.next)
    (hidv : ∀ z, (c.view z).isSome = true → z < w.next)
    (hL : getEqR (wNode c.p base w) c.i k1 c.p.fuel rq = some L)
    (hNL : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (hqwf : ∀ q qn, (q, k1) ∈ eqVisits (wNode c.p base w) c.i k1 c.p.fuel rq →
      wNode c.p base w q = some qn → klongsWf qn.ks = true)
    (post : Bool → W → Prop)
    (hk : ∀ q qn d' (w5 : W), (q, k1) ∈ eqVisits (wNode c.p base w) c.i k1 c.p.fuel rq →
      wNode c.p base w q = some qn → qn.leaf = true → (k1, L) ∈ qn.liveAt c.i →
      w5.nodes.lookup L = some n → w5.nodes.lookup q = some qn →
      (∀ z, (w5.nodes.lookup z).isSome = true → z < w.next) →
      ReadsAs c.p base w w5 →
      (w5.path[d']?).map (·.2) = some q → w5.path[d' + 1]? = some (some k1, L) →
      w5.path.length - 1 = d' + 1 →
      WriterWP (do
        let noop ← deleteUpward L (d' + 1) cv (pre0 ++ [k1, cv])
        if !noop then do let _ ← fresh; pure noop else pure noop) c w5 post) :
    WriterWP (putKv (.del (pre0 ++ [k1, cv]))) c w post := by
  have hfuel : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  have hkey' : pre0 ++ [k1, cv] = (pre0 ++ [k1]) ++ [cv] := by simp
  have hvk1 : ∀ q ∈ eqVisits (wNode c.p base w) c.i k1 c.p.fuel rq,
      q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre0 ++ [k1, cv]) w.top.rootKey :=
    fromVisits_append_gen _ _ _ k1 [cv] pre0 _ rq hrq
  have hsegL : segRootR (wNode c.p base w) c.i c.p.fuel (pre0 ++ [k1]) w.top.rootKey = some L := by
    rw [segRootR_snoc, hrq]
    simp only [Option.bind_some, hL, hNL, Option.isSome_some, ↓reduceIte]
  have hvcv : ∀ q ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel L,
      q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre0 ++ [k1, cv]) w.top.rootKey := by
    rw [hkey']; exact fromVisits_append _ _ _ (pre0 ++ [k1]) cv _ L hsegL
  unfold putKv pathClear findRoot pathAdd
  wpSimplify
  generalize hw2 : ({ ({ w with path := [] } : W) with
    path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w2
  have hr02 : ReadsAs c.p base w w2 := by subst hw2; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hw2n : w2.nodes = w.nodes := by subst hw2; rfl
  refine writerWP_putSegs_walk_src c base hvc (pre0 ++ [k1, cv]) none [k1, cv] (by simp) _ pre0
    w.top.rootKey rq w2 (by rw [hr02.1, hr02.2.2.1]; exact ht) (by rw [hr02.1]; exact hrq)
    (by subst hw2; simp) ?_
  intro w2' hr2' hp2' hsrc2'
  have hr0 := ReadsAs.trans _ _ _ _ _ hr02 hr2'
  rw [putSegs.eq_3 _ _ rq k1 [cv] (by simp)]
  unfold setNode
  wpSimplify
  have ht1 : ∀ q ∈ eqVisits (wNode c.p base w2') c.i k1 c.p.fuel rq,
      w2'.taken.contains q.1 = false := by
    rw [hr0.1, hr0.2.2.1]
    exact fun q hq => ht q (hvk1 q hq)
  refine writerWP_mono (writerWP_and
    (writerWP_descendLte_path k1 c base hvc c.p.fuel rq w2' ht1 hp2')
    (writerWP_descendLte_cache k1 c base hvc c.p.fuel rq w2' ht1)) ?_
  intro q w3 ⟨⟨hr23, qn, hq, hql, hlkq3, hvisq, hgetq, hdpq⟩, ⟨hcache3, hsrc3, _⟩⟩
  rw [hr0.1] at hq hvisq hgetq hcache3
  have hr03 := ReadsAs.trans _ _ _ _ _ hr0 hr23
  rw [writerWP_getNode_known q qn c _ (by simpa using hlkq3)]
  rw [hL] at hgetq
  cases hfd : qn.searchEq c.i k1 with
  | none => rw [hfd] at hgetq; cases hgetq
  | some fd =>
    rw [hfd] at hgetq
    simp only [Option.map_some, Option.some.injEq] at hgetq
    have hfdc : fd.c = k1 := KNode.searchEq_c qn c.i k1 fd hfd
    simp only [pathAdd, writerWP_bind, writerWP_modify, writerWP_pure]
    rw [← hgetq, putSegs.eq_2]
    generalize hw4 : ({ w3 with path := w3.path ++ [(some fd.c, L)] } : W) = w4
    have hr34 : ReadsAs c.p base w3 w4 := by subst hw4; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    have hr04 := ReadsAs.trans _ _ _ _ _ hr03 hr34
    have hp4 : w4.path.getLast?.map (·.2) = some L := by subst hw4; simp
    unfold setValue
    wpSimplify
    have ht2 : ∀ q ∈ eqVisits (wNode c.p base w4) c.i cv c.p.fuel L,
        w4.taken.contains q.1 = false := by
      rw [hr04.1, hr04.2.2.1]
      exact fun q hq => ht q (hvcv q hq)
    refine writerWP_mono (writerWP_and
      (writerWP_descendLte_path cv c base hvc c.p.fuel L w4 ht2 hp4)
      (writerWP_descendLte_cache cv c base hvc c.p.fuel L w4 ht2)) ?_
    intro L' w5 ⟨⟨hr45, n', hn', _, hlk5, _, _, hdp⟩, ⟨_, hsrc5, hpre5⟩⟩
    rw [hr04.1] at hn'
    have hr05 := ReadsAs.trans _ _ _ _ _ hr04 hr45
    have hnext5 : w5.next = w.next := hr05.2.2.2.2
    have hevL : eqVisits (wNode c.p base w) c.i cv c.p.fuel L = [(L, cv)] := by
      obtain ⟨f2, hf2⟩ : ∃ f2, c.p.fuel = f2 + 1 := ⟨c.p.fuel - 1, by omega⟩
      rw [hf2]
      simp [eqVisits, hNL, hnl]
    obtain ⟨hLL, hp5⟩ : L' = L ∧ w5.path = w4.path := by
      rcases hdp with hd | ⟨pre', q', k1', qn', fd', _, _, hq', hql', _, _, _, hqv'⟩
      · exact hd
      · rw [hr04.1, hevL] at hqv'
        simp only [List.mem_singleton, Prod.mk.injEq] at hqv'
        rw [hr04.1, hqv'.1, hNL] at hq'
        cases hq'
        rw [hnl] at hql'
        cases hql'
    subst L'
    rw [hNL] at hn'
    cases hn'
    simp only [pathSize, writerWP_bind, writerWP_get, writerWP_pure]
    have hlast3 : w3.path.getLast?.map (·.2) = some q := by
      rcases hdpq with ⟨hqr, hp3⟩ | ⟨pre', q', k1', qn', fd', hp3, _, _, _, _, _, _, _⟩
      · rw [hp3, hp2', hqr]
      · rw [hp3]; simp
    have hne3 : w3.path ≠ [] := by intro he; rw [he] at hlast3; simp at hlast3
    obtain ⟨d', hd'⟩ : ∃ d', w3.path.length = d' + 1 := by
      cases h' : w3.path.length with
      | zero => exact absurd (List.eq_nil_of_length_eq_zero h') hne3
      | succ k => exact ⟨k, rfl⟩
    have hlen : w5.path.length - 1 = d' + 1 := by
      rw [hp5, ← hw4]; simp only [List.length_append, List.length_singleton]; omega
    have hpq : (w5.path[d']?).map (·.2) = some q := by
      rw [hp5, ← hw4]
      simp only
      rw [List.getElem?_append_left (by omega)]
      rw [List.getLast?_eq_getElem?, hd'] at hlast3
      simpa using hlast3
    have hpk : w5.path[d' + 1]? = some (some fd.c, L) := by
      rw [hp5, ← hw4]
      simp only
      rw [List.getElem?_append_right (by omega), hd']
      simp
    have hlq5 : w5.nodes.lookup q = some qn := by
      have h3 := hcache3 q qn hvisq hq
      have h4 : w4.nodes = w3.nodes := by rw [← hw4]
      obtain ⟨tl, htl⟩ := hpre5
      rw [← htl, List.lookup_append, h4, h3]; rfl
    have hsrcw5 : ∀ z, (w5.nodes.lookup z).isSome = true → z < w.next := by
      intro z hz
      have h4 : w4.nodes = w3.nodes := by rw [← hw4]
      rcases hsrc5 z hz with h1 | h1
      · rw [h4] at h1
        rcases hsrc3 z h1 with h2 | h2
        · rcases hsrc2' z h2 with h3 | h3
          · rw [hw2n] at h3; exact hidn z h3
          · exact hidv z h3
        · exact hidv z h2
      · exact hidv z h1
    have hk1 : (k1, L) ∈ qn.liveAt c.i := by
      have := KNode.searchEq_mem qn c.i k1 fd (hqwf q qn hvisq hq) hfd
      rw [← hgetq] at this
      exact this
    rw [hfdc] at hpk
    rw [hlen]
    have := hk q qn d' w5 hvisq hq hql hk1 (by simpa using hlk5) (by simpa using hlq5) hsrcw5 hr05
      (by simpa using hpq) (by simpa using hpk) hlen
    simpa only [writerWP_bind] using this

/-- The parts about the tree after a node s that linked L by k1 loses that
klong (and maybe others), L changed in any way: L is reached no more. -/
theorem putInvT_drop (c : Ctx) (base : View BVal) (w w' : W) (hI : PutInv c base w)
    (s L : NodeId) (sn sn' : KNode) (k1 : Nat)
    (hs : wNode c.p base w s = some sn) (hrs : ReachS (wNode c.p base w) c.i w.top.rootKey s)
    (hk1 : (k1, L) ∈ sn.liveAt c.i) (hl' : sn'.leaf = sn.leaf)
    (ht' : ∀ t, Klong.time t ∈ sn'.ks → t ≤ c.i)
    (hsub : ∀ c' z, (c', z) ∈ sn'.liveAt c.i → c' ≠ k1 ∧ (c', z) ∈ sn.liveAt c.i)
    (htk : w'.taken = w.taken) (htop : w'.top = w.top)
    (hN's : wNode c.p base w' s = some sn')
    (hother : ∀ x, x ≠ s → x ≠ L → wNode c.p base w' x = wNode c.p base w x) :
    PutInvT c base w' := by
  have hst := hI.times s sn hs
  have hT := htree_of_treeOK _ _ _ hI.tree
  have honlyL : ∀ x xn cc, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → (cc, L) ∈ xn.liveAt c.i → x = s ∧ cc = k1 :=
    fun x xn cc hx hxn hc => hT x xn cc L hx hxn hc s sn k1 hrs hs hk1
  have hsL : s ≠ L := by
    intro he; subst he
    exact hI.tree.no_self_link s k1 (reachS_tReach _ _ _ _ hrs) ⟨sn, hs, hk1⟩
  have hroot : w.top.rootKey ≠ L := by
    intro he; exact hI.rootFree' s sn k1 hrs hs (he ▸ hk1)
  have hsub' : ∀ x, ReachS (wNode c.p base w') c.i w'.top.rootKey x →
      ReachS (wNode c.p base w) c.i w.top.rootKey x ∧ x ≠ L := by
    rw [htop]
    apply reachS_closed _ _ _ (fun x => ReachS (wNode c.p base w) c.i w.top.rootKey x ∧ x ≠ L)
      ⟨ReachS.root, hroot⟩
    intro x xn cc z ⟨hx, hxL⟩ hxn hz
    by_cases hxs : x = s
    · subst hxs
      rw [hN's] at hxn
      cases hxn
      obtain ⟨hne, h2⟩ := hsub cc z hz
      refine ⟨ReachS.step x sn cc z hx hs h2, ?_⟩
      intro hzL; subst hzL; exact hne (honlyL x sn cc hx hs h2).2
    · rw [hother x hxs hxL] at hxn
      refine ⟨ReachS.step x xn cc z hx hxn hz, ?_⟩
      intro hzL; subst hzL; exact hxs (honlyL x xn cc hx hxn hz).1
  have hlive : ∀ c' z, (c', z) ∈ sn'.live → (c', z) ∈ sn.live := by
    intro c' z h
    rw [← KNode.liveAt_of_times _ c.i ht'] at h
    have := (hsub c' z h).2
    rwa [KNode.liveAt_of_times _ c.i hst] at this
  refine ⟨?_, ?_⟩
  · intro x hx; rw [htk]; exact hI.untaken x (hsub' x hx).1
  · intro q qn L' n' k1' hq hqn hql hn' hnl' hk'
    obtain ⟨hq', hqL⟩ := hsub' q hq
    by_cases hqs : q = s
    · subst hqs
      rw [hN's] at hqn
      cases hqn
      have hk'' : (k1', L') ∈ sn'.liveAt c.i := by rw [KNode.liveAt_of_times _ c.i ht']; exact hk'
      obtain ⟨hne, h2⟩ := hsub k1' L' hk''
      have hL'L : L' ≠ L := by
        intro he; subst he; exact hne (honlyL q sn k1' hq' hs h2).2
      have hL's : L' ≠ q := by
        intro he; subst he
        exact hI.tree.no_self_link L' k1' (reachS_tReach _ _ _ _ hq') ⟨sn, hs, h2⟩
      rw [hother L' hL's hL'L] at hn'
      rw [KNode.liveAt_of_times _ c.i hst] at h2
      have hold := hI.order q sn L' n' k1' hq' hs (by rw [← hl']; exact hql) hn' hnl' h2
      intro c' z hz
      exact ⟨(hold c' z hz).1, fun c'' z'' hz'' hlt => (hold c' z hz).2 c'' z'' (hlive c'' z'' hz'') hlt⟩
    · rw [hother q hqs hqL] at hqn
      have hk'' : (k1', L') ∈ qn.liveAt c.i := by
        rw [KNode.liveAt_of_times qn c.i (hI.times q qn hqn)]; exact hk'
      have hL'L : L' ≠ L := by
        intro he; subst he; exact hqs (honlyL q qn k1' hq' hqn hk'').1
      by_cases hL's : L' = s
      · subst hL's
        rw [hN's] at hn'
        cases hn'
        have hold := hI.order q qn L' sn k1' hq' hqn hql hs (by rw [← hl']; exact hnl') hk'
        exact fun c' z hz => hold c' z (hlive c' z hz)
      · rw [hother L' hL's hL'L] at hn'
        exact hI.order q qn L' n' k1' hq' hqn hql hn' hnl' hk'

theorem writerWP_getNode_frame3 (x : NodeId) (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (w : W) :
    WriterWP (getNode x) c w (fun _ v => ReadsAs c.p base w v ∧ w.nodes.IsPrefix v.nodes ∧
      v.path = w.path) := by
  have h1 := writerWP_getNode_reads x c w base hvc
  have h2 := writerWP_getNode_cache2 x c w
  have h3 : WriterWP (getNode x) c w (fun _ v => v.path = w.path) := by
    unfold getNode
    simp only [writerWP_bind, writerWP_get]
    split
    · simp only [writerWP_pure]
    · simp only [writerWP_bind, writerWP_read]
      split
      · split
        · exact writerWP_throw _ _ _ _
        · simp only [writerWP_bind, writerWP_set, writerWP_pure]
      · exact writerWP_throw _ _ _ _
  intro r v h
  exact ⟨(h1 r v h).1, (h2 r v h).1, h3 r v h⟩

/-- A fold of reads over node ids keeps what the state reads, extends its
cache and keeps its access path. -/
theorem writerWP_foldlM_frame {α β : Type} (c : Ctx) (base : View BVal) (f : β → α → M β)
    (hf : ∀ b a (w : W), WriterWP (f b a) c w (fun _ v => ReadsAs c.p base w v ∧
      w.nodes.IsPrefix v.nodes ∧ v.path = w.path)) :
    ∀ (l : List α) (b : β) (w : W), WriterWP (l.foldlM f b) c w (fun _ v =>
      ReadsAs c.p base w v ∧ w.nodes.IsPrefix v.nodes ∧ v.path = w.path) := by
  intro l
  induction l with
  | nil =>
    intro b w
    simp only [List.foldlM_nil, writerWP_pure]
    exact ⟨ReadsAs.refl _ _ _, List.prefix_refl _, trivial⟩
  | cons a l ih =>
    intro b w
    simp only [List.foldlM_cons, writerWP_bind]
    refine writerWP_mono (hf b a w) ?_
    intro b' v ⟨hr, hp, hpa⟩
    refine writerWP_mono (ih b' v) ?_
    intro _ u ⟨hr', hp', hpa'⟩
    exact ⟨ReadsAs.trans _ _ _ _ _ hr hr', hp.trans hp', hpa'.trans hpa⟩

/-- The climb from an emptied leaf L stops at its parent q, which keeps a live
klong; L existed before the transaction. Nothing changes. -/
theorem writerWP_climb_stop (d : Nat) (L q : NodeId) (pq : Option Nat) (k1 : Nat) (n qn : KNode)
    (c : Ctx) (w : W)
    (hpath : w.path[d + 1]? = some (some k1, L)) (hparent : w.path[d]? = some (pq, q))
    (hx : w.nodes.lookup L = some n) (hq : w.nodes.lookup q = some qn)
    (hfirst : n.firstTime ≠ some c.i)
    (hkeep : qn.allKeysIn (bitsUnion qn.lastBitmap (qn.bitsOf k1)) = false) :
    WriterWP (climb (d + 1)) c w (fun r v => r = d ∧ v = w) := by
  have hf : (n.firstTime == some c.i) = false := by simpa using hfirst
  unfold climb
  repeat' first
    | wpSimplify
    | simp only [pathNode, klongAt, canTakeBack, replacedBy, hpath, hparent, hkeep, hf,
        Bool.false_eq_true, Bool.false_and, ↓reduceIte]
    | rw [writerWP_getNode_known L n c w hx]
    | rw [writerWP_getNode_known q qn c w hq]
    | exact writerWP_throw _ _ _ _
    | exact ⟨rfl, rfl⟩
    | trivial
    | wpSplit
    | split

theorem writerWP_appendDeleteKlong_room_drop (base : View BVal) (x : NodeId) (depth cv : Nat)
    (n : KNode) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup x = some n) (hxt : w.taken.contains x = false)
    (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ c.i)
    (hroom : lastIsDel n.ks = false ∨ n.lastTime ≠ some c.i → n.size + 1 < c.p.M)
    (hdead1 : deadOver c.p (n.setAt (n.size - 1)
      (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))) = false)
    (hdead2 : deadOver c.p (n.add c.i (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))) = false)
    (hne : bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap) :
    WriterWP (appendDeleteKlong x depth cv) c w (fun _ w' => ∃ n' : KNode, n'.leaf = n.leaf ∧
      (∀ s, Klong.time s ∈ n'.ks → s ≤ c.i) ∧
      (∀ c' z, (c', z) ∈ n'.liveAt c.i → c' ≠ cv ∧ (c', z) ∈ n.liveAt c.i) ∧
      w'.taken = w.taken ∧ w'.top = w.top ∧
      ∀ y, wNode c.p base w' y = if y = x then some n' else wNode c.p base w y) := by
  have hwn : ∀ (n' : KNode) (w' : W), w'.nodes = upsert w.nodes x n' → w'.taken = w.taken →
      ∀ y, wNode c.p base w' y = if y = x then some n' else wNode c.p base w y := by
    intro n' w' h1 h2 y
    by_cases hy : y = x
    · subst hy; simp only [wNode, h2, hxt, Bool.false_eq_true, ↓reduceIte, h1, lookup_upsert]
    · simp only [wNode, h2, h1, lookup_upsert, hy, ↓reduceIte]
  have hsetAt : ∀ old, n.ks.getLast? = some (.del old) → ∀ c' z,
      (c', z) ∈ (n.setAt (n.size - 1) (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))).liveAt c.i →
      c' ≠ cv ∧ (c', z) ∈ n.liveAt c.i := fun old hold c' z hm =>
    liveAt_sub_of_lookup n _ c.i cv hnt (KNode.setAt_last_del_times n c.i old _ hold hnt)
      (fun c'' => n.setAt_delete_live_lookup cv c'' old hold) c' z hm
  have hadd : ∀ c' z,
      (c', z) ∈ (n.add c.i (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))).liveAt c.i →
      c' ≠ cv ∧ (c', z) ∈ n.liveAt c.i := fun c' z hm =>
    liveAt_sub_of_lookup n _ c.i cv hnt (KNode.add_times n c.i _ (fun s h => by cases h) hnt)
      (fun c'' => n.add_delete_live_lookup c.i cv c'') c' z hm
  have haddt := KNode.add_times n c.i (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))
    (fun s h => by cases h) hnt
  unfold appendDeleteKlong
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c w hlk]
  split
  · exact writerWP_throw _ _ _ _
  · generalize hU : bitsUnion n.lastBitmap (n.bitsOf cv) = U at hdead1 hdead2 hsetAt hadd haddt
    cases hno : (U == n.lastBitmap)
    · cases hgl : n.ks.getLast? with
      | none =>
        have hld : lastIsDel n.ks = false := by unfold lastIsDel; rw [hgl]
        have hroom' : n.size + 1 < c.p.M := hroom (Or.inl hld)
        simp only [hroom', hdead2, Bool.not_false, Bool.false_and, Bool.false_eq_true,
          ↓reduceIte, note, putNode, writerWP_bind, writerWP_modify, writerWP_pure]
        exact ⟨_, KNode.add_leaf _ _ _, haddt, hadd, trivial, trivial, hwn _ _ rfl rfl⟩
      | some k =>
        cases k with
        | del old =>
          cases hlt : (n.lastTime == some c.i)
          · have hlt' : n.lastTime ≠ some c.i := by simpa using hlt
            have hroom' : n.size + 1 < c.p.M := hroom (Or.inr hlt')
            simp only [hroom', hdead2, Bool.not_false, Bool.true_and, Bool.false_eq_true,
              ↓reduceIte, note, putNode, writerWP_bind, writerWP_modify, writerWP_pure]
            exact ⟨_, KNode.add_leaf _ _ _, haddt, hadd, trivial, trivial, hwn _ _ rfl rfl⟩
          · simp only [hdead1, Bool.not_false, Bool.true_and, Bool.false_eq_true,
              ↓reduceIte, note, putNode, writerWP_bind, writerWP_modify, writerWP_pure]
            exact ⟨_, KNode.setAt_leaf _ _ _, KNode.setAt_last_del_times n c.i old _ hgl hnt,
              hsetAt old hgl, trivial, trivial, hwn _ _ rfl rfl⟩
        | _ =>
          have hld : lastIsDel n.ks = false := by unfold lastIsDel; rw [hgl]
          have hroom' : n.size + 1 < c.p.M := hroom (Or.inl hld)
          simp only [hroom', hdead2, Bool.not_false, Bool.false_and, Bool.false_eq_true,
            ↓reduceIte, note, putNode, writerWP_bind, writerWP_modify, writerWP_pure]
          exact ⟨_, KNode.add_leaf _ _ _, haddt, hadd, trivial, trivial, hwn _ _ rfl rfl⟩
    · exact absurd (by simpa [hU] using hno) hne


/-- `unlink` of a cached node changes that node alone. -/
theorem writerWP_unlink_frame2 (x : NodeId) (n : KNode) (c : Ctx) (w : W)
    (hx : w.nodes.lookup x = some n) :
    WriterWP (unlink x) c w (fun _ v => v.taken = w.taken ∧ v.top = w.top ∧ v.path = w.path ∧
      v.next = w.next ∧ (∀ y, y ≠ x → v.nodes.lookup y = w.nodes.lookup y)) := by
  unfold unlink
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c w hx]
  split
  · simp only [putNode, writerWP_modify]
    refine ⟨trivial, trivial, trivial, trivial, ?_⟩
    intro y hy
    simp only [lookup_upsert, hy, ↓reduceIte]
  · simp only [writerWP_pure]
    simp

/-- The upward delete that empties a segment's tree of one leaf L, a leaf that
existed before the transaction, below the segment leaf q of the segment
before, which keeps a live klong and has room for the bitmap, the merges off,
keeps `PutInv` (the writer's tree after it given): L loses its klongs of the
transaction, q a live klong k1, and L is reached no more. -/
theorem putInv_del_up_segRoot (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (pre0 : List Nat) (k1 cv : Nat) (rq L : NodeId) (n : KNode) (w : W)
    (hI : PutInv c base w) (hw : PutBook c B top0 w) (hmerges : c.p.merges = false)
    (hrq : segRootR (wNode c.p base w) c.i c.p.fuel pre0 w.top.rootKey = some rq)
    (hL : getEqR (wNode c.p base w) c.i k1 c.p.fuel rq = some L)
    (hNL : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (hne : bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap)
    (hempty : n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = true)
    (hfirst : n.firstTime ≠ some c.i)
    (hseg : ∀ q qn, (q, k1) ∈ eqVisits (wNode c.p base w) c.i k1 c.p.fuel rq →
      wNode c.p base w q = some qn → qn.leaf = true →
      qn.allKeysIn (bitsUnion qn.lastBitmap (qn.bitsOf k1)) = false ∧
      bitsUnion qn.lastBitmap (qn.bitsOf k1) ≠ qn.lastBitmap ∧
      deadOver c.p (qn.setAt (qn.size - 1) (.del (bitsUnion qn.lastBitmap (qn.bitsOf k1)))) = false ∧
      deadOver c.p (qn.add c.i (.del (bitsUnion qn.lastBitmap (qn.bitsOf k1)))) = false ∧
      (lastIsDel qn.ks = false ∨ qn.lastTime ≠ some c.i → qn.size + 1 < c.p.M)) :
    WriterWP (putKv (.del (pre0 ++ [k1, cv]))) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey → PutInv c base w') := by
  have hvc := hB.coherent
  obtain ⟨_, _, ht, hrrq⟩ := segRoot_facts c base w hI pre0 k1 cv rq L n hrq hL hNL hnl
  apply writerWP_putInv_of_T c base B top0 _ w hB hw
  apply writerWP_del_segRoot_leaf c base hvc pre0 k1 cv rq L n w hrq ht hI.ids.1 hI.ids.2.1 hL hNL hnl
    (fun q qn _ hqn => hI.wf q qn hqn)
  intro q qn d' w5 hqv hqn hql hk1 hlk5 hlq5 hsrc5 hr5 hpq' hpk _
  obtain ⟨hkeep, hqne, hd1, hd2, hroom⟩ := hseg q qn hqv hqn hql
  obtain ⟨pq, hpq⟩ : ∃ pq, w5.path[d']? = some (pq, q) := by
    cases h' : w5.path[d']? with
    | none => rw [h'] at hpq'; cases hpq'
    | some e => rw [h'] at hpq'; simp at hpq'; exact ⟨e.1, by rw [← hpq']⟩
  have hrq' : ReachS (wNode c.p base w) c.i w.top.rootKey q :=
    eqVisits_reach _ _ _ k1 c.p.fuel rq q k1 hrrq hqv
  have hLt : w.taken.contains L = false := (wNode_cases _ _ _ _ _ hNL).1
  have hqt : w.taken.contains q = false := (wNode_cases _ _ _ _ _ hqn).1
  have hqL : q ≠ L := by
    intro he; subst he
    exact hI.tree.no_self_link q k1 (reachS_tReach _ _ _ _ hrq') ⟨qn, hqn, hk1⟩
  simp only [writerWP_bind]
  unfold deleteUpward
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w5 hlk5]
  have hnb : (bitsUnion n.lastBitmap (n.bitsOf cv) == n.lastBitmap) = false := by simpa using hne
  simp only [hnb, Bool.false_eq_true, ↓reduceIte, hempty, Bool.not_true, writerWP_bind]
  refine writerWP_mono (writerWP_climb_stop d' L q pq k1 n qn c w5 hpk hpq hlk5 hlq5 hfirst hkeep) ?_
  rintro r v ⟨rfl, rfl⟩
  simp only [show (r == r + 1) = false by simp, Bool.false_eq_true, ↓reduceIte, note,
    writerWP_bind, writerWP_modify, writerWP_get]
  refine writerWP_mono (writerWP_foldlM_frame c base _ (fun b e w => ?_) _ 0 _) ?_
  · simp only [writerWP_bind]
    refine writerWP_mono (writerWP_getNode_frame3 e.2 c base hvc w) ?_
    intro _ u h
    simp only [writerWP_pure]
    exact h
  intro seg w6 ⟨hr6, hp6, hpa6⟩
  have hlk6 : w6.nodes.lookup L = some n := by
    obtain ⟨t, ht⟩ := hp6
    rw [← ht, List.lookup_append]
    simp only at hlk5 ⊢
    rw [hlk5]; rfl
  have hlq6 : w6.nodes.lookup q = some qn := by
    obtain ⟨t, ht⟩ := hp6
    rw [← ht, List.lookup_append]
    simp only at hlq5 ⊢
    rw [hlq5]; rfl
  simp only at hpa6
  rw [show r + 1 - r = 1 by omega, show List.range 1 = [0] from rfl]
  simp only [List.forIn_cons, List.forIn_nil, writerWP_bind, pathNode, writerWP_get, hpa6,
    Nat.sub_zero, hpk, writerWP_pure]
  rw [writerWP_getNode_known L n c w6 hlk6]
  have hf : (n.firstTime == some c.i) = false := by simpa using hfirst
  simp only [hf, Bool.false_eq_true, ↓reduceIte, writerWP_bind, writerWP_modify]
  refine writerWP_mono (writerWP_unlink_frame2 L n c _ hlk6) ?_
  intro _ w7 ⟨h7t, h7top, h7p, h7n, h7l⟩
  simp only at h7t h7top h7p h7n h7l
  have hlq7 : w7.nodes.lookup q = some qn := by rw [h7l q hqL]; exact hlq6
  simp only [writerWP_pure, h7p, hpa6, hpq, klongAt, writerWP_bind, writerWP_get]
  rw [hpk]
  simp only [writerWP_pure]
  rw [writerWP_getNode_known q qn c w7 hlq7]
  refine writerWP_ghOf_cached q qn c w7 hlq7 _ (fun gh => ?_)
  simp only [hql, ↓reduceIte, writerWP_bind, writerWP_modify]
  have htk7 : w7.taken = w.taken := by rw [h7t, hr6.2.2.1]; exact hr5.2.2.1
  have htop7 : w7.top = w.top := by rw [h7top, hr6.2.1]; exact hr5.2.1
  have hW7 : ∀ x, x ≠ L → wNode c.p base w7 x = wNode c.p base w x := by
    intro x hxL
    have h1 : wNode c.p base w7 x = wNode c.p base w6 x := by
      unfold wNode; rw [h7t, h7l x hxL]
    rw [h1, hr6.1]
    exact congrFun hr5.1 x
  have hqnt := hI.times q qn hqn
  refine writerWP_mono (writerWP_appendDeleteKlong_room_drop base q r k1 qn c _ hlq7
    (by simp only; rw [htk7]; exact hqt) hqnt hroom hd1 hd2 hqne) ?_
  intro _ w9 ⟨n', hl', ht', hsub, h9t, h9top, hN9⟩
  have hdrop : PutInvT c base w9 := by
    refine putInvT_drop c base w w9 hI q L qn n' k1 hqn hrq' hk1 hl' ht' hsub
      (by rw [h9t]; exact htk7) (by rw [h9top]; exact htop7) (by rw [hN9]; simp) ?_
    intro x hxq hxL
    rw [hN9]
    simp only [hxq, ↓reduceIte]
    exact hW7 x hxL
  unfold afterDelete fresh
  simp only [writerWP_bind, writerWP_read, hmerges, Bool.false_eq_true, ↓reduceIte, writerWP_pure,
    Bool.not_false, writerWP_get, writerWP_set]
  exact hdrop

end SIS.Tree
