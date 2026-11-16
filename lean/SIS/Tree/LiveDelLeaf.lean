/-
The delete's leaf with room, for `l4` (bergdb 030-01, step 5): the bitmap leaves
the live counts but at the leaf, which keeps a live klong; the leaf is the hole
that the merges' descent at its cached segment and height finds
(`holeAtW_leaf`), so `afterDelete` is called with `LiveHoleW` at the leaf's pair
(`liveDel_room`). Its obligation, the merges' loop and root collapse from the
hole (030-01, steps 3 and 4), is a hypothesis here.

* `writerWP_deleteUpward_gh`: `writerWP_deleteUpward_full` (DelStepsFull.lean)
  with the leaf's cached pair given to the continuation;
* `liveEdgesH_leaf_shrink`: a leaf that loses live klongs but keeps one is the
  only hole;
* the reads of the key's descent after the bitmap agree with the walk's tree on
  the key's reading: its nodes are on the walk's path, which the walk cached
  (`fromVisits_reach_leaf`, `nodeAt_of_reach`).
-/
import SIS.Tree.LiveHoleLeaf
import SIS.Tree.StratumSteps
import SIS.Tree.LiveDelRoom
import SIS.Tree.HeightsFitsR
import SIS.Tree.LiveLoop

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## The leaf's pair at the call -/

theorem writerWP_ghOf_lookup (x : NodeId) (n : KNode) (c : Ctx) (w : W)
    (hn : w.nodes.lookup x = some n) (post : Nat × Nat → W → Prop)
    (hp : ∀ gh, w.gh.lookup x = some gh → post gh w) : WriterWP (ghOf x) c w post := by
  unfold ghOf
  simp only [writerWP_bind]
  rw [writerWP_getNode_known x n c w hn]
  simp only [writerWP_get]
  split
  · rename_i v hv
    simp only [writerWP_pure]
    exact hp _ hv
  · exact writerWP_throw _ _ _ _

/-- `writerWP_deleteUpward_full` with the leaf's cached segment and height given
to the continuation. -/
theorem writerWP_deleteUpward_gh (c : Ctx) (L : NodeId) (n : KNode) (d cv : Nat) (key : Key) (w3 : W)
    (hlk3 : w3.nodes.lookup L = some n)
    (hne : bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap)
    (hkeep : n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = false)
    (Q : W → Prop) (Post : W → Prop)
    (hbit : WriterWP (appendDeleteKlong L d cv) c w3 (fun _ v => Q v))
    (hcont : ∀ g h v, w3.gh.lookup L = some (g, h) → Q v →
      WriterWP (afterDelete key g h) c v (fun _ v' => Post v')) :
    WriterWP (deleteUpward L d cv key) c w3 (fun _ v => Post v) := by
  unfold deleteUpward
  wpSimplify
  rw [writerWP_getNode_known L n c _ hlk3]
  have hnb : (bitsUnion n.lastBitmap (n.bitsOf cv) == n.lastBitmap) = false := by
    simpa using hne
  simp only [hnb, Bool.false_eq_true, ↓reduceIte, hkeep, Bool.not_false]
  wpSimplify
  refine writerWP_ghOf_lookup L n c _ hlk3 _ (fun gh hgh => ?_)
  refine writerWP_mono hbit ?_
  intro _ v hv
  refine writerWP_mono (hcont gh.1 gh.2 v hgh hv) ?_
  intro _ v' hv'
  try simp only [writerWP_pure]
  exact hv'

/-! ## The leaf as the hole -/

theorem keyLookup_ne_none_of_kept (del : List Nat) (c : Nat) :
    ∀ (xs : List (Klong × Nat)) (acc : Option NodeId),
      ((∃ y i, (Klong.key c y, i) ∈ xs ∧ del.contains i = false) ∨ acc ≠ none) →
      xs.foldl (keyLookupStep del c) acc ≠ none := by
  intro xs
  induction xs with
  | nil =>
    intro acc h
    rcases h with ⟨_, _, h, _⟩ | h
    · cases h
    · exact h
  | cons q qs ih =>
    intro acc h
    simp only [List.foldl_cons]
    apply ih
    rcases h with ⟨y, i, hm, hd⟩ | h
    · rcases List.mem_cons.mp hm with he | hm
      · subst he
        right
        have hd' : i ∉ del := by simpa using hd
        simp [keyLookupStep, hd']
      · exact Or.inl ⟨y, i, hm, hd⟩
    · right
      rcases q with ⟨k, i⟩
      cases k with
      | key a y =>
        simp only [keyLookupStep]
        split
        · exact h
        · split
          · simp
          · exact h
      | time _ => exact h
      | del _ => exact h

/-- A delete that leaves its node a live klong: the node after keeps one. -/
theorem live_ne_of_keep (n n' : KNode) (cv : Nat)
    (hkeep : n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = false)
    (hl : ∀ c', n'.live.lookup c' = if c' == cv then none else n.live.lookup c') : n'.live ≠ [] := by
  unfold KNode.allKeysIn at hkeep
  obtain ⟨⟨k, i⟩, hm, hf⟩ := List.all_eq_false.mp hkeep
  cases k with
  | key c y =>
    simp only [Bool.not_eq_true] at hf
    have hc : c ≠ cv := by
      intro he
      rw [he] at hm
      have : (bitsUnion n.lastBitmap (n.bitsOf cv)).contains i = true := by
        simp only [List.contains_eq_mem, decide_eq_true_eq, mem_bitsUnion_iff]
        exact Or.inr ((n.mem_bitsOf_iff cv i).mpr ⟨y, hm⟩)
      rw [this] at hf
      cases hf
    have h1 := keyLookup_ne_none_of_kept _ c _ none (Or.inl ⟨y, i, hm, hf⟩)
    change keyLookup n.ks (bitsUnion n.lastBitmap (n.bitsOf cv)) c ≠ none at h1
    rw [keyLookup_delete_union] at h1
    have hcb : (c == cv) = false := by simp [hc]
    rw [hcb] at h1
    simp only [Bool.false_eq_true, ↓reduceIte] at h1
    intro h0
    have := hl c
    rw [h0, hcb] at this
    simp only [List.lookup, Bool.false_eq_true, ↓reduceIte] at this
    exact h1 this.symm
  | time _ => simp at hf
  | del _ => simp at hf

/-- A leaf that loses live klongs but keeps one is the only hole. -/
theorem liveEdgesH_leaf_shrink (p : Params) (N : NodeId → Option KNode) (t : Time) (r L : NodeId)
    (n n' : KNode) (h : LiveEdges p N t r) (hL : N L = some n) (hnl : n.leaf = true)
    (hn'l : n'.leaf = true) (hsub : ∀ q ∈ n'.liveAt t, q ∈ n.liveAt t) (hpos : n'.liveAt t ≠ []) :
    LiveEdgesH p (updN N L n') t r (fun y => y = L) := by
  have hsubT : ∀ x c y, TLink (updN N L n') t x c y → TLink N t x c y := by
    rintro x c y ⟨m, hm, hc⟩
    by_cases hx : x = L
    · rw [hx, updN_self] at hm
      cases hm
      rw [hx]
      exact ⟨n, hL, hsub _ hc⟩
    · rw [updN_ne _ _ _ _ hx] at hm
      exact ⟨m, hm, hc⟩
  refine ⟨fun rn hrn => ⟨fun hE => ?_, fun hnr hl => ?_⟩,
    fun u un c y yn hu hun hc hyn => ⟨fun hyL => ?_, fun hyL => ?_⟩⟩
  · by_cases hr : r = L
    · rw [hr, updN_self] at hrn
      cases hrn
      exact hn'l
    · rw [updN_ne _ _ _ _ hr] at hrn
      exact (h.1 rn hrn).1 hE
  · rw [updN_ne _ _ _ _ hnr] at hrn
    exact (h.1 rn hrn).2 hl
  · rw [updN_ne _ _ _ _ hyL] at hyn
    have hu0 := tReach_of_sublinks N (updN N L n') t r hsubT u hu
    by_cases huL : u = L
    · rw [huL, updN_self] at hun
      cases hun
      rw [huL] at hu0
      exact childOK_grow p t n n' yn yn (h.2 L n c y yn hu0 hL (hsub _ hc) hyn) (by rw [hn'l, hnl]) rfl
        (Nat.le_refl _)
    · rw [updN_ne _ _ _ _ huL] at hun
      exact h.2 u un c y yn hu0 hun hc hyn
  · rw [hyL, updN_self] at hyn
    cases hyn
    exact hpos

/-- The hole that the merges' descent finds: `LiveHoleW`. -/
theorem liveHoleW_of_hole (key : Key) (g h : Nat) (c : Ctx) (base : View BVal) (v : W) (x : NodeId)
    (hE : LiveEdgesH c.p (wNode c.p base v) c.i v.top.rootKey (fun y => y = x))
    (hx : HoleAtW key g h c v x) : LiveHoleW key g h c base v :=
  liveEdgesH_mono c.p _ c.i _ (fun y => y = x) _ (fun y hy => hy ▸ hx)
    (fun u un cc y yn hu hun hcc hyn _ hyx => ((hE.2 u un cc y yn hu hun hcc hyn).1 hyx).1) hE

theorem keyWf_init_long : ∀ (pre : List Nat) (cv : Nat), keyWf (pre ++ [cv]) = true →
    ∀ c ∈ pre, segLen c = 7 := by
  intro pre
  induction pre with
  | nil => intro _ _ c hc; cases hc
  | cons a rest ih =>
    intro cv hk c hc
    have hne : rest ++ [cv] ≠ [] := by simp
    obtain ⟨d, rest', he⟩ : ∃ d rest', rest ++ [cv] = d :: rest' := by
      cases h' : rest ++ [cv] with
      | nil => exact absurd h' hne
      | cons d rest' => exact ⟨d, rest', rfl⟩
    rw [List.cons_append, he] at hk
    simp only [keyWf, Bool.and_eq_true, beq_iff_eq] at hk
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hk.1.2
    · exact ih cv (by rw [he]; exact hk.2) c hc

/-! ## The heights' walk to the leaf, with no heights' bound -/

/-- `HtJ` (HeightsFitsR.lean) without the heights' bound: the books, the heights'
walk, a path not taken back, well-formed klongs. -/
structure HtJ0 (c : Ctx) (H : NodeId → Nat → Prop) (B : NodeId) (v : W) : Prop where
  book : Book B c v
  inv : HtInv H B c v
  free : PathFreeTo v v.path.length
  wf : WriterKlongsWf v

theorem htJ0_descendLte {H : NodeId → Nat → Prop} {B : NodeId} {c : Ctx} (hvo : ViewHtOK H B c)
    (hkw : ViewKlongsWf c.p c.view) (s f : Nat) (x : NodeId) (v : W) (hJ : HtJ0 c H B v)
    (hx : KdPathLast v x) : WriterWP (descendLte s f x) c v (fun _ v' => HtJ0 c H B v') := by
  refine writerWP_mono (writerWP_and
    (ht_descendLte B s f x c v hvo hJ.book hJ.inv hJ.free (Or.inl hx))
    (klongsWf_descendLte s f x c v hkw hJ.wf)) ?_
  rintro _ v' ⟨⟨hb', hi', _, -, -, hpf'⟩, hwf'⟩
  exact ⟨hb', hi', hpf', hwf'⟩

theorem htJ0_pathAdd {H : NodeId → Nat → Prop} {B : NodeId} {c : Ctx} (hvo : ViewHtOK H B c)
    (s : Nat) (fd : Found) (L : NodeId) (n : KNode)
    (v : W) (hJ : HtJ0 c H B v) (hL : KdPathLast v L) (hlk : v.nodes.lookup L = some n)
    (hleaf : n.leaf = true) (hfd : n.searchEq c.i s = some fd) :
    HtJ0 c H B { v with path := v.path ++ [(some fd.c, fd.y)] } := by
  obtain ⟨a, ha⟩ := hL
  obtain ⟨g, h, hm⟩ := kd_tag_of_lookup hJ.book hlk
  have h0 : h = 0 := kd_h0 hJ.book hlk hm hleaf
  subst h0
  have hLf : v.taken.contains L = false :=
    hJ.free _ a L (by have := (List.getElem?_eq_some_iff.mp ha).1; omega) ha
  have hN := ht_cache_at hlk hJ.inv hm hLf (HtLe.refl _)
  have hlive := ht_searchEq_live (writerKlongsWf_lookup v hJ.wf L n hlk) hN.3 hfd
  have hpa := ht_pathAdd B fd.c fd.y c v hvo hJ.book hJ.inv a L n (ht_getLast_of ha) hlk s hlive hLf
  simp only [pathAdd, writerWP_modify] at hpa
  obtain ⟨hb', hi', -, -, -, hyf⟩ := hpa
  exact ⟨hb', hi', PathFreeTo.append hJ.free _ rfl rfl hyf, hJ.wf⟩

theorem htJ0_start {H : NodeId → Nat → Prop} {B : NodeId} {c : Ctx} (hvo : ViewHtOK H B c) (w : W)
    (hb : Book B c w) (hi : HtInv H B c w) (hwf : WriterKlongsWf w) :
    HtJ0 c H B ({ ({ w with path := [] } : W) with
      path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) := by
  have h1 := ht_pathClear B c w hvo hb hi
  simp only [pathClear, writerWP_modify] at h1
  have h2 := ht_findRoot B c { w with path := [] } hvo h1.1 h1.2.1 rfl
  simp only [findRoot, pathAdd, writerWP_bind, writerWP_get, writerWP_modify, writerWP_pure] at h2
  obtain ⟨hb2, hi2, -, -, -, hpf2⟩ := h2
  exact ⟨hb2, hi2, hpf2, hwf⟩

/-! ## The leaf with room -/

set_option maxHeartbeats 3200000 in
/-- The leaf with room (bergdb 030-01, step 5): a delete whose leaf keeps a live
klong and has room for the bitmap calls `afterDelete` at the leaf's cached pair
from a state with the stratum's tree facts (`DelInvJT`) and the live counts but
at the leaf, which the merges' descent there finds (`LiveHoleW`). So it keeps any
Q that `afterDelete` reaches from such a state and `fresh` keeps. -/
theorem liveDel_room (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P) :
    ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
      lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
      topOf p (ctxOf p ts).view z = .ok top →
      ∀ pre op post, tx.ops = pre ++ op :: post →
      ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      SJ0 p ts tx w → TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w →
      ∀ key, op = .del key → DelRoomM (ctxOf p ts) (viewOf (treeRun p ts)) w op →
      ∀ Q : W → Prop, (∀ v, Q v → WriterWP fresh (ctxOf p ts) v (fun _ v' => Q v')) →
      (∀ g v, DelInvJT (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts))
          tx.base tx.base v → PutBook (ctxOf p ts) tx.base top v →
        HtInv (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) v →
        LiveHoleW key g 0 (ctxOf p ts) (viewOf (treeRun p ts)) v →
        WriterWP (afterDelete key g 0) (ctxOf p ts) v (fun _ v' => Q v')) →
      WriterWP (putKv op) (ctxOf p ts) w (fun _ w' => Q w') := by
  intro ts tx hw hr z top _ htop ops op post hops r w hpre hS hJ key hop hPc Q hfresh hA
  obtain ⟨pre, cv, L0, n0, hop', _, hK, hne0, hkeep0, hroom0⟩ := hPc
  subst hop'
  cases hop
  have hI : PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w := hS.1.1.1.1.1
  have hRO : RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey := hS.1.1.2
  have hSB : tx.base ≤ w.next := hS.1.1.1.2
  have hLC0 : LiveCounts p (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey := hS.2.2
  have hkey : keyWf (pre ++ [cv]) = true := within_op_keyWf p ts tx hw ops _ post hops
  obtain ⟨rk, hrk, hn0⟩ := keyLeaf_rk hK
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  have hbook := putBook_reached p ts tx hw (hRL _ _ hr) z top htop ops r w hpre
  have hICE := innerChildren_reachedR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
    (fun x hx => hI.untaken x (tReach_reachS _ _ _ _ hx))
  have hLV := leafVals_all hS.1.1.1.1.2 hkey hrk
  obtain ⟨hv, hk, hb0, hi0⟩ := kd_contextR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
  have hJ0 : KdJ (ctxOf p ts) tx.base top (kindOracleOf p (treeRun p ts)) tx.base w := ⟨hbook, hb0, hi0⟩
  obtain ⟨hvo, hkw, _, _, hbw, hiw, hwfw0⟩ := hS.2.1
  have hpos : 0 < (ctxOf p ts).i := by simp [ctxOf]
  refine writerWP_del_toLeafMKH (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w
    (fun v => KdJ (ctxOf p ts) tx.base top (kindOracleOf p (treeRun p ts)) tx.base v ∧
      HtJ0 (ctxOf p ts) (htOracleOf p (treeRun p ts)) tx.base v)
    (fun s f x v hJ hx => writerWP_and (kdJ_descendLte _ _ tx.base top hB _ tx.base hv hk s f x v hJ.1 hx)
      (htJ0_descendLte hvo hkw s f x v hJ.2 hx))
    (fun s fd L n v hJ hL hlk hleaf hfd =>
      ⟨kdJ_pathAdd _ _ tx.base top hB _ tx.base hv fd.c fd.y L n v hJ.1 hL hlk
        (kd_searchEq_mem n _ s fd hfd), htJ0_pathAdd hvo s fd L n v hJ.2 hL hlk hleaf hfd⟩)
    ⟨kdJ_start _ _ tx.base top hB _ tx.base hv w hJ0, htJ0_start hvo w hbw hiw hwfw0⟩
    hrk (hI.pathUntaken _) hI.wf _ hfresh ?_
  intro L n P w3 hL hn hnl hr03 hJ3h hlk3 hp3' hlinkP hXD hlkX
  have hJ3 := hJ3h.1
  have hH3 := hJ3h.2
  obtain ⟨g0, h0, hm0⟩ := kd_tag_of_lookup hH3.book hlk3
  obtain ⟨hwf, htimes, hne, hkeep, hroomD⟩ := keyLeaf_all hK hrk
    (fun m => klongsWf m.ks = true ∧ (∀ s, Klong.time s ∈ m.ks → s ≤ (ctxOf p ts).i) ∧
      bitsUnion m.lastBitmap (m.bitsOf cv) ≠ m.lastBitmap ∧
      m.allKeysIn (bitsUnion m.lastBitmap (m.bitsOf cv)) = false ∧ DelRoom (ctxOf p ts) cv m)
    ⟨hI.wf L0 n0 hn0, hI.times L0 n0 hn0, hne0, hkeep0, hroom0⟩ L n hL hn hnl
  have hLt : w.taken.contains L = false :=
    hI.pathUntaken _ (L, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hL)
  have h3t : w3.taken.contains L = false := by rw [hr03.2.2.1]; exact hLt
  obtain ⟨a, hpx⟩ := path_last_of_toLeaf w w3 P L hp3' hXD
  have hJ23 : TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w3 := takeJ2_of_readsAs _ _ _ w w3 hJ hr03
  refine writerWP_deleteUpward_gh (ctxOf p ts) L n P.length cv (pre ++ [cv]) w3 hlk3 hne hkeep
    (fun v => DelInvJT (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base tx.base v ∧
      v.taken = w3.taken ∧ v.top = w3.top ∧ KdLe w3 v ∧ PutBook (ctxOf p ts) tx.base top v ∧
      HtInv (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) v ∧
      ∃ n', v.nodes = upsert w3.nodes L n' ∧ n'.leaf = n.leaf ∧ klongsWf n'.ks = true ∧
        (∀ s, Klong.time s ∈ n'.ks → s ≤ (ctxOf p ts).i) ∧
        (∀ c', n'.live.lookup c' = if c' == cv then none else n.live.lookup c'))
    _ ?_ ?_
  · refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and
      (writerWP_appendDeleteKlong_room_exactD L _ cv n _ _ hlk3 htimes hwf hne hroomD)
      (putBook_appendDeleteKlong L _ cv _ _ tx.base top hB _ hJ3.1))
      (kd_appendDeleteKlong _ tx.base L P.length cv _ w3 hv hk hJ3.2.1 hJ3.2.2 a hpx))
      (ht_appendDeleteKlong tx.base L P.length cv _ w3 hvo hpos hH3.book hH3.inv g0 h0 hm0 a hpx
        (hH3.free.mono (by rw [hp3']; simp)))) ?_
    rintro _ v ⟨⟨⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, hbv⟩, hkv⟩, hhv⟩
    obtain ⟨a1, a2, a3, a4⟩ := delInvFT_after_bitmap (ctxOf p ts) _ tx.base top hB w w3 v cv L n hI hRO hICE
      hn hnl hr03 hLt h1 h2 h3 h7 hbv
    refine ⟨⟨⟨a1, a2, a3, a4, ⟨tx.base, top, hB, hbv⟩, hkv.1, hkv.2.1⟩, ?_, ?_⟩, h1, h2, hkv.2.2.1, hbv,
      hhv.2.1, ?_⟩
    · exact takeJ2_after_bitmap (ctxOf p ts) _ tx.base w3 v cv L n (by simp [ctxOf]) hJ23 hlk3
        (by rw [hr03.2.2.1]; exact hLt) (hI.times L n hn)
        (by rw [hr03.1, hr03.2.1]; exact keyLeaf_reached hI hrk L hL)
        (fun y hy => by rw [hr03.1]; exact (hLV L n hL hn hnl y hy).1)
        (fun y hy => by rw [hr03.2.2.2.1]; exact (hLV L n hL hn hnl y hy).2) h1 h2 h3 h7
    · rw [h5, hr03.2.2.2.2]; exact hSB
    · obtain ⟨n', e1, e2, e3, e4, e5, _⟩ := h7
      exact ⟨n', e1, e2, e3, e4, e5⟩
  · intro g h v hgh ⟨hD, hvt, hvtop, hkle, hpbv, hhiv, n', hnodes, hleafeq, hwf', htimes', hlive'⟩
    have hh0 : h = 0 := kd_h0 hH3.book hlk3 (bk_mem_of_lookup _ _ _ hgh) hnl
    subst hh0
    apply hA g v hD hpbv hhiv
    -- the tree after the bitmap: the leaf changed alone
    have hN : wNode p (viewOf (treeRun p ts)) v = updN (wNode p (viewOf (treeRun p ts)) w) L n' := by
      have e3 : wNode p (viewOf (treeRun p ts)) w3 = wNode p (viewOf (treeRun p ts)) w := hr03.1
      rw [wNode_upsert_updN p _ w3 v L n' hnodes hvt h3t, e3]
    have hvtop' : v.top = w.top := hvtop.trans hr03.2.1
    have hn'l : n'.leaf = true := by rw [hleafeq]; exact hnl
    obtain ⟨hsubl, _⟩ := live_shrink n n' cv hlive'
    have e1 : n.liveAt (ts.length + 1) = n.live := KNode.liveAt_of_times n _ htimes
    have e2 : n'.liveAt (ts.length + 1) = n'.live := KNode.liveAt_of_times n' _ htimes'
    have hsub : ∀ q ∈ n'.liveAt (ts.length + 1), q ∈ n.liveAt (ts.length + 1) := by
      rw [e1, e2]; exact hsubl
    have hpos : n'.liveAt (ts.length + 1) ≠ [] := by
      rw [e2]; exact live_ne_of_keep n n' cv hkeep hlive'
    have hE : LiveEdgesH p (wNode p (viewOf (treeRun p ts)) v) (ts.length + 1) v.top.rootKey
        (fun y => y = L) := by
      rw [hN, hvtop']
      exact liveEdgesH_leaf_shrink p _ _ _ L n n' (edges_of_liveCounts p _ _ _ hLC0) hn hnl hn'l hsub hpos
    refine liveHoleW_of_hole (pre ++ [cv]) g 0 (ctxOf p ts) _ v L hE ?_
    -- the merges' descent at the leaf's pair finds the leaf
    have hbv : Book tx.base (ctxOf p ts) v := hD.1.2.2.2.2.2.1
    have hkv : KdInv (kindOracleOf p (treeRun p ts)) tx.base v := hD.1.2.2.2.2.2.2
    have hs := segRd_of _ tx.base (ctxOf p ts) v hbv hkv hk
    have hlkv : v.nodes.lookup L = some n' := by rw [hnodes, lookup_upsert]; simp
    -- the reads after the bitmap agree with the walk's tree on the key's reading
    have hwfw : ∀ x m, wNode p (viewOf (treeRun p ts)) w x = some m → klongsWf m.ks = true :=
      fun x m hm => hI.wf x m hm
    have hag2 : ∀ q ∈ fromVisits (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) p.fuel (pre ++ [cv])
        w.top.rootKey, q.1 ≠ L → ∃ m, wNode p (viewOf (treeRun p ts)) w q.1 = some m ∧
        rdN (ctxOf p ts) v q.1 = some m := by
      intro q hq hqL
      obtain ⟨k, hk⟩ := fromVisits_reach_leaf _ _ _ cv L n hn hnl hwfw pre _ rk hrk hL q hq
      have hR : TReach (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey q.1 :=
        reachS_tReach _ _ _ _ (fromVisits_reach _ _ _ _ (fun x xn _ hx => hwfw x xn hx) _ _ q.1 q.2
          ReachS.root hq)
      obtain ⟨hkj, hqj⟩ := nodeAt_of_reach _ _ _ hI.tree P hlinkP q.1 L k hk hR P.length
        (Nat.le_refl _) hXD.symm
      have hk0 : k ≠ 0 := by
        intro h0
        rw [h0, Nat.sub_zero, hXD] at hqj
        exact hqL hqj
      obtain ⟨_, m, _, hm0, _⟩ := LinkedFrom.get _ _ _ P hlinkP (P.length - k) (by omega)
      have hm : wNode p (viewOf (treeRun p ts)) w q.1 = some m := by rw [hqj]; exact hm0
      have hl3 : w3.nodes.lookup q.1 = some ((wNode p (viewOf (treeRun p ts)) w q.1).getD n) := by
        have := hlkX (P.length - k) (by omega)
        rw [← hqj] at this
        exact this
      rw [hm] at hl3
      have hl4 : v.nodes.lookup q.1 = some m := by
        rw [hnodes, lookup_upsert]
        simp only [hqL, ↓reduceIte]
        exact hl3
      exact ⟨m, hm, rdN_of_lookup _ v _ m hl4⟩
    have hag : ∀ q ∈ fromVisits (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) p.fuel (pre ++ [cv])
        w.top.rootKey, ∀ m, wNode p (viewOf (treeRun p ts)) w q.1 = some m → q.1 ≠ L →
        rdN (ctxOf p ts) v q.1 = some m := by
      intro q hq m hm hqL
      obtain ⟨m', hm', hr'⟩ := hag2 q hq hqL
      rw [hm] at hm'
      cases hm'
      exact hr'
    have hsearch : ∀ c', c' ≠ cv →
        (n.searchEq (ts.length + 1) c').map (·.y) = (n'.searchEq (ts.length + 1) c').map (·.y) := by
      intro c' hc'
      rw [KNode.searchEq_live n (ts.length + 1) hwf htimes, KNode.searchEq_live n' (ts.length + 1) hwf' htimes',
        hlive' c']
      have : (c' == cv) = false := by simp [hc']
      rw [this]
      rfl
    have hdsr : ∃ P', pre.foldl (dsrStep (rdN (ctxOf p ts) v) (ctxOf p ts).i (ctxOf p ts).p.fuel)
        (some (v.top.rootKey, [(none, v.top.rootKey)])) = some (rk, P') := by
      rw [hvtop']
      refine dsrFold_of_segRootR (wNode p (viewOf (treeRun p ts)) w) (rdN (ctxOf p ts) v) _ _ cv pre
        w.top.rootKey _ rk ?_ (keyWf_last_notin pre cv hkey) hrk
      intro q hq hq2
      by_cases hqL : q.1 = L
      · refine Or.inr ⟨n, n', by rw [hqL]; exact hn, by rw [hqL]; exact rdN_of_lookup _ v _ n' hlkv,
          hnl, hn'l, ?_⟩
        exact hsearch q.2 hq2
      · obtain ⟨m, hm, hr'⟩ := hag2 q hq hqL
        exact Or.inl (by rw [hm, hr'])
    have hlte : ∃ ext, lteP (rdN (ctxOf p ts) v) (ctxOf p ts).i cv (ctxOf p ts).p.fuel rk = some (L, ext) :=
      lteP_of_eqVisits (wNode p (viewOf (treeRun p ts)) w) (rdN (ctxOf p ts) v) _ cv L
        ⟨n', rdN_of_lookup _ v _ n' hlkv, hn'l⟩ _ rk hL
        (fun q hq m hm hqL => hag q (fromVisits_append _ _ _ pre cv _ rk hrk q hq) m hm hqL)
    have hgL : rdG (ctxOf p ts) v L = some (g, 0) := by
      rw [rdG_of_lookup _ v L n' hlkv]
      exact lookup_of_mem_nodup _ hbv.nodup L (g, 0) (hkle.1.2 _ (bk_mem_of_lookup _ _ _ hgh))
    exact holeAtW_leaf (ctxOf p ts) v pre cv rk L g 0 hs (keyWf_init_long pre cv hkey) hdsr hlte hgL

/-- The leaf with room keeps the live counts (bergdb 030-01, steps 5 and 3): with
the merges' loop and root collapse from the hole (`writerWP_afterDelete_live`,
LiveLoop.lean), given its live merge and root collapse (`MergeLiveOK`,
`CollapseLiveOK`, its open obligations). -/
theorem liveDel_room_live (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove) (hcap : 1 ≤ p.mergeMax)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P)
    (hML : ∀ ts (tx : Tx), MergeLiveOK (ctxOf p ts) (viewOf (treeRun p ts)) tx.base
      (htOracleOf p (treeRun p ts)))
    (hCL : ∀ ts (tx : Tx), CollapseLiveOK (ctxOf p ts) (viewOf (treeRun p ts)) tx.base) :
    ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
      lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
      topOf p (ctxOf p ts).view z = .ok top →
      ∀ pre op post, tx.ops = pre ++ op :: post →
      ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      SJ0 p ts tx w → TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w →
      ∀ key, op = .del key → DelRoomM (ctxOf p ts) (viewOf (treeRun p ts)) w op →
      WriterWP (putKv op) (ctxOf p ts) w (fun _ w' =>
        LiveEdges p (wNode p (viewOf (treeRun p ts)) w') (ts.length + 1) w'.top.rootKey) := by
  intro ts tx hw hr z top hz htop pre op post hops r w hpre hS hJ key hop hPc
  have hm : (ctxOf p ts).p.merges = true := by
    obtain ⟨_, _, _, _, _, hm, _⟩ := hPc
    exact hm
  obtain ⟨hv, hk, _, _⟩ := kd_contextR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top pre (op :: post) hops r w hpre
  have hICEk : ICEFromKinds (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base :=
    fun v hb hi hun => innerChildren_of_kinds p (treeRun p ts) tx.base (ctxOf p ts) v rfl (hRK _ _ hr)
      (hRP _ _ hr) hb hi.cache hun
  obtain ⟨hvo, hkw, _⟩ := hS.2.1
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  refine liveDel_room p R hM hRL hRP hRK ts tx hw hr z top hz htop pre op post hops r w hpre hS hJ key hop hPc
    _ (fun v hv => by
      unfold fresh
      simp only [writerWP_bind, writerWP_get, writerWP_set, writerWP_pure]
      exact hv) ?_
  intro g v hD hpb hhi hLH
  exact writerWP_afterDelete_live key g (ctxOf p ts) _ (viewCoherent_ctxOf p ts) hm _ tx.base hv hk hICEk
    hsa2 hcap (by simp [ctxOf]) hvo hkw top hB (hML ts tx) (hCL ts tx) v
    (delInvJAE_of_T _ _ _ _ _ v hD) hpb hhi hLH

end SIS.Tree
