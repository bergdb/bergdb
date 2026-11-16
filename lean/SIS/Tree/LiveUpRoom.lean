/-
The upward delete with room above its leaf, for `l4` (bergdb 030-01, step 6): the
delete calls `afterDelete` at the stop node, a segment leaf (`lebStop_false`), at
its cached pair (g, 0), from a state with the stratum's tree facts, the books and
the live counts but at the stop node, which the merges' descent there finds
(`liveEdgesH_up`, `holeAtW_stop`); so it keeps any Q that `afterDelete` reaches
from such a state with the heights' walk (`writerWP_del_upRoomLive`). The heights
at that call are a hypothesis: an invariant Ju of the upward delete's steps that
gives `HtInv` (030-01's R2, the heights: over `putKv` the take-back keeps the
heights only with the checked copy's checks, `ht_takeBackChk`).
-/
import SIS.Tree.LiveUpHole
import SIS.Tree.LiveUpWalk

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## The kinds' walk with the books' segments kept -/

/-- `KdJP` and the segments and heights of the walk's end G kept. -/
def KdJG (c : Ctx) (B : NodeId) (top0 : Top) (KO : KindOracle) (BK : NodeId)
    (p0 : List (Option Nat × NodeId)) (G : List (NodeId × Nat × Nat)) (v : W) : Prop :=
  KdJP c B top0 KO BK p0 v ∧ ∀ e ∈ G, e ∈ v.gh

theorem kdJG_takeBack (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top) (hB : PutBase c base B)
    (KO : KindOracle) (BK : NodeId) (hv : ViewIdsBelow BK c.view) (hk : ViewKinds KO BK c)
    (p0 : List (Option Nat × NodeId)) (G : List (NodeId × Nat × Nat)) (x q : NodeId) (k : Nat) (v : W)
    (hJ : KdJG c B top0 KO BK p0 G v) (hx : ∃ xn, v.nodes.lookup x = some xn) :
    WriterWP (takeBack x q k) c v (fun _ v' => KdJG c B top0 KO BK p0 G v') := by
  obtain ⟨xn, hl⟩ := hx
  obtain ⟨g, h, hgh⟩ := kd_tag_of_lookup hJ.1.1.2.1 hl
  refine writerWP_mono (writerWP_and (kdJP_takeBack c base B top0 hB KO BK hv hk p0 x q k v hJ.1 ⟨xn, hl⟩)
    (kd_takeBack KO BK x q k c v hv hk hJ.1.1.2.1 hJ.1.1.2.2 g h hgh)) ?_
  rintro _ v' ⟨h1, _, _, hle, _⟩
  exact ⟨h1, fun e he => hle.1.2 e (hJ.2 e he)⟩

theorem kdJG_unlink (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top) (hB : PutBase c base B)
    (KO : KindOracle) (BK : NodeId) (hv : ViewIdsBelow BK c.view) (hk : ViewKinds KO BK c)
    (p0 : List (Option Nat × NodeId)) (G : List (NodeId × Nat × Nat)) (x : NodeId) (v : W)
    (hJ : KdJG c B top0 KO BK p0 G v) :
    WriterWP (unlink x) c v (fun _ v' => KdJG c B top0 KO BK p0 G v') := by
  refine writerWP_mono (writerWP_and (kdJP_unlink c base B top0 hB KO BK hv hk p0 x v hJ.1)
    (kd_unlink KO BK x c v hv hk hJ.1.1.2.1 hJ.1.1.2.2)) ?_
  rintro _ v' ⟨h1, _, _, hle, _⟩
  exact ⟨h1, fun e he => hle.1.2 e (hJ.2 e he)⟩

theorem kdJG_appendDeleteKlong (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (KO : KindOracle) (BK : NodeId) (hv : ViewIdsBelow BK c.view)
    (hk : ViewKinds KO BK c) (p0 : List (Option Nat × NodeId)) (G : List (NodeId × Nat × Nat))
    (x : NodeId) (d k : Nat) (v : W)
    (hJ : KdJG c B top0 KO BK p0 G v) (hx : (p0[d]?).map (·.2) = some x) :
    WriterWP (appendDeleteKlong x d k) c v (fun _ v' => KdJG c B top0 KO BK p0 G v') := by
  obtain ⟨a, ha⟩ : ∃ a, v.path[d]? = some (a, x) := by
    rw [hJ.1.2]
    cases he : p0[d]? with
    | none => rw [he] at hx; cases hx
    | some e =>
      rw [he] at hx
      simp only [Option.map_some, Option.some.injEq] at hx
      exact ⟨e.1, by rw [← hx]⟩
  refine writerWP_mono (writerWP_and (kdJP_appendDeleteKlong c base B top0 hB KO BK hv hk p0 x d k v hJ.1 hx)
    (kd_appendDeleteKlong KO BK x d k c v hv hk hJ.1.1.2.1 hJ.1.1.2.2 a ha)) ?_
  rintro _ v' ⟨h1, _, _, hle, _⟩
  exact ⟨h1, fun e he => hle.1.2 e (hJ.2 e he)⟩

theorem kdJG_emptyKeyNext (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (KO : KindOracle) (BK : NodeId) (hv : ViewIdsBelow BK c.view)
    (hk : ViewKinds KO BK c) (p0 : List (Option Nat × NodeId)) (G : List (NodeId × Nat × Nat))
    (x : NodeId) (d : Nat) (v : W) (xn : KNode)
    (hJ : KdJG c B top0 KO BK p0 G v) (hx : (p0[d]?).map (·.2) = some x)
    (hl : v.nodes.lookup x = some xn) (hxl : xn.leaf = false) :
    WriterWP (emptyKeyNext x d) c v (fun _ v' => KdJG c B top0 KO BK p0 G v') := by
  obtain ⟨a, ha⟩ : ∃ a, v.path[d]? = some (a, x) := by
    rw [hJ.1.2]
    cases he : p0[d]? with
    | none => rw [he] at hx; cases hx
    | some e =>
      rw [he] at hx
      simp only [Option.map_some, Option.some.injEq] at hx
      exact ⟨e.1, by rw [← hx]⟩
  obtain ⟨g, h, hgh⟩ := kd_tag_of_lookup hJ.1.1.2.1 hl
  have hlf := kd_leaf hJ.1.1.2.1 hl hgh
  have hh : h ≠ 0 := by intro h0; rw [h0] at hlf; rw [hxl] at hlf; simp at hlf
  refine writerWP_mono (writerWP_and (kdJP_emptyKeyNext c base B top0 hB KO BK hv hk p0 x d v xn hJ.1 hx hl hxl)
    (kd_emptyKeyNext KO BK x d c v hv hk hJ.1.1.2.1 hJ.1.1.2.2 a ha g h hgh hh)) ?_
  rintro _ v' ⟨h1, _, _, hle, _⟩
  exact ⟨h1, fun e he => hle.1.2 e (hJ.2 e he)⟩

/-- A node whose every key klong a delete of compare value k does not remove has a
live klong of another compare value. -/
theorem exists_live_of_keep (n : KNode) (k : Nat)
    (hkeep : n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf k)) = false) :
    ∃ c z, c ≠ k ∧ (c, z) ∈ n.live := by
  unfold KNode.allKeysIn at hkeep
  obtain ⟨⟨kl, i⟩, hm, hf⟩ := List.all_eq_false.mp hkeep
  cases kl with
  | key c y =>
    simp only [Bool.not_eq_true] at hf
    have hc : c ≠ k := by
      intro he
      rw [he] at hm
      have : (bitsUnion n.lastBitmap (n.bitsOf k)).contains i = true := by
        simp only [List.contains_eq_mem, decide_eq_true_eq, mem_bitsUnion_iff]
        exact Or.inr ((n.mem_bitsOf_iff k i).mpr ⟨y, hm⟩)
      rw [this] at hf
      cases hf
    have h1 := keyLookup_ne_none_of_kept _ c _ none (Or.inl ⟨y, i, hm, hf⟩)
    change keyLookup n.ks (bitsUnion n.lastBitmap (n.bitsOf k)) c ≠ none at h1
    rw [keyLookup_delete_union] at h1
    have hcb : (c == k) = false := by simp [hc]
    rw [hcb] at h1
    simp only [Bool.false_eq_true, ↓reduceIte] at h1
    cases h2 : n.live.lookup c with
    | none => exact absurd h2 h1
    | some z => exact ⟨c, z, hc, bk_mem_of_lookup _ _ _ h2⟩
  | time _ => simp at hf
  | del _ => simp at hf

/-! ## The upward delete with room -/

set_option maxHeartbeats 6400000 in
/-- The upward delete with room above its leaf, the live counts at the start
(bergdb 030-01, step 6): `afterDelete` at the stop node's cached pair (g, 0) from
the hole there. -/
theorem writerWP_del_upRoomLive (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv : Nat) (rk : NodeId) (w : W) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (hbook : PutBook c B top0 w)
    (KO : KindOracle) (BK : NodeId) (hvB : ViewIdsBelow BK c.view) (hk : ViewKinds KO BK c)
    (hb0 : Book BK c w) (hi0 : KdInv KO BK w)
    (hI : PutInv c base w) (hRO : RangeOrder (wNode c.p base w) c.i w.top.rootKey)
    (hICE : InnerChildrenExist (wNode c.p base w) c.i w.top.rootKey)
    (hkey : keyWf (pre ++ [cv]) = true)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hleafC : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
      n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = true ∧ UpRoom c base w L n)
    (hm : c.p.merges = true) (hpos : 0 < c.i)
    (hJ2 : TakeJ2 c base B w) (hMF : ∀ x o, w.madeFor.lookup x = some o → o < B)
    (hLV : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true → ∀ y, (cv, y) ∈ n.liveAt c.i →
      wNode c.p base w y = none)
    (hLC : LiveCounts c.p (wNode c.p base w) c.i w.top.rootKey)
    {H : NodeId → Nat → Prop} (hvo : ViewHtOK H BK c) (hkw : ViewKlongsWf c.p c.view)
    (hHi : HtInv H BK c w) (hHwf : WriterKlongsWf w)
    (Ju : W → Prop) (hJu0 : ∀ v, HtJ0 c H BK v → Ju v)
    (hJuNote : ∀ (s : String) v, Ju v → Ju { v with trail := s :: v.trail })
    (hJuTake : ∀ x q k v, Ju v → WriterWP (takeBack x q k) c v (fun _ v' => Ju v'))
    (hJuUnlink : ∀ x v, Ju v → WriterWP (unlink x) c v (fun _ v' => Ju v'))
    (hJuAdk : ∀ x d k v, Ju v → WriterWP (appendDeleteKlong x d k) c v (fun _ v' => Ju v'))
    (hJuEkn : ∀ x d v, Ju v → WriterWP (emptyKeyNext x d) c v (fun _ v' => Ju v'))
    (hJuHt : ∀ v, Ju v → HtInv H BK c v)
    (Post : W → Prop) (hfresh : ∀ v, Post v → WriterWP fresh c v (fun _ v' => Post v'))
    (hA : ∀ g v, DelInvJT c base KO BK B v → PutBook c B top0 v → HtInv H BK c v →
      LiveHoleW (pre ++ [cv]) g 0 c base v →
      WriterWP (afterDelete (pre ++ [cv]) g 0) c v (fun _ v' => Post v')) :
    WriterWP (putKv (.del (pre ++ [cv]))) c w (fun _ w' => Post w') := by
  have hfuel : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  refine writerWP_del_toLeafMKH c base hvc pre cv rk w
    (fun v => (KdJ c B top0 KO BK v ∧ v.madeFor = w.madeFor) ∧ HtJ0 c H BK v)
    (fun s f x v hJ hx => writerWP_mono (writerWP_and (writerWP_and
      (kdJ_descendLte c base B top0 hB KO BK hvB hk s f x v hJ.1.1 hx)
      (writerWP_descendLte_madeFor s c f x v)) (htJ0_descendLte hvo hkw s f x v hJ.2 hx))
      (fun _ v' h => ⟨⟨h.1.1, h.1.2.trans hJ.1.2⟩, h.2⟩))
    (fun s fd L n v hJ hL hlk hleaf hfd =>
      ⟨⟨kdJ_pathAdd c base B top0 hB KO BK hvB fd.c fd.y L n v hJ.1.1 hL hlk (kd_searchEq_mem n _ s fd hfd),
        hJ.1.2⟩, htJ0_pathAdd hvo s fd L n v hJ.2 hL hlk hleaf hfd⟩)
    ⟨⟨kdJ_start c base B top0 hB KO BK hvB w ⟨hbook, hb0, hi0⟩, rfl⟩, htJ0_start hvo w hb0 hHi hHwf⟩
    hrk (hI.pathUntaken _) hI.wf Post hfresh ?_
  intro L n P w3 hL hn hnl hr03 hJ3h hlk3 hp3' hlinkP hXD hlkX
  have hJ3 := hJ3h.1
  have hH3 := hJ3h.2
  have hb3 := hJ3.1
  have hMF3 : ∀ x o, w3.madeFor.lookup x = some o → o < B := by rw [hJ3.2]; exact hMF
  have hJ23 : TakeJ2 c base B w3 := takeJ2_of_readsAs c base B w w3 hJ2 hr03
  obtain ⟨hne, hall, hup⟩ := hleafC L n hL hn hnl
  obtain ⟨hdepth, hstopOK⟩ := hup P hlinkP hXD
  -- the path, at w
  have hgetP := LinkedFrom.get _ _ _ P hlinkP
  have hXN : ∀ i, i ≤ P.length → wNode c.p base w (nodeAt w.top.rootKey P i) =
      some ((wNode c.p base w (nodeAt w.top.rootKey P i)).getD n) := by
    intro i hi
    rcases Nat.lt_or_ge i P.length with hlt | hge
    · obtain ⟨_, n', _, h2, _⟩ := hgetP i hlt
      rw [h2]; rfl
    · have : i = P.length := by omega
      subst this
      rw [hXD, hn]; rfl
  have hKP : ∀ i, 0 < i → i ≤ P.length →
      P[i - 1]? = some (some (((P[i - 1]?).bind (·.1)).getD 0), nodeAt w.top.rootKey P i) ∧
      (((P[i - 1]?).bind (·.1)).getD 0, nodeAt w.top.rootKey P i) ∈
        ((wNode c.p base w (nodeAt w.top.rootKey P (i - 1))).getD n).liveAt c.i := by
    intro i h1 h2
    obtain ⟨k, n', e1, e2, e3⟩ := hgetP (i - 1) (by omega)
    have hi : i - 1 + 1 = i := by omega
    rw [hi] at e1 e3
    rw [e1, e2]
    exact ⟨rfl, e3⟩
  have hPL := LinkedFrom.pathLen _ _ _ P hlinkP
  have hreachX : ∀ i, i ≤ P.length →
      TReach (wNode c.p base w) c.i w.top.rootKey (nodeAt w.top.rootKey P i) :=
    fun i hi => (hPL i hi).reach
  have hdistP : ∀ i i', i ≤ P.length → i' ≤ P.length →
      nodeAt w.top.rootKey P i = nodeAt w.top.rootKey P i' → i = i' := by
    intro i i' h1 h2 he
    have a := hPL i h1
    have b := hPL i' h2
    rw [he] at a
    exact PathLen.depth_unique hI.tree _ _ _ a b
  have hpX : ∀ i, i ≤ P.length → (w3.path[i]?).map (·.2) = some (nodeAt w.top.rootKey P i) := by
    intro i hi
    have hl : i < (w.top.rootKey :: P.map (·.2)).length := by simp; omega
    rw [hp3', ← List.getElem?_map, List.map_cons, List.getElem?_eq_getElem hl]
    simp [nodeAt, List.getElem?_eq_getElem hl]
  have hpK : ∀ i, 0 < i → i ≤ P.length →
      w3.path[i]? = some (some (((P[i - 1]?).bind (·.1)).getD 0), nodeAt w.top.rootKey P i) := by
    intro i h1 h2
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [hp3', List.getElem?_cons_succ]
    exact (hKP (j + 1) h1 h2).1
  -- the facts at w3
  have hN3 : ∀ i, i ≤ P.length → wNode c.p base w3 (nodeAt w.top.rootKey P i) =
      some ((wNode c.p base w (nodeAt w.top.rootKey P i)).getD n) := fun i hi => by
    rw [hr03.1]; exact hXN i hi
  have htk3 : ∀ i, i ≤ P.length → w3.taken.contains (nodeAt w.top.rootKey P i) = false := fun i hi => by
    rw [hr03.2.2.1]; exact hI.untaken _ (tReach_reachS _ _ _ _ (hreachX i hi))
  have hT3 : TreeOK (wNode c.p base w3) c.i w3.top.rootKey := by rw [hr03.1, hr03.2.1]; exact hI.tree
  have hR3 : RangeOrder (wNode c.p base w3) c.i w3.top.rootKey := by rw [hr03.1, hr03.2.1]; exact hRO
  have hwf3 : ∀ x xn, TReach (wNode c.p base w3) c.i w3.top.rootKey x → wNode c.p base w3 x = some xn →
      klongsWf xn.ks = true := fun x xn _ h => by rw [hr03.1] at h; exact hI.wf x xn h
  have hRt3 : ∀ y, TReach (wNode c.p base w3) c.i w3.top.rootKey y → w3.taken.contains y = false := by
    intro y hy
    rw [hr03.1, hr03.2.1] at hy
    rw [hr03.2.2.1]
    exact hI.untaken y (tReach_reachS _ _ _ _ hy)
  have hTimesR3 : ∀ y yn, TReach (wNode c.p base w3) c.i w3.top.rootKey y → wNode c.p base w3 y = some yn →
      ∀ s, Klong.time s ∈ yn.ks → s ≤ c.i := fun y yn _ h => by rw [hr03.1] at h; exact hI.times y yn h
  have hICE3 : InnerChildrenExist (wNode c.p base w3) c.i w3.top.rootKey := by
    rw [hr03.1, hr03.2.1]; exact hICE
  have hfit3 : SegFits (wNode c.p base w3) c.i w3.next w3.top.rootKey :=
    segFits_next_of_putInv c base w3 (putInv_of_readsAs c base w w3 hI hr03)
  have hnovalAll3 : ∀ y yn, wNode c.p base w3 y = some yn → wValue base w3 y = none := by
    intro y yn h
    rw [hr03.1] at h
    rw [ReadsAs.value _ _ _ _ hr03]
    exact hI.keyNoValue y yn h
  have hreach3 : ∀ i, i ≤ P.length →
      TReach (wNode c.p base w3) c.i w3.top.rootKey (nodeAt w.top.rootKey P i) := fun i hi => by
    rw [hr03.1, hr03.2.1]; exact hreachX i hi
  have hlinkK : ∀ i, 0 < i → i ≤ P.length →
      (((P[i - 1]?).bind (·.1)).getD 0, nodeAt w.top.rootKey P i) ∈
        ((wNode c.p base w (nodeAt w.top.rootKey P (i - 1))).getD n).liveAt c.i :=
    fun i h1 h2 => (hKP i h1 h2).2
  have hNnD : (wNode c.p base w (nodeAt w.top.rootKey P P.length)).getD n = n := by rw [hXD, hn]; rfl
  -- the tree's facts at a continuation of the upward delete
  have hD : ∀ (stop : Nat) (w' : W) (sn' : KNode) (f : Nat → Nat), stop < P.length →
      (∀ y, (∀ k, stop < k → k ≤ P.length → y ≠ nodeAt w.top.rootKey P k) →
        w'.taken.contains y = w3.taken.contains y) →
      w'.top = w3.top → w'.vals = w3.vals →
      (∀ y, y ≠ nodeAt w.top.rootKey P stop → (∀ k, stop < k → k ≤ P.length → y ≠ nodeAt w.top.rootKey P k) →
        w'.nodes.lookup y = w3.nodes.lookup y) →
      w'.nodes.lookup (nodeAt w.top.rootKey P stop) = some sn' →
      sn'.leaf = ((wNode c.p base w (nodeAt w.top.rootKey P stop)).getD n).leaf →
      klongsWf sn'.ks = true → (∀ s, Klong.time s ∈ sn'.ks → s ≤ c.i) →
      (∀ c' z, (c', z) ∈ sn'.liveAt c.i →
        ∃ c0, (c0, z) ∈ ((wNode c.p base w (nodeAt w.top.rootKey P stop)).getD n).liveAt c.i ∧
          c0 ≠ ((P[stop + 1 - 1]?).bind (·.1)).getD 0 ∧ f c0 = c') →
      RangeOrder (wNode c.p base w') c.i w'.top.rootKey →
      PutBook c B top0 w' → Book BK c w' → KdInv KO BK w' →
      DelInvT c base KO BK w' := by
    intro stop w' sn' f hsD ht htop hv hnodes hsn' hsl' hsw' hst' hlive' hRO' hb' hbk hik
    have hCG := collGetInvD_after_upT c base (fun i => nodeAt w.top.rootKey P i)
      (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
      (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length w3 hlkX htk3 hdistP hT3 hwf3 hRt3 hTimesR3
      hICE3 w3.next hfit3 hnovalAll3 hreach3 hlinkK stop w' sn' f hsD ht htop hv hnodes hsn' hsl' hsw' hst' hlive'
    have hG := putInvG_of_book c base B top0 w' hB hb'
    have hPI : PutInv c base w' := putInv_of_parts c base w' hG hCG.1.1
      (fun y hy => hCG.1.2.1 y (reachS_tReach _ _ _ _ hy))
      (leafOrder_of_rangeOrder _ _ _ hRO' hG.times)
    exact ⟨hPI, hG, hRO', fun y yn cc z hy hyn hl hz => hCG.1.2.2.2 y yn cc z hy hyn hl hz,
      ⟨B, top0, hB, hb'⟩, hbk, hik⟩
  -- the frame facts at a continuation
  have hXs : ∀ stop, stop < P.length → ∀ k, stop < k → k ≤ P.length →
      nodeAt w.top.rootKey P stop ≠ nodeAt w.top.rootKey P k :=
    fun stop _ k h1 h2 he => by have := hdistP _ _ (by omega) h2 he; omega
  have hfr : ∀ (stop : Nat) (w' : W) (sn' : KNode), stop < P.length →
      (∀ y, (∀ k, stop < k → k ≤ P.length → y ≠ nodeAt w.top.rootKey P k) →
        w'.taken.contains y = w3.taken.contains y) →
      (∀ y, y ≠ nodeAt w.top.rootKey P stop → (∀ k, stop < k → k ≤ P.length → y ≠ nodeAt w.top.rootKey P k) →
        w'.nodes.lookup y = w3.nodes.lookup y) →
      w'.nodes.lookup (nodeAt w.top.rootKey P stop) = some sn' →
      (∀ u, u ≠ nodeAt w.top.rootKey P stop → (∀ i, stop < i → i ≤ P.length → u ≠ nodeAt w.top.rootKey P i) →
        wNode c.p base w' u = wNode c.p base w3 u) ∧
      wNode c.p base w' (nodeAt w.top.rootKey P stop) = some sn' := by
    intro stop w' sn' hsD ht hnodes hsn'
    refine ⟨fun u hus hnc => by simp only [wNode, ht u hnc, hnodes u hus hnc], ?_⟩
    simp only [wNode, ht _ (hXs stop hsD), htk3 stop (by omega), Bool.false_eq_true, ↓reduceIte, hsn']
  have hcvAll : ∀ c' z, (c', z) ∈ n.liveAt c.i → c' = cv := by
    intro c' z hm'
    have hnt := hI.times L n hn
    have hm2 : (c', z) ∈ n.live := by rw [← KNode.liveAt_of_times _ c.i hnt]; exact hm'
    exact allKeysIn_live_cv n cv hall c' z hm2
  have hallD : ((wNode c.p base w (nodeAt w.top.rootKey P P.length)).getD n).allKeysIn
      (bitsUnion ((wNode c.p base w (nodeAt w.top.rootKey P P.length)).getD n).lastBitmap
        (((wNode c.p base w (nodeAt w.top.rootKey P P.length)).getD n).bitsOf cv)) = true := by
    rw [hNnD]; exact hall
  have hX0 : nodeAt w.top.rootKey P 0 = w.top.rootKey := by simp [nodeAt]
  have hlinkK' : ∀ i, 0 < i → i ≤ P.length →
      (((P[i - 1]?).bind (·.1)).getD 0, nodeAt w.top.rootKey P i) ∈
        ((wNode c.p base w (nodeAt w.top.rootKey P (i - 1))).getD n).liveAt c.i := hlinkK
  rw [← hXD]
  refine takeJ2_deleteUpward_upTMBKDS c base (fun i => nodeAt w.top.rootKey P i)
    (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
    (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length cv pre rk B w3 hdepth hfuel hpos hpX hpK hlkX htk3
    (fun i hi => hTimesR3 _ _ (hreach3 i hi) (hN3 i hi))
    hdistP (by rw [hNnD]; exact hne) (by rw [hNnD]; exact hall) (by rw [hNnD]; exact hnl) hT3 hR3 hwf3 hRt3
    hTimesR3 hICE3 w3.next hfit3 hnovalAll3 hreach3
    hlinkK (by rw [hr03.1, hr03.2.1]; exact hrk)
    (keyWf_last_notin pre cv hkey) (by rw [hr03.1, hXD]; exact hL)
    (by rw [hr03.1, hr03.2.1]; exact hI.keyUniq pre cv rk hkey hrk) hstopOK hm
    (fun c' z hz => by
      rw [hNnD] at hz
      have := hcvAll c' z hz
      subst this
      rw [hr03.1]; exact hLV L n hL hn hnl z hz) hJ23 hMF3 _
    (fun v => KdJG c B top0 KO BK w3.path w3.gh v ∧ Ju v) ⟨⟨⟨hb3, rfl⟩, fun _ he => he⟩, hJu0 w3 hH3⟩
    (fun s v hJ => ⟨⟨kdJP_note c base B top0 hB KO BK hvB hk _ s v hJ.1.1, hJ.1.2⟩, hJuNote s v hJ.2⟩)
    (fun x q k v hJ hx => writerWP_and (kdJG_takeBack c base B top0 hB KO BK hvB hk _ _ x q k v hJ.1 hx)
      (hJuTake x q k v hJ.2))
    (fun x v hJ => writerWP_and (kdJG_unlink c base B top0 hB KO BK hvB hk _ _ x v hJ.1) (hJuUnlink x v hJ.2))
    (fun x d k v hJ hx => writerWP_and (kdJG_appendDeleteKlong c base B top0 hB KO BK hvB hk _ _ x d k v hJ.1 hx)
      (hJuAdk x d k v hJ.2))
    (fun x d v xn hJ hx hl hxl => writerWP_and (kdJG_emptyKeyNext c base B top0 hB KO BK hvB hk _ _ x d v xn
      hJ.1 hx hl hxl) (hJuEkn x d v hJ.2)) ?_ ?_ ?_
  · -- an inner stop node: none, with the live counts at the start
    intro seg stop w' sn' hsD hbetween _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hNl
    exfalso
    exact lebStop_false c base w hLC hm hI (fun i => nodeAt w.top.rootKey P i)
      (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
      (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length stop cv hX0 hXN hlinkK' hallD hsD hbetween hNl
  · intro stop w' sn' hsD hbetween ht htop hv hnodes hsn' hsl' hsw' hst' hlive' hread hfate hfJ hst hJv
      hCG hstp hJw' gs hs hgh
    obtain ⟨hagree, hsnw⟩ := hfr stop w' sn' hsD ht hnodes hsn'
    -- the stop node is a leaf
    cases hsl0 : ((wNode c.p base w (nodeAt w.top.rootKey P stop)).getD n).leaf with
    | false =>
      exfalso
      exact lebStop_false c base w hLC hm hI (fun i => nodeAt w.top.rootKey P i)
        (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
        (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length stop cv hX0 hXN hlinkK' hallD hsD hbetween hsl0
    | true =>
    have hRO' : RangeOrder (wNode c.p base w') c.i w'.top.rootKey := by
      rw [htop]
      exact rangeOrder_up_bitmap (wNode c.p base w3) (wNode c.p base w') c.i w3.top.rootKey _ _ _ stop
        P.length hsD hR3 hT3 (hreach3 stop (by omega)) (fun i _ h2 => hN3 i h2)
        (fun i h1 h2 => hlinkK i (by omega) h2) (fun i i' _ h2 _ h4 he => hdistP i i' h2 h4 he)
        hagree sn' hsnw hsl' (fun c' z h => (hlive' c' z).mp h)
    obtain ⟨⟨⟨hkdj, hpp⟩, hgsub⟩, hju⟩ := hJw'
    have hDv := hD stop w' sn' id hsD ht htop hv hnodes hsn' hsl' hsw' hst'
      (fun c' z h => ⟨c', ((hlive' c' z).mp h).1, ((hlive' c' z).mp h).2, rfl⟩) hRO' hkdj.1 hkdj.2.1 hkdj.2.2
    -- the pair is the stop node's
    obtain ⟨g0, h0, hm0⟩ := kd_tag_of_lookup hb3.2.1 (hlkX stop (by omega))
    have hh0 : h0 = 0 := kd_h0 hb3.2.1 (hlkX stop (by omega)) hm0 hsl0
    subst hh0
    obtain ⟨v0, ⟨⟨⟨hkdj0, _⟩, hgsub0⟩, _⟩, hgh0⟩ := hgh
    rw [lookup_of_mem_nodup _ hkdj0.2.1.nodup _ _ (hgsub0 _ hm0)] at hgh0
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hgh0)
    have hsn'l : sn'.leaf = true := by rw [hsl']; exact hsl0
    refine hA g0 w' ⟨hDv, hJv, hkdj.1.fresh.1⟩ hkdj.1 (hJuHt w' hju) ?_
    -- the hole at the stop node
    have hroot' : w'.top.rootKey = w.top.rootKey := by rw [htop, hr03.2.1]
    have hagree' : ∀ u, u ≠ nodeAt w.top.rootKey P stop →
        (∀ i, stop < i → i ≤ P.length → u ≠ nodeAt w.top.rootKey P i) →
        wNode c.p base w' u = wNode c.p base w u := by
      intro u h1 h2; rw [hagree u h1 h2, hr03.1]
    have hE : LiveEdgesH c.p (wNode c.p base w') c.i w'.top.rootKey
        (fun y => y = nodeAt w.top.rootKey P stop) := by
      rw [hroot']
      by_cases hak : ((wNode c.p base w (nodeAt w.top.rootKey P stop)).getD n).allKeysIn
          (bitsUnion ((wNode c.p base w (nodeAt w.top.rootKey P stop)).getD n).lastBitmap
            (((wNode c.p base w (nodeAt w.top.rootKey P stop)).getD n).bitsOf
              (((P[stop + 1 - 1]?).bind (·.1)).getD 0))) = true
      · -- the stop node is the space root, a leaf, left empty
        obtain ⟨hs0, _⟩ := hstp hak
        have hroot0 : nodeAt w.top.rootKey P stop = w.top.rootKey := by rw [hs0]; simp [nodeAt]
        have hempty : sn'.liveAt c.i = [] := by
          cases hl' : sn'.liveAt c.i with
          | nil => rfl
          | cons q rest =>
            exfalso
            have hq : q ∈ sn'.liveAt c.i := by rw [hl']; exact List.mem_cons_self
            obtain ⟨hq1, hq2⟩ := (hlive' q.1 q.2).mp hq
            have hNt := hTimesR3 _ _ (hreach3 stop (by omega)) (hN3 stop (by omega))
            rw [KNode.liveAt_of_times _ c.i hNt] at hq1
            exact hq2 (allKeysIn_live_cv _ _ hak q.1 q.2 hq1)
        apply liveEdgesH_of_liveEdges
        rw [← hroot0]
        exact liveEdges_emptyRoot c.p _ c.i _ sn' hsnw hsn'l hempty
      · -- the stop node keeps a live klong
        have hak' := Bool.eq_false_iff.mpr hak
        obtain ⟨c1, z1, hc1, hz1⟩ := exists_live_of_keep _ _ hak'
        have hNt := hTimesR3 _ _ (hreach3 stop (by omega)) (hN3 stop (by omega))
        have hpos' : sn'.liveAt c.i ≠ [] := by
          intro h0
          have : (c1, z1) ∈ sn'.liveAt c.i :=
            (hlive' c1 z1).mpr ⟨by rw [KNode.liveAt_of_times _ c.i hNt]; exact hz1, hc1⟩
          rw [h0] at this
          cases this
        exact liveEdgesH_up c.p (wNode c.p base w) (wNode c.p base w') c.i w.top.rootKey
          (fun i => nodeAt w.top.rootKey P i) (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
          (fun i => ((P[i - 1]?).bind (·.1)).getD 0) stop P.length hsD hI.tree (hreachX stop (by omega))
          (fun i _ h2 => hXN i h2) (fun i h1 h2 => hlinkK i (by omega) h2)
          (fun i i' _ h2 _ h4 he => hdistP i i' h2 h4 he) hagree' sn' hsnw
          hsl' (fun c' z h => (hlive' c' z).mp h) hpos' (edges_of_liveCounts c.p _ _ _ hLC)
    refine liveHoleW_of_hole (pre ++ [cv]) g0 0 c base w' _ hE ?_
    have hs := segRd_of KO BK c w' hkdj.2.1 hkdj.2.2 hk
    have hgL : rdG c w' (nodeAt w.top.rootKey P stop) = some (g0, 0) := by
      rw [rdG_of_lookup c w' _ sn' hsn']
      exact lookup_of_mem_nodup _ hkdj.2.1.nodup _ _ (hgsub _ hm0)
    refine holeAtW_stop c base hvc w w3 w' pre cv rk L n P stop g0 sn' hI.tree
      (fun y hy => hI.untaken y (tReach_reachS _ _ _ _ hy)) hI.wf hrk hL hn hnl hr03 hp3' hlinkP hXD hlkX
      hkey hsD hsl0 hnodes htop hsn' hsn'l ?_ hsw' hst' hs hgL
    intro z hz
    have hNt' : ∀ s, Klong.time s ∈ sn'.ks → s ≤ c.i := hst'
    have hz' : (((P[stop]?).bind (·.1)).getD 0, z) ∈ sn'.liveAt c.i := by
      rw [KNode.liveAt_of_times _ c.i hNt']; exact hz
    exact ((hlive' _ z).mp hz').2 (by simp)
  · intro seg stop w' sn' jcv jy hsD hbetween _ _ _ _ _ _ _ _ hsl
    exfalso
    exact lebStop_false c base w hLC hm hI (fun i => nodeAt w.top.rootKey P i)
      (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
      (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length stop cv hX0 hXN hlinkK' hallD hsD hbetween hsl

/-! ## The case of the live family -/

/-- The heights through the upward delete's steps (030-01's R2, the heights): an
invariant from the walk's end that the steps keep and that gives `HtInv`. -/
def UpHtWalk (c : Ctx) (H : NodeId → Nat → Prop) (B : NodeId) (Ju : W → Prop) : Prop :=
  (∀ v, HtJ0 c H B v → Ju v) ∧ (∀ (s : String) v, Ju v → Ju { v with trail := s :: v.trail }) ∧
  (∀ x q k v, Ju v → WriterWP (takeBack x q k) c v (fun _ v' => Ju v')) ∧
  (∀ x v, Ju v → WriterWP (unlink x) c v (fun _ v' => Ju v')) ∧
  (∀ x d k v, Ju v → WriterWP (appendDeleteKlong x d k) c v (fun _ v' => Ju v')) ∧
  (∀ x d v, Ju v → WriterWP (emptyKeyNext x d) c v (fun _ v' => Ju v')) ∧
  (∀ v, Ju v → HtInv H B c v)

set_option maxHeartbeats 1600000 in
/-- The upward delete with room (bergdb 030-01, step 6): from the first stratum's
start with the live counts, the delete calls `afterDelete` at the stop node's pair
(g, 0) from a state with `DelInvJT`, `PutBook`, `HtInv` and `LiveHoleW key g 0`,
given the heights through the upward steps (`UpHtWalk`). -/
theorem liveDel_upRoom (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P) :
    ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
      lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
      topOf p (ctxOf p ts).view z = .ok top →
      ∀ pre op post, tx.ops = pre ++ op :: post →
      ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      SJ0 p ts tx w → TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w →
      ∀ key, op = .del key → DelEmptyRoomM (ctxOf p ts) (viewOf (treeRun p ts)) w op →
      ∀ Ju, UpHtWalk (ctxOf p ts) (htOracleOf p (treeRun p ts)) tx.base Ju →
      ∀ Q : W → Prop, (∀ v, Q v → WriterWP fresh (ctxOf p ts) v (fun _ v' => Q v')) →
      (∀ g v, DelInvJT (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts))
          tx.base tx.base v → PutBook (ctxOf p ts) tx.base top v →
        HtInv (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) v →
        LiveHoleW key g 0 (ctxOf p ts) (viewOf (treeRun p ts)) v →
        WriterWP (afterDelete key g 0) (ctxOf p ts) v (fun _ v' => Q v')) →
      WriterWP (putKv op) (ctxOf p ts) w (fun _ w' => Q w') := by
  intro ts tx hw hr z top _ htop ops op post hops r w hpre hS hJ key hop hPc Ju hU Q hfresh hA
  obtain ⟨pre, cv, L0, n0, hop', hm, hK, hne0, hall0, hup0⟩ := hPc
  subst hop'
  cases hop
  have hI : PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w := hS.1.1.1.1.1
  have hRO : RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey := hS.1.1.2
  have hkey : keyWf (pre ++ [cv]) = true := within_op_keyWf p ts tx hw ops _ post hops
  obtain ⟨rk, hrk, _⟩ := keyLeaf_rk hK
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  have hbook := putBook_reached p ts tx hw (hRL _ _ hr) z top htop ops r w hpre
  have hICE := innerChildren_reachedR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
    (fun x hx => hI.untaken x (tReach_reachS _ _ _ _ hx))
  have hLV := leafVals_all hS.1.1.1.1.2 hkey hrk
  obtain ⟨hv, hk, hb0, hi0⟩ := kd_contextR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
  obtain ⟨hvo, hkw, _, _, _, hiw, hwfw⟩ := hS.2.1
  obtain ⟨hU0, hUn, hUt, hUu, hUa, hUe, hUh⟩ := hU
  exact writerWP_del_upRoomLive (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w tx.base top hB hbook
    _ tx.base hv hk hb0 hi0 hI hRO hICE hkey hrk (keyLeaf_all2 hK hrk _ ⟨hne0, hall0, hup0⟩) hm
    (by simp [ctxOf]) hJ hS.1.2 (fun L n hL hn hnl y hy => (hLV L n hL hn hnl y hy).1) hS.2.2
    hvo hkw hiw hwfw Ju hU0 hUn hUt hUu hUa hUe hUh Q hfresh hA

/-- The upward delete with room keeps the live counts (bergdb 030-01, steps 6, 3
and 4): with the merges' loop and root collapse from the hole
(`writerWP_afterDelete_live`), given its live merge and root collapse
(`MergeLiveOK`, `CollapseLiveOK`) and the heights through the upward steps
(`UpHtWalk`). -/
theorem liveDel_upRoom_live (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
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
      ∀ key, op = .del key → DelEmptyRoomM (ctxOf p ts) (viewOf (treeRun p ts)) w op →
      ∀ Ju, UpHtWalk (ctxOf p ts) (htOracleOf p (treeRun p ts)) tx.base Ju →
      WriterWP (putKv op) (ctxOf p ts) w (fun _ w' =>
        LiveEdges p (wNode p (viewOf (treeRun p ts)) w') (ts.length + 1) w'.top.rootKey) := by
  intro ts tx hw hr z top hz htop pre op post hops r w hpre hS hJ key hop hPc Ju hU
  have hm : (ctxOf p ts).p.merges = true := by
    obtain ⟨_, _, _, _, _, hm, _⟩ := hPc
    exact hm
  obtain ⟨hv, hk, _, _⟩ := kd_contextR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top pre (op :: post) hops r w hpre
  have hICEk : ICEFromKinds (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base :=
    fun v hb hi hun => innerChildren_of_kinds p (treeRun p ts) tx.base (ctxOf p ts) v rfl (hRK _ _ hr)
      (hRP _ _ hr) hb hi.cache hun
  obtain ⟨hvo, hkw, _⟩ := hS.2.1
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  refine liveDel_upRoom p R hM hRL hRP hRK ts tx hw hr z top hz htop pre op post hops r w hpre hS hJ key hop
    hPc Ju hU _ (fun v hv => by
      unfold fresh
      simp only [writerWP_bind, writerWP_get, writerWP_set, writerWP_pure]
      exact hv) ?_
  intro g v hD hpb hhi hLH
  exact writerWP_afterDelete_live key g (ctxOf p ts) _ (viewCoherent_ctxOf p ts) hm _ tx.base hv hk hICEk
    hsa2 hcap (by simp [ctxOf]) hvo hkw top hB (hML ts tx) (hCL ts tx) v
    (delInvJAE_of_T _ _ _ _ _ v hD) hpb hhi hLH

end SIS.Tree
