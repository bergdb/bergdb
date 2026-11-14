/-
`QDead` of the puts that make new segments below a leaf with room (bergdb
024-12, the top theorem's premise `d3`, cases (3a) and (3b)): the leaf gets a
key klong of a compare value it has no live klong of, which adds no dead klong
(`KNode.deadCount_add_key_new`: a klong of that compare value before it is
deleted or shadowed already, and the bitmap names no klong after the node's
last; cost's `LastLive`, `keyLookup_of_last`), and the new segment leaves hold
one klong each.
-/
import SIS.Tree.DeadRun
import SIS.Tree.KlongDeleteAppend
import SIS.Tree.KlongRoundTripBits
import SIS.Tree.NormalizedDead

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- Every bit of a node's last bitmap names a klong of the node. -/
theorem lastBitmapOf_lt (ks : List Klong) (hw : klongsWf ks = true) :
    ∀ b ∈ lastBitmapOf ks, b < ks.length := by
  intro b hb
  rcases lastBitmapFold_origin ks [] with he | hm
  · change lastBitmapOf ks = [] at he
    rw [he] at hb; cases hb
  · change .del (lastBitmapOf ks) ∈ ks at hm
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
    have hil : i < ks.length := (List.getElem?_eq_some_iff.mp hi).1
    have hs := klongsWfState_ok ks hw (i+1)
    rw [klongsWfState_succ ks i (.del (lastBitmapOf ks)) hi] at hs
    simp only [klongsWfStep, Bool.and_eq_true] at hs
    have hall := hs.1.2
    have hb' := List.all_eq_true.mp hall b hb
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb'
    omega

/-- The predicate of `KNode.deadCount`. -/
def deadP (ks : List Klong) (del : List Nat) : Klong × Nat → Bool := fun (k, i) => match k with
  | .key c _ => del.contains i || (ks.drop (i + 1)).any (fun k' => match k' with
      | .key c' _ => c' == c
      | _ => false)
  | _ => false

theorem KNode.deadCount_eq (n : KNode) :
    n.deadCount = (n.ks.zipIdx.filter (deadP n.ks n.lastBitmap)).length := rfl

/-- A key klong of a compare value that has no live klong in the node adds no
dead klong. -/
theorem KNode.deadCount_add_key_new (n : KNode) (t : Time) (c : Nat) (v : NodeId)
    (hw : klongsWf n.ks = true) (hnone : n.live.lookup c = none) :
    (n.add t (.key c v)).deadCount ≤ n.deadCount := by
  have hlb := KNode.add_key_lastBitmap n t c v
  have hlt := lastBitmapOf_lt n.ks hw
  obtain ⟨E, hE, hEk⟩ : ∃ E : List Klong, (n.add t (.key c v)).ks = n.ks ++ E ∧
      (E = [.time t, .key c v] ∨ E = [.key c v]) := by
    unfold KNode.add
    split
    · split
      · exact ⟨_, rfl, Or.inl rfl⟩
      · exact ⟨_, rfl, Or.inr rfl⟩
    · exact ⟨_, rfl, Or.inl rfl⟩
  rw [KNode.deadCount_eq, KNode.deadCount_eq, hlb, hE]
  generalize hdel : n.lastBitmap = del at hlt
  have hdel' : lastBitmapOf n.ks = del := hdel
  rw [hdel'] at hlt
  have hA : (n.ks.zipIdx.filter (deadP (n.ks ++ E) del)) = n.ks.zipIdx.filter (deadP n.ks del) := by
    apply List.filter_congr
    intro x hx
    obtain ⟨k, i⟩ := x
    have hki : n.ks[i]? = some k := by
      have := List.mem_zipIdx_iff_getElem?.mp hx
      simpa using this
    have hil : i < n.ks.length := (List.getElem?_eq_some_iff.mp hki).1
    cases k with
    | time _ => rfl
    | del _ => rfl
    | key c' y =>
      simp only [deadP]
      rw [List.drop_append_of_le_length (by omega), List.any_append]
      have hEany : E.any (fun k' => match k' with
          | .key c'' _ => c'' == c'
          | _ => false) = (c == c') := by
        rcases hEk with h | h <;> subst h <;> simp
      rw [hEany]
      cases hcc : (c == c') with
      | false => simp
      | true =>
        have hcc' : c = c' := by simpa using hcc
        subst hcc'
        cases hA : (del.contains i || (List.drop (i + 1) n.ks).any (fun k' => match k' with
            | .key c'' _ => c'' == c
            | _ => false)) with
        | true => simp
        | false =>
          exfalso
          simp only [Bool.or_eq_false_iff] at hA
          obtain ⟨h1, h2⟩ := hA
          have hl : LastLive n.ks n.lastBitmap i c := by
            refine ⟨⟨y, hki⟩, ?_, ?_⟩
            · intro hm
              rw [hdel] at hm
              have : del.contains i = true := List.elem_eq_true_of_mem hm
              rw [this] at h1; cases h1
            · intro j y' hij hj
              exfalso
              have hmem : Klong.key c y' ∈ List.drop (i + 1) n.ks := by
                have hj' : (List.drop (i + 1) n.ks)[j - (i + 1)]? = some (.key c y') := by
                  rw [List.getElem?_drop]
                  have : i + 1 + (j - (i + 1)) = j := by omega
                  rw [this]; exact hj
                exact List.mem_of_getElem? hj'
              have : (List.drop (i + 1) n.ks).any (fun k' => match k' with
                  | .key c'' _ => c'' == c
                  | _ => false) = true := List.any_eq_true.mpr ⟨_, hmem, by simp⟩
              rw [this] at h2; cases h2
          have hk := keyLookup_of_last n.lastBitmap c n.ks i y hki hl
          rw [← KNode.live_lookup, hnone] at hk
          cases hk
  rw [List.zipIdx_append, List.filter_append, List.length_append, hA]
  have hB : ((E.zipIdx (0 + n.ks.length)).filter (deadP (n.ks ++ E) del)).length = 0 := by
    have hm1 : n.ks.length ∉ del := fun h => by have := hlt _ h; omega
    have hm2 : n.ks.length + 1 ∉ del := fun h => by have := hlt _ h; omega
    rcases hEk with h | h <;> subst h
    · have hd : List.drop (n.ks.length + 1 + 1) (n.ks ++ [Klong.time t, Klong.key c v]) = [] :=
        List.drop_eq_nil_of_le (by simp)
      simp [deadP, hm2, hd, List.zipIdx_cons]
    · have hd : List.drop (n.ks.length + 1) (n.ks ++ [Klong.key c v]) = [] :=
        List.drop_eq_nil_of_le (by simp)
      simp [deadP, hm1, hd, List.zipIdx_cons]
  omega

/-- A leaf with no live klong of c0 at the transaction's time has none at all
(its klongs are of no later time). -/
theorem KNode.live_lookup_none_of_searchEq (n : KNode) (t : Time) (c : Nat)
    (hw : klongsWf n.ks = true) (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t)
    (h : n.searchEq t c = none) : n.live.lookup c = none := by
  have hs := searchEqSpec n t c hw
  rw [h, KNode.liveAt_of_times n t ht] at hs
  exact hs.symm

/-- A new segment leaf with one klong holds no dead klong. -/
theorem KNode.deadCount_newLeaf (t : Time) (a : Nat) (y : NodeId) :
    ((⟨true, []⟩ : KNode).add t (.key a y)).deadCount = 0 :=
  KNode.newKlongs_deadCount true t [(a, y)] (by simp)

/-- (3a), `QDead`. -/
theorem deadCase_putNewSeg1Room (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M) :
    OpCaseOK p R (QDead p) PutNewSeg1RoomCase := by
  intro ts tx _ _ _ _ _ _ _ op _ _ _ w _ hI _ hP
  obtain ⟨pre, c0, cl, h, rk0, L, n, hop, hat, hroom⟩ := hP
  subst hop
  have ht : ∀ q ∈ fromVisits (wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w) (ctxOf p ts).i
      (ctxOf p ts).p.fuel (pre ++ [c0, cl]) w.top.rootKey, w.taken.contains q.1 = false :=
    fun q hq => hI.untaken q.1 (fromVisits_reach _ _ _ _ (fun x xn _ hn => hI.wf x xn hn) _ _ q.1 q.2
      ReachS.root hq)
  have hall := newSegAt_one hat (fun _ m => m.searchEq (ctxOf p ts).i c0 = none ∧
      m.size + 1 < (ctxOf p ts).p.M) ⟨hat.2.2.2.2.2, hroom⟩
  refine writerWP_mono (writerWP_put_newSeg_after (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre c0 cl
    h rk0 w hM hat.2.1 ht hI.ids.1 hI.ids.2.1 hI.ids.2.2.1 hall) ?_
  intro _ w' ⟨L', n', hvis, hn', hnl', _, _, hL', hy', hother⟩ hW h0 x m hx
  have hn'2 : wNode p (viewOf (treeRun p ts)) w L' = some n' := hn'
  by_cases hxy : x = w.next
  · subst hxy
    have hy'2 : wNode p (viewOf (treeRun p ts)) w' w.next =
        some ((⟨true, []⟩ : KNode).add (ts.length + 1) (.key cl (w.next + 2))) := hy'
    rw [hy'2] at hx
    cases hx
    rw [KNode.deadCount_newLeaf]
    exact Nat.zero_le _
  · by_cases hxL : x = L'
    · subst hxL
      have hL'2 : wNode p (viewOf (treeRun p ts)) w' x =
          some (n'.add (ts.length + 1) (.key c0 w.next)) := hL'
      rw [hL'2] at hx
      cases hx
      have hnone := KNode.live_lookup_none_of_searchEq n' (ctxOf p ts).i c0 (hI.wf x n' hn'2)
        (hI.times x n' hn'2) (hall x n' hvis hn' hnl').1
      exact Nat.le_trans (KNode.deadCount_add_key_new n' _ c0 w.next (hI.wf x n' hn'2) hnone)
        (hW h0 x n' hn'2)
    · have hother2 : wNode p (viewOf (treeRun p ts)) w' x = wNode p (viewOf (treeRun p ts)) w x :=
        hother x hxL hxy
      rw [hother2] at hx
      exact hW h0 x m hx

/-! ## (3b) -/

/-- `WDeadOK` over any node map. -/
def WDeadN (p : Params) (N : NodeId → Option KNode) : Prop :=
  p.theta ≠ 0 → ∀ x n, N x = some n → n.deadCount ≤ p.theta

/-- `writerWP_putSegs_new_live` for the dead klongs: the new segment leaves
hold none. -/
theorem writerWP_putSegs_new_dead (c : Ctx) (base : View BVal) (key : List Nat) (h : Nat)
    (hM : 2 ≤ c.p.M) (hfuel : 1 ≤ c.p.fuel) :
    ∀ (tail : List Nat), tail ≠ [] → ∀ (ws : W) (x : NodeId),
      ws.nodes.lookup x = some ⟨true, []⟩ → ws.taken.contains x = false → x < ws.next →
      (∀ z, ws.next ≤ z → ws.nodes.lookup z = none ∧ ws.taken.contains z = false ∧
        knodeOf c.p base z = none ∧ valueOf base z = none ∧ ws.vals.lookup z = none) →
      WriterWP (putSegs key (some h) tail x) c ws (fun _ wf =>
        wf.taken = ws.taken ∧ wf.top = ws.top ∧ ws.next ≤ wf.next ∧
        (∀ z, z < ws.next → z ≠ x → wf.nodes.lookup z = ws.nodes.lookup z) ∧
        (∀ z, wf.next ≤ z → wf.nodes.lookup z = none) ∧
        ∀ z m, (z = x ∨ ws.next ≤ z) → wf.nodes.lookup z = some m →
          m.deadCount = 0) := by
  obtain ⟨f2, hf2⟩ : ∃ f2, c.p.fuel = f2 + 1 := ⟨c.p.fuel - 1, by omega⟩
  intro tail
  induction tail with
  | nil => intro hne; exact absurd rfl hne
  | cons a tail' ih =>
    intro _ ws x hx htx hxn hfr
    cases tail' with
    | nil =>
      rw [putSegs.eq_2]
      refine writerWP_mono (post := fun _ wf => wf.nodes = upsert ws.nodes x
          ((⟨true, []⟩ : KNode).add c.i (.key a ws.next)) ∧ wf.vals = ws.vals ++ [(ws.next, h)] ∧
          wf.taken = ws.taken ∧ wf.top = ws.top ∧ wf.next = ws.next + 2) ?_ ?_
      · unfold setValue
        simp only [writerWP_bind, writerWP_read]
        rw [hf2]
        unfold descendLte
        simp only [writerWP_bind, writerWP_read]
        rw [writerWP_getNode_known _ _ c ws hx]
        simp only [↓reduceIte, writerWP_pure]
        unfold newValue fresh
        simp only [writerWP_bind, writerWP_get, writerWP_set, writerWP_modify, writerWP_pure]
        rw [writerWP_getNode_known _ _ c _ (by simpa using hx)]
        have hcond : (decide ((⟨true, []⟩ : KNode).size + 1 < c.p.M) &&
            !deadOver c.p ((⟨true, []⟩ : KNode).add c.i (.key a ws.next))) = true := by
          simp only [KNode.size, List.length_nil, deadOver_empty_add]
          simp; omega
        simp only [hcond, ↓reduceIte, putNode, writerWP_bind, writerWP_modify, writerWP_pure]
        all_goals (refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial)
      · intro _ wf ⟨g1, _, g3, g4, g5⟩
        refine ⟨g3, g4, by omega, ?_, ?_, ?_⟩
        · intro z _ hzx; rw [g1, lookup_upsert]; simp [hzx]
        · intro z hz
          rw [g1, lookup_upsert]
          simp only [show z ≠ x by omega, ↓reduceIte]
          exact (hfr z (by omega)).1
        · intro z m hz hm
          rw [g1, lookup_upsert] at hm
          by_cases hzx : z = x
          · simp only [hzx, ↓reduceIte, Option.some.injEq] at hm
            subst hm
            exact KNode.deadCount_newLeaf c.i a ws.next
          · simp only [hzx, ↓reduceIte] at hm
            rcases hz with hz | hz
            · exact absurd hz hzx
            · rw [(hfr z hz).1] at hm; cases hm
    | cons a' tail'' =>
      have hv := hfr ws.next (Nat.le_refl _)
      have hstep : ∀ ws1 : W, ws1.nodes = upsert (ws.nodes ++ [(ws.next, (⟨true, []⟩ : KNode))]) x
            ((⟨true, []⟩ : KNode).add c.i (.key a ws.next)) → ws1.next = ws.next + 2 →
          ws1.taken = ws.taken → ws1.vals = ws.vals → ws1.top = ws.top →
          WriterWP (putSegs key (some h) (a' :: tail'') ws.next) c ws1 (fun _ wf =>
            wf.taken = ws.taken ∧ wf.top = ws.top ∧ ws.next ≤ wf.next ∧
            (∀ z, z < ws.next → z ≠ x → wf.nodes.lookup z = ws.nodes.lookup z) ∧
            (∀ z, wf.next ≤ z → wf.nodes.lookup z = none) ∧
            ∀ z m, (z = x ∨ ws.next ≤ z) → wf.nodes.lookup z = some m →
              m.deadCount = 0) := by
        intro ws1 g1 g2 g3 g4 g5
        have hch : ws1.nodes.lookup ws.next = some ⟨true, []⟩ := by
          rw [g1, lookup_upsert]
          simp only [show ws.next ≠ x by omega, ↓reduceIte]
          exact lookup_append_single_self _ _ _ hv.1
        refine writerWP_mono (ih (by simp) ws1 ws.next hch (by rw [g3]; exact hv.2.1) (by omega) ?_) ?_
        · intro z hz
          rw [g2] at hz
          have hz' := hfr z (by omega)
          refine ⟨?_, by rw [g3]; exact hz'.2.1, hz'.2.2.1, hz'.2.2.2.1, by rw [g4]; exact hz'.2.2.2.2⟩
          rw [g1, lookup_upsert]
          simp only [show z ≠ x by omega, ↓reduceIte]
          rw [lookup_append_single_ne _ _ _ _ (by omega)]; exact hz'.1
        · rintro _ wf ⟨k1, k2, k3, k4, k6, k7⟩
          have hxf : wf.nodes.lookup x = some ((⟨true, []⟩ : KNode).add c.i (.key a ws.next)) := by
            rw [k4 x (by omega) (by omega), g1, lookup_upsert]; simp
          refine ⟨by rw [k1, g3], by rw [k2, g5], by omega, ?_, k6, ?_⟩
          · intro z hz hzx
            rw [k4 z (by omega) (by omega), g1, lookup_upsert]
            simp only [hzx, ↓reduceIte]
            exact lookup_append_single_ne _ _ _ _ (by omega)
          · intro z m hz hm
            by_cases hzx : z = x
            · rw [hzx, hxf] at hm
              simp only [Option.some.injEq] at hm
              subst hm
              exact KNode.deadCount_newLeaf c.i a ws.next
            · have hz2 : ws.next ≤ z := by rcases hz with hz | hz; exact absurd hz hzx; exact hz
              by_cases hz0 : z = ws.next
              · exact k7 z m (Or.inl hz0) hm
              · by_cases hz1 : z < ws.next + 2
                · rw [k4 z (by omega) hz0, g1, lookup_upsert] at hm
                  simp only [hzx, ↓reduceIte] at hm
                  rw [lookup_append_single_ne _ _ _ _ hz0, (hfr z hz2).1] at hm
                  cases hm
                · exact k7 z m (Or.inr (by omega)) hm
      rw [putSegs.eq_3 _ _ x a (a' :: tail'') (by simp)]
      unfold setNode
      simp only [writerWP_bind, writerWP_read]
      rw [hf2]
      unfold descendLte
      simp only [writerWP_bind, writerWP_read]
      rw [writerWP_getNode_known _ _ c ws hx]
      simp only [↓reduceIte, writerWP_pure]
      rw [writerWP_getNode_known _ _ c ws hx]
      have hse : ((⟨true, []⟩ : KNode).searchEq c.i a) = none := rfl
      simp only [hse, Option.isSome_some, Bool.not_true, Bool.false_eq_true, ↓reduceIte, writerWP_bind]
      refine writerWP_ghOf_cached x _ c ws hx _ (fun gh => ?_)
      have hroom : (⟨true, []⟩ : KNode).size + 1 < c.p.M := by simp [KNode.size]; omega
      simp only [note, newKey, fresh, putNode, hroom, ↓reduceIte, writerWP_bind, writerWP_modify,
        writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
      split <;>
      · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
        exact hstep _ rfl rfl rfl rfl rfl


set_option maxHeartbeats 800000 in
/-- `liveCounts_put_newSegs` for the dead klongs: a put of a key pre ++ c0 ::
tail whose leaf for c0 has no klong of c0 and has room keeps every node the
writer reads at or below theta dead klongs. -/
theorem dead_put_newSegs (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (c0 h : Nat) (tail : List Nat) (htail : tail ≠ []) (rk0 : NodeId) (w : W)
    (hM : 2 ≤ c.p.M)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk0)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ c0 :: tail) w.top.rootKey,
      w.taken.contains q.1 = false)
    (hids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
      (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next) ∧
      (∀ q ∈ w.vals, q.1 < w.next) ∧ w.top.rootKey < w.next)
    (hbase : ∀ z, w.next ≤ z → knodeOf c.p base z = none ∧ valueOf base z = none)
    (hcur : ∀ L n, (L, c0) ∈ eqVisits (wNode c.p base w) c.i c0 c.p.fuel rk0 →
      wNode c.p base w L = some n → n.leaf = true →
      klongsWf n.ks = true ∧ (∀ s, Klong.time s ∈ n.ks → s ≤ c.i) ∧ n.searchEq c.i c0 = none ∧
      n.size + 1 < c.p.M ∧
      (∀ key', keyWf key' = true →
        (L, c0) ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
        ∃ rest', key' = pre ++ c0 :: rest') ∧
      ∀ c', (L, c') ∉ fromVisits (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey) :
    WriterWP (putKv (.put (pre ++ c0 :: tail) h)) c w (fun _ w' =>
      WDeadN c.p (wNode c.p base w) → WDeadN c.p (wNode c.p base w')) := by
  obtain ⟨hidn, hidv, hidt, hidvals, hidr⟩ := hids
  have _ := hidr
  have hfuel : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  have hvk : ∀ q ∈ eqVisits (wNode c.p base w) c.i c0 c.p.fuel rk0,
      q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ c0 :: tail) w.top.rootKey :=
    fromVisits_append_gen _ _ _ c0 tail pre _ rk0 hrk
  unfold putKv pathClear findRoot pathAdd
  wpSimplify
  generalize hw2 : ({ ({ w with path := [] } : W) with
    path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w2
  have hr02 : ReadsAs c.p base w w2 := by subst hw2; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hw2n : w2.nodes = w.nodes := by subst hw2; rfl
  refine writerWP_putSegs_walk_src c base hvc (pre ++ c0 :: tail) (some h) (c0 :: tail) (by simp) _ pre
    w.top.rootKey rk0 w2 (by rw [hr02.1, hr02.2.2.1]; exact ht) (by rw [hr02.1]; exact hrk)
    (by subst hw2; simp) ?_
  intro w2' hr2' _ hsrc2'
  have hr0 := ReadsAs.trans _ _ _ _ _ hr02 hr2'
  rw [putSegs.eq_3 _ _ rk0 c0 tail htail]
  unfold setNode
  wpSimplify
  have ht1 : ∀ q ∈ eqVisits (wNode c.p base w2') c.i c0 c.p.fuel rk0,
      w2'.taken.contains q.1 = false := by
    rw [hr0.1, hr0.2.2.1]
    exact fun q hq => ht q (hvk q hq)
  refine writerWP_mono (writerWP_and (writerWP_descendLte_reads c0 c base hvc c.p.fuel rk0 w2' ht1)
    (writerWP_descendLte_cache c0 c base hvc c.p.fuel rk0 w2' ht1)) ?_
  intro L w3 ⟨⟨hr23, n, hn, hnl, hlk3, hvisL, _⟩, ⟨_, hsrc3, _⟩⟩
  rw [hr0.1] at hn hvisL
  have hr03 := ReadsAs.trans _ _ _ _ _ hr0 hr23
  have hnext3 : w3.next = w.next := hr03.2.2.2.2
  obtain ⟨hnwf, hnt, hnone, hroom, _, _⟩ := hcur L n hvisL hn hnl
  rw [writerWP_getNode_known L n c _ hlk3]
  simp only [hnone, Option.isSome_some, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    writerWP_bind]
  -- ids
  have hsrcw3 : ∀ z, (w3.nodes.lookup z).isSome = true → z < w.next := by
    intro z hz
    rcases hsrc3 z hz with h1 | h1
    · rcases hsrc2' z h1 with h2 | h2
      · rw [hw2n] at h2; exact hidn z h2
      · exact hidv z h2
    · exact hidv z h1
  have hLlt : L < w.next := hsrcw3 L (by rw [hlk3]; rfl)
  have hntake : ∀ z, w.next ≤ z → w.taken.contains z = false := by
    intro z hz
    cases h' : w.taken.contains z with
    | false => rfl
    | true => have := hidt z h'; omega
  have hvalnone : ∀ z, w.next ≤ z → w.vals.lookup z = none := by
    intro z hz
    apply List.lookup_eq_none_iff.mpr
    intro q' hq'
    have := hidvals q' hq'
    simp only [bne_iff_ne, ne_eq]
    omega
  have hLt : w.taken.contains L = false := ht (L, c0) (hvk _ hvisL)
  let e : KNode := ⟨true, []⟩
  have hrest : ∀ ws : W, ws.nodes = upsert (w3.nodes ++ [(w3.next, e)]) L (n.add c.i (.key c0 w3.next)) →
      ws.next = w3.next + 2 → ws.taken = w3.taken → ws.vals = w3.vals → ws.top = w3.top →
      WriterWP (putSegs (pre ++ c0 :: tail) (some h) tail w3.next) c ws (fun _ w' =>
        WDeadN c.p (wNode c.p base w) → WDeadN c.p (wNode c.p base w')) := by
    intro ws h1 h2 h3 h4 h5
    rw [hnext3] at h1 h2
    rw [hnext3]
    have hw3n : w3.nodes.lookup w.next = none := by
      cases h' : w3.nodes.lookup w.next with
      | none => rfl
      | some _ => have := hsrcw3 _ (by rw [h']; rfl); omega
    have hLne : L ≠ w.next := by omega
    have hlkc : ws.nodes.lookup w.next = some e := by
      rw [h1, lookup_upsert]
      simp only [show w.next ≠ L by omega, ↓reduceIte]
      exact lookup_append_single_self _ _ _ hw3n
    have htk : ∀ z, ws.taken.contains z = w.taken.contains z := by intro z; rw [h3, hr03.2.2.1]
    have hfrW : ∀ z, ws.next ≤ z → ws.nodes.lookup z = none ∧ ws.taken.contains z = false ∧
        knodeOf c.p base z = none ∧ valueOf base z = none ∧ ws.vals.lookup z = none := by
      intro z hz
      rw [h2] at hz
      refine ⟨?_, by rw [htk]; exact hntake z (by omega), (hbase z (by omega)).1,
        (hbase z (by omega)).2, by rw [h4, hr03.2.2.2.1]; exact hvalnone z (by omega)⟩
      rw [h1, lookup_upsert]
      simp only [show z ≠ L by omega, ↓reduceIte]
      rw [lookup_append_single_ne _ _ _ _ (by omega)]
      cases h' : w3.nodes.lookup z with
      | none => rfl
      | some _ => have := hsrcw3 z (by rw [h']; rfl); omega
    refine writerWP_mono (writerWP_and (writerWP_putSegs_new_shape c base (pre ++ c0 :: tail) h hM
      hfuel tail htail ws w.next hlkc (by rw [htk]; exact hntake _ (Nat.le_refl _)) (by omega) hfrW)
      (writerWP_putSegs_new_dead c base (pre ++ c0 :: tail) h hM hfuel tail htail ws w.next hlkc
        (by rw [htk]; exact hntake _ (Nat.le_refl _)) (by omega) hfrW)) ?_
    rintro _ wf ⟨⟨k1, _, _, k4, _, _⟩, ⟨_, _, _, _, _, k8⟩⟩
    have htkf : ∀ z, wf.taken.contains z = w.taken.contains z := by intro z; rw [k1, htk]
    have hLf : wf.nodes.lookup L = some (n.add c.i (.key c0 w.next)) := by
      rw [k4 L (by omega) hLne, h1, lookup_upsert]; simp
    have hwfz : ∀ z, w.next ≤ z → ∀ m, wNode c.p base wf z = some m → wf.nodes.lookup z = some m := by
      intro z hz m hm
      unfold wNode at hm
      rw [htkf, hntake z hz] at hm
      simp only [Bool.false_eq_true, ↓reduceIte] at hm
      cases h' : wf.nodes.lookup z with
      | some m' => rw [h'] at hm; exact hm
      | none => rw [h'] at hm; simp only at hm; rw [(hbase z hz).1] at hm; cases hm
    intro hW h0 z m hm
    by_cases hzL : z = L
    · subst hzL
      have hLw : wNode c.p base wf z = some (n.add c.i (.key c0 w.next)) := by
        simp only [wNode, htkf, hLt, Bool.false_eq_true, ↓reduceIte, hLf]
      rw [hLw] at hm
      cases hm
      exact Nat.le_trans (KNode.deadCount_add_key_new n c.i c0 w.next hnwf
        (KNode.live_lookup_none_of_searchEq n c.i c0 hnwf hnt hnone)) (hW h0 z n hn)
    · by_cases hzb : w.next ≤ z
      · have hm' := hwfz z hzb m hm
        by_cases hz0 : z = w.next
        · rw [k8 z m (Or.inl hz0) hm']; exact Nat.zero_le _
        · by_cases hz1 : z < w.next + 2
          · exfalso
            rw [k4 z (by omega) hz0, h1, lookup_upsert] at hm'
            simp only [show z ≠ L by omega, ↓reduceIte] at hm'
            rw [lookup_append_single_ne _ _ _ _ hz0] at hm'
            cases h' : w3.nodes.lookup z with
            | none => rw [h'] at hm'; cases hm'
            | some _ => have := hsrcw3 z (by rw [h']; rfl); omega
          · rw [k8 z m (Or.inr (by omega)) hm']; exact Nat.zero_le _
      · have hzb' : z < w.next := by omega
        have hx := k4 z (by omega) (by omega)
        rw [h1, lookup_upsert] at hx
        simp only [hzL, ↓reduceIte] at hx
        rw [lookup_append_single_ne _ _ _ _ (by omega)] at hx
        have heq : wNode c.p base wf z = wNode c.p base w z := by
          rw [← hr03.1]
          simp only [wNode, htkf, hr03.2.2.1, hx]
        rw [heq] at hm
        exact hW h0 z m hm
  refine writerWP_ghOf_cached L n c w3 hlk3 _ (fun gh => ?_)
  simp only [note, newKey, fresh, putNode, hroom, ↓reduceIte, writerWP_bind, writerWP_modify,
    writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
  split <;>
  · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
    exact hrest _ rfl rfl rfl rfl rfl


/-- (3b), `QDead`. -/
theorem deadCase_putNewSegsRoom (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M) :
    OpCaseOK p R (QDead p) PutNewSegsRoomCase := by
  intro ts tx _ _ _ _ _ _ _ op _ _ _ w _ hI _ hP
  obtain ⟨pre, c0, tail, h, rk0, L, n, hop, _, hat, hroom⟩ := hP
  subst hop
  obtain ⟨hkeys, hnotpre⟩ := newSeg_leaf_keys hI pre c0 rk0 L hat.2.1 hat.2.2.1
  intro a w' hrun hW
  exact dead_put_newSegs (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre c0 h tail hat.1 rk0 w hM
    hat.2.1 (hI.pathUntaken _) hI.ids hI.fresh
    (newSegAt_one hat (fun L' m => klongsWf m.ks = true ∧
      (∀ s, Klong.time s ∈ m.ks → s ≤ (ctxOf p ts).i) ∧ m.searchEq (ctxOf p ts).i c0 = none ∧
      m.size + 1 < (ctxOf p ts).p.M ∧
      (∀ key', keyWf key' = true →
        (L', c0) ∈ fromVisits (wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w) (ctxOf p ts).i
          (ctxOf p ts).p.fuel key' w.top.rootKey → ∃ rest', key' = pre ++ c0 :: rest') ∧
      ∀ c', (L', c') ∉ fromVisits (wNode (ctxOf p ts).p (viewOf (treeRun p ts)) w) (ctxOf p ts).i
        (ctxOf p ts).p.fuel pre w.top.rootKey)
      ⟨hI.wf L n hat.2.2.2.1, hI.times L n hat.2.2.2.1, hat.2.2.2.2.2, hroom, hkeys, hnotpre⟩)
    a w' hrun hW

end SIS.Tree
