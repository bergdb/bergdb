import SIS.Tree.GetSegRoot

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! A put of a key whose last segment has no tree yet (bergdb 024-12, TP10;
`OpGetOK`'s rules): the leaf of the segment before, with room, gets a klong to a
new segment leaf, which gets the put's klong (`setNode`'s creation). Every key
reads what it read but the put's key: a key through the new klong read nothing
before and reads nothing after, but the put's. -/

theorem getFromR_append_gen (N : NodeId → Option KNode) (V : NodeId → Option Nat) (t : Time)
    (fuel : Nat) (s : List Nat) (hs : s ≠ []) :
    ∀ (pre : List Nat) (r : NodeId), getFromR N V t fuel (pre ++ s) r =
      (segRootR N t fuel pre r).bind (fun rk => getFromR N V t fuel s rk) := by
  intro pre
  induction pre with
  | nil => intro r; rfl
  | cons c rest ih =>
    intro r
    have hne : rest ++ s ≠ [] := by simp [hs]
    obtain ⟨d, rest', he⟩ : ∃ d rest', rest ++ s = d :: rest' := by
      cases h : rest ++ s with
      | nil => exact absurd h hne
      | cons d rest' => exact ⟨d, rest', rfl⟩
    simp only [List.cons_append]
    rw [he]
    simp only [getFromR, segRootR]
    rw [← he]
    cases getEqR N t c fuel r with
    | none => rfl
    | some y =>
      simp only
      split
      · exact ih y
      · rfl

/-- The walk down a prefix is the same in two readers that agree at its visits
and on which reached nodes are key nodes. -/
theorem segRootR_frame_reach (N1 N2 : NodeId → Option KNode) (t : Time) (fuel : Nat)
    (r0 : NodeId) (hwf : ∀ x xn, ReachS N1 t r0 x → N1 x = some xn → klongsWf xn.ks = true)
    (hsome : ∀ y, ReachS N1 t r0 y → (N1 y).isSome = (N2 y).isSome) :
    ∀ (pre : List Nat) (r : NodeId), ReachS N1 t r0 r →
      (∀ q ∈ fromVisits N1 t fuel pre r, AgreeAt N1 N2 t q.1 q.2) →
      segRootR N1 t fuel pre r = segRootR N2 t fuel pre r := by
  intro pre
  induction pre with
  | nil => intro r _ _; rfl
  | cons c rest ih =>
    intro r hr h
    have hev : ∀ q ∈ eqVisits N1 t c fuel r, AgreeAt N1 N2 t q.1 q.2 := by
      intro q hq
      apply h q
      cases rest with
      | nil => exact hq
      | cons d rest' => simp only [fromVisits]; exact List.mem_append_left _ hq
    obtain ⟨he, _⟩ := getEqR_frame N1 N2 t c fuel r hev
    simp only [segRootR]
    rw [← he]
    cases hg : getEqR N1 t c fuel r with
    | none => rfl
    | some y =>
      simp only
      have hy : ReachS N1 t r0 y := getEqR_reach N1 t r0 c hwf fuel r y hr hg
      rw [← hsome y hy]
      split
      · apply ih y hy
        intro q hq
        apply h q
        cases rest with
        | nil => simp [fromVisits] at hq
        | cons d rest' =>
          simp only [fromVisits, hg]
          exact List.mem_append_right _ hq
      · rfl

/-- After the leaf cur of the key's segment before got a klong at c0 to the new
segment leaf ch, which holds the put's klong at cl to the new value v, every
key reads what it read but the key, which reads the put's value. -/
theorem getFromR_newSeg (N N2 : NodeId → Option KNode) (V V2 : NodeId → Option Nat)
    (t : Time) (fuel : Nat) (hfuel : 1 ≤ fuel) (root rk0 cur ch v : NodeId) (n cn : KNode)
    (pre : List Nat) (c0 cl h : Nat)
    (hrk : segRootR N t fuel pre root = some rk0)
    (hcurv : (cur, c0) ∈ eqVisits N t c0 fuel rk0) (hNcur : N cur = some n) (hnl : n.leaf = true)
    (hnwf : klongsWf n.ks = true) (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ t)
    (hnone : (n.searchEq t c0).map (·.y) = none)
    (hN2cur : N2 cur = some (n.add t (.key c0 ch)))
    (hN2ch : N2 ch = some cn) (hcnl : cn.leaf = true)
    (hcns : ∀ c', (cn.searchEq t c').map (·.y) = if cl == c' then some v else none)
    (hN2 : ∀ x, x ≠ cur → x ≠ ch → N2 x = N x) (hN2v : N2 v = none)
    (hV2v : V2 v = some h) (hV2 : ∀ a, a ≠ v → V2 a = V a) (hV2ch : V2 ch = none)
    (hcurch : cur ≠ ch) (hrootch : root ≠ ch)
    (hwf : ∀ x xn, ReachS N t root x → N x = some xn → klongsWf xn.ks = true)
    (hfr : ∀ x xn c z, ReachS N t root x → N x = some xn → (c, z) ∈ xn.liveAt t →
      z ≠ ch ∧ z ≠ v)
    (huniq : ∀ key', keyWf key' = true → (cur, c0) ∈ fromVisits N t fuel key' root →
      ∃ rest', key' = pre ++ c0 :: rest')
    (hpre : ∀ c', (cur, c') ∉ fromVisits N t fuel pre root) :
    ∀ key', keyWf key' = true → getFromR N2 V2 t fuel key' root =
      if pre ++ [c0, cl] == key' then some h else getFromR N V t fuel key' root := by
  -- nodes reached are not the new leaf
  have hreach_ne : ∀ x, ReachS N t root x → x ≠ ch := by
    intro x hx
    cases hx with
    | root => exact hrootch
    | step x' n' c _ hx' hn' hz => exact (hfr x' n' c _ hx' hn' hz).1
  have hagree : ∀ x c, ReachS N t root x → (x = cur → c ≠ c0) → AgreeAt N N2 t x c := by
    intro x c hx hc
    by_cases hxc : x = cur
    · subst hxc
      right
      refine ⟨n, n.add t (.key c0 ch), hNcur, hN2cur, hnl, by rw [KNode.add_leaf]; exact hnl, ?_⟩
      rw [KNode.add_key_searchEq n t c0 ch hnwf hnt c]
      have : (c0 == c) = false := by
        cases hb : (c0 == c) with
        | false => rfl
        | true => exact absurd (beq_iff_eq.mp hb).symm (hc rfl)
      rw [this]; rfl
    · left; exact (hN2 x hxc (hreach_ne x hx)).symm
  have hsome : ∀ y, ReachS N t root y → (N y).isSome = (N2 y).isSome := by
    intro y hy
    by_cases hyc : y = cur
    · rw [hyc, hNcur, hN2cur]; rfl
    · rw [hN2 y hyc (hreach_ne y hy)]
  have hrrk : ReachS N t root rk0 := segRootR_reach N t fuel root hwf pre root rk0 ReachS.root hrk
  have hkeyv : (cur, c0) ∈ fromVisits N t fuel (pre ++ [c0, cl]) root :=
    fromVisits_append_gen N t fuel c0 [cl] pre root rk0 hrk _ hcurv
  intro key' hkey'
  by_cases hv : (cur, c0) ∈ fromVisits N t fuel key' root
  · obtain ⟨rest', hk⟩ := huniq key' hkey' hv
    subst hk
    have hs : c0 :: rest' ≠ [] := by simp
    rw [getFromR_append_gen N2 V2 t fuel _ hs, getFromR_append_gen N V t fuel _ hs, hrk]
    rw [← segRootR_frame_reach N N2 t fuel root hwf hsome pre root ReachS.root (by
      intro q hq
      exact hagree q.1 q.2 (fromVisits_reach N t fuel root hwf pre root q.1 q.2 ReachS.root hq)
        (fun he => absurd (he ▸ hq) (hpre q.2))), hrk]
    simp only [Option.bind_some]
    -- the descents of c0 from rk0: none before, the new leaf after
    have hg1 : getEqR N t c0 fuel rk0 = none := by
      rw [getEqR_change_leaf N N t c0 cur n hNcur hnl fuel rk0 (fun _ _ _ => rfl) hcurv
        (fun n1 h1 => by rw [hNcur] at h1; cases h1; exact hnl)]
      exact hnone
    have hg2 : getEqR N2 t c0 fuel rk0 = some ch := by
      rw [getEqR_change_leaf N N2 t c0 cur _ hN2cur (by rw [KNode.add_leaf]; exact hnl) fuel rk0
        (fun q hq hqc => (hN2 q.1 hqc (hreach_ne q.1
          (eqVisits_reach N t root c0 fuel rk0 q.1 q.2 hrrk hq))).symm) hcurv
        (fun n1 h1 => by rw [hNcur] at h1; cases h1; exact hnl)]
      rw [KNode.add_key_searchEq n t c0 ch hnwf hnt c0]
      simp
    have hN : getFromR N V t fuel (c0 :: rest') rk0 = none := by
      cases rest' with
      | nil => simp only [getFromR, hg1]; rfl
      | cons d more => simp only [getFromR, hg1]
    rw [hN]
    cases rest' with
    | nil =>
      simp only [getFromR, hg2, Option.bind_some, hV2ch]
      have : (pre ++ [c0, cl] == pre ++ [c0]) = false := by simp
      simp [this]
    | cons d more =>
      simp only [getFromR, hg2, hN2ch, Option.isSome_some, ↓reduceIte]
      obtain ⟨f2, hf2⟩ : ∃ f2, fuel = f2 + 1 := ⟨fuel - 1, by omega⟩
      have hgd : getEqR N2 t d fuel ch = if cl == d then some v else none := by
        rw [hf2]; simp only [getEqR, hN2ch, hcnl, ↓reduceIte]; exact hcns d
      cases more with
      | nil =>
        simp only [getFromR, hgd]
        by_cases hd : cl = d
        · subst hd; simp [hV2v]
        · have hb : (cl == d) = false := by simpa using hd
          have hne : (pre ++ [c0, cl] == pre ++ [c0, d]) = false := by simp [hd]
          simp [hb, hne]
      | cons e more' =>
        simp only [getFromR, hgd]
        have hne : (pre ++ [c0, cl] == pre ++ c0 :: d :: e :: more') = false := by simp
        by_cases hd : cl = d
        · subst hd; simp [hN2v, hne]
        · have hb : (cl == d) = false := by simpa using hd
          simp [hb, hne]
  · have hne : (pre ++ [c0, cl] == key') = false := by
      cases hb : (pre ++ [c0, cl] == key') with
      | false => rfl
      | true => rw [beq_iff_eq.mp hb] at hkeyv; exact absurd hkeyv hv
    rw [hne]
    simp only [Bool.false_eq_true, ↓reduceIte]
    symm
    apply getFromR_frame N N2 V V2 t fuel hfuel key' root
    · intro q hq
      exact hagree q.1 q.2 (fromVisits_reach N t fuel root hwf key' root q.1 q.2 ReachS.root hq)
        (fun he hc => hv (by rw [← he, ← hc]; exact hq))
    · intro x c m y hx hm _ hs
      have hrx := fromVisits_reach N t fuel root hwf key' root x c ReachS.root hx
      cases hfd : m.searchEq t c with
      | none => rw [hfd] at hs; cases hs
      | some fd =>
        rw [hfd] at hs
        simp only [Option.map_some, Option.some.injEq] at hs
        subst hs
        exact (hV2 fd.y (hfr x m c fd.y hrx hm (KNode.searchEq_mem m t c fd (hwf x m hrx hm) hfd)).2).symm

theorem deadOver_empty_add (p : Params) (t : Time) (cl : Nat) (v : NodeId) :
    deadOver p ((⟨true, []⟩ : KNode).add t (.key cl v)) = false := by
  simp [deadOver, KNode.deadCount, KNode.add, KNode.lastBitmap, KNode.lastTime, lastBitmapOf]

/-- A put of a key pre ++ [c0, cl] whose prefix pre is there and whose leaf for
c0 in the tree of pre has no klong of c0 and has room: the new segment leaf with
the put's klong changes the reading by the put alone. The premises are those of
the other rules, the leaf not on the prefix's walk, and the keys through its c0
of the form pre ++ c0 :: _. -/
theorem writerWP_put_newSeg (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (c0 cl h : Nat) (rk0 : NodeId) (w : W) (hM : 2 ≤ c.p.M)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk0)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [c0, cl]) w.top.rootKey,
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
      ∀ c', (L, c') ∉ fromVisits (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey)
    (hwf : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → klongsWf xn.ks = true)
    (hlinks : ∀ x xn cc z, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → (cc, z) ∈ xn.liveAt c.i → z < w.next) :
    WriterWP (putKv (.put (pre ++ [c0, cl]) h)) c w (fun _ w' => ∀ key', keyWf key' = true →
      wGet c.p c.i base w' key' =
        if Op.key (.put (pre ++ [c0, cl]) h) == key' then Op.value (.put (pre ++ [c0, cl]) h)
        else wGet c.p c.i base w key') := by
  obtain ⟨hidn, hidv, hidt, hidvals, hidr⟩ := hids
  have hfuel : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  have hvk : ∀ q ∈ eqVisits (wNode c.p base w) c.i c0 c.p.fuel rk0,
      q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [c0, cl]) w.top.rootKey :=
    fromVisits_append_gen _ _ _ c0 [cl] pre _ rk0 hrk
  unfold putKv pathClear findRoot pathAdd
  wpSimplify
  generalize hw2 : ({ ({ w with path := [] } : W) with
    path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w2
  have hr02 : ReadsAs c.p base w w2 := by subst hw2; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hw2n : w2.nodes = w.nodes := by subst hw2; rfl
  refine writerWP_putSegs_walk_src c base hvc (pre ++ [c0, cl]) (some h) [c0, cl] (by simp) _ pre
    w.top.rootKey rk0 w2 (by rw [hr02.1, hr02.2.2.1]; exact ht) (by rw [hr02.1]; exact hrk)
    (by subst hw2; simp) ?_
  intro w2' hr2' _ hsrc2'
  have hr0 := ReadsAs.trans _ _ _ _ _ hr02 hr2'
  rw [putSegs.eq_3 _ _ rk0 c0 [cl] (by simp)]
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
  obtain ⟨hnwf, hnt, hnone, hroom, huniq, hpre⟩ := hcur L n hvisL hn hnl
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
      WriterWP (setValue w3.next cl (pre ++ [c0, cl]) (some h)) c ws (fun _ w' =>
        ∀ key', keyWf key' = true → wGet c.p c.i base w' key' =
          if Op.key (.put (pre ++ [c0, cl]) h) == key' then Op.value (.put (pre ++ [c0, cl]) h)
          else wGet c.p c.i base w key') := by
    intro ws h1 h2 h3 h4 h5
    have hlkc : ws.nodes.lookup w3.next = some e := by
      rw [h1, lookup_upsert]
      simp only [show w3.next ≠ L by omega, ↓reduceIte]
      rw [List.lookup_append]
      have : w3.nodes.lookup w3.next = none := by
        cases h' : w3.nodes.lookup w3.next with
        | none => rfl
        | some _ => have := hsrcw3 _ (by rw [h']; rfl); omega
      rw [this]; simp [List.lookup]
    obtain ⟨f2, hf2⟩ : ∃ f2, c.p.fuel = f2 + 1 := ⟨c.p.fuel - 1, by omega⟩
    unfold setValue
    simp only [writerWP_bind, writerWP_read]
    rw [hf2]
    unfold descendLte
    simp only [writerWP_bind, writerWP_read]
    rw [writerWP_getNode_known _ e c ws hlkc]
    simp only [e, ↓reduceIte, writerWP_pure]
    unfold newValue fresh
    simp only [writerWP_bind, writerWP_get, writerWP_set, writerWP_modify, writerWP_pure]
    rw [writerWP_getNode_known _ e c _ (by simpa using hlkc)]
    have hcond : (decide ((e.size) + 1 < c.p.M) && !deadOver c.p (e.add c.i (.key cl ws.next))) = true := by
      simp only [e, KNode.size, List.length_nil, deadOver_empty_add]
      simp; omega
    have hfinal : ∀ wf : W, wf.nodes = upsert ws.nodes w3.next (e.add c.i (.key cl ws.next)) →
        wf.vals = ws.vals ++ [(ws.next, h)] → wf.taken = ws.taken → wf.top = ws.top →
        ∀ key', keyWf key' = true → wGet c.p c.i base wf key' =
          if Op.key (.put (pre ++ [c0, cl]) h) == key' then Op.value (.put (pre ++ [c0, cl]) h)
          else wGet c.p c.i base w key' := by
      intro wf g1 g2 g3 g4 key' hkey'
      rw [h2, hnext3] at g1 g2
      rw [h1, hnext3] at g1
      rw [h4, hr03.2.2.2.1] at g2
      rw [h3, hr03.2.2.1] at g3
      rw [h5, hr03.2.1] at g4
      have hLne : L ≠ w.next := by omega
      have hw3n : w3.nodes.lookup w.next = none := by
        cases h' : w3.nodes.lookup w.next with
        | none => rfl
        | some _ => have := hsrcw3 _ (by rw [h']; rfl); omega
      have hw3v : w3.nodes.lookup (w.next + 2) = none := by
        cases h' : w3.nodes.lookup (w.next + 2) with
        | none => rfl
        | some _ => have := hsrcw3 _ (by rw [h']; rfl); omega
      have hlookf : ∀ x, wf.nodes.lookup x =
          if x = w.next then some (e.add c.i (.key cl (w.next + 2)))
          else if x = L then some (n.add c.i (.key c0 w.next)) else w3.nodes.lookup x := by
        intro x
        rw [g1, lookup_upsert, lookup_upsert, List.lookup_append]
        by_cases hx1 : x = w.next
        · simp [hx1]
        · simp only [hx1, ↓reduceIte]
          by_cases hx2 : x = L
          · simp [hx2]
          · simp only [hx2, ↓reduceIte]
            cases h' : w3.nodes.lookup x with
            | some _ => rfl
            | none =>
              show (none : Option KNode).or ([(w.next, e)].lookup x) = none
              rw [lookup_cons_ne _ _ _ _ hx1]; rfl
      unfold wGet
      rw [g4]
      have hres := getFromR_newSeg (wNode c.p base w) (wNode c.p base wf) (wValue base w)
        (wValue base wf) c.i c.p.fuel hfuel w.top.rootKey rk0 L w.next (w.next + 2) n
        (e.add c.i (.key cl (w.next + 2))) pre c0 cl h hrk hvisL hn hnl hnwf hnt
        (by rw [hnone]; rfl)
        (by simp only [wNode, g3, hLt, Bool.false_eq_true, ↓reduceIte, hlookf, hLne])
        (by
          have : wf.taken.contains w.next = false := by rw [g3]; exact hntake _ (Nat.le_refl _)
          simp only [wNode, this, Bool.false_eq_true, ↓reduceIte, hlookf])
        (by rw [KNode.add_leaf])
        (by
          intro c'
          rw [KNode.add_key_searchEq e c.i cl (w.next + 2) (by rfl) (by simp [e]) c']
          rfl)
        (by
          intro x hxL hxc
          rw [← hr03.1]
          simp only [wNode, g3, hr03.2.2.1, hlookf, hxc, hxL, ↓reduceIte])
        (by
          have : wf.taken.contains (w.next + 2) = false := by rw [g3]; exact hntake _ (by omega)
          simp only [wNode, this, Bool.false_eq_true, ↓reduceIte, hlookf,
            show w.next + 2 ≠ w.next by omega, show w.next + 2 ≠ L by omega, hw3v,
            (hbase (w.next + 2) (by omega)).1])
        (by
          have hvt : wf.taken.contains (w.next + 2) = false := by rw [g3]; exact hntake _ (by omega)
          simp only [wValue, hvt, Bool.false_eq_true, ↓reduceIte, g2,
            lookup_append_single_self _ _ _ (hvalnone (w.next + 2) (by omega))])
        (by
          intro a ha
          simp only [wValue, g3, g2, lookup_append_single_ne _ _ _ _ ha])
        (by
          have hvt : wf.taken.contains w.next = false := by rw [g3]; exact hntake _ (Nat.le_refl _)
          simp only [wValue, hvt, Bool.false_eq_true, ↓reduceIte, g2,
            lookup_append_single_ne _ _ _ _ (by omega : w.next ≠ w.next + 2),
            hvalnone _ (Nat.le_refl _), (hbase w.next (Nat.le_refl _)).2])
        hLne (by omega) hwf
        (fun x xn cc z hx hxn hz => by
          have := hlinks x xn cc z hx hxn hz
          exact ⟨by omega, by omega⟩)
        huniq hpre
      rw [hres key' hkey']
      simp only [Op.key, Op.value]
      rfl
    simp only [hcond, ↓reduceIte, putNode, writerWP_bind, writerWP_modify, writerWP_pure]
    exact hfinal _ rfl rfl rfl rfl
  refine writerWP_ghOf_cached L n c w3 hlk3 _ (fun gh => ?_)
  simp only [note, newKey, fresh, putNode, hroom, ↓reduceIte, writerWP_bind, writerWP_modify,
    writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
  split <;>
  · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
    rw [putSegs.eq_2]
    exact hrest _ rfl rfl rfl rfl rfl

end SIS.Tree
