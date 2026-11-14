import SIS.Tree.GetNewSeg
import SIS.Tree.GetSegInPlace

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! A put of a key with more than one segment that has no tree yet (bergdb
024-12, TP10; `OpGetOK`'s rules): the leaf of the last segment that is there gets
a klong to a new segment leaf, each new segment leaf a klong to the next one, and
the last the put's klong (`setNode`'s creation, segment by segment). Every key
reads what it read but the put's key. -/

/-- `getFromR_newSeg` for a new segment leaf ch below which a key's tail reads:
after the leaf cur of the key's segment before got a klong at c0 to ch, from
which only tail reads h, every key reads what it read but pre ++ c0 :: tail,
which reads h. The new nodes and values have ids from b on. -/
theorem getFromR_newSegs (N N2 : NodeId → Option KNode) (V V2 : NodeId → Option Nat)
    (t : Time) (fuel : Nat) (hfuel : 1 ≤ fuel) (root rk0 cur ch b : NodeId) (n : KNode)
    (pre : List Nat) (c0 h : Nat) (tail : List Nat) (htail : tail ≠ [])
    (hrk : segRootR N t fuel pre root = some rk0)
    (hcurv : (cur, c0) ∈ eqVisits N t c0 fuel rk0) (hNcur : N cur = some n) (hnl : n.leaf = true)
    (hnwf : klongsWf n.ks = true) (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ t)
    (hnone : (n.searchEq t c0).map (·.y) = none)
    (hN2cur : N2 cur = some (n.add t (.key c0 ch)))
    (hN2ch : (N2 ch).isSome = true) (hV2ch : V2 ch = none)
    (hsub : ∀ rest', rest' ≠ [] →
      getFromR N2 V2 t fuel rest' ch = if tail == rest' then some h else none)
    (hN2 : ∀ x, x ≠ cur → x < b → N2 x = N x) (hV2 : ∀ a, a < b → V2 a = V a)
    (hrootb : root < b)
    (hwf : ∀ x xn, ReachS N t root x → N x = some xn → klongsWf xn.ks = true)
    (hfr : ∀ x xn c z, ReachS N t root x → N x = some xn → (c, z) ∈ xn.liveAt t → z < b)
    (huniq : ∀ key', keyWf key' = true → (cur, c0) ∈ fromVisits N t fuel key' root →
      ∃ rest', key' = pre ++ c0 :: rest')
    (hpre : ∀ c', (cur, c') ∉ fromVisits N t fuel pre root) :
    ∀ key', keyWf key' = true → getFromR N2 V2 t fuel key' root =
      if pre ++ c0 :: tail == key' then some h else getFromR N V t fuel key' root := by
  -- nodes reached have ids below b
  have hreach_lt : ∀ x, ReachS N t root x → x < b := by
    intro x hx
    cases hx with
    | root => exact hrootb
    | step x' n' c _ hx' hn' hz => exact hfr x' n' c _ hx' hn' hz
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
    · left; exact (hN2 x hxc (hreach_lt x hx)).symm
  have hsome : ∀ y, ReachS N t root y → (N y).isSome = (N2 y).isSome := by
    intro y hy
    by_cases hyc : y = cur
    · rw [hyc, hNcur, hN2cur]; rfl
    · rw [hN2 y hyc (hreach_lt y hy)]
  have hrrk : ReachS N t root rk0 := segRootR_reach N t fuel root hwf pre root rk0 ReachS.root hrk
  have hkeyv : (cur, c0) ∈ fromVisits N t fuel (pre ++ c0 :: tail) root :=
    fromVisits_append_gen N t fuel c0 tail pre root rk0 hrk _ hcurv
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
    have hrchb : ∀ q ∈ eqVisits N t c0 fuel rk0, q.1 < b :=
      fun q hq => hreach_lt q.1 (eqVisits_reach N t root c0 fuel rk0 q.1 q.2 hrrk hq)
    have hg1 : getEqR N t c0 fuel rk0 = none := by
      rw [getEqR_change_leaf N N t c0 cur n hNcur hnl fuel rk0 (fun _ _ _ => rfl) hcurv
        (fun n1 h1 => by rw [hNcur] at h1; cases h1; exact hnl)]
      exact hnone
    have hg2 : getEqR N2 t c0 fuel rk0 = some ch := by
      rw [getEqR_change_leaf N N2 t c0 cur _ hN2cur (by rw [KNode.add_leaf]; exact hnl) fuel rk0
        (fun q hq hqc => (hN2 q.1 hqc (hrchb q hq)).symm) hcurv
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
      have : (pre ++ c0 :: tail == pre ++ [c0]) = false := by simp [htail]
      simp [this]
    | cons d more =>
      simp only [getFromR, hg2, hN2ch, ↓reduceIte]
      rw [hsub (d :: more) (by simp)]
      by_cases ht : tail = d :: more
      · subst ht; simp
      · have h1 : (tail == d :: more) = false := by simpa using ht
        have h2 : (pre ++ c0 :: tail == pre ++ c0 :: d :: more) = false := by simp [ht]
        simp [h1, h2]
  · have hne : (pre ++ c0 :: tail == key') = false := by
      cases hb : (pre ++ c0 :: tail == key') with
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
        exact (hV2 fd.y (hfr x m c fd.y hrx hm (KNode.searchEq_mem m t c fd (hwf x m hrx hm) hfd))).symm

/-- The searches of a new segment leaf with one klong. -/
theorem getEqR_single (N : NodeId → Option KNode) (t : Time) (f2 : Nat) (x : NodeId) (a : Nat)
    (y : NodeId) (hx : N x = some ((⟨true, []⟩ : KNode).add t (.key a y))) (d : Nat) :
    getEqR N t d (f2 + 1) x = if a == d then some y else none := by
  simp only [getEqR, hx, KNode.add_leaf, ↓reduceIte]
  rw [KNode.add_key_searchEq _ t a y (by rfl) (by simp) d]
  rfl

/-- The new segment leaves of a put: from a state in which x is a new empty
segment leaf, `putSegs` of the put's segments from x, tail, gives each but the last
a new segment leaf with a klong to it, and the last segment's leaf the put's klong
to a new value. After it only tail reads from x, and reads h; the nodes and values
with ids below the next id before change only at x. -/
theorem writerWP_putSegs_new (c : Ctx) (base : View BVal) (key : List Nat) (h : Nat)
    (hM : 2 ≤ c.p.M) (hfuel : 1 ≤ c.p.fuel) :
    ∀ (tail : List Nat), tail ≠ [] → ∀ (ws : W) (x : NodeId),
      ws.nodes.lookup x = some ⟨true, []⟩ → ws.taken.contains x = false → x < ws.next →
      (∀ z, ws.next ≤ z → ws.nodes.lookup z = none ∧ ws.taken.contains z = false ∧
        knodeOf c.p base z = none ∧ valueOf base z = none ∧ ws.vals.lookup z = none) →
      WriterWP (putSegs key (some h) tail x) c ws (fun _ wf =>
        wf.taken = ws.taken ∧ wf.top = ws.top ∧ ws.next ≤ wf.next ∧
        (∀ z, z < ws.next → z ≠ x → wf.nodes.lookup z = ws.nodes.lookup z) ∧
        (∀ a, a < ws.next → wf.vals.lookup a = ws.vals.lookup a) ∧
        (∀ z, wf.next ≤ z → wf.nodes.lookup z = none ∧ wf.vals.lookup z = none) ∧
        (wf.nodes.lookup x).isSome = true ∧
        ∀ rest', rest' ≠ [] → getFromR (wNode c.p base wf) (wValue base wf) c.i c.p.fuel rest' x =
          if tail == rest' then some h else none) := by
  obtain ⟨f2, hf2⟩ : ∃ f2, c.p.fuel = f2 + 1 := ⟨c.p.fuel - 1, by omega⟩
  intro tail
  induction tail with
  | nil => intro hne; exact absurd rfl hne
  | cons a tail' ih =>
    intro _ ws x hx htx hxn hfr
    cases tail' with
    | nil =>
      have hpost : ∀ wf : W, wf.nodes = upsert ws.nodes x ((⟨true, []⟩ : KNode).add c.i (.key a ws.next)) →
          wf.vals = ws.vals ++ [(ws.next, h)] → wf.taken = ws.taken → wf.top = ws.top →
          wf.next = ws.next + 2 →
          (wf.taken = ws.taken ∧ wf.top = ws.top ∧ ws.next ≤ wf.next ∧
            (∀ z, z < ws.next → z ≠ x → wf.nodes.lookup z = ws.nodes.lookup z) ∧
            (∀ a, a < ws.next → wf.vals.lookup a = ws.vals.lookup a) ∧
            (∀ z, wf.next ≤ z → wf.nodes.lookup z = none ∧ wf.vals.lookup z = none) ∧
            (wf.nodes.lookup x).isSome = true ∧
            ∀ rest', rest' ≠ [] → getFromR (wNode c.p base wf) (wValue base wf) c.i c.p.fuel rest' x =
              if [a] == rest' then some h else none) := by
        intro wf g1 g2 g3 g4 g5
        refine ⟨g3, g4, by omega, ?_, ?_, ?_, by rw [g1, lookup_upsert]; simp, ?_⟩
        · intro z hz hzx; rw [g1, lookup_upsert]; simp [hzx]
        · intro b hb; rw [g2]; exact lookup_append_single_ne _ _ _ _ (by omega)
        · intro z hz
          refine ⟨?_, ?_⟩
          · rw [g1, lookup_upsert]
            simp only [show z ≠ x by omega, ↓reduceIte]
            exact (hfr z (by omega)).1
          · rw [g2, lookup_append_single_ne _ _ _ _ (by omega)]; exact (hfr z (by omega)).2.2.2.2
        · intro rest' hr
          have hv := hfr ws.next (Nat.le_refl _)
          have hwx : wNode c.p base wf x = some ((⟨true, []⟩ : KNode).add c.i (.key a ws.next)) := by
            simp only [wNode, g3, htx, Bool.false_eq_true, ↓reduceIte, g1, lookup_upsert]
          have hwv : wNode c.p base wf ws.next = none := by
            simp only [wNode, g3, hv.2.1, Bool.false_eq_true, ↓reduceIte, g1, lookup_upsert,
              show ws.next ≠ x by omega, hv.1, hv.2.2.1]
          have hvv : wValue base wf ws.next = some h := by
            simp only [wValue, g3, hv.2.1, Bool.false_eq_true, ↓reduceIte, g2,
              lookup_append_single_self _ _ _ hv.2.2.2.2]
          have hg := getEqR_single (wNode c.p base wf) c.i f2 x a ws.next hwx
          rw [hf2]
          cases rest' with
          | nil => exact absurd rfl hr
          | cons d more =>
            cases more with
            | nil =>
              simp only [getFromR, hg]
              by_cases had : a = d
              · subst had; simp [hvv]
              · have hb : (a == d) = false := by simpa using had
                simp [hb]
            | cons d' more' =>
              simp only [getFromR, hg]
              by_cases had : a = d
              · subst had; simp [hwv]
              · have hb : (a == d) = false := by simpa using had
                simp [hb]
      rw [putSegs.eq_2]
      refine writerWP_mono (post := fun _ wf => wf.nodes = upsert ws.nodes x
          ((⟨true, []⟩ : KNode).add c.i (.key a ws.next)) ∧ wf.vals = ws.vals ++ [(ws.next, h)] ∧
          wf.taken = ws.taken ∧ wf.top = ws.top ∧ wf.next = ws.next + 2) ?_
        (fun _ wf hw => hpost wf hw.1 hw.2.1 hw.2.2.1 hw.2.2.2.1 hw.2.2.2.2)
      unfold setValue
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
    | cons a' tail'' =>
      have hv := hfr ws.next (Nat.le_refl _)
      have hstep : ∀ ws1 : W, ws1.nodes = upsert (ws.nodes ++ [(ws.next, (⟨true, []⟩ : KNode))]) x
            ((⟨true, []⟩ : KNode).add c.i (.key a ws.next)) → ws1.next = ws.next + 2 →
          ws1.taken = ws.taken → ws1.vals = ws.vals → ws1.top = ws.top →
          WriterWP (putSegs key (some h) (a' :: tail'') ws.next) c ws1 (fun _ wf =>
            wf.taken = ws.taken ∧ wf.top = ws.top ∧ ws.next ≤ wf.next ∧
            (∀ z, z < ws.next → z ≠ x → wf.nodes.lookup z = ws.nodes.lookup z) ∧
            (∀ a, a < ws.next → wf.vals.lookup a = ws.vals.lookup a) ∧
            (∀ z, wf.next ≤ z → wf.nodes.lookup z = none ∧ wf.vals.lookup z = none) ∧
            (wf.nodes.lookup x).isSome = true ∧
            ∀ rest', rest' ≠ [] → getFromR (wNode c.p base wf) (wValue base wf) c.i c.p.fuel rest' x =
              if a :: a' :: tail'' == rest' then some h else none) := by
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
        · rintro _ wf ⟨k1, k2, k3, k4, k5, k6, k7, k8⟩
          have hxf : wf.nodes.lookup x = some ((⟨true, []⟩ : KNode).add c.i (.key a ws.next)) := by
            rw [k4 x (by omega) (by omega), g1, lookup_upsert]; simp
          refine ⟨by rw [k1, g3], by rw [k2, g5], by omega, ?_, ?_, k6, by rw [hxf]; rfl, ?_⟩
          · intro z hz hzx
            rw [k4 z (by omega) (by omega), g1, lookup_upsert]
            simp only [hzx, ↓reduceIte]
            exact lookup_append_single_ne _ _ _ _ (by omega)
          · intro b hb
            rw [k5 b (by omega), g4]
          · intro rest' hr
            have htk : ∀ z, wf.taken.contains z = ws.taken.contains z := by intro z; rw [k1, g3]
            have hwx : wNode c.p base wf x = some ((⟨true, []⟩ : KNode).add c.i (.key a ws.next)) := by
              simp only [wNode, htk, htx, Bool.false_eq_true, ↓reduceIte, hxf]
            have hwch : (wNode c.p base wf ws.next).isSome = true := by
              cases hl : wf.nodes.lookup ws.next with
              | none => rw [hl] at k7; cases k7
              | some m =>
                simp only [wNode, htk, hv.2.1, Bool.false_eq_true, ↓reduceIte, hl]; rfl
            have hvch : wValue base wf ws.next = none := by
              simp only [wValue, htk, hv.2.1, Bool.false_eq_true, ↓reduceIte, k5 ws.next (by omega), g4,
                hv.2.2.2.2, hv.2.2.2.1]
            have hg := getEqR_single (wNode c.p base wf) c.i f2 x a ws.next hwx
            cases rest' with
            | nil => exact absurd rfl hr
            | cons d more =>
              cases more with
              | nil =>
                rw [hf2]; simp only [getFromR, hg]
                by_cases had : a = d
                · subst had; simp [hvch]
                · have hb : (a == d) = false := by simpa using had
                  simp [hb]
              | cons d' more' =>
                have hrec := k8 (d' :: more') (by simp)
                rw [hf2] at hrec ⊢
                simp only [getFromR, hg]
                by_cases had : a = d
                · subst had
                  simp only [beq_self_eq_true, ↓reduceIte, hwch]
                  rw [hrec]
                  simp
                · have hb : (a == d) = false := by simpa using had
                  simp [hb]
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
        exact writerWP_mono (hstep _ rfl rfl rfl rfl rfl) (fun _ _ hh => by rw [hf2] at hh; exact hh)

/-- A put of a key pre ++ c0 :: tail whose prefix pre is there and whose leaf
for c0 in the tree of pre has no klong of c0 and has room, with tail of one
segment or more: the new segment leaves, the last with the put's klong, change
the reading by the put alone. The premises are those of `writerWP_put_newSeg`. -/
theorem writerWP_put_newSegs (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
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
      ∀ c', (L, c') ∉ fromVisits (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey)
    (hwf : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → klongsWf xn.ks = true)
    (hlinks : ∀ x xn cc z, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → (cc, z) ∈ xn.liveAt c.i → z < w.next) :
    WriterWP (putKv (.put (pre ++ c0 :: tail) h)) c w (fun _ w' => ∀ key', keyWf key' = true →
      wGet c.p c.i base w' key' =
        if Op.key (.put (pre ++ c0 :: tail) h) == key' then Op.value (.put (pre ++ c0 :: tail) h)
        else wGet c.p c.i base w key') := by
  obtain ⟨hidn, hidv, hidt, hidvals, hidr⟩ := hids
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
      WriterWP (putSegs (pre ++ c0 :: tail) (some h) tail w3.next) c ws (fun _ w' =>
        ∀ key', keyWf key' = true → wGet c.p c.i base w' key' =
          if Op.key (.put (pre ++ c0 :: tail) h) == key' then Op.value (.put (pre ++ c0 :: tail) h)
          else wGet c.p c.i base w key') := by
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
    refine writerWP_mono (writerWP_putSegs_new c base (pre ++ c0 :: tail) h hM hfuel tail htail ws
      w.next hlkc (by rw [htk]; exact hntake _ (Nat.le_refl _)) (by omega) ?_) ?_
    · intro z hz
      rw [h2] at hz
      refine ⟨?_, by rw [htk]; exact hntake z (by omega), (hbase z (by omega)).1,
        (hbase z (by omega)).2, by rw [h4, hr03.2.2.2.1]; exact hvalnone z (by omega)⟩
      rw [h1, lookup_upsert]
      simp only [show z ≠ L by omega, ↓reduceIte]
      rw [lookup_append_single_ne _ _ _ _ (by omega)]
      cases h' : w3.nodes.lookup z with
      | none => rfl
      | some _ => have := hsrcw3 z (by rw [h']; rfl); omega
    rintro _ wf ⟨k1, k2, _, k4, k5, _, k7, k8⟩
    intro key' hkey'
    have htkf : ∀ z, wf.taken.contains z = w.taken.contains z := by intro z; rw [k1, htk]
    have hLf : wf.nodes.lookup L = some (n.add c.i (.key c0 w.next)) := by
      rw [k4 L (by omega) hLne, h1, lookup_upsert]; simp
    unfold wGet
    rw [k2, h5, hr03.2.1]
    have hres := getFromR_newSegs (wNode c.p base w) (wNode c.p base wf) (wValue base w)
      (wValue base wf) c.i c.p.fuel hfuel w.top.rootKey rk0 L w.next w.next n pre c0 h tail htail
      hrk hvisL hn hnl hnwf hnt (by rw [hnone]; rfl)
      (by simp only [wNode, htkf, hLt, Bool.false_eq_true, ↓reduceIte, hLf])
      (by
        cases hl : wf.nodes.lookup w.next with
        | none => rw [hl] at k7; cases k7
        | some m => simp only [wNode, htkf, hntake _ (Nat.le_refl _), Bool.false_eq_true, ↓reduceIte, hl]; rfl)
      (by
        simp only [wValue, htkf, hntake _ (Nat.le_refl _), Bool.false_eq_true, ↓reduceIte,
          k5 w.next (by omega), h4, hr03.2.2.2.1, hvalnone _ (Nat.le_refl _), (hbase w.next (Nat.le_refl _)).2])
      k8
      (by
        intro x hxL hxb
        rw [← hr03.1]
        have hx := k4 x (by omega) (by omega)
        rw [h1, lookup_upsert] at hx
        simp only [hxL, ↓reduceIte] at hx
        rw [lookup_append_single_ne _ _ _ _ (by omega)] at hx
        simp only [wNode, htkf, hr03.2.2.1, hx])
      (by
        intro a ha
        simp only [wValue, htkf, k5 a (by omega), h4, hr03.2.2.2.1])
      hidr hwf hlinks huniq hpre
    rw [hres key' hkey']
    simp only [Op.key, Op.value]
    rfl
  refine writerWP_ghOf_cached L n c w3 hlk3 _ (fun gh => ?_)
  simp only [note, newKey, fresh, putNode, hroom, ↓reduceIte, writerWP_bind, writerWP_modify,
    writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
  split <;>
  · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
    exact hrest _ rfl rfl rfl rfl rfl

/-- `writerWP_put_newSegs` under `PutInv`: a put of a key pre ++ c0 :: tail,
tail of one segment or more, whose prefix is there and whose leaf for c0 has no
klong of c0 and room. -/
theorem writerWP_put_newSegs_inv (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (c0 h : Nat) (tail : List Nat) (htail : tail ≠ []) (rk0 : NodeId) (w : W)
    (hI : PutInv c base w) (hM : 2 ≤ c.p.M)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk0)
    (hcur : ∀ L n, (L, c0) ∈ eqVisits (wNode c.p base w) c.i c0 c.p.fuel rk0 →
      wNode c.p base w L = some n → n.leaf = true →
      n.searchEq c.i c0 = none ∧ n.size + 1 < c.p.M) :
    WriterWP (putKv (.put (pre ++ c0 :: tail) h)) c w (fun _ w' => ∀ key', keyWf key' = true →
      wGet c.p c.i base w' key' =
        if Op.key (.put (pre ++ c0 :: tail) h) == key' then Op.value (.put (pre ++ c0 :: tail) h)
        else wGet c.p c.i base w key') := by
  have hwfR : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → klongsWf xn.ks = true := fun x xn _ hn => hI.wf x xn hn
  have hrkp : TPathK (wNode c.p base w) c.i w.top.rootKey rk0 pre := by
    have := segRootR_tPathK _ _ _ _ hI.wf pre _ [] rk0 TPathK.root hrk
    simpa using this
  refine writerWP_put_newSegs c base hvc pre c0 h tail htail rk0 w hM hrk
    (fun q hq => hI.untaken q.1 (fromVisits_reach _ _ _ _ hwfR _ _ q.1 q.2 ReachS.root hq))
    hI.ids hI.fresh ?_ hwfR hI.links
  intro L n hL hn hnl
  obtain ⟨hnone, hroom⟩ := hcur L n hL hn hnl
  have hLp := (eqVisits_tPathK _ _ _ c0 _ rk0 pre hrkp L c0 hL).1
  refine ⟨hI.wf L n hn, hI.times L n hn, hnone, hroom, ?_, ?_⟩
  · intro key' _ h1
    obtain ⟨j, hxj, hj⟩ := fromVisits_tPathK _ _ _ _ hI.wf key' _ [] TPathK.root L c0 h1
    simp only [List.nil_append] at hxj
    have htake : key'.take j = pre := tPathK_unique _ _ _ hI.tree L _ hxj pre hLp
    have hsplit : key' = pre ++ key'.drop j := by rw [← htake, List.take_append_drop]
    have hdrop : (key'.drop j).head? = some c0 := by rw [List.head?_drop]; exact hj
    cases hd : key'.drop j with
    | nil => rw [hd] at hdrop; cases hdrop
    | cons d rest =>
      rw [hd] at hdrop hsplit
      simp only [List.head?_cons, Option.some.injEq] at hdrop
      subst hdrop
      exact ⟨rest, hsplit⟩
  · intro c' h1
    obtain ⟨j, hxj, hj⟩ := fromVisits_tPathK _ _ _ _ hI.wf pre _ [] TPathK.root L c' h1
    simp only [List.nil_append] at hxj
    have htake : pre.take j = pre := tPathK_unique _ _ _ hI.tree L _ hxj pre hLp
    have hjlt : j < pre.length := by
      have := List.getElem?_eq_some_iff.mp hj
      exact this.1
    have hlen := congrArg List.length htake
    simp only [List.length_take] at hlen
    omega

end SIS.Tree
