/-
The contract package (bergdb 030-04): a scan is right. On a tree that meets
the invariants, `scan` gives what a scan of the plain map of the tree's
contents gives (`scan_contents`): the setup's chain is at the start key
(Setup.lean), and the loop gives what is after the chain (Chain.lean).
-/
import Contract.Proof.Setup

namespace Contract

variable {s : Tree}

/-- A key is within the scan's start. -/
def inStart (req : ScanReq) (k : Key) : Bool :=
  match req.start with
  | none => true
  | some st =>
    if req.forward then (if req.inclusive then !keyLt k st else keyLt st k)
    else (if req.inclusive then !keyLt st k else keyLt k st)

theorem inRange_eq (req : ScanReq) (k : Key) : inRange req k = (inStart req k && inEnd req k) :=
  rfl

theorem setupGo_first (fwd : Bool) (Kp : List Pos) :
    ∀ (f : Nat) (x : NodeId) (index : Nat) (hasDiff : Bool) (ch : Chain),
      (setupGo s fwd Kp f x index hasDiff ch).first = ch.first
  | 0, _, _, _, _ => rfl
  | f + 1, x, index, hasDiff, ch => by
    unfold setupGo
    split
    · split
      · rfl
      · split
        · rfl
        · split
          · rw [setupGo_first]
          · rw [setupGo_first]
    · rfl

theorem chainEq_true {ch : Chain} {K : Key} (h : chainEq ch (some K) = true) :
    ∃ x c above, ch.links = (x, Pos.at c) :: above ∧ K = ch.segs ++ [c] := by
  unfold chainEq at h
  cases hl : ch.links with
  | nil => simp [hl] at h
  | cons a above =>
    obtain ⟨x, p⟩ := a
    cases p with
    | lo => simp [hl] at h
    | hi => simp [hl] at h
    | «at» lc =>
      simp only [hl, List.head?_cons, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      refine ⟨x, lc, above, rfl, ?_⟩
      have h4 : K = K.take ch.segs.length ++ K.drop ch.segs.length :=
        (List.take_append_drop _ _).symm
      have h5 : (K.drop ch.segs.length).length = 1 := by
        rw [List.length_drop]; omega
      obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp h5
      rw [← h2, ha] at h4
      rw [h4] at h3
      simp only [List.getLast?_concat, Option.some.injEq] at h3
      rw [h4, h3]

theorem chainEq_of {ch : Chain} {x : NodeId} {c : Nat} {above : List (NodeId × Pos)}
    (hl : ch.links = (x, Pos.at c) :: above) : chainEq ch (some (ch.segs ++ [c])) = true := by
  unfold chainEq
  simp [hl]

/-- The klongs at or below a position, backward: the one at it, then those
below it. -/
theorem pend_incl_bwd (n : KNode) (p : Pos) :
    pend false true n p =
      ((live n.ks).filter (fun cy => p.is cy.1)).reverse ++ pend false false n p := by
  simp only [pend, ite_true, Bool.false_eq_true, ite_false]
  have h3 := sorted_split3 (live_sorted n.ks) p
  have e1 : ((live n.ks).filter (fun cy => p.above cy.1)).filter (fun cy => !p.below cy.1) =
      (live n.ks).filter (fun cy => p.above cy.1) := by
    rw [List.filter_eq_self]
    intro a ha
    have := (Pos.above_iff p a.1).mp (List.mem_filter.mp ha).2
    rw [Bool.not_eq_true', ← Bool.not_eq_true, Pos.below_iff]
    exact not_lt_of_gt this
  have e2 : ((live n.ks).filter (fun cy => p.is cy.1)).filter (fun cy => !p.below cy.1) =
      (live n.ks).filter (fun cy => p.is cy.1) := by
    rw [List.filter_eq_self]
    intro a ha
    have := (Pos.is_iff p a.1).mp (List.mem_filter.mp ha).2
    rw [Bool.not_eq_true', ← Bool.not_eq_true, Pos.below_iff, this]
    exact lt_irrefl _
  have e3 : ((live n.ks).filter (fun cy => p.below cy.1)).filter (fun cy => !p.below cy.1) = [] := by
    rw [List.filter_eq_nil_iff]
    intro a ha
    simp [(List.mem_filter.mp ha).2]
  conv_lhs => rw [h3]
  rw [List.filter_append, List.filter_append, e1, e2, e3, List.append_nil, List.reverse_append]

/-- With the klong at the chain: what is at the chain, then what is after
it, in the scan's direction. -/
theorem restX_true (fwd : Bool) (links : List (NodeId × Pos)) (segs : List Nat) :
    restX s fwd true links segs = dir fwd (atOf s links segs) ++ restD s fwd links segs := by
  cases links with
  | nil => cases fwd <;> rfl
  | cons a above =>
    obtain ⟨x, p⟩ := a
    simp only [restX, atOf, restD]
    cases ho : s.obj x with
    | none => cases fwd <;> rfl
    | some o =>
      cases o with
      | val v => cases fwd <;> rfl
      | key n =>
        simp only
        cases fwd with
        | true =>
          rw [pend_incl_fwd]
          simp [entD, ent, dir]
        | false =>
          rw [pend_incl_bwd]
          have := entD_dir (s := s) false segs n ((live n.ks).filter (fun cy => p.is cy.1))
          simp only [dir, Bool.false_eq_true, ite_false] at this ⊢
          rw [← this]
          simp [entD]

theorem filter_const {α : Type} {l : List α} {p : α → Bool} {b : Bool} (h : ∀ a ∈ l, p a = b) :
    l.filter p = if b then l else [] := by
  cases b with
  | true => simp only [ite_true]; exact List.filter_eq_self.mpr h
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    rw [List.filter_eq_nil_iff]
    intro a ha
    simp [h a ha]

/-- A filter of what is before, at and after a chain, when each part is kept
or dropped whole. -/
theorem filter3 {L Bf At Af : List (Key × Nat)} (hL : L = Bf.reverse ++ At ++ Af)
    (p : Key × Nat → Bool) {b1 b2 b3 : Bool} (hB : ∀ kv ∈ Bf, p kv = b1)
    (hA : ∀ kv ∈ At, p kv = b2) (hF : ∀ kv ∈ Af, p kv = b3) :
    L.filter p = (if b1 then Bf.reverse else []) ++ (if b2 then At else []) ++
      (if b3 then Af else []) := by
  rw [hL, List.filter_append, List.filter_append,
    filter_const (l := Bf.reverse) (fun a ha => hB a (List.mem_reverse.mp ha)), filter_const hA,
    filter_const hF]

/-- A chain that meets `SetupOK` for the scan's start key: what the first
`next` has before it is what the tree holds within the scan's start, in the
scan's direction. -/
theorem start_core {r : NodeId} (hG : Good s r 0 none) (req : ScanReq)
    {links : List (NodeId × Pos)} {segs : List Nat} {eqm : Bool} {Kp : List Pos}
    (hKp : Kp = startPos req)
    (hS : SetupOK s r req.forward Kp
      { links := links, segs := segs, first := true, eqMatch := eqm }) :
    restX s req.forward (true && req.inclusive &&
        chainEq { links := links, segs := segs, first := true, eqMatch := eqm } req.start)
      links segs =
      dir req.forward ((L s r).filter (fun kv => inStart req kv.1)) := by
  obtain ⟨start, incl, fwd, endKey, endIncl⟩ := req
  obtain ⟨hpath, hbef, haft, hat⟩ := hS
  simp only [startPos] at hpath hbef haft hat hKp ⊢
  simp only [Bool.true_and]
  have hL := hpath.split hG
  -- keys of the tree have a segment
  have hne : ∀ kv ∈ L s r, kv.1 ≠ [] := by
    intro kv hkv
    obtain ⟨d, r', hd, _⟩ := hG.range kv.1 kv.2 hkv
    rw [hd]; simp
  have hmemB : ∀ kv ∈ restD s false links segs, kv ∈ L s r := by
    intro kv hkv; rw [hL]; simp [hkv]
  have hmemA : ∀ kv ∈ atOf s links segs, kv ∈ L s r := by
    intro kv hkv; rw [hL]; simp [hkv]
  have hmemF : ∀ kv ∈ restD s true links segs, kv ∈ L s r := by
    intro kv hkv; rw [hL]; simp [hkv]
  cases start with
  | none =>
    -- no start key: the chain is before every key, or backward after every key
    subst hKp
    have hceq : chainEq { links := links, segs := segs, first := true, eqMatch := eqm } none =
        false := by
      unfold chainEq; rfl
    simp only [hceq, Bool.and_false, restX_false, inStart, List.filter_true]
    rcases hat with ⟨hside, _⟩ | ⟨x, c, above, v, _, _, hkp⟩
    · cases fwd with
      | true =>
        have hB0 : restD s false links segs = [] := by
          rw [List.eq_nil_iff_forall_not_mem]
          intro kv hkv
          have h1 := hbef kv hkv
          have h2 := hne kv (hmemB kv hkv)
          cases hk : kv.1 with
          | nil => exact h2 hk
          | cons d r' => rw [hk] at h1; simp [kp, List.cons_lt_cons_iff, not_at_lt_lo] at h1
        have hA0 : atOf s links segs = [] := by
          rw [List.eq_nil_iff_forall_not_mem]
          intro kv hkv
          have h1 := hside kv hkv
          have h2 := hne kv (hmemA kv hkv)
          simp only [Side, ite_true] at h1
          cases hk : kv.1 with
          | nil => exact h2 hk
          | cons d r' => rw [hk] at h1; simp [kp, List.cons_lt_cons_iff, not_at_lt_lo] at h1
        simp [dir, hL, hB0, hA0]
      | false =>
        have hF0 : restD s true links segs = [] := by
          rw [List.eq_nil_iff_forall_not_mem]
          intro kv hkv
          have h1 := haft kv hkv
          cases hk : kv.1 with
          | nil => rw [hk] at h1; simp [kp] at h1
          | cons d r' => rw [hk] at h1; simp [kp, List.cons_lt_cons_iff, not_hi_lt_at] at h1
        have hA0 : atOf s links segs = [] := by
          rw [List.eq_nil_iff_forall_not_mem]
          intro kv hkv
          have h1 := hside kv hkv
          simp only [Side, Bool.false_eq_true, ite_false] at h1
          cases hk : kv.1 with
          | nil => rw [hk] at h1; simp [kp] at h1
          | cons d r' => rw [hk] at h1; simp [kp, List.cons_lt_cons_iff, not_hi_lt_at] at h1
        simp [dir, hL, hF0, hA0]
    · exfalso
      simp only [kp, List.map_append, List.map_cons, List.map_nil] at hkp
      have hlen := congrArg List.length hkp
      simp only [List.length_append, List.length_map, List.length_cons, List.length_nil] at hlen
      have hs0 : segs = [] := List.length_eq_zero_iff.mp (by omega)
      subst hs0
      cases fwd <;> simp at hkp
  | some K =>
    subst hKp
    change ∀ kv ∈ restD s false links segs, kp kv.1 < kp K at hbef
    change ∀ kv ∈ restD s true links segs, kp K < kp kv.1 at haft
    have hB1 : ∀ kv ∈ restD s false links segs, keyLt kv.1 K = true ∧ keyLt K kv.1 = false := by
      intro kv hkv
      have h1 := (kp_lt_iff _ _).mp (hbef kv hkv)
      exact ⟨(keyLt_iff _ _).mpr h1, (keyLt_false_iff _ _).mpr (le_of_lt h1)⟩
    have hF1 : ∀ kv ∈ restD s true links segs, keyLt K kv.1 = true ∧ keyLt kv.1 K = false := by
      intro kv hkv
      have h1 := (kp_lt_iff _ _).mp (haft kv hkv)
      exact ⟨(keyLt_iff _ _).mpr h1, (keyLt_false_iff _ _).mpr (le_of_lt h1)⟩
    rcases hat with ⟨hside, hneq⟩ | ⟨x, c, above, v, hlinks, hatv, hkp⟩
    · -- the tree does not hold the start key
      have hceq : chainEq { links := links, segs := segs, first := true, eqMatch := eqm }
          (some K) = false := by
        rw [← Bool.not_eq_true]
        intro h
        obtain ⟨x, c, above, hl, hK'⟩ := chainEq_true h
        simp only at hl hK'
        exact hneq x c above hl (by rw [hK']; rfl)
      simp only [hceq, Bool.and_false, restX_false, inStart]
      cases fwd with
      | true =>
        have hA1 : ∀ kv ∈ atOf s links segs, keyLt kv.1 K = true ∧ keyLt K kv.1 = false := by
          intro kv hkv
          have h1 := hside kv hkv
          simp only [Side, ite_true] at h1
          have h1 := (kp_lt_iff _ _).mp h1
          exact ⟨(keyLt_iff _ _).mpr h1, (keyLt_false_iff _ _).mpr (le_of_lt h1)⟩
        cases incl with
        | true =>
          rw [filter3 hL _ (b1 := false) (b2 := false) (b3 := true)
            (fun kv h => by simp [(hB1 kv h).1]) (fun kv h => by simp [(hA1 kv h).1])
            (fun kv h => by simp [(hF1 kv h).2])]
          simp [dir]
        | false =>
          rw [filter3 hL _ (b1 := false) (b2 := false) (b3 := true)
            (fun kv h => by simp [(hB1 kv h).2]) (fun kv h => by simp [(hA1 kv h).2])
            (fun kv h => by simp [(hF1 kv h).1])]
          simp [dir]
      | false =>
        have hA1 : ∀ kv ∈ atOf s links segs, keyLt K kv.1 = true ∧ keyLt kv.1 K = false := by
          intro kv hkv
          have h1 := hside kv hkv
          simp only [Side, Bool.false_eq_true, ite_false] at h1
          have h1 := (kp_lt_iff _ _).mp h1
          exact ⟨(keyLt_iff _ _).mpr h1, (keyLt_false_iff _ _).mpr (le_of_lt h1)⟩
        cases incl with
        | true =>
          rw [filter3 hL _ (b1 := true) (b2 := false) (b3 := false)
            (fun kv h => by simp [(hB1 kv h).2]) (fun kv h => by simp [(hA1 kv h).1])
            (fun kv h => by simp [(hF1 kv h).1])]
          simp [dir]
        | false =>
          rw [filter3 hL _ (b1 := true) (b2 := false) (b3 := false)
            (fun kv h => by simp [(hB1 kv h).1]) (fun kv h => by simp [(hA1 kv h).2])
            (fun kv h => by simp [(hF1 kv h).2])]
          simp [dir]
    · -- the chain is at the start key
      have hKeq : K = segs ++ [c] := kp_injective hkp.symm
      have hceq : chainEq { links := links, segs := segs, first := true, eqMatch := eqm }
          (some K) = true := by
        rw [hKeq]
        exact chainEq_of (ch := { links := links, segs := segs, first := true, eqMatch := eqm })
          hlinks
      have hA1 : ∀ kv ∈ atOf s links segs, keyLt kv.1 K = false ∧ keyLt K kv.1 = false := by
        intro kv hkv
        rw [hatv] at hkv
        simp only [List.mem_singleton] at hkv
        rw [hkv, ← hKeq]
        simp [keyLt_false_iff]
      simp only [hceq, Bool.and_true, inStart]
      cases fwd with
      | true =>
        cases incl with
        | true =>
          rw [restX_true, filter3 hL _ (b1 := false) (b2 := true) (b3 := true)
            (fun kv h => by simp [(hB1 kv h).1]) (fun kv h => by simp [(hA1 kv h).1])
            (fun kv h => by simp [(hF1 kv h).2])]
          simp [dir]
        | false =>
          rw [restX_false, filter3 hL _ (b1 := false) (b2 := false) (b3 := true)
            (fun kv h => by simp [(hB1 kv h).2]) (fun kv h => by simp [(hA1 kv h).2])
            (fun kv h => by simp [(hF1 kv h).1])]
          simp [dir]
      | false =>
        cases incl with
        | true =>
          rw [restX_true, filter3 hL _ (b1 := true) (b2 := true) (b3 := false)
            (fun kv h => by simp [(hB1 kv h).2]) (fun kv h => by simp [(hA1 kv h).2])
            (fun kv h => by simp [(hF1 kv h).1])]
          simp [dir]
        | false =>
          rw [restX_false, filter3 hL _ (b1 := true) (b2 := false) (b3 := false)
            (fun kv h => by simp [(hB1 kv h).1]) (fun kv h => by simp [(hA1 kv h).1])
            (fun kv h => by simp [(hF1 kv h).2])]
          simp [dir]

/-- The chain that the setup makes is a path, and what the first `next` has
before it is what the tree holds within the scan's start. -/
theorem setup_start {r : NodeId} (hG : Good s r 0 none) (req : ScanReq)
    (hreq : req.wf = true) {n : KNode} (hobj : s.obj r = some (.key n)) :
    Path s r (chainSetup s req (s.fuel r) r).links (chainSetup s req (s.fuel r) r).segs ∧
    restX s req.forward ((chainSetup s req (s.fuel r) r).first && req.inclusive &&
        (chainSetup s req (s.fuel r) r).eqMatch)
      (chainSetup s req (s.fuel r) r).links (chainSetup s req (s.fuel r) r).segs =
      dir req.forward ((L s r).filter (fun kv => inStart req kv.1)) := by
  have hK : StartOK (startPos req) := by
    unfold startPos
    cases hs : req.start with
    | none => exact startOK_sentinel req.forward
    | some k =>
      simp only [ScanReq.wf, hs, Bool.and_eq_true] at hreq
      exact startOK_kp hreq.1
  simp only [chainSetup]
  generalize hKp : startPos req = Kp at hK ⊢
  have hfuel : n.level + 1 ≤ s.fuel r := by simp [Tree.fuel, hobj]
  have hS := setupGo_spec hG req.forward hK (s.fuel r) r 0 false {} n hobj hfuel
    (fun p => Path.root p) (by simp [restD]) (by simp [restD])
    (fun _ => ⟨rfl, List.length_pos_iff.mpr hK.ne, by simp [kp]⟩) (fun h => by simp at h)
  have hfirst := setupGo_first (s := s) req.forward Kp (s.fuel r) r 0 false {}
  generalize setupGo s req.forward Kp (s.fuel r) r 0 false {} = ch at hS hfirst ⊢
  obtain ⟨links, segs, first, eqm⟩ := ch
  have hfirst' : first = true := hfirst
  subst hfirst'
  exact ⟨hS.path, start_core hG req hKp.symm hS⟩

/-- TP11 for one tree: on a tree that meets the invariants, a scan gives the
keys and values of the contents in its range, in order, the first `limit`. -/
theorem scan_contents {p : Params} (h : invOk p s = true) (req : ScanReq) (hreq : req.wf = true)
    (limit : Nat) : scan s req limit = refScan (contents s) req limit := by
  unfold invOk at h
  unfold scan contents
  cases hr : s.root with
  | none => simp [hr] at h
  | some r =>
    simp only [hr] at h ⊢
    cases ho : s.obj r with
    | none => simp [ho] at h
    | some o =>
      rw [ho] at h
      cases o with
      | val v => simp at h
      | key n =>
        simp only [Bool.and_eq_true] at h
        have hG : Good s r 0 none := walk_good _ _ _ _ h.2
        have hend : req.endKey ≠ none → req.forward = true := by
          intro he
          simp only [ScanReq.wf, Bool.and_eq_true] at hreq
          cases hk : req.endKey with
          | none => exact absurd hk he
          | some e => rw [hk] at hreq; simp only [Bool.and_eq_true] at hreq; exact hreq.2.2
        obtain ⟨hpath, hstart⟩ := setup_start hG req hreq ho
        rw [scanGo_spec hG req hend _ (by omega) limit _ (Or.inr hpath), hstart]
        show _ = refScan (L s r) req limit
        unfold refScan
        have hf : ((L s r).filter (fun kv => inRange req kv.1)) =
            ((L s r).filter (fun kv => inStart req kv.1)).filter (fun kv => inEnd req kv.1) := by
          rw [List.filter_filter]
          apply List.filter_congr
          intro kv _
          rw [inRange_eq, Bool.and_comm]
        simp only [hf]
        cases req.forward with
        | true => simp [dir]
        | false => simp [dir, List.filter_reverse]

end Contract
