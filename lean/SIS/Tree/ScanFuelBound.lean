import SIS.Tree.IntervalSearchProof

namespace SIS.Tree

open SIS SIS.Check

theorem KNode.searchLte_cvLo (n : KNode) (t : Time) : n.searchLte t cvLo = none := by
  apply (n.searchLte_spec t cvLo).2.mpr
  intro q _
  change decide ((q.1 : Int) ≤ -1) = false
  simp
  omega

/-- A forward scan without a start key begins above the space root, with
no key segment already passed, regardless of the view. -/
theorem chainSetup_forward_segs (p : Params) (v : View BVal) (t x : Nat) :
    (chainSetup p v t {} x).segs = [] := by
  unfold chainSetup
  cases hf : p.fuel with
  | zero => rfl
  | succ f =>
    simp only [setupGo]
    cases hn : knodeOf p v x with
    | none => rfl
    | some n => simp [n.searchLte_cvLo]

/-- Each scan step can add at most one segment to the returned key. -/
theorem nextGo_key_length (p : Params) (v : View BVal) (t : Time) (req : ScanReq)
    (f : Nat) (ch : Chain) (kv : Kvt)
    (h : (nextGo p v t req f ch).1 = some kv) :
    kv.key.length ≤ ch.segs.length + f := by
  induction f generalizing ch with
  | zero => simp [nextGo] at h
  | succ f ih =>
    cases hl : ch.links with
    | nil => simp [nextGo, hl] at h
    | cons link rest =>
      rcases link with ⟨x, lc⟩
      cases hn : knodeOf p v x with
      | none => simp [nextGo, hl, hn] at h
      | some n =>
        simp only [nextGo, hl, hn] at h
        generalize hfd : (if ch.first && req.inclusive && ch.eqMatch then
          (if req.forward then n.searchGte t lc else n.searchLte t lc)
          else (if req.forward then n.searchGt t lc else n.searchLt t lc)) = found at h
        cases found with
        | none =>
          simp only at h
          have hb := ih _ h
          have hs : (match rest with
              | (q, _) :: _ =>
                if ((knodeOf p v q).map (fun (node : KNode) => node.leaf)) == some true then
                  ch.segs.dropLast else ch.segs
              | [] => ch.segs).length ≤ ch.segs.length := by
            cases rest with
            | nil => exact Nat.le_refl _
            | cons link rest =>
              rcases link with ⟨q, c⟩
              simp only
              split
              · simp
              · exact Nat.le_refl _
          exact Nat.le_trans hb (Nat.le_trans (Nat.add_le_add_right hs f) (by omega))
        | some fd =>
          simp only at h
          let past : Bool := match req.endKey with
            | some e => pastEnd ch.segs fd.c e req.endInclusive
            | none => false
          change ((if past then _ else _) : Option Kvt × Chain).1 = some kv at h
          cases hpast : past with
          | true => simp only [hpast, ↓reduceIte] at h; cases h
          | false =>
            simp only [hpast, Bool.false_eq_true, ↓reduceIte] at h
            cases hy : v fd.y with
            | none => simp [hy] at h
            | some nd =>
              simp only [hy] at h
              cases hd : nd.isData with
              | true =>
                simp only [hd, ↓reduceIte] at h
                cases hv : valueOf v fd.y with
                | none => simp [hv] at h
                | some value =>
                  simp only [hv, Option.some.injEq] at h
                  subst kv
                  simp only [List.length_append, List.length_singleton]
                  omega
              | false =>
                simp only [hd, Bool.false_eq_true, ↓reduceIte] at h
                have hb := ih _ h
                have hs : (if n.leaf then ch.segs ++ [fd.c] else ch.segs).length ≤
                    ch.segs.length + 1 := by
                  split <;> simp
                exact Nat.le_trans hb (by dsimp only at *; omega)

/-- A first forward result from the beginning cannot have more segments
than the fixed `nextGo` fuel. -/
theorem scan_forward_one_key_length (p : Params) (v : View BVal) (t : Time)
    (kv : Kvt) (h : kv ∈ scan p v t {} 1) : kv.key.length ≤ scanFuel := by
  unfold scan at h
  cases hr : rootAt v t with
  | none => simp [hr] at h
  | some r =>
    simp only [hr, scanGo, List.length_nil, Nat.le_zero_eq, Nat.one_ne_zero,
      ↓reduceIte] at h
    cases hn : nextGo p v t {} scanFuel (chainSetup p v t {} r) with
    | mk result ch =>
      cases result with
      | none => simp [hn] at h
      | some found =>
        have heq : kv = found := by simpa [hn, scanGo] using h
        subst kv
        have hb := nextGo_key_length p v t {} scanFuel (chainSetup p v t {} r)
          found (by rw [hn])
        simpa only [chainSetup_forward_segs, List.length_nil, Nat.zero_add] using hb

/-- A first forward scan from the beginning that gives the reference map's
first KV gives a key of at most `scanFuel` segments: TP11 holds only for runs
whose keys are that short (its premise). -/
theorem scanEq_first_key_length (p : Params) (ts : List Tx) (t : Time)
    (he : (scan p (viewOf (treeRun p ts)) t {} 1).map (fun kv => (kv.key, kv.h)) =
      refScan ts t {} 1)
    (key : Key) (value : Nat) (hk : (key, value) ∈ refScan ts t {} 1) :
    key.length ≤ scanFuel := by
  rw [← he] at hk
  obtain ⟨kv, hkv, hpair⟩ := List.mem_map.mp hk
  have hkey : kv.key = key := congrArg Prod.fst hpair
  rw [← hkey]
  exact scan_forward_one_key_length p _ t kv hkv

end SIS.Tree
