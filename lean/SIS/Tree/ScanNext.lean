import SIS.Tree.ScanModel

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! The scan's next step gives the head of the chain's remainder (bergdb
024-12, TP11). -/

/-- A chain whose every link names a sound key node, with the depth bound of
`ScanChain`. -/
def SChain (p : Params) (v : View BVal) (t : Time) (bound : Nat) :
    List (NodeId × Int) → Prop
  | [] => True
  | (x, _) :: rest => ∃ depth, SNode p v t depth x ∧ depth + rest.length ≤ bound ∧
      SChain p v t bound rest

/-- A key at or after the end key (after it, when the end is not inclusive). -/
def endPast (req : ScanReq) (k : Key) : Bool :=
  match req.endKey with
  | some e => keyLt e k || (k == e && !req.endInclusive)
  | none => false

theorem scanPast_eq (req : ScanReq) (ch : Chain) (fd : Found) :
    scanPast req ch fd = endPast req (ch.segs ++ [fd.c]) := by
  unfold scanPast endPast pastEnd
  cases req.endKey <;> rfl

/-- Whether the top link's cursor is itself still to give (the first step of
an inclusive scan that set up at its start key). -/
def incOf (req : ScanReq) (ch : Chain) : Bool := ch.first && req.inclusive && ch.eqMatch

/-- The remainder of a chain. -/
def rem (p : Params) (v : View BVal) (t : Time) (F : Nat) (req : ScanReq) (ch : Chain) :
    List (Key × Nat) :=
  chainRem p v t F req.forward ch.links ch.segs (incOf req ch)

/-- What a next step must give for the remainder L: none at its end or past
the end key; else L's head, with a chain whose remainder is L's tail. -/
def NextOK (p : Params) (v : View BVal) (t : Time) (F bound : Nat) (req : ScanReq)
    (eqM : Bool) (L : List (Key × Nat)) (r : Option Kvt × Chain) : Prop :=
  match L with
  | [] => r.1 = none
  | kv :: rest =>
    if endPast req kv.1 then r.1 = none
    else ∃ kvt, r.1 = some kvt ∧ (kvt.key, kvt.h) = kv ∧ r.2.first = false ∧
      r.2.eqMatch = eqM ∧ chainRem p v t F req.forward r.2.links r.2.segs false = rest ∧
      SChain p v t bound r.2.links

theorem keyLt_append_left (A x y : Key) : keyLt (A ++ x) (A ++ y) = keyLt x y := by
  induction A with
  | nil => rfl
  | cons a A ih => simp [keyLt, ih]

theorem endPast_mono (req : ScanReq) (a b : Key) (h : endPast req a = true)
    (hab : keyLt a b = true ∨ a = b) : endPast req b = true := by
  rcases hab with hab | rfl
  · unfold endPast at h ⊢
    cases he : req.endKey with
    | none => simp [he] at h
    | some e =>
      simp only [he, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h ⊢
      rcases h with h | ⟨rfl, _⟩
      · exact Or.inl (keyLt_trans _ _ _ h hab)
      · exact Or.inl hab
  · exact h

theorem keyLe_single (c c' : Nat) (r : Key) (h : c ≤ c') :
    keyLt [c] (c' :: r) = true ∨ [c] = c' :: r := by
  rcases Nat.lt_or_eq_of_le h with h | rfl
  · left; simp [keyLt, h]
  · cases r with
    | nil => right; rfl
    | cons d r => left; simp [keyLt]

theorem orient_true {α : Type} (l : List α) : orient true l = l := rfl

/-- The first key a klong gives forward starts at or above its compare value. -/
theorem klongC_head (p : Params) (v : View BVal) (t d F x : Nat) (n : KNode)
    (hs : SNode p v t (d+1) x) (hn : knodeOf p v x = some n) (hdF : d ≤ F)
    (q : Nat × NodeId) (hq : q ∈ n.liveAt t) :
    ∃ kv rest, klongC p v t F true n q = kv :: rest ∧ ∃ c r, kv.1 = c :: r ∧ q.1 ≤ c := by
  obtain ⟨n', hn', _, _, hc⟩ := hs
  rw [hn] at hn'
  cases Option.some.inj hn'
  obtain ⟨hshort, hnot⟩ := hc q hq
  cases hl : (n.leaf && segLen q.1 != 7) with
  | true =>
    obtain ⟨_, h, _, _, hv⟩ := hshort hl
    have hleaf : n.leaf = true := by simp_all
    have hlen : segLen q.1 ≠ 7 := by simp_all
    refine ⟨([q.1], h), [], ?_, q.1, [], rfl, Nat.le_refl _⟩
    simp [klongC, hleaf, hlen, hv]
  | false =>
    obtain ⟨_, _, _, hcs, ⟨cn, hcn, hcne⟩, hrange⟩ := hnot hl
    have hne := treeContents_ne_nil p v t d q.2 hcs cn hcn hcne
    rw [← treeContents_stable p v t d q.2 hcs F hdF] at hne
    obtain ⟨kv0, rest0, he⟩ := List.exists_cons_of_ne_nil hne
    cases hleaf : n.leaf with
    | true =>
      have hlen : segLen q.1 = 7 := by simpa [hleaf] using hl
      refine ⟨(q.1 :: kv0.1, kv0.2), rest0.map (fun kv => (q.1 :: kv.1, kv.2)), ?_,
        q.1, kv0.1, rfl, Nat.le_refl _⟩
      simp [klongC, hleaf, hlen, orient_true, he]
    | false =>
      have hmem : kv0 ∈ treeContents p v t d q.2 := by
        rw [← treeContents_stable p v t d q.2 hcs F hdF, he]; simp
      obtain ⟨c, r, hk, hle, _⟩ := hrange hleaf kv0 hmem
      refine ⟨kv0, rest0, ?_, c, r, hk, hle⟩
      simp [klongC, hleaf, orient_true, he]

theorem sNode_bound (p : Params) (v : View BVal) (t d y : Nat) (hs : SNode p v t d y)
    (cn : KNode) (hcn : knodeOf p v y = some cn) : ∀ q ∈ cn.liveAt t, q.1 < 2^62 := by
  cases d with
  | zero => exact hs.elim
  | succ d =>
    obtain ⟨n', hn', _, hb, _⟩ := hs
    rw [hcn] at hn'
    cases Option.some.inj hn'
    exact hb

theorem afterL_sentinel (cn : KNode) (t : Time) (fw : Bool)
    (hb : ∀ q ∈ cn.liveAt t, q.1 < 2^62) :
    afterL cn t fw false (if fw then cvLo else cvHi) = orient fw (cn.liveAt t) := by
  cases fw with
  | true =>
    simp only [afterL, ↓reduceIte, Bool.false_eq_true, orient]
    apply List.filter_eq_self.mpr
    intro q _
    apply decide_eq_true
    simp only [cvLo]
    omega
  | false =>
    simp only [afterL, Bool.false_eq_true, ↓reduceIte, orient]
    congr 1
    apply List.filter_eq_self.mpr
    intro q hq
    have := hb q hq
    apply decide_eq_true
    simp only [cvHi]
    omega

theorem rem_found (p : Params) (v : View BVal) (t F : Nat) (req : ScanReq) (ch : Chain)
    (x : NodeId) (lc : Int) (rest : List (NodeId × Int)) (hl : ch.links = (x, lc) :: rest)
    (n : KNode) (hn : knodeOf p v x = some n) (fd : Found)
    (hfd : scanChoice n t req ch.first ch.eqMatch lc = some fd) :
    rem p v t F req ch =
      (klongC p v t F req.forward n (fd.c, fd.y)).map (fun kv => (ch.segs ++ kv.1, kv.2)) ++
        chainRem p v t F req.forward ((x, (fd.c : Int)) :: rest) ch.segs false := by
  unfold rem incOf
  rw [hl]
  simp only [chainRem, hn]
  rw [afterL_choice_some n t req ch.first ch.eqMatch lc fd hfd]
  simp [List.flatMap_cons, List.map_append, List.append_assoc]

theorem rem_push (p : Params) (v : View BVal) (t F : Nat) (req : ScanReq) (ch : Chain)
    (x : NodeId) (rest : List (NodeId × Int)) (n : KNode) (hn : knodeOf p v x = some n)
    (fd : Found) (d : Nat) (hcs : SNode p v t d fd.y) (cn : KNode)
    (hcn : knodeOf p v fd.y = some cn) (hdF : d ≤ F)
    (hkind : (n.leaf && segLen fd.c != 7) = false) :
    rem p v t F req (scanPush req ch n x rest fd) =
      (klongC p v t F req.forward n (fd.c, fd.y)).map (fun kv => (ch.segs ++ kv.1, kv.2)) ++
        chainRem p v t F req.forward ((x, (fd.c : Int)) :: rest) ch.segs false := by
  unfold rem incOf scanPush
  simp only [Bool.false_and, chainRem, hcn]
  rw [afterL_sentinel cn t req.forward (sNode_bound p v t d fd.y hcs cn hcn),
    ← treeContents_orient p v t F fd.y cn hcn,
    treeContents_stable p v t d fd.y hcs (F+1) (by omega)]
  have hpop : popSegs p v (if n.leaf = true then ch.segs ++ [fd.c] else ch.segs)
      ((x, (fd.c : Int)) :: rest) = ch.segs := by
    cases hleaf : n.leaf <;> simp [popSegs, hn, hleaf]
  rw [hpop]
  congr 1
  cases hleaf : n.leaf with
  | false =>
    simp [klongC, hleaf, treeContents_stable p v t d fd.y hcs F hdF]
  | true =>
    have hlen : segLen fd.c = 7 := by simpa [hleaf] using hkind
    simp [klongC, hleaf, hlen, treeContents_stable p v t d fd.y hcs F hdF]

/-- One step of the scan at a klong found in the top link: past the end key it
stops, a value it gives, a key node it enters (the step after is `hpush`). -/
theorem nextGo_found_ok (p : Params) (v : View BVal) (t F bound : Nat) (req : ScanReq)
    (hF : bound ≤ F) (hdir : req.forward = false → req.endKey = none)
    (ch : Chain) (x : NodeId) (lc : Int) (rest : List (NodeId × Int))
    (hl : ch.links = (x, lc) :: rest) (d : Nat) (hs : SNode p v t (d+1) x) (n : KNode)
    (hn : knodeOf p v x = some n) (hb : d + 1 + rest.length ≤ bound)
    (hrest : SChain p v t bound rest) (fd : Found)
    (hfd : scanChoice n t req ch.first ch.eqMatch lc = some fd) (f : Nat)
    (hpush : SNode p v t d fd.y → (∃ cn, knodeOf p v fd.y = some cn ∧ cn.liveAt t ≠ []) →
      NextOK p v t F bound req ch.eqMatch (rem p v t F req (scanPush req ch n x rest fd))
        (nextGo p v t req f (scanPush req ch n x rest fd))) :
    NextOK p v t F bound req ch.eqMatch (rem p v t F req ch) (nextGo p v t req (f+1) ch) := by
  have hmem := scanChoice_mem n t req ch.first ch.eqMatch lc fd hfd
  have hs' := hs
  obtain ⟨n', hn', _, _, hc⟩ := hs'
  rw [hn] at hn'
  cases Option.some.inj hn'
  obtain ⟨hshort, hnot⟩ := hc _ hmem
  rw [nextGo_step p v t req f ch x lc rest hl n hn, hfd]
  simp only
  rw [rem_found p v t F req ch x lc rest hl n hn fd hfd]
  by_cases hpast : scanPast req ch fd = true
  · simp only [hpast, ↓reduceIte]
    have hfw : req.forward = true := by
      cases hf : req.forward with
      | true => rfl
      | false =>
        have he := hdir hf
        simp [scanPast, he] at hpast
    obtain ⟨kv, rest0, hk, c, r, hkc, hle⟩ :=
      klongC_head p v t d F x n hs hn (by omega) (fd.c, fd.y) hmem
    rw [hfw, hk]
    simp only [List.map_cons, List.cons_append, NextOK]
    have hp : endPast req (ch.segs ++ kv.1) = true := by
      apply endPast_mono req (ch.segs ++ [fd.c])
      · rw [← scanPast_eq]; exact hpast
      · rw [hkc]
        rcases keyLe_single fd.c c r hle with h | h
        · left; rw [keyLt_append_left]; exact h
        · right; rw [h]
    simp [hp]
  · simp only [hpast, Bool.false_eq_true, ↓reduceIte]
    have hpast' : endPast req (ch.segs ++ [fd.c]) = false := by
      rw [← scanPast_eq]; simpa using hpast
    cases hkind : (n.leaf && segLen fd.c != 7) with
    | true =>
      obtain ⟨nd, h, hy, hd, hv⟩ := hshort hkind
      have hleaf : n.leaf = true := by simp_all
      have hlen : segLen fd.c ≠ 7 := by simp_all
      simp only [hy, hd, ↓reduceIte, hv]
      have hk : klongC p v t F req.forward n (fd.c, fd.y) = [([fd.c], h)] := by
        simp [klongC, hleaf, hlen, hv]
      rw [hk]
      simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, NextOK,
        hpast', Bool.false_eq_true, ↓reduceIte]
      exact ⟨_, rfl, rfl, trivial, trivial, trivial, ⟨d+1, hs, hb, hrest⟩⟩
    | false =>
      obtain ⟨nd, hy, hd, hcs, ⟨cn, hcn, hcne⟩, _⟩ := hnot hkind
      simp only [hy, hd, Bool.false_eq_true, ↓reduceIte]
      rw [← rem_push p v t F req ch x rest n hn fd d hcs cn hcn (by omega) hkind]
      exact hpush hcs ⟨cn, hcn, hcne⟩

theorem scanChoice_some_of_sentinel (p : Params) (v : View BVal) (t d y : Nat)
    (hs : SNode p v t d y) (cn : KNode) (hcn : knodeOf p v y = some cn)
    (hne : cn.liveAt t ≠ []) (req : ScanReq) (eqMatch : Bool) :
    ∃ fd, scanChoice cn t req false eqMatch (if req.forward then cvLo else cvHi) = some fd := by
  have hb := sNode_bound p v t d y hs cn hcn
  cases h : scanChoice cn t req false eqMatch (if req.forward then cvLo else cvHi) with
  | some fd => exact ⟨fd, rfl⟩
  | none =>
    exact (scanChoice_sentinel cn t req eqMatch hne (fun q hq => by
      have := hb q hq
      simp only [cvLo, cvHi]
      omega) h).elim

/-- Entering a sound key node with a live klong, the scan's next step gives the
head of the remainder: it descends to the node's first value in its order. -/
theorem nextGo_descent_ok (p : Params) (v : View BVal) (t F bound : Nat) (req : ScanReq)
    (hF : bound ≤ F) (hdir : req.forward = false → req.endKey = none) (d : Nat) :
    ∀ (y : NodeId) (ch : Chain) (rest : List (NodeId × Int)), SNode p v t d y →
      (∃ cn, knodeOf p v y = some cn ∧ cn.liveAt t ≠ []) →
      ch.links = (y, if req.forward then cvLo else cvHi) :: rest → ch.first = false →
      SChain p v t bound rest → d + rest.length ≤ bound → ∀ f, d ≤ f →
      NextOK p v t F bound req ch.eqMatch (rem p v t F req ch) (nextGo p v t req f ch) := by
  induction d with
  | zero => intro y ch rest hs; exact hs.elim
  | succ d ih =>
    intro y ch rest hs hne hl hfirst hrest hb f hf
    obtain ⟨cn, hcn, hcne⟩ := hne
    obtain ⟨fd, hfd⟩ := scanChoice_some_of_sentinel p v t _ y hs cn hcn hcne req ch.eqMatch
    cases f with
    | zero => omega
    | succ f =>
      apply nextGo_found_ok p v t F bound req hF hdir ch y _ rest hl d hs cn hcn
        (by omega) hrest fd (by rw [hfirst]; exact hfd) f
      intro hcs hcne'
      exact ih fd.y _ ((y, (fd.c : Int)) :: rest) hcs hcne' rfl rfl
        ⟨d+1, hs, by omega, hrest⟩ (by simp only [List.length_cons]; omega) f (by omega)

/-- The scan's next step on a sound chain, with the fuel of `nextGo_stable`,
gives the head of the chain's remainder (none at its end or past the end key),
and a chain whose remainder is the rest. -/
theorem nextGo_ok (p : Params) (v : View BVal) (t F bound : Nat) (req : ScanReq)
    (hF : bound ≤ F) (hdir : req.forward = false → req.endKey = none)
    (links : List (NodeId × Int)) :
    ∀ ch : Chain, ch.links = links → SChain p v t bound links → ∀ f,
      bound + links.length + 1 ≤ f →
      NextOK p v t F bound req ch.eqMatch (rem p v t F req ch) (nextGo p v t req f ch) := by
  induction links with
  | nil =>
    intro ch hl _ f hf
    cases f with
    | zero => omega
    | succ f =>
      have hr : rem p v t F req ch = [] := by
        unfold rem; rw [hl]; rfl
      rw [hr]
      simp [NextOK, nextGo, hl]
  | cons link rest ih =>
    intro ch hl hc f hf
    rcases link with ⟨x, lc⟩
    obtain ⟨depth, hs, hb, hrest⟩ := hc
    cases depth with
    | zero => exact hs.elim
    | succ d =>
      have hs' := hs
      obtain ⟨n, hn, _⟩ := hs'
      cases f with
      | zero => omega
      | succ f =>
        cases hfd : scanChoice n t req ch.first ch.eqMatch lc with
        | none =>
          rw [nextGo_step p v t req f ch x lc rest hl n hn, hfd]
          simp only
          have hr : rem p v t F req ch = rem p v t F req (scanPop p v ch rest) := by
            unfold rem incOf
            rw [hl]
            simp only [chainRem, hn]
            rw [afterL_choice_none n t req ch.first ch.eqMatch lc hfd]
            simp only [List.flatMap_nil, List.map_nil, List.nil_append]
            rfl
          rw [hr]
          exact ih (scanPop p v ch rest) rfl hrest f
            (by simp only [List.length_cons] at hf; omega)
        | some fd =>
          apply nextGo_found_ok p v t F bound req hF hdir ch x lc rest hl d hs n hn
            hb hrest fd hfd f
          intro hcs hcne
          exact nextGo_descent_ok p v t F bound req hF hdir d fd.y _ ((x, (fd.c : Int)) :: rest)
            hcs hcne rfl rfl ⟨d+1, hs, hb, hrest⟩ (by simp only [List.length_cons]; omega) f
            (by simp only [List.length_cons] at hf; omega)

theorem sChain_length (p : Params) (v : View BVal) (t bound : Nat)
    (links : List (NodeId × Int)) (h : SChain p v t bound links) : links.length ≤ bound := by
  cases links with
  | nil => simp
  | cons q rest =>
    obtain ⟨depth, hd, hb, _⟩ := h
    cases depth with
    | zero => exact hd.elim
    | succ d => simp only [List.length_cons]; omega

/-- The scan's loop gives the first `limit` pairs of the remainder before the
end key, on a sound chain of the parameters' path bound. -/
theorem scanGo_ok (p : Params) (v : View BVal) (t F : Nat) (req : ScanReq)
    (hF : p.fuel ≤ F) (hdir : req.forward = false → req.endKey = none) (limit : Nat) :
    ∀ fuel (ch : Chain) (acc : List Kvt), SChain p v t p.fuel ch.links →
      (scanGo p v t req limit fuel ch acc).map (fun kv => (kv.key, kv.h)) =
        acc.map (fun kv => (kv.key, kv.h)) ++
          ((rem p v t F req ch).takeWhile (fun kv => !endPast req kv.1)).take
            (min fuel (limit - acc.length)) := by
  intro fuel
  induction fuel with
  | zero => intro ch acc _; simp [scanGo]
  | succ f ih =>
    intro ch acc hc
    by_cases hlim : acc.length ≥ limit
    · simp only [scanGo, hlim, ↓reduceIte]
      have : limit - acc.length = 0 := by omega
      simp [this]
    · simp only [scanGo, hlim, ↓reduceIte]
      have hl := sChain_length p v t p.fuel ch.links hc
      have hn := nextGo_ok p v t F p.fuel req hF hdir ch.links ch rfl hc (2 * p.fuel + 2)
        (by omega)
      generalize hr : rem p v t F req ch = L at hn
      cases hng : nextGo p v t req (2 * p.fuel + 2) ch with
      | mk r ch' =>
        rw [hng] at hn
        cases L with
        | nil =>
          simp only [NextOK] at hn
          subst hn
          simp
        | cons kv rest =>
          simp only [NextOK] at hn
          by_cases hp : endPast req kv.1 = true
          · simp only [hp, ↓reduceIte] at hn
            subst hn
            simp [hp]
          · simp only [hp, Bool.false_eq_true, ↓reduceIte] at hn
            obtain ⟨kvt, hkvt, hkv, hfirst, _, hrest, hc'⟩ := hn
            subst hkvt
            simp only
            rw [ih ch' (acc ++ [kvt]) hc']
            have hr' : rem p v t F req ch' = rest := by
              unfold rem incOf; rw [hfirst]; simpa using hrest
            rw [hr']
            have hp' : endPast req kv.1 = false := by simpa using hp
            have hmin : min (f + 1) (limit - acc.length) = min f (limit - (acc.length + 1)) + 1 := by
              omega
            simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
              List.length_append, List.length_singleton, List.takeWhile_cons, hp',
              Bool.not_false, ↓reduceIte, hmin, List.take_succ_cons, hkv]
            rfl

/-- A scan from a chain set up in a sound tree, on the parameters' path bound,
gives the first `limit` pairs of the chain's remainder before the end key. -/
theorem scan_eq_rem (p : Params) (v : View BVal) (t F : Nat) (req : ScanReq) (limit : Nat)
    (hF : p.fuel ≤ F) (hdir : req.forward = false → req.endKey = none) (r : NodeId)
    (hr : rootAt v t = some r) (hc : SChain p v t p.fuel (chainSetup p v t req r).links) :
    (scan p v t req limit).map (fun kv => (kv.key, kv.h)) =
      ((rem p v t F req (chainSetup p v t req r)).takeWhile
        (fun kv => !endPast req kv.1)).take limit := by
  unfold scan
  rw [hr]
  simp only
  rw [scanGo_ok p v t F req hF hdir limit limit _ [] hc]
  simp

end SIS.Tree
