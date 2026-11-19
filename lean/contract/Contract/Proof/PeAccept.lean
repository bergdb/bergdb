/-
bergdb 030-21, part 3: PE accepts every transaction but those it refuses by
design (Contract/PeAcceptStatement.lean): `pe_accepts`.

The program refuses (gives none) where a recursion runs out of fuel, where it
meets a node that is not one of PE's, where a put's key is not one the tree
can hold, where a root would get a new root above height H, and where a
match it never meets fails. From `Inv` each of these is shown not to
happen but the named ones:

* A. The root settled alone (`settle_acc`): an old root's single children
  are key nodes (`Shaped`); a planned root's single child is one of its
  entries (`VOk`); a root cut into k parts gets a new root of k entries, cut
  again into at most half as many (`cutParts_next`, h and cap at least 2),
  so the new roots stay within H when k - 1 < 2^(H - e) at the root's
  height e (`settle_up`). The root settled is one node (`One`).
* B. emit (`emit_some`, `emit_one`): a decision to keep or append has a
  base, a key node (`EOk`); a root of one node gives one entry.
* C. rebalance (`rebalance_acc`): a child to join has a neighbour; an
  untouched child opened is a key node; a joined node is within the level
  bounds.
* D. plan (`acc_all`): by induction on the fuel, with `PlanAcc` (plan),
  `GroupsAcc` (a segment leaf's groups) and `TreeAcc` (a segment's tree):
  each key node of the tree before planned is a key node shaped as PE's
  trees (`Shaped`), sound (`Good`); a long compare value's entry is the
  root of the next segment's tree; a key of more segments than the leaf's
  segment goes on (`keyWf`), within G; the fuel a level uses is at most
  M + p + 2 H + 6; a planned root holds at most the tree's nodes plus the
  operations (PeAccSize.lean), which `Room` bounds.
* E. The transaction (`pe_accepts`); a put of a key the tree cannot hold
  refused (`pe_refuses`); with `pe_step`, the transaction meets the
  contract (`pe_accepts_step`); every history from the empty tree goes on
  (`pe_extend`).
-/
import Contract.Proof.PeAccSize
import Contract.Proof.PeTx
import Contract.PeAcceptStatement

namespace Contract.PE

open PeProof PeProof.Abs PeProof.Keys

variable {cf : Cfg} {i : Time} {s : Tree}

/-! ## A. The root settled alone -/

/-- A decision at height h leaves room below H: a cut into k ≥ 2 parts has
k - 1 < 2^(H - h). -/
def RoomD (cf : Cfg) (h : Nat) (dec : Dec) : Prop :=
  ∀ k, dec = .parts k → 2 ≤ k → k - 1 < 2 ^ (cf.H - h)

/-- A root as emit writes it is one node: not cut into two or more parts. -/
def One : VN → Prop
  | .old _ => True
  | .node _ _ _ _ _ _ dec => ∀ k, dec = .parts k → k < 2

theorem nParts_half {cap k : Nat} (hc : 2 ≤ cap) (hk : cap < k) : nParts cap k ≤ (k + 1) / 2 := by
  unfold nParts
  have hm : max cap 1 = cap := by omega
  simp only [hm, show ¬ k ≤ cap from by omega, ↓reduceIte]
  obtain ⟨d, rfl⟩ : ∃ d, cap = d + 2 := ⟨cap - 2, by omega⟩
  have hq1 : 1 ≤ (k + (d + 2) - 1) / (d + 2) := by
    rw [Nat.le_div_iff_mul_le (by omega)]; omega
  have hq2 := Nat.div_mul_le_self (k + (d + 2) - 1) (d + 2)
  generalize (k + (d + 2) - 1) / (d + 2) = q at hq1 hq2
  rw [Nat.le_div_iff_mul_le (by omega)]
  have h3 : d ≤ q * d := Nat.le_mul_of_pos_left d (by omega)
  have h4 : q * (d + 2) = q * d + q * 2 := Nat.mul_add q d 2
  omega

/-- The parts of a new root's list of k entries, when two or more: k is at
least 3, and they are at most half as many, less one. -/
theorem cutParts_next (h2 : 2 ≤ cf.h) (hc2 : 2 ≤ cf.cap) {k : Nat} (hk : 2 ≤ cutParts cf k) :
    3 ≤ k ∧ cutParts cf k - 1 ≤ (k - 1) / 2 := by
  unfold cutParts at hk ⊢
  split at hk
  · omega
  · rename_i hkh
    simp only [hkh, ↓reduceIte]
    by_cases hkc : k ≤ cf.cap
    · have : nParts cf.cap k = 1 := by
        unfold nParts; simp only [show k ≤ max cf.cap 1 from by omega, ↓reduceIte]
      rw [this]; omega
    · have := nParts_half hc2 (by omega : cf.cap < k)
      omega

/-- The room left by a cut into k ≥ 2 parts at height h: the new root's
height is within H, and its own cut into k2 parts, at most half as many, has
room at h + 1. -/
theorem room_next {h k k2 : Nat} (hk : 2 ≤ k) (hr : k - 1 < 2 ^ (cf.H - h))
    (hk2 : k2 - 1 ≤ (k - 1) / 2) : h + 1 ≤ cf.H ∧ k2 - 1 < 2 ^ (cf.H - (h + 1)) := by
  have hpos : cf.H - h ≠ 0 := by
    intro h0; rw [h0] at hr; simp at hr; omega
  obtain ⟨e, he⟩ : ∃ e, cf.H - h = e + 1 := ⟨cf.H - h - 1, by omega⟩
  rw [he, Nat.pow_succ] at hr
  refine ⟨by omega, ?_⟩
  rw [show cf.H - (h + 1) = e by omega]
  omega

theorem ents_length_ge (c : Nat) (w : VN) : 1 ≤ (ents c w).length := by
  have := ents_ne c w
  cases h : ents c w with
  | nil => exact absurd h this
  | cons _ _ => simp

theorem flatMap_ents_length_ge (es : List (Nat × VN)) :
    es.length ≤ (es.flatMap (fun e => ents e.1 e.2)).length := by
  induction es with
  | nil => simp
  | cons e es ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have := ents_length_ge e.1 e.2
    omega

/-- A planned node's decision to cut into k ≥ 2 parts gives its parent k
entries. -/
theorem ents_parts_length {c : Nat} {b : Option NodeId} {g h : Nat} {j : Bool}
    {es : List (Nat × VN)} {F : List (Nat × Option NodeId)} {k : Nat} (hk : 2 ≤ k) :
    (ents c (.node b g h j es F (.parts k))).length = k := by
  simp only [ents, hk, ↓reduceIte]
  exact partEnts_length c F (by omega) j

/-- A node whose final list has at most one entry is one node. -/
theorem one_of_short {g h : Nat} {b : Option NodeId} {j : Bool} {es : List (Nat × VN)}
    {F : List (Nat × Option NodeId)} {dec : Dec} (hv : VOk cf s g h (.node b g h j es F dec))
    (hF : F.length ≤ 1) : One (.node b g h j es F dec) := by
  intro k hk
  have hd : DecOk dec F := by cases hv <;> assumption
  by_contra h2
  have := hd k hk (by omega)
  omega

/-- What a root settled alone is: an untouched node or a planned one (`RootOk`),
with `EOk`, one node. -/
def SettOk (cf : Cfg) (i : Time) (s : Tree) (g : Nat) (v : VN) : Prop :=
  ∃ h', RootOk cf s g h' v ∧ EOk cf i s g h' v ∧ One v

/-- **The new roots**: a planned node that is not empty and not an inner node
of one entry settles into one node, if its cut has room below H. -/
theorem settle_up (hcf : cf.Ok) (h2 : 2 ≤ cf.h) (hc2 : 2 ≤ cf.cap) {g : Nat} (hG : g ≤ cf.G)
    (space : Bool) : ∀ (f h : Nat) (b : Option NodeId) (j : Bool) (es : List (Nat × VN))
    (F : List (Nat × Option NodeId)) (dec : Dec),
    VOk cf s g h (.node b g h j es F dec) → EOk cf i s g h (.node b g h j es F dec) →
    RoomD cf h dec → F ≠ [] → (h = 0 ∨ 2 ≤ F.length) → h ≤ cf.H → cf.H - h + 1 ≤ f →
    ∃ v', settleRoot cf i s f g (.node b g h j es F dec) space = some (some v') ∧
      SettOk cf i s g v'
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, hf => by omega
  | f + 1, h, b, j, es, F, dec, hv, he, hroom, hF, hh, hH, hf => by
    have hdone : SettOk cf i s g (.node b g h j es F dec) → ∃ v', some (some
        (VN.node b g h j es F dec)) = some (some v') ∧ SettOk cf i s g v' :=
      fun hs => ⟨_, rfl, hs⟩
    have hFe : F.isEmpty = false := by
      cases F with
      | nil => exact absurd rfl hF
      | cons _ _ => rfl
    have hone : (h != 0 && F.length == 1) = false := by
      rcases hh with hh | hh
      · simp [hh]
      · simp only [Bool.and_eq_false_iff, bne_eq_false_iff_eq, beq_eq_false_iff_ne, ne_eq]
        right; omega
    simp only [settleRoot, hFe, hone, Bool.false_eq_true, ite_false]
    have hd : DecOk dec F := by cases hv <;> assumption
    cases dec with
    | same =>
      exact hdone ⟨h, Or.inr hv, he, fun k hk => by cases hk⟩
    | append =>
      exact hdone ⟨h, Or.inr hv, he, fun k hk => by cases hk⟩
    | parts k =>
      simp only
      by_cases hk : 2 ≤ k
      · simp only [hk, ↓reduceIte]
        have hkF := hd k rfl hk
        have hr := hroom k rfl hk
        have hh1 : h + 1 ≤ cf.H := (room_next (k2 := 0) hk hr (by omega)).1
        have hne : (VN.node b g h j es F (.parts k)).isEmpty = false := by
          simp only [VN.isEmpty]; exact hFe
        cases hm : mkNode cf i s none g (h + 1) false [(0, .node b g h j es F (.parts k))] with
        | none =>
          exfalso
          unfold mkNode at hm
          simp only at hm
          split at hm
          · rename_i hc; simp at hc; omega
          · cases hm
        | some r =>
          simp only
          obtain ⟨⟨F2, dec2, hr2⟩, hvr⟩ := mkNode_inner hcf hm
            (by intro e he'; simp at he'; subst he'; exact hv)
            (by intro e he'; simp at he'; subst he'; exact hne)
          obtain ⟨her, _⟩ := mkNode_eok hm (by simp)
            (by intro e he' _; simp at he'; subst he'; simpa using he)
          subst hr2
          have hren : renameHead 0 [((0 : Nat), VN.node b g h j es F (.parts k))] =
              [(0, VN.node b g h j es F (.parts k))] := rfl
          rw [hren] at hvr her
          have hF2 : F2.length = k := by
            cases hvr with
            | inner _ _ _ hF2 _ =>
              rw [hF2, renameHead_length]
              simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
              exact ents_parts_length hk
          have hdec2 : dec2 = .parts (cutParts cf k) := by
            cases her with
            | node hdec _ _ _ =>
              rw [hdec]
              simp [decideNode, hF2]
          subst hdec2
          refine settle_up hcf h2 hc2 hG space f (h + 1) none false _ F2 _ hvr her ?_ ?_
            (Or.inr (by omega)) hh1 (by omega)
          · intro k2 hk2 h22
            cases hk2
            have := cutParts_next h2 hc2 h22
            exact (room_next hk hr this.2).2
          · intro h0; rw [h0] at hF2; simp at hF2; omega
      · simp only [hk, ↓reduceIte]
        exact hdone ⟨h, Or.inr hv, he, fun k' hk' => by cases hk'; omega⟩

/-- **The root settled alone** (`settleRoot`): an untouched root shaped as
PE's trees, or a planned root, settles into one node (or, for a segment's
tree, none), with fuel h + H + 2, if a cut of the planned root has room
below H. The space root never settles into none. -/
theorem settle_acc (hcf : cf.Ok) (h2 : 2 ≤ cf.h) (hc2 : 2 ≤ cf.cap) {g : Nat} (hG : g ≤ cf.G)
    (space : Bool) : ∀ (f h : Nat) (v : VN), RootOk cf s g h v → EOk cf i s g h v →
    (∀ b j es F dec, v = .node b g h j es F dec → RoomD cf h dec) → h ≤ cf.H →
    h + cf.H + 2 ≤ f →
    ∃ r, settleRoot cf i s f g v space = some r ∧ (space = true → r ≠ none) ∧
      ∀ v', r = some v' → SettOk cf i s g v'
  | 0, _, _, _, _, _, _, hf => by omega
  | f + 1, h, v, hv, he, hroom, hH, hf => by
    cases v with
    | old y =>
      have hsh : Shaped cf s g h y := by
        rcases hv with ⟨y', hy, hsh⟩ | hv
        · cases hy; exact hsh
        · cases hv with
          | old hsh _ _ => exact hsh
      obtain ⟨n, hobj, _, hleaf, _, _⟩ := shaped_obj hsh
      have hgk : getKey s y = some n := by simp [getKey, hobj]
      have hdone : ∃ r, some (some (VN.old y)) = some r ∧ (space = true → r ≠ none) ∧
          ∀ v', r = some v' → SettOk cf i s g v' :=
        ⟨_, rfl, by simp, fun v' hv' => by
          cases hv'; exact ⟨h, Or.inl ⟨y, rfl, hsh⟩, EOk.old hsh, trivial⟩⟩
      simp only [settleRoot, hgk]
      split
      · rename_i c z hl
        split
        · exact hdone
        · rename_i hnl
          cases hsh with
          | leaf hobj' hleaf' _ _ _ =>
            rw [hobj] at hobj'
            obtain rfl : n = _ := by injection hobj' with h1; injection h1
            exact absurd hleaf' hnl
          | @inner _ h'' _ n' hobj' _ _ _ _ _ hkids =>
            rw [hobj] at hobj'
            obtain rfl : n = n' := by injection hobj' with h1; injection h1
            have hz : Shaped cf s g h'' z := hkids c z (by rw [hl]; simp)
            exact settle_acc hcf h2 hc2 hG space f h'' (.old z) (Or.inl ⟨z, rfl, hz⟩)
              (EOk.old hz) (fun _ _ _ _ _ h => by cases h) (by omega) (by omega)
      · exact hdone
    | node b g' h' j es F dec =>
      have hvok : VOk cf s g h (.node b g' h' j es F dec) := by
        rcases hv with ⟨y', hy, _⟩ | hv
        · cases hy
        · exact hv
      obtain ⟨hh1, hh2⟩ := hvok.ht
      subst h' g'
      by_cases hF : F = []
      · subst hF
        simp only [settleRoot, List.isEmpty_nil, ite_true]
        cases space with
        | false => exact ⟨none, rfl, by simp, fun v' h => by cases h⟩
        | true =>
          simp only [Bool.not_true, Bool.false_eq_true, ite_false]
          split
          · exact ⟨_, rfl, by simp, fun v' h => by
              cases h; exact ⟨h, Or.inr hvok, he, one_of_short hvok (by simp)⟩⟩
          · cases hm : mkNode cf i s none g 0 false [] with
            | none =>
              exfalso
              unfold mkNode at hm
              simp only at hm
              split at hm
              · rename_i hc; simp at hc; omega
              · cases hm
            | some w =>
              obtain ⟨⟨F2, dec2, rfl⟩, hw⟩ := mkNode_leaf hcf hm (by simp)
              obtain ⟨hew, _⟩ := mkNode_eok hm (by simp) (by simp)
              have hF2 : F2 = [] := by
                cases hw with
                | leaf _ hF2 _ => simpa using hF2
              refine ⟨_, rfl, by simp, fun v' h => ?_⟩
              cases h
              exact ⟨0, Or.inr hw, hew, one_of_short hw (by simp [hF2])⟩
      · by_cases hone : h ≠ 0 ∧ F.length = 1
        · obtain ⟨hh0, hl1⟩ := hone
          obtain ⟨h'', rfl⟩ : ∃ h'', h = h'' + 1 := ⟨h - 1, by omega⟩
          cases hvok with
          | inner hk hne _ hFes _ =>
            have hles := flatMap_ents_length_ge es
            rw [hFes, renameHead_length] at hl1
            obtain ⟨c, ch, rfl⟩ : ∃ c ch, es = [(c, ch)] := by
              match es, hles, hl1 with
              | [], _, hl1 => simp at hl1
              | [(c, ch)], _, _ => exact ⟨c, ch, rfl⟩
              | _ :: _ :: _, hles, hl1 => simp only [List.length_cons] at hles; omega
            have hFe : F.isEmpty = false := by
              cases F with
              | nil => exact absurd rfl hF
              | cons _ _ => rfl
            have hl1' : (ents c ch).length = 1 := by simpa using hl1
            have hon : (h'' + 1 != 0 && F.length == 1) = true := by
              rw [hFes, renameHead_length]; simp [hl1']
            simp only [settleRoot, hFe, hon, Bool.false_eq_true, ite_false, ite_true]
            have hech : EOk cf i s g h'' ch := by
              cases he with
              | node _ _ _ hkids => exact hkids (c, ch) (by simp) (by omega)
            refine settle_acc hcf h2 hc2 hG space f h'' ch (Or.inr (hk (c, ch) (by simp))) hech
              ?_ (by omega) (by omega)
            intro b2 j2 es2 F2 dec2 hch k hk2 h22
            subst hch hk2
            have := ents_parts_length (c := c) (b := b2) (g := g) (h := h'') (j := j2)
              (es := es2) (F := F2) h22
            simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hl1
            omega
        · have hlen : F.length ≠ 0 := fun h0 => hF (List.length_eq_zero_iff.mp h0)
          obtain ⟨v', hs, hok⟩ := settle_up hcf h2 hc2 hG space (f + 1) h b j es F dec hvok he
            (hroom b j es F dec rfl) hF (by omega) hH (by omega)
          exact ⟨_, hs, by simp, fun v'' h => by cases h; exact hok⟩

/-! ## B. emit -/

/-- What emit needs of a node it writes: an untouched node anything, a
planned one `VOk` and `EOk`. -/
def EmOk (cf : Cfg) (i : Time) (s : Tree) (g h : Nat) (v : VN) : Prop :=
  ∀ b g' h' j es F dec, v = .node b g' h' j es F dec → VOk cf s g h v ∧ EOk cf i s g h v

theorem emitKids_some {es : List (Nat × VN)}
    (hk : ∀ e ∈ es, ∀ acc, ∃ E acc', emit cf i s e.2 acc = some (E, acc')) :
    ∀ acc, ∃ F acc', emitKids cf i s es acc = some (F, acc') := by
  induction es with
  | nil => intro acc; exact ⟨[], acc, by simp [emitKids]⟩
  | cons e es ih =>
    intro acc
    obtain ⟨E, acc1, h1⟩ := hk e (by simp) acc
    obtain ⟨F, acc2, h2⟩ := ih (fun e' he' => hk e' (by simp [he'])) acc1
    exact ⟨renameHead e.1 E ++ F, acc2, by simp [emitKids, h1, h2]⟩

/-- **emit writes every node the program makes**: emit of an untouched node,
or of a planned node with `VOk` and `EOk`, gives its entries. -/
theorem emit_some : ∀ (h : Nat) {g : Nat} {v : VN}, EmOk cf i s g h v →
    ∀ acc, ∃ E acc', emit cf i s v acc = some (E, acc')
  | h, g, .old y, _ => fun acc => ⟨[(0, y)], acc, by simp [emit]⟩
  | h, g, .node b g' h' j es F dec, hv => by
    obtain ⟨hvok, he⟩ := hv b g' h' j es F dec rfl
    obtain ⟨rfl, rfl⟩ := hvok.ht
    have hkids : ∀ acc, ∃ F acc', emitKids cf i s es acc = some (F, acc') := by
      apply emitKids_some
      intro e hes
      cases hvok with
      | leaf hold _ _ =>
        obtain ⟨y, hy⟩ := hold e hes
        intro acc; rw [hy]; exact ⟨[(0, y)], acc, by simp [emit]⟩
      | @inner h'' _ _ _ _ _ hk _ _ _ _ =>
        apply emit_some h''
        intro b2 g2 h2 j2 es2 F2 dec2 he2
        refine ⟨hk e hes, ?_⟩
        cases he with
        | node _ _ _ hkk => exact hkk e hes (by omega)
    intro acc
    obtain ⟨F0, acc1, hk1⟩ := hkids acc
    have hdec : dec = decideNode cf i (b.bind (getKey s)) j F := by
      cases he with
      | node hdec _ _ _ => exact hdec
    have hbase : ∀ x, b = some x → ∃ n, getKey s x = some n := by
      intro x hx
      cases he with
      | node _ hb _ _ =>
        obtain ⟨n, hobj, _⟩ := shaped_obj (hb x hx)
        exact ⟨n, by simp [getKey, hobj]⟩
    simp only [emit, hk1]
    cases dec with
    | same =>
      cases b with
      | none => simp [decideNode] at hdec
      | some x => exact ⟨_, _, rfl⟩
    | append =>
      cases b with
      | none => simp [decideNode] at hdec
      | some x =>
        obtain ⟨n, hn⟩ := hbase x rfl
        simp only [hn]
        exact ⟨_, _, rfl⟩
    | parts k => exact ⟨_, _, rfl⟩

/-- **A root of one node gives one entry**. -/
theorem emit_one (hcf : cf.Ok) {g h : Nat} {v : VN} (hv : EmOk cf i s g h v) (hone : One v) (acc : Acc) :
    ∃ c y acc', emit cf i s v acc = some ([(c, y)], acc') := by
  cases v with
  | old y => exact ⟨0, y, acc, by simp [emit]⟩
  | node b g' h' j es F dec =>
    obtain ⟨E, acc', hE⟩ := emit_some h hv acc
    obtain ⟨hvok, he⟩ := hv b g' h' j es F dec rfl
    obtain ⟨rfl, rfl⟩ := hvok.ht
    simp only [emit] at hE ⊢
    cases hk1 : emitKids cf i s es acc with
    | none => rw [hk1] at hE; cases hE
    | some p =>
      obtain ⟨F0, acc1⟩ := p
      rw [hk1] at hE
      simp only at hE ⊢
      cases dec with
      | same =>
        cases b with
        | none => simp at hE
        | some x => exact ⟨_, _, _, rfl⟩
      | append =>
        cases b with
        | none => simp at hE
        | some x =>
          simp only at hE ⊢
          cases hg : getKey s x with
          | none => rw [hg] at hE; cases hE
          | some n => exact ⟨_, _, _, rfl⟩
      | parts k =>
        have hk1' : 1 ≤ k := decParts_pos hcf he
        have hk2 : k < 2 := hone k rfl
        obtain rfl : k = 1 := by omega
        simp only
        have hl : (cutList (if h' == 0 then F0 else renameHead 0 F0)
            (partSizes (if h' == 0 then F0 else renameHead 0 F0).length 1 j)).length = 1 := by
          rw [cutList_length, partSizes_length]
        generalize cutList _ _ = Ps at hl
        match Ps, hl with
        | [P], _ => exact ⟨_, _, _, rfl⟩

/-! ## C. rebalance -/

/-- `joinAt`'s choice of the left neighbour. -/
def useLeftOf (cf : Cfg) (s : Tree) (es : List (Nat × VN)) (ix : Nat) : Bool :=
  match es[ix]? with
  | none => false
  | some x =>
    if ix == 0 then false
    else match es[ix - 1]?, es[ix + 1]? with
      | some _, none => true
      | some l, some _ => decide (cntOf s l.2 + x.2.size ≤ cf.c)
      | none, _ => false

/-- `joinAt` at the left one il of the two children joined. -/
def joinAtIl (cf : Cfg) (i : Time) (s : Tree) (g h : Nat)
    (down : List (Nat × VN) → Option (List (Nat × VN))) (es : List (Nat × VN)) (il : Nat) :
    Option (List (Nat × VN)) :=
  match es[il]?, es[il + 1]? with
  | some l, some r =>
    match openEs s l.2, openEs s r.2 with
    | some esL, some esR =>
      let J := esL ++ (if h == 0 then esR else renameHead r.1 esR)
      let J' := if h == 0 then some J else down J
      match J' with
      | some J' =>
        match mkNode cf i s none g h true J' with
        | some v => some (es.take il ++ [(l.1, v)] ++ es.drop (il + 2))
        | none => none
      | none => none
    | _, _ => none
  | _, _ => none

theorem joinAt_eq {g h : Nat} (down : List (Nat × VN) → Option (List (Nat × VN)))
    (es : List (Nat × VN)) (ix : Nat) :
    joinAt cf i s g h down es ix =
      joinAtIl cf i s g h down es (if useLeftOf cf s es ix then ix - 1 else ix) := rfl

/-- The child to join has a neighbour: the left one il of the two has a right
one. -/
theorem useLeft_idx {es : List (Nat × VN)} {ix : Nat} (h2 : 2 ≤ es.length) (hix : ix < es.length) :
    (if useLeftOf cf s es ix then ix - 1 else ix) + 1 < es.length := by
  have hx : es[ix]? = some es[ix] := List.getElem?_eq_getElem hix
  unfold useLeftOf
  rw [hx]
  simp only
  cases ix with
  | zero => simp; omega
  | succ k =>
    have hk : es[k]? = some es[k] := List.getElem?_eq_getElem (by omega)
    simp only [Nat.add_one_sub_one, Nat.add_eq_zero_iff, one_ne_zero, and_false, beq_iff_eq,
      ite_false, hk]
    cases hk2 : es[k + 1 + 1]? with
    | none => simp; omega
    | some z =>
      have : k + 1 + 1 < es.length := (List.getElem?_eq_some_iff.mp hk2).1
      simp only
      split <;> omega

/-- An untouched child is opened into its key node's live klongs, a planned
one into its entries: one height down, `EOk`. -/
theorem openEs_some {g h : Nat} {w : VN} (he : EOk cf i s g h w) :
    ∃ esW, openEs s w = some esW ∧ (h ≠ 0 → ∀ e ∈ esW, EOk cf i s g (h - 1) e.2) := by
  cases he with
  | @old _ y hsh =>
    obtain ⟨n, hobj, _⟩ := shaped_obj hsh
    refine ⟨(live n.ks).map (fun q => (q.1, VN.old q.2)), by simp [openEs, getKey, hobj],
      fun hh e he => ?_⟩
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp he
    cases hsh with
    | leaf => exact absurd rfl hh
    | inner hobj' _ _ _ _ _ hkids =>
      rw [hobj] at hobj'
      obtain rfl : n = _ := by injection hobj' with h1; injection h1
      exact EOk.old (hkids q.1 q.2 hq)
  | node _ _ _ hk => exact ⟨_, rfl, fun hh e he => hk e he hh⟩

/-- **One join**: two neighbours joined into one node within the level
bounds, its list rebalanced one level down. -/
theorem joinAt_acc {g h : Nat} (hG : g ≤ cf.G) (hH : h ≤ cf.H)
    {down : List (Nat × VN) → Option (List (Nat × VN))}
    (hdown : h ≠ 0 → ∀ J, (∀ e ∈ J, EOk cf i s g (h - 1) e.2) →
      ∃ J', down J = some J' ∧ ∀ e ∈ J', EOk cf i s g (h - 1) e.2)
    {es : List (Nat × VN)} {ix : Nat} (h2 : 2 ≤ es.length) (hix : ix < es.length)
    (hes : ∀ e ∈ es, EOk cf i s g h e.2) :
    ∃ es', joinAt cf i s g h down es ix = some es' ∧ ∀ e ∈ es', EOk cf i s g h e.2 := by
  rw [joinAt_eq]
  have key := useLeft_idx (cf := cf) (s := s) h2 hix
  generalize (if useLeftOf cf s es ix then ix - 1 else ix) = il at key ⊢
  have hl : es[il]? = some es[il] := List.getElem?_eq_getElem (by omega)
  have hr : es[il + 1]? = some es[il + 1] := List.getElem?_eq_getElem key
  have hlm : es[il] ∈ es := List.getElem_mem _
  have hrm : es[il + 1] ∈ es := List.getElem_mem _
  obtain ⟨esL, hoL, hkL⟩ := openEs_some (hes _ hlm)
  obtain ⟨esR, hoR, hkR⟩ := openEs_some (hes _ hrm)
  have hJ : h ≠ 0 → ∀ e ∈ esL ++ renameHead es[il + 1].1 esR, EOk cf i s g (h - 1) e.2 := by
    intro hh e he
    rcases List.mem_append.mp he with he | he
    · exact hkL hh e he
    · obtain ⟨e', he', h2⟩ := renameHead_mem he
      rw [← h2]; exact hkR hh e' he'
  obtain ⟨J', hJ'1, hJ'2⟩ : ∃ J', (if h == 0 then some (esL ++ if h == 0 then esR else
      renameHead es[il + 1].1 esR) else down (esL ++ if h == 0 then esR else
      renameHead es[il + 1].1 esR)) = some J' ∧ (h ≠ 0 → ∀ e ∈ J', EOk cf i s g (h - 1) e.2) := by
    by_cases hh : h = 0
    · subst hh; exact ⟨_, rfl, fun h0 => absurd rfl h0⟩
    · have hb : (h == 0) = false := by simp [hh]
      simp only [hb, Bool.false_eq_true, ite_false]
      obtain ⟨J', h1, h2⟩ := hdown hh _ (hJ hh)
      exact ⟨J', h1, fun _ => h2⟩
  cases hm : mkNode cf i s none g h true J' with
  | none =>
    exfalso
    unfold mkNode at hm
    simp only at hm
    split at hm
    · rename_i hc; simp at hc; omega
    · cases hm
  | some v =>
    obtain ⟨hev, _⟩ := mkNode_eok hm (by simp) (fun e he hh => hJ'2 hh e he)
    refine ⟨es.take il ++ [(es[il].1, v)] ++ es.drop (il + 2), ?_, ?_⟩
    · simp only [joinAtIl, hl, hr, hoL, hoR]
      rw [hJ'1]
      simp only [hm]
    · intro e he
      simp only [List.mem_append, List.mem_singleton] at he
      rcases he with (he | rfl) | he
      · exact hes e (List.mem_of_mem_take he)
      · exact hev
      · exact hes e (List.mem_of_mem_drop he)

theorem findSmall_lt {es : List (Nat × VN)} {ix : Nat} (h : findSmall cf es = some ix) :
    ix < es.length := by
  unfold findSmall at h
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
  have hm := List.mem_of_find?_eq_some hp
  have : p = (p.1, p.2) := rfl
  rw [this] at hm
  have := (List.mem_zipIdx hm).2.1
  omega

/-- The loop of joins: each join finds its neighbours. -/
theorem joinLoop_acc {g h : Nat} (hG : g ≤ cf.G) (hH : h ≤ cf.H)
    {down : List (Nat × VN) → Option (List (Nat × VN))}
    (hdown : h ≠ 0 → ∀ J, (∀ e ∈ J, EOk cf i s g (h - 1) e.2) →
      ∃ J', down J = some J' ∧ ∀ e ∈ J', EOk cf i s g (h - 1) e.2) :
    ∀ (n : Nat) (es : List (Nat × VN)), (∀ e ∈ es, EOk cf i s g h e.2) →
      ∃ es', joinLoop cf i s g h down n es = some es' ∧ ∀ e ∈ es', EOk cf i s g h e.2
  | 0, es, hes => ⟨es, by simp [joinLoop], hes⟩
  | n + 1, es, hes => by
    simp only [joinLoop]
    split
    · exact ⟨es, rfl, hes⟩
    · rename_i hlen
      split
      · exact ⟨es, rfl, hes⟩
      · rename_i ix hix
        obtain ⟨es1, h1, h2⟩ := joinAt_acc hG hH hdown (by omega) (findSmall_lt hix) hes
        rw [h1]
        exact joinLoop_acc hG hH hdown n es1 h2

/-- **rebalance gives the children rebalanced**, with fuel h + 1 at the
children's height h. -/
theorem rebalance_acc {g : Nat} (hG : g ≤ cf.G) : ∀ (f h : Nat) (es : List (Nat × VN)),
    h ≤ cf.H → h + 1 ≤ f → (∀ e ∈ es, EOk cf i s g h e.2) →
    ∃ es', rebalance cf i s f g h es = some es' ∧ ∀ e ∈ es', EOk cf i s g h e.2
  | 0, _, _, _, hf, _ => by omega
  | f + 1, h, es, hH, hf, hes => by
    have hes1 : ∀ e ∈ es.filter (fun e => !e.2.isEmpty), EOk cf i s g h e.2 :=
      fun e he => hes e (List.mem_of_mem_filter he)
    simp only [rebalance]
    split
    · exact ⟨_, rfl, hes1⟩
    · exact joinLoop_acc hG hH (fun hh J hJ =>
        rebalance_acc hG f (h - 1) J (by omega) (by omega) hJ) _ _ hes1

/-! ## D. plan -/

theorem insertCv_length_le (c : Nat) (y : NodeId) : ∀ m : List (Nat × NodeId),
    (insertCv c y m).length ≤ m.length + 1
  | [] => by simp [insertCv]
  | (c', y') :: r => by
    unfold insertCv
    split
    · simp
    · split
      · simp
      · have := insertCv_length_le c y r
        simp only [List.length_cons]; omega

theorem foldl_length_le {α β : Type} (st : List β → α → List β)
    (hst : ∀ m x, (st m x).length ≤ m.length + 1) :
    ∀ (l : List α) (m : List β), (l.foldl st m).length ≤ m.length + l.length
  | [], m => by simp
  | x :: l, m => by
    simp only [List.foldl_cons, List.length_cons]
    have := foldl_length_le st hst l (st m x)
    have := hst m x
    omega

/-- A node's live klongs are no more than its klongs. -/
theorem live_length_le (ks : List Klong) : (live ks).length ≤ ks.length := by
  unfold live liveWith
  refine le_trans (foldl_length_le _ ?_ ks.zipIdx []) (by simp)
  intro m x
  obtain ⟨k, j⟩ := x
  cases k with
  | key c y =>
    simp only
    split
    · omega
    · exact insertCv_length_le c y m
  | _ => simp

/-- The fuel's unit for a transaction of p operations: what one level of the
recursions uses at most. -/
def unitK (cf : Cfg) (p : Nat) : Nat := cf.M + p + 2 * cf.H + 6

/-- The levels below a key node of segment g at height h in the order of the
recursions (its level, less one). -/
def dd (cf : Cfg) (g h : Nat) : Nat := (cf.G - g) * (cf.H + 1) + h

theorem dd_next {g : Nat} (hg : g + 1 ≤ cf.G) : dd cf (g + 1) cf.H + 1 = dd cf g 0 := by
  unfold dd
  obtain ⟨d, hd⟩ : ∃ d, cf.G - g = d + 1 := ⟨cf.G - g - 1, by omega⟩
  rw [hd, show cf.G - (g + 1) = d by omega, Nat.succ_mul]
  omega

theorem dd_mono {g h h' : Nat} (hh : h ≤ h') : dd cf g h ≤ dd cf g h' := by
  unfold dd; omega

/-- The operations at segment g: keys the tree can hold, of more than g
segments. -/
def OpsAt (cf : Cfg) (g : Nat) (ops : List Op) : Prop :=
  ∀ op ∈ ops, keyOk cf op.key = true ∧ g < op.key.length

/-- What the induction needs of the tree before, for p operations. -/
structure AEnv (cf : Cfg) (s : Tree) (p : Nat) : Prop where
  hcf : cf.Ok
  room : Room cf s p
  size : ∀ x n, s.obj x = some (.key n) → n.ks.length ≤ cf.M
  r0 : ∃ y, y ∈ reach s

/-- A segment's root: none, or a key node shaped as PE's trees at the height
of its level, sound, its nodes among the tree's. -/
def RootS (cf : Cfg) (s : Tree) (g : Nat) (root : Option NodeId) : Prop :=
  ∀ y, root = some y → Shaped cf s g (htIn cf s y) y ∧ Good s y 0 none ∧ (R s y).Sublist (reach s)

/-- plan succeeds at fuel f. -/
def PlanAcc (cf : Cfg) (i : Time) (s : Tree) (p f : Nat) : Prop :=
  ∀ (x : NodeId) (g h : Nat) (ops : List Op) (acc : Acc), Shaped cf s g h x →
    (∃ lo hi, Good s x lo hi) → (R s x).Sublist (reach s) → OpsAt cf g ops → ops.length ≤ p →
    (dd cf g h + 1) * unitK cf p ≤ f → ∃ v acc', plan cf i s f x g h ops acc = some (v, acc')

/-- A segment leaf's list before its groups: a long compare value of a group
still to come names a segment's root. -/
def EsInv (cf : Cfg) (s : Tree) (g : Nat) (es : List (Nat × NodeId)) (cvs : List Nat) : Prop :=
  ∀ c ∈ cvs, isLong c = true → RootS cf s (g + 1) (es.lookup c)

/-- applyGroups succeeds at fuel f. -/
def GroupsAcc (cf : Cfg) (i : Time) (s : Tree) (p f : Nat) : Prop :=
  ∀ (g : Nat) (es : List (Nat × NodeId)) (cvs : List Nat) (ops : List Op) (acc : Acc),
    g ≤ cf.G → OpsAt cf g ops → ops.length ≤ p → cvs.Nodup → EsInv cf s g es cvs →
    dd cf g 0 * unitK cf p + cvs.length + 1 ≤ f →
    ∃ es' acc', applyGroups cf i s f g es cvs ops acc = some (es', acc')

/-- planTree succeeds at fuel f. -/
def TreeAcc (cf : Cfg) (i : Time) (s : Tree) (p f : Nat) : Prop :=
  ∀ (root : Option NodeId) (g : Nat) (ops : List Op) (acc : Acc), g ≤ cf.G → RootS cf s g root →
    OpsAt cf g ops → ops.length ≤ p → (dd cf g cf.H + 1) * unitK cf p + 1 ≤ f →
    ∃ res acc', planTree cf i s f root g ops acc = some (res, acc')

theorem sublist_flatMap_mem {α β : Type} (f : α → List β) {a : α} :
    ∀ {L : List α}, a ∈ L → (f a).Sublist (L.flatMap f)
  | [], h => by simp at h
  | b :: L, h => by
    rw [List.flatMap_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact List.sublist_append_left _ _
    · exact (sublist_flatMap_mem f h).trans (List.sublist_append_right _ _)

/-- A child's nodes are among its parent's. -/
theorem R_sub_kid {x : NodeId} {lo : Nat} {hi : Option Nat} (hg : Good s x lo hi) {n : KNode}
    (hobj : s.obj x = some (.key n)) {c : Nat} {y : NodeId} (hm : (c, y) ∈ live n.ks) :
    (R s y).Sublist (R s x) := by
  rw [R_good hg hobj]
  exact (sublist_flatMap_mem (fun cy : Nat × NodeId => R s cy.2) hm).cons x

theorem R_head (s : Tree) (y : NodeId) : y ∈ R s y := by
  unfold R
  cases s.fuel y <;> simp [reachAt]

/-- The groups of a segment leaf: a long compare value's group goes on to the
next segment's tree, within G. -/
theorem groups_step (env : AEnv cf s p) {f0 : Nat} (IH : ∀ f' < f0, TreeAcc cf i s p f') :
    ∀ (cvs : List Nat) (f g : Nat) (es : List (Nat × NodeId)) (ops : List Op) (acc : Acc),
    f ≤ f0 → g ≤ cf.G → OpsAt cf g ops → ops.length ≤ p → cvs.Nodup → EsInv cf s g es cvs →
    dd cf g 0 * unitK cf p + cvs.length + 1 ≤ f →
    ∃ es' acc', applyGroups cf i s f g es cvs ops acc = some (es', acc')
  | [], f, g, es, ops, acc, _, _, _, _, _, _, hf => by
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    exact ⟨es, acc, by simp [applyGroups]⟩
  | cv :: cvs, f, g, es0, ops, acc, hf0, hG, hops, hp, hnd, hinv, hf => by
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    have hnd' := (List.nodup_cons.mp hnd)
    unfold applyGroups
    simp only
    generalize hq : List.foldl _ (es0, acc) _ = q
    have hq1 : ∀ c, c ≠ cv → q.1.lookup c = es0.lookup c := by
      rw [← hq]
      refine foldl_inv (fun q : List (Nat × NodeId) × Acc =>
        ∀ c, c ≠ cv → q.1.lookup c = es0.lookup c) _ ?_ _ _ (fun _ _ => rfl)
      intro q' op hq'
      cases op with
      | put k hv =>
        intro c hc
        show (setEntry cv _ q'.1).lookup c = _
        rw [setEntry_lookup, ite_eq_right hc]
        exact hq' c hc
      | del k =>
        intro c hc
        show (removeEntry cv q'.1).lookup c = _
        rw [removeEntry_lookup, ite_eq_right hc]
        exact hq' c hc
    have hinv2 : ∀ es2 : List (Nat × NodeId), (∀ c, c ≠ cv → es2.lookup c = q.1.lookup c) →
        EsInv cf s g es2 cvs := by
      intro es2 h2 c hc hl
      have hne : c ≠ cv := fun h => hnd'.1 (h ▸ hc)
      rw [h2 c hne, hq1 c hne]
      exact hinv c (List.mem_cons_of_mem _ hc) hl
    have hrest : ∀ es2 acc2, (∀ c, c ≠ cv → es2.lookup c = q.1.lookup c) →
        ∃ es' acc', applyGroups cf i s f' g es2 cvs ops acc2 = some (es', acc') := by
      intro es2 acc2 h2
      exact groups_step env IH cvs f' g es2 ops acc2 (by omega) hG hops hp hnd'.2 (hinv2 es2 h2)
        (by simp only [List.length_cons] at hf; omega)
    obtain ⟨es1, acc1⟩ := q
    simp only at hq1 hinv2 hrest ⊢
    split
    · exact hrest es1 acc1 (fun _ _ => rfl)
    · rename_i hsubs
      -- a long compare value: no key ends here, the next segment's tree
      have hw : ∀ op ∈ ops, keyWf op.key = true := fun op hop => by
        have := (hops op hop).1
        simp only [keyOk, Bool.and_eq_true] at this
        exact this.1
      obtain ⟨op0, hop0⟩ : ∃ op0, op0 ∈ (ops.filter (fun op => segAt g op == cv)).filter
          (fun op => !endsAt g op) := by
        cases hl : (ops.filter (fun op => segAt g op == cv)).filter (fun op => !endsAt g op) with
        | nil => rw [hl] at hsubs; simp at hsubs
        | cons a _ => exact ⟨a, by simp⟩
      obtain ⟨hop0g, hop0e⟩ := List.mem_filter.mp hop0
      obtain ⟨hop0m, hop0c⟩ := mem_grp hop0g
      have hlong : isLong cv = true := by
        have := endsAt_of_keyWf (hw op0 hop0m) (hops op0 hop0m).2
        rw [hop0c] at this
        have he : endsAt g op0 = false := by simpa using hop0e
        rw [he] at this
        cases h : isLong cv
        · rw [h] at this; simp at this
        · rfl
      have hnoend : (ops.filter (fun op => segAt g op == cv)).filter (endsAt g) = [] := by
        rw [List.filter_eq_nil_iff]
        intro op hop
        obtain ⟨hm, hc⟩ := mem_grp hop
        rw [endsAt_of_keyWf (hw op hm) (hops op hm).2, hc, hlong]
        simp
      rw [hnoend] at hq
      simp only [List.foldl_nil, Prod.mk.injEq] at hq
      obtain ⟨rfl, rfl⟩ := hq
      have hsubs_ops : OpsAt cf (g + 1)
          ((ops.filter (fun op => segAt g op == cv)).filter (fun op => !endsAt g op)) := by
        intro op hop
        obtain ⟨hg1, he1⟩ := List.mem_filter.mp hop
        obtain ⟨hm, _⟩ := mem_grp hg1
        refine ⟨(hops op hm).1, ?_⟩
        have := (hops op hm).2
        simp only [endsAt, Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne, ne_eq] at he1
        omega
      have hG1 : g + 1 ≤ cf.G := by
        have h1 := (hsubs_ops op0 hop0).2
        have h2 := (hops op0 hop0m).1
        simp only [keyOk, Bool.and_eq_true, decide_eq_true_eq] at h2
        omega
      have hlen : ((ops.filter (fun op => segAt g op == cv)).filter
          (fun op => !endsAt g op)).length ≤ p :=
        le_trans ((List.filter_sublist.trans List.filter_sublist).length_le) hp
      have hfT : (dd cf (g + 1) cf.H + 1) * unitK cf p + 1 ≤ f' := by
        rw [dd_next hG1]
        simp only [List.length_cons] at hf
        omega
      obtain ⟨res, acc2, hT⟩ := IH f' (by omega) (es0.lookup cv) (g + 1) _ acc hG1
        (hinv cv (List.mem_cons_self) hlong) hsubs_ops hlen hfT
      rw [hT]
      cases res with
      | none =>
        simp only
        exact hrest _ acc2 (fun c hc => by rw [removeEntry_lookup, ite_eq_right hc])
      | some y =>
        simp only
        exact hrest _ acc2 (fun c hc => by rw [setEntry_lookup, ite_eq_right hc])

/-- A planned root's cut has room below H: it is no longer than the tree's
nodes plus the operations, which `Room` bounds at its height. -/
theorem roomD_of_size {g h : Nat} {b : Option NodeId} {j : Bool} {es : List (Nat × VN)}
    {F : List (Nat × Option NodeId)} {dec : Dec} (hv : VOk cf s g h (.node b g h j es F dec))
    (hsz : (VN.node b g h j es F dec).size < 2 ^ (cf.H - h)) : RoomD cf h dec := by
  intro k hk h2
  have hd : DecOk dec F := by cases hv <;> assumption
  have := hd k hk h2
  simp only [VN.size] at hsz
  omega

/-- The room at a planned root's height from `Room`: for a node of the tree,
or for a new tree (height 0). -/
theorem room_at (env : AEnv cf s p) {y : NodeId} (hy : y ∈ reach s) :
    (reach s).length + p < 2 ^ (cf.H - htIn cf s y) := env.room.room y hy

theorem room_zero (env : AEnv cf s p) : (reach s).length + p < 2 ^ (cf.H - 0) := by
  obtain ⟨y, hy⟩ := env.r0
  exact lt_of_lt_of_le (env.room.room y hy) (Nat.pow_le_pow_right (by omega) (by omega))

/-- A segment's tree: planned, its root settled, emitted. -/
theorem tree_step (env : AEnv cf s p) {f : Nat} (IHp : ∀ f' < f, PlanAcc cf i s p f')
    (IHg : ∀ f' < f, GroupsAcc cf i s p f') : TreeAcc cf i s p f := by
  intro root g ops acc hG hroot hops hp hf
  obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  have hK : unitK cf p = cf.M + p + 2 * cf.H + 6 := rfl
  have hK1 : unitK cf p ≤ (dd cf g cf.H + 1) * unitK cf p := Nat.le_mul_of_pos_left _ (by omega)
  -- settle and emit the planned root
  have tail : ∀ (v : VN) (ht : Nat) (acc1 : Acc), VOk cf s g ht v → EOk cf i s g ht v →
      ht ≤ cf.H → v.size < 2 ^ (cf.H - ht) →
      ∃ r, settleRoot cf i s f' g v false = some r ∧
        (r = none ∨ ∃ v' c y acc2, r = some v' ∧ emit cf i s v' acc1 = some ([(c, y)], acc2)) := by
    intro v ht acc1 hvok hev hhH hsz
    obtain ⟨r, hs, _, hok⟩ := settle_acc env.hcf env.room.h2 env.room.cap2 hG false f' ht v
      (Or.inr hvok) hev (fun b j es F dec hveq => by
        subst hveq; exact roomD_of_size hvok hsz) hhH (by omega)
    refine ⟨r, hs, ?_⟩
    cases r with
    | none => exact Or.inl rfl
    | some v' =>
      obtain ⟨h', hro, he', hone⟩ := hok v' rfl
      have hem : EmOk cf i s g h' v' := by
        intro b g2 h2 j es F dec hveq
        subst hveq
        rcases hro with ⟨y, hy, _⟩ | hro
        · cases hy
        · exact ⟨hro, he'⟩
      obtain ⟨c, y, acc2, hE⟩ := emit_one env.hcf hem hone acc1
      exact Or.inr ⟨v', c, y, acc2, rfl, hE⟩
  unfold planTree
  cases root with
  | some y =>
    obtain ⟨hsh, hgy, hsub⟩ := hroot y rfl
    obtain ⟨n, hobj, _, _, _, hHy⟩ := shaped_obj hsh
    have hgk : getKey s y = some n := by simp [getKey, hobj]
    have hht : htIn cf s y = cf.htOf n.level := by simp [htIn, hobj]
    have hfp : (dd cf g (htIn cf s y) + 1) * unitK cf p ≤ f' := by
      have := Nat.mul_le_mul_right (unitK cf p)
        (Nat.add_le_add_right (dd_mono (cf := cf) (g := g) hHy) 1)
      omega
    obtain ⟨v, acc1, hpl⟩ := IHp f' (by omega) y g (htIn cf s y) ops acc hsh ⟨0, none, hgy⟩
      hsub hops hp hfp
    have hsize := plan_size_le env.hcf hpl hsh hgy
    have hR := hsub.length_le
    have hroomy := room_at env (hsub.subset (R_head s y))
    obtain ⟨_, _, _, hvok⟩ := plan_inst env.hcf hpl hsh hgy
    obtain ⟨r, hs, hr⟩ := tail v (htIn cf s y) acc1 hvok
      (plan_own env.hcf hpl hsh hgy).1 hHy (by omega)
    rw [hht] at hpl
    simp only [hgk, hpl, hs]
    rcases hr with rfl | ⟨v', c, y', acc2, rfl, hE⟩
    · exact ⟨none, acc1, rfl⟩
    · simp only [hE]; exact ⟨_, _, rfl⟩
  | none =>
    obtain ⟨es, acc1, ha⟩ := IHg f' (by omega) g [] (touched g ops) ops acc hG hops hp
      (nodup_touched g ops) (fun c _ _ y hy => by simp at hy)
      (by
        have h1 := touched_length_le g ops
        have := Nat.mul_le_mul_right (unitK cf p)
          (Nat.add_le_add_right (dd_mono (cf := cf) (g := g) (Nat.zero_le cf.H)) 1)
        rw [Nat.succ_mul] at this
        omega)
    cases hm : mkNode cf i s none g 0 false (es.map (fun e => (e.1, VN.old e.2))) with
    | none =>
      exfalso
      unfold mkNode at hm
      simp only at hm
      split at hm
      · rename_i hc; simp at hc; omega
      · cases hm
    | some v =>
      have hsize := new_size_le ha hm
      have hr0 := room_zero env
      obtain ⟨⟨_, _, hveq⟩, hvok⟩ := mkNode_leaf env.hcf hm (by
        intro (e : Nat × VN) he; obtain ⟨q, _, rfl⟩ := List.mem_map.mp he; exact ⟨q.2, rfl⟩)
      obtain ⟨hev, _⟩ := mkNode_eok hm (by simp) (by simp)
      obtain ⟨r, hs, hr⟩ := tail v 0 acc1 hvok hev (Nat.zero_le _) (by omega)
      have ha' : applyGroups cf i s f' g [] ((ops.map (segAt g)).eraseDups) ops acc =
          some (es, acc1) := ha
      simp only [ha', hm, Option.map_some, hs]
      rcases hr with rfl | ⟨v', c, y', acc2, rfl, hE⟩
      · exact ⟨none, acc1, rfl⟩
      · simp only [hE]; exact ⟨_, _, rfl⟩

theorem route_length {α β : Type} (cv : α → Nat) : ∀ (lv : List (Nat × β)) (ops : List α),
    (Contract.PE.route cv lv ops).length = lv.length
  | [], _ => rfl
  | [_], _ => rfl
  | _ :: (c', y) :: r, ops => by
    simp only [Contract.PE.route, List.length_cons]
    rw [route_length cv ((c', y) :: r)]
    simp

theorem route_sub {α β : Type} (cv : α → Nat) : ∀ (lv : List (Nat × β)) (ops : List α),
    ∀ o ∈ Contract.PE.route cv lv ops, o.Sublist ops
  | [], _ => by simp [Contract.PE.route]
  | [_], _ => by simp [Contract.PE.route]
  | _ :: (c', y) :: r, ops => by
    intro o ho
    simp only [Contract.PE.route, List.mem_cons] at ho
    rcases ho with rfl | ho
    · exact List.filter_sublist
    · exact (route_sub cv ((c', y) :: r) _ o ho).trans List.filter_sublist

/-- The children of an inner node planned: each untouched, or planned one
height down. -/
theorem planKids_acc (env : AEnv cf s p) {f0 : Nat} (IHp : ∀ f' < f0, PlanAcc cf i s p f')
    {g h : Nat} : ∀ (lv : List (Nat × NodeId)) (os : List (List Op)) (F : Nat) (acc : Acc),
    F ≤ f0 → os.length = lv.length →
    (∀ e ∈ lv, Shaped cf s g h e.2 ∧ (∃ lo hi, Good s e.2 lo hi) ∧ (R s e.2).Sublist (reach s)) →
    (∀ o ∈ os, OpsAt cf g o ∧ o.length ≤ p) →
    (dd cf g h + 1) * unitK cf p + lv.length + 1 ≤ F →
    ∃ es acc', planKids cf i s F g (h + 1) lv os acc = some (es, acc') ∧
      ∀ e ∈ es, EOk cf i s g h e.2
  | [], os, F, acc, _, _, _, _, hF => by
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    exact ⟨[], acc, by simp [planKids], by simp⟩
  | (c, y) :: rest, [], F, acc, _, hl, _, _, _ => by simp at hl
  | (c, y) :: rest, o :: os, F, acc, hF0, hl, hlv, hos, hF => by
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    have hlv' : ∀ e ∈ rest, Shaped cf s g h e.2 ∧ (∃ lo hi, Good s e.2 lo hi) ∧
        (R s e.2).Sublist (reach s) := fun e he => hlv e (List.mem_cons_of_mem _ he)
    have hos' : ∀ o ∈ os, OpsAt cf g o ∧ o.length ≤ p := fun o ho => hos o (List.mem_cons_of_mem _ ho)
    obtain ⟨hsh, ⟨lo, hi, hgy⟩, hsub⟩ := hlv (c, y) List.mem_cons_self
    simp only [List.length_cons] at hF
    simp only [planKids, Nat.add_sub_cancel]
    split
    · obtain ⟨es, acc', h1, h2⟩ := planKids_acc env IHp rest os F' acc (by omega) hl hlv' hos'
        (by omega)
      rw [h1]
      refine ⟨_, _, rfl, ?_⟩
      intro e he
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · exact EOk.old hsh
      · exact h2 e he
    · obtain ⟨hop, hlen⟩ := hos o List.mem_cons_self
      obtain ⟨v, acc1, hpl⟩ := IHp F' (by omega) y g h o acc hsh ⟨lo, hi, hgy⟩ hsub hop hlen
        (by omega)
      rw [hpl]
      simp only
      obtain ⟨es, acc', h1, h2⟩ := planKids_acc env IHp rest os F' acc1 (by omega) hl hlv' hos'
        (by omega)
      rw [h1]
      refine ⟨_, _, rfl, ?_⟩
      intro e he
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · exact (plan_own env.hcf hpl hsh hgy).1
      · exact h2 e he

/-- plan of a key node: a segment leaf's groups, or an inner node's
children planned and rebalanced. -/
theorem plan_step (env : AEnv cf s p) {f : Nat} (IHp : ∀ f' < f, PlanAcc cf i s p f')
    (IHg : ∀ f' < f, GroupsAcc cf i s p f') : PlanAcc cf i s p f := by
  intro x g h ops acc hsh ⟨lo, hi, hg⟩ hsub hops hp hf
  have hK : unitK cf p = cf.M + p + 2 * cf.H + 6 := rfl
  obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by
    have : unitK cf p ≤ (dd cf g h + 1) * unitK cf p := Nat.le_mul_of_pos_left _ (by omega)
    omega⟩
  obtain ⟨n, hobj, hlev, hleaf, hG, hH⟩ := shaped_obj hsh
  have hgk : getKey s x = some n := by simp [getKey, hobj]
  have hsz : (live n.ks).length ≤ cf.M := le_trans (live_length_le n.ks) (env.size x n hobj)
  have hfe : (dd cf g h + 1) * unitK cf p = dd cf g h * unitK cf p + unitK cf p := Nat.succ_mul _ _
  cases h with
  | zero =>
    have hleaf' : n.leaf = true := by simpa using hleaf
    obtain ⟨es, acc1, ha⟩ := IHg f' (by omega) g (live n.ks) (touched g ops) ops acc hG hops hp
      (nodup_touched g ops) (by
        intro c _ hc y hy
        have hm := lookup_mem hy
        cases hsh with
        | leaf hobj' _ _ _ hlong =>
          rw [hobj] at hobj'
          obtain rfl : n = _ := by injection hobj' with h1; injection h1
          refine ⟨hlong c y hm hc, ?_, (R_sub_kid hg hobj hm).trans hsub⟩
          cases hg with
          | mk _ _ _ n' hobj'' _ _ _ _ _ hseg _ =>
            rw [hobj] at hobj''
            obtain rfl : n = n' := by injection hobj'' with h1; injection h1
            exact hseg hleaf' c y hm hc)
      (by have := touched_length_le g ops; omega)
    simp only [plan, hgk, beq_self_eq_true, ite_true]
    have ha' : applyGroups cf i s f' g (live n.ks) ((ops.map (segAt g)).eraseDups) ops acc =
        some (es, acc1) := ha
    rw [ha']
    simp only [mkNode, beq_self_eq_true, ite_true, hgk]
    exact ⟨_, _, rfl⟩
  | succ h =>
    have hleaf' : n.leaf = false := by simpa using hleaf
    have hkids : ∀ c y, (c, y) ∈ live n.ks → Shaped cf s g h y := by
      cases hsh with
      | inner hobj' _ _ _ _ _ hk =>
        rw [hobj] at hobj'
        obtain rfl : n = _ := by injection hobj' with h1; injection h1
        exact hk
    have hgkid : ∀ c y, (c, y) ∈ live n.ks → ∃ lo hi, Good s y lo hi := by
      intro c y hm
      obtain ⟨pre, post, he⟩ := List.append_of_mem hm
      cases hg with
      | mk _ _ _ n' hobj'' _ _ _ _ _ _ hkid =>
        rw [hobj] at hobj''
        obtain rfl : n = n' := by injection hobj'' with h1; injection h1
        exact ⟨_, _, hkid hleaf' pre c y post he⟩
    have hdd : dd cf g (h + 1) = dd cf g h + 1 := by unfold dd; omega
    obtain ⟨es, acc1, hk1, hk2⟩ := planKids_acc env IHp (live n.ks)
      (Contract.PE.route (segAt g) (live n.ks) ops) f' acc (by omega) (route_length _ _ _)
      (fun e he => ⟨hkids e.1 e.2 he, hgkid e.1 e.2 he, (R_sub_kid hg hobj he).trans hsub⟩)
      (fun o ho => ⟨fun op hop => hops op ((route_sub _ _ _ o ho).subset hop),
        le_trans (route_sub _ _ _ o ho).length_le hp⟩)
      (by
        rw [hdd, Nat.succ_mul] at hf
        have : (dd cf g h + 1) * unitK cf p = dd cf g h * unitK cf p + unitK cf p := Nat.succ_mul _ _
        omega)
    obtain ⟨es2, hr, _⟩ := rebalance_acc (i := i) (s := s) hG (f' + 1) h es (by omega)
      (by
        have : unitK cf p ≤ (dd cf g (h + 1) + 1) * unitK cf p := Nat.le_mul_of_pos_left _ (by omega)
        omega) hk2
    simp only [plan, hgk, Nat.add_one_ne_zero, beq_iff_eq, ite_false, Nat.add_sub_cancel, hk1, hr]
    simp only [mkNode, hgk]
    exact ⟨_, _, rfl⟩

/-- **The induction on the fuel**: plan, a segment leaf's groups, and a
segment's tree succeed with the fuel their depth asks. -/
theorem acc_all (env : AEnv cf s p) :
    ∀ f, PlanAcc cf i s p f ∧ GroupsAcc cf i s p f ∧ TreeAcc cf i s p f := by
  intro f
  induction f using Nat.strong_induction_on with
  | _ f IH =>
    have IHp : ∀ f' < f, PlanAcc cf i s p f' := fun f' h => (IH f' h).1
    have IHg : ∀ f' < f, GroupsAcc cf i s p f' := fun f' h => (IH f' h).2.1
    have IHt : ∀ f' < f, TreeAcc cf i s p f' := fun f' h => (IH f' h).2.2
    refine ⟨plan_step env IHp IHg, ?_, tree_step env IHp IHg⟩
    intro g es cvs ops acc hG hops hp hnd hinv hf
    exact groups_step env IHt cvs f g es ops acc le_rfl hG hops hp hnd hinv hf

/-! ## E. The transaction -/

theorem opsOk_dropNoops {ops : List Op} (hputs : ∀ k v, Op.put k v ∈ ops → keyOk cf k = true) :
    opsOk cf (dropNoops cf ops) = true := by
  unfold opsOk dropNoops
  rw [List.all_eq_true]
  intro op hop
  obtain ⟨hm, hp⟩ := List.mem_filter.mp hop
  cases op with
  | put k v => exact hputs k v hm
  | del k => simpa [Op.key] using hp

theorem keyOk_pos {k : Key} (h : keyOk cf k = true) : 0 < k.length := by
  cases k with
  | nil => simp [keyOk, keyWf] at h
  | cons _ _ => simp

/-- **PE accepts every transaction but those it refuses by design**: from a
state PE keeps (`Inv`), for parameters with `Cfg.Ok`, PE's transaction at
any time gives a state (`peTx` is not none) if every put's key is one the
tree can hold (`keyOk`: well formed, of at most G + 1 segments), the
operations and the parameters are within the program's fuel (`FuelOk`), and
H leaves room for the transaction (`Room`: h and cap at least 2, and
2^(H - e) more than the tree's nodes plus the operations, at the height e of
every node of the tree). A delete of a key the tree cannot hold is accepted
(dropped as the noop it is). -/
theorem pe_accepts (hcf : cf.Ok) {t : Time} {tp : Top} {next : NodeId} {ops : List Op}
    (hI : Inv cf t s tp next) (hputs : ∀ k v, Op.put k v ∈ ops → keyOk cf k = true)
    (hfuel : FuelOk cf ops.length) (hroom : Room cf s ops.length) :
    ∃ o, peTx cf i s tp next ops = some o := by
  obtain ⟨r, hr, hsh⟩ := hI.shaped
  have hreach : reach s = R s r := reach_eq_R hr
  have env : AEnv cf s ops.length := {
    hcf := hcf, room := hroom,
    size := fun x n hx => by
      have := (hI.sok x n hx).1
      simp only [nodeOk, Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.1.1
    r0 := ⟨r, by rw [hreach]; exact R_head s r⟩ }
  obtain ⟨n, hobj, _, _, _, hH⟩ := shaped_obj hsh
  have hgk : getKey s r = some n := by simp [getKey, hobj]
  have hht : htIn cf s r = cf.htOf n.level := by simp [htIn, hobj]
  have hgood : Good s r 0 none := good_of_invOk hr hI.inv
  have hok := opsOk_dropNoops hputs
  have hsub' : (dropNoops cf ops).Sublist ops := List.filter_sublist
  have hops' : OpsAt cf 0 (dropNoops cf ops) := by
    intro op hop
    have h1 : keyOk cf op.key = true := by
      unfold opsOk at hok
      exact List.all_eq_true.mp hok op hop
    exact ⟨h1, keyOk_pos h1⟩
  -- the fuel
  have hK : unitK cf ops.length = cf.M + ops.length + 2 * cf.H + 6 := rfl
  have hGH : dd cf 0 (htIn cf s r) + 1 ≤ (cf.G + 1) * (cf.H + 1) := by
    unfold dd
    rw [Nat.sub_zero, Nat.succ_mul]
    omega
  have hfp : (dd cf 0 (htIn cf s r) + 1) * unitK cf ops.length ≤ fuel :=
    le_trans (Nat.mul_le_mul_right _ hGH) hfuel
  have hfs : htIn cf s r + cf.H + 2 ≤ fuel := by
    have : unitK cf ops.length ≤ (dd cf 0 (htIn cf s r) + 1) * unitK cf ops.length :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega
  -- plan
  obtain ⟨v, acc1, hpl⟩ := ((acc_all (i := i) env) fuel).1 r 0 (htIn cf s r) (dropNoops cf ops)
    ⟨[], next⟩ hsh ⟨0, none, hgood⟩ (by rw [hreach]) hops' hsub'.length_le hfp
  obtain ⟨_, _, _, hvok⟩ := plan_inst hcf hpl hsh hgood
  have hev := (plan_own hcf hpl hsh hgood).1
  have hsize := plan_size_le hcf hpl hsh hgood
  have hR : (R s r).length = (reach s).length := by rw [hreach]
  have hroomr := room_at env (show r ∈ reach s by rw [hreach]; exact R_head s r)
  have hlen := hsub'.length_le
  -- settle and emit
  obtain ⟨rr, hs, hne, hsett⟩ := settle_acc hcf hroom.h2 hroom.cap2 (Nat.zero_le cf.G) true fuel
    (htIn cf s r) v (Or.inr hvok) hev (fun b j es F dec hveq => by
      subst hveq; exact roomD_of_size hvok (by omega)) hH hfs
  obtain ⟨v', rfl⟩ : ∃ v', rr = some v' := by
    cases rr with
    | none => exact absurd rfl (hne rfl)
    | some v' => exact ⟨v', rfl⟩
  obtain ⟨h', hro, he', hone⟩ := hsett v' rfl
  have hem : EmOk cf i s 0 h' v' := by
    intro b g2 h2 j es F dec hveq
    subst hveq
    rcases hro with ⟨y, hy, _⟩ | hro
    · cases hy
    · exact ⟨hro, he'⟩
  obtain ⟨c, r', acc2, hE⟩ := emit_one hcf hem hone acc1
  rw [hht] at hpl
  unfold peTx
  simp only [hok, Bool.not_true, Bool.false_eq_true, ite_false, hr, hgk, hpl, hs, hE]
  split
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- **PE refuses a put of a key the tree cannot hold** (the converse for the
keys): a transaction with a put of a key that is not well formed or has more
than G + 1 segments gives no state. -/
theorem pe_refuses {tp : Top} {next : NodeId} {ops : List Op} {k : Key} {v : Nat}
    (hput : Op.put k v ∈ ops) (hk : keyOk cf k = false) : peTx cf i s tp next ops = none := by
  have hno : opsOk cf (dropNoops cf ops) = false := by
    unfold opsOk
    rw [List.all_eq_false]
    exact ⟨.put k v, List.mem_filter.mpr ⟨hput, rfl⟩, by simp [Op.key, hk]⟩
  unfold peTx
  simp [hno]

/-- **A transaction from a state PE keeps, accepted and meeting the
contract**: `pe_accepts` with `pe_step`. -/
theorem pe_accepts_step (hcf : cf.Ok) {i : Time} (hi : 1 ≤ i) {tp : Top} {next : NodeId}
    {ops : List Op} (hI : Inv cf (i - 1) s tp next)
    (hputs : ∀ k v, Op.put k v ∈ ops → keyOk cf k = true) (hfuel : FuelOk cf ops.length)
    (hroom : Room cf s ops.length) :
    ∃ o, peTx cf i s tp next ops = some o ∧ Contract cf.params i s ops o.D (o.tree s) ∧
      Contract.TreeOk ((o.tree s).at i) ∧ TopStep i tp o.top ∧ (o.tree s).roots = rootsOf o.top ∧
      Inv cf i (o.tree s) o.top o.next := by
  obtain ⟨o, hw⟩ := pe_accepts (i := i) hcf hI hputs hfuel hroom
  exact ⟨o, hw, pe_step hcf hi hI hw⟩

/-- **Every history PE writes from the empty tree goes on**: by any
transaction whose puts' keys the tree can hold, within the fuel, for which H
leaves room. -/
theorem pe_extend (hcf : cf.Ok) {txs : List (List Op)} {tp : Top} {nx : NodeId}
    (hh : PeHist cf (startTree cf) startTop startNext txs s tp nx) {ops : List Op}
    (hputs : ∀ k v, Op.put k v ∈ ops → keyOk cf k = true) (hfuel : FuelOk cf ops.length)
    (hroom : Room cf s ops.length) :
    ∃ o, peTx cf (txs.length + 1) s tp nx ops = some o ∧
      PeHist cf (startTree cf) startTop startNext (txs ++ [ops]) (o.tree s) o.top o.next := by
  obtain ⟨h0, hst, htop⟩ := start_inv hcf
  have hI := (pe_meetsTop hcf h0 hst htop hh).2
  obtain ⟨o, hw⟩ := pe_accepts (i := txs.length + 1) hcf hI hputs hfuel hroom
  exact ⟨o, hw, PeHist.step hh hw⟩

end Contract.PE
