/-
The contract package (bergdb 030-24): proofs for RC2 and RC3 on BergDB's key
tree (Contract/ReclaimTree.lean), in the contract's words.

A sound key node with a live klong has a value below it (`Good.val_below`):
a live klong of an inner node, or of a long segment, names a sound key node
with a live klong, on a lower level; a short segment's names a value. And
every node that the walk reaches from a sound node is the node itself, a
value, or a sound key node with a live klong (`Good.reach_cases`).
-/
import Contract.Proof.Good
import Contract.Proof.BridgeReach
import Contract.Proof.BridgeWords
import Contract.BridgeFull
import SIS.Proof.CutCover

namespace Contract

open SIS.Check (BVal)

variable {s : Tree}

/-- A sound key node with a live klong has a value below it, which the walk
with enough fuel reaches. -/
theorem Good.val_below : ∀ (f : Nat) {x : NodeId} {lo : Nat} {hi : Option Nat} {n : KNode},
    Good s x lo hi → s.obj x = some (.key n) → live n.ks ≠ [] → n.level < f →
    ∃ v w, s.obj v = some (.val w) ∧ v ∈ reachAt s f x
  | 0, _, _, _, _, _, _, _, hf => absurd hf (Nat.not_lt_zero _)
  | f + 1, x, lo, hi, n, hg, hobj, hne, hf => by
    obtain ⟨⟨c, y⟩, hm⟩ : ∃ cy, cy ∈ live n.ks := List.exists_mem_of_ne_nil _ hne
    have hreach : ∀ z, z ∈ reachAt s f y → z ∈ reachAt s (f + 1) x := by
      intro z hz
      simp only [reachAt, hobj, List.mem_cons, List.mem_flatMap]
      exact Or.inr ⟨(c, y), hm, hz⟩
    by_cases hk : n.leaf = true → isLong c = true
    · obtain ⟨m, lo', hi', hm1, hm2, hm3, hgy⟩ := hg.child hobj hm hk
      obtain ⟨v, w, hv, hvr⟩ := Good.val_below f hgy hm1 hm3 (by omega)
      exact ⟨v, w, hv, hreach v hvr⟩
    · have hl : n.leaf = true := by
        by_contra hl
        exact hk (fun h => absurd h hl)
      have hs : isLong c = false := by
        cases hc : isLong c with
        | false => rfl
        | true => exact absurd (fun _ => hc) hk
      cases hg with
      | mk _ _ _ n' hobj' _ _ _ hval _ _ _ =>
        rw [hobj] at hobj'
        obtain rfl : n = n' := by injection hobj' with h1; injection h1
        obtain ⟨w, hw⟩ := hval hl c y hm hs
        exact ⟨y, w, hw, hreach y (mem_reachAt_self s f y)⟩

/-- What the walk reaches from a sound node: the node, a value, or a sound key
node with a live klong. -/
theorem Good.reach_cases : ∀ (f : Nat) {r : NodeId} {lo : Nat} {hi : Option Nat},
    Good s r lo hi → ∀ x, x ∈ reachAt s f r →
    x = r ∨ (∃ w, s.obj x = some (.val w)) ∨
      ∃ m lo' hi', s.obj x = some (.key m) ∧ live m.ks ≠ [] ∧ Good s x lo' hi'
  | 0, r, _, _, _, x, hx => by
    simp only [reachAt, List.mem_singleton] at hx
    exact Or.inl hx
  | f + 1, r, lo, hi, hg, x, hx => by
    simp only [reachAt, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Or.inl rfl
    · right
      cases hro : s.obj r with
      | none => rw [hro] at hx; simp at hx
      | some o =>
        cases o with
        | val w => rw [hro] at hx; simp at hx
        | key n =>
          rw [hro] at hx
          simp only [List.mem_flatMap] at hx
          obtain ⟨⟨c, y⟩, hm, hxy⟩ := hx
          by_cases hk : n.leaf = true → isLong c = true
          · obtain ⟨m, lo', hi', hm1, _, hm3, hgy⟩ := hg.child hro hm hk
            rcases Good.reach_cases f hgy x hxy with rfl | h2 | h2
            · exact Or.inr ⟨m, lo', hi', hm1, hm3, hgy⟩
            · exact Or.inl h2
            · exact Or.inr h2
          · have hl : n.leaf = true := by
              by_contra hl
              exact hk (fun h => absurd h hl)
            have hs : isLong c = false := by
              cases hc : isLong c with
              | false => rfl
              | true => exact absurd (fun _ => hc) hk
            cases hg with
            | mk _ _ _ n' hobj' _ _ _ hval _ _ _ =>
              rw [hro] at hobj'
              obtain rfl : n = n' := by injection hobj' with h1; injection h1
              obtain ⟨w, hw⟩ := hval hl c y hm hs
              have : x = y := by
                cases f with
                | zero => simpa [reachAt] using hxy
                | succ f =>
                  simp only [reachAt, hw, List.mem_cons] at hxy
                  rcases hxy with h | h
                  · exact h
                  · simp at h
              subst this
              exact Or.inl ⟨w, hw⟩

section Hist

variable {p : Params} {h : BHist} {top : Nat → Top}

/-- The invariants after every transaction of a history in the contract's
words, at the transaction's time. -/
theorem MeetsFull.inv_at (hm : MeetsFull p h top) (hM : 1 ≤ p.M) :
    ∀ j, j ≤ h.txs.length → invOk p ((h.tree j).at j) = true
  | 0, _ => (hm.start.start hM).1
  | j + 1, hj => by
    have hc := (hm.step j hj).1.1
    simp only [contractOk, Bool.and_eq_true] at hc
    exact hc.1

/-- The space root after transaction j is a sound key node, and, if the tree
holds a key, it has a live klong. -/
theorem MeetsFull.root_good (hm : MeetsFull p h top) (hM : 1 ≤ p.M) {j : Nat}
    (hj : j ≤ h.txs.length) {r : NodeId} (hr : (h.tree j).root = some r) :
    ∃ n, (h.tree j).obj r = some (.key n) ∧ Good (h.tree j) r 0 none ∧
      (contents (h.tree j) ≠ [] → live n.ks ≠ []) := by
  have hi := hm.meetsBridge.binv j hj
  have hinv := hm.inv_at hM j hj
  rw [hi.timely.at_eq] at hinv
  unfold invOk at hinv
  simp only [hr] at hinv
  cases ho : (h.tree j).obj r with
  | none => simp [ho] at hinv
  | some o =>
    simp only [ho] at hinv
    cases o with
    | val w => simp at hinv
    | key n =>
      simp only [Bool.and_eq_true] at hinv
      refine ⟨n, rfl, walk_good _ _ _ _ hinv.2, ?_⟩
      intro hne hl
      apply hne
      unfold contents
      rw [hr]
      simp [Tree.fuel, ho, listAt, hl]

end Hist

/-! ## The versions of the model's run, for any algorithm -/

section Run

variable {V T : Type} [DecidableEq V] (sp : SIS.Spec V T) (al : SIS.Algo V T) (ts : List T)

theorem st_len' : ∀ j, j ≤ ts.length → (SIS.st sp al ts j).S.length = j + 1
  | 0, _ => by rw [SIS.st_zero]; rfl
  | j + 1, hj => by
    rw [SIS.st_S_succ sp al ts (by omega), List.length_append, st_len' j (by omega)]
    rfl

/-- Every version of the model's run is in the record of its number, whatever
the algorithm's choices. -/
theorem st_recNo : ∀ j, j ≤ ts.length → ∀ (r : Nat) (R : SIS.Record V T),
    (SIS.st sp al ts j).S[r]? = some R → ∀ v ∈ R.vers, v.recNo = r
  | 0, _, r, R, hR, v, hv => by
    rw [SIS.st_zero, SIS.init_eq] at hR
    cases r with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hR
      subst hR
      obtain ⟨_, _, _, _, h, _⟩ := SIS.built_mem (SIS.initVers_built sp) hv
      exact h
    | succ r => simp at hR
  | j + 1, hj, r, R, hR, v, hv => by
    have hlen := st_len' sp al ts j (by omega)
    rw [SIS.st_S_succ sp al ts (by omega)] at hR
    rcases Nat.lt_or_ge r (SIS.st sp al ts j).S.length with hr | hr
    · rw [List.getElem?_append_left hr] at hR
      exact st_recNo j (by omega) r R hR v hv
    · rw [List.getElem?_append_right hr] at hR
      have hr' : r = j + 1 := by
        rcases Nat.lt_or_ge (r - (SIS.st sp al ts j).S.length) 1 with h1 | h1
        · omega
        · rw [List.getElem?_eq_none (by simpa using h1)] at hR; cases hR
      subst hr'
      rw [hlen] at hR
      simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hR
      subst hR
      obtain ⟨_, _, _, _, h, _⟩ :=
        SIS.built_mem (SIS.step_vs_built sp al (SIS.st sp al ts j) ts[j] hlen) hv
      exact h

end Run

/-- A node of the model's structure after j stays, with its kind, in every
later structure. -/
theorem BHist.P_isData (h : BHist) {x : NodeId} {j : Nat} {n : SIS.Node BVal}
    (hx : (h.P j).get? x = some n) :
    ∀ j', j ≤ j' → j' ≤ h.txs.length → ∃ n', (h.P j').get? x = some n' ∧ n'.isData = n.isData
  | 0, hj, _ => by
    have : j = 0 := by omega
    subst this
    exact ⟨n, hx, rfl⟩
  | j' + 1, hj, hj' => by
    rcases Nat.lt_or_ge j (j' + 1) with hlt | hge
    · obtain ⟨n', h1, h2⟩ := BHist.P_isData h hx j' (by omega) (by omega)
      rw [h.P_succ (by omega), SIS.get?_apply_of_get? h1]
      exact ⟨_, rfl, h2⟩
    · have : j = j' + 1 := by omega
      subst this
      exact ⟨n, hx, rfl⟩

section Data

variable {p : Params} {h : BHist}

/-- A node that a change makes, as the model's structure gets it: one of the
change's new nodes, with its kind. -/
theorem newNodeOf_some {c : SIS.Changes BVal} {x : NodeId} {n : SIS.Node BVal}
    (h : SIS.newNodeOf c x = some n) : ∃ nn ∈ c.new, nn.id = x ∧ n.isData = nn.isData := by
  unfold SIS.newNodeOf at h
  obtain ⟨l₁, l₂, hl, -⟩ := List.lookup_eq_some_iff.mp h
  have hmem : (x, n) ∈ c.new.map (fun n => (n.id,
      ({ level := n.level, isData := n.isData, hist := [] } : SIS.Node BVal))) := by
    rw [hl]; simp
  obtain ⟨nn, hnn, heq⟩ := List.mem_map.mp hmem
  injection heq with h1 h2
  exact ⟨nn, hnn, h1, by rw [← h2]⟩

/-- A node that the start's change makes is an index node. -/
theorem StartB.p0_index (hs : StartB h) {x : NodeId} {n : SIS.Node BVal}
    (hx : (h.P 0).get? x = some n) : n.isData = false := by
  obtain ⟨r, z, lr, lz, l0, -, -, -, -, -, -, -, hnew, -⟩ := hs
  change (SIS.Struct.apply [] 0 h.c0).get? x = some n at hx
  rw [SIS.get?_apply] at hx
  simp only [SIS.Struct.get?, List.lookup_nil, Option.none_or] at hx
  cases hn : SIS.newNodeOf h.c0 x with
  | none => rw [hn] at hx; cases hx
  | some n0 =>
    rw [hn] at hx
    injection hx with hx
    subst hx
    obtain ⟨nn, hnn, -, hd⟩ := newNodeOf_some hn
    rw [hnew] at hnn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hnn
    rcases hnn with rfl | rfl | rfl <;> exact hd

/-- A data node that transaction j + 1 made has a version in record j + 1 of
the model's run, so its latest version after any later transaction is in a
record at or after j + 1, whatever the algorithm's choices. -/
theorem MeetsBridge.data_version (hm : MeetsBridge p h) (al : SIS.Algo BVal Nat) {j e : Nat}
    (hj : j < h.txs.length) (hje : j + 1 ≤ e) (he : e ≤ h.txs.length) {d : NodeId}
    (hd : d ∈ h.txs[j].c.new.map (·.id)) {m : SIS.Node BVal} (hdm : (h.P e).get? d = some m)
    (hmd : m.isData = true) :
    ∃ u, (SIS.run h.spec al (h.ts.take e)).S.lv d = some u ∧ j + 1 ≤ u.recNo := by
  have hstep := (hm.facts j hj).stepOK (hm.binv j (by omega)) (hm.binv (j + 1) hj)
  obtain ⟨nn, hnn, hid⟩ := List.mem_map.mp hd
  have hfresh : (h.P j).get? d = none := by rw [← hid]; exact hstep.fresh nn hnn
  -- The node made, in the structure after j + 1, and its kind.
  obtain ⟨n1, hn1, nn', hnn', hid', hd1⟩ : ∃ n1, (h.P (j + 1)).get? d = some n1 ∧
      ∃ nn' ∈ h.txs[j].c.new, nn'.id = d ∧ n1.isData = nn'.isData := by
    rw [h.P_succ hj, SIS.get?_apply, hfresh, Option.none_or]
    cases hnew : SIS.newNodeOf h.txs[j].c d with
    | none =>
      exfalso
      unfold SIS.newNodeOf at hnew
      have : (SIS.Struct.get? (h.txs[j].c.new.map (fun n => (n.id,
          ({ level := n.level, isData := n.isData, hist := [] } : SIS.Node BVal)))) d).isSome := by
        simp only [SIS.Struct.get?, List.lookup_isSome_iff, List.mem_map]
        exact ⟨_, ⟨nn, hnn, rfl⟩, by simp [hid]⟩
      rw [hnew] at this
      cases this
    | some n0 =>
      unfold SIS.newNodeOf at hnew
      obtain ⟨l₁, l₂, hl, -⟩ := List.lookup_eq_some_iff.mp hnew
      have hmem : (d, n0) ∈ h.txs[j].c.new.map (fun n => (n.id,
          ({ level := n.level, isData := n.isData, hist := [] } : SIS.Node BVal))) := by
        rw [hl]; simp
      obtain ⟨nn', hnn', heq⟩ := List.mem_map.mp hmem
      injection heq with h1 h2
      exact ⟨_, rfl, nn', hnn', h1, by rw [← h2]⟩
  obtain ⟨n2, hn2, hd2⟩ := h.P_isData hn1 e hje he
  rw [hdm, Option.some.injEq] at hn2
  subst hn2
  have hdat : nn'.isData = true := by rw [← hd1, ← hd2]; exact hmd
  -- The model's step j + 1 writes a version of d.
  have hjl : j < h.ts.length := by simp [BHist.ts]; omega
  have hlen : (SIS.st h.spec al h.ts j).S.length = j + 1 :=
    st_len' h.spec al h.ts j (by simp [BHist.ts]; omega)
  have hc : (SIS.parts h.spec al (SIS.st h.spec al h.ts j) h.ts[j]).c = h.txs[j].c := by
    rw [SIS.parts_c, hlen, h.ts_get hj, h.exec_eq hj]
  have hP : (SIS.parts h.spec al (SIS.st h.spec al h.ts j) h.ts[j]).P = h.P (j + 1) := by
    rw [SIS.parts_P' h.spec al _ _ hlen, hc, h.P_succ hj]
    congr 1
    exact run_P h al j (by omega)
  have hw0 : d ∈ (SIS.parts h.spec al (SIS.st h.spec al h.ts j) h.ts[j]).vs0.map (·.node) := by
    rw [SIS.parts_vs0, SIS.writeAll_nodes]
    simp only [List.map_nil, List.nil_append, List.mem_filter, List.mem_map, hc, hP, hn1,
      Option.isSome_some, and_true]
    exact ⟨nn', ⟨hnn', hdat⟩, hid'⟩
  obtain ⟨w, hw, hwd⟩ := List.mem_map.mp hw0
  have hwv : w ∈ (SIS.parts h.spec al (SIS.st h.spec al h.ts j) h.ts[j]).R.vers :=
    (SIS.step_vs0_prefix h.spec al _ _).subset hw
  have hv1 : ∃ w', (SIS.st h.spec al h.ts (j + 1)).S.versionAt (j + 1) d = some w' := by
    rw [SIS.st_S_succ h.spec al h.ts hjl, ← hlen, SIS.versionAt_snoc_self]
    cases hf : (SIS.parts h.spec al (SIS.st h.spec al h.ts j) h.ts[j]).R.vers.find?
        (fun v => v.node == d) with
    | some w' => exact ⟨w', rfl⟩
    | none =>
      exfalso
      have := List.find?_eq_none.mp hf w hwv
      simp [hwd] at this
  obtain ⟨w', hw'⟩ := hv1
  have hve := SIS.versionAt_prefix (SIS.st_S_prefix h.spec al h.ts hje (by simp [BHist.ts]; omega))
    hw'
  obtain ⟨r', u, hu, hlv, hle⟩ := SIS.lv_recNo_ge hve
  obtain ⟨R, hR, huR, -⟩ := SIS.versionAt_spec hu
  have hrec := st_recNo h.spec al h.ts e (by simp [BHist.ts]; omega) r' R hR u huR
  exact ⟨u, hlv, by omega⟩

end Data

end Contract
