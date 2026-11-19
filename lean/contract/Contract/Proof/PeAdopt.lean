/-
bergdb 030-21, part 2: A6' and A-COPY for PE (BridgeTop.lean: `adoptOk`,
`copyOk`), with its change in the model's words (`peChange`).

* `InvA`, what the tree keeps for A6': every key klong, live or dead, of a key
  node reached names a live child of it, a value, or a node not reached. It
  is A6' without its fourth case ("below x"), which PE does not need: a klong
  that dies names a child dropped from the node's list, and a child dropped is
  replaced by a value or no more reached (`invA_start`, `adoptOk_of_invA`).
* The tree's two walks: a node reached but the root has a parent reached
  (`reach_parent`), at most one (`reach_one_parent`, from TREE and A4), and
  the root is no node's child (`reach_root_not_kid`).
* `Prov`, PE's provenance of the old nodes its written key nodes name: every
  old node that a written key node names by a live klong after the
  transaction was, before it, a live child of that node or of an old node
  reached that the transaction does not write.
* `pe_adopt_copy_of_prov`: from `Prov` and the facts that `pe_step` and
  `pe_bridge` give, A-COPY (`copyOk`), A6' after the transaction
  (`adoptOk`) and `InvA` after it. The argument: an old child y of an
  appended base q that is no longer its child is no more reached (`kept_or_gone`:
  a parent of y after it would be q by TREE before, against `Prov`); so a
  dead klong keeps `InvA`; an old node that a new klong names is a child,
  before, of the node itself (given an entry) or of a node not written, which
  TREE after puts out of the walk; the new space root likewise. Premises:
  `Cfg.Ok`, `Inv` at i - 1, `InvB`, `InvA`, the operations' keys distinct (as
  `pe_bridge`: every node written is reached), and `Prov`.
* `pe_adopt_run`, `pe_adopt_hist`: every transaction of a run of PE and of
  its history from the empty tree (`peHist`) meets A-COPY with the history's
  tops, every tree of it A6' at its time (`MeetsFull.adopt`) and `InvA`, for
  transactions of distinct keys, given each transaction's `Prov`.
* `pe_touch_hist`: the touch rules (`touchOk`), PE's transactions touching
  nothing.
* `provB`, `Prov` computed (`provB_sound`); Contract/PeAdoptExample.lean
  shows `pe_adopt_hist` not vacuous (a history of three transactions, its
  `Prov` computed by the kernel).

`Prov` for PE's transaction is proved in PeProv.lean (`pe_prov`,
`pe_prov_hist`; the theorems without the premise: `pe_adopt_copy`,
`pe_adopt_hist_full`). Computed, it holds at all 221,142 transactions of
026-21's 288 traces, with A-COPY, A6' and `InvA` (bergdb 030-21,
runs/adopt.txt).
-/
import Contract.Proof.PeBridge
import Contract.Proof.BridgeTree
import Contract.Proof.BridgeMap
import Contract.Proof.BridgeWords

namespace Contract.PE

open PeProof PeProof.Abs PeProof.Keys
open SIS (Changes NewNode)
open SIS.Check (BVal)

variable {cf : Cfg}

/-! ## What PE keeps for A6' -/

/-- What the tree keeps for A6' (BridgeTop.lean, `adoptOk`), beyond `Inv` and
`InvB`. -/
structure InvA (cf : Cfg) (s : Tree) : Prop where
  /-- A6' without "below": every key klong, live or dead, of a key node
  reached names a live child of the node, a value, or a node not reached. -/
  adopt : ∀ x ∈ reach s, ∀ n, s.obj x = some (.key n) → ∀ c y, Klong.key c y ∈ n.ks →
    y ∈ (live n.ks).map (·.2) ∨ (∃ v, s.obj y = some (.val v)) ∨ y ∉ reach s

/-- **The start**: PE's empty tree meets `InvA` (its one key node has no key
klong). -/
theorem invA_start : InvA cf (startTree cf) := by
  refine ⟨fun x _ n hx c y hk => ?_⟩
  by_cases h1 : x = 1
  · subst h1
    rw [startTree_obj1] at hx
    cases hx
    simp at hk
  · rw [startTree_obj_ne h1] at hx; cases hx

/-- `InvA` gives A6'. -/
theorem adoptOk_of_invA {s : Tree} (h : InvA cf s) : adoptOk s = true := by
  unfold adoptOk
  simp only [List.all_eq_true]
  intro x hx
  split
  · rename_i n hn
    simp only [List.all_eq_true]
    intro k hk
    cases k with
    | key c y =>
      simp only [Bool.or_eq_true, List.contains_iff_mem, Bool.not_eq_true']
      rcases h.adopt x hx n hn c y hk with h1 | ⟨v, h1⟩ | h1
      · exact Or.inl (Or.inl (Or.inl h1))
      · left; left; right
        rw [h1]
      · left; right
        simpa using h1
    | time _ => rfl
    | del _ => rfl
  · rfl

/-! ## The walk of a tree -/

/-- A node the walk reaches but its start has a parent in the walk, whose live
klong names it. -/
theorem reachAt_parent {s : Tree} : ∀ (f : Nat) (x0 y : NodeId), y ∈ reachAt s f x0 → y ≠ x0 →
    ∃ x1 ∈ reachAt s f x0, ∃ n c, s.obj x1 = some (.key n) ∧ (c, y) ∈ live n.ks
  | 0, x0, y, hy, hne => by
    simp only [reachAt, List.mem_singleton] at hy
    exact absurd hy hne
  | f + 1, x0, y, hy, hne => by
    simp only [reachAt, List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact absurd rfl hne
    · cases ho : s.obj x0 with
      | none => rw [ho] at hy; simp at hy
      | some o =>
        cases o with
        | val v => rw [ho] at hy; simp at hy
        | key n =>
          rw [ho] at hy
          obtain ⟨⟨c, z⟩, hz, hyz⟩ := List.mem_flatMap.mp hy
          by_cases hyz' : y = z
          · subst hyz'
            exact ⟨x0, mem_reachAt_self s (f + 1) x0, n, c, ho, hz⟩
          · obtain ⟨x1, hx1, n1, c1, h1, h2⟩ := reachAt_parent f z y hyz hyz'
            refine ⟨x1, ?_, n1, c1, h1, h2⟩
            simp only [reachAt, List.mem_cons, ho]
            exact Or.inr (List.mem_flatMap.mpr ⟨(c, z), hz, hx1⟩)

/-- A key node reached: the space root is a key node, and the walk is from it
with its level and one more as fuel. -/
theorem reach_key_root {s : Tree} {x : NodeId} {n : KNode} (hx : x ∈ reach s)
    (hn : s.obj x = some (.key n)) :
    ∃ r nr, s.root = some r ∧ s.obj r = some (.key nr) ∧ reach s = reachAt s (nr.level + 1) r := by
  unfold reach at hx ⊢
  cases hroot : s.root with
  | none => rw [hroot] at hx; simp at hx
  | some r =>
    rw [hroot] at hx
    simp only at hx ⊢
    cases hr : s.obj r with
    | none =>
      have h0 : s.fuel r = 0 := by simp [Tree.fuel, hr]
      rw [h0] at hx
      simp only [reachAt, List.mem_singleton] at hx
      subst hx
      rw [hr] at hn; cases hn
    | some o =>
      cases o with
      | val v =>
        have h0 : s.fuel r = 0 := by simp [Tree.fuel, hr]
        rw [h0] at hx
        simp only [reachAt, List.mem_singleton] at hx
        subst hx
        rw [hr] at hn; cases hn
      | key nr =>
        exact ⟨r, nr, rfl, hr, by simp [Tree.fuel, hr]⟩

/-- TREE: two key nodes reached with one live child are one node. -/
theorem reach_one_parent {s : Tree} (hl : LevOK s) (hnd : (reach s).Nodup)
    {x1 x2 : NodeId} {n1 n2 : KNode} {c1 c2 : Nat} {y : NodeId}
    (hx1 : x1 ∈ reach s) (hx2 : x2 ∈ reach s) (hn1 : s.obj x1 = some (.key n1))
    (hn2 : s.obj x2 = some (.key n2)) (hy1 : (c1, y) ∈ live n1.ks) (hy2 : (c2, y) ∈ live n2.ks) :
    x1 = x2 := by
  obtain ⟨r, nr, _, hr, heq⟩ := reach_key_root hx1 hn1
  rw [heq] at hx1 hx2 hnd
  exact reachAt_one_parent hl (nr.level + 1) r (.key nr) hr (by simp [lvl]) hnd x1 x2 n1 n2 c1 c2 y
    hx1 hx2 hn1 hn2 hy1 hy2

/-- A live child of a key node reached is reached. -/
theorem reach_kid {s : Tree} (hl : LevOK s) {x : NodeId} {n : KNode} {c : Nat} {y : NodeId}
    (hx : x ∈ reach s) (hn : s.obj x = some (.key n)) (hy : (c, y) ∈ live n.ks) : y ∈ reach s := by
  obtain ⟨r, nr, _, hr, heq⟩ := reach_key_root hx hn
  rw [heq] at hx ⊢
  exact reachAt_closed hl (nr.level + 1) r (.key nr) hr (by simp [lvl]) x n c y hx hn hy

/-- A node reached but the space root has a parent reached. -/
theorem reach_parent {s : Tree} {r y : NodeId} (hroot : s.root = some r) (hy : y ∈ reach s)
    (hne : y ≠ r) : ∃ x ∈ reach s, ∃ n c, s.obj x = some (.key n) ∧ (c, y) ∈ live n.ks := by
  unfold reach at hy ⊢
  rw [hroot] at hy ⊢
  exact reachAt_parent _ r y hy hne

/-- The space root is no live child of a key node reached. -/
theorem reach_root_not_kid {s : Tree} (hl : LevOK s) {r x : NodeId} {n : KNode} {c : Nat}
    (hroot : s.root = some r) (hx : x ∈ reach s) (hn : s.obj x = some (.key n))
    (hc : (c, r) ∈ live n.ks) : False := by
  obtain ⟨r1, nr, hr1, hr, heq⟩ := reach_key_root hx hn
  rw [hroot] at hr1
  cases hr1
  rw [heq] at hx
  obtain ⟨o', ho', hcase⟩ := reachAt_lvl hl (nr.level + 1) r (.key nr) hr x hx
  obtain ⟨orr, horr, hlt⟩ := hl x n hn c r (live_mem_key hc)
  rw [hn] at ho'
  cases ho'
  rw [hr] at horr
  cases horr
  rcases hcase with h1 | h1
  · subst h1
    rw [hr] at hn
    cases hn
    simp [lvl] at hlt
  · simp only [lvl] at h1 hlt
    omega

/-! ## PE's provenance -/

/-- **PE's provenance**: every old node (a node of s) that a key node written
(in D) names by a live klong in the tree after T was, in s, a live child of
that node or of an old key node reached that the transaction does not write
(a base replaced, a node opened by a join, a collapsed root). -/
def Prov (s T : Tree) (D : List NodeId) : Prop :=
  ∀ p ∈ D, ∀ m, T.obj p = some (.key m) → ∀ c y, (c, y) ∈ live m.ks → s.obj y ≠ none →
    (∃ n c', s.obj p = some (.key n) ∧ (c', y) ∈ live n.ks) ∨
    ∃ q ∈ reach s, q ∉ D ∧ ∃ n c', s.obj q = some (.key n) ∧ (c', y) ∈ live n.ks

/-- Node y is a live child of the key node q of s. -/
def kidOf (s : Tree) (q y : NodeId) : Bool :=
  match s.obj q with
  | some (.key n) => (live n.ks).any (fun cy => cy.2 == y)
  | _ => false

/-- `Prov`, computed. -/
def provB (s T : Tree) (D : List NodeId) : Bool :=
  D.all (fun p => match T.obj p with
    | some (.key m) => (live m.ks).all (fun cy => (s.obj cy.2).isNone || kidOf s p cy.2 ||
        (reach s).any (fun q => !D.contains q && kidOf s q cy.2))
    | _ => true)

theorem kidOf_iff {s : Tree} {q y : NodeId} :
    kidOf s q y = true ↔ ∃ n c, s.obj q = some (.key n) ∧ (c, y) ∈ live n.ks := by
  unfold kidOf
  constructor
  · intro h
    split at h
    · rename_i n hn
      obtain ⟨⟨c, y'⟩, hm, he⟩ := List.any_eq_true.mp h
      simp only [beq_iff_eq] at he
      subst he
      exact ⟨n, c, hn, hm⟩
    · cases h
  · rintro ⟨n, c, hn, hm⟩
    rw [hn]
    exact List.any_eq_true.mpr ⟨(c, y), hm, by simp⟩

/-- The computed `Prov` gives `Prov`. -/
theorem provB_sound {s T : Tree} {D : List NodeId} (h : provB s T D = true) : Prov s T D := by
  intro p hp m hTp c y hy hsy
  have h1 := List.all_eq_true.mp h p hp
  rw [hTp] at h1
  have h2 := List.all_eq_true.mp h1 (c, y) hy
  simp only [Bool.or_eq_true, Option.isNone_iff_eq_none, List.any_eq_true, Bool.and_eq_true,
    Bool.not_eq_true'] at h2
  rcases h2 with (h2 | h2) | ⟨q, hq, hqD, hk⟩
  · exact absurd h2 hsy
  · exact Or.inl (kidOf_iff.mp h2)
  · refine Or.inr ⟨q, hq, fun hm => ?_, kidOf_iff.mp hk⟩
    have : D.contains q = true := List.contains_iff_mem.mpr hm
    rw [hqD] at this
    cases this

/-- The facts of a transaction from s to T with the writes W, at time i, that
A6' and A-COPY follow from, with `Prov`: the space roots r0 and r'; the
writes, each of a form of `WForm`, the other nodes kept; an old node written
was reached; every node written is reached; an old node reached after was
reached before; TREE and A4 before and after. -/
structure TxF (i : Time) (s T : Tree) (W : List (NodeId × Obj)) (r0 r' : NodeId) : Prop where
  root0 : s.root = some r0
  root1 : T.root = some r'
  key1 : ∃ m, T.obj r' = some (.key m)
  ws : ∀ p ∈ W, T.obj p.1 = some p.2
  keep : ∀ x, x ∉ W.map (·.1) → T.obj x = s.obj x
  form : ∀ p ∈ W, WForm i s p
  oldW : ∀ x ∈ W.map (·.1), s.obj x ≠ none → x ∈ reach s
  reachW : ∀ x ∈ W.map (·.1), x ∈ reach T
  sub : ∀ x ∈ reach T, s.obj x ≠ none → x ∈ reach s
  treeS : (reach s).Nodup
  treeT : (reach T).Nodup
  levS : LevOK s
  levT : LevOK T

section Abstract

variable {i : Time} {s T : Tree} {W : List (NodeId × Obj)} {r0 r' : NodeId}

theorem mem_ws_of {x : NodeId} (hx : x ∈ W.map (·.1)) : ∃ ob, (x, ob) ∈ W := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  exact ⟨p.2, hp⟩

/-- An old node written is a key node with emit's klongs appended. -/
theorem TxF.old_key (hF : TxF i s T W r0 r') {x : NodeId} (hx : x ∈ W.map (·.1))
    (hsx : s.obj x ≠ none) : ∃ n F, s.obj x = some (.key n) ∧
      T.obj x = some (.key { n with ks := n.ks ++ emitKs i n.ks F }) ∧
      live (n.ks ++ emitKs i n.ks F) = F := by
  obtain ⟨ob, hm⟩ := mem_ws_of hx
  have hT := hF.ws _ hm
  rcases hF.form _ hm with ⟨h0, _⟩ | ⟨n, F, h1, h2, h3, _⟩
  · exact absurd h0 hsx
  · simp only at h1 h2 hT
    rw [h2] at hT
    exact ⟨n, F, h1, hT, h3⟩

/-- An old node keeps its level. -/
theorem TxF.lvl_keep (hF : TxF i s T W r0 r') {x : NodeId} {o : Obj} (hx : s.obj x = some o) :
    ∃ o', T.obj x = some o' ∧ lvl o' = lvl o := by
  by_cases hxW : x ∈ W.map (·.1)
  · obtain ⟨n, F, h1, h2, _⟩ := hF.old_key hxW (by rw [hx]; simp)
    rw [hx] at h1
    cases h1
    exact ⟨_, h2, rfl⟩
  · exact ⟨o, by rw [hF.keep x hxW, hx], rfl⟩

/-- An old value is kept. -/
theorem TxF.val_keep (hF : TxF i s T W r0 r') {y : NodeId} {v : Nat}
    (hy : s.obj y = some (.val v)) : T.obj y = some (.val v) := by
  by_cases hyW : y ∈ W.map (·.1)
  · obtain ⟨n, F, h1, _, _⟩ := hF.old_key hyW (by rw [hy]; simp)
    rw [hy] at h1
    cases h1
  · rw [hF.keep y hyW, hy]

/-- A node of s reached in T was reached in s. -/
theorem TxF.sub_obj (hF : TxF i s T W r0 r') {x : NodeId} {o : Obj} (hx : x ∈ reach T)
    (ho : s.obj x = some o) : x ∈ reach s :=
  hF.sub x hx (by rw [ho]; simp)

/-- **A child kept or gone**: an old live child y of a key node q written and
reached after is a live child of q after, or not reached after. Else y has a
parent reached after (y is not the new space root: levels), not q; written by
`Prov` it names y as a child before of itself or of a node not written, which
is q by TREE before; not written, it is y's parent before, q by TREE before. -/
theorem TxF.kept_or_gone (hF : TxF i s T W r0 r') (hP : Prov s T (W.map (·.1))) {q : NodeId}
    {n0 m : KNode} (hq : q ∈ W.map (·.1)) (hsq : s.obj q = some (.key n0)) (hqT : q ∈ reach T)
    (hTq : T.obj q = some (.key m)) {c : Nat} {y : NodeId} (hy : (c, y) ∈ live n0.ks) :
    y ∈ (live m.ks).map (·.2) ∨ y ∉ reach T := by
  by_cases hyT : y ∈ reach T
  · left
    have hqs : q ∈ reach s := hF.oldW q hq (by rw [hsq]; simp)
    obtain ⟨oy, hoy, hlty⟩ := hF.levS q n0 hsq c y (live_mem_key hy)
    by_cases hyr : y = r'
    · exfalso
      subst hyr
      obtain ⟨oy', hoy', hl'⟩ := hF.lvl_keep hoy
      obtain ⟨rq, nrq, hrq, hrqo, heq⟩ := reach_key_root hqT hTq
      rw [hF.root1] at hrq
      cases hrq
      rw [hoy'] at hrqo
      cases hrqo
      rw [heq] at hqT
      obtain ⟨o2, ho2, hcase⟩ := reachAt_lvl hF.levT (nrq.level + 1) y (.key nrq) hoy' q hqT
      rw [hTq] at ho2
      cases ho2
      obtain ⟨oq', hoq', hlq⟩ := hF.lvl_keep hsq
      rw [hTq] at hoq'
      cases hoq'
      simp only [lvl] at hl' hlq hlty
      rcases hcase with h1 | h1
      · subst h1
        rw [hsq] at hoy
        cases hoy
        simp at hlty
      · simp only [lvl] at h1
        omega
    · obtain ⟨p, hpT, mp, cp, hTp, hyp⟩ := reach_parent hF.root1 hyT hyr
      by_cases hpW : p ∈ W.map (·.1)
      · have hsy : s.obj y ≠ none := by rw [hoy]; simp
        rcases hP p hpW mp hTp cp y hyp hsy with ⟨n, c', hsp, hyp'⟩ | ⟨q', hq's, hq'W, n', c', hsq', hyq'⟩
        · have hps : p ∈ reach s := hF.oldW p hpW (by rw [hsp]; simp)
          have := reach_one_parent hF.levS hF.treeS hps hqs hsp hsq hyp' hy
          subst this
          rw [hTq] at hTp
          cases hTp
          exact List.mem_map.mpr ⟨_, hyp, rfl⟩
        · have := reach_one_parent hF.levS hF.treeS hq's hqs hsq' hsq hyq' hy
          subst this
          exact absurd hq hq'W
      · have hsp : s.obj p = some (.key mp) := by rw [← hF.keep p hpW]; exact hTp
        have hps : p ∈ reach s := hF.sub_obj hpT hsp
        have := reach_one_parent hF.levS hF.treeS hps hqs hsp hsq hyp hy
        subst this
        exact absurd hq hpW
  · exact Or.inr hyT

/-- **The new space root, if old and not the old one, is a child before of a
node not reached after.** Its parent before is not reached after: not
written, it would name it after (the root is no child); written, it keeps it
as a child (`kept_or_gone`) or it is not reached. -/
theorem TxF.root_named (hF : TxF i s T W r0 r') (hP : Prov s T (W.map (·.1)))
    (hsr : s.obj r' ≠ none) (hne : r' ≠ r0) :
    ∃ q ∈ reach s, q ∉ reach T ∧ ∃ n c, s.obj q = some (.key n) ∧ (c, r') ∈ live n.ks := by
  have hrT : r' ∈ reach T := by
    unfold reach
    rw [hF.root1]
    exact mem_reachAt_self _ _ _
  have hrs : r' ∈ reach s := hF.sub r' hrT hsr
  obtain ⟨q, hqs, n, c, hsq, hc⟩ := reach_parent hF.root0 hrs hne
  refine ⟨q, hqs, fun hqT => ?_, n, c, hsq, hc⟩
  by_cases hqW : q ∈ W.map (·.1)
  · obtain ⟨n', F, h1, h2, _⟩ := hF.old_key hqW (by rw [hsq]; simp)
    rw [hsq] at h1
    cases h1
    rcases hF.kept_or_gone hP hqW hsq hqT h2 hc with h | h
    · obtain ⟨⟨c', y'⟩, hm, hy'⟩ := List.mem_map.mp h
      simp only at hy'
      subst hy'
      exact reach_root_not_kid hF.levT hF.root1 hqT h2 hm
    · exact h hrT
  · have hTq : T.obj q = some (.key n) := by rw [hF.keep q hqW]; exact hsq
    exact reach_root_not_kid hF.levT hF.root1 hqT hTq hc

/-- **A node named by a live klong of a node written** that is an old node was
a live child before of that node, or of a node not reached after. -/
theorem TxF.kid_named (hF : TxF i s T W r0 r') (hP : Prov s T (W.map (·.1))) {p : NodeId}
    {m : KNode} (hp : p ∈ W.map (·.1)) (hTp : T.obj p = some (.key m)) {c : Nat} {y : NodeId}
    (hy : (c, y) ∈ live m.ks) (hsy : s.obj y ≠ none) :
    (∃ n c', s.obj p = some (.key n) ∧ (c', y) ∈ live n.ks) ∨
      ∃ q ∈ reach s, q ∉ reach T ∧ ∃ n c', s.obj q = some (.key n) ∧ (c', y) ∈ live n.ks := by
  rcases hP p hp m hTp c y hy hsy with h | ⟨q, hqs, hqW, n, c', hsq, hyq⟩
  · exact Or.inl h
  · refine Or.inr ⟨q, hqs, fun hqT => ?_, n, c', hsq, hyq⟩
    have hTq : T.obj q = some (.key n) := by rw [hF.keep q hqW]; exact hsq
    have := reach_one_parent hF.levT hF.treeT (hF.reachW p hp) hqT hTp hTq hy hyq
    subst this
    exact hqW hp

/-- **`InvA` is kept.** A key node reached after is written new (its klongs
are its live list), written as an appended base (its new klongs live; an old
klong as `InvA` before had it, a child before kept or gone), or not written
(as before; a node not reached before is not reached after). -/
theorem TxF.invA (hF : TxF i s T W r0 r') (hP : Prov s T (W.map (·.1))) (hA : InvA cf s) :
    InvA cf T := by
  refine ⟨fun x hxT m hTx c y hk => ?_⟩
  -- a node of s not reached before is not reached after
  have gone : ∀ z, s.obj z ≠ none → z ∉ reach s → z ∉ reach T :=
    fun z hz hzs hzT => hzs (hF.sub z hzT hz)
  have old : ∀ (n : KNode), Klong.key c y ∈ n.ks → s.obj x = some (.key n) → x ∈ reach s →
      y ∈ (live n.ks).map (·.2) ∨ (∃ v, T.obj y = some (.val v)) ∨ y ∉ reach T := by
    intro n hkn hsx hxs
    obtain ⟨oy, hoy, _⟩ := hF.levS x n hsx c y hkn
    rcases hA.adopt x hxs n hsx c y hkn with h | ⟨v, h⟩ | h
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨v, hF.val_keep h⟩)
    · exact Or.inr (Or.inr (gone y (by rw [hoy]; simp) h))
  by_cases hxW : x ∈ W.map (·.1)
  · obtain ⟨ob, hm⟩ := mem_ws_of hxW
    have hT := hF.ws _ hm
    rw [hTx] at hT
    rcases hF.form _ hm with ⟨_, ⟨v, hv⟩ | ⟨l, b, F, hk', hlive⟩⟩ | ⟨n, F, hsx, hob, hlive, _⟩
    · simp only at hv; rw [hv] at hT; cases hT
    · simp only at hk'
      rw [hk'] at hT
      cases hT
      left
      rw [hlive]
      simp only [newKs, keysOf, List.mem_cons, List.mem_map] at hk
      rcases hk with h | ⟨e, he, h⟩
      · cases h
      · injection h with h1 h2
        subst h1 h2
        exact List.mem_map.mpr ⟨_, he, rfl⟩
    · simp only at hsx hob hlive
      rw [hob] at hT
      cases hT
      simp only at hk ⊢
      rw [hlive]
      rcases List.mem_append.mp hk with hk | hk
      · have hxs : x ∈ reach s := hF.oldW x hxW (by rw [hsx]; simp)
        rcases old n hk hsx hxs with h | h | h
        · obtain ⟨⟨c', y'⟩, hc', hy'⟩ := List.mem_map.mp h
          simp only at hy'
          subst hy'
          rcases hF.kept_or_gone hP hxW hsx hxT (hob ▸ hF.ws _ hm) hc' with h1 | h1
          · left; rwa [hlive] at h1
          · exact Or.inr (Or.inr h1)
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · left
        exact List.mem_map.mpr ⟨_, emitKs_ptrs hk, rfl⟩
  · have hsx : s.obj x = some (.key m) := by rw [← hF.keep x hxW]; exact hTx
    exact old m hk hsx (hF.sub_obj hxT hsx)

end Abstract

/-! ## PE's transaction -/

/-- **The facts of PE's transaction** (`TxF`), from a state PE keeps at
i - 1 with `InvB`, for operations of distinct keys: the writes `o.ws`, the
tree at its times, and the new top node made exactly when the space root
changes. -/
theorem pe_txF (hcf : cf.Ok) {i : Time} (hi : 1 ≤ i) {s : Tree} {tp : Top} {next : NodeId}
    {ops : List Op} {o : Out} (hI : Inv cf (i - 1) s tp next) (hB : InvB cf s)
    (hkeys : (ops.map Op.key).Nodup) (hw : peTx cf i s tp next ops = some o) :
    ∃ r0 r', TxF i s (o.tree s) o.ws r0 r' ∧ (o.tree s).at i = o.tree s ∧ s.at (i - 1) = s ∧
      ((r' = r0 ∧ newTopOf tp o = none) ∨
        (r' ≠ r0 ∧ ∃ z, newTopOf tp o = some (z, newTopNode tp i r'))) := by
  obtain ⟨_, _, _, _, hI2⟩ := pe_step hcf hi hI hw
  obtain ⟨_, _, hB2⟩ := pe_bridge hcf hi hI hB hkeys hw
  obtain ⟨hok, r, n, v, acc1, v', c0, r', acc2, hr, hn, hp, hsr, he, hout⟩ := peTx_spec hw
  have hi1 : i - 1 + 1 = i := by tomega
  have hsok : SOk cf i s := hi1 ▸ hI.sok
  have hgood : Good s r 0 none := good_of_invOk hr hI.inv
  have hnd : (R s r).Nodup := by
    have := hI.tree; unfold Contract.TreeOk at this; rwa [reach_eq_R hr] at this
  obtain ⟨r0, hr0, hsh0⟩ := hI.shaped
  have hrr : r0 = r := by rw [hr] at hr0; exact (Option.some.inj hr0).symm
  subst hrr
  have hobj : s.obj r0 = some (.key n) := getKey_obj hn
  have hht : htIn cf s r0 = cf.htOf n.level := by simp [htIn, hobj]
  have hpre : SegPre cf i s 0 (some r0) (dropNoops cf ops) ⟨[], next⟩ :=
    { sok := hsok
      fresh := hI.fresh
      ops := fun op hop => by
        have h1 : keyOk cf op.key = true := List.all_eq_true.mp hok op hop
        exact ⟨h1, key_ne_nil h1⟩
      root := fun r1 h => by
        cases h
        exact ⟨hsh0, hgood, hnd⟩ }
  have hkeys' : ((dropNoops cf ops).map Op.key).Nodup :=
    hkeys.sublist ((List.filter_sublist).map _)
  obtain ⟨W, hWok, _, hT⟩ := seg_space hcf hpre (hht ▸ hp) hsr he
  obtain ⟨W2, hW2, hform⟩ := seg_space_form hcf hpre (hht ▸ hp) hsr he
  obtain ⟨W3, hW3, hrch⟩ := seg_space_rch hcf hpre hkeys' (hht ▸ hp) hsr he
  have hws : acc2.ws = W := by simpa using hWok.ws
  have hW2W : W2 = W := by rw [← hws, hW2]; simp
  have hW3W : W3 = W := by rw [← hws, hW3]; simp
  rw [hW2W] at hform
  rw [hW3W] at hrch
  have hows : o.ws = W := by rcases hout with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> exact hws
  have hroots : o.roots = s.roots ∨ o.roots = s.roots ++ [(i, r')] := by
    rcases hout with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  set T := o.tree s with hTdef
  have hTobj : T.obj = (applyWs s W o.roots).obj := by simp [hTdef, Out.tree, hows]
  have hTroots : T.roots = o.roots := rfl
  have hafter : After s T W (R s r0) := by
    have := applyWs_after (s := s) (roots := o.roots) (U := R s r0) hWok.nodup
    exact ⟨fun p hp => by rw [hTobj]; exact this.ws p hp,
      fun z hz hz' => by rw [hTobj]; exact this.keep z hz hz',
      fun z hz => by rw [hTobj]; exact this.exist z hz⟩
  obtain ⟨_, hh, ht⟩ := hT T hafter
  have hTroot : T.root = some r' := by
    rcases hout with ⟨heq, rfl⟩ | ⟨_, rfl⟩
    · show s.root = some r'
      rw [hr, heq]
    · show (s.roots ++ [(i, r')]).getLast?.map (·.2) = some r'
      simp
  have hrootT : ∀ q ∈ s.roots, q.1 ≤ i - 1 := by rw [hI.roots]; exact roots_times hI.top
  have hcases : ∀ x, (∃ ob, (x, ob) ∈ W ∧ T.obj x = some ob) ∨
      (x ∉ W.map (·.1) ∧ T.obj x = s.obj x) := by
    intro x
    rw [hTobj]
    exact applyWs_obj_cases hWok.nodup x
  have hTat : T.at i = T := by
    apply tree_at_self
    · intro x nk hx u hu
      rcases hcases x with ⟨ob, hm, hx'⟩ | ⟨_, hx'⟩
      · rw [hx] at hx'
        exact hWok.times (x, ob) hm nk (by rw [Option.some.inj hx']) u hu
      · rw [hx] at hx'
        exact Nat.le_of_lt ((hsok x nk hx'.symm).2.2 u hu)
    · intro q hq
      rw [hTroots] at hq
      rcases hroots with h | h <;> rw [h] at hq
      · have := hrootT q hq; tomega
      · rcases List.mem_append.mp hq with hq | hq
        · have := hrootT q hq; tomega
        · simp at hq; rw [hq]
  have hsat : s.at (i - 1) = s := sok_at hsok (fun q hq => by have := hrootT q hq; tomega)
  have hreachT : reach T = R T r' := reach_eq_R hTroot
  have hreachS : reach s = R s r0 := reach_eq_R hr
  obtain ⟨nr, hnr, hlev, _, _, _⟩ := shaped_obj ht.shaped
  have hRT : R T r' = reachAt T (cf.lev 0 hh + 1) r' := by simp [R, Tree.fuel, hnr, hlev]
  have hsub := ht.reach _ (le_refl _)
  rw [← hRT] at hsub
  have hWids : ∀ w ∈ W.map (·.1), (next ≤ w ∧ w < acc2.next) ∨ w ∈ R s r0 := by
    intro w hw'
    simpa using hWok.ids w hw'
  have hTW : ∀ x ob, (x, ob) ∈ W → T.obj x = some ob := by
    intro x ob hm
    rw [hTobj]
    exact applyWs_obj_of_mem hWok.nodup hm
  have hTN : ∀ x, x ∉ W.map (·.1) → T.obj x = s.obj x := by
    intro x hx
    rw [hTobj]
    exact applyWs_obj_of_not hx
  have hlevS : LevOK s := fun x m hx => ptrsLow_iff.mp (hB.low x m hx)
  have hlevT : LevOK T := fun x m hx => ptrsLow_iff.mp (hB2.low x m hx)
  rw [hows]
  refine ⟨r0, r', ⟨hr, hTroot, ⟨nr, hnr⟩, fun p hp => hTW p.1 p.2 hp, hTN, hform,
    ?_, ?_, ?_, hI.tree, hI2.tree, hlevS, hlevT⟩, hTat, hsat, ?_⟩
  · intro x hx hsx
    rw [hreachS]
    rcases hWids x hx with ⟨h1, _⟩ | h1
    · exact absurd (hI.fresh x h1) hsx
    · exact h1
  · intro x hx
    rw [hreachT]
    exact rch_reachAt ht.good ht.shaped (hrch T hafter x hx) _ (le_refl _)
  · intro x hx hsx
    rw [hreachT] at hx
    rw [hreachS]
    rcases List.mem_append.mp (hsub.subset hx) with h | h
    · exact h
    · rw [List.mem_range'_1] at h
      exact absurd (hI.fresh x h.1) hsx
  · rcases hout with ⟨heq, rfl⟩ | ⟨hne, rfl⟩
    · left
      refine ⟨heq, ?_⟩
      simp [newTopOf]
    · right
      refine ⟨hne, acc2.next, ?_⟩
      simp [newTopOf]

/-! ## A-COPY, computed -/

/-- What A-COPY asks of a node y that an entry added names (`copyOk`'s
`named`, in words): a node made, or the pointee of a key klong of a node of
the writer's paths (reached before, and given an entry or not reached
after). -/
def NamedP (i : Nat) (s s' : Tree) (c : Changes BVal) (y : NodeId) : Prop :=
  (∃ nn ∈ c.new, nn.id = y) ∨
    ∃ z ∈ reach (s.at (i - 1)), ((∃ a ∈ c.adds, a.1 = z) ∨ z ∉ reach (s'.at i)) ∧
      namesKey s z y = true

/-- A-COPY from its clauses in words: every key entry and root pointer added
names a node as `NamedP` says, every skip pointer added the super root before
or the pointee of one of its skip pointers. -/
theorem copyOk_of {i : Nat} {s s' : Tree} {tp : Top} {c : Changes BVal}
    (h : ∀ a ∈ c.adds, (∀ c' y, a.2 = .key c' y → NamedP i s s' c y) ∧
      (∀ y, a.2 = .rootKey y → NamedP i s s' c y) ∧
      (∀ j y, a.2 = .skip j y → ∃ w nw, tp.getLast? = some (w, nw) ∧
        (y = w ∨ ∃ q ∈ nw.skips, q.2.1 = y))) :
    copyOk i s s' tp c = true := by
  have hn : ∀ y, NamedP i s s' c y →
      (c.new.any (fun nn => nn.id == y) ||
        ((reach (s.at (i - 1))).filter (fun x => c.adds.any (fun a => a.1 == x) ||
          c.touch.contains x || !(reach (s'.at i)).contains x)).contains y ||
        ((reach (s.at (i - 1))).filter (fun x => c.adds.any (fun a => a.1 == x) ||
          c.touch.contains x || !(reach (s'.at i)).contains x)).any (fun z => namesKey s z y)) =
        true := by
    intro y hy
    simp only [Bool.or_eq_true, List.any_eq_true, beq_iff_eq]
    rcases hy with ⟨nn, hnn, he⟩ | ⟨z, hz, hpz, hnk⟩
    · exact Or.inl (Or.inl ⟨nn, hnn, he⟩)
    · right
      refine ⟨z, List.mem_filter.mpr ⟨hz, ?_⟩, hnk⟩
      simp only [Bool.or_eq_true, List.any_eq_true, beq_iff_eq, List.contains_iff_mem,
        Bool.not_eq_true']
      rcases hpz with h1 | h1
      · exact Or.inl (Or.inl h1)
      · right; simpa using h1
  unfold copyOk
  simp only [List.all_eq_true]
  intro a ha
  obtain ⟨h1, h2, h3⟩ := h a ha
  split
  · rename_i c' y he
    have := hn y (h1 c' y he)
    simp only [Bool.or_eq_true] at this ⊢
    exact Or.inl this
  · rename_i y he
    have := hn y (h2 y he)
    simp only [Bool.or_eq_true] at this ⊢
    exact Or.inl this
  · rename_i j y he
    obtain ⟨w, nw, hl, hy⟩ := h3 j y he
    rw [hl]
    simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    rcases hy with hy | ⟨q, hq, hqy⟩
    · exact Or.inl hy
    · exact Or.inr ⟨q, hq, hqy⟩
  · rfl

/-- The skip pointers of a new top node: the super root before, or one of its
skip pointers (`TopDs.newSuperRoot`). -/
theorem newTopNode_skips {tp : Top} {i : Time} {r : NodeId} {q : Nat × NodeId × Time}
    (hq : q ∈ (newTopNode tp i r).skips) :
    ∃ w nw, tp.getLast? = some (w, nw) ∧ (q.2.1 = w ∨ ∃ q' ∈ nw.skips, q'.2.1 = q.2.1) := by
  unfold newTopNode at hq
  cases h : tp.getLast? with
  | none => rw [h] at hq; simp at hq
  | some wn =>
    obtain ⟨w, nw⟩ := wn
    rw [h] at hq
    simp only [List.mem_filterMap] at hq
    obtain ⟨j, _, hf⟩ := hq
    refine ⟨w, nw, rfl, ?_⟩
    split at hf
    · split at hf
      · rename_i q' hq'
        simp only [Option.some.injEq] at hf
        subst hf
        exact Or.inr ⟨q', List.mem_of_find?_eq_some hq', rfl⟩
      · simp only [Option.some.injEq] at hf
        subst hf
        exact Or.inl rfl
    · cases hf

section Abstract2

variable {i : Time} {s T : Tree} {W : List (NodeId × Obj)} {r0 r' : NodeId}

/-- A key entry that a node written got names a live child of it after: the
klongs it got are its new node's or emit's, whose key klongs are its live
list. -/
theorem TxF.newVals_key (hF : TxF i s T W r0 r') {x : NodeId} (hx : x ∈ W.map (·.1)) {c y : Nat}
    (hv : BVal.key c y ∈ newVals s T x) :
    ∃ m c', T.obj x = some (.key m) ∧ (c', y) ∈ live m.ks := by
  obtain ⟨ob, hm⟩ := mem_ws_of hx
  have hT := hF.ws _ hm
  simp only at hT
  rcases hF.form _ hm with ⟨hs0, ⟨v, hv0⟩ | ⟨l, b, F, hk, hlive⟩⟩ | ⟨n, F, hs0, hob, hlive, _⟩
  · simp only at hs0 hv0
    rw [hv0] at hT
    unfold newVals at hv
    rw [hT, hs0] at hv
    simp at hv
  · simp only at hs0 hk
    rw [hk] at hT
    unfold newVals at hv
    rw [hT, hs0] at hv
    simp only [List.drop_zero, List.mem_map] at hv
    obtain ⟨e, he, hev⟩ := hv
    obtain ⟨c', hc'⟩ := entriesFrom_ptr _ [] 0 [] e he y (by rw [hev]; simp [SIS.Check.bptrs])
    refine ⟨_, c', hT, ?_⟩
    simp only
    rw [hlive]
    simp only [newKs, keysOf, List.mem_cons, List.mem_map] at hc'
    rcases hc' with h | ⟨e', he', h⟩
    · cases h
    · injection h with h1 h2
      subst h1 h2
      exact he'
  · simp only at hs0 hob hlive
    rw [hob] at hT
    unfold newVals at hv
    rw [hT, hs0] at hv
    simp only [entriesOf_append, List.drop_left, List.mem_map] at hv
    obtain ⟨e, he, hev⟩ := hv
    obtain ⟨c', hc'⟩ := entriesFrom_ptr _ _ _ _ e he y (by rw [hev]; simp [SIS.Check.bptrs])
    refine ⟨_, c', hT, ?_⟩
    simp only
    rw [hlive]
    exact emitKs_ptrs hc'

theorem namesKey_of {s : Tree} {z y : NodeId} {n : KNode} {c : Nat} (hz : s.obj z = some (.key n))
    (hc : (c, y) ∈ live n.ks) : namesKey s z y = true := by
  unfold namesKey
  rw [hz]
  simp only [List.any_eq_true]
  exact ⟨_, live_mem_key hc, by simp⟩

end Abstract2

/-! ## The transaction -/

/-- **PE's transaction meets A-COPY and A6' and keeps `InvA`, given its
provenance** (`Prov`): from a state PE keeps at i - 1 (`Inv`) with `InvB`
and `InvA`, for operations of distinct keys. -/
theorem pe_adopt_copy_of_prov (hcf : cf.Ok) {i : Time} (hi : 1 ≤ i) {s : Tree} {tp : Top}
    {next : NodeId} {ops : List Op} {o : Out} (hI : Inv cf (i - 1) s tp next) (hB : InvB cf s)
    (hA : InvA cf s) (hkeys : (ops.map Op.key).Nodup) (hP : Prov s (o.tree s) o.D)
    (hw : peTx cf i s tp next ops = some o) :
    copyOk i s (o.tree s) tp (peChange cf s tp o) = true ∧
      adoptOk ((o.tree s).at i) = true ∧ InvA cf (o.tree s) := by
  obtain ⟨r0, r', hF, hTat, hsat, htop⟩ := pe_txF hcf hi hI hB hkeys hw
  have hP' : Prov s (o.tree s) (o.ws.map (·.1)) := hP
  have hA' := hF.invA hP' hA
  refine ⟨?_, by rw [hTat]; exact adoptOk_of_invA hA', hA'⟩
  set T := o.tree s with hTdef
  set W := o.ws with hWdef
  -- a node made: a fresh id written
  have hmade : ∀ y, y ∈ W.map (·.1) → s.obj y = none →
      ∃ nn ∈ (peChange cf s tp o).new, nn.id = y := by
    intro y hy hsy
    refine ⟨⟨y, lvlOf T y, isDataOf T y⟩, ?_, rfl⟩
    unfold peChange
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨y, List.mem_filter.mpr ⟨List.mem_reverse.mpr hy, by simp [hsy]⟩, rfl⟩
  have hreachT0 : ∀ z, z ∉ reach T → z ∉ reach (T.at i) := by rw [hTat]; exact fun z h => h
  apply copyOk_of
  intro a ha
  unfold peChange at ha
  rcases List.mem_append.mp ha with ha | ha
  · -- an entry of a node written
    obtain ⟨x, hx, hxv⟩ := List.mem_flatMap.mp ha
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hxv
    have hx : x ∈ W.map (·.1) := List.mem_reverse.mp hx
    simp only
    refine ⟨fun c' y hcy => ?_, fun y hy => ?_, fun j y hy => ?_⟩
    · subst hcy
      obtain ⟨m, c'', hTx, hlive⟩ := hF.newVals_key hx hv
      by_cases hsy : s.obj y = none
      · left
        obtain ⟨oy, hoy, _⟩ := hF.levT x m hTx c'' y (live_mem_key hlive)
        have hyW : y ∈ W.map (·.1) := by
          by_contra hn
          rw [hF.keep y hn, hsy] at hoy
          cases hoy
        exact hmade y hyW hsy
      · right
        rw [hsat]
        rcases hF.kid_named hP' hx hTx hlive hsy with ⟨n, c3, hsx, hc3⟩ | ⟨q, hqs, hqT, n, c3, hsq, hc3⟩
        · refine ⟨x, hF.oldW x hx (by rw [hsx]; simp), Or.inl ⟨(x, BVal.key c' y), ?_, rfl⟩,
            namesKey_of hsx hc3⟩
          unfold peChange
          apply List.mem_append_left
          exact List.mem_flatMap.mpr ⟨x, List.mem_reverse.mpr hx, List.mem_map.mpr ⟨_, hv, rfl⟩⟩
        · exact ⟨q, hqs, Or.inr (hreachT0 q hqT), namesKey_of hsq hc3⟩
    · subst hy
      rcases newVals_kind hv with ⟨_, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> cases h
    · subst hy
      rcases newVals_kind hv with ⟨_, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> cases h
  · -- the new top node's entries and the root's
    rcases htop with ⟨_, hnt⟩ | ⟨hne, z, hnt⟩
    · rw [hnt] at ha
      simp at ha
    · rw [hnt] at ha
      simp only [List.mem_cons, List.mem_map] at ha
      rcases ha with rfl | ⟨v, hv, rfl⟩
      · exact ⟨(fun _ _ h => by cases h), (fun _ h => by cases h), (fun _ _ h => by cases h)⟩
      · simp only [topVals, List.mem_cons, List.mem_map] at hv
        rcases hv with rfl | ⟨q, hq, rfl⟩
        · refine ⟨(fun _ _ h => by cases h), (fun y hy => ?_), (fun _ _ h => by cases h)⟩
          simp only [BVal.rootKey.injEq, newTopNode_root] at hy
          subst hy
          by_cases hsr : s.obj r' = none
          · left
            obtain ⟨m, hm⟩ := hF.key1
            have hrW : r' ∈ W.map (·.1) := by
              by_contra hn
              rw [hF.keep r' hn, hsr] at hm
              cases hm
            exact hmade r' hrW hsr
          · right
            rw [hsat]
            obtain ⟨q, hqs, hqT, n, c3, hsq, hc3⟩ := hF.root_named hP' hsr hne
            exact ⟨q, hqs, Or.inr (hreachT0 q hqT), namesKey_of hsq hc3⟩
        · refine ⟨(fun _ _ h => by cases h), (fun _ h => by cases h), (fun j y hy => ?_)⟩
          simp only [BVal.skip.injEq] at hy
          obtain ⟨_, rfl⟩ := hy
          obtain ⟨w, nw, hl, hc⟩ := newTopNode_skips hq
          exact ⟨w, nw, hl, hc⟩

/-! ## Runs and histories -/

/-- The top before the j-th transaction of a run from the top tp whose
transactions, each with the top after it, are L. -/
def topBefore (tp : Top) (L : List (BTx × Top)) : Nat → Top
  | 0 => tp
  | j + 1 => ((L[j]?).map (·.2)).getD tp

/-- **Every run of PE meets A-COPY and A6' and keeps `InvA`**, given each
transaction's provenance: from a state PE keeps at time t with `InvB` and
`InvA`, for transactions each of distinct keys, the run's transactions at
t + 1, t + 2, ... (`peRun`), as a history from s. -/
theorem pe_adopt_run (hcf : cf.Ok) (c0' : Changes BVal) :
    ∀ (txs : List (List Op)) (s : Tree) (tp : Top) (nx : NodeId) (t : Time)
      (L : List (BTx × Top)), Inv cf t s tp nx → InvB cf s → InvA cf s →
      (∀ ops ∈ txs, (ops.map Op.key).Nodup) → peRun cf s tp nx t txs = some L →
      (∀ j (hj : j < L.length), Prov ((⟨s, c0', L.map (·.1)⟩ : BHist).tree j)
        ((⟨s, c0', L.map (·.1)⟩ : BHist).tree (j + 1)) L[j].1.D) →
      ∀ j (hj : j < L.length),
        copyOk (t + j + 1) ((⟨s, c0', L.map (·.1)⟩ : BHist).tree j)
          ((⟨s, c0', L.map (·.1)⟩ : BHist).tree (j + 1)) (topBefore tp L j) L[j].1.c = true ∧
        adoptOk (((⟨s, c0', L.map (·.1)⟩ : BHist).tree (j + 1)).at (t + j + 1)) = true ∧
        InvA cf ((⟨s, c0', L.map (·.1)⟩ : BHist).tree (j + 1))
  | [], s, tp, nx, t, L, _, _, _, _, hr, _ => by
    simp only [peRun, Option.some.injEq] at hr
    subst hr
    intro j hj
    simp at hj
  | ops :: rest, s, tp, nx, t, L, hI, hB, hA, hk, hr, hP => by
    simp only [peRun] at hr
    split at hr
    · cases hr
    rename_i o hw
    cases hrest : peRun cf (o.tree s) o.top o.next (t + 1) rest with
    | none => rw [hrest] at hr; cases hr
    | some L' =>
      rw [hrest, Option.map_some, Option.some.injEq] at hr
      subst hr
      have hI' : Inv cf (t + 1 - 1) s tp nx := by simpa using hI
      have hko : (ops.map Op.key).Nodup := hk ops List.mem_cons_self
      have hP0 : Prov s (o.tree s) o.D := hP 0 (by simp)
      obtain ⟨hc, had, hA'⟩ :=
        pe_adopt_copy_of_prov hcf (Nat.succ_pos t) hI' hB hA hko hP0 hw
      obtain ⟨_, _, hB'⟩ := pe_bridge hcf (Nat.succ_pos t) hI' hB hko hw
      obtain ⟨_, _, _, _, hI2⟩ := pe_step hcf (Nat.succ_pos t) hI' hw
      have hP' : ∀ j (hj : j < L'.length),
          Prov ((⟨o.tree s, c0', L'.map (·.1)⟩ : BHist).tree j)
            ((⟨o.tree s, c0', L'.map (·.1)⟩ : BHist).tree (j + 1)) L'[j].1.D := by
        intro j hj
        have h1 := hP (j + 1) (by simp; omega)
        have e1 := bhist_tree_cons s c0' ⟨ops, o.D, o.tree s, peChange cf s tp o⟩ (L'.map (·.1)) j
          (by simp; omega)
        have e2 := bhist_tree_cons s c0' ⟨ops, o.D, o.tree s, peChange cf s tp o⟩ (L'.map (·.1))
          (j + 1) (by simp; omega)
        simp only [List.map_cons] at e1 e2 h1
        rw [e1, e2] at h1
        simpa using h1
      have ih := pe_adopt_run hcf c0' rest (o.tree s) o.top o.next (t + 1) L' (by simpa using hI2)
        hB' hA' (fun ops' h' => hk ops' (List.mem_cons_of_mem _ h')) hrest hP'
      intro j hj
      cases j with
      | zero =>
        exact ⟨hc, had, hA'⟩
      | succ j =>
        have hj' : j < L'.length := by simpa using hj
        obtain ⟨h1, h2, h3⟩ := ih j hj'
        have e1 := bhist_tree_cons s c0' ⟨ops, o.D, o.tree s, peChange cf s tp o⟩ (L'.map (·.1)) j
          (by simp; omega)
        have e2 := bhist_tree_cons s c0' ⟨ops, o.D, o.tree s, peChange cf s tp o⟩ (L'.map (·.1))
          (j + 1) (by simp; omega)
        simp only [List.map_cons] at e1 e2 ⊢
        rw [e1, e2]
        have htop : topBefore tp ((⟨ops, o.D, o.tree s, peChange cf s tp o⟩, o.top) :: L') (j + 1) =
            topBefore o.top L' j := by
          cases j with
          | zero => rfl
          | succ j =>
            have hj2 : j < L'.length := by omega
            simp [topBefore, List.getElem?_eq_getElem hj2]
        rw [htop, show t + (j + 1) + 1 = t + 1 + j + 1 by omega]
        exact ⟨by simpa using h1, h2, h3⟩

/-- **A6' and A-COPY for PE's history from the empty tree** (`peHist`, the
record of 030-21 part 2), for transactions each of distinct keys, given each
transaction's provenance (`Prov`): the clause `MeetsFull.adopt` at every time
and A-COPY of `MeetsFull.step` at every transaction, with the history's own
tops; and every tree of it meets `InvA`. -/
theorem pe_adopt_hist (hcf : cf.Ok) {txs : List (List Op)} {h : BHist} {top : Nat → Top}
    (hk : ∀ ops ∈ txs, (ops.map Op.key).Nodup) (hh : peHist cf txs = some (h, top))
    (hP : ∀ j (hj : j < h.txs.length), Prov (h.tree j) (h.tree (j + 1)) h.txs[j].D) :
    (∀ j, j ≤ h.txs.length → adoptOk ((h.tree j).at j) = true) ∧
    (∀ j (hj : j < h.txs.length),
      copyOk (j + 1) (h.tree j) (h.tree (j + 1)) (top j) h.txs[j].c = true) ∧
    ∀ j, j ≤ h.txs.length → InvA cf (h.tree j) := by
  unfold peHist at hh
  cases hr : peRun cf (startTree cf) startTop startNext 0 txs with
  | none => rw [hr] at hh; cases hh
  | some L =>
    rw [hr, Option.map_some, Option.some.injEq] at hh
    have hh1 := congrArg Prod.fst hh
    have hh2 := congrArg Prod.snd hh
    simp only at hh1 hh2
    subst hh1 hh2
    obtain ⟨h0, _, _⟩ := start_inv hcf
    have hP' : ∀ j (hj : j < L.length), Prov ((⟨startTree cf, c0 cf, L.map (·.1)⟩ : BHist).tree j)
        ((⟨startTree cf, c0 cf, L.map (·.1)⟩ : BHist).tree (j + 1)) L[j].1.D := by
      intro j hj
      have := hP j (by simpa using hj)
      simpa using this
    have hrun := pe_adopt_run hcf (c0 cf) txs _ _ _ 0 L h0 (invB_start hcf) invA_start hk hr hP'
    refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩
    · cases j with
      | zero =>
        show adoptOk ((startTree cf).at 0) = true
        rw [inv_at_zero h0]
        exact adoptOk_of_invA invA_start
      | succ j =>
        have hj' : j < L.length := by simpa using hj
        obtain ⟨_, h2, _⟩ := hrun j hj'
        rw [show 0 + j + 1 = j + 1 by omega] at h2
        exact h2
    · have hj' : j < L.length := by simpa using hj
      obtain ⟨h1, _, _⟩ := hrun j hj'
      rw [show 0 + j + 1 = j + 1 by omega] at h1
      simp only [List.getElem_map]
      cases j with
      | zero => exact h1
      | succ j => exact h1
    · cases j with
      | zero => exact invA_start
      | succ j =>
        have hj' : j < L.length := by simpa using hj
        exact (hrun j hj').2.2

/-! ## The touch -/

/-- PE's transactions touch nothing (no reclaim step), so the touch rules hold. -/
theorem touchOk_nil (s : Tree) (tp : Top) : touchOk s tp [] = true := by
  simp [touchOk]

theorem peRun_touch (cf : Cfg) : ∀ (txs : List (List Op)) (s : Tree) (tp : Top) (nx : NodeId)
    (t : Time) (L : List (BTx × Top)), peRun cf s tp nx t txs = some L →
    ∀ x ∈ L, x.1.c.touch = []
  | [], _, _, _, _, L, hr => by
    simp only [peRun, Option.some.injEq] at hr
    subst hr
    simp
  | ops :: rest, s, tp, nx, t, L, hr => by
    simp only [peRun] at hr
    split at hr
    · cases hr
    rename_i o _
    cases hrest : peRun cf (o.tree s) o.top o.next (t + 1) rest with
    | none => rw [hrest] at hr; cases hr
    | some L' =>
      rw [hrest, Option.map_some, Option.some.injEq] at hr
      subst hr
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · rfl
      · exact peRun_touch cf rest _ _ _ _ L' hrest x hx

/-- **The touch rules for PE's history** (`MeetsFull.step`'s `touchOk`): PE's
transactions touch nothing. -/
theorem pe_touch_hist {txs : List (List Op)} {h : BHist} {top : Nat → Top}
    (hh : peHist cf txs = some (h, top)) :
    ∀ j (hj : j < h.txs.length), touchOk ((h.tree j).at j) (top j) h.txs[j].c.touch = true := by
  unfold peHist at hh
  cases hr : peRun cf (startTree cf) startTop startNext 0 txs with
  | none => rw [hr] at hh; cases hh
  | some L =>
    rw [hr, Option.map_some, Option.some.injEq] at hh
    have hh1 := congrArg Prod.fst hh
    simp only at hh1
    subst hh1
    intro j hj
    have hj' : j < L.length := by simpa using hj
    have := peRun_touch cf txs _ _ _ 0 L hr L[j] (List.getElem_mem hj')
    simp only [List.getElem_map, this]
    exact touchOk_nil _ _

end Contract.PE
