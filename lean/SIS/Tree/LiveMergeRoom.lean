/-
The live merge with the parent with room (bergdb 030-01, step 3): every merge
whose parent has room and no compaction, of nodes the transaction made or not,
into one node or two. A merge into one node moves the hole to the parent
(`liveEdgesH_mergeOne`, LiveHole.lean); a merge into two nodes leaves no hole
(`liveEdges_mergeTwo`): both new nodes are filled (`mergeKlongs_live_fill`) and
the parent keeps its number of live klongs (`live_len_mergeTwo`), the second
node's compare value being none of the parent's but the right child's (as
`dw_mergeTail` shows for `d4`). A made node merged is taken back, which changes
no live klong (`writerWP_mergeCleanup_frameV`).
-/
import SIS.Tree.LiveLoop

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The parent of a merge into two nodes keeps its number of live klongs: by
its lookup (`mpNode_live_lookup`), the second node's compare value g not the
left one's and, unless it is the right one's, no live compare value of the
parent. -/
theorem live_len_mergeTwo (n n' : KNode) (cL cR g : Nat) (m1 m2 : NodeId)
    (hl : ∀ c, n'.live.lookup c = if c = g then some m2 else if c = cL then some m1
      else if c = cR then none else n.live.lookup c)
    (hgL : g ≠ cL) (hcR : ∃ z, n.live.lookup cR = some z)
    (hg : g ≠ cR → n.live.lookup g = none) :
    n.live.length ≤ n'.live.length := by
  have hK := n.live_keys_nodup
  have hK' := n'.live_keys_nodup
  have hmem' : ∀ k z, n'.live.lookup k = some z → k ∈ n'.live.map Prod.fst :=
    fun k z h => List.mem_map.mpr ⟨(k, z), bk_mem_of_lookup _ k z h, rfl⟩
  have hold : ∀ k, k ∈ n.live.map Prod.fst → k ≠ cR → k ∈ n'.live.map Prod.fst := by
    intro k hk hkR
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.mp hk
    have h1 := lookup_of_mem_nodup n.live hK a b hab
    by_cases hag : a = g
    · exact hmem' a m2 (by rw [hl a]; simp [hag])
    · by_cases haL : a = cL
      · exact hmem' a m1 (by rw [hl a, if_neg hag, if_pos haL])
      · exact hmem' a b (by rw [hl a]; simp [hag, haL, hkR, h1])
  have hgin : g ∈ n'.live.map Prod.fst := hmem' g m2 (by rw [hl g]; simp)
  by_cases hgR : g = cR
  · have := length_le_of_nodup_sub _ _ hK (fun k hk => by
      by_cases hkR : k = cR
      · rw [hkR, ← hgR]; exact hgin
      · exact hold k hk hkR)
    simpa using this
  · have hgn := hg hgR
    have hgK : g ∉ n.live.map Prod.fst := by
      intro hm
      obtain ⟨⟨a, b⟩, hab, ha⟩ := List.mem_map.mp hm
      simp only at ha
      subst ha
      rw [lookup_of_mem_nodup n.live hK a b hab] at hgn
      cases hgn
    have hnd : (g :: (n.live.map Prod.fst).erase cR).Nodup :=
      List.nodup_cons.mpr ⟨fun h => hgK (List.mem_of_mem_erase h), List.Nodup.erase cR hK⟩
    have h3 := length_le_of_nodup_sub _ _ hnd (fun k hk => by
      rcases List.mem_cons.mp hk with h | h
      · rw [h]; exact hgin
      · rw [List.Nodup.mem_erase_iff hK] at h
        exact hold k h.2 h.1)
    obtain ⟨zR, hzR⟩ := hcR
    have hRin : cR ∈ n.live.map Prod.fst :=
      List.mem_map.mpr ⟨(cR, zR), bk_mem_of_lookup _ _ _ hzR, rfl⟩
    rw [List.length_cons, List.length_erase_of_mem hRin, List.length_map, List.length_map] at h3
    have : 0 < n.live.length := by
      cases hn : n.live with
      | nil => rw [hn] at hzR; cases hzR
      | cons _ _ => simp
    omega

theorem nodup_of_keys_nodup (l : List (Nat × NodeId)) (h : (l.map Prod.fst).Nodup) : l.Nodup :=
  List.Pairwise.of_map Prod.fst (fun a b hab hne => hab (by rw [hne])) h

/-- A merge into two nodes leaves no hole: siblings l and rr under q, one of
them the hole (or none is), named by q's live klongs cL and cR, replaced by the
new nodes m1 and m2 of their kind, filled, whose live klongs name children of
theirs; q's live klongs after are cL naming m1, one naming m2, and its others but
cL's and cR's, at least as many as before; nothing else changes but l and rr,
which are left behind. -/
theorem liveEdges_mergeTwo (p : Params) (N N' : NodeId → Option KNode) (t : Time)
    (r q l rr m1 m2 : NodeId) (qn ln rn qn' mn1 mn2 : KNode) (cL cR : Nat) (Hl : NodeId → Prop)
    (hT : TreeOK N t r) (hq : TReach N t r q) (hqn : N q = some qn) (hql : qn.leaf = false)
    (hl : (cL, l) ∈ qn.liveAt t) (hrr : (cR, rr) ∈ qn.liveAt t)
    (hln : N l = some ln) (hrn : N rr = some rn) (hm1R : ¬ TReach N t r m1)
    (hm2R : ¬ TReach N t r m2)
    (hN'm1 : N' m1 = some mn1) (hN'm2 : N' m2 = some mn2)
    (hmn : ∀ mn, (mn = mn1 ∨ mn = mn2) → ∀ c z, (c, z) ∈ mn.liveAt t →
      (∃ c0, (c0, z) ∈ ln.liveAt t) ∨ (∃ c0, (c0, z) ∈ rn.liveAt t))
    (hml1 : mn1.leaf = ln.leaf) (hml2 : mn2.leaf = ln.leaf) (hrl : rn.leaf = ln.leaf)
    (hmne : mn1.liveAt t ≠ [] ∧ mn2.liveAt t ≠ [])
    (hmfill : p.mergeBelow ≤ (mn1.liveAt t).length ∧ p.mergeBelow ≤ (mn2.liveAt t).length)
    (hN'q : N' q = some qn') (hq'l : qn'.leaf = qn.leaf)
    (hq' : ∀ c z, (c, z) ∈ qn'.liveAt t →
      z = m1 ∨ z = m2 ∨ ((c, z) ∈ qn.liveAt t ∧ c ≠ cL ∧ c ≠ cR))
    (hq'len : (qn.liveAt t).length ≤ (qn'.liveAt t).length)
    (hother : ∀ y, y ≠ q → y ≠ l → y ≠ rr → y ≠ m1 → y ≠ m2 → N' y = N y)
    (hHl : ∀ y, Hl y → y = l ∨ y = rr)
    (h : LiveEdgesH p N t r Hl) :
    LiveEdges p N' t r := by
  have hlink_l : TLink N t q cL l := ⟨qn, hqn, hl⟩
  have hlink_r : TLink N t q cR rr := ⟨qn, hqn, hrr⟩
  have hlR : TReach N t r l := TReach.link hq hlink_l
  have hrR : TReach N t r rr := TReach.link hq hlink_r
  have hql' : q ≠ l := fun he => hT.no_self_link q cL hq (by rw [← he] at hlink_l; exact hlink_l)
  have hqr' : q ≠ rr := fun he => hT.no_self_link q cR hq (by rw [← he] at hlink_r; exact hlink_r)
  have hR' := mergeV_reach N N' t r q l rr m1 (some m2) qn ln rn qn' cL cR hT hq hqn hl hrr hln hrn
    hN'q (fun c z hc => by
      rcases hq' c z hc with hz | hz | hz
      · exact Or.inl hz
      · exact Or.inr (Or.inl (by rw [hz]))
      · exact Or.inr (Or.inr hz))
    (fun m mn' hm hmn' c z hz => by
      rcases hm with hm | hm
      · subst hm; rw [hN'm1] at hmn'; cases hmn'; exact hmn mn1 (Or.inl rfl) c z hz
      · cases hm; rw [hN'm2] at hmn'; cases hmn'; exact hmn mn2 (Or.inr rfl) c z hz)
    (fun y h1 h2 h3 h4 h5 => hother y h1 h2 h3 h4 (fun he => h5 (by cases he; rfl)))
    hm1R (fun m hm => by cases hm; exact hm2R)
  have hnotLR : ∀ u c z, TReach N t r u → TLink N t u c z → u ≠ q → z ≠ l ∧ z ≠ rr := by
    intro u c z hu hlk huq
    refine ⟨fun he => huq ?_, fun he => huq ?_⟩
    · rw [he] at hlk; exact (hT.oneLink u c q cL l hu hq hlk hlink_l).1
    · rw [he] at hlk; exact (hT.oneLink u c q cR rr hu hq hlk hlink_r).1
  have hnotM : ∀ u c z, TReach N t r u → TLink N t u c z → z ≠ m1 ∧ z ≠ m2 := by
    intro u c z hu hlk
    exact ⟨fun he => hm1R (by rw [← he]; exact TReach.link hu hlk),
      fun he => hm2R (by rw [← he]; exact TReach.link hu hlk)⟩
  have hnotH : ∀ z, z ≠ l → z ≠ rr → ¬ Hl z := by
    intro z h1 h2 hH
    rcases hHl z hH with h' | h'
    · exact h1 h'
    · exact h2 h'
  obtain ⟨dq, hdq⟩ := TReach.pathLen hq
  -- a child of l or rr is not q
  have hnotQ : ∀ P Pn c0 z, (P = l ∨ P = rr) → N P = some Pn → (c0, z) ∈ Pn.liveAt t → z ≠ q := by
    intro P Pn c0 z hP hPn hc0 hzq
    have hPd : PathLen N t r P (dq + 1) := by
      rcases hP with h' | h' <;> rw [h']
      · exact PathLen.link hdq hlink_l
      · exact PathLen.link hdq hlink_r
    have hz2 : PathLen N t r z (dq + 1 + 1) := PathLen.link hPd ⟨Pn, hPn, hc0⟩
    rw [hzq] at hz2
    have := PathLen.depth_unique hT _ _ _ hdq hz2
    omega
  -- the root
  have hqne : qn.liveAt t ≠ [] := by
    intro h0; rw [h0] at hl; cases hl
  refine ⟨fun rn0 hrn0 => ?_, fun u un c z zn hu hun hc hzn => ?_⟩
  · by_cases hrq : r = q
    · rw [hrq, hN'q] at hrn0; cases hrn0
      have hq0 := h.1 qn (by rw [hrq]; exact hqn)
      refine ⟨fun hE => ?_, fun hl' => ?_⟩
      · have h0 : (qn'.liveAt t).length = 0 := by rw [hE]; rfl
        exact absurd (List.eq_nil_of_length_eq_zero (by omega)) hqne
      · have := hq0.2 (by rw [hrq]; exact hnotH q hql' hqr') (by rw [← hq'l]; exact hl')
        omega
    · have hrl : r ≠ l := fun he => hT.rootFree q cL hq (by rw [← he] at hlink_l; exact hlink_l)
      have hrr' : r ≠ rr := fun he => hT.rootFree q cR hq (by rw [← he] at hlink_r; exact hlink_r)
      have hrm1 : r ≠ m1 := fun he => hm1R (by rw [← he]; exact TReach.root)
      have hrm2 : r ≠ m2 := fun he => hm2R (by rw [← he]; exact TReach.root)
      rw [hother r hrq hrl hrr' hrm1 hrm2] at hrn0
      exact ⟨(h.1 rn0 hrn0).1, (h.1 rn0 hrn0).2 (hnotH r hrl hrr')⟩
  · obtain ⟨huR, hul, hur⟩ := hR' u hu
    by_cases hum : u = m1 ∨ u = m2
    · -- a new node: its children are children of l or rr
      have hmn' : ∃ mn, (mn = mn1 ∨ mn = mn2) ∧ un = mn := by
        rcases hum with h' | h'
        · rw [h', hN'm1] at hun; cases hun; exact ⟨mn1, Or.inl rfl, rfl⟩
        · rw [h', hN'm2] at hun; cases hun; exact ⟨mn2, Or.inr rfl, rfl⟩
      obtain ⟨mn, hmm, hun'⟩ := hmn'
      rw [hun'] at hc
      have hmlf : mn.leaf = ln.leaf := by rcases hmm with h' | h' <;> rw [h'] <;> assumption
      have hsrc : ∃ P Pn c0, TReach N t r P ∧ N P = some Pn ∧ (c0, z) ∈ Pn.liveAt t ∧
          Pn.leaf = ln.leaf ∧ (P = l ∨ P = rr) := by
        rcases hmn mn hmm c z hc with ⟨c0, h0⟩ | ⟨c0, h0⟩
        · exact ⟨l, ln, c0, hlR, hln, h0, rfl, Or.inl rfl⟩
        · exact ⟨rr, rn, c0, hrR, hrn, h0, hrl, Or.inr rfl⟩
      obtain ⟨P, Pn, c0, hPR, hPn, hc0, hPl, hP⟩ := hsrc
      have hPq : P ≠ q := by
        rcases hP with h' | h'
        · rw [h']; exact Ne.symm hql'
        · rw [h']; exact Ne.symm hqr'
      obtain ⟨hzl, hzr⟩ := hnotLR P c0 z hPR ⟨Pn, hPn, hc0⟩ hPq
      obtain ⟨hzm1, hzm2⟩ := hnotM P c0 z hPR ⟨Pn, hPn, hc0⟩
      have hzq := hnotQ P Pn c0 z hP hPn hc0
      rw [hother z hzq hzl hzr hzm1 hzm2] at hzn
      rw [hun']
      exact childOK_grow p t Pn mn zn zn
        ((h.2 P Pn c0 z zn hPR hPn hc0 hzn).1 (hnotH z hzl hzr)) (by rw [hmlf, hPl]) rfl
        (Nat.le_refl _)
    · have hum1 : u ≠ m1 := fun he => hum (Or.inl he)
      have hum2 : u ≠ m2 := fun he => hum (Or.inr he)
      have huR' : TReach N t r u := by
        rcases huR with h' | h' | h'
        · exact h'
        · exact absurd h' hum1
        · exact absurd (Option.some.inj h') hum2
      by_cases huq : u = q
      · rw [huq, hN'q] at hun; cases hun
        rcases hq' c z hc with hz | hz | ⟨hc0, hcl, hcr⟩
        · subst hz
          rw [hN'm1] at hzn; cases hzn
          exact ⟨hmne.1, fun h1 => (by rw [hq'l, hql] at h1; cases h1), fun _ _ => hmfill.1⟩
        · subst hz
          rw [hN'm2] at hzn; cases hzn
          exact ⟨hmne.2, fun h1 => (by rw [hq'l, hql] at h1; cases h1), fun _ _ => hmfill.2⟩
        · have hzl : z ≠ l := fun he =>
            hcl (hT.oneLink q c q cL l hq hq (by rw [← he]; exact ⟨qn, hqn, hc0⟩) hlink_l).2
          have hzr : z ≠ rr := fun he =>
            hcr (hT.oneLink q c q cR rr hq hq (by rw [← he]; exact ⟨qn, hqn, hc0⟩) hlink_r).2
          obtain ⟨hzm1, hzm2⟩ := hnotM q c z hq ⟨qn, hqn, hc0⟩
          have hzq : z ≠ q := fun he => hT.no_self_link q c hq ⟨qn, hqn, by rw [he] at hc0; exact hc0⟩
          rw [hother z hzq hzl hzr hzm1 hzm2] at hzn
          exact childOK_grow p t qn _ zn zn ((h.2 q qn c z zn hq hqn hc0 hzn).1 (hnotH z hzl hzr))
            hq'l rfl (Nat.le_refl _)
      · rw [hother u huq hul hur hum1 hum2] at hun
        by_cases hzq : z = q
        · rw [hzq, hN'q] at hzn; cases hzn
          rw [hzq] at hc
          exact childOK_grow p t un un qn _ ((h.2 u un c q qn huR' hun hc hqn).1
            (hnotH q hql' hqr')) rfl hq'l hq'len
        · obtain ⟨hzl, hzr⟩ := hnotLR u c z huR' ⟨un, hun, hc⟩ huq
          obtain ⟨hzm1, hzm2⟩ := hnotM u c z huR' ⟨un, hun, hc⟩
          rw [hother z hzq hzl hzr hzm1 hzm2] at hzn
          exact (h.2 u un c z zn huR' hun hc hzn).1 (hnotH z hzl hzr)

/-- The klongs that `mergeParent` adds to its parent p when it stores p's new
version in place (its `need`). -/
def mergeParentNeed (tt : Time) (pn : KNode) (il ir cR : Nat) (m2 : Option (NodeId × Nat)) : Nat :=
  let deleteR := match m2 with
    | some (_, g) => g != cR
    | none => true
  let ofTt := pn.lastTime == some tt
  let after (i : Nat) : Bool := match pn.lastTimeIndex with
    | some ti => decide (ti < i)
    | none => false
  let hasTransDel := (match pn.ks.getLast? with
    | some (.del _) => true
    | _ => false) && ofTt
  let lInPlace := ofTt && after il
  let rInPlace := !deleteR && ofTt && after ir
  (if deleteR && !hasTransDel then 1 else 0) + (if lInPlace then 0 else 1) +
    (if m2.isNone || rInPlace then 0 else 1) + (if ofTt then 0 else 1)

theorem mergeParentNeed_le (tt : Time) (pn : KNode) (il ir cR : Nat) (m2 : Option (NodeId × Nat)) :
    mergeParentNeed tt pn il ir cR m2 ≤ 4 := by
  unfold mergeParentNeed
  cases m2 <;> simp only [Option.isNone_none, Option.isNone_some, Bool.true_or, Bool.false_or,
    ↓reduceIte, Nat.add_zero] <;> repeat' split
  all_goals omega

/-- `mergeParent`'s branch with room for these arguments: the parent's new
version fits and does not compact, so it is stored in place. Its negation is
`mergeParent`'s `full`. -/
def MergeParentRoom (c : Ctx) (pn : KNode) (il cL : Nat) (m1 : NodeId) (ir cR : Nat)
    (m2 : Option (NodeId × Nat)) : Prop :=
  pn.size + mergeParentNeed c.i pn il ir cR m2 ≤ c.p.M ∧
    deadOver c.p (mergeParentNode pn c.i il cL m1 ir cR m2) = false

/-- The second new node of a merge as `mergeTail` hands it to `mergeParent`, the
first new node being nx: nx + 2 with its first compare value, if the merge makes
two nodes. -/
def mergeM2 (c : Ctx) (xn ln rn : KNode) (cR : Nat) (nx : NodeId) : Option (NodeId × Nat) :=
  (mergeKlongs (!xn.leaf) c.p.mergeMax cR ln.live rn.live).2.map (fun s => (nx + 2, s.2))

/-- `mergeParent` in its branch with room: the parent's new version stored in
place. -/
theorem writerWP_mergeParent_roomB (p : NodeId) (pn : KNode) (depth il cL : Nat) (m1 : NodeId)
    (ir cR : Nat) (m2 : Option (NodeId × Nat)) (c : Ctx) (w : W) (post : Unit → W → Prop)
    (hlk : w.nodes.lookup p = some pn) (hB : MergeParentRoom c pn il cL m1 ir cR m2)
    (hroomP : ∀ s : String, post () ({ ({ w with trail := s :: w.trail } : W) with
      nodes := upsert w.nodes p (mergeParentNode pn c.i il cL m1 ir cR m2) } : W)) :
    WriterWP (mergeParent p depth il cL m1 ir cR m2) c w post := by
  unfold mergeParent
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known p pn c w hlk]
  apply writerWP_if
  · intro _
    apply writerWP_if
    · intro hd
      exfalso
      have h' : deadOver c.p (mergeParentNode pn c.i il cL m1 ir cR m2) = true := hd
      rw [hB.2] at h'
      cases h'
    · intro _
      simp only [note, putNode, writerWP_bind, writerWP_modify]
      exact hroomP _
  · intro hn
    exact absurd hB.1 hn

theorem mergeParentRoom_of_room (c : Ctx) (pn : KNode) (hroom : pn.size + 4 ≤ c.p.M)
    (hnd : ∀ il cL m1 ir cR m2, deadOver c.p (mergeParentNode pn c.i il cL m1 ir cR m2) = false)
    (il cL : Nat) (m1 : NodeId) (ir cR : Nat) (m2 : Option (NodeId × Nat)) :
    MergeParentRoom c pn il cL m1 ir cR m2 :=
  ⟨by have := mergeParentNeed_le c.i pn il ir cR m2; omega, hnd _ _ _ _ _ _⟩

/-- `mergeParent` with room and no compaction: the parent's new version stored
in place, into one node or two. -/
theorem writerWP_mergeParent_room (p : NodeId) (pn : KNode) (depth il cL : Nat) (m1 : NodeId)
    (ir cR : Nat) (m2 : Option (NodeId × Nat)) (c : Ctx) (w : W) (post : Unit → W → Prop)
    (hlk : w.nodes.lookup p = some pn) (hroom : pn.size + 4 ≤ c.p.M)
    (hnd : deadOver c.p (mergeParentNode pn c.i il cL m1 ir cR m2) = false)
    (hroomP : ∀ s : String, post () ({ ({ w with trail := s :: w.trail } : W) with
      nodes := upsert w.nodes p (mergeParentNode pn c.i il cL m1 ir cR m2) } : W)) :
    WriterWP (mergeParent p depth il cL m1 ir cR m2) c w post := by
  unfold mergeParent
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known p pn c w hlk]
  apply writerWP_if
  · intro _
    apply writerWP_if
    · intro hd
      exfalso
      have h' : deadOver c.p (mergeParentNode pn c.i il cL m1 ir cR m2) = true := hd
      rw [hnd] at h'
      cases h'
    · intro _
      simp only [note, putNode, writerWP_bind, writerWP_modify]
      exact hroomP _
  · intro hn
    exfalso
    apply hn
    cases m2 <;> simp only [Option.isNone_none, Option.isNone_some, Bool.true_or, Bool.false_or,
      ↓reduceIte, Nat.add_zero] <;> repeat' split
    all_goals omega

set_option maxHeartbeats 16000000 in
/-- A merge whose parent takes `mergeParent`'s branch with room (`MergeParentRoom`
for the merge's arguments), of nodes the transaction made or not: into one node it keeps the hole's form with the parent
the hole after, and the nodes but the parent, the two merged and the new one
keep their lookups; into two nodes it leaves no hole. -/
theorem writerWP_mergeTail_liveRoomB (c : Ctx) (base : View BVal) (x : NodeId) (d : Nat) (p : NodeId)
    (pn xn : KNode) (leftSome : Bool) (l : NodeId) (ln : KNode) (il : Nat) (r : NodeId)
    (rn : KNode) (ir : Nat) (cL cR : Nat) (N : NodeId → Option KNode) (root : NodeId) (nx : Nat)
    (w3 : W) (Hl : NodeId → Prop) (hm : c.p.merges = true) (hMP : MergeParamsOK c.p)
    (hT : TreeOK N c.i root) (hp : TReach N c.i root p) (hpn : N p = some pn)
    (hL : pn.ks[il]? = some (.key cL l)) (hLL : LastLive pn.ks pn.lastBitmap il cL)
    (hR : pn.ks[ir]? = some (.key cR r)) (hRL : LastLive pn.ks pn.lastBitmap ir cR)
    (hclt : cL < cR) (hadj : ∀ cc z, (cc, z) ∈ pn.liveAt c.i → cc ≤ cL ∨ cR ≤ cc)
    (hxlr : x = l ∨ x = r) (hln : N l = some ln) (hrn : N r = some rn)
    (hpwf : klongsWf pn.ks = true) (hpt : ∀ s, Klong.time s ∈ pn.ks → s ≤ c.i)
    (hch : ∀ cc z zn, (cc, z) ∈ pn.liveAt c.i → N z = some zn →
      ∀ s, Klong.time s ∈ zn.ks → s ≤ c.i)
    (hN3 : wNode c.p base w3 = N) (h3top : w3.top.rootKey = root) (h3next : w3.next = nx)
    (h3p : w3.nodes.lookup p = some pn) (h3src : ∀ z, (w3.nodes.lookup z).isSome = true → z < nx)
    (hfree : ∀ z, nx ≤ z → N z = none ∧ w3.taken.contains z = false)
    (hfreshT : ∀ z, nx ≤ z → ∀ u c', TReach N c.i root u → ¬ TLink N c.i u c' z)
    (hpleaf : pn.leaf = false) (hll : ln.leaf = xn.leaf) (hrl : rn.leaf = xn.leaf)
    (hlrange : ∀ cc z, (cc, z) ∈ ln.liveAt c.i → cc < cR)
    (hllow : ∀ cc z, (cc, z) ∈ ln.liveAt c.i →
      ((!xn.leaf) = true → cc = 0 ∨ cL < cc) ∧ ((!xn.leaf) = false → cL ≤ cc))
    (hrrange : ∀ cc z, (cc, z) ∈ rn.liveAt c.i →
      ((!xn.leaf) = true → cc = 0 ∨ cR < cc) ∧ ((!xn.leaf) = false → cR ≤ cc))
    (hrup : ∀ k z, (k, z) ∈ pn.liveAt c.i → cR < k → ∀ cc z', (cc, z') ∈ rn.liveAt c.i → cc < k)
    (hB : MergeParentRoom c pn il cL nx ir cR (mergeM2 c xn ln rn cR nx))
    (hLive : LiveEdgesH c.p N c.i root Hl) (hHl : ∀ y, Hl y → y = x) :
    WriterWP (mergeTail c x d p pn xn leftSome l ln il r rn ir) c w3
      (fun res w' => (res = 1 →
        LiveEdgesH c.p (wNode c.p base w') c.i w'.top.rootKey (fun y => y = p) ∧
        (∀ y, y ≠ p → y ≠ l → y ≠ r → y ≠ nx → w'.nodes.lookup y = w3.nodes.lookup y) ∧
        w'.top = w3.top) ∧
        (res ≠ 1 → LiveEdges c.p (wNode c.p base w') c.i w'.top.rootKey)) := by
  -- the tree's facts
  have hpL : (cL, l) ∈ pn.liveAt c.i := by
    rw [KNode.liveAt_of_times pn c.i hpt]
    apply bk_mem_of_lookup
    rw [KNode.live_lookup]
    exact keyLookup_of_last _ _ _ il l hL hLL
  have hpR : (cR, r) ∈ pn.liveAt c.i := by
    rw [KNode.liveAt_of_times pn c.i hpt]
    apply bk_mem_of_lookup
    rw [KNode.live_lookup]
    exact keyLookup_of_last _ _ _ ir r hR hRL
  have hc : cL ≠ cR := Nat.ne_of_lt hclt
  have hlink_l : TLink N c.i p cL l := ⟨pn, hpn, hpL⟩
  have hlink_r : TLink N c.i p cR r := ⟨pn, hpn, hpR⟩
  have hpl : p ≠ l := fun h => hT.no_self_link p cL hp (by rw [← h] at hlink_l; exact hlink_l)
  have hpr : p ≠ r := fun h => hT.no_self_link p cR hp (by rw [← h] at hlink_r; exact hlink_r)
  have hlr : l ≠ r := fun h => hc (hT.oneLink p cL p cR l hp hp hlink_l (by rw [h]; exact hlink_r)).2
  have hlt := hch cL l ln hpL hln
  have hrt := hch cR r rn hpR hrn
  have hcvL : pn.cv? il = some cL := by simp [KNode.cv?, hL]
  have hcvR : pn.cv? ir = some cR := by simp [KNode.cv?, hR]
  have hlt_nx : ∀ y yn, N y = some yn → y < nx := by
    intro y yn hy
    rcases Nat.lt_or_ge y nx with h | h
    · exact h
    · have := (hfree y h).1; rw [this] at hy; cases hy
  have hlnx := hlt_nx l ln hln
  have hrnx := hlt_nx r rn hrn
  have hpnx := hlt_nx p pn hpn
  -- the sibling of the hole is filled: the two hold m live klongs or more
  have hsib : c.p.mergeBelow ≤ ln.live.length + rn.live.length := by
    have hok : ∀ s sn, N s = some sn → (∃ cs, (cs, s) ∈ pn.liveAt c.i) → s ≠ x →
        c.p.mergeBelow ≤ (sn.liveAt c.i).length := by
      intro s sn hs ⟨cs, hcs⟩ hsx
      exact ((hLive.2 p pn cs s sn hp hpn hcs hs).1 (fun h => hsx (hHl s h))).2.2 hpleaf hm
    rcases hxlr with hx | hx
    · have := hok r rn hrn ⟨cR, hpR⟩ (by rw [hx]; exact hlr.symm)
      rw [KNode.liveAt_of_times rn c.i hrt] at this
      omega
    · have := hok l ln hln ⟨cL, hpL⟩ (by rw [hx]; exact hlr)
      rw [KNode.liveAt_of_times ln c.i hlt] at this
      omega
  have hmb : 2 ≤ c.p.mergeBelow := hMP.1
  unfold mergeTail
  simp only [hcvL, hcvR]
  generalize hLM : (ln.firstTime == some c.i) = lMade
  generalize hRM : (rn.firstTime == some c.i) = rMade
  simp only [note, writerWP_bind, writerWP_modify, writerWP_pure]
  have hBm : ∀ first second, mergeKlongs (!xn.leaf) c.p.mergeMax cR ln.live rn.live =
      (first, second) → MergeParentRoom c pn il cL nx ir cR (second.map (fun s => (nx + 2, s.2))) := by
    intro f s h
    have := hB
    rw [mergeM2, h] at this
    exact this
  generalize hmk : mergeKlongs (!xn.leaf) c.p.mergeMax cR ln.live rn.live = fs
  obtain ⟨first, second⟩ := fs
  have hB' := hBm first second hmk
  wpSplit
  · simp only [writerWP_bind]; exact writerWP_throw _ _ _ _
  wpSplit
  · simp only [writerWP_bind]; exact writerWP_throw _ _ _ _
  rename_i hne1 hne2
  have hrhead : (!xn.leaf) = true → ∃ y0 tl, rn.live = (0, y0) :: tl := by
    intro hin
    rw [hin] at hne2
    simp only [Bool.true_and, Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not]
      at hne2
    cases hr' : rn.live with
    | nil => rw [hr'] at hne2; simp at hne2
    | cons a tl =>
      rw [hr'] at hne2
      simp only [List.head?_cons, Option.map_some, Option.some.injEq] at hne2
      exact ⟨a.2, tl, by rw [← hne2.2]⟩
  have hsortE := mrg_mergeList_sorted ln rn c.i (!xn.leaf) cR hlt hrt hlrange hrrange hrhead
  have hmkd : splitMerged (!xn.leaf) c.p.mergeMax (mergeList (!xn.leaf) cR ln.live rn.live) =
      (first, second) := hmk
  have hElen : (mergeList (!xn.leaf) cR ln.live rn.live).length = ln.live.length + rn.live.length :=
    by simpa using congrArg List.length (mergeList_map_snd (!xn.leaf) cR ln.live rn.live)
  -- the new nodes: their klongs name children of l or r, and they are filled
  have hsrcE : ∀ z, z ∈ (mergeList (!xn.leaf) cR ln.live rn.live).map Prod.snd →
      (∃ c0, (c0, z) ∈ ln.liveAt c.i) ∨ (∃ c0, (c0, z) ∈ rn.liveAt c.i) := by
    intro z hz
    rw [mergeList_map_snd] at hz
    rcases List.mem_append.mp hz with h | h
    · obtain ⟨q', hq', he⟩ := List.mem_map.mp h
      exact Or.inl ⟨q'.1, by rw [KNode.liveAt_of_times ln c.i hlt, ← he]; exact hq'⟩
    · obtain ⟨q', hq', he⟩ := List.mem_map.mp h
      exact Or.inr ⟨q'.1, by rw [KNode.liveAt_of_times rn c.i hrt, ← he]; exact hq'⟩
  have hnewT : ∀ ks : List (Nat × NodeId), ∀ s, Klong.time s ∈
      ({ leaf := !!xn.leaf, ks := newKlongs c.i ks } : KNode).ks → s ≤ c.i := by
    intro ks s hs
    simp only [newKlongs, List.mem_cons, Klong.time.injEq, List.mem_map, reduceCtorEq, and_false,
      exists_false, or_false] at hs
    omega
  have hnewSrc : ∀ ks : List (Nat × NodeId), (∀ z, z ∈ ks.map Prod.snd →
      z ∈ (mergeList (!xn.leaf) cR ln.live rn.live).map Prod.snd) → ∀ cc z,
      (cc, z) ∈ ({ leaf := !!xn.leaf, ks := newKlongs c.i ks } : KNode).liveAt c.i →
      (∃ c0, (c0, z) ∈ ln.liveAt c.i) ∨ (∃ c0, (c0, z) ∈ rn.liveAt c.i) := by
    intro ks hks cc z hmem
    have hm2 := liveAt_newKlongs_mem (!!xn.leaf) c.i c.i ks cc z hmem
    exact hsrcE z (hks z (List.mem_map.mpr ⟨(cc, z), hm2, rfl⟩))
  have hnewFill : ∀ ks : List (Nat × NodeId), CvSorted ks → c.p.mergeBelow ≤ ks.length →
      ({ leaf := !!xn.leaf, ks := newKlongs c.i ks } : KNode).liveAt c.i ≠ [] ∧
      c.p.mergeBelow ≤ (({ leaf := !!xn.leaf, ks := newKlongs c.i ks } : KNode).liveAt c.i).length := by
    intro ks hks hlen
    have hcnt : (({ leaf := !!xn.leaf, ks := newKlongs c.i ks } : KNode).liveAt c.i).length =
        ks.length := by
      rw [KNode.liveAt_of_times _ c.i (hnewT ks)]
      exact newKlongs_cnt_of_sorted _ _ _ hks
    refine ⟨fun h0 => ?_, by rw [hcnt]; exact hlen⟩
    have : (({ leaf := !!xn.leaf, ks := newKlongs c.i ks } : KNode).liveAt c.i).length = 0 := by
      rw [h0]; rfl
    omega
  simp only [writerWP_bind, writerWP_modify]
  refine writerWP_mono (writerWP_ghOf_frame x c _) ?_
  intro gh w4 ⟨h4t, h4top, h4n, h4v, h4p, h4m, h4l⟩
  have hlk4 : ∀ y, y ≠ x → w4.nodes.lookup y = w3.nodes.lookup y := h4l
  have hnone3 : ∀ z, nx ≤ z → w3.nodes.lookup z = none := by
    intro z hz
    cases h' : w3.nodes.lookup z with
    | none => rfl
    | some _ => have := h3src z (by rw [h']; rfl); omega
  have hpx : p ≠ x := by rcases hxlr with h | h <;> rw [h] <;> assumption
  have hxnx : x < nx := by rcases hxlr with h | h <;> rw [h] <;> assumption
  have hpT : w3.taken.contains p = false := by
    have := hN3 ▸ hpn
    unfold wNode at this
    split at this
    · cases this
    · rename_i h; simpa using h
  have hNw3 : ∀ y, wNode c.p base w3 y = N y := fun y => by rw [hN3]
  have hcl' : ∀ y, y ≠ l → y ≠ r → ∀ q ∈ [(l, lMade), (r, rMade)], y ≠ (q : NodeId × Bool).1 := by
    intro y hyl hyr q hq
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with h | h <;> rw [h] <;> assumption
  have hne' : ∀ q ∈ [(l, lMade), (r, rMade)], (q : NodeId × Bool).1 ≠ p := by
    intro q hq
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with h | h <;> rw [h]
    · exact Ne.symm hpl
    · exact Ne.symm hpr
  have hlr' : ∀ (q : NodeId × Bool), q ∈ [(l, lMade), (r, rMade)] → q.1 = l ∨ q.1 = r := by
    intro q hq
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with h | h <;> rw [h]
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hnoOld : ∀ z, (z = l ∨ z = r) → ∀ cc, (cc, z) ∈ pn.liveAt c.i → cc ≠ cL → cc ≠ cR → False := by
    intro z hz cc hmem h1 h2
    rcases hz with hz | hz
    · rw [hz] at hmem
      exact h1 (hT.oneLink p cc p cL l hp hp ⟨pn, hpn, hmem⟩ hlink_l).2
    · rw [hz] at hmem
      exact h2 (hT.oneLink p cc p cR r hp hp ⟨pn, hpn, hmem⟩ hlink_r).2
  have hmpT : ∀ il' cL' m1' ir' cR' m2', ∀ s, Klong.time s ∈
      (mergeParentNode pn c.i il' cL' m1' ir' cR' m2').ks → s ≤ c.i := by
    intro il' cL' m1' ir' cR' m2'
    rw [mergeParentNode_eq]
    exact mpNode_times pn c.i _ _ _ _ _ _ _ _ _ (htd_last pn _) hpt
  try dsimp only
  cases lMade <;> cases rMade <;>
    simp only [Bool.false_eq_true, ↓reduceIte, writerWP_bind, writerWP_modify, writerWP_pure,
      replacedBy, writerWP_get]
  all_goals
    refine writerWP_mono (writerWP_newKey_frame _ _ _ _ c _) ?_
    intro m1 w5 ⟨hm1, h5n, h5t, h5top, h5next, h5v, h5p, h5m⟩
    refine writerWP_mono (writerWP_setMadeFor_frame _ _ c _) ?_
    intro _ w6 ⟨h6n, h6t, h6top, h6next, h6v, h6p⟩
    try dsimp only at hm1 h5n h5t h5top h5next h5v h5p h5m
    have hm1 : m1 = nx := by rw [hm1, h4n, h3next]
    subst hm1
    have hw6p : w6.nodes.lookup p = some pn := by
      rw [h6n, h5n, lookup_append_single_ne _ _ _ _ (by omega), hlk4 p hpx, h3p]
    have hw6m1 : w6.nodes.lookup m1 = some ⟨!!xn.leaf, newKlongs c.i first⟩ := by
      rw [h6n, h5n, h4n, h3next, lookup_append_single_self]
      rw [hlk4 _ (by omega)]
      exact hnone3 m1 (Nat.le_refl _)
    have h6taken : w6.taken = w3.taken := by rw [h6t, h5t, h4t]
    have h6old : ∀ y, y ≠ x → y ≠ m1 → w6.nodes.lookup y = w3.nodes.lookup y := by
      intro y hyx hym
      rw [h6n, h5n, h4n, h3next, lookup_append_single_ne _ _ _ _ hym, hlk4 y hyx]
    have h6next' : w6.next = m1 + 2 := by rw [h6next, h5next, h4n, h3next]
    have h6top' : w6.top.rootKey = root := by rw [h6top, h5top, h4top, h3top]
    have hm1T : w3.taken.contains m1 = false := (hfree m1 (Nat.le_refl _)).2
    have hm1N : N m1 = none := (hfree m1 (Nat.le_refl _)).1
    have hlm1 : l ≠ m1 := by omega
    have hrm1 : r ≠ m1 := by omega
    have hpm1 : p ≠ m1 := by omega
    have hm1R : ¬ TReach N c.i root m1 :=
      not_reach_fresh N c.i root m1 hT hm1N (hfreshT m1 (Nat.le_refl _))
    cases hsec : second with
    | none =>
      rw [hsec] at hmkd
      have hfirst : first = mergeList (!xn.leaf) cR ln.live rn.live := splitMerged_one _ _ _ _ hmkd
      simp only [writerWP_bind, writerWP_pure]
      refine writerWP_mergeParent_roomB p pn (d - 1) il cL m1 ir cR none c w6 _ hw6p
        (by rw [hsec] at hB'; exact hB') ?_
      intro s7
      generalize hw7 : ({ ({ w6 with trail := s7 :: w6.trail } : W) with
        nodes := upsert w6.nodes p (mergeParentNode pn c.i il cL m1 ir cR none) } : W) = w7
      have h7n : w7.nodes = upsert w6.nodes p (mergeParentNode pn c.i il cL m1 ir cR none) := by
        rw [← hw7]
      have h7t : w7.taken = w6.taken := by rw [← hw7]
      have h7top : w7.top = w6.top := by rw [← hw7]
      have hlk7 : w7.nodes.lookup p = some (mergeParentNode pn c.i il cL m1 ir cR none) := by
        rw [h7n, lookup_upsert]; simp
      have hchar1 : ∀ cc z, (cc, z) ∈ (mergeParentNode pn c.i il cL m1 ir cR none).liveAt c.i →
          (cc = cL ∧ z = m1) ∨ ((cc, z) ∈ pn.liveAt c.i ∧ cc ≠ cL ∧ cc ≠ cR) := by
        intro cc z hmem
        rw [KNode.liveAt_of_times _ c.i (hmpT _ _ _ _ _ _)] at hmem
        have hlk := lookup_of_mem_nodup _ (KNode.live_keys_nodup _) cc z hmem
        rw [mergeParentNode_eq, mpNode_live_lookup pn c.i il cL m1 ir cR none _ _ _ l r hpwf hL hLL hR
          hRL hc ?htd (fun _ _ _ h => by cases h) cc] at hlk
        case htd => exact htd_last pn _
        simp only at hlk
        by_cases h1 : cc = cL
        · simp only [h1, ↓reduceIte, Option.some.injEq] at hlk
          exact Or.inl ⟨h1, hlk.symm⟩
        · by_cases h2 : cc = cR
          · simp [h2, Ne.symm hc] at hlk
          · simp only [h1, h2, ↓reduceIte] at hlk
            right
            refine ⟨?_, h1, h2⟩
            rw [KNode.liveAt_of_times pn c.i hpt]
            exact bk_mem_of_lookup _ cc z hlk
      have hcLm1 : (cL, m1) ∈ (mergeParentNode pn c.i il cL m1 ir cR none).liveAt c.i := by
        rw [KNode.liveAt_of_times _ c.i (hmpT _ _ _ _ _ _)]
        apply bk_mem_of_lookup
        rw [mergeParentNode_eq, mpNode_live_lookup pn c.i il cL m1 ir cR none _ _ _ l r hpwf hL hLL hR
          hRL hc ?htd (fun _ _ _ h => by cases h) cL]
        case htd => exact htd_last pn _
        simp
      refine writerWP_mono (writerWP_mergeCleanup_frameV p m1 c.i c _ w7 _ hne' hlk7
        (fun q hq c' hmem => by
          rcases hchar1 c' q.1 hmem with ⟨_, h⟩ | ⟨hold, h1, h2⟩
          · rcases hlr' q hq with h' | h' <;> rw [h'] at h
            · exact hlm1 h
            · exact hrm1 h
          · exact hnoOld q.1 (hlr' q hq) c' hold h1 h2)) ?_
      intro _ w8 ⟨h8top, _, _, h8t, h8l, pn8, h8p, h8leaf, _, h8iff⟩
      refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
      have h8tc : ∀ y, y ≠ l → y ≠ r → w8.taken.contains y = w3.taken.contains y := by
        intro y hyl hyr; rw [h8t y (hcl' y hyl hyr), h7t, h6taken]
      have h8l' : ∀ y, y ≠ p → y ≠ l → y ≠ r → w8.nodes.lookup y = w6.nodes.lookup y := by
        intro y hyp hyl hyr; rw [h8l y hyp (hcl' y hyl hyr), h7n, lookup_upsert]; simp [hyp]
      refine ⟨?_, fun y hyp hyl hyr hym => ?_, by rw [h8top, h7top, h6top, h5top, h4top]⟩
      rotate_left
      · rw [h8l' y hyp hyl hyr, h6old y (by rcases hxlr with h | h <;> rw [h] <;> assumption) hym]
      rw [h8top, h7top, h6top']
      have hfirstS : CvSorted first := by rw [hfirst]; exact hsortE
      have hmlen : first.length = ln.live.length + rn.live.length := by rw [hfirst, hElen]
      obtain ⟨hmne, hmfill⟩ := hnewFill first hfirstS (by rw [hmlen]; exact hsib)
      refine liveEdgesH_mergeOne c.p N (wNode c.p base w8) c.i root p l r m1 pn ln rn pn8
        ⟨!!xn.leaf, newKlongs c.i first⟩ cL cR Hl hT hp hpn hpleaf hpL hpR hln hrn hm1R ?_
        (hnewSrc first (fun z hz => by rw [hfirst] at hz; exact hz))
        (by show (!!xn.leaf) = ln.leaf; rw [hll, Bool.not_not]) (by rw [hrl, hll]) hmne hmfill ?_
        (by rw [h8leaf, mrg_mergeParentNode_leaf]) ?_ ?_ ?_
        (fun y hy => by
          have hyx := hHl y hy
          rcases hxlr with h | h
          · exact Or.inl (hyx.trans h)
          · exact Or.inr (hyx.trans h))
        hLive
      · simp only [wNode, h8tc m1 (Ne.symm hlm1) (Ne.symm hrm1), hm1T, Bool.false_eq_true,
          ↓reduceIte]
        rw [h8l' m1 (Ne.symm hpm1) (Ne.symm hlm1) (Ne.symm hrm1), hw6m1]
      · simp only [wNode, h8tc p hpl hpr, hpT, Bool.false_eq_true, ↓reduceIte, h8p]
      · intro cc z hmem
        exact hchar1 cc z ((h8iff cc z).mp hmem)
      · intro h0
        have := (h8iff cL m1).mpr hcLm1
        rw [h0] at this
        cases this
      · intro y hyp hyl hyr hym
        rw [← hNw3 y]
        unfold wNode
        rw [h8tc y hyl hyr, h8l' y hyp hyl hyr,
          h6old y (by rcases hxlr with h | h <;> rw [h] <;> assumption) hym]
    | some ksg =>
      obtain ⟨ks2, g2⟩ := ksg
      rw [hsec] at hmkd
      have hcap : 1 ≤ c.p.mergeMax := by have := hMP.1; have := hMP.2.1; omega
      obtain ⟨yg, hE1, hgs, hE2⟩ := mrg_splitMerged_two (!xn.leaf) c.p.mergeMax hcap _ first ks2 g2 hmkd
      have hElt : c.p.mergeMax < (mergeList (!xn.leaf) cR ln.live rn.live).length := by
        rcases Nat.lt_or_ge c.p.mergeMax (mergeList (!xn.leaf) cR ln.live rn.live).length with h | h
        · exact h
        · exfalso
          unfold splitMerged at hmkd
          simp only [show (mergeList (!xn.leaf) cR ln.live rn.live).length ≤ c.p.mergeMax from h,
            ↓reduceIte, Prod.mk.injEq, reduceCtorEq, and_false] at hmkd
      have hlnL : ∀ q ∈ ln.live, q.1 < cR ∧ ((!xn.leaf) = true → q.1 = 0 ∨ cL < q.1) ∧
          ((!xn.leaf) = false → cL ≤ q.1) := by
        intro q hq
        have hq' : (q.1, q.2) ∈ ln.liveAt c.i := by rw [KNode.liveAt_of_times ln c.i hlt]; exact hq
        exact ⟨hlrange _ _ hq', hllow _ _ hq'⟩
      have hrnR : ∀ q ∈ rn.live, ((!xn.leaf) = true → q.1 = 0 ∨ cR < q.1) ∧
          ((!xn.leaf) = false → cR ≤ q.1) := by
        intro q hq
        have hq' : (q.1, q.2) ∈ rn.liveAt c.i := by rw [KNode.liveAt_of_times rn c.i hrt]; exact hq
        exact hrrange _ _ hq'
      obtain ⟨hgL, _, hgU0⟩ := mrg_two_g (!xn.leaf) cL cR ln.live rn.live
        (((mergeList (!xn.leaf) cR ln.live rn.live).length + 1) / 2) g2 yg hsortE (by omega) hgs
        hclt hlnL hrnR
      have hg2 : g2 ≠ cR → pn.live.lookup g2 = none := by
        intro hne
        cases hlg : pn.live.lookup g2 with
        | none => rfl
        | some z =>
          exfalso
          have hm : (g2, z) ∈ pn.liveAt c.i := by
            rw [KNode.liveAt_of_times pn c.i hpt]; exact bk_mem_of_lookup _ _ _ hlg
          rcases hadj g2 z hm with h1 | h1
          · omega
          · have hgt : cR < g2 := by omega
            have := hgU0 g2 hgt (fun q hq => hrup g2 z hm hgt q.1 q.2 (by
              rw [KNode.liveAt_of_times rn c.i hrt]; exact hq))
            omega
      -- the halves: sorted, filled, naming children of l or r
      have hsortD : CvSorted ((mergeList (!xn.leaf) cR ln.live rn.live).drop
          (((mergeList (!xn.leaf) cR ln.live rn.live).length + 1) / 2)) :=
        hsortE.sublist (List.drop_sublist _ _)
      have hS1 : CvSorted first := by rw [hE1]; exact hsortE.sublist (List.take_sublist _ _)
      have hS2 : CvSorted ks2 := by
        rw [hE2]
        generalize hb : (!xn.leaf) = b at hsortD hgs ⊢
        cases b with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact hsortD
        | true =>
          simp only [↓reduceIte]
          apply renameHead_sorted 0 _ hsortD
          intro q hq
          cases hd : (mergeList true cR ln.live rn.live).drop
              (((mergeList true cR ln.live rn.live).length + 1) / 2) with
          | nil => rw [hd] at hq; simp at hq
          | cons a tl =>
            rw [hd] at hq hgs hsortD
            simp only [List.head?_cons, Option.some.injEq] at hgs
            subst hgs
            simp only [List.tail_cons] at hq
            have := (List.pairwise_cons.mp hsortD).1 q hq
            simp at this; omega
      have hlen1 : first.length = ((mergeList (!xn.leaf) cR ln.live rn.live).length + 1) / 2 := by
        rw [hE1, List.length_take]; omega
      have hlen2 : ks2.length = (mergeList (!xn.leaf) cR ln.live rn.live).length -
          ((mergeList (!xn.leaf) cR ln.live rn.live).length + 1) / 2 := by
        rw [hE2]
        split <;> simp [renameHead_length, List.length_drop]
      have hmb2 := hMP.2.1
      obtain ⟨hmne1, hmfill1⟩ := hnewFill first hS1 (by omega)
      obtain ⟨hmne2, hmfill2⟩ := hnewFill ks2 hS2 (by omega)
      have hsnd := splitMerged_map_snd (!xn.leaf) c.p.mergeMax _ first ks2 g2 hmkd
      have hsrc1 : ∀ z, z ∈ first.map Prod.snd →
          z ∈ (mergeList (!xn.leaf) cR ln.live rn.live).map Prod.snd := by
        intro z hz; rw [← hsnd, List.map_append]; exact List.mem_append_left _ hz
      have hsrc2 : ∀ z, z ∈ ks2.map Prod.snd →
          z ∈ (mergeList (!xn.leaf) cR ln.live rn.live).map Prod.snd := by
        intro z hz; rw [← hsnd, List.map_append]; exact List.mem_append_right _ hz
      simp only [writerWP_bind, writerWP_pure]
      refine writerWP_mono (writerWP_newKey_frame _ _ _ _ c _) ?_
      intro m2 w7 ⟨hm2, h7n, h7t, h7top, h7next, h7v, h7p, h7m⟩
      try simp only [writerWP_bind, writerWP_pure, writerWP_get]
      refine writerWP_mono (writerWP_setMadeFor_frame _ _ c _) ?_
      intro _ w8 ⟨h8n, h8t, h8top, h8next, h8v, h8p⟩
      try simp only [writerWP_pure]
      have hm2' : m2 = m1 + 2 := by rw [hm2, h6next']
      subst hm2'
      have hw8p : w8.nodes.lookup p = some pn := by
        rw [h8n, h7n, lookup_append_single_ne _ _ _ _ (by omega), hw6p]
      have hw8m1 : w8.nodes.lookup m1 = some ⟨!!xn.leaf, newKlongs c.i first⟩ := by
        rw [h8n, h7n, lookup_append_single_ne _ _ _ _ (by omega), hw6m1]
      have hw8m2 : w8.nodes.lookup (m1 + 2) = some ⟨!!xn.leaf, newKlongs c.i ks2⟩ := by
        rw [h8n, h7n, h6next', lookup_append_single_self]
        rw [h6old _ (by omega) (by omega)]
        exact hnone3 _ (by omega)
      have h8old : ∀ y, y ≠ x → y ≠ m1 → y ≠ m1 + 2 → w8.nodes.lookup y = w3.nodes.lookup y := by
        intro y hyx hym hym2
        rw [h8n, h7n, h6next', lookup_append_single_ne _ _ _ _ hym2, h6old y hyx hym]
      have h8taken : w8.taken = w3.taken := by rw [h8t, h7t, h6taken]
      have hm2T : w3.taken.contains (m1 + 2) = false := (hfree (m1 + 2) (by omega)).2
      have hm2N : N (m1 + 2) = none := (hfree (m1 + 2) (by omega)).1
      have hm2R : ¬ TReach N c.i root (m1 + 2) :=
        not_reach_fresh N c.i root (m1 + 2) hT hm2N (hfreshT (m1 + 2) (by omega))
      have hlm2 : l ≠ m1 + 2 := by omega
      have hrm2 : r ≠ m1 + 2 := by omega
      have hpm2 : p ≠ m1 + 2 := by omega
      refine writerWP_mergeParent_roomB p pn (d - 1) il cL m1 ir cR (some (m1 + 2, g2)) c w8 _ hw8p
        (by rw [hsec] at hB'; exact hB') ?_
      intro s9
      generalize hw9 : ({ ({ w8 with trail := s9 :: w8.trail } : W) with
        nodes := upsert w8.nodes p (mergeParentNode pn c.i il cL m1 ir cR (some (m1 + 2, g2))) } : W) = w9
      have h9n : w9.nodes = upsert w8.nodes p
          (mergeParentNode pn c.i il cL m1 ir cR (some (m1 + 2, g2))) := by rw [← hw9]
      have h9t : w9.taken = w8.taken := by rw [← hw9]
      have h9top : w9.top = w8.top := by rw [← hw9]
      have hlk9 : w9.nodes.lookup p =
          some (mergeParentNode pn c.i il cL m1 ir cR (some (m1 + 2, g2))) := by
        rw [h9n, lookup_upsert]; simp
      have hlk2 : ∀ cc, (mergeParentNode pn c.i il cL m1 ir cR (some (m1 + 2, g2))).live.lookup cc =
          if cc = g2 then some (m1 + 2) else if cc = cL then some m1
            else if cc = cR then none else pn.live.lookup cc := by
        intro cc
        rw [mergeParentNode_eq, mpNode_live_lookup pn c.i il cL m1 ir cR (some (m1 + 2, g2)) _ _ _ l r
          hpwf hL hLL hR hRL hc ?htd ?hrip cc]
        case htd => exact htd_last pn _
        case hrip =>
          intro hrip y g hm
          cases hm
          simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, bne_eq_false_iff_eq]
            at hrip
          exact hrip.1.1
      have hmpT2 := hmpT il cL m1 ir cR (some (m1 + 2, g2))
      have hchar2 : ∀ cc z, (cc, z) ∈
          (mergeParentNode pn c.i il cL m1 ir cR (some (m1 + 2, g2))).liveAt c.i →
          z = m1 ∨ z = m1 + 2 ∨ ((cc, z) ∈ pn.liveAt c.i ∧ cc ≠ cL ∧ cc ≠ cR) := by
        intro cc z hmem
        rw [KNode.liveAt_of_times _ c.i hmpT2] at hmem
        have hlk := lookup_of_mem_nodup _ (KNode.live_keys_nodup _) cc z hmem
        rw [hlk2 cc] at hlk
        by_cases h0 : cc = g2
        · rw [if_pos h0] at hlk
          exact Or.inr (Or.inl (Option.some.inj hlk).symm)
        · by_cases h1 : cc = cL
          · rw [if_neg h0, if_pos h1] at hlk
            exact Or.inl (Option.some.inj hlk).symm
          · by_cases h2 : cc = cR
            · rw [if_neg h0, if_neg h1, if_pos h2] at hlk; cases hlk
            · rw [if_neg h0, if_neg h1, if_neg h2] at hlk
              right; right
              refine ⟨?_, h1, h2⟩
              rw [KNode.liveAt_of_times pn c.i hpt]
              exact bk_mem_of_lookup _ cc z hlk
      have hlen9 : pn.live.length ≤
          (mergeParentNode pn c.i il cL m1 ir cR (some (m1 + 2, g2))).live.length :=
        live_len_mergeTwo pn _ cL cR g2 m1 (m1 + 2) hlk2 (by omega)
          ⟨r, by rw [KNode.live_lookup]; exact keyLookup_of_last _ _ _ ir r hR hRL⟩ hg2
      refine writerWP_mono (writerWP_mergeCleanup_frameV p m1 c.i c _ w9 _ hne' hlk9
        (fun q hq c' hmem => by
          rcases hchar2 c' q.1 hmem with h | h | ⟨hold, h1, h2⟩
          · rcases hlr' q hq with h' | h' <;> rw [h'] at h
            · exact hlm1 h
            · exact hrm1 h
          · rcases hlr' q hq with h' | h' <;> rw [h'] at h
            · exact hlm2 h
            · exact hrm2 h
          · exact hnoOld q.1 (hlr' q hq) c' hold h1 h2)) ?_
      intro _ w10 ⟨h10top0, _, _, h10t, h10l, pn10, h10p, h10leaf, h10times, h10iff⟩
      refine ⟨fun h => absurd h (by simp), fun _ => ?_⟩
      have h10tc : ∀ y, y ≠ l → y ≠ r → w10.taken.contains y = w3.taken.contains y := by
        intro y hyl hyr; rw [h10t y (hcl' y hyl hyr), h9t, h8taken]
      have h10l' : ∀ y, y ≠ p → y ≠ l → y ≠ r → w10.nodes.lookup y = w8.nodes.lookup y := by
        intro y hyp hyl hyr; rw [h10l y hyp (hcl' y hyl hyr), h9n, lookup_upsert]; simp [hyp]
      have h10top : w10.top.rootKey = root := by
        rw [h10top0, h9top, h8top, h7top, h6top']
      rw [h10top]
      have hpn10T := h10times hmpT2
      have hlen10 : (pn.liveAt c.i).length ≤ (pn10.liveAt c.i).length := by
        rw [KNode.liveAt_of_times pn c.i hpt, KNode.liveAt_of_times pn10 c.i hpn10T]
        refine Nat.le_trans hlen9 (length_le_of_nodup_sub _ _
          (nodup_of_keys_nodup _ (KNode.live_keys_nodup _)) (fun q hq => ?_))
        have hq' : (q.1, q.2) ∈ pn10.liveAt c.i :=
          (h10iff q.1 q.2).mpr (by rw [KNode.liveAt_of_times _ c.i hmpT2]; exact hq)
        rw [KNode.liveAt_of_times pn10 c.i hpn10T] at hq'
        exact hq'
      refine liveEdges_mergeTwo c.p N (wNode c.p base w10) c.i root p l r m1 (m1 + 2) pn ln rn pn10
        ⟨!!xn.leaf, newKlongs c.i first⟩ ⟨!!xn.leaf, newKlongs c.i ks2⟩ cL cR Hl hT hp hpn hpleaf
        hpL hpR hln hrn hm1R hm2R ?_ ?_ ?_
        (by show (!!xn.leaf) = ln.leaf; rw [hll, Bool.not_not])
        (by show (!!xn.leaf) = ln.leaf; rw [hll, Bool.not_not]) (by rw [hrl, hll])
        ⟨hmne1, hmne2⟩ ⟨hmfill1, hmfill2⟩ ?_ (by rw [h10leaf, mrg_mergeParentNode_leaf])
        (fun cc z hmem => hchar2 cc z ((h10iff cc z).mp hmem)) hlen10 ?_
        (fun y hy => by
          have hyx := hHl y hy
          rcases hxlr with h | h
          · exact Or.inl (hyx.trans h)
          · exact Or.inr (hyx.trans h))
        hLive
      · simp only [wNode, h10tc m1 (Ne.symm hlm1) (Ne.symm hrm1), hm1T, Bool.false_eq_true,
          ↓reduceIte]
        rw [h10l' m1 (Ne.symm hpm1) (Ne.symm hlm1) (Ne.symm hrm1), hw8m1]
      · simp only [wNode, h10tc (m1 + 2) (Ne.symm hlm2) (Ne.symm hrm2), hm2T, Bool.false_eq_true,
          ↓reduceIte]
        rw [h10l' (m1 + 2) (Ne.symm hpm2) (Ne.symm hlm2) (Ne.symm hrm2), hw8m2]
      · intro mn hmn cc z hmem
        rcases hmn with h | h <;> subst h
        · exact hnewSrc first hsrc1 cc z hmem
        · exact hnewSrc ks2 hsrc2 cc z hmem
      · simp only [wNode, h10tc p hpl hpr, hpT, Bool.false_eq_true, ↓reduceIte, h10p]
      · intro y hyp hyl hyr hym hym2
        rw [← hNw3 y]
        unfold wNode
        rw [h10tc y hyl hyr, h10l' y hyp hyl hyr,
          h8old y (by rcases hxlr with h | h <;> rw [h] <;> assumption) hym hym2]

/-- A merge with the parent with room and no compaction, of nodes the
transaction made or not: into one node it keeps the hole's form with the parent
the hole after, and the nodes but the parent, the two merged and the new one
keep their lookups; into two nodes it leaves no hole. -/
theorem writerWP_mergeTail_liveRoom (c : Ctx) (base : View BVal) (x : NodeId) (d : Nat) (p : NodeId)
    (pn xn : KNode) (leftSome : Bool) (l : NodeId) (ln : KNode) (il : Nat) (r : NodeId)
    (rn : KNode) (ir : Nat) (cL cR : Nat) (N : NodeId → Option KNode) (root : NodeId) (nx : Nat)
    (w3 : W) (Hl : NodeId → Prop) (hm : c.p.merges = true) (hMP : MergeParamsOK c.p)
    (hT : TreeOK N c.i root) (hp : TReach N c.i root p) (hpn : N p = some pn)
    (hL : pn.ks[il]? = some (.key cL l)) (hLL : LastLive pn.ks pn.lastBitmap il cL)
    (hR : pn.ks[ir]? = some (.key cR r)) (hRL : LastLive pn.ks pn.lastBitmap ir cR)
    (hclt : cL < cR) (hadj : ∀ cc z, (cc, z) ∈ pn.liveAt c.i → cc ≤ cL ∨ cR ≤ cc)
    (hxlr : x = l ∨ x = r) (hln : N l = some ln) (hrn : N r = some rn)
    (hpwf : klongsWf pn.ks = true) (hpt : ∀ s, Klong.time s ∈ pn.ks → s ≤ c.i)
    (hch : ∀ cc z zn, (cc, z) ∈ pn.liveAt c.i → N z = some zn →
      ∀ s, Klong.time s ∈ zn.ks → s ≤ c.i)
    (hN3 : wNode c.p base w3 = N) (h3top : w3.top.rootKey = root) (h3next : w3.next = nx)
    (h3p : w3.nodes.lookup p = some pn) (h3src : ∀ z, (w3.nodes.lookup z).isSome = true → z < nx)
    (hfree : ∀ z, nx ≤ z → N z = none ∧ w3.taken.contains z = false)
    (hfreshT : ∀ z, nx ≤ z → ∀ u c', TReach N c.i root u → ¬ TLink N c.i u c' z)
    (hpleaf : pn.leaf = false) (hll : ln.leaf = xn.leaf) (hrl : rn.leaf = xn.leaf)
    (hlrange : ∀ cc z, (cc, z) ∈ ln.liveAt c.i → cc < cR)
    (hllow : ∀ cc z, (cc, z) ∈ ln.liveAt c.i →
      ((!xn.leaf) = true → cc = 0 ∨ cL < cc) ∧ ((!xn.leaf) = false → cL ≤ cc))
    (hrrange : ∀ cc z, (cc, z) ∈ rn.liveAt c.i →
      ((!xn.leaf) = true → cc = 0 ∨ cR < cc) ∧ ((!xn.leaf) = false → cR ≤ cc))
    (hrup : ∀ k z, (k, z) ∈ pn.liveAt c.i → cR < k → ∀ cc z', (cc, z') ∈ rn.liveAt c.i → cc < k)
    (hroom : pn.size + 4 ≤ c.p.M)
    (hnd : ∀ il cL m1 ir cR m2, deadOver c.p (mergeParentNode pn c.i il cL m1 ir cR m2) = false)
    (hLive : LiveEdgesH c.p N c.i root Hl) (hHl : ∀ y, Hl y → y = x) :
    WriterWP (mergeTail c x d p pn xn leftSome l ln il r rn ir) c w3
      (fun res w' => (res = 1 →
        LiveEdgesH c.p (wNode c.p base w') c.i w'.top.rootKey (fun y => y = p) ∧
        (∀ y, y ≠ p → y ≠ l → y ≠ r → y ≠ nx → w'.nodes.lookup y = w3.nodes.lookup y) ∧
        w'.top = w3.top) ∧
        (res ≠ 1 → LiveEdges c.p (wNode c.p base w') c.i w'.top.rootKey)) :=
  writerWP_mergeTail_liveRoomB c base x d p pn xn leftSome l ln il r rn ir cL cR N root nx w3 Hl hm
    hMP hT hp hpn hL hLL hR hRL hclt hadj hxlr hln hrn hpwf hpt hch hN3 h3top h3next h3p h3src hfree
    hfreshT hpleaf hll hrl hlrange hllow hrrange hrup
    (mergeParentRoom_of_room c pn hroom hnd _ _ _ _ _ _) hLive hHl

set_option maxHeartbeats 8000000 in
/-- The tail of a merge of the loop from a state w3 that reads as w, the
merge's start, its parent p on the key access path taking `mergeParent`'s branch
with room (bergdb 030-01, step 3): into one node it keeps the hole's form with p
the hole after, and reads every node outside p's children, p and the new node
as at w; into two nodes it leaves no hole. -/
theorem writerWP_mergeTail_liveRoomR (base : View BVal) (x : NodeId) (d : Nat) (c : Ctx) (w : W)
    (hm : c.p.merges = true) (hMP : MergeParamsOK c.p)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hR : RangeOrder (wNode c.p base w) c.i w.top.rootKey) (p : NodeId) (pn : KNode)
    (hpR : TReach (wNode c.p base w) c.i w.top.rootKey p) (hpn : wNode c.p base w p = some pn)
    (hpleaf : pn.leaf = false) (hpwf : klongsWf pn.ks = true)
    (hpt : ∀ s, Klong.time s ∈ pn.ks → s ≤ c.i)
    (hch : ∀ cc z zn, (cc, z) ∈ pn.liveAt c.i → wNode c.p base w z = some zn →
      ∀ s, Klong.time s ∈ zn.ks → s ≤ c.i)
    (hidn : ∀ z, (w.nodes.lookup z).isSome = true → z < w.next)
    (hidv : ∀ z, (c.view z).isSome = true → z < w.next)
    (hfree : ∀ z, w.next ≤ z → wNode c.p base w z = none ∧ w.taken.contains z = false)
    (hfreshT : ∀ z, w.next ≤ z → ∀ u c', TReach (wNode c.p base w) c.i w.top.rootKey u →
      ¬ TLink (wNode c.p base w) c.i u c' z)
    (Hl : NodeId → Prop) (hLive : LiveEdgesH c.p (wNode c.p base w) c.i w.top.rootKey Hl)
    (hHl : ∀ y, Hl y → y = x)
    (leftSome : Bool) (l : NodeId) (ln : KNode) (il : Nat) (r : NodeId) (rn : KNode)
    (ir cL cR : Nat) (xn : KNode) (w3 : W) (hr3 : ReadsAs c.p base w w3)
    (h3p : w3.nodes.lookup p = some pn) (hk3 : ObsKept c w w3)
    (hsrc3 : ∀ z, (w3.nodes.lookup z).isSome = true → (w.nodes.lookup z).isSome = true ∨
      (c.view z).isSome = true)
    (hL : pn.ks[il]? = some (.key cL l)) (hLL : LastLive pn.ks pn.lastBitmap il cL)
    (hR' : pn.ks[ir]? = some (.key cR r)) (hRL : LastLive pn.ks pn.lastBitmap ir cR)
    (hclt : cL < cR) (hadj : ∀ cc z, (cc, z) ∈ pn.liveAt c.i → cc ≤ cL ∨ cR ≤ cc)
    (hll : ln.leaf = xn.leaf) (hrl : rn.leaf = xn.leaf) (hxlr : x = l ∨ x = r)
    (hln : wNode c.p base w l = some ln) (hrn : wNode c.p base w r = some rn)
    (hB : MergeParentRoom c pn il cL w.next ir cR (mergeM2 c xn ln rn cR w.next)) :
    WriterWP (mergeTail c x d p pn xn leftSome l ln il r rn ir) c w3
      (fun res w' => (res = 1 →
        LiveEdgesH c.p (wNode c.p base w') c.i w'.top.rootKey (fun y => y = p) ∧
        (∀ y, y ≠ p → (∀ cc, (cc, y) ∉ pn.liveAt c.i) → y ≠ w.next → rdN c w' y = rdN c w y) ∧
        w'.top = w.top) ∧ (res ≠ 1 → LiveEdges c.p (wNode c.p base w') c.i w'.top.rootKey)) := by
  have hpRS := tReach_reachS _ c.i _ _ hpR
  have hmemL : (cL, l) ∈ pn.liveAt c.i := by
    rw [KNode.liveAt_of_times pn c.i hpt]
    apply bk_mem_of_lookup
    rw [KNode.live_lookup]
    exact keyLookup_of_last _ _ _ il l hL hLL
  have hmemR : (cR, r) ∈ pn.liveAt c.i := by
    rw [KNode.liveAt_of_times pn c.i hpt]
    apply bk_mem_of_lookup
    rw [KNode.live_lookup]
    exact keyLookup_of_last _ _ _ ir r hR' hRL
  obtain ⟨hlr1, hlr2⟩ := mrg_child_range (wNode c.p base w) c.i w.top.rootKey hR p pn hpRS hpn
    hpleaf cL l ln hmemL hln
  obtain ⟨hrr1, hrr2⟩ := mrg_child_range (wNode c.p base w) c.i w.top.rootKey hR p pn hpRS hpn
    hpleaf cR r rn hmemR hrn
  have hN3 : wNode c.p base w3 = wNode c.p base w := hr3.1
  refine writerWP_mono (writerWP_mergeTail_liveRoomB c base x d p pn xn leftSome l ln il r rn ir
    cL cR (wNode c.p base w) w.top.rootKey w.next w3 Hl hm hMP hT hpR hpn hL hLL hR' hRL hclt hadj
    hxlr hln hrn hpwf hpt hch hN3 (by rw [hr3.2.1]) hr3.2.2.2.2 h3p
    (fun z hz => by
      rcases hsrc3 z hz with h | h
      · exact hidn z h
      · exact hidv z h)
    (fun z hz => ⟨(hfree z hz).1, by rw [hr3.2.2.1]; exact (hfree z hz).2⟩)
    hfreshT hpleaf hll hrl
    (fun cc z h => hlr2 cR r hmemR hclt cc z h)
    (by
      intro cc z h
      have h1 := hlr1 cc z h
      rw [hll] at h1
      constructor
      · intro hin
        have hxl : xn.leaf = false := by simpa using hin
        rcases (h1.2 hxl) with h0 | h0
        · exact Or.inl h0
        · rcases Nat.eq_zero_or_pos cL with hc0 | hc0
          · rcases Nat.eq_zero_or_pos cc with hcc | hcc
            · exact Or.inl hcc
            · exact Or.inr (by omega)
          · exact Or.inr (h0 hc0)
      · intro hin
        have hxl : xn.leaf = true := by simpa using hin
        rcases Nat.eq_zero_or_pos cL with hc0 | hc0
        · omega
        · exact h1.1 hxl hc0)
    (by
      intro cc z h
      have h1 := hrr1 cc z h
      rw [hrl] at h1
      constructor
      · intro hin
        have hxl : xn.leaf = false := by simpa using hin
        rcases (h1.2 hxl) with h0 | h0
        · exact Or.inl h0
        · exact Or.inr (h0 (by omega))
      · intro hin
        have hxl : xn.leaf = true := by simpa using hin
        exact h1.1 hxl (by omega))
    (fun k z hk hkc cc z' h => hrr2 k z hk hkc cc z' h) hB hLive hHl) ?_
  rintro res w' ⟨hpost, hpost2⟩
  refine ⟨fun hres => ?_, hpost2⟩
  obtain ⟨hL', hfr, htop⟩ := hpost hres
  refine ⟨hL', fun y hyp hych hyn => ?_, by rw [htop, hr3.2.1]⟩
  have hyl : y ≠ l := fun h => hych cL (by rw [h]; exact hmemL)
  have hyr : y ≠ r := fun h => hych cR (by rw [h]; exact hmemR)
  have hlk := hfr y hyp hyl hyr hyn
  have : rdN c w' y = rdN c w3 y := by simp only [rdN, hlk]
  rw [this, hk3.1]

set_option maxHeartbeats 8000000 in
/-- A merge of the loop from w, its parent p on the key access path, up to its
tail (bergdb 030-01, step 3): the merge reads p, x and a sibling, and hands
`mergeTail` the two nodes it chose, with their facts; what every such tail ends
with, the merge ends with. -/
theorem writerWP_merge_liveG (base : View BVal) (x : NodeId) (d : Nat) (c : Ctx) (w : W)
    (hvc : ViewCoherent c base) (p : NodeId) (pn : KNode)
    (hpath : (w.path[d - 1]?).map (·.2) = some p)
    (hpR : TReach (wNode c.p base w) c.i w.top.rootKey p) (hpn : wNode c.p base w p = some pn)
    (hpt : ∀ s, Klong.time s ∈ pn.ks → s ≤ c.i)
    (hRt : ∀ y, TReach (wNode c.p base w) c.i w.top.rootKey y → w.taken.contains y = false)
    (Q : Nat → W → Prop)
    (htail : ∀ (leftSome : Bool) (l : NodeId) (ln : KNode) (il : Nat) (r : NodeId)
        (rn : KNode) (ir cL cR : Nat) (xn : KNode) (w3 : W), ReadsAs c.p base w w3 →
        w3.nodes.lookup p = some pn → ObsKept c w w3 →
        (∀ z, (w3.nodes.lookup z).isSome = true → (w.nodes.lookup z).isSome = true ∨
          (c.view z).isSome = true) →
        pn.ks[il]? = some (.key cL l) → LastLive pn.ks pn.lastBitmap il cL →
        pn.ks[ir]? = some (.key cR r) → LastLive pn.ks pn.lastBitmap ir cR → cL < cR →
        (∀ cc z, (cc, z) ∈ pn.liveAt c.i → cc ≤ cL ∨ cR ≤ cc) →
        ln.leaf = xn.leaf → rn.leaf = xn.leaf → wNode c.p base w x = some xn →
        (x = l ∨ x = r) → wNode c.p base w l = some ln → wNode c.p base w r = some rn →
        w.nodes <+: w3.nodes → w3.path = w.path →
        WriterWP (mergeTail c x d p pn xn leftSome l ln il r rn ir) c w3 Q) :
    WriterWP (merge x d) c w Q := by
  unfold merge
  simp only [writerWP_bind, writerWP_read]
  unfold pathNode
  simp only [writerWP_bind, writerWP_get]
  split
  · rename_i e he
    simp only [writerWP_pure]
    have hep : e.2 = p := by rw [he] at hpath; simpa using hpath
    subst hep
    refine writerWP_mono (writerWP_and (writerWP_getNode_all e.2 c w base hvc)
      (writerWP_getNode_rd e.2 c w)) ?_
    intro pn' w1 ⟨⟨hr1, hlk1, hwn1, hpre1, hsrc1⟩, _, hk1, hpath1, _⟩
    rw [hwn1 (hRt _ hpR)] at hpn
    cases hpn
    have hpn : wNode c.p base w e.2 = some pn := hwn1 (hRt _ hpR)
    have hptrk : ∀ i cv y, LastLive pn.ks pn.lastBitmap i cv → pn.ptr? i = some y →
        pn.ks[i]? = some (.key cv y) := by
      intro i cv y hl hy
      obtain ⟨⟨y0, hy0⟩, _, _⟩ := hl
      simp only [KNode.ptr?, hy0, Option.some.injEq] at hy
      rw [hy0, hy]
    have hchild : ∀ i cv y, pn.ks[i]? = some (.key cv y) → LastLive pn.ks pn.lastBitmap i cv →
        (cv, y) ∈ pn.liveAt c.i ∧ TReach (wNode c.p base w) c.i w.top.rootKey y := by
      intro i cv y hk hl
      have hm : (cv, y) ∈ pn.liveAt c.i := by
        rw [KNode.liveAt_of_times pn c.i hpt]
        apply bk_mem_of_lookup
        rw [KNode.live_lookup]
        exact keyLookup_of_last _ _ _ i y hk hl
      exact ⟨hm, TReach.link hpR ⟨pn, hpn, hm⟩⟩
    refine writerWP_mono (writerWP_and (writerWP_getNode_all x c w1 base hvc)
      (writerWP_getNode_rd x c w1)) ?_
    intro xn w2 ⟨⟨hr2, _, hwn2, hpre2, hsrc2⟩, _, hk2, hpath2, _⟩
    have hr02 := ReadsAs.trans _ _ _ _ _ hr1 hr2
    have hk02 := hk1.trans hk2
    have hsrc02 : ∀ z, (w2.nodes.lookup z).isSome = true → (w.nodes.lookup z).isSome = true ∨
        (c.view z).isSome = true := by
      intro z hz
      rcases hsrc2 z hz with h | h
      · exact hsrc1 z h
      · exact Or.inr h
    unfold klongAt
    simp only [writerWP_bind, writerWP_get]
    split
    · rename_i cx _ hcx
      simp only [writerWP_pure]
      generalize hmi : mergeIdx pn cx = mi
      obtain ⟨ixo, ia, ib⟩ := mi
      have hML := mergeIdx_last pn cx
      rw [hmi] at hML
      obtain ⟨hMx, hMa, hMb⟩ := hML
      split
      · rename_i ix hix
        simp only [writerWP_bind, writerWP_pure]
        have hLx := hMx ix hix
        refine writerWP_if _ _ _ _ _ _ (fun _ => ?_) (fun hptr => ?_)
        · simp only [writerWP_bind]; exact writerWP_throw _ _ _ _
        have hpx : pn.ptr? ix = some x := by simpa using hptr
        have hkx := hptrk ix cx x hLx hpx
        obtain ⟨_, hxR⟩ := hchild ix cx x hkx hLx
        have hxn : wNode c.p base w x = some xn := by
          rw [← hr1.1]; exact hwn2 (by rw [hr1.2.2.1]; exact hRt x hxR)
        -- a sibling read
        have hsib : ∀ (wb : W) (i cv : Nat) (sn : NodeId × KNode) (w3 : W),
            ReadsAs c.p base w wb → w1.nodes <+: wb.nodes →
            LastLive pn.ks pn.lastBitmap i cv →
            pn.ptr? i = some sn.1 → ReadsAs c.p base wb w3 → wb.nodes <+: w3.nodes →
            (wb.taken.contains sn.1 = false → wNode c.p base wb sn.1 = some sn.2) →
            pn.ks[i]? = some (.key cv sn.1) ∧ wNode c.p base w sn.1 = some sn.2 ∧
              ReadsAs c.p base w w3 ∧ w1.nodes <+: w3.nodes := by
          intro wb i cv sn w3 hrb hpreb hl hp hr3 hpre3 hwn3
          have hk := hptrk i cv sn.1 hl hp
          obtain ⟨_, hsR⟩ := hchild i cv sn.1 hk hl
          refine ⟨hk, ?_, ReadsAs.trans _ _ _ _ _ hrb hr3, hpreb.trans hpre3⟩
          rw [← hrb.1]; exact hwn3 (by rw [hrb.2.2.1]; exact hRt _ hsR)
        have hright : ∀ (wb : W) (ia0 cva : Nat), ReadsAs c.p base w wb → w1.nodes <+: wb.nodes →
            ObsKept c w wb →
            (∀ z, (wb.nodes.lookup z).isSome = true → (w.nodes.lookup z).isSome = true ∨
              (c.view z).isSome = true) →
            LastLive pn.ks pn.lastBitmap ia0 cva → cx < cva →
            (mergeIdx pn cx).2.1 = some (ia0, cva) → wb.path = w.path →
            WriterWP (do
              let __x ← sibling e.2 pn ia0 !xn.leaf
              mergeTail c x d e.2 pn xn false x xn ix __x.1 __x.2 ia0) c wb Q := by
          intro wb ia0 cva hrb hpreb hkb hsrcb hLa hax hia hpb
          rw [writerWP_bind]
          refine writerWP_mono (writerWP_and (writerWP_and
            (writerWP_sibling_leaf e.2 pn ia0 (!xn.leaf) c wb base hvc)
            (writerWP_sibling_rd e.2 pn ia0 (!xn.leaf) c wb))
            (writerWP_sibling_path e.2 pn ia0 (!xn.leaf) c wb)) ?_
          rintro ⟨rs, rsn⟩ w4 ⟨⟨⟨hs1, hr4, _, hwn4, hpre4, hsrc4, hsl⟩, hk4⟩, hpath4⟩
          obtain ⟨hka, hrn, hr04, hpre14⟩ :=
            hsib wb ia0 cva (rs, rsn) w4 hrb hpreb hLa hs1 hr4 hpre4 hwn4
          exact htail false x xn ix rs rsn ia0 cx cva xn w4 hr04
            (lookup_of_prefix _ _ hpre14 _ _ hlk1) (hkb.trans hk4)
            (fun z hz => by
              rcases hsrc4 z hz with h | h
              · exact hsrcb z h
              · exact Or.inr h)
            hkx hLx hka hLa hax (by
              have hmin := mergeIdx_right_min pn cx ia0 cva hia
              intro cc z hm
              rcases Nat.lt_or_ge cx cc with h | h
              · have hm' : (cc, z) ∈ pn.live := by rw [← KNode.liveAt_of_times pn c.i hpt]; exact hm
                exact Or.inr (hmin cc z hm' h)
              · exact Or.inl h) rfl (by rw [hsl]; simp) hxn (Or.inl rfl) hxn hrn
                (hpre1.trans hpre14) (hpath4.trans hpb)
        split
        · rename_i ib0 cvb
          obtain ⟨hLb, hbx⟩ := hMb ib0 cvb rfl
          simp only [writerWP_bind]
          refine writerWP_mono (writerWP_and (writerWP_and
            (writerWP_sibling_leaf e.2 pn ib0 (!xn.leaf) c w2 base hvc)
            (writerWP_sibling_rd e.2 pn ib0 (!xn.leaf) c w2))
            (writerWP_sibling_path e.2 pn ib0 (!xn.leaf) c w2)) ?_
          rintro ⟨ls, lsn⟩ w3 ⟨⟨⟨hs1, hr3, _, hwn3, hpre3, hsrc3, hsl⟩, hk3⟩, hpath3⟩
          obtain ⟨hkb, hln, hr03, hpre13⟩ :=
            hsib w2 ib0 cvb (ls, lsn) w3 hr02 hpre2 hLb hs1 hr3 hpre3 hwn3
          have hsrc03 : ∀ z, (w3.nodes.lookup z).isSome = true → (w.nodes.lookup z).isSome = true ∨
              (c.view z).isSome = true := by
            intro z hz
            rcases hsrc3 z hz with h | h
            · exact hsrc02 z h
            · exact Or.inr h
          refine writerWP_if _ _ _ _ _ _ (fun _ => ?_) (fun _ => ?_)
          · show WriterWP (mergeTail c x d e.2 pn xn true ls lsn ib0 x xn ix) c w3 _
            exact htail true ls lsn ib0 x xn ix cvb cx xn w3 hr03
              (lookup_of_prefix _ _ hpre13 _ _ hlk1) (hk02.trans hk3) hsrc03
              hkb hLb hkx hLx hbx (by
                have hmax := mergeIdx_left_max pn cx ib0 cvb (by rw [hmi])
                intro cc z hm
                rcases Nat.lt_or_ge cc cx with h | h
                · have hm' : (cc, z) ∈ pn.live := by rw [← KNode.liveAt_of_times pn c.i hpt]; exact hm
                  exact Or.inl (hmax cc z hm' h)
                · exact Or.inr h) (by rw [hsl]; simp) rfl hxn (Or.inr rfl) hln hxn
                (hpre1.trans hpre13) (hpath3.trans (hpath2.trans hpath1))
          · rw [writerWP_bind, writerWP_pure]
            dsimp only
            split
            · rename_i ia0 cva _
              obtain ⟨hLa, hax⟩ := hMa ia0 cva rfl
              exact hright w3 ia0 cva hr03 hpre13 (hk02.trans hk3) hsrc03 hLa hax (by rw [hmi])
                (hpath3.trans (hpath2.trans hpath1))
            · exact writerWP_throw _ _ _ _
        · rw [writerWP_bind, writerWP_pure]
          dsimp only
          split
          · rename_i ia0 cva
            obtain ⟨hLa, hax⟩ := hMa ia0 cva rfl
            exact hright w2 ia0 cva hr02 hpre2 hk02 hsrc02 hLa hax (by rw [hmi])
              (hpath2.trans hpath1)
          · exact writerWP_throw _ _ _ _
      · exact writerWP_throw _ _ _ _
    · exact writerWP_throw _ _ _ _
  · exact writerWP_throw _ _ _ _


/-- A merge of the loop, its parent p on the key access path with room and no
compaction (bergdb 030-01, step 3): into one node it keeps the hole's form with
p the hole after, and reads every node outside p's children, p and the new node
as before; into two nodes it leaves no hole. -/
theorem writerWP_merge_liveRoom (base : View BVal) (x : NodeId) (d : Nat) (c : Ctx) (w : W)
    (hvc : ViewCoherent c base) (hm : c.p.merges = true) (hMP : MergeParamsOK c.p)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hR : RangeOrder (wNode c.p base w) c.i w.top.rootKey)
    (p : NodeId) (pn : KNode) (hpath : (w.path[d - 1]?).map (·.2) = some p)
    (hpR : TReach (wNode c.p base w) c.i w.top.rootKey p) (hpn : wNode c.p base w p = some pn)
    (hpleaf : pn.leaf = false) (hpwf : klongsWf pn.ks = true)
    (hpt : ∀ s, Klong.time s ∈ pn.ks → s ≤ c.i)
    (hch : ∀ cc z zn, (cc, z) ∈ pn.liveAt c.i → wNode c.p base w z = some zn →
      ∀ s, Klong.time s ∈ zn.ks → s ≤ c.i)
    (hRt : ∀ y, TReach (wNode c.p base w) c.i w.top.rootKey y → w.taken.contains y = false)
    (hidn : ∀ z, (w.nodes.lookup z).isSome = true → z < w.next)
    (hidv : ∀ z, (c.view z).isSome = true → z < w.next)
    (hfree : ∀ z, w.next ≤ z → wNode c.p base w z = none ∧ w.taken.contains z = false)
    (hfreshT : ∀ z, w.next ≤ z → ∀ u c', TReach (wNode c.p base w) c.i w.top.rootKey u →
      ¬ TLink (wNode c.p base w) c.i u c' z)
    (Hl : NodeId → Prop) (hLive : LiveEdgesH c.p (wNode c.p base w) c.i w.top.rootKey Hl)
    (hHl : ∀ y, Hl y → y = x)
    (hroom : pn.size + 4 ≤ c.p.M)
    (hnd : ∀ il cL m1 ir cR m2, deadOver c.p (mergeParentNode pn c.i il cL m1 ir cR m2) = false) :
    WriterWP (merge x d) c w (fun res w' => (res = 1 →
      LiveEdgesH c.p (wNode c.p base w') c.i w'.top.rootKey (fun y => y = p) ∧
      (∀ y, y ≠ p → (∀ cc, (cc, y) ∉ pn.liveAt c.i) → y ≠ w.next → rdN c w' y = rdN c w y) ∧
      w'.top = w.top) ∧ (res ≠ 1 → LiveEdges c.p (wNode c.p base w') c.i w'.top.rootKey)) := by
  refine writerWP_merge_liveG base x d c w hvc p pn hpath hpR hpn hpt hRt _ ?_
  intro leftSome l ln il r rn ir cL cR xn w3 hr3 h3p hk3 hsrc3 hL hLL hR' hRL hclt hadj hll hrl _
    hxlr hln hrn _ _
  exact writerWP_mergeTail_liveRoomR base x d c w hm hMP hT hR p pn hpR hpn hpleaf hpwf hpt hch hidn
    hidv hfree hfreshT Hl hLive hHl leftSome l ln il r rn ir cL cR xn w3 hr3 h3p hk3 hsrc3 hL hLL hR'
    hRL hclt hadj hll hrl hxlr hln hrn (mergeParentRoom_of_room c pn hroom hnd _ _ _ _ _ _)

set_option maxHeartbeats 4000000 in
/-- A round of the merges' loop at (g, h) from v (bergdb 030-01, step 3), given
the merge's tail where its parent takes `mergeParent`'s `full` (`hFull`): its
descent finds x at depth d with its parent p (v1), its reads (to v3), and a
merge of x with a sibling. If the live counts hold but at the node the round's
descent finds, then after a merge into one node they hold but at the node the
next round's descent finds, one height up, and after a merge into two nodes
they hold. -/
theorem liveHoleW_merge_G (key : Key) (g h : Nat) (c : Ctx) (base : View BVal) (v v1 v3 : W)
    (d : Nat) (hvc : ViewCoherent c base) (hm : c.p.merges = true) (hMP : MergeParamsOK c.p)
    (hS : descendToHeight key g h c v = .ok (d, v1)) (hd : 0 < d)
    (hr13 : ReadsAs c.p base v1 v3) (hk13 : ObsKept c v1 v3) (hp13 : v3.path = v1.path)
    (hLH : LiveHoleW key g h c base v)
    (hT : TreeOK (wNode c.p base v3) c.i v3.top.rootKey)
    (hR : RangeOrder (wNode c.p base v3) c.i v3.top.rootKey)
    (hRt : ∀ y, TReach (wNode c.p base v3) c.i v3.top.rootKey y → v3.taken.contains y = false)
    (hidn : ∀ z, (v3.nodes.lookup z).isSome = true → z < v3.next)
    (hidv : ∀ z, (c.view z).isSome = true → z < v3.next)
    (hfree : ∀ z, v3.next ≤ z → wNode c.p base v3 z = none ∧ v3.taken.contains z = false)
    (hfreshT : ∀ z, v3.next ≤ z → ∀ u c', TReach (wNode c.p base v3) c.i v3.top.rootKey u →
      ¬ TLink (wNode c.p base v3) c.i u c' z)
    (hdepth : ∀ j e, v3.path[j]? = some e → PathLen (wNode c.p base v3) c.i v3.top.rootKey e.2 j)
    (hpc3 : PathCached v3)
    (x p : NodeId) (pn : KNode) (hx : (v3.path[d]?).map (·.2) = some x)
    (hpath : (v3.path[d - 1]?).map (·.2) = some p) (hplk : v3.nodes.lookup p = some pn)
    (hpleaf : pn.leaf = false) (hpwf : klongsWf pn.ks = true)
    (hpt : ∀ s, Klong.time s ∈ pn.ks → s ≤ c.i)
    (hch : ∀ cc z zn, (cc, z) ∈ pn.liveAt c.i → wNode c.p base v3 z = some zn →
      ∀ s, Klong.time s ∈ zn.ks → s ≤ c.i)
    {H : NodeId → Nat → Prop} {B : NodeId} (hvh : ViewHeights H B c) (hvb : ViewIdsBelow B c.view)
    (hb1 : Book B c v1) (hi1 : HtInv H B c v1) (hpf1 : PathFreeTo v1 v1.path.length)
    (hb3 : Book B c v3)
    (hFull : ∀ (leftSome : Bool) (l : NodeId) (ln : KNode) (il : Nat) (r : NodeId)
        (rn : KNode) (ir cL cR : Nat) (xn : KNode) (w3 : W), ReadsAs c.p base v3 w3 →
        w3.nodes.lookup p = some pn → ObsKept c v3 w3 →
        (∀ z, (w3.nodes.lookup z).isSome = true → (v3.nodes.lookup z).isSome = true ∨
          (c.view z).isSome = true) →
        pn.ks[il]? = some (.key cL l) → LastLive pn.ks pn.lastBitmap il cL →
        pn.ks[ir]? = some (.key cR r) → LastLive pn.ks pn.lastBitmap ir cR → cL < cR →
        (∀ cc z, (cc, z) ∈ pn.liveAt c.i → cc ≤ cL ∨ cR ≤ cc) →
        ln.leaf = xn.leaf → rn.leaf = xn.leaf → wNode c.p base v3 x = some xn →
        (x = l ∨ x = r) → wNode c.p base v3 l = some ln → wNode c.p base v3 r = some rn →
        v3.nodes <+: w3.nodes → w3.path = v3.path →
        ¬ MergeParentRoom c pn il cL v3.next ir cR (mergeM2 c xn ln rn cR v3.next) →
        WriterWP (mergeTail c x d p pn xn leftSome l ln il r rn ir) c w3
          (fun res v4 => (res = 1 → LiveHoleW key g (h + 1) c base v4) ∧
            (res ≠ 1 → LiveEdges c.p (wNode c.p base v4) c.i v4.top.rootKey))) :
    WriterWP (merge x d) c v3 (fun res v4 => (res = 1 → LiveHoleW key g (h + 1) c base v4) ∧
      (res ≠ 1 → LiveEdges c.p (wNode c.p base v4) c.i v4.top.rootKey)) := by
  -- the round's descent: it reads, and finds x
  have hk01 : ObsKept c v v1 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, hk⟩ := writerWP_descendToHeight_rd key g h c v d v1 hS
    exact hk
  have hr01 : ReadsAs c.p base v v1 := writerWP_descendToHeight_readsU key g h c base hvc v d v1 hS
  have hk03 := hk01.trans hk13
  have hHl : ∀ y, HoleAtW key g h c v y → y = x := by
    intro y hy
    have h1 := hy d v1 hS
    rw [← hp13, hx] at h1
    exact (Option.some.inj h1).symm
  have hN3 : wNode c.p base v3 = wNode c.p base v := by rw [hr13.1, hr01.1]
  have htop3 : v3.top = v.top := hk03.2.2
  have hLive : LiveEdgesH c.p (wNode c.p base v3) c.i v3.top.rootKey (HoleAtW key g h c v) := by
    rw [hN3, htop3]; exact hLH
  have hpR : TReach (wNode c.p base v3) c.i v3.top.rootKey p := by
    obtain ⟨e, he⟩ : ∃ e, v3.path[d - 1]? = some e := by
      cases h' : v3.path[d - 1]? with
      | none => rw [h'] at hpath; cases hpath
      | some e => exact ⟨e, rfl⟩
    have hep : e.2 = p := by rw [he] at hpath; simpa using hpath
    rw [← hep]; exact (hdepth _ e he).reach
  have hpT := hRt p hpR
  have hpT' : p ∉ v3.taken := by simpa using hpT
  have hpn : wNode c.p base v3 p = some pn := by simp [wNode, hpT', hplk]
  refine writerWP_mono (writerWP_and (writerWP_merge_liveG base x d c v3 hvc p pn hpath hpR hpn hpt
    hRt (fun res w' => ((res = 1 →
      LiveEdgesH c.p (wNode c.p base w') c.i w'.top.rootKey (fun y => y = p) ∧
      (∀ y, y ≠ p → (∀ cc, (cc, y) ∉ pn.liveAt c.i) → y ≠ v3.next → rdN c w' y = rdN c v3 y) ∧
      w'.top = v3.top) ∧ (res ≠ 1 → LiveEdges c.p (wNode c.p base w') c.i w'.top.rootKey)) ∨
      ((res = 1 → LiveHoleW key g (h + 1) c base w') ∧
        (res ≠ 1 → LiveEdges c.p (wNode c.p base w') c.i w'.top.rootKey))) ?_)
    (book_merge B x d c v3 hvb hb3)) ?_
  · intro leftSome l ln il r rn ir cL cR xn w3 hr3 h3p hk3 hsrc3 hL hLL hR' hRL hclt hadj hll hrl hxn
      hxlr hln hrn hpre3 hpath3
    by_cases hB : MergeParentRoom c pn il cL v3.next ir cR (mergeM2 c xn ln rn cR v3.next)
    · exact writerWP_mono (writerWP_mergeTail_liveRoomR base x d c v3 hm hMP hT hR p pn hpR hpn hpleaf
        hpwf hpt hch hidn hidv hfree hfreshT _ hLive hHl leftSome l ln il r rn ir cL cR xn w3 hr3 h3p
        hk3 hsrc3 hL hLL hR' hRL hclt hadj hll hrl hxlr hln hrn hB) (fun _ _ h => Or.inl h)
    · exact writerWP_mono (hFull leftSome l ln il r rn ir cL cR xn w3 hr3 h3p hk3 hsrc3 hL hLL hR' hRL
        hclt hadj hll hrl hxn hxlr hln hrn hpre3 hpath3 hB) (fun _ _ h => Or.inr h)
  rintro res v4 ⟨hpost0, hb4, hkept⟩
  rcases hpost0 with ⟨hpost, hpost2⟩ | hround
  rotate_left
  · exact hround
  refine ⟨fun hres => ?_, hpost2⟩
  obtain ⟨hL4, hfr, htop4⟩ := hpost hres
  -- the path below the descent: its length and its node at d - 1
  have hlen1 : v1.path.length = d + 1 := by
    obtain ⟨_, _, _, _, _, _, _, hp, hdd, _⟩ := writerWP_descendToHeight_rd key g h c v d v1 hS
    rw [hp]; rw [← hp] at hdd ⊢
    have : d < v1.path.length := by
      rw [← hp13]
      by_cases hc : d < v3.path.length
      · exact hc
      · rw [List.getElem?_eq_none (by omega)] at hx; cases hx
    omega
  -- the descent one height up stops at p
  have hup : ∀ d' T1, descendToHeight key g (h + 1) c v4 = .ok (d', T1) →
      (T1.path[d']?).map (·.2) = some p := by
    intro d' T1 hT1
    refine (fun hres' => ?_) (descendToHeight_up key g h c v v1 v4 d hS hd ?_ ?_ ?_ ?_ ?_ d' T1 hT1)
    · obtain ⟨hd', hpath'⟩ := hres'
      rw [hd', hpath', List.getElem?_dropLast]
      have : d - 1 < v1.path.length - 1 := by omega
      simp only [this, ↓reduceIte]
      rw [← hp13]; exact hpath
    · intro e he
      have hep : e.2 = p := by rw [← hp13] at he; rw [he] at hpath; simpa using hpath
      refine ⟨pn, ?_, hpleaf⟩
      rw [hep, ← hk03.1]; exact rdN_of_lookup c v3 p pn hplk
    · rw [htop4, htop3]
    · intro y hy
      -- a node of the path two above the end: not p, not p's child, not new
      rw [List.mem_iff_getElem] at hy
      obtain ⟨j, hj, hjy⟩ := hy
      simp only [List.length_dropLast, List.length_map] at hj
      have hjd : j + 1 < d := by omega
      have hjl : j < v1.path.length := by omega
      have hy' : y = v1.path[j].2 := by
        rw [← hjy]; simp [List.getElem_dropLast]
      have hej : v3.path[j]? = some v1.path[j] := by rw [hp13]; exact List.getElem?_eq_getElem hjl
      have hpl := hdepth j _ hej
      obtain ⟨ep, hep⟩ : ∃ ep, v3.path[d - 1]? = some ep := by
        cases h' : v3.path[d - 1]? with
        | none => rw [h'] at hpath; cases hpath
        | some e => exact ⟨e, rfl⟩
      have hepp : ep.2 = p := by rw [hep] at hpath; simpa using hpath
      have hpd := hdepth (d - 1) ep hep
      rw [hepp] at hpd
      have hpl' : PathLen (wNode c.p base v3) c.i v3.top.rootKey y j := by rw [hy']; exact hpl
      have hyp : y ≠ p := by
        intro he; rw [he] at hpl'
        have := PathLen.depth_unique hT _ _ _ hpl' hpd; omega
      have hych : ∀ cc, (cc, y) ∉ pn.liveAt c.i := by
        intro cc hcc
        have hl : PathLen (wNode c.p base v3) c.i v3.top.rootKey y (d - 1 + 1) :=
          PathLen.link hpd ⟨pn, hpn, hcc⟩
        have := PathLen.depth_unique hT _ _ _ hpl' hl; omega
      have hyn : y ≠ v3.next := by
        have hjl3 : j < v3.path.length := by rw [hp13]; exact hjl
        have hy3 : v3.path[j].2 = y := by rw [hy']; simp [hp13]
        obtain ⟨n, hn⟩ := hpc3 _ (List.getElem_mem hjl3)
        have := hidn _ (by rw [hn]; rfl)
        rw [hy3] at this
        omega
      rw [hfr y hyp hych hyn, ← hk03.1]
    · intro y hy
      -- the nodes of the path but the last are cached with their segment and height
      rw [List.mem_iff_getElem] at hy
      obtain ⟨j, hj, hjy⟩ := hy
      simp only [List.length_dropLast, List.length_map] at hj
      have hjl : j < v1.path.length := by omega
      have hy' : y = v1.path[j].2 := by rw [← hjy]; simp [List.getElem_dropLast]
      have hjl3 : j < v3.path.length := by rw [hp13]; exact hjl
      obtain ⟨n3, hn3⟩ := hpc3 _ (List.getElem_mem hjl3)
      have hy3 : v3.path[j].2 = y := by rw [hy']; simp [hp13]
      rw [hy3] at hn3
      obtain ⟨g0, h0, hm0⟩ := kd_tag_of_lookup hb3 hn3
      obtain ⟨n4, hn4, _⟩ := hkept.1 y n3 hn3
      have h4 : rdG c v4 y = some (g0, h0) := by
        rw [rdG_of_lookup c v4 y n4 hn4]
        exact lookup_of_mem_nodup _ hb4.nodup y (g0, h0) (hkept.2 _ hm0)
      have h3 : rdG c v3 y = some (g0, h0) := by
        rw [rdG_of_lookup c v3 y n3 hn3]
        exact lookup_of_mem_nodup _ hb3.nodup y (g0, h0) hm0
      rw [h4, ← h3, hk03.2.1]
    · have hpc1 : PathCached v1 := writerWP_descendToHeight_path_cached key g h c v d v1 hS
      have := gradedL_of_ht hvh hb1 hi1 hpf1 hpc1
      rw [hk01.1, hk01.2.1] at this
      exact this
  refine liveEdgesH_mono c.p _ c.i _ (fun y => y = p) _ (fun y hy => hy ▸ hup) ?_ hL4
  intro u un cc y yn hu hun hcc hyn _ hyp
  exact ((hL4.2 u un cc y yn hu hun hcc hyn).1 hyp).1

/-- A round of the merges' loop at (g, h) from v whose merge's parent has room
and no compaction (bergdb 030-01, step 3; the pilot `liveHoleW_merge_pilot`
without its conditions on the made nodes and the merge into one node): its
descent finds x at depth d with its parent p (v1), its reads (to v3), and a
merge of x with a sibling. If the live counts hold but at the node the round's
descent finds, then after a merge into one node they hold but at the node the
next round's descent finds, one height up, and after a merge into two nodes
they hold. -/
theorem liveHoleW_merge_room (key : Key) (g h : Nat) (c : Ctx) (base : View BVal) (v v1 v3 : W)
    (d : Nat) (hvc : ViewCoherent c base) (hm : c.p.merges = true) (hMP : MergeParamsOK c.p)
    (hS : descendToHeight key g h c v = .ok (d, v1)) (hd : 0 < d)
    (hr13 : ReadsAs c.p base v1 v3) (hk13 : ObsKept c v1 v3) (hp13 : v3.path = v1.path)
    (hLH : LiveHoleW key g h c base v)
    (hT : TreeOK (wNode c.p base v3) c.i v3.top.rootKey)
    (hR : RangeOrder (wNode c.p base v3) c.i v3.top.rootKey)
    (hRt : ∀ y, TReach (wNode c.p base v3) c.i v3.top.rootKey y → v3.taken.contains y = false)
    (hidn : ∀ z, (v3.nodes.lookup z).isSome = true → z < v3.next)
    (hidv : ∀ z, (c.view z).isSome = true → z < v3.next)
    (hfree : ∀ z, v3.next ≤ z → wNode c.p base v3 z = none ∧ v3.taken.contains z = false)
    (hfreshT : ∀ z, v3.next ≤ z → ∀ u c', TReach (wNode c.p base v3) c.i v3.top.rootKey u →
      ¬ TLink (wNode c.p base v3) c.i u c' z)
    (hdepth : ∀ j e, v3.path[j]? = some e → PathLen (wNode c.p base v3) c.i v3.top.rootKey e.2 j)
    (hpc3 : PathCached v3)
    (x p : NodeId) (pn : KNode) (hx : (v3.path[d]?).map (·.2) = some x)
    (hpath : (v3.path[d - 1]?).map (·.2) = some p) (hplk : v3.nodes.lookup p = some pn)
    (hpleaf : pn.leaf = false) (hpwf : klongsWf pn.ks = true)
    (hpt : ∀ s, Klong.time s ∈ pn.ks → s ≤ c.i)
    (hch : ∀ cc z zn, (cc, z) ∈ pn.liveAt c.i → wNode c.p base v3 z = some zn →
      ∀ s, Klong.time s ∈ zn.ks → s ≤ c.i)
    {H : NodeId → Nat → Prop} {B : NodeId} (hvh : ViewHeights H B c) (hvb : ViewIdsBelow B c.view)
    (hb1 : Book B c v1) (hi1 : HtInv H B c v1) (hpf1 : PathFreeTo v1 v1.path.length)
    (hb3 : Book B c v3)
    (hroom : pn.size + 4 ≤ c.p.M)
    (hnd : ∀ il cL m1 ir cR m2, deadOver c.p (mergeParentNode pn c.i il cL m1 ir cR m2) = false) :
    WriterWP (merge x d) c v3 (fun res v4 => (res = 1 → LiveHoleW key g (h + 1) c base v4) ∧
      (res ≠ 1 → LiveEdges c.p (wNode c.p base v4) c.i v4.top.rootKey)) :=
  liveHoleW_merge_G key g h c base v v1 v3 d hvc hm hMP hS hd hr13 hk13 hp13 hLH hT hR hRt hidn hidv
    hfree hfreshT hdepth hpc3 x p pn hx hpath hplk hpleaf hpwf hpt hch hvh hvb hb1 hi1 hpf1 hb3
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hB' =>
      absurd (mergeParentRoom_of_room c pn hroom hnd _ _ _ _ _ _) hB')

/-! ## The live merge but where the parent is full or compacts -/

/-- The merge's parent p has room and no compaction for every merge it could
make (`mergeParent`'s branch that stores p's new version in place). -/
def MergeRoom (c : Ctx) (pn : KNode) : Prop :=
  pn.size + 4 ≤ c.p.M ∧
    ∀ il cL m1 ir cR m2, deadOver c.p (mergeParentNode pn c.i il cL m1 ir cR m2) = false

/-- `MergeLiveOK` where the merge's parent has no room or may compact (bergdb
030-01, step 3's rest: `mergeParent`'s `full`, the parent's split and its
cascade, with the hole below the chain; an obligation here). -/
def MergeLiveFullOK (c : Ctx) (base : View BVal) (B : NodeId) (H : NodeId → Nat → Prop) : Prop :=
  ∀ (key : Key) (g h : Nat) (v v1 v3 : W) (d F : Nat) (w0 : W) (k0 : Key) (KO : KindOracle)
    (top0 : Top) (X : Nat → NodeId) (K : Nat → Nat) (Nn : Nat → KNode) (x p : NodeId)
    (pn xn : KNode),
    descendToHeight key g h c v = .ok (d, v1) → 0 < d →
    ReadsAs c.p base v1 v3 → ObsKept c v1 v3 → v3.path = v1.path →
    LiveHoleW key g h c base v →
    DelInvJ c base w0 k0 F KO B B v3 → PutBook c B top0 v3 → PathOK c v3 d X K Nn →
    Book B c v1 → HtInv H B c v1 → PathFreeTo v1 v1.path.length → HtInv H B c v3 →
    (v3.path[d]?).map (·.2) = some x → (v3.path[d - 1]?).map (·.2) = some p →
    v3.nodes.lookup p = some pn → pn.leaf = false → v3.nodes.lookup x = some xn →
    xn.cnt < c.p.mergeBelow → ¬ MergeRoom c pn →
    WriterWP (merge x d) c v3 (fun res v4 => (res = 1 → LiveHoleW key g (h + 1) c base v4) ∧
      (res ≠ 1 → LiveEdges c.p (wNode c.p base v4) c.i v4.top.rootKey))

set_option maxHeartbeats 4000000 in
/-- The live merge (bergdb 030-01, step 3): every merge whose parent has room
and no compaction is proved (`liveHoleW_merge_room`, from the round's facts);
the rest is `MergeLiveFullOK`. -/
theorem mergeLiveOK_of_full (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (hm : c.p.merges = true) (hMP : MergeParamsOK c.p) {B : NodeId} {H : NodeId → Nat → Prop}
    (hvo : ViewHtOK H B c) (hF : MergeLiveFullOK c base B H) : MergeLiveOK c base B H := by
  intro key g h v v1 v3 d F w0 k0 KO top0 X K Nn x p pn xn hS hd hr13 hk13 hp13 hLH hJ3 hpb3 hP3 hb1
    hi1 hpf1 hi3 hx hpath hplk hpleaf hxlk hcnt
  by_cases hroom : MergeRoom c pn
  rotate_left
  · exact hF key g h v v1 v3 d F w0 k0 KO top0 X K Nn x p pn xn hS hd hr13 hk13 hp13 hLH hJ3 hpb3 hP3
      hb1 hi1 hpf1 hi3 hx hpath hplk hpleaf hxlk hcnt hroom
  have hI : PutInv c base v3 := hJ3.1.1.1
  have hRO : RangeOrder (wNode c.p base v3) c.i v3.top.rootKey := hJ3.1.1.2.2.1
  obtain ⟨hX, _, hS2, _, _⟩ := id hP3
  -- the path's length
  have hlen : d + 1 = v3.path.length := by
    obtain ⟨_, _, hl, _, _⟩ := descend_exit_shape key g h c v v1 d hS
    rw [hp13]; exact hl
  have hpX : p = X (d - 1) := by
    have := hX (d - 1) (by omega); rw [hpath] at this; exact Option.some.inj this
  have hpn : wNode c.p base v3 p = some pn := by
    obtain ⟨a, b⟩ := hS2 (d - 1) (by omega)
    rw [← hpX] at a b
    rw [hplk] at a
    simp only [wNode, b, Bool.false_eq_true, ↓reduceIte, hplk]
  have hfree : ∀ z, v3.next ≤ z → wNode c.p base v3 z = none ∧ v3.taken.contains z = false := by
    intro z hz
    have hl : v3.nodes.lookup z = none := by
      cases h' : v3.nodes.lookup z with
      | none => rfl
      | some _ => have := hI.ids.1 z (by rw [h']; rfl); omega
    have ht : v3.taken.contains z = false := by
      cases h' : v3.taken.contains z with
      | false => rfl
      | true => have := hI.ids.2.2.1 z h'; omega
    refine ⟨?_, ht⟩
    simp only [wNode, ht, Bool.false_eq_true, ↓reduceIte, hl, (hI.fresh z hz).1]
  refine liveHoleW_merge_room key g h c base v v1 v3 d hvc hm hMP hS hd hr13 hk13 hp13 hLH hI.tree hRO
    (fun y hy => hI.untaken y (tReach_reachS _ _ _ _ hy)) hI.ids.1 hI.ids.2.1 hfree
    (fun z hz u c' hu hl => by
      obtain ⟨un, hun, hc⟩ := hl
      have := hI.links u un c' z (tReach_reachS _ _ _ _ hu) hun hc
      omega)
    (fun j e he => by
      have hj : j ≤ d := by
        have := (List.getElem?_eq_some_iff.mp he).1; omega
      have hXj := hX j hj
      rw [he] at hXj
      have hej : e.2 = X j := Option.some.inj hXj
      rw [hej]
      exact pathOK_depth c base v3 d X K Nn hP3 j hj)
    (fun e he => by
      obtain ⟨j, hj, hje⟩ := List.mem_iff_getElem.mp he
      have hXj := hX j (by omega)
      rw [List.getElem?_eq_getElem hj, hje] at hXj
      have hej : e.2 = X j := Option.some.inj hXj
      rw [hej]
      exact ⟨Nn j, (hS2 j (by omega)).1⟩)
    x p pn hx hpath hplk hpleaf (hI.wf p pn hpn) (hI.times p pn hpn)
    (fun cc z zn _ hzn => hI.times z zn hzn) hvo.heights hvo.ids hb1 hi1 hpf1 hpb3.book hroom.1 hroom.2

/-- `afterDelete` with the hole (bergdb 030-01, step 3): `writerWP_afterDelete_live`
with the live merge reduced to the merges whose parent is full or compacts. -/
theorem writerWP_afterDelete_liveF (key : Key) (g : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (hm : c.p.merges = true) (hMP : MergeParamsOK c.p) (KO : KindOracle)
    (B : NodeId) (hv : ViewIdsBelow B c.view) (hk : ViewKinds KO B c)
    (hICEk : ICEFromKinds c base KO B) (hsa2 : 2 ≤ c.p.splitAbove) (hcap : 1 ≤ c.p.mergeMax)
    (hpos : 0 < c.i) {H : NodeId → Nat → Prop} (hvo : ViewHtOK H B c)
    (hkw : ViewKlongsWf c.p c.view) (top0 : Top) (hB : PutBase c base B)
    (hF : MergeLiveFullOK c base B H) (hCL : CollapseLiveOK c base B)
    (v : W) (hJ : DelInvJAE c base KO B B v) (hpb : PutBook c B top0 v) (hhi : HtInv H B c v)
    (hLH : LiveHoleW key g 0 c base v) :
    WriterWP (afterDelete key g 0) c v
      (fun _ v' => LiveEdges c.p (wNode c.p base v') c.i v'.top.rootKey) :=
  writerWP_afterDelete_live key g c base hvc hm KO B hv hk hICEk hsa2 hcap hpos hvo hkw top0 hB
    (mergeLiveOK_of_full c base hvc hm hMP hvo hF) hCL v hJ hpb hhi hLH

end SIS.Tree
