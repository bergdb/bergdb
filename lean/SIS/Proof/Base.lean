/-
Proofs, part 15: what startup reads (readFrom, readAt, baseStruct) and the rerun.
-/
import SIS.Proof.Recon

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

theorem readFrom_eq (sp : Spec V T) (S : Stream V T) (s : Nat) (ruleR : Bool) (t : Time)
    (v : Version V) :
    readFrom sp S s ruleR t v =
      (v.node, v) :: (sp.live (v.hist.upTo t)).flatMap (fun y =>
        match follow S s ruleR y (v.ref? y) with
        | none => []
        | some w => if w.level < v.level then readFrom sp S s ruleR t w else []) := by
  rw [readFrom]; rfl

section Read

variable {sp : Spec V T} {db : DB V T} {k : Nat}

/-- Reading from a version that is good with Rule R gives the nodes reachable
from its node, each with a version that is good with Rule R. -/
theorem Inv.read (hinv : Inv sp db k) (t : Time) :
    ∀ (b : Nat) (v : Version V) (n : Node V), v.level < b →
      GoodR sp db.S db.P (lastSp db.S) t v → db.P.get? v.node = some n → v.level = n.level →
      (∃ r, db.S.versionAt r v.node = some v) →
      (readFrom sp db.S (lastSp db.S) true t v).map (·.1) = reachFrom sp db.P t v.node n ∧
      ∀ p ∈ readFrom sp db.S (lastSp db.S) true t v,
        GoodR sp db.S db.P (lastSp db.S) t p.2 ∧ p.2.node = p.1 ∧ ∃ r, db.S.versionAt r p.1 = some p.2 := by
  intro b
  induction b with
  | zero => intro v n h; omega
  | succ b ih =>
    intro v n hb hg hn hlev hvS
    have hg0 := hg
    cases hg with
    | mk _ n' hn' hc hsome hlt hgood =>
    rw [hn] at hn'
    cases hn'
    -- The children, one by one.
    have hch : ∀ y ∈ sp.live (v.hist.upTo t), ∃ w m,
        follow db.S (lastSp db.S) true y (v.ref? y) = some w ∧ db.P.get? y = some m ∧
        w.level = m.level ∧ w.level < v.level ∧ GoodR sp db.S db.P (lastSp db.S) t w ∧ w.node = y ∧
        ∃ r, db.S.versionAt r y = some w := by
      intro y hy
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (hsome y hy)
      obtain ⟨hwy, r, hr⟩ := follow_spec hw
      obtain ⟨-, -, m, hm, -, hlevw, -⟩ := hinv.version_node hr
      exact ⟨w, m, hw, hm, hlevw, hlt y hy w hw, hgood y hy w hw, hwy, r, hr⟩
    constructor
    · rw [readFrom_eq, reachFrom_eq]
      simp only [List.map_cons, List.map_flatMap]
      rw [← hc]
      congr 1
      apply flatMap_congr_mem
      intro y hy
      obtain ⟨w, m, hw, hm, hlevw, hltw, hgw, hwy, r, hr⟩ := hch y hy
      rw [hw, hm]
      have hlt' : m.level < n.level := by omega
      simp only [hltw, hlt', ite_true]
      have := (ih w m (by omega) hgw (by rw [hwy]; exact hm) hlevw ⟨r, by rw [hwy]; exact hr⟩).1
      rw [hwy] at this
      exact this
    · intro p hp
      rw [readFrom_eq] at hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨hg0, rfl, hvS⟩
      · simp only [List.mem_flatMap] at hp
        obtain ⟨y, hy, hp⟩ := hp
        obtain ⟨w, m, hw, hm, hlevw, hltw, hgw, hwy, r, hr⟩ := hch y hy
        rw [hw] at hp
        simp only [hltw, ite_true] at hp
        exact (ih w m (by omega) hgw (by rw [hwy]; exact hm) hlevw ⟨r, by rw [hwy]; exact hr⟩).2 p hp

theorem Inv.lv_root (hinv : Inv sp db k) : ∃ u, db.S.lv root = some u := by
  obtain ⟨n0, hn0⟩ := Option.isSome_iff_exists.mp hinv.rootIn
  cases hl : db.S.lv root with
  | some u => exact ⟨u, rfl⟩
  | none =>
    exfalso
    cases hd : n0.isData
    · have hidx : isIndex db.P root = true := by simp [isIndex, hn0, hd]
      have hdirty : dirty sp db.S db.P k root = true := by simp [dirty, hl]
      obtain ⟨d, hD⟩ := (inD_iff _ _).mp (hinv.inv2 root hidx hdirty)
      have hsd := (sectionD_mem (hinv.inv1 ▸ hD)).1
      have := hinv.inv4 root d hD hl 0 (by omega)
      have hr : reachable sp db.P 0 root = true := (reachable_iff _ _ _ _).mpr (Reach.root n0 hn0)
      rw [hr] at this; simp at this
    · obtain ⟨v, hv, -⟩ := hinv.dataV root n0 hn0 hd
      rw [hl] at hv; simp at hv

theorem reachable_root {P : Struct V} {n : Node V} (h : P.get? root = some n) (t : Time) :
    reachable sp P t root = true := (reachable_iff _ _ _ _).mpr (Reach.root n h)

/-- Reading the stream at a time t <= s gives exactly the nodes reachable at t,
each with a version that is good with Rule R (L-RECON). -/
theorem Inv.readAt_spec (hinv : Inv sp db k) (hls : LiveSub sp) {t : Time} (ht : t ≤ lastSp db.S) :
    (SIS.readAt sp db.S (lastSp db.S) true t).map (·.1) = reachList sp db.P t ∧
    ∀ p ∈ SIS.readAt sp db.S (lastSp db.S) true t,
      GoodR sp db.S db.P (lastSp db.S) t p.2 ∧ p.2.node = p.1 ∧
        ∃ r, db.S.versionAt r p.1 = some p.2 := by
  obtain ⟨n0, hn0⟩ := Option.isSome_iff_exists.mp hinv.rootIn
  obtain ⟨u, hu⟩ := hinv.lv_root
  have hsk : lastSp db.S ≤ k := by have := hinv.spLt; omega
  -- The record of root's latest version, from top(k).
  have htop : db.S.getLast?.bind (·.top) = some u.recNo := by
    cases hl : db.S.getLast? with
    | none =>
      have : db.S = [] := List.getLast?_eq_none_iff.mp hl
      have := hinv.len; simp_all
    | some R =>
      simp only [Option.bind_some]
      rw [hinv.top R hl, hu]; rfl
  -- The version of root that startup starts from is good with Rule R.
  have hrecon := hinv.recon hls
  obtain ⟨v0, hf, hg0, hv0S, hv0node⟩ : ∃ v0, follow db.S (lastSp db.S) true root (some u.recNo) = some v0 ∧
      GoodR sp db.S db.P (lastSp db.S) t v0 ∧ (∃ r, db.S.versionAt r v0.node = some v0) ∧
      v0.node = root := by
    cases hnw : newest db.S (lastSp db.S) root with
    | some w =>
      obtain ⟨r, hr, hwr⟩ := newest_some hnw
      obtain ⟨hwy, -⟩ := hinv.version_node hwr
      refine ⟨w, follow_newest hnw, ?_, ⟨r, by rw [hwy]; exact hwr⟩, hwy⟩
      exact (hrecon (w.level + 1)).1 r w hr (by rw [hwy]; exact hwr) (by omega) t ht
        (by rw [hwy]; exact reachable_root hn0 t)
    | none =>
      have hu' := hinv.lv_at hu
      obtain ⟨huy, -⟩ := hinv.version_node hu'
      have hus : u.recNo ≤ lastSp db.S := by
        cases Nat.lt_or_ge (lastSp db.S) u.recNo with
        | inl h =>
          have := (newest_eq_none_iff _ _ _).mp hnw u.recNo h
          rw [hu'] at this; simp at this
        | inr h => exact h
      refine ⟨u, by rw [follow_old hnw]; exact hu', ?_, ⟨u.recNo, by rw [huy]; exact hu'⟩, huy⟩
      exact (hrecon (u.level + 1)).2 u.recNo u (by rw [huy]; exact hu') (by omega) t ht
        (by rw [huy]; exact reachable_root hn0 t)
        (hinv.lout hls hu hus ht (reachable_root hn0 t))
  have hread : SIS.readAt sp db.S (lastSp db.S) true t = readFrom sp db.S (lastSp db.S) true t v0 := by
    unfold SIS.readAt
    rw [htop]
    simp only
    rw [hf]
  obtain ⟨r0, hr0⟩ := hv0S
  rw [hv0node] at hr0
  obtain ⟨-, -, m, hm, -, hlev, -⟩ := hinv.version_node hr0
  have hR := hinv.read t (v0.level + 1) v0 m (by omega) hg0 (by rw [hv0node]; exact hm) hlev
    ⟨r0, by rw [hv0node]; exact hr0⟩
  rw [hread]
  refine ⟨?_, hR.2⟩
  rw [hR.1, hv0node]
  simp only [reachList, hm]

end Read

/-! ### The last occurrence in a list of blocks -/

theorem lookup_rev_flatMap_range {β : Type} (f : Nat → List (NodeId × β)) :
    ∀ (n : Nat) (x : NodeId) (u : β),
      List.lookup x (((List.range (n + 1)).flatMap f).reverse) = some u →
      ∃ t ≤ n, (x, u) ∈ f t ∧ ∀ t', t < t' → t' ≤ n → x ∉ (f t').map (·.1) := by
  intro n
  induction n with
  | zero =>
    intro x u h
    rw [show List.range (0 + 1) = [0] from rfl] at h
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at h
    obtain ⟨l1, l2, hl, -⟩ := List.lookup_eq_some_iff.mp h
    refine ⟨0, Nat.le_refl 0, ?_, fun t' h1 h2 => by omega⟩
    have : (x, u) ∈ (f 0).reverse := by rw [hl]; simp
    simpa using this
  | succ n ih =>
    intro x u h
    rw [List.range_succ, List.flatMap_append, List.reverse_append, List.lookup_append] at h
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at h
    cases hl : List.lookup x (f (n + 1)).reverse with
    | some u' =>
      rw [hl, Option.some_or] at h
      have huu : u' = u := Option.some.inj h
      subst huu
      obtain ⟨l1, l2, hl', -⟩ := List.lookup_eq_some_iff.mp hl
      refine ⟨n + 1, Nat.le_refl _, ?_, fun t' h1 h2 => by omega⟩
      have : (x, u') ∈ (f (n + 1)).reverse := by rw [hl']; simp
      simpa using this
    | none =>
      rw [hl, Option.none_or] at h
      obtain ⟨t, ht, hm, hlater⟩ := ih x u h
      refine ⟨t, by omega, hm, fun t' h1 h2 => ?_⟩
      rcases Nat.lt_or_ge t' (n + 1) with h3 | h3
      · exact hlater t' h1 (by omega)
      · have : t' = n + 1 := by omega
        subst this
        rw [List.lookup_eq_none_iff] at hl
        intro hx
        simp only [List.mem_map] at hx
        obtain ⟨p, hp, rfl⟩ := hx
        have := hl p (by simpa using hp)
        simp at this

/-! ### P up to s -/

section Base

variable {sp : Spec V T} {db : DB V T} {k : Nat}

/-- A version as a node of P, cut at time s. -/
def cutNode (s : Nat) (v : Version V) : Node V :=
  { level := v.level, isData := v.isData, hist := v.hist.upTo s }

theorem baseStruct_eq (sp : Spec V T) (S : Stream V T) (s : Nat) (ruleR : Bool) :
    baseStruct sp S s ruleR =
      ((((List.range (s + 1)).flatMap (fun t => SIS.readAt sp S s ruleR t)).map (·.1)).eraseDups).filterMap
        (fun x => ((List.lookup x ((List.range (s + 1)).flatMap
          (fun t => SIS.readAt sp S s ruleR t)).reverse).map (cutNode s)).map (fun b => (x, b))) := by
  unfold baseStruct
  simp only
  congr
  funext x
  cases List.lookup x _ <;> rfl

/-- The node that startup reads for x, cut at s. -/
theorem Inv.base_get? (hinv : Inv sp db k) (hls : LiveSub sp) (x : NodeId) :
    (baseStruct sp db.S (lastSp db.S) true).get? x =
      if ∃ t ≤ lastSp db.S, reachable sp db.P t x = true then
        (db.P.get? x).map (fun n => { n with hist := n.hist.upTo (lastSp db.S) })
      else none := by
  have hsk : lastSp db.S ≤ k := by have := hinv.spLt; omega
  rw [baseStruct_eq, Struct.get?, lookup_filterMap_pair]
  -- Membership in the ids.
  have hmem : x ∈ ((List.flatMap (fun t => SIS.readAt sp db.S (lastSp db.S) true t)
      (List.range (lastSp db.S + 1))).map (·.1)).eraseDups ↔
      ∃ t ≤ lastSp db.S, reachable sp db.P t x = true := by
    rw [List.mem_eraseDups, List.map_flatMap]
    simp only [List.mem_flatMap, List.mem_range]
    constructor
    · rintro ⟨t, ht, hx⟩
      rw [(hinv.readAt_spec hls (t := t) (by omega)).1] at hx
      exact ⟨t, by omega, by simp [reachable, hx]⟩
    · rintro ⟨t, ht, hx⟩
      refine ⟨t, by omega, ?_⟩
      rw [(hinv.readAt_spec hls (t := t) ht).1]
      simpa [reachable] using hx
  by_cases hex : ∃ t ≤ lastSp db.S, reachable sp db.P t x = true
  · rw [ite_eq_left_iff.mpr (fun h => absurd (hmem.mpr hex) h), ite_eq_left_iff.mpr (fun h => absurd hex h)]
    -- The version from the last time x is reached.
    have hids := hmem.mpr hex
    rw [List.mem_eraseDups, List.mem_map] at hids
    obtain ⟨⟨x', u0⟩, hp0, hx'⟩ := hids
    simp only at hx'
    subst hx'
    cases hl : List.lookup x' (List.flatMap (fun t => SIS.readAt sp db.S (lastSp db.S) true t)
        (List.range (lastSp db.S + 1))).reverse with
    | none =>
      exfalso
      rw [List.lookup_eq_none_iff] at hl
      have := hl (x', u0) (by simpa using hp0)
      simp at this
    | some u =>
      obtain ⟨t, ht, hmem', hlater⟩ := lookup_rev_flatMap_range _ _ x' u hl
      obtain ⟨hgu, hux, r, hr⟩ := (hinv.readAt_spec hls (t := t) ht).2 _ hmem'
      simp only at hgu hux hr
      obtain ⟨-, hrec, n, hn, huh, hlev, hdata⟩ := hinv.version_node hr
      rw [hn]
      simp only [Option.map_some, Option.some.injEq, cutNode]
      cases hgu with
      | mk _ n' hn' hc _ _ _ =>
      rw [hux, hn] at hn'
      cases hn'
      -- The history of u, cut at s, is the history of x cut at s.
      have hcut : u.hist.upTo (lastSp db.S) = n.hist.upTo (lastSp db.S) := by
        rw [huh]
        simp only [History.upTo, List.filter_filter]
        apply List.filter_congr
        intro e he
        by_cases hes : e.time ≤ lastSp db.S
        · have her : e.time ≤ r := by
            rcases Nat.lt_or_ge r e.time with hcon | hcon
            · exfalso
              have hre := hinv.er x' n hn e he
              have het : e.time ≤ t := by
                rcases Nat.lt_or_ge t e.time with hcon2 | hcon2
                · exfalso
                  exact hlater e.time hcon2 hes (by
                    rw [(hinv.readAt_spec hls (t := e.time) hes).1]
                    simpa [reachable] using hre)
                · exact hcon2
              have : e ∈ n.hist.upTo t := mem_upTo.mpr ⟨he, het⟩
              rw [← hc, huh] at this
              have := (mem_upTo.mp (mem_upTo.mp this).1).2
              omega
            · exact hcon
          simp [hes, her]
        · simp [hes]
      rw [hcut, hlev, hdata]
  · rw [ite_eq_right_iff.mpr (fun h => absurd (hmem.mp h) hex), ite_eq_right_iff.mpr (fun h => absurd h hex)]

end Base

end SIS
