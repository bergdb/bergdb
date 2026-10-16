/-
Proofs, part 14b: reading the stream from a version that is good with Rule R
(readFrom).
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

/-- v could be a version of x in P: it has x's level and kind, and x's
history up to some time. The versions of the stream are (`Inv.versionOf`);
so is the root that startup rebuilds with a virtual root. -/
def VersionOf (P : Struct V) (x : NodeId) (v : Version V) : Prop :=
  ∃ r n, P.get? x = some n ∧ v.hist = n.hist.upTo r ∧ v.level = n.level ∧ v.isData = n.isData

section Read

variable {sp : Spec V T} {db : DB V T} {k : Nat}

theorem Inv.versionOf (hinv : Inv sp db k) {r : Nat} {y : NodeId} {w : Version V}
    (h : db.S.versionAt r y = some w) : VersionOf db.P y w := by
  obtain ⟨-, -, n, hn, h1, h2, h3⟩ := hinv.version_node h
  exact ⟨r, n, hn, h1, h2, h3⟩

/-- Reading from a version that is good with Rule R gives the nodes reachable
from its node, each with a version that is good with Rule R. -/
theorem Inv.read (hinv : Inv sp db k) (t : Time) :
    ∀ (b : Nat) (v : Version V) (n : Node V), v.level < b →
      GoodR sp db.S db.P (lastSp db.S) t v → db.P.get? v.node = some n → v.level = n.level →
      VersionOf db.P v.node v →
      (readFrom sp db.S (lastSp db.S) true t v).map (·.1) = reachFrom sp db.P t v.node n ∧
      ∀ p ∈ readFrom sp db.S (lastSp db.S) true t v,
        GoodR sp db.S db.P (lastSp db.S) t p.2 ∧ p.2.node = p.1 ∧ VersionOf db.P p.1 p.2 := by
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
      have := (ih w m (by omega) hgw (by rw [hwy]; exact hm) hlevw
        (by rw [hwy]; exact hinv.versionOf hr)).1
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
        exact (ih w m (by omega) hgw (by rw [hwy]; exact hm) hlevw
          (by rw [hwy]; exact hinv.versionOf hr)).2 p hp

end Read

theorem reachable_root {sp : Spec V T} {P : Struct V} {n : Node V} (h : P.get? root = some n)
    (t : Time) : reachable sp P t root = true := (reachable_iff _ _ _ _).mpr (Reach.root n h)

end SIS
