/-
The contract package (bergdb 030-14, section 2): the independent review's
example of 17 November (`FullLeafGap`, by a review of the night's proofs run
read-only on main 7ef19685), here as a test of the statement of reads after a
crash.

Two histories of one transaction that differ only in the kind of one key node
(node 3, on level 2: a segment leaf or an inner node) and in the key that the
put names ([56, 64] or [64]). Both meet every clause of `MeetsFull`; their
model structures and streams are one; their reads differ. So the model's
structure alone (what recovery gives back, `Rep`) does not fix the reads: the
kind of a key node must come through it.

The statement of RecoverTheorems.lean takes the kinds from the levels (the
reader `kindOf kind V`) for a history that meets K-LEVEL (`KindsOK kind`).
For any kind function, at most one of the two histories meets it
(`kinds_exclusive`), and each meets it for its own (`kinds_leaf`,
`kinds_inner`): after a crash, the reader of the same recovered view with the
kinds of each history's levels reads each history's own plain map
(`crash_leaf`, `crash_inner`). The gap is ruled out.

The definitions and the proof of `full` are the review's, unchanged but for
the names of this package.
-/
import Contract.RecoverTheorems

namespace Contract.RecoverLeafGap

open Contract
open SIS (Changes)
open SIS.Check (BVal)

def p : Params := ⟨8⟩
def s0 : Tree := { obj := fun x => if x = 1 then some (.key ⟨1,true,[.time 0]⟩) else none, roots := [(0,1)] }
def s1 (leaf : Bool) : Tree := {
  obj := fun x => if x = 1 then some (.key ⟨1,true,[.time 0]⟩)
    else if x = 2 then some (.val 5)
    else if x = 3 then some (.key ⟨2,leaf,[.time 1,.key 56 4]⟩)
    else if x = 4 then some (.key ⟨1,true,[.time 1,.key 64 2]⟩) else none,
  roots := [(0,1),(1,3)] }
def c0 : Changes BVal := { new := [⟨0,20,false⟩, ⟨1,1,false⟩, ⟨5,8,false⟩], adds := [(0,.top 5),(5,.rootKey 1)] }
def c1 : Changes BVal := {
  new := [⟨2,0,true⟩,⟨3,2,false⟩,⟨4,1,false⟩,⟨6,9,false⟩],
  adds := [(0,.top 6),(6,.rootKey 3),(6,.skip 0 5),(3,.key 56 4),(4,.key 64 2),(2,.data 5)] }
def tp0 : Top := [(5,⟨0,1,[]⟩)]
def tp1 : Top := tp0 ++ [(6,⟨1,3,[(0,5,0)]⟩)]
def tops (j : Nat) : Top := if j = 0 then tp0 else tp1
def txops (leaf : Bool) : List Op := [Op.put (if leaf then [56,64] else [64]) 5]
def hist (leaf : Bool) : BHist :=
  { s0 := s0, c0 := c0,
    txs := [{ ops := txops leaf, D := [3,4], s := s1 leaf, c := c1 }] }
theorem frame (leaf : Bool) : Frame 1 s0 [3,4] (s1 leaf) := by
  refine ⟨?_, ?_, ⟨[(1,3)], rfl, by simp⟩⟩
  · intro x o hx
    by_cases hx1 : x = 1
    · subst hx1
      simp [s0] at hx
      subst hx
      exact ⟨_, rfl, ⟨rfl, rfl, Or.inl rfl⟩, fun _ => rfl⟩
    · simp [s0, hx1] at hx
  · intro x n hx hno
    by_cases h1 : x = 1
    · simp [s0,h1] at hno
    · by_cases h2 : x = 2
      · simp [s1,h2] at hx
      · by_cases h3 : x = 3
        · simp [h3]
        · by_cases h4 : x = 4
          · simp [h4]
          · simp [s1,h1,h2,h3,h4] at hx

theorem made (leaf : Bool) : Made s0 (s1 leaf) c1 := by
  intro x hno hs
  by_cases h1 : x = 1
  · simp [s0,h1] at hno
  · by_cases h2 : x = 2
    · simp [h2,c1]
    · by_cases h3 : x = 3
      · simp [h3,c1]
      · by_cases h4 : x = 4
        · simp [h4,c1]
        · simp [s1,h1,h2,h3,h4] at hs

theorem full (leaf : Bool) : MeetsFull p (hist leaf) tops where
  start := ⟨1,5,1,8,20,by decide,by decide,by decide,by decide,by decide,by decide,by decide,
    rfl,rfl,rfl,fun x hx => by simp [hist,s0,hx],rfl⟩
  startTop := by change topStartOk c0 tp0 s0 = true; decide
  step := by
    intro j hj
    have hz : j = 0 := by simpa [hist] using hj
    subst hz
    refine ⟨⟨?_, frame leaf⟩, ?_, made leaf, ?_, rfl, ?_, ?_, ?_⟩
    · change contractOk p 1 s0 (txops leaf) (s1 leaf) = true
      cases leaf <;> decide
    · change bridgeOk 8 1 s0 (s1 leaf) [3,4] c1 = true
      cases leaf <;> decide
    · exact topStepB_sound 1 tp0 tp1 (by decide)
    · change topChangeOk 8 (SIS.Struct.apply [] 0 c0) (s1 leaf) tp0 tp1 c1 = true
      cases leaf <;> decide
    · change touchOk (s0.at 0) tp0 [] = true; decide
    · change copyOk 1 s0 (s1 leaf) tp0 c1 = true
      cases leaf <;> decide
  tree := by
    intro j hj
    have hl : j ≤ 1 := hj
    interval_cases j
    · change TreeOk (s0.at 0); decide
    · cases leaf <;> decide
  adopt := by
    intro j hj
    have hl : j ≤ 1 := hj
    interval_cases j
    · change adoptOk (s0.at 0) = true; decide
    · cases leaf <;> decide

theorem same_model : (hist true).P 1 = (hist false).P 1 := rfl

theorem same_stream (al : SIS.Algo BVal Nat) :
    (SIS.run (hist true).spec al (hist true).ts).S =
      (SIS.run (hist false).spec al (hist false).ts).S := rfl

theorem different_reads :
    get ((s1 true).at 1) [56, 64] = some 5 ∧ get ((s1 false).at 1) [56, 64] = none ∧
    scan ((s1 true).at 1) {} 10 = [([56, 64], 5)] ∧
    scan ((s1 false).at 1) {} 10 = [([64], 5)] := by decide

/-- No kind function by level is met by both histories: node 3 is on level 2
in both, a segment leaf in one and an inner node in the other. -/
theorem kinds_exclusive (kind : Nat → Bool) :
    KindsOK kind (hist true) → KindsOK kind (hist false) → False := by
  intro ht hf
  have h1 := ht.2 0 (by decide)
  have h2 := hf.2 0 (by decide)
  change kindsOk kind (s1 true) [3, 4] = true at h1
  change kindsOk kind (s1 false) [3, 4] = true at h2
  simp [kindsOk, s1] at h1 h2
  cases hk : kind 2 <;> simp_all

theorem start_kinds (kind : Nat → Bool) (hk : kind 1 = true) (leaf : Bool) :
    ∀ x n, (hist leaf).s0.obj x = some (.key n) → n.leaf = kind n.level := by
  intro x n hx
  by_cases h1 : x = 1
  · subst h1
    simp [hist, s0] at hx
    subst hx
    exact hk.symm
  · simp [hist, s0, h1] at hx

/-- The history with node 3 a segment leaf meets K-LEVEL for h = 0 (every key
node a segment leaf). -/
theorem kinds_leaf : KindsOK (kindOfHeight 0) (hist true) :=
  ⟨start_kinds _ rfl true, fun j hj => by
    have : j = 0 := by simpa [hist] using hj
    subst this
    rfl⟩

/-- The history with node 3 an inner node meets K-LEVEL for h = 1. -/
theorem kinds_inner : KindsOK (kindOfHeight 1) (hist false) :=
  ⟨start_kinds _ rfl false, fun j hj => by
    have : j = 0 := by simpa [hist] using hj
    subst this
    rfl⟩

/-- After a crash after the transaction, the reader of the recovered view,
with the kinds of the levels of the history with the segment leaf, scans the
key [56, 64]. -/
theorem crash_leaf :
    let V := SIS.view (hist true).spec (SIS.startup (hist true).spec
      ((SIS.run (hist true).spec (hist true).al0 (hist true).ts).S.take 2)).P 1
    vscan V (kindOf (kindOfHeight 0) V) {} 10 = [([56, 64], 5)] := by
  intro V
  rw [(crash_reads (full true) (by decide) kinds_leaf (hist true).al0 rfl (k := 1) (t := 1)
    (by decide) (le_refl _)).2 {} (by decide) 10]
  decide

/-- And with the kinds of the levels of the history with the inner node, the
key [64]: each history's own plain map. -/
theorem crash_inner :
    let V := SIS.view (hist false).spec (SIS.startup (hist false).spec
      ((SIS.run (hist false).spec (hist false).al0 (hist false).ts).S.take 2)).P 1
    vscan V (kindOf (kindOfHeight 1) V) {} 10 = [([64], 5)] := by
  intro V
  rw [(crash_reads (full false) (by decide) kinds_inner (hist false).al0 rfl (k := 1) (t := 1)
    (by decide) (le_refl _)).2 {} (by decide) 10]
  decide

end Contract.RecoverLeafGap
