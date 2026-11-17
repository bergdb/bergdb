/-
The contract package (bergdb 030-07): what of bounded startup follows from
the bridge (bergdb 030-04, step 4; 006-26, sections 3.4, 3.5 and 5.1).

* T3 (the startup distance bounds the startup section: `SIS.T3_take`,
  `SIS.T3_take_decrease`, `SIS.T3_takeB`) and T4's record (`SIS.T4_record`)
  assume nothing of the structure, so they hold for the model's instance of
  any history as they stand.
* T4's debt (`bridge_debt`): every node of D reaches, through pointers live or
  dead, a node changed or touched in the last few startup sections. It was
  reduced to `RunOK`; for BergDB's key tree it is now proved from the
  contract and the bridge's clauses.
* The live height (`bridge_liveHeight`): if the space root's level is at most
  K after every transaction, every chain of live pointers down from the
  model's root has at most K + 2 steps, since a live klong names a node on a
  lower level. This is the premise H of T4's count and of `bounded_startup`,
  with H = K + 2: a bound by the level's number, not by the tree's height.

Open, for `bounded_startup` (006-26, section 5.1): the fit of D in a record;
Hp and Q (the height and the parents along all pointers, live or dead: not
known to stay bounded as the database ages); what a transaction removes (K,
with `DropRunOKJ`), the siblings its merges read (B), the size of its change
(A), a top node's pointers (Pt). None follows from the contract as it is:
the contract left the fill and the balance out (030-05, section 3).
-/
import SIS.BoundT4JavaTheorems
import SIS.BoundHeight
import Contract.BridgeTheorems

namespace Contract

open SIS (Struct Changes Entry History Node NewNode Spec)
open SIS.Check (BVal bptrs blive bspec)

variable {p : Params} {h : BHist}

/-- T4's debt, for BergDB's key tree: after any history that meets the contract
and the bridge's clauses, with BergDB's still-dirty test, every node x of D
reaches, through pointers live or dead, a node on the access path of the
change of a transaction of the last lev(x) + 1 startup sections. -/
theorem bridge_debt (hm : MeetsBridge p h) (al : SIS.Algo BVal Nat)
    (hj : al.stillDirty = SIS.javaTest h.spec) : SIS.DebtByChains h.spec al h.ts :=
  SIS.T4_debt_java h.spec al h.ts (hm.runOK al) hj

/-- A node of the tree on level L or lower has live height at most L in the
model: a live klong names a node on a lower level. -/
theorem BInv.liveHeight {j : Nat} (hi : BInv h j) : ∀ (L : Nat) (x : NodeId) (o : Obj),
    (h.tree j).obj x = some o → lvl o ≤ L → SIS.LiveHeightLe h.spec (h.P j) j L x
  | 0, x, o, ho, hl => by
    intro N hN
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro y hy
    cases o with
    | val v => exact hi.val_live ho hN j y hy
    | key n =>
      obtain ⟨hP, hlive⟩ := hi.key_live ho
      rw [hP] at hN
      injection hN with hN
      subst hN
      obtain ⟨c, hc⟩ := (hlive y).mp hy
      obtain ⟨oy, _, hlt⟩ := hi.lev x n ho c y (live_mem_key hc)
      have h0 : n.level ≤ 0 := hl
      omega
  | L + 1, x, o, ho, hl => by
    intro N hN y hy
    cases o with
    | val v => exact absurd hy (hi.val_live ho hN j y)
    | key n =>
      obtain ⟨hP, hlive⟩ := hi.key_live ho
      rw [hP] at hN
      injection hN with hN
      subst hN
      obtain ⟨c, hc⟩ := (hlive y).mp hy
      obtain ⟨oy, hoy, hlt⟩ := hi.lev x n ho c y (live_mem_key hc)
      have h1 : n.level ≤ L + 1 := hl
      exact hi.liveHeight L y oy hoy (by omega)

/-- The live height of the model's root, for BergDB's key tree: if the space
root's level is at most K after every transaction (and at the start), then
after every transaction every chain of live pointers down from the root has
at most K + 2 steps. -/
theorem bridge_liveHeight (hm : MeetsBridge p h) (al : SIS.Algo BVal Nat) (K : Nat)
    (hK : ∀ j, j ≤ h.txs.length → ∀ y n, (h.tree j).root = some y →
      (h.tree j).obj y = some (.key n) → n.level ≤ K) :
    ∀ t, t ≤ h.ts.length →
      SIS.LiveHeightLe h.spec (SIS.run h.spec al (h.ts.take t)).P t (K + 2) SIS.root := by
  intro t ht
  have ht' : t ≤ h.txs.length := by rw [h.ts_length] at ht; exact ht
  rw [run_P h al t ht']
  have hi := hm.binv t ht'
  obtain ⟨n0, z, nz, y, n, h0, hl0, hz, hlz, hly, hroot, hy, hny, hs0, hsz⟩ := hi.link
  intro N hN y1 hy1
  rw [h0] at hN
  injection hN with hN
  subst hN
  rw [hl0] at hy1
  rw [List.mem_singleton.mp hy1]
  intro N hN y2 hy2
  rw [hz] at hN
  injection hN with hN
  subst hN
  rw [hly] at hy2
  rw [List.mem_singleton.mp hy2]
  exact hi.liveHeight K y _ hy (hK t ht' y n hroot hy)

end Contract
