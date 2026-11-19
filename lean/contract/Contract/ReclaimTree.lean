/-
The contract package (bergdb 030-24): RC2 and RC3, the two conditions of
reclaim's contract RC that are about the tree, for BergDB's key tree
(bergdb 030-22, sections 4.1 and 4.2).

RC3, a value below every index node a read at the iteration's end e reaches,
follows from the writer's contract (`rc3_tree`): the contract's invariants say
that every key node a live klong names has a live klong, and that a segment
leaf's live klong names a value or a non-empty key node; so, if some key is
live at e (reclaim's last step puts its row), every key node a read at e
reaches has a value below it, and so has the top node of time e. As in the
writer's contract, a tree after transaction j is read at time j
(`(h.tree j).at j`).

RC2, every value that a read at e reaches made at the cut c or later, is
stated in the contract's words (`RC2Tree`: the value node that each live key
names at e was made by a transaction from c on), carried to the model
(`rc2_of_tree`), and follows from the iteration (`rc2_of_iteration`):
`IterationOK`, every key live before the iteration's first step s whose value
node was made before c is put again by a transaction from s to e, and VAL-NEW
(`ValNew`, 030-22, section 2.3), a put makes a new value node that the key
names, and a key that a transaction does not write keeps its value node.
That Java's iteration meets `IterationOK` is tested (C-CUT's RC2 at every
cut; 027-13, section 3, REWRITES); VAL-NEW is the writer's.
-/
import Contract.ReclaimReads
import Contract.Proof.ReclaimTree

namespace Contract

open SIS.Check (BVal)

/-! ## The value nodes of the live keys -/

/-- What the live klong (c, y) of a key node holds, with value nodes by id:
as `klongList`, the key with the id of the value node its klong names. -/
def idKlongList (s : Tree) (leaf : Bool) (sub : NodeId → List (Key × NodeId)) (c : Nat)
    (y : NodeId) : List (Key × NodeId) :=
  if leaf then
    if isLong c then (sub y).map (fun ky => (c :: ky.1, ky.2))
    else
      match s.obj y with
      | some (.val _) => [([c], y)]
      | _ => []
  else sub y

/-- What key node x holds, with value nodes by id: as `listAt`. -/
def idListAt (s : Tree) : Nat → NodeId → List (Key × NodeId)
  | 0, _ => []
  | f + 1, x =>
    match s.obj x with
    | some (.key n) =>
      (live n.ks).flatMap (fun cy => idKlongList s n.leaf (fun y => idListAt s f y) cy.1 cy.2)
    | _ => []

/-- The live keys of a tree with the value nodes their klongs name: as
`contents`, by id instead of by value. -/
def idContents (s : Tree) : List (Key × NodeId) :=
  match s.root with
  | some r => idListAt s (s.fuel r) r
  | none => []

/-- Transaction i of the history made node y (the trace's NEW lines; 0 is the
start's change). -/
def madeAt (h : BHist) (i : Nat) (y : NodeId) : Bool :=
  ((h.chs.getD i { new := [], adds := [] }).new.any (·.id == y))

/-- The keys a transaction puts. -/
def putKeys (ops : List Op) : List Key :=
  ops.filterMap (fun op => match op with
    | .put k _ => some k
    | .del _ => none)

/-! ## RC3 -/

/-- **RC3 for BergDB's key tree** (bergdb 030-24; 030-22, section 4.1): if some
key is live after transaction e, every written index node that a read at e
reaches has a value below it then. -/
theorem rc3_tree {p : Params} {h : BHist} {top : Nat → Top} (hm : MeetsFull p h top)
    (hM : 1 ≤ p.M) (al : SIS.Algo BVal Nat) {e : Nat} (he : e ≤ h.txs.length)
    (hne : contents ((h.tree e).at e) ≠ []) :
    RC3 h.spec (SIS.run h.spec al (h.ts.take e)) e := by
  have hi := hm.meetsBridge.binv e he
  obtain ⟨n0, z, nz, y, ny, h0, hl0, hz, hlz, hly, hroot, hy, hny, -, -⟩ := hi.link
  obtain ⟨n, hn, hgr, hne'⟩ := hm.root_good hM he hroot
  rw [hy] at hn
  obtain rfl : ny = n := by injection hn with h1; injection h1
  rw [hi.timely.at_eq] at hne
  have hner := hne' hne
  -- Below a sound key node with a live klong, the model reaches a data node.
  have hval : ∀ x m lo' hi', (h.tree e).obj x = some (.key m) → live m.ks ≠ [] →
      Good (h.tree e) x lo' hi' → ∃ d M,
        d ∈ SIS.reachFrom h.spec (h.P e) e x
          { level := m.level, isData := false, hist := entriesOf m.ks } ∧
        (h.P e).get? d = some M ∧ M.isData = true := by
    intro x m lo' hi' hxm hm hg
    obtain ⟨v, w, hv, hvr⟩ := hg.val_below (m.level + 1) hxm hm (by omega)
    obtain ⟨hP, -⟩ := hi.key_live hxm
    have hrv := hi.rep.rep v (.val w) hv
    obtain ⟨t, ht⟩ := hrv
    exact ⟨v, _, hi.walk_reachFrom _ x _ hP v hvr, ht, rfl⟩
  unfold RC3
  rw [run_P h al e he]
  intro x nx hx hnd hw hr
  rcases hi.reach3 h0 hl0 hz hly hroot hy ((SIS.reachable_iff _ _ _ _).mp hr) with
    rfl | rfl | hxr
  · -- The root is not written.
    simp [SIS.written, BHist.spec, SIS.Check.bspec] at hw
  · -- The top node: the space root is below it.
    rw [hz] at hx
    injection hx with hx
    subst hx
    obtain ⟨d, M, hd, hM', hMd⟩ := hval y ny 0 none hy hner hgr
    obtain ⟨hPy, -⟩ := hi.key_live hy
    exact ⟨d, M, SIS.reachFrom_child_sub h.spec (by rw [hly]; exact List.mem_singleton_self y)
      hPy hny d hd, hM', hMd⟩
  · -- A node of the tree.
    unfold reach at hxr
    rw [hroot] at hxr
    rcases hgr.reach_cases _ x hxr with rfl | ⟨w, hw'⟩ | ⟨m, lo', hi', hxm, hm, hg⟩
    · obtain ⟨hPy, -⟩ := hi.key_live hy
      rw [hPy] at hx
      injection hx with hx
      subst hx
      exact hval x ny 0 none hy hner hgr
    · have hrx := hi.rep.rep x (.val w) hw'
      obtain ⟨t, ht⟩ := hrx
      rw [ht] at hx
      injection hx with hx
      subst hx
      simp at hnd
    · obtain ⟨hPx, -⟩ := hi.key_live hxm
      rw [hPx] at hx
      injection hx with hx
      subst hx
      exact hval x m lo' hi' hxm hm hg

/-! ## RC2 -/

/-- **RC2 in the contract's words**: every value node that a live key names
after transaction e was made by a transaction from c to e. -/
def RC2Tree (h : BHist) (c e : Nat) : Prop :=
  ∀ k y, (k, y) ∈ idContents ((h.tree e).at e) → ∃ i, c ≤ i ∧ i ≤ e ∧ madeAt h i y = true

/- Not yet proved (bergdb 030-24):
/-- RC2 in the contract's words gives the model's RC2. -/
theorem rc2_of_tree {p : Params} {h : BHist} {top : Nat → Top} (hm : MeetsFull p h top)
    (hM : 1 ≤ p.M) (al : SIS.Algo BVal Nat) {c e : Nat} (he : e ≤ h.txs.length)
    (h2 : RC2Tree h c e) :
    RC2 h.spec (SIS.run h.spec al (h.ts.take e)) e c := by
  (proof to come)
-/

/-- **VAL-NEW** (bergdb 030-22, section 2.3): in each transaction, a put makes
a new value node, which the key names after it, and a key that the
transaction does not write keeps its value node. -/
def ValNew (h : BHist) : Prop :=
  ∀ j (hj : j < h.txs.length), ∀ k,
    (k ∈ putKeys h.txs[j].ops →
      ∃ y, (idContents ((h.tree (j + 1)).at (j + 1))).lookup k = some y ∧
        madeAt h (j + 1) y = true) ∧
    (k ∉ h.txs[j].ops.map Op.key →
      (idContents ((h.tree (j + 1)).at (j + 1))).lookup k =
        (idContents ((h.tree j).at j)).lookup k)

/-- **Reclaim's iteration** in the contract's words (bergdb 030-22, section
4.2), with its cut c, its first step s and its last step e: c ≤ s ≤ e, and
every key live before s whose value node was made before c is written (put
again, or deleted) by a transaction from s to e: a step rewrites it, or the
user wrote it first. -/
def IterationOK (h : BHist) (c s e : Nat) : Prop :=
  c ≤ s ∧ 1 ≤ s ∧ s ≤ e ∧ e ≤ h.txs.length ∧
  ∀ k y, (idContents ((h.tree (s - 1)).at (s - 1))).lookup k = some y →
    (∃ i, i < c ∧ madeAt h i y = true) →
    ∃ j, ∃ hj : j < h.txs.length, s ≤ j + 1 ∧ j + 1 ≤ e ∧ k ∈ h.txs[j].ops.map Op.key

/- Not yet proved (bergdb 030-24):
/-- **RC2 from the iteration** (bergdb 030-24): with VAL-NEW, an iteration that
meets `IterationOK` leaves every live key's value node made at c or later. -/
theorem rc2_of_iteration {p : Params} {h : BHist} {top : Nat → Top} (hm : MeetsFull p h top)
    (hM : 1 ≤ p.M) (hv : ValNew h) {c s e : Nat} (hit : IterationOK h c s e) :
    RC2Tree h c e := by
  (proof to come)
-/

/-! ## The cuts of a run, with the iteration -/

/-- The cut marks of a run meet reclaim's contract with RC2 and RC3 in the
contract's words: at each mark of a cut c, c is at or after every earlier
mark's cut, and some iteration (s, e) with the cut c meets `IterationOK`, some
key is live after e (the iteration's last step puts its row), e is at most
the first available time, and RC4 holds (Java's two waits). -/
def CutsMeetIter (h : BHist) (al : SIS.Algo BVal Nat)
    (cs : List (Nat × Option Nat × List SIS.HCacheOp)) : Prop :=
  ∀ j (hjl : j < cs.length) c, cs[j].2.1 = some c →
    (∀ i (hi : i < j) c', cs[i].2.1 = some c' → c' ≤ c) ∧
    ∃ s e, IterationOK h c s e ∧ contents ((h.tree e).at e) ≠ [] ∧
      e ≤ SIS.lastFa (SIS.run h.spec al (h.ts.take (j + 1))).S ∧ RC4 h.spec al h.ts e (j + 1)

/- Not yet proved (bergdb 030-24):
/-- With VAL-NEW, cuts that meet the iteration meet RC. -/
theorem cutsMeetRC_of_iter {p : Params} {h : BHist} {top : Nat → Top} (hm : MeetsFull p h top)
    (hM : 1 ≤ p.M) (hv : ValNew h) (al : SIS.Algo BVal Nat)
    {cs : List (Nat × Option Nat × List SIS.HCacheOp)} (hcs : cs.map (·.1) = h.ts)
    (hit : CutsMeetIter h al cs) :
    CutsMeetRC h.spec al cs := by
  (proof to come)
-/

end Contract

namespace Contract.PE

variable {cf : Cfg}

/- Not yet proved (bergdb 030-24):
/-- **PE meets VAL-NEW** (bergdb 030-24; 030-22, section 2.3): every history PE
writes makes a new value node for each put, which the key names after the
transaction, and keeps the value node of each key it does not write. -/
theorem pe_valNew (hcf : cf.Ok) (hcap : cf.topBase ≤ 2 ^ 62) {txs : List (List Op)}
    {h : BHist} {top : Nat → Top} (hlen : txs.length < 2 ^ 48 - 1)
    (hk : ∀ ops ∈ txs, (ops.map Op.key).Nodup) (hh : peHist cf txs = some (h, top)) :
    ValNew h := by
  (proof to come)
-/

/- Not yet proved (bergdb 030-24):
/-- **Reclaim chooses only safe cuts, for PE** (bergdb 030-24): for every history
PE writes, with Java's still-dirty test and the marking, policies that read no
cut stream, and cuts whose iterations meet `IterationOK` (with a key live at
each iteration's end, the end at most the first available time, and Java's
two waits), Java's get and scan after the run with handles, evictions and
restarts from the cut streams are right at every time from the first
available time on. -/
theorem pe_reclaim_reads (hcf : cf.Ok) (hcap : cf.topBase ≤ 2 ^ 62) {txs : List (List Op)}
    {h : BHist} {top : Nat → Top} (hlen : txs.length < 2 ^ 48 - 1)
    (hk : ∀ ops ∈ txs, (ops.map Op.key).Nodup) (hh : peHist cf txs = some (h, top))
    (hM : 1 ≤ cf.params.M)
    (al : SIS.Algo SIS.Check.BVal Nat) (hj : al.stillDirty = SIS.javaTest h.spec)
    (hmk : al.mark = true) (hpol : SIS.PolicyCutOK al)
    (cs : List (Nat × Option Nat × List SIS.HCacheOp)) (hcs : cs.map (·.1) = h.ts)
    (hit : CutsMeetIter h al cs)
    (hreads : ∀ j (hjl : j < cs.length), cs[j].2.1 = none → ∀ t,
      SIS.HCacheOp.read t ∈ cs[j].2.2 →
      SIS.lastFa (SIS.run h.spec al ((cs.map (·.1)).take (j + 1))).S ≤ t ∧ t ≤ j + 1)
    {t : Nat} (hft : SIS.lastFa (SIS.run h.spec al h.ts).S ≤ t) (htn : t ≤ h.txs.length)
    (mid : Bool) (s : Tree) (tp : Top) :
    let V := SIS.view h.spec (SIS.runHandlesCut h.spec al cs).1.P t
    HoldsView V (kindOf (peKind cf) V) t s →
      TopFrom (SIS.lastFa (SIS.run h.spec al h.ts).S) (top h.txs.length) tp →
      JReadsRight s tp t mid (h.txs.map (·.ops)) := by
  (proof to come)
-/

end Contract.PE
