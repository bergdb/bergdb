/-
The contract package (bergdb 030-24): the read half of T-SCHEME proved, so
that every theorem after cuts holds given RC at each cut alone.

The independent search made beside bergdb 030-23 found and proved, in a
scratch study, the read invariant `OldReads.OldReadsGood` (its I1 and I2): in
every reached state, a version that a read at a time t may follow and that is
written at or before the startup pos s is good at min t s, and its node is
reachable then (`OldReads.oldReadsGood_st`, Contract/Proof/OldReadsClosure.lean,
from RunOK and Java's Rule A alone; no A6', no reclaim). With Lemma G's
argument, a version good at a time from the iteration's end e on at which its
node is reachable is at the cut or later (`OldReads.reads_ge_cut`), so RC2,
RC3 and the first wait (e ≤ s) give `CutOK`'s part 2 (`OldReads.rc_reads`).
Its proofs are in Contract/Proof/OldReads*.lean, taken over with their names.

So `TSchemeReads`, 030-23's open half, holds for every spec and algorithm
(`tschemeReads_holds`); with `rc_dref` (A6'), RC gives `CutOK`
(`cutOK_of_rc`); and the theorems after cuts need only RC at each cut
(`full_cut_of_rc`, `cut_keeps_top_of_rc`, `cut_java_reads_of_rc`), for PE's
histories too (`PE.pe_cut_java_reads`).
-/
import Contract.ReclaimGis
import Contract.Proof.OldReadsCut
import Contract.Proof.OldReadsDirty
import Contract.Proof.PeFullProved

namespace Contract

open SIS.Check (BVal)
open SIS (Spec Algo DB Version reachable good lastSp lastFa inD run ReadsPhys RunOK javaTest CutOK
  cutMax)

variable {V T : Type} [DecidableEq V]

section

variable {sp : Spec V T} {al : Algo V T} {ts : List T}

/-- **The read invariant** (the independent search's I1 and I2; bergdb 030-24):
in the state after the first k transactions of a run that meets `RunOK`, with
Java's still-dirty test, every version that a read at a time t ≤ k may follow
(`ReadsPhys`) and that is written at or before the startup pos s is good at
min t s, and its node is reachable then. -/
theorem old_reads_good (hok : RunOK sp al ts) (hj : al.stillDirty = javaTest sp) {k : Nat}
    (hk : k ≤ ts.length) :
    let db := run sp al (ts.take k)
    ∀ t, t ≤ k → ∀ w, ReadsPhys sp db.S db.P db.D t w → w.recNo ≤ lastSp db.S →
      good sp db.S db.P (min t (lastSp db.S)) w = true ∧
        reachable sp db.P (min t (lastSp db.S)) w.node = true :=
  OldReads.oldReadsGood_st hok hj hk

/-- **Part 2 needs only the first wait** (the independent search's remark;
bergdb 030-24): with c ≤ e ≤ fa(k), RC2 and RC3 at e, and the startup pos of
record k at e or later, every version that a read at a time from the first
available time to k may follow is at the cut or later. Java's second wait
(RC4's v) is needed for D's references (`rc_dref`), not for reads. -/
theorem rc_part2_first_wait (hok : RunOK sp al ts) (hj : al.stillDirty = javaTest sp)
    {c e k : Nat} (hk : k ≤ ts.length) (hce : c ≤ e) (hef : e ≤ lastFa (run sp al (ts.take k)).S)
    (h2 : RC2 sp (run sp al (ts.take e)) e c) (h3 : RC3 sp (run sp al (ts.take e)) e)
    (hsp : e ≤ lastSp (run sp al (ts.take k)).S) :
    let db := run sp al (ts.take k)
    ∀ t w, lastFa db.S ≤ t → t ≤ k → ReadsPhys sp db.S db.P db.D t w → c ≤ w.recNo := by
  dsimp only
  intro t w hft htk hr
  have hst := SIS.algOK_of sp al (Or.inl hj)
  have h1 := lastSp_take_le hok hst k
  exact OldReads.rc_reads hok hj e k c hce (by omega) hk h2 h3 hsp t w (by omega) htk hr

/-- **`CutOK`'s part 2 under RC** (bergdb 030-24): every version that a read at
a time from the first available time to k may follow is at the cut or later.
From RunOK and Java's still-dirty test; of RC it uses c ≤ e ≤ fa(k), RC2, RC3
and e ≤ s(k), which RC4 gives (the first wait). -/
theorem rc_part2 (hok : RunOK sp al ts) (hj : al.stillDirty = javaTest sp) {c e k : Nat}
    (hk : k ≤ ts.length) (hrc : RC sp al ts c e k) :
    let db := run sp al (ts.take k)
    ∀ t w, lastFa db.S ≤ t → t ≤ k → ReadsPhys sp db.S db.P db.D t w → c ≤ w.recNo := by
  dsimp only
  intro t w hft htk hr
  have hst := SIS.algOK_of sp al (Or.inl hj)
  obtain ⟨hce, hef, hrw, hlb, v, hv1, hv2⟩ := hrc
  have h1 := lastSp_take_le hok hst v
  have h2 := lastSp_take_le hok hst k
  exact OldReads.rc_reads hok hj e k c hce (by omega) hk hrw hlb
    (show e ≤ lastSp (run sp al (ts.take k)).S by omega) t w (by omega) htk hr

/-- **`CutOK` under RC** (bergdb 030-24), for a run with TREE and A6'
(`EvictRunOK`, which the bridge gives for BergDB's key tree): parts 1, 3 and 4
by `rc_parts` and `rc_dref`, part 2 by `rc_part2`. -/
theorem cutOK_of_rc (hok : RunOK sp al ts) (hev : SIS.EvictRunOK sp al ts)
    (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) {c e k : Nat}
    (hk : k ≤ ts.length) (hrc : RC sp al ts c e k) :
    CutOK sp c (run sp al (ts.take k)) k :=
  cutOK_of_reads hok hev hj hmk hk hrc (rc_part2 hok hj hk hrc)

end

/-- **030-23's open half holds** (bergdb 030-24): `TSchemeReads` for every spec
and algorithm. -/
theorem tschemeReads_holds (sp : Spec V T) (al : Algo V T) : TSchemeReads sp al := by
  intro hj _ ts hok _ c e k hk hrc
  exact rc_part2 hok hj hk hrc

/-- RC at every cut mark gives the premise `hcut` of the theorems after cuts,
for a run with A6'. -/
theorem hcut_of_cutsMeetRC {sp : Spec V T} {al : Algo V T}
    (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true)
    {cs : List (T × Option Nat × List SIS.HCacheOp)} (hok : RunOK sp al (cs.map (·.1)))
    (hev : SIS.EvictRunOK sp al (cs.map (·.1))) (hrc : CutsMeetRC sp al cs) :
    ∀ j (hjl : j < cs.length) c, cs[j].2.1 = some c →
      CutOK sp (cutMax ((cs.take (j + 1)).map (·.2.1))) (run sp al ((cs.map (·.1)).take (j + 1)))
        (j + 1) :=
  hcut_of_reads (tschemeReads_holds sp al) hj hmk hok hev hrc

section

variable {p : Params} {h : BHist} {top : Nat → Top} {kind : Nat → Bool}

/-- **Reclaim's cut with eviction, given RC at each cut** (bergdb 030-24):
`full_cut` with `CutsMeetRC` in place of `CutOK`, and no other new premise. -/
theorem full_cut_of_rc (hm : MeetsFull p h top) (al : SIS.Algo BVal Nat)
    (hj : al.stillDirty = SIS.javaTest h.spec) (hmk : al.mark = true)
    (hpol : SIS.PolicyCutOK al) (cs : List (Nat × Option Nat × List SIS.HCacheOp))
    (hcs : cs.map (·.1) = h.ts)
    (hrc : CutsMeetRC h.spec al cs)
    (hreads : ∀ j (hjl : j < cs.length), cs[j].2.1 = none → ∀ t,
      SIS.HCacheOp.read t ∈ cs[j].2.2 →
      SIS.lastFa (SIS.run h.spec al ((cs.map (·.1)).take (j + 1))).S ≤ t ∧ t ≤ j + 1) :
    let db := (SIS.runHandlesCut h.spec al cs).1
    let r := SIS.run h.spec al (cs.map (·.1))
    db.S = SIS.cutStream (SIS.cutMax (cs.map (·.2.1))) r.S ∧ db.D = r.D ∧
      SIS.SameFrom h.spec (SIS.lastFa r.S) cs.length db.P r.P :=
  full_cut_reads hm al hj hmk (tschemeReads_holds _ _) hpol cs hcs hrc hreads

/-- **The cut keeps the top nodes that Java's search reads, given RC at each
cut** (bergdb 030-24): `cut_keeps_top` with `CutsMeetRC` in place of `CutOK`. -/
theorem cut_keeps_top_of_rc (hm : MeetsFull p h top)
    (al : SIS.Algo BVal Nat) (hj : al.stillDirty = SIS.javaTest h.spec) (hmk : al.mark = true)
    (hpol : SIS.PolicyCutOK al) (cs : List (Nat × Option Nat × List SIS.HCacheOp))
    (hcs : cs.map (·.1) = h.ts)
    (hrc : CutsMeetRC h.spec al cs)
    (hreads : ∀ j (hjl : j < cs.length), cs[j].2.1 = none → ∀ t,
      SIS.HCacheOp.read t ∈ cs[j].2.2 →
      SIS.lastFa (SIS.run h.spec al ((cs.map (·.1)).take (j + 1))).S ≤ t ∧ t ≤ j + 1)
    {t : Nat} (hft : SIS.lastFa (SIS.run h.spec al h.ts).S ≤ t) (htn : t ≤ h.txs.length)
    {zn : NodeId × TopNode} (hz : topAt (top h.txs.length) t = some zn) :
    let P' := (SIS.runHandlesCut h.spec al cs).1.P
    viewTop (SIS.view h.spec P' t) = some zn.1 ∧
      ∃ nz, SIS.view h.spec P' t zn.1 = some nz ∧ nz.hist = topEntries zn.2 :=
  cut_keeps_top_reads hm al hj hmk (tschemeReads_holds _ _) hpol cs hcs hrc hreads hft htn hz

/-- **Java's reads after cuts, given RC at each cut** (bergdb 030-24):
`cut_java_reads` with `CutsMeetRC` in place of `CutOK`: after the run with
handles, reads from the first available time on, evictions, and restarts from
cut streams whose cuts meet RC, Java's get and scan at a time from the first
available time on are right. -/
theorem cut_java_reads_of_rc (hm : MeetsFull p h top) (hM : 1 ≤ p.M) (hkd : KindsOK kind h)
    (al : SIS.Algo BVal Nat) (hj : al.stillDirty = SIS.javaTest h.spec) (hmk : al.mark = true)
    (hpol : SIS.PolicyCutOK al) (cs : List (Nat × Option Nat × List SIS.HCacheOp))
    (hcs : cs.map (·.1) = h.ts)
    (hrc : CutsMeetRC h.spec al cs)
    (hreads : ∀ j (hjl : j < cs.length), cs[j].2.1 = none → ∀ t,
      SIS.HCacheOp.read t ∈ cs[j].2.2 →
      SIS.lastFa (SIS.run h.spec al ((cs.map (·.1)).take (j + 1))).S ≤ t ∧ t ≤ j + 1)
    {t : Nat} (hft : SIS.lastFa (SIS.run h.spec al h.ts).S ≤ t) (htn : t ≤ h.txs.length)
    (mid : Bool) (s : Tree) (tp : Top) :
    let V := SIS.view h.spec (SIS.runHandlesCut h.spec al cs).1.P t
    HoldsView V (kindOf kind V) t s →
      TopFrom (SIS.lastFa (SIS.run h.spec al h.ts).S) (top h.txs.length) tp →
      JReadsRight s tp t mid (h.txs.map (·.ops)) :=
  cut_java_reads_reads hm hM hkd al hj hmk (tschemeReads_holds _ _) hpol cs hcs hrc hreads hft htn
    mid s tp

end

end Contract

namespace Contract.PE

variable {cf : Cfg}

/-- **Java's reads after reclaim's cuts, for every history PE writes**
(bergdb 030-24): for parameters with `Cfg.Ok` and the top nodes' level at most
2^62, fewer than 2^48 - 1 transactions of distinct keys, Java's still-dirty test
and the marking, policies that read no cut stream, and cuts that meet RC, a
tree that holds the view after the run with handles, evictions and restarts
from the cut streams at a time from the first available time on, read with a
top that holds the history's top from there, gives Java's get and scan right. -/
theorem pe_cut_java_reads (hcf : cf.Ok) (hcap : cf.topBase ≤ 2 ^ 62) {txs : List (List Op)}
    {h : BHist} {top : Nat → Top} (hlen : txs.length < 2 ^ 48 - 1)
    (hk : ∀ ops ∈ txs, (ops.map Op.key).Nodup) (hh : peHist cf txs = some (h, top))
    (hM : 1 ≤ cf.params.M)
    (al : SIS.Algo SIS.Check.BVal Nat) (hj : al.stillDirty = SIS.javaTest h.spec)
    (hmk : al.mark = true) (hpol : SIS.PolicyCutOK al)
    (cs : List (Nat × Option Nat × List SIS.HCacheOp)) (hcs : cs.map (·.1) = h.ts)
    (hrc : CutsMeetRC h.spec al cs)
    (hreads : ∀ j (hjl : j < cs.length), cs[j].2.1 = none → ∀ t,
      SIS.HCacheOp.read t ∈ cs[j].2.2 →
      SIS.lastFa (SIS.run h.spec al ((cs.map (·.1)).take (j + 1))).S ≤ t ∧ t ≤ j + 1)
    {t : Nat} (hft : SIS.lastFa (SIS.run h.spec al h.ts).S ≤ t) (htn : t ≤ h.txs.length)
    (mid : Bool) (s : Tree) (tp : Top) :
    let V := SIS.view h.spec (SIS.runHandlesCut h.spec al cs).1.P t
    HoldsView V (kindOf (peKind cf) V) t s →
      TopFrom (SIS.lastFa (SIS.run h.spec al h.ts).S) (top h.txs.length) tp →
      JReadsRight s tp t mid (h.txs.map (·.ops)) := by
  obtain ⟨hm, hkd⟩ := pe_full hcf hcap hlen hk hh
  exact cut_java_reads_of_rc hm hM hkd al hj hmk hpol cs hcs hrc hreads hft htn mid s tp

end Contract.PE
