/-
bergdb 030-21, part 2: PE's histories meet `MeetsFull` (BridgeTop.lean) with
no premise but the parameters' and distinct keys: `pe_full_of_prov` and
`pe_crash_reads_of_prov` (PeFull.lean) with PE's provenance (`Prov`) proved
for every transaction of the history (`pe_prov_hist`, PeProv.lean).
-/
import Contract.Proof.PeFull
import Contract.Proof.PeProv

namespace Contract.PE

variable {cf : Cfg}

/-- **Every history PE writes from the empty tree meets `MeetsFull` and
K-LEVEL** (030-21 part 2): for parameters with `Cfg.Ok` and the top nodes'
level at most 2^62, fewer than 2^48 - 1 transactions, each of distinct keys.
So recovery, restarts, lazy reading, eviction with handles and reclaim's
safe cuts (BridgeFull.lean) hold for PE. -/
theorem pe_full (hcf : cf.Ok) (hcap : cf.topBase ≤ 2 ^ 62) {txs : List (List Op)}
    {h : BHist} {top : Nat → Top} (hlen : txs.length < 2 ^ 48 - 1)
    (hk : ∀ ops ∈ txs, (ops.map Op.key).Nodup) (hh : peHist cf txs = some (h, top)) :
    MeetsFull cf.params h top ∧ KindsOK (peKind cf) h :=
  pe_full_of_prov hcf hcap hlen hk hh (pe_prov_hist hcf hk hh)

/-- **Reads after a crash, for PE**: after a crash that keeps the first k + 1
records of PE's history, startup gives a structure whose reader at every time
t up to k answers every get and scan as the plain map after the first t
transactions. -/
theorem pe_crash_reads (hcf : cf.Ok) (hcap : cf.topBase ≤ 2 ^ 62) {txs : List (List Op)}
    {h : BHist} {top : Nat → Top} (hlen : txs.length < 2 ^ 48 - 1)
    (hk : ∀ ops ∈ txs, (ops.map Op.key).Nodup) (hh : peHist cf txs = some (h, top))
    (al : SIS.Algo SIS.Check.BVal Nat) (hst : al.stillDirty = SIS.javaTest h.spec) {k t : Nat}
    (hkl : k ≤ h.txs.length) (htk : t ≤ k) :
    let V := SIS.view h.spec (SIS.startup h.spec ((SIS.run h.spec al h.ts).S.take (k + 1))).P t
    ReadsRight V (kindOf (peKind cf) V) (h.txs.map (·.ops)) t :=
  pe_crash_reads_of_prov hcf hcap hlen hk hh (pe_prov_hist hcf hk hh) al hst hkl htk

end Contract.PE
