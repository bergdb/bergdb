import SIS.Tree.ScanHistorySetup

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The scan loop observes only the old closed set, at any result limit. -/
theorem scanGo_of_readClosed (p : Params) (P Q : Struct BVal) (t : Time)
    (hext : ReadExtension p t P Q) (S : NodeId → Prop)
    (hclosed : ReadClosed p (viewOf P) t S) (req : ScanReq) (limit fuel : Nat)
    (ch : Chain) (acc : List Kvt) (hc : ReadChain S ch.links) :
    scanGo p (viewOf Q) t req limit fuel ch acc =
      scanGo p (viewOf P) t req limit fuel ch acc := by
  induction fuel generalizing ch acc with
  | zero => rfl
  | succ fuel ih =>
    simp only [scanGo]
    split
    · rfl
    · have he := nextGo_of_readClosed p P Q t hext S hclosed req (2 * p.fuel + 2) ch hc
      rw [he.1]
      cases hn : nextGo p (viewOf P) t req (2 * p.fuel + 2) ch with
      | mk result next =>
        cases result with
        | none => rfl
        | some kv =>
          simp only
          apply ih
          simpa only [hn] using he.2

/-- A fault-free old tree gives the same complete scan after any read
extension. No invariant of the later structure is required; requests need
not be well formed for historical preservation. -/
theorem scan_of_readExtension (p : Params) (P Q : Struct BVal) (t : Time)
    (hext : ReadExtension p t P Q) (hkinds : HighKindsOK p P) (hdata : DataEntriesOK P)
    (hinv : InvOK p P t) (req : ScanReq) (limit : Nat) :
    scan p (viewOf Q) t req limit = scan p (viewOf P) t req limit := by
  have hclosed := readClosed_walkNode p P t hkinds hdata
  unfold InvOK faultsAt at hinv
  cases hr : rootAt (viewOf P) t with
  | none => simp [hr] at hinv
  | some r =>
    simp only [hr] at hinv
    have hnode : WalkNode p P t r := ⟨p.fuel, 0, none, true, true, hinv⟩
    have he := chainSetup_of_readClosed p P Q t hext (WalkNode p P t) hclosed req r hnode
    unfold scan
    rw [hext.root r hr, hr]
    simp only
    rw [he.1]
    exact scanGo_of_readClosed p P Q t hext (WalkNode p P t) hclosed req limit limit _ [] he.2

/-- Scan preservation at an old time requires only the invariant of the
prefix ending at that time, including when later transactions fail. -/
theorem treeRun_scan_eq_prefix_of_invariant (p : Params) (ts : List Tx) (t : Time)
    (ht : t ≤ ts.length) (hinv : InvOK p (treeRun p (ts.take t)) t)
    (req : ScanReq) (limit : Nat) :
    scan p (viewOf (treeRun p ts)) t req limit =
      scan p (viewOf (treeRun p (ts.take t))) t req limit :=
  scan_of_readExtension p _ _ t (treeRun_readExtension_prefix p ts t ht)
    (treeRun_highKindsOK p (ts.take t)) (treeRun_dataEntriesOK p (ts.take t)) hinv req limit

theorem treeRun_scan_eq_prefix (p : Params) (hinv : InvPreserved p)
    (ts : List Tx) (hw : Within p ts) (t : Time) (ht : t ≤ ts.length)
    (req : ScanReq) (limit : Nat) :
    scan p (viewOf (treeRun p ts)) t req limit =
      scan p (viewOf (treeRun p (ts.take t))) t req limit := by
  have hlen : (ts.take t).length = t := by simp only [List.length_take, Nat.min_eq_left ht]
  have hi := (hinv (ts.take t) (within_take p ts hw t) t (by rw [hlen]; exact Nat.le_refl _)).1
  exact treeRun_scan_eq_prefix_of_invariant p ts t ht hi req limit

/-- Latest-time scan correctness, with the full API range, direction and
limit semantics. This is a remaining reader/writer refinement obligation,
not an assumption about any historical snapshot. -/
def LatestScanOK (p : Params) : Prop :=
  ∀ ts, Within p ts → ∀ (req : ScanReq) (limit : Nat), req.wf = true →
    (scan p (viewOf (treeRun p ts)) ts.length req limit).map (fun kv => (kv.key, kv.h)) =
      refScan ts ts.length req limit

theorem refKvs_take_eq (ts : List Tx) (t : Time) :
    refKvs (ts.take t) t = refKvs ts t := by
  simp only [refKvs, refGet, List.take_take, Nat.min_self]

theorem refScan_take_eq (ts : List Tx) (t : Time) (req : ScanReq) (limit : Nat) :
    refScan (ts.take t) t req limit = refScan ts t req limit := by
  simp only [refScan, refKvs_take_eq]

/-- TP11 reduces to latest-time invariant and scan correctness. The former
is weaker than TP7; no invariant of later states is needed. -/
theorem scanOK_of_latest_invariant (p : Params) (hinv : LatestInvOK p)
    (hlatest : LatestScanOK p) : ScanOK p := by
  intro ts hw t ht req limit hreq
  have hlen : (ts.take t).length = t := by simp only [List.length_take, Nat.min_eq_left ht]
  have hwithin := within_take p ts hw t
  have hi := hinv (ts.take t) hwithin
  rw [hlen] at hi
  rw [treeRun_scan_eq_prefix_of_invariant p ts t ht hi req limit]
  have he := hlatest (ts.take t) hwithin req limit hreq
  rw [hlen, refScan_take_eq ts t req limit] at he
  exact he

/-- TP11 from TP7 and the explicit remaining latest-time scan obligation.
Neither premise is claimed proved here. -/
theorem scanOK_of_latest (p : Params) (hinv : InvPreserved p)
    (hlatest : LatestScanOK p) : ScanOK p :=
  scanOK_of_latest_invariant p (fun ts hw => (hinv ts hw ts.length (Nat.le_refl _)).1) hlatest

end SIS.Tree
