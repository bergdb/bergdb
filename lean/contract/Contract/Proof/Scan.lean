/-
The contract package (bergdb 030-04): a scan is right. On a tree that meets
the invariants, `scan` gives what a scan of the plain map of the tree's
contents gives (`scan_contents`).
-/
import Contract.Proof.Good

namespace Contract

variable {s : Tree}

/-- TP11 for one tree: on a tree that meets the invariants, a scan gives the
keys and values of the contents in its range, in order, the first `limit`. -/
theorem scan_contents {p : Params} (h : invOk p s = true) (req : ScanReq) (hreq : req.wf = true)
    (limit : Nat) : scan s req limit = refScan (contents s) req limit := by
  sorry

end Contract
