import SIS.Tree.ScanAdequacy

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The target compare value used at one level of setup. -/
def setupTarget (forward : Bool) (start : List Int) (index : Nat) : Int :=
  match start[index]? with
  | some s => s
  | none => if forward then cvHi else cvLo

/-- Setup's node search, separated out for its live-pointer specification. -/
def setupChoice (n : KNode) (t : Time) (forward hasDiff : Bool) (sks : Int) : Option Found :=
  if hasDiff then (if forward then n.searchLt t cvHi else n.searchGt t cvLo)
  else if forward then n.searchLte t sks
  else if n.leaf then n.searchGte t sks
  else n.searchLte t sks

theorem setupChoice_mem (n : KNode) (t : Time) (forward hasDiff : Bool) (sks : Int)
    (fd : Found) (hf : setupChoice n t forward hasDiff sks = some fd) :
    (fd.c, fd.y) ∈ n.liveAt t := by
  unfold setupChoice at hf
  split at hf
  · split at hf
    · exact ((n.searchLt_spec t cvHi).1 fd hf).1
    · exact ((n.searchGt_spec t cvLo).1 fd hf).1
  · split at hf
    · exact ((n.searchLte_spec t sks).1 fd hf).1
    · split at hf
      · exact ((n.searchGte_spec t sks).1 fd hf).1
      · exact ((n.searchLte_spec t sks).1 fd hf).1

/-- A setup call on a non-key node stops without changing the chain. -/
theorem setupGo_no_node (p : Params) (v : View BVal) (t : Time) (forward : Bool)
    (start : List Int) (fuel x index : Nat) (hasDiff : Bool) (ch : Chain)
    (hn : knodeOf p v x = none) :
    setupGo p v t forward start fuel x index hasDiff ch = ch := by
  cases fuel <;> simp [setupGo, hn]

theorem knodeOf_not_data (p : Params) (v : View BVal) (x : NodeId)
    (nd : Node BVal) (hv : v x = some nd) (hd : nd.isData = true) :
    knodeOf p v x = none := by simp [knodeOf, hv, hd]

/-- Setup builds a chain whose ancestors and remaining subtree depth fit
within the original path bound. Its loop fuel may be arbitrary. -/
theorem setupGo_scanChain (p : Params) (v : View BVal) (t : Time) (forward : Bool)
    (start : List Int) (bound fuel depth x index : Nat) (hasDiff : Bool) (ch : Chain)
    (hs : ScanTree p v t depth x) (hb : depth + ch.links.length ≤ bound)
    (hc : ScanChain p v t bound ch.links) :
    ScanChain p v t bound
      (setupGo p v t forward start fuel x index hasDiff ch).links := by
  induction fuel generalizing depth x index hasDiff ch with
  | zero => exact hc
  | succ fuel ih =>
    cases depth with
    | zero => exact hs.elim
    | succ depth =>
      obtain ⟨n, hn, hbounds, hchildren⟩ := hs
      simp only [setupGo, hn]
      change ScanChain p v t bound ((match setupChoice n t forward hasDiff
          (setupTarget forward start index) with
        | none => _
        | some fd => _) : Chain).links
      cases hf : setupChoice n t forward hasDiff (setupTarget forward start index) with
      | none => exact ⟨depth+1, ⟨n, hn, hbounds, hchildren⟩, hb, hc⟩
      | some fd =>
        have hmem := setupChoice_mem n t forward hasDiff _ fd hf
        simp only
        split
        · exact ⟨depth+1, ⟨n, hn, hbounds, hchildren⟩, hb, hc⟩
        · have hparent : ScanChain p v t bound ((x, (fd.c : Int)) :: ch.links) :=
            ⟨depth+1, ⟨n, hn, hbounds, hchildren⟩, hb, hc⟩
          cases hy : v fd.y with
          | none =>
            have hnone : knodeOf p v fd.y = none := by simp [knodeOf, hy]
            split <;> rw [setupGo_no_node p v t forward start fuel fd.y _ _ _ hnone] <;>
              exact hparent
          | some nd =>
            cases hd : nd.isData with
            | true =>
              have hnone := knodeOf_not_data p v fd.y nd hy hd
              split <;> rw [setupGo_no_node p v t forward start fuel fd.y _ _ _ hnone] <;>
                exact hparent
            | false =>
              have hchild := (hchildren (fd.c, fd.y) hmem nd hy hd).1
              split <;> apply ih depth fd.y _ _ _ hchild _ hparent <;>
                simp only [List.length_cons] <;> omega

/-- The actual setup uses a single path budget, independent of key length. -/
theorem chainSetup_scanChain (p : Params) (v : View BVal) (t : Time) (req : ScanReq)
    (r : NodeId) (hs : ScanTree p v t p.fuel r) :
    ScanChain p v t p.fuel (chainSetup p v t req r).links := by
  unfold chainSetup
  exact setupGo_scanChain p v t req.forward _ p.fuel p.fuel p.fuel r 0 false {}
    hs (by simp) trivial

/-- Every call made by the scan loop has sufficient next-step fuel. The
property covers the initial call and all calls after earlier results. -/
def ScanCallsAdequate (p : Params) (v : View BVal) (t : Time) (req : ScanReq) :
    Nat → Chain → Prop
  | 0, _ => True
  | fuel+1, ch =>
      (∀ extra, nextGo p v t req (2 * p.fuel + 2 + extra) ch =
        nextGo p v t req (2 * p.fuel + 2) ch) ∧
      ScanCallsAdequate p v t req fuel (nextGo p v t req (2 * p.fuel + 2) ch).2

theorem scanCallsAdequate_of_chain (p : Params) (v : View BVal) (t : Time) (req : ScanReq)
    (fuel : Nat) (ch : Chain) (hc : ScanChain p v t p.fuel ch.links) :
    ScanCallsAdequate p v t req fuel ch := by
  induction fuel generalizing ch with
  | zero => trivial
  | succ fuel ih =>
    exact ⟨nextGo_parameter_fuel p v t req ch hc,
      ih _ (nextGo_scanChain p v t req p.fuel _ ch hc)⟩

/-- TP7 supplies the walk needed by scan fuel adequacy. The encoding and
high-node kind invariants are already unconditional results for actual runs.
There is no key-length, threshold or additional latest-map premise. -/
theorem treeRun_scan_fuel_adequate (p : Params) (ts : List Tx) (hw : Within p ts)
    (t : Time) (hinv : InvOK p (treeRun p ts) t) (req : ScanReq) (calls : Nat) :
    ∃ r, rootAt (viewOf (treeRun p ts)) t = some r ∧
      ScanCallsAdequate p (viewOf (treeRun p ts)) t req calls
        (chainSetup p (viewOf (treeRun p ts)) t req r) := by
  unfold InvOK faultsAt at hinv
  cases hr : rootAt (viewOf (treeRun p ts)) t with
  | none => simp [hr] at hinv
  | some r =>
    simp only [hr] at hinv
    have hs := scanTree_of_walk p (treeRun p ts) t p.fuel (treeRun_highKindsOK p ts)
      (structEncoded_viewOf _ (treeRun_encoded_of_within p ts hw)) r 0 none true true hinv
    exact ⟨r, rfl, scanCallsAdequate_of_chain p _ t req calls _
      (chainSetup_scanChain p _ t req r hs)⟩

theorem scan_fuel_adequate_of_invPreserved (p : Params) (hinv : InvPreserved p)
    (ts : List Tx) (hw : Within p ts) (t : Time) (ht : t ≤ ts.length)
    (req : ScanReq) (calls : Nat) :
    ∃ r, rootAt (viewOf (treeRun p ts)) t = some r ∧
      ScanCallsAdequate p (viewOf (treeRun p ts)) t req calls
        (chainSetup p (viewOf (treeRun p ts)) t req r) :=
  treeRun_scan_fuel_adequate p ts hw t (hinv ts hw t ht).1 req calls

end SIS.Tree
