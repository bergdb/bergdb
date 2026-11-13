import SIS.Tree.ScanRead

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

theorem setupChoice_of_prefix (a b : KNode) (t : Time) (forward hasDiff : Bool)
    (sks : Int) (hleaf : a.leaf = b.leaf) (hpre : prefixAt a.ks t = prefixAt b.ks t) :
    setupChoice a t forward hasDiff sks = setupChoice b t forward hasDiff sks := by
  simp only [setupChoice, hleaf]
  split
  · split <;> exact a.searchBy_eq_of_prefix b t _ hpre
  · split
    · exact a.searchBy_eq_of_prefix b t _ hpre
    · split <;> exact a.searchBy_eq_of_prefix b t _ hpre

theorem setupGo_step (p : Params) (v : View BVal) (t : Time) (forward : Bool)
    (start : List Int) (f x index : Nat) (hasDiff : Bool) (ch : Chain)
    (n : KNode) (hn : knodeOf p v x = some n) :
    setupGo p v t forward start (f+1) x index hasDiff ch =
      match setupChoice n t forward hasDiff (setupTarget forward start index) with
      | none =>
        { ch with links := (x, if forward || (!forward && !hasDiff && !n.leaf)
              then cvLo else cvHi) :: ch.links }
      | some fd =>
        let ch := { ch with links := (x, (fd.c : Int)) :: ch.links }
        if n.leaf && segLen fd.c < 7 then ch
        else
          let ch := { ch with seen := fd.y :: ch.seen }
          if n.leaf then
            setupGo p v t forward start f fd.y (index+1)
              (hasDiff || (fd.c : Int) != setupTarget forward start index)
              { ch with segs := ch.segs ++ [fd.c] }
          else setupGo p v t forward start f fd.y index hasDiff ch := by
  simp only [setupGo, hn]
  rfl

/-- Setup reads the same old snapshot after an extension and builds only
frames belonging to the old closed set. Fuel and start segments are arbitrary. -/
theorem setupGo_of_readClosed (p : Params) (P Q : Struct BVal) (t : Time)
    (hext : ReadExtension p t P Q) (S : NodeId → Prop)
    (hclosed : ReadClosed p (viewOf P) t S) (forward : Bool) (start : List Int)
    (fuel x index : Nat) (hasDiff : Bool) (ch : Chain) (hx : S x)
    (hc : ReadChain S ch.links) :
    setupGo p (viewOf Q) t forward start fuel x index hasDiff ch =
      setupGo p (viewOf P) t forward start fuel x index hasDiff ch ∧
    ReadChain S (setupGo p (viewOf P) t forward start fuel x index hasDiff ch).links := by
  induction fuel generalizing x index hasDiff ch with
  | zero => exact ⟨rfl, hc⟩
  | succ fuel ih =>
    obtain ⟨n, hn, hchildren⟩ := hclosed x hx
    obtain ⟨next, hn', hleaf, hpre⟩ := hext.key x n hn
    rw [setupGo_step p (viewOf Q) t forward start fuel x index hasDiff ch next hn',
      setupGo_step p (viewOf P) t forward start fuel x index hasDiff ch n hn]
    rw [setupChoice_of_prefix next n t forward hasDiff _ hleaf hpre]
    cases hf : setupChoice n t forward hasDiff (setupTarget forward start index) with
    | none => simp only [hleaf]; exact ⟨trivial, (readChain_cons S x _ _).mpr ⟨hx, hc⟩⟩
    | some fd =>
      have hmem := setupChoice_mem n t forward hasDiff _ fd hf
      simp only [hleaf]
      split
      · exact ⟨rfl, (readChain_cons S x _ _).mpr ⟨hx, hc⟩⟩
      · have hparent : ReadChain S ((x, (fd.c : Int)) :: ch.links) :=
          (readChain_cons S x _ _).mpr ⟨hx, hc⟩
        rcases hchildren (fd.c, fd.y) hmem with ⟨value, hv⟩ | hchild
        · have hv' := hext.value fd.y value hv
          obtain ⟨nd, hy, hd⟩ := valueOf_view _ fd.y value hv
          obtain ⟨nd', hy', hd'⟩ := valueOf_view _ fd.y value hv'
          have hnone := knodeOf_not_data p _ fd.y nd hy hd
          have hnone' := knodeOf_not_data p _ fd.y nd' hy' hd'
          split <;>
            rw [setupGo_no_node p (viewOf Q) t forward start fuel fd.y _ _ _ hnone',
              setupGo_no_node p (viewOf P) t forward start fuel fd.y _ _ _ hnone] <;>
            exact ⟨rfl, hparent⟩
        · split <;> exact ih fd.y _ _ _ hchild hparent

theorem chainSetup_of_readClosed (p : Params) (P Q : Struct BVal) (t : Time)
    (hext : ReadExtension p t P Q) (S : NodeId → Prop)
    (hclosed : ReadClosed p (viewOf P) t S) (req : ScanReq) (r : NodeId) (hr : S r) :
    chainSetup p (viewOf Q) t req r = chainSetup p (viewOf P) t req r ∧
      ReadChain S (chainSetup p (viewOf P) t req r).links := by
  cases hstart : req.start with
  | none =>
    have he := setupGo_of_readClosed p P Q t hext S hclosed req.forward
      [if req.forward then cvLo else cvHi] p.fuel r 0 false {} hr (readChain_nil S)
    simp only [chainSetup, hstart]
    rw [he.1]
    exact ⟨rfl, he.2⟩
  | some key =>
    have he := setupGo_of_readClosed p P Q t hext S hclosed req.forward
      (key.map (fun (c : Nat) => (c : Int))) p.fuel r 0 false {} hr (readChain_nil S)
    simp only [chainSetup, hstart]
    rw [he.1]
    exact ⟨rfl, he.2⟩

end SIS.Tree
