import SIS.Tree.HistoricalGet

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

theorem KNode.searchEq_eq_of_prefix (a b : KNode) (t cv : Nat)
    (he : prefixAt a.ks t = prefixAt b.ks t) :
    a.searchEq t cv = b.searchEq t cv := by
  simp only [KNode.searchEq, he]

theorem KNode.searchBy_eq_of_prefix (a b : KNode) (t : Nat)
    (better : Nat → Option Nat → Bool) (he : prefixAt a.ks t = prefixAt b.ks t) :
    a.searchBy t better = b.searchBy t better := by
  simp only [KNode.searchBy, he]

/-- Segment lookup is stable under arbitrary future changes. The sound
segment is required only in the old structure, at any sufficient walk depth;
the reader's own search fuel is arbitrary. -/
theorem getEq_apply_past_of_segment (p : Params) (P : Struct BVal) (i t : Time)
    (changes : Changes BVal) (ht : t < i) (f x lo : Nat) (hi : Option Nat)
    (hs : SegmentSound p (viewOf P) t f x lo hi) (cv fuel : Nat) :
    getEq p (viewOf (P.apply i changes)) t cv fuel x = getEq p (viewOf P) t cv fuel x := by
  induction fuel generalizing f x lo hi with
  | zero => rfl
  | succ fuel ih =>
    cases f with
    | zero => exact hs.elim
    | succ f =>
      obtain ⟨n, hn, hwf, hrange, hchildren⟩ := hs
      obtain ⟨next, hn', hleaf, hpre⟩ := knodeOf_apply_past p P i t changes ht x n hn
      have heq := next.searchEq_eq_of_prefix n t cv hpre
      have hlte : next.searchLte t cv = n.searchLte t cv :=
        next.searchBy_eq_of_prefix n t _ hpre
      simp only [getEq, hn, hn', hleaf, heq, hlte]
      cases hnl : n.leaf with
      | true => simp only [hnl, ↓reduceIte]
      | false =>
        simp only [hnl, Bool.false_eq_true, ↓reduceIte]
        cases hfd : n.searchLte t cv with
        | none => rfl
        | some fd =>
          have hmem := (n.searchLte_spec t cv).1 fd hfd |>.1
          obtain ⟨b, hb⟩ := childBounds_exists (n.liveAt t) hi (fd.c, fd.y) hmem
          exact ih f fd.y _ b (hchildren hnl ((fd.c, fd.y), b) hb)

/-- A successful segment lookup in an old fault-free walk reaches an actual
value or the root of the next segment, as its compare value requires. -/
theorem getEq_walk_target (p : Params) (P : Struct BVal) (t : Time)
    (hkinds : HighKindsOK p P) (hdata : DataEntriesOK P) (fuel f x lo : Nat)
    (hi : Option Nat) (isRoot space : Bool)
    (hw : walk p (viewOf P) t f x lo hi isRoot space = []) (cv y : Nat)
    (hget : getEq p (viewOf P) t cv fuel x = some y) :
    (segLen cv ≠ 7 → ∃ value, valueOf (viewOf P) y = some value) ∧
    (segLen cv = 7 → ∃ depth < f, walk p (viewOf P) t depth y 0 none true false = []) := by
  induction fuel generalizing f x lo hi isRoot space with
  | zero => simp [getEq] at hget
  | succ fuel ih =>
    cases f with
    | zero => simp [walk] at hw
    | succ f =>
      cases hx : P.get? x with
      | none => simp [walk, viewOf, hx] at hw
      | some nd =>
        cases hd : nd.isData with
        | true => simp [walk, viewOf, hx, hd] at hw
        | false =>
          have hl := highKindsOK_walk_level p P t f x lo hi isRoot space nd hkinds hx hd hw
          let n : KNode := ⟨p.heightOf nd.level == 0, klongsOf nd.hist⟩
          have hn : knodeOf p (viewOf P) x = some n := by
            simp [knodeOf, viewOf, hx, hd, Nat.not_lt_of_ge hl, n]
          simp only [getEq, hn] at hget
          cases hleaf : n.leaf with
          | true =>
            have hheight : (p.heightOf nd.level == 0) = true := hleaf
            have hwf := walk_current_wf p _ t f x lo hi isRoot space nd hx hd hw
            have hlookup : (n.liveAt t).lookup cv = some y := by
              rw [← searchEqSpec n t cv hwf]
              simpa only [hleaf, ↓reduceIte] using hget
            have hmem := lookup_some_mem hlookup
            obtain ⟨b, hb⟩ := childBounds_exists (n.liveAt t) hi (cv, y) hmem
            have hedge := walk_edge_info p P t f x lo hi isRoot space nd hdata hx hd hw (cv, y) b hb
            change ((n.leaf && segLen cv != 7) = true → _) ∧
              ((n.leaf && segLen cv != 7) = false → _) at hedge
            constructor
            · intro hshort
              exact hedge.1 (by simp [hleaf, hshort])
            · intro hlong
              exact ⟨f, by omega, by simpa [hheight] using hedge.2 (by simp [hleaf, hlong])⟩
          | false =>
            have hheight : (p.heightOf nd.level == 0) = false := hleaf
            simp only [hleaf, Bool.false_eq_true, ↓reduceIte] at hget
            cases hfd : n.searchLte t cv with
            | none => simp [hfd] at hget
            | some fd =>
              have hmem := (n.searchLte_spec t cv).1 fd hfd |>.1
              obtain ⟨b, hb⟩ := childBounds_exists (n.liveAt t) hi (fd.c, fd.y) hmem
              have hedge := walk_edge_info p P t f x lo hi isRoot space nd hdata hx hd hw
                (fd.c, fd.y) b hb
              change ((n.leaf && segLen fd.c != 7) = true → _) ∧
                ((n.leaf && segLen fd.c != 7) = false → _) at hedge
              have hchild := hedge.2 (by simp [hleaf])
              simp only [hheight, Bool.false_eq_true, ↓reduceIte] at hchild
              have hget' : getEq p (viewOf P) t cv fuel fd.y = some y := by
                simpa only [hfd] using hget
              obtain ⟨hvalue, hnext⟩ := ih f fd.y _ b false space hchild hget'
              refine ⟨hvalue, ?_⟩
              intro hlong
              obtain ⟨depth, hdepth, hwalk⟩ := hnext hlong
              exact ⟨depth, by omega, hwalk⟩

/-- A multisegment get in an old fault-free tree is unaffected by arbitrary
future changes. No soundness of the resulting structure is assumed. -/
theorem getFrom_apply_past_of_walk (p : Params) (P : Struct BVal) (i t : Time)
    (changes : Changes BVal) (ht : t < i) (hkinds : HighKindsOK p P)
    (hdata : DataEntriesOK P) (key : Key) (f x lo : Nat) (hi : Option Nat)
    (isRoot space : Bool) (hw : walk p (viewOf P) t f x lo hi isRoot space = [])
    (hkey : keyWf key = true) :
    getFrom p (viewOf (P.apply i changes)) t key x = getFrom p (viewOf P) t key x := by
  induction key generalizing f x lo hi isRoot space with
  | nil => simp [keyWf] at hkey
  | cons cv rest ih =>
    have hseg := segmentSound_of_walk p P t f hkinds x lo hi isRoot space hw
    have heq := getEq_apply_past_of_segment p P i t changes ht f x lo hi hseg cv p.fuel
    cases hget : getEq p (viewOf P) t cv p.fuel x with
    | none => cases rest <;> simp only [getFrom, heq, hget, Option.bind_none]
    | some y =>
      have htarget := getEq_walk_target p P t hkinds hdata p.fuel f x lo hi isRoot space hw cv y hget
      cases rest with
      | nil =>
        have hshort := ((keyWf_singleton cv).mp hkey).2.2
        obtain ⟨value, hv⟩ := htarget.1 hshort
        have hv' := valueOf_apply_some P i changes y value hv
        simp only [getFrom, heq, hget, Option.bind_some, hv, hv']
      | cons a rest =>
        obtain ⟨_, _, hlong, hrest⟩ := (keyWf_cons_cons cv a rest).mp hkey
        obtain ⟨depth, hdepth, hwalk⟩ := htarget.2 hlong
        have hs := keyTreeSound_of_walk p P t depth hkinds y 0 none true false hwalk
        obtain ⟨n, hn⟩ := keyTreeSound_node p (viewOf P) t depth y 0 none hs
        obtain ⟨next, hn', _, _⟩ := knodeOf_apply_past p P i t changes ht y n hn
        simp only [getFrom, heq, hget, hn, hn', Option.isSome_some, ↓reduceIte]
        exact ih depth y 0 none true false hwalk hrest

theorem get_apply_past_of_old_invariant (p : Params) (P : Struct BVal) (i t : Time)
    (changes : Changes BVal) (ht : t < i) (hkinds : HighKindsOK p P)
    (hdata : DataEntriesOK P) (hinv : InvOK p P t) (key : Key) (hkey : keyWf key = true) :
    get p (viewOf (P.apply i changes)) t key = get p (viewOf P) t key := by
  unfold InvOK faultsAt at hinv
  cases hr : rootAt (viewOf P) t with
  | none => simp [hr] at hinv
  | some r =>
    simp only [hr] at hinv
    unfold get
    rw [rootAt_apply_some_past P i t changes ht r hr, hr]
    simp only [Option.bind_some]
    exact getFrom_apply_past_of_walk p P i t changes ht hkinds hdata key p.fuel r 0 none true true hinv hkey

end SIS.Tree
