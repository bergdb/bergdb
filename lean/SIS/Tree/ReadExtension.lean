import SIS.Tree.HistoricalGetDirect

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The reader-visible facts retained from an old structure. Only existing
key nodes, values and roots are constrained. -/
structure ReadExtension (p : Params) (t : Time) (P Q : Struct BVal) : Prop where
  key : ∀ x n, knodeOf p (viewOf P) x = some n →
    ∃ next, knodeOf p (viewOf Q) x = some next ∧ next.leaf = n.leaf ∧
      prefixAt next.ks t = prefixAt n.ks t
  value : ∀ y value, valueOf (viewOf P) y = some value → valueOf (viewOf Q) y = some value
  root : ∀ r, rootAt (viewOf P) t = some r → rootAt (viewOf Q) t = some r

theorem readExtension_refl (p : Params) (t : Time) (P : Struct BVal) : ReadExtension p t P P :=
  ⟨by intro x n hn; exact ⟨n, hn, rfl, rfl⟩,
   by intro y value hv; exact hv,
   by intro r hr; exact hr⟩

theorem ReadExtension.trans (p : Params) (t : Time) (P Q R : Struct BVal)
    (hPQ : ReadExtension p t P Q) (hQR : ReadExtension p t Q R) : ReadExtension p t P R := by
  constructor
  · intro x n hn
    obtain ⟨mid, hm, hleaf, hpre⟩ := hPQ.key x n hn
    obtain ⟨last, hl, hleaf', hpre'⟩ := hQR.key x mid hm
    exact ⟨last, hl, hleaf'.trans hleaf, hpre'.trans hpre⟩
  · intro y value hv
    exact hQR.value y value (hPQ.value y value hv)
  · intro r hr
    exact hQR.root r (hPQ.root r hr)

theorem readExtension_apply_past (p : Params) (P : Struct BVal) (i t : Time)
    (changes : Changes BVal) (ht : t < i) : ReadExtension p t P (P.apply i changes) :=
  ⟨knodeOf_apply_past p P i t changes ht,
   valueOf_apply_some P i changes,
   rootAt_apply_some_past P i t changes ht⟩

/-- Every prefix is extended at its own time by the complete run. This is
an unconditional consequence of structure application, including runs with
rejected transactions. -/
theorem treeRun_readExtension_prefix (p : Params) (ts : List Tx) (t : Time)
    (ht : t ≤ ts.length) :
    ReadExtension p t (treeRun p (ts.take t)) (treeRun p ts) := by
  have hf : ∀ revts : List Tx, ∀ u ≤ revts.reverse.length,
      ReadExtension p u (treeRun p (revts.reverse.take u)) (treeRun p revts.reverse) := by
    intro revts
    induction revts with
    | nil =>
      intro u hu
      simp only [List.reverse_nil, List.take_nil]
      exact readExtension_refl p u (treeRun p [])
    | cons tx revts ih =>
      intro u hu
      simp only [List.reverse_cons] at hu ⊢
      by_cases hle : u ≤ revts.reverse.length
      · rw [List.take_append_of_le_length hle, treeRun_snoc]
        exact ReadExtension.trans p u _ _ _ (ih u hle)
          (readExtension_apply_past p _ (revts.reverse.length + 1) u _ (by omega))
      · have he : u = (revts.reverse ++ [tx]).length := by
          simp only [List.length_append, List.length_singleton] at hu ⊢
          omega
        rw [he, List.take_length]
        exact readExtension_refl p _ _
  simpa only [List.reverse_reverse] using hf ts.reverse t (by simpa using ht)

theorem getEq_of_readExtension (p : Params) (P Q : Struct BVal) (t : Time)
    (hext : ReadExtension p t P Q) (f x lo : Nat) (hi : Option Nat)
    (hs : SegmentSound p (viewOf P) t f x lo hi) (cv fuel : Nat) :
    getEq p (viewOf Q) t cv fuel x = getEq p (viewOf P) t cv fuel x := by
  induction fuel generalizing f x lo hi with
  | zero => rfl
  | succ fuel ih =>
    cases f with
    | zero => exact hs.elim
    | succ f =>
      obtain ⟨n, hn, hwf, hrange, hchildren⟩ := hs
      obtain ⟨next, hn', hleaf, hpre⟩ := hext.key x n hn
      have heq := next.searchEq_eq_of_prefix n t cv hpre
      have hlte : next.searchLte t cv = n.searchLte t cv :=
        next.searchBy_eq_of_prefix n t _ hpre
      simp only [getEq, hn, hn', hleaf, heq, hlte]
      cases hnl : n.leaf with
      | true => simp only [↓reduceIte]
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        cases hfd : n.searchLte t cv with
        | none => rfl
        | some fd =>
          have hmem := (n.searchLte_spec t cv).1 fd hfd |>.1
          obtain ⟨b, hb⟩ := childBounds_exists (n.liveAt t) hi (fd.c, fd.y) hmem
          exact ih f fd.y _ b (hchildren hnl ((fd.c, fd.y), b) hb)

theorem getFrom_of_readExtension (p : Params) (P Q : Struct BVal) (t : Time)
    (hext : ReadExtension p t P Q) (hkinds : HighKindsOK p P) (hdata : DataEntriesOK P)
    (key : Key) (f x lo : Nat) (hi : Option Nat) (isRoot space : Bool)
    (hw : walk p (viewOf P) t f x lo hi isRoot space = []) (hkey : keyWf key = true) :
    getFrom p (viewOf Q) t key x = getFrom p (viewOf P) t key x := by
  induction key generalizing f x lo hi isRoot space with
  | nil => simp [keyWf] at hkey
  | cons cv rest ih =>
    have hseg := segmentSound_of_walk p P t f hkinds x lo hi isRoot space hw
    have heq := getEq_of_readExtension p P Q t hext f x lo hi hseg cv p.fuel
    cases hget : getEq p (viewOf P) t cv p.fuel x with
    | none => cases rest <;> simp only [getFrom, heq, hget, Option.bind_none]
    | some y =>
      have htarget := getEq_walk_target p P t hkinds hdata p.fuel f x lo hi isRoot space hw cv y hget
      cases rest with
      | nil =>
        have hshort := ((keyWf_singleton cv).mp hkey).2.2
        obtain ⟨value, hv⟩ := htarget.1 hshort
        have hv' := hext.value y value hv
        simp only [getFrom, heq, hget, Option.bind_some, hv, hv']
      | cons a rest =>
        obtain ⟨_, _, hlong, hrest⟩ := (keyWf_cons_cons cv a rest).mp hkey
        obtain ⟨depth, hdepth, hwalk⟩ := htarget.2 hlong
        have hs := keyTreeSound_of_walk p P t depth hkinds y 0 none true false hwalk
        obtain ⟨n, hn⟩ := keyTreeSound_node p (viewOf P) t depth y 0 none hs
        obtain ⟨next, hn', _, _⟩ := hext.key y n hn
        simp only [getFrom, heq, hget, hn, hn', Option.isSome_some, ↓reduceIte]
        exact ih depth y 0 none true false hwalk hrest

theorem get_of_readExtension (p : Params) (P Q : Struct BVal) (t : Time)
    (hext : ReadExtension p t P Q) (hkinds : HighKindsOK p P) (hdata : DataEntriesOK P)
    (hinv : InvOK p P t) (key : Key) (hkey : keyWf key = true) :
    get p (viewOf Q) t key = get p (viewOf P) t key := by
  unfold InvOK faultsAt at hinv
  cases hr : rootAt (viewOf P) t with
  | none => simp [hr] at hinv
  | some r =>
    simp only [hr] at hinv
    unfold get
    rw [hext.root r hr, hr]
    simp only [Option.bind_some]
    exact getFrom_of_readExtension p P Q t hext hkinds hdata key p.fuel r 0 none true true hinv hkey

/-- Only the state immediately after time t needs an invariant. No
invariant is required of any later state or of the complete run. -/
theorem treeRun_get_eq_prefix_of_invariant (p : Params) (ts : List Tx) (t : Time)
    (ht : t ≤ ts.length) (hinv : InvOK p (treeRun p (ts.take t)) t)
    (key : Key) (hkey : keyWf key = true) :
    get p (viewOf (treeRun p ts)) t key = get p (viewOf (treeRun p (ts.take t))) t key :=
  get_of_readExtension p _ _ t (treeRun_readExtension_prefix p ts t ht)
    (treeRun_highKindsOK p (ts.take t)) (treeRun_dataEntriesOK p (ts.take t)) hinv key hkey

/-- Latest-time structural correctness, without the historical or global
pointer-closure clauses of TP7. -/
def LatestInvOK (p : Params) : Prop :=
  ∀ ts, Within p ts → InvOK p (treeRun p ts) ts.length

theorem getOK_of_latest_invariant (p : Params) (hinv : LatestInvOK p)
    (hlatest : LatestGetOK p) : GetOK p := by
  intro ts hw t ht key hkey
  have hlen : (ts.take t).length = t := by simp only [List.length_take, Nat.min_eq_left ht]
  have hwithin := within_take p ts hw t
  have hi := hinv (ts.take t) hwithin
  rw [hlen] at hi
  rw [treeRun_get_eq_prefix_of_invariant p ts t ht hi key hkey]
  have he := hlatest (ts.take t) hwithin key hkey
  rw [hlen, refGet_take_eq ts t t (Nat.le_refl _) key] at he
  exact he

theorem getOK_of_latest_invariant_contents (p : Params) (hinv : LatestInvOK p)
    (hcontents : ∀ ts, Within p ts → ∀ key, keyWf key = true →
      (rootContents p (treeRun p ts) ts.length).lookup key = refGet ts ts.length key) : GetOK p := by
  apply getOK_of_latest_invariant p hinv
  intro ts hw key hkey
  rw [treeRun_get_lookup p ts ts.length (hinv ts hw) key hkey]
  exact hcontents ts hw key hkey

end SIS.Tree
