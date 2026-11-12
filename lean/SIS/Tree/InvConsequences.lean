import SIS.Tree.MergeProps

namespace SIS.Tree

open SIS SIS.Check

theorem keyNodeAt_eq_knodeOf (p : Params) (P : Struct BVal) (x : NodeId) :
    keyNodeAt p P x = knodeOf p (viewOf P) x := by
  unfold keyNodeAt knodeOf viewOf
  cases P.get? x with
  | none => rfl
  | some nd =>
    cases hd : nd.isData <;>
      by_cases hl : nd.level ≤ p.keyMax <;> simp_all

theorem mem_zip_left_witness {α β : Type} (xs : List α) (ys : List β)
    (hlen : xs.length ≤ ys.length) (a : α) (ha : a ∈ xs) :
    ∃ b, (a,b) ∈ xs.zip ys := by
  induction xs generalizing ys with
  | nil => simp at ha
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      rcases List.mem_cons.mp ha with rfl | ha
      · exact ⟨y,List.mem_cons_self⟩
      · obtain ⟨b,hb⟩ := ih ys (by simpa using hlen) ha
        exact ⟨b,List.mem_cons_of_mem _ hb⟩

theorem nodesRoots_of_no_node (p : Params) (v : View BVal) (t f x : Nat)
    (isRoot : Bool) (hn : knodeOf p v x = none) :
    nodesRoots p v t f x isRoot = [] := by
  cases f <;> simp only [nodesRoots,hn]

def walkChildFaults (p : Params) (v : View BVal) (t f : Nat)
    (x : NodeId) (n : KNode) (g h lo : Nat) (space : Bool)
    (q : (Nat × NodeId) × Option Nat) : Faults :=
  let ((c,y),hi) := q
  if n.leaf then
    if segLen c == 7 then
      match v y with
      | some ny =>
        if ny.isData then [s!"KindsOK: segment leaf {x}: the long segment {c} names a value"]
        else if p.segOf ny.level != g + 1 then
          [s!"KindsOK: segment leaf {x}: {y} is not in the next segment"]
        else walk p v t f y 0 none true false
      | none => []
    else
      match v y with
      | some ny => if ny.isData then [] else [s!"KindsOK: segment leaf {x}: the short segment {c} names a key node"]
      | none => []
  else
    match v y with
    | some ny =>
      if ny.isData then [s!"KindsOK: inner node {x} names a value"]
      else if p.segOf ny.level != g || p.heightOf ny.level + 1 != h then
        [s!"KindsOK: inner node {x} at height {h}: child {y} at height {p.heightOf ny.level}, segment {p.segOf ny.level}"]
      else walk p v t f y (if c == 0 then lo else c) hi false space
    | none => []

theorem walk_child_faults_nil (p : Params) (v : View BVal) (t f : Nat)
    (x lo : Nat) (hi : Option Nat) (isRoot space : Bool) (nd : Node BVal)
    (hv : v x = some nd) (hd : nd.isData = false)
    (hw : walk p v t (f+1) x lo hi isRoot space = []) :
    let n : KNode := ⟨p.heightOf nd.level == 0,klongsOf nd.hist⟩
    ((n.liveAt t).zip ((n.liveAt t).drop 1 |>.map (fun q => some q.1) |>.append [hi])).flatMap
      (walkChildFaults p v t f x n (p.segOf nd.level) (p.heightOf nd.level) lo space) = [] := by
  rw [walk] at hw
  simp only [hv,hd,Bool.false_eq_true,↓reduceIte] at hw
  exact (List.eq_nil_of_append_eq_nil hw).2

theorem walk_current_fill (p : Params) (v : View BVal) (t f : Nat)
    (x lo : Nat) (hi : Option Nat) (space : Bool) (nd : Node BVal)
    (hv : v x = some nd) (hd : nd.isData = false)
    (hw : walk p v t (f+1) x lo hi false space = []) (hm : p.merges = true) :
    p.mergeBelow ≤ ((⟨p.heightOf nd.level == 0,klongsOf nd.hist⟩ : KNode).liveAt t).length := by
  by_cases hf : p.mergeBelow ≤
      ((⟨p.heightOf nd.level == 0,klongsOf nd.hist⟩ : KNode).liveAt t).length
  · exact hf
  · have hlt : ((⟨p.heightOf nd.level == 0,klongsOf nd.hist⟩ : KNode).liveAt t).length <
        p.mergeBelow := by omega
    have hmem : s!"FillOK: key node {x}, not a root, has {((⟨p.heightOf nd.level == 0,klongsOf nd.hist⟩ : KNode).liveAt t).length} live klongs at {t}, fewer than m = {p.mergeBelow}" ∈
        walk p v t (f+1) x lo hi false space := by
      rw [walk]
      simp only [hv,hd,Bool.false_eq_true,↓reduceIte]
      simp [hm,hlt]
    simp [hw] at hmem

theorem walk_all_nodes (p : Params) (v : View BVal) (t : Nat)
    (pred : NodeId → Bool → KNode → Prop)
    (hlocal : ∀ f x lo hi isRoot space (nd : Node BVal),
      v x = some nd → nd.isData = false → walk p v t (f+1) x lo hi isRoot space = [] →
      pred x isRoot ⟨p.heightOf nd.level == 0,klongsOf nd.hist⟩)
    (f : Nat)
    (x lo : Nat) (hi : Option Nat) (isRoot space : Bool)
    (hw : walk p v t f x lo hi isRoot space = []) :
    ∀ q ∈ nodesRoots p v t f x isRoot,
      ∀ n, knodeOf p v q.1 = some n → pred q.1 q.2 n := by
  induction f generalizing x lo hi isRoot space with
  | zero => simp only [walk,List.cons_ne_nil] at hw
  | succ f ih =>
    intro q hq n' hn'
    cases hv : v x with
    | none => simp only [walk,hv,List.cons_ne_nil] at hw
    | some nd =>
      cases hd : nd.isData with
      | true => simp only [walk,hv,hd,↓reduceIte,List.cons_ne_nil] at hw
      | false =>
        by_cases hl : p.keyMax < nd.level
        · simp [nodesRoots,knodeOf,hv,hd,hl] at hq
        · let n : KNode := ⟨p.heightOf nd.level == 0,klongsOf nd.hist⟩
          have hnode : knodeOf p v x = some n := by simp [knodeOf,hv,hd,hl,n]
          simp only [nodesRoots,hnode] at hq
          rcases List.mem_cons.mp hq with hself | hq
          · cases hself
            change knodeOf p v x = some n' at hn'
            rw [hnode] at hn'
            rw [← Option.some.inj hn']
            exact hlocal f x lo hi isRoot space nd hv hd hw
          · obtain ⟨⟨c,y⟩,hcy,hbelow⟩ := List.mem_flatMap.mp hq
            have hlen : (n.liveAt t).length ≤
                (((n.liveAt t).drop 1).map (fun q => some q.1) ++ [hi]).length := by
              simp only [List.length_append,List.length_map,List.length_drop,List.length_singleton]
              omega
            obtain ⟨hi',hzip⟩ := mem_zip_left_witness _ _ hlen (c,y) hcy
            have hchild := List.flatMap_eq_nil_iff.mp
              (walk_child_faults_nil p v t f x lo hi isRoot space nd hv hd hw)
              ((c,y),hi') hzip
            change walkChildFaults p v t f x n (p.segOf nd.level)
              (p.heightOf nd.level) lo space ((c,y),hi') = [] at hchild
            cases hleaf : n.leaf with
            | true =>
              by_cases hc : segLen c = 7
              · simp only [hleaf,hc,↓reduceIte] at hbelow
                simp only [walkChildFaults,hleaf,hc,beq_self_eq_true,↓reduceIte] at hchild
                cases hvy : v y with
                | none =>
                  rw [nodesRoots_of_no_node p v t f y true (by simp [knodeOf,hvy])] at hbelow
                  cases hbelow
                | some ny =>
                  simp only [hvy] at hchild
                  split at hchild
                  · cases hchild
                  · split at hchild
                    · cases hchild
                    · exact ih y 0 none true false hchild q hbelow n' hn'
              · simp [hleaf,hc] at hbelow
            | false =>
              simp only [hleaf,Bool.false_eq_true,↓reduceIte] at hbelow
              simp only [walkChildFaults,hleaf,Bool.false_eq_true,↓reduceIte] at hchild
              cases hvy : v y with
              | none =>
                rw [nodesRoots_of_no_node p v t f y false (by simp [knodeOf,hvy])] at hbelow
                cases hbelow
              | some ny =>
                simp only [hvy] at hchild
                split at hchild
                · cases hchild
                · split at hchild
                  · cases hchild
                  · exact ih y (if c == 0 then lo else c) hi' false space hchild q hbelow n' hn'

theorem walk_fill (p : Params) (v : View BVal) (t f : Nat)
    (x lo : Nat) (hi : Option Nat) (isRoot space : Bool)
    (hw : walk p v t f x lo hi isRoot space = []) (hm : p.merges = true) :
    ∀ q ∈ nodesRoots p v t f x isRoot, q.2 = false →
      ∀ n, knodeOf p v q.1 = some n → p.mergeBelow ≤ (n.liveAt t).length := by
  have hall := walk_all_nodes p v t
    (fun _ isRoot n => isRoot = false → p.mergeBelow ≤ (n.liveAt t).length)
    (by
      intro f x lo hi isRoot space nd hv hd hw hr
      subst isRoot
      exact walk_current_fill p v t f x lo hi space nd hv hd hw hm)
    f x lo hi isRoot space hw
  intro q hq hqr n hn
  exact hall q hq n hn hqr

/-- FillOK is already checked by the invariant walk. No history or parameter
premise is needed to extract it. -/
theorem fillOK_of_invOK (p : Params) (P : Struct BVal) (t : Time)
    (hi : InvOK p P t) : FillOK p P t := by
  intro hm q hq hqr n hn
  unfold InvOK faultsAt at hi
  unfold nodesRootsAt at hq
  cases hr : rootAt (viewOf P) t with
  | none => simp only [hr,List.cons_ne_nil] at hi
  | some r =>
    rw [hr] at hi hq
    exact walk_fill p (viewOf P) t p.fuel r 0 none true true hi hm q hq hqr n
      (by rwa [← keyNodeAt_eq_knodeOf])

/-- TP30 has no independent fill-preservation obligation once TP7 holds:
the invariant walk includes that check. The TP7 premise remains explicit. -/
theorem mergeInvPreserved_of_invPreserved (p : Params) (h : InvPreserved p) :
    MergeInvPreserved p := by
  intro _ ts hts t ht
  obtain ⟨hi,hp⟩ := h ts hts t ht
  exact ⟨hi,fillOK_of_invOK p _ t hi,hp⟩

theorem nodesRoots_map_fst (p : Params) (v : View BVal) (t f x : Nat) (isRoot : Bool) :
    (nodesRoots p v t f x isRoot).map Prod.fst = nodesAt p v t f x := by
  induction f generalizing x isRoot with
  | zero => rfl
  | succ f ih =>
    simp only [nodesRoots,nodesAt]
    cases hn : knodeOf p v x with
    | none => rfl
    | some n =>
      simp only [List.map_cons,List.map_flatMap]
      congr 1
      congr 1
      funext q
      rcases q with ⟨c,y⟩
      cases hl : n.leaf <;> cases hc : segLen c != 7 <;> simp [ih]

theorem walk_current_wf (p : Params) (v : View BVal) (t f : Nat)
    (x lo : Nat) (hi : Option Nat) (isRoot space : Bool) (nd : Node BVal)
    (hv : v x = some nd) (hd : nd.isData = false)
    (hw : walk p v t (f+1) x lo hi isRoot space = []) :
    klongsWf (klongsOf nd.hist) = true := by
  by_cases hf : klongsWf (klongsOf nd.hist) = true
  · exact hf
  · have hmem : s!"klongsWf: key node {x}" ∈ walk p v t (f+1) x lo hi isRoot space := by
      rw [walk]
      simp only [hv,hd,Bool.false_eq_true,↓reduceIte]
      simp [hf]
    simp [hw] at hmem

theorem walk_current_size (p : Params) (v : View BVal) (t f : Nat)
    (x lo : Nat) (hi : Option Nat) (isRoot space : Bool) (nd : Node BVal)
    (hv : v x = some nd) (hd : nd.isData = false)
    (hw : walk p v t (f+1) x lo hi isRoot space = []) :
    (klongsOf nd.hist).length ≤ p.M := by
  by_cases hs : (klongsOf nd.hist).length ≤ p.M
  · exact hs
  · have hlt : p.M < (klongsOf nd.hist).length := by omega
    have hmem : s!"SizeOK: key node {x} has {(klongsOf nd.hist).length} klongs" ∈
        walk p v t (f+1) x lo hi isRoot space := by
      rw [walk]
      simp only [hv,hd,Bool.false_eq_true,↓reduceIte]
      simp [KNode.size,hlt]
    simp [hw] at hmem

theorem invOK_reachable_nodes (p : Params) (P : Struct BVal) (t : Time)
    (pred : NodeId → KNode → Prop)
    (hlocal : ∀ f x lo hi isRoot space (nd : Node BVal),
      viewOf P x = some nd → nd.isData = false →
      walk p (viewOf P) t (f+1) x lo hi isRoot space = [] →
      pred x ⟨p.heightOf nd.level == 0,klongsOf nd.hist⟩)
    (hi : InvOK p P t) :
    ∀ x ∈ keyNodesAt p P t, ∀ n, keyNodeAt p P x = some n → pred x n := by
  intro x hx n hn
  unfold InvOK faultsAt at hi
  unfold keyNodesAt at hx
  cases hr : rootAt (viewOf P) t with
  | none => simp only [hr,List.cons_ne_nil] at hi
  | some r =>
    rw [hr] at hi hx
    dsimp only at hi hx
    have hall := walk_all_nodes p (viewOf P) t
      (fun x _ n => pred x n) hlocal
      p.fuel r 0 none true true hi
    rw [← nodesRoots_map_fst p (viewOf P) t p.fuel r true] at hx
    obtain ⟨q,hq,hqx⟩ := List.mem_map.mp hx
    subst x
    exact hall q hq n (by rwa [← keyNodeAt_eq_knodeOf])

theorem invOK_reachable_wf_size (p : Params) (P : Struct BVal) (t : Time)
    (hi : InvOK p P t) :
    ∀ x ∈ keyNodesAt p P t, ∀ n, keyNodeAt p P x = some n →
      klongsWf n.ks = true ∧ n.size ≤ p.M := by
  apply invOK_reachable_nodes p P t (fun _ n => klongsWf n.ks = true ∧ n.size ≤ p.M) _ hi
  intro f x lo hi isRoot space nd hv hd hw
  exact ⟨walk_current_wf p _ t f x lo hi isRoot space nd hv hd hw,
    walk_current_size p _ t f x lo hi isRoot space nd hv hd hw⟩

theorem walk_current_inner_nonempty (p : Params) (v : View BVal) (t f : Nat)
    (x lo : Nat) (hi : Option Nat) (isRoot space : Bool) (nd : Node BVal)
    (hv : v x = some nd) (hd : nd.isData = false)
    (hw : walk p v t (f+1) x lo hi isRoot space = [])
    (hleaf : (p.heightOf nd.level == 0) = false) :
    (⟨p.heightOf nd.level == 0,klongsOf nd.hist⟩ : KNode).liveAt t ≠ [] := by
  intro he
  simp only [hleaf] at he
  have hmem : s!"NonEmptyOK: key node {x} has no live klong at {t}" ∈
      walk p v t (f+1) x lo hi isRoot space := by
    rw [walk]
    simp only [hv,hd,Bool.false_eq_true,↓reduceIte]
    simp [he,hleaf]
  simp [hw] at hmem

theorem walk_current_leftmost (p : Params) (v : View BVal) (t f : Nat)
    (x lo : Nat) (hi : Option Nat) (isRoot space : Bool) (nd : Node BVal)
    (hv : v x = some nd) (hd : nd.isData = false)
    (hw : walk p v t (f+1) x lo hi isRoot space = [])
    (hleaf : (p.heightOf nd.level == 0) = false) :
    (((⟨p.heightOf nd.level == 0,klongsOf nd.hist⟩ : KNode).liveAt t).head?.map (·.1)) =
      some 0 := by
  have hne := walk_current_inner_nonempty p v t f x lo hi isRoot space nd hv hd hw hleaf
  have hemp : ((⟨p.heightOf nd.level == 0,klongsOf nd.hist⟩ : KNode).liveAt t).isEmpty = false := by
    cases he : (⟨p.heightOf nd.level == 0,klongsOf nd.hist⟩ : KNode).liveAt t with
    | nil => exact (hne he).elim
    | cons q qs => rfl
  by_cases hh : (((⟨p.heightOf nd.level == 0,klongsOf nd.hist⟩ : KNode).liveAt t).head?.map (·.1)) = some 0
  · exact hh
  · simp only [hleaf] at hemp hh
    have hmem : s!"LeftmostOK: inner node {x} has no live klong of the empty key at {t}" ∈
        walk p v t (f+1) x lo hi isRoot space := by
      rw [walk]
      simp only [hv,hd,Bool.false_eq_true,↓reduceIte]
      simp [hleaf,hemp,hh]
    simp [hw] at hmem

theorem leftmostOK_of_invOK (p : Params) (P : Struct BVal) (t : Time)
    (hi : InvOK p P t) : LeftmostOK p P t := by
  have hall := invOK_reachable_nodes p P t
    (fun _ n => n.leaf = false → ((n.liveAt t).head?.map (·.1)) = some 0)
    (by
      intro f x lo hi isRoot space nd hv hd hw hleaf
      exact walk_current_leftmost p _ t f x lo hi isRoot space nd hv hd hw hleaf) hi
  intro x hx n hn hleaf
  exact hall x hx n hn hleaf

end SIS.Tree
