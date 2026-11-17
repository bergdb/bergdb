/-
The contract package (bergdb 030-10): two trees that differ below one node.
The lemmas that make every rule of the writer a local argument:

* a subtree depends only on the nodes reached in it (`reachAt_agree`,
  `listAt_agree`, `Good.agree`, `L_agree`);
* the invariants are `Good` at the space root and the rules of each node
  reached (`invOk_iff`);
* a sound node is sound for a wider range (`Good.widen`); no node is below
  itself (`Good.not_below`);
* the context lemma (`Good.ctx`, `ctx_L`, `ctx_route`, `ctx_reach`): if two
  trees agree on every node reached from r that is not below q, and q in the
  second tree is sound for every range it is sound for in the first, then r
  is sound in the second tree; it holds the same keys if q does, and the
  keys with a put or a delete applied if q does and the key is routed to q;
  and it meets TREE if q's new subtree does and holds only nodes of its old
  subtree and nodes not reached before.
-/
import Contract.Proof.Reach
import Contract.Proof.Chain

namespace Contract

variable {p : Params}

/-- The tree with node x set to o. -/
def Tree.set (s : Tree) (x : NodeId) (o : Obj) : Tree :=
  { s with obj := fun y => if y = x then some o else s.obj y }

/-! ## 1. A subtree depends only on the nodes reached -/

theorem tc_self (s : Tree) (f : Nat) (x : NodeId) : x ∈ reachAt s f x := by
  cases f <;> simp [reachAt]

theorem tc_key {s : Tree} {x : NodeId} {n : KNode} (h : s.obj x = some (.key n)) (f : Nat) :
    reachAt s (f + 1) x = x :: (live n.ks).flatMap (fun cy => reachAt s f cy.2) := by
  simp [reachAt, h]

theorem tc_nokey {s : Tree} {x : NodeId} (h : ∀ n, s.obj x ≠ some (.key n)) :
    ∀ f, reachAt s f x = [x]
  | 0 => rfl
  | f + 1 => by
    cases ho : s.obj x with
    | none => simp [reachAt, ho]
    | some o =>
      cases o with
      | val v => simp [reachAt, ho]
      | key n => exact absurd ho (h n)

theorem tc_val {s : Tree} {x : NodeId} {v : Nat} (h : s.obj x = some (.val v)) (f : Nat) :
    reachAt s f x = [x] :=
  tc_nokey (fun n => by simp [h]) f

theorem tc_mem_succ {s : Tree} {f : Nat} {x w : NodeId} :
    w ∈ reachAt s (f + 1) x ↔
      w = x ∨ ∃ n, s.obj x = some (.key n) ∧ ∃ cy ∈ live n.ks, w ∈ reachAt s f cy.2 := by
  cases ho : s.obj x with
  | none => simp [reachAt, ho]
  | some o =>
    cases o with
    | val v => simp [reachAt, ho]
    | key n => simp [tc_key ho, List.mem_flatMap]

theorem tc_kid {s : Tree} {x : NodeId} {n : KNode} (h : s.obj x = some (.key n)) {f : Nat}
    {c : Nat} {y z : NodeId} (hm : (c, y) ∈ live n.ks) (hz : z ∈ reachAt s f y) :
    z ∈ reachAt s (f + 1) x := by
  rw [tc_key h]
  exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨(c, y), hm, hz⟩)

theorem tc_mono {s : Tree} {w : NodeId} : ∀ (f g : Nat) (x : NodeId), f ≤ g →
    w ∈ reachAt s f x → w ∈ reachAt s g x
  | 0, g, x, _, h => by
    simp only [reachAt, List.mem_singleton] at h
    rw [h]; exact tc_self s g x
  | f + 1, g, x, hfg, h => by
    obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    rcases tc_mem_succ.mp h with rfl | ⟨n, ho, cy, hcy, hw⟩
    · exact tc_self s _ _
    · exact tc_kid ho hcy (tc_mono f g' cy.2 (by omega) hw)

theorem tc_trans {s : Tree} {w : NodeId} (g : Nat) : ∀ (f : Nat) (x z : NodeId),
    z ∈ reachAt s f x → w ∈ reachAt s g z → w ∈ reachAt s (f + g) x
  | 0, x, z, hz, hw => by
    simp only [reachAt, List.mem_singleton] at hz
    rw [hz] at hw; simpa using hw
  | f + 1, x, z, hz, hw => by
    rcases tc_mem_succ.mp hz with rfl | ⟨n, ho, cy, hcy, hz⟩
    · exact tc_mono g _ z (by omega) hw
    · rw [show f + 1 + g = (f + g) + 1 by omega]
      exact tc_kid ho hcy (tc_trans g f cy.2 z hz hw)

theorem reachAt_agree {s s' : Tree} : ∀ (f : Nat) (y : NodeId),
    (∀ z ∈ reachAt s f y, s'.obj z = s.obj z) → reachAt s' f y = reachAt s f y
  | 0, _, _ => rfl
  | f + 1, y, ha => by
    have hy : s'.obj y = s.obj y := ha y (tc_self _ _ _)
    cases ho : s.obj y with
    | none => simp [reachAt, ho, hy]
    | some o =>
      cases o with
      | val v => simp [reachAt, ho, hy]
      | key n =>
        rw [tc_key ho, tc_key (hy.trans ho)]
        congr 1
        apply List.flatMap_congr
        rintro ⟨c, x⟩ hm
        exact reachAt_agree f x (fun z hz => ha z (tc_kid ho hm hz))

theorem tc_klongList {s s' : Tree} {leaf : Bool} {sub sub' : NodeId → List (Key × Nat)}
    {c : Nat} {y : NodeId} (h1 : s'.obj y = s.obj y) (h2 : sub' y = sub y) :
    klongList s' leaf sub' c y = klongList s leaf sub c y := by
  unfold klongList
  rw [h1, h2]

theorem listAt_agree {s s' : Tree} : ∀ (f : Nat) (y : NodeId),
    (∀ z ∈ reachAt s f y, s'.obj z = s.obj z) → listAt s' f y = listAt s f y
  | 0, _, _ => rfl
  | f + 1, y, ha => by
    have hy : s'.obj y = s.obj y := ha y (tc_self _ _ _)
    cases ho : s.obj y with
    | none => simp [listAt, ho, hy]
    | some o =>
      cases o with
      | val v => simp [listAt, ho, hy]
      | key n =>
        simp only [listAt, ho, hy]
        apply List.flatMap_congr
        rintro ⟨c, x⟩ hm
        have hx : ∀ z ∈ reachAt s f x, s'.obj z = s.obj z := fun z hz => ha z (tc_kid ho hm hz)
        exact tc_klongList (hx x (tc_self _ _ _)) (listAt_agree f x hx)

/-- The nodes reached from a sound node do not depend on the fuel, if it is
enough. -/
theorem Good.reachAt_eq {s : Tree} {y : NodeId} {lo : Nat} {hi : Option Nat} (h : Good s y lo hi) :
    ∀ f, s.fuel y ≤ f → reachAt s f y = reachAt s (s.fuel y) y := by
  induction h with
  | mk x lo hi n hobj hwf hhi hlo hval hkey hseg hkid ihseg ihkid =>
    intro f hf
    have hfuel : s.fuel x = n.level + 1 := by simp [Tree.fuel, hobj]
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    rw [hfuel, tc_key hobj, tc_key hobj]
    congr 1
    apply List.flatMap_congr
    rintro ⟨c, y⟩ hm
    by_cases hk : n.leaf = true → isLong c = true
    · obtain ⟨m, hm1, hm2, _⟩ := hkey c y hm hk
      have hfy : s.fuel y = m.level + 1 := by simp [Tree.fuel, hm1]
      cases hl : n.leaf with
      | true =>
        rw [ihseg hl c y hm (hk hl) f' (by omega), ihseg hl c y hm (hk hl) n.level (by omega)]
      | false =>
        obtain ⟨pre, post, he⟩ := List.append_of_mem hm
        rw [ihkid hl pre c y post he f' (by omega), ihkid hl pre c y post he n.level (by omega)]
    · simp only [Classical.not_imp, Bool.not_eq_true] at hk
      obtain ⟨v, hv⟩ := hval hk.1 c y hm hk.2
      rw [tc_val hv, tc_val hv]

theorem Good.agree {s s' : Tree} {y : NodeId} {lo : Nat} {hi : Option Nat} (h : Good s y lo hi)
    (ha : ∀ z ∈ reachAt s (s.fuel y) y, s'.obj z = s.obj z) : Good s' y lo hi := by
  revert ha
  induction h with
  | mk x lo hi n hobj hwf hhi hlo hval hkey hseg hkid ihseg ihkid =>
    intro ha
    have hfuel : s.fuel x = n.level + 1 := by simp [Tree.fuel, hobj]
    rw [hfuel] at ha
    have hkA : ∀ c y, (c, y) ∈ live n.ks → ∀ z ∈ reachAt s n.level y, s'.obj z = s.obj z :=
      fun c y hm z hz => ha z (tc_kid hobj hm hz)
    have hy : ∀ c y, (c, y) ∈ live n.ks → s'.obj y = s.obj y :=
      fun c y hm => hkA c y hm y (tc_self _ _ _)
    have hsub : ∀ c y lo' hi', (c, y) ∈ live n.ks → (n.leaf = true → isLong c = true) →
        Good s y lo' hi' → ∀ z ∈ reachAt s (s.fuel y) y, s'.obj z = s.obj z := by
      intro c y lo' hi' hm hk hg
      obtain ⟨m, hm1, hm2, _⟩ := hkey c y hm hk
      rw [← hg.reachAt_eq n.level (by simp [Tree.fuel, hm1]; omega)]
      exact hkA c y hm
    refine Good.mk x lo hi n ((ha x (tc_self _ _ _)).trans hobj) hwf hhi hlo ?_ ?_ ?_ ?_
    · intro hl c y hm hs
      rw [hy c y hm]
      exact hval hl c y hm hs
    · intro c y hm hk
      rw [hy c y hm]
      exact hkey c y hm hk
    · intro hl c y hm hs
      exact ihseg hl c y hm hs (hsub c y 0 none hm (fun _ => hs) (hseg hl c y hm hs))
    · intro hl pre c y post he
      have hm : (c, y) ∈ live n.ks := by rw [he]; simp
      exact ihkid hl pre c y post he
        (hsub c y _ _ hm (by simp [hl]) (hkid hl pre c y post he))

theorem L_agree {s s' : Tree} {y : NodeId}
    (ha : ∀ z ∈ reachAt s (s.fuel y) y, s'.obj z = s.obj z) : L s' y = L s y := by
  have hy : s'.obj y = s.obj y := ha y (tc_self _ _ _)
  have hf : s'.fuel y = s.fuel y := by simp [Tree.fuel, hy]
  unfold L
  rw [hf]
  exact listAt_agree _ _ ha

/-! ## 2. The invariants as `Good` and the rules of each node reached -/

theorem tc_walk_nodeOk {s : Tree} : ∀ (f : Nat) (x : NodeId) (lo : Nat) (hi : Option Nat),
    walk p s f x lo hi = true →
      ∀ z ∈ reachAt s f x, ∀ m, s.obj z = some (.key m) → nodeOk p s m = true
  | 0, _, _, _, h => by simp [walk] at h
  | f + 1, x, lo, hi, h => by
    unfold walk at h
    cases ho : s.obj x with
    | none => simp [ho] at h
    | some o =>
      rw [ho] at h
      cases o with
      | val v => simp at h
      | key n =>
        simp only [Bool.and_eq_true] at h
        intro z hz m hm
        rcases tc_mem_succ.mp hz with rfl | ⟨n', ho', ⟨c, y⟩, hcy, hz⟩
        · rw [ho] at hm
          cases hm
          exact h.1
        · rw [ho] at ho'
          cases ho'
          obtain ⟨pre, post, he⟩ := List.append_of_mem hcy
          have hko := kidsOk_at _ pre c y post h.2 he
          unfold kidOk at hko
          cases hy : s.obj y with
          | none =>
            by_cases hl : n.leaf = true <;> by_cases hlong : isLong c = true <;>
              simp [hl, hlong, hy] at hko
          | some o =>
            cases o with
            | val v =>
              rw [tc_val hy] at hz
              rw [List.mem_singleton.mp hz, hy] at hm
              cases hm
            | key m' =>
              have hw : ∃ lo' hi', walk p s f y lo' hi' = true := by
                by_cases hl : n.leaf = true <;> by_cases hlong : isLong c = true <;>
                  simp [hl, hlong, hy] at hko
                · exact ⟨_, _, hko.2.2.2⟩
                · exact ⟨_, _, hko.2.2⟩
                · exact ⟨_, _, hko.2.2⟩
              obtain ⟨lo', hi', hw⟩ := hw
              exact tc_walk_nodeOk f y lo' hi' hw z hz m hm

theorem Good.tc_walk {s : Tree} {x : NodeId} {lo : Nat} {hi : Option Nat} (h : Good s x lo hi) :
    ∀ f, s.fuel x ≤ f →
      (∀ z ∈ reachAt s f x, ∀ m, s.obj z = some (.key m) → nodeOk p s m = true) →
      walk p s f x lo hi = true := by
  induction h with
  | mk x lo hi n hobj hwf hhi hlo hval hkey hseg hkid ihseg ihkid =>
    intro f hf hn
    have hfuel : s.fuel x = n.level + 1 := by simp [Tree.fuel, hobj]
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    unfold walk
    rw [hobj]
    simp only [Bool.and_eq_true]
    refine ⟨hn x (tc_self _ _ _) n hobj, ?_⟩
    have main : ∀ (post pre : List (Nat × NodeId)), live n.ks = pre ++ post →
        kidsOk s n lo hi (fun y lo' hi' => walk p s f' y lo' hi') post = true := by
      intro post
      induction post with
      | nil => intro _ _; rfl
      | cons a post ih =>
        obtain ⟨c, y⟩ := a
        intro pre he
        simp only [kidsOk, Bool.and_eq_true]
        refine ⟨?_, ih (pre ++ [(c, y)]) (by simp [he])⟩
        have hm : (c, y) ∈ live n.ks := by rw [he]; simp
        have hny : ∀ z ∈ reachAt s f' y, ∀ m, s.obj z = some (.key m) → nodeOk p s m = true :=
          fun z hz => hn z (tc_kid hobj hm hz)
        unfold kidOk
        simp only [hhi c y hm, Bool.true_and]
        cases hl : n.leaf with
        | false =>
          obtain ⟨m, hm1, hm2, hm3⟩ := hkey c y hm (by simp [hl])
          have hfy : s.fuel y = m.level + 1 := by simp [Tree.fuel, hm1]
          have hw := ihkid hl pre c y post he f' (by omega) hny
          simp [hm1, hm2, hm3, hw]
        | true =>
          simp only [hlo hl c y hm, decide_true, Bool.true_and, ite_true]
          cases hlong : isLong c with
          | false =>
            obtain ⟨v, hv⟩ := hval hl c y hm hlong
            simp [hv]
          | true =>
            obtain ⟨m, hm1, hm2, hm3⟩ := hkey c y hm (fun _ => hlong)
            have hfy : s.fuel y = m.level + 1 := by simp [Tree.fuel, hm1]
            have hw := ihseg hl c y hm hlong f' (by omega) hny
            simp [hm1, hm2, hm3, hw]
    exact main (live n.ks) [] rfl

theorem invOk_iff {s : Tree} :
    invOk p s = true ↔ ∃ r n, s.root = some r ∧ s.obj r = some (.key n) ∧
      (n.leaf = true ∨ live n.ks ≠ []) ∧ Good s r 0 none ∧
      ∀ z ∈ reach s, ∀ m, s.obj z = some (.key m) → nodeOk p s m = true := by
  constructor
  · intro h
    unfold invOk at h
    cases hr : s.root with
    | none => simp [hr] at h
    | some r =>
      simp only [hr] at h
      cases ho : s.obj r with
      | none => simp [ho] at h
      | some o =>
        rw [ho] at h
        cases o with
        | val v => simp at h
        | key n =>
          simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
            List.isEmpty_eq_false_iff] at h
          refine ⟨r, n, rfl, ho, h.1, walk_good _ _ _ _ h.2, ?_⟩
          intro z hz m hm
          unfold reach at hz
          rw [hr] at hz
          simp only [Tree.fuel, ho] at hz
          exact tc_walk_nodeOk _ _ _ _ h.2 z hz m hm
  · rintro ⟨r, n, hr, ho, hne, hG, hn⟩
    unfold invOk
    simp only [hr, ho, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      List.isEmpty_eq_false_iff]
    refine ⟨hne, hG.tc_walk _ (by simp [Tree.fuel, ho]) ?_⟩
    intro z hz m hm
    refine hn z ?_ m hm
    unfold reach
    rw [hr]
    simpa [Tree.fuel, ho] using hz

/-! ## 3. Ranges; no node below itself -/

theorem Good.widen {s : Tree} {y : NodeId} {lo lo' : Nat} {hi hi' : Option Nat}
    (h : Good s y lo hi) (hlo : lo' ≤ lo) (hhi : ∀ c, belowHi c hi = true → belowHi c hi' = true) :
    Good s y lo' hi' := by
  induction h generalizing lo' hi' with
  | mk x lo hi n hobj hwf hhi0 hlo0 hval hkey hseg hkid ihseg ihkid =>
    refine Good.mk x lo' hi' n hobj hwf (fun c y hm => hhi c (hhi0 c y hm))
      (fun hl c y hm => le_trans hlo (hlo0 hl c y hm)) hval hkey hseg ?_
    intro hl pre c y post he
    refine ihkid hl pre c y post he (max_le_max hlo le_rfl) ?_
    intro d hd
    cases post with
    | nil => exact hhi d hd
    | cons b rest => exact hd

theorem Good.tc_level {s : Tree} {x : NodeId} {lo : Nat} {hi : Option Nat} (h : Good s x lo hi) :
    ∀ n, s.obj x = some (.key n) → ∀ f, ∀ w ∈ reachAt s f x, ∀ m, s.obj w = some (.key m) →
      m.level ≤ n.level := by
  induction h with
  | mk x lo hi n hobj hwf hhi hlo hval hkey hseg hkid ihseg ihkid =>
    intro n' hobj' f w hw m hm
    rw [hobj] at hobj'
    cases hobj'
    cases f with
    | zero =>
      simp only [reachAt, List.mem_singleton] at hw
      rw [hw, hobj] at hm
      cases hm
      exact le_refl _
    | succ f =>
      rcases tc_mem_succ.mp hw with rfl | ⟨n'', ho, ⟨c, y⟩, hm', hw⟩
      · rw [hobj] at hm
        cases hm
        exact le_refl _
      · rw [hobj] at ho
        cases ho
        by_cases hk : n.leaf = true → isLong c = true
        · obtain ⟨m', hm1, hm2, _⟩ := hkey c y hm' hk
          have : m.level ≤ m'.level := by
            cases hl : n.leaf with
            | true => exact ihseg hl c y hm' (hk hl) m' hm1 f w hw m hm
            | false =>
              obtain ⟨pre, post, he⟩ := List.append_of_mem hm'
              exact ihkid hl pre c y post he m' hm1 f w hw m hm
          omega
        · simp only [Classical.not_imp, Bool.not_eq_true] at hk
          obtain ⟨v, hv⟩ := hval hk.1 c y hm' hk.2
          rw [tc_val hv, List.mem_singleton] at hw
          rw [hw, hv] at hm
          cases hm

/-- The level of every key node reached from a sound node is at most the
node's; that of a node reached from a child is below it. -/
theorem Good.not_below {s : Tree} {y : NodeId} {lo : Nat} {hi : Option Nat} (h : Good s y lo hi)
    {n : KNode} (hobj : s.obj y = some (.key n)) {c : Nat} {z : NodeId} (hm : (c, z) ∈ live n.ks) :
    ∀ f, y ∉ reachAt s f z := by
  intro f hy
  rcases h.kind hobj hm with ⟨_, _, v, hv⟩ | ⟨_, m, lo', hi', hm1, hm2, _, hg⟩
  · rw [tc_val hv, List.mem_singleton] at hy
    rw [hy, hv] at hobj
    cases hobj
  · have := hg.tc_level m hm1 f y hy n hobj
    omega

/-! ## 4. The context lemma

A and B are two trees, r a sound node of A, and q a node. B agrees with A on
every node reached from r in A that is not reached from q in A (`Agree`).
q is a key node of A (`hqk`): of a value q, `Agree`, `KeepsKind` and `hloc`
ask nothing, so B could change it at will. -/

/-- B agrees with A on the nodes reached from r in A but not from q. -/
def Agree (A B : Tree) (r q : NodeId) : Prop :=
  ∀ z ∈ reachAt A (A.fuel r) r, z ∉ reachAt A (A.fuel q) q → B.obj z = A.obj z

/-- What q's parent asks of q: in B it is a key node, on a level at most its
level in A, with a live klong if it had one. -/
def KeepsKind (A B : Tree) (q : NodeId) : Prop :=
  ∀ n, A.obj q = some (.key n) → ∃ n', B.obj q = some (.key n') ∧ n'.level ≤ n.level ∧
    (live n.ks ≠ [] → live n'.ks ≠ [])

theorem Good.tc_kid_eq {s : Tree} {u : NodeId} {lo : Nat} {hi : Option Nat} (h : Good s u lo hi)
    {n : KNode} (hobj : s.obj u = some (.key n)) {c : Nat} {y : NodeId}
    (hm : (c, y) ∈ live n.ks) : reachAt s n.level y = reachAt s (s.fuel y) y := by
  rcases h.kind hobj hm with ⟨_, _, v, hv⟩ | ⟨_, m, lo', hi', hm1, hm2, _, hg⟩
  · rw [tc_val hv, tc_val hv]
  · exact hg.reachAt_eq n.level (by simp [Tree.fuel, hm1]; omega)

theorem Good.tc_closed {s : Tree} {u : NodeId} {lo : Nat} {hi : Option Nat} (h : Good s u lo hi)
    {n : KNode} (hobj : s.obj u = some (.key n)) {c : Nat} {y : NodeId}
    (hm : (c, y) ∈ live n.ks) {z w : NodeId} {g : Nat} (hz : z ∈ reachAt s n.level y)
    (hw : w ∈ reachAt s g z) : w ∈ reachAt s n.level y := by
  rcases h.kind hobj hm with ⟨_, _, v, hv⟩ | ⟨_, m, lo', hi', hm1, hm2, _, hg⟩
  · rw [tc_val hv, List.mem_singleton] at hz
    rw [hz, tc_val hv] at hw
    rw [tc_val hv]
    exact hw
  · have h1 := tc_trans g n.level y z hz hw
    have hf : s.fuel y ≤ n.level := by simp [Tree.fuel, hm1]; omega
    rw [hg.reachAt_eq (n.level + g) (by omega)] at h1
    rw [hg.reachAt_eq n.level hf]
    exact h1

theorem Good.tc_no_cycle {s : Tree} {w q : NodeId} {lo : Nat} {hi : Option Nat}
    (h : Good s w lo hi) {g : Nat} (hq : q ∈ reachAt s g w) (hne : q ≠ w) (f : Nat) :
    w ∉ reachAt s f q := by
  intro hw
  obtain ⟨n, hobj⟩ := h.obj
  cases g with
  | zero =>
    simp only [reachAt, List.mem_singleton] at hq
    exact hne hq
  | succ g =>
    rcases tc_mem_succ.mp hq with h1 | ⟨n', ho, ⟨c, y⟩, hcy, hq'⟩
    · exact hne h1
    · rw [hobj] at ho
      cases ho
      exact h.not_below hobj hcy (g + f) (tc_trans f g y q hq' hw)

theorem tc_nodup_mid {α β : Type} {l pre post : List α} {a b : α} {g : α → List β} {z : β}
    (h : (l.flatMap g).Nodup) (he : l = pre ++ a :: post) (hb : b ∈ pre ++ post)
    (hzb : z ∈ g b) (hza : z ∈ g a) : False := by
  subst he
  rw [List.flatMap_append, List.flatMap_cons, List.nodup_append, List.nodup_append] at h
  rcases List.mem_append.mp hb with hb | hb
  · exact h.2.2 z (List.mem_flatMap.mpr ⟨b, hb, hzb⟩) z (List.mem_append_left _ hza) rfl
  · exact h.2.1.2.2 z hza z (List.mem_flatMap.mpr ⟨b, hb, hzb⟩) rfl

theorem tc_nodup_of_mem {α β : Type} {l : List α} {a : α} {g : α → List β}
    (h : (l.flatMap g).Nodup) (ha : a ∈ l) : (g a).Nodup :=
  (List.nodup_flatMap.mp h).1 a ha

/-- One step down from u towards q, reached from u's child y: u and every
node reached from u's other children are unchanged, and so is y unless it
is q; y is a key node, and the hypotheses hold at y. -/
theorem Good.tc_step {A B : Tree} {u q : NodeId} {lo : Nat} {hi : Option Nat}
    (hG : Good A u lo hi) {n : KNode} (hobj : A.obj u = some (.key n))
    (hT : (reachAt A (A.fuel u) u).Nodup) (ha : Agree A B u q)
    (hqk : ∃ m, A.obj q = some (.key m)) {pre post : List (Nat × NodeId)} {c : Nat} {y : NodeId}
    (he : live n.ks = pre ++ (c, y) :: post) (hqy : q ∈ reachAt A n.level y) :
    B.obj u = A.obj u ∧
      (∀ c' y', (c', y') ∈ pre ++ post → ∀ z ∈ reachAt A n.level y', B.obj z = A.obj z) ∧
      (y ≠ q → B.obj y = A.obj y) ∧ (n.leaf = true → isLong c = true) ∧
      (reachAt A (A.fuel y) y).Nodup ∧ q ∈ reachAt A (A.fuel y) y ∧ Agree A B y q := by
  have hm : (c, y) ∈ live n.ks := by rw [he]; simp
  have hfuel : A.fuel u = n.level + 1 := by simp [Tree.fuel, hobj]
  have hRA := tc_key hobj n.level
  rw [← hfuel] at hRA
  have hT' := (List.nodup_cons.mp (hRA ▸ hT)).2
  have hin : ∀ c' y' z, (c', y') ∈ live n.ks → z ∈ reachAt A n.level y' →
      z ∈ reachAt A (A.fuel u) u := by
    intro c' y' z hm' hz
    rw [hfuel]
    exact tc_kid hobj hm' hz
  have hqsub : ∀ w ∈ reachAt A (A.fuel q) q, w ∈ reachAt A n.level y :=
    fun w hw => hG.tc_closed hobj hm hqy hw
  obtain ⟨mq, hmq⟩ := hqk
  have hk' : n.leaf = true → isLong c = true := by
    rcases hG.kind hobj hm with ⟨_, _, v, hv⟩ | ⟨hk, _⟩
    · rw [tc_val hv, List.mem_singleton] at hqy
      rw [hqy, hv] at hmq
      cases hmq
    · exact hk
  have hpp : ∀ c' y', (c', y') ∈ pre ++ post → (c', y') ∈ live n.ks := by
    intro c' y' h
    rw [he]
    rcases List.mem_append.mp h with h | h <;> simp [h]
  refine ⟨ha u (tc_self _ _ _) (fun hu => hG.not_below hobj hm n.level (hqsub u hu)), ?_, ?_,
    hk', ?_, ?_, ?_⟩
  · intro c' y' hb z hz
    exact ha z (hin c' y' z (hpp c' y' hb) hz) (fun hz' => tc_nodup_mid hT' he hb hz (hqsub z hz'))
  · intro hyq
    obtain ⟨m, lo', hi', _, _, _, hg⟩ := hG.child hobj hm hk'
    exact ha y (hin c y y hm (tc_self _ _ _)) (hg.tc_no_cycle hqy (Ne.symm hyq) _)
  · rw [← hG.tc_kid_eq hobj hm]
    exact tc_nodup_of_mem (g := fun cy => reachAt A n.level cy.2) hT' hm
  · rw [← hG.tc_kid_eq hobj hm]
    exact hqy
  · intro z hz hzq
    rw [← hG.tc_kid_eq hobj hm] at hz
    exact ha z (hin c y z hm hz) hzq

theorem tc_klongList_long {s s' : Tree} {leaf : Bool} {sub sub' : NodeId → List (Key × Nat)}
    {c : Nat} {y : NodeId} (h1 : leaf = true → isLong c = true) (h2 : sub' y = sub y) :
    klongList s' leaf sub' c y = klongList s leaf sub c y := by
  unfold klongList
  cases leaf with
  | false => simp [h2]
  | true => simp [h1 rfl, h2]

/-- The context lemma by induction: r is sound in B, and holds the same keys
if q does. -/
theorem tc_ctx {A B : Tree} {q : NodeId} (hk : KeepsKind A B q)
    (hloc : ∀ lo' hi', Good A q lo' hi' → Good B q lo' hi') (hqk : ∃ n, A.obj q = some (.key n))
    {u : NodeId} {lo : Nat} {hi : Option Nat} (hG : Good A u lo hi) :
    (reachAt A (A.fuel u) u).Nodup → q ∈ reachAt A (A.fuel u) u → Agree A B u q →
      Good B u lo hi ∧ (L B q = L A q → L B u = L A u) := by
  induction hG with
  | mk u lo hi n hobj hwf hhi hlo hval hkey hseg hkid ihseg ihkid =>
    intro hT hq ha
    have hG : Good A u lo hi := Good.mk u lo hi n hobj hwf hhi hlo hval hkey hseg hkid
    by_cases huq : u = q
    · subst huq
      exact ⟨hloc lo hi hG, id⟩
    have hfuel : A.fuel u = n.level + 1 := by simp [Tree.fuel, hobj]
    rw [hfuel] at hq
    rcases tc_mem_succ.mp hq with h | ⟨n', ho, ⟨c, y⟩, hm, hqy⟩
    · exact absurd h.symm huq
    rw [hobj] at ho
    cases ho
    obtain ⟨pre, post, he⟩ := List.append_of_mem hm
    obtain ⟨hBu, hside, hBy, hlong, hTy, hqy', hay⟩ := hG.tc_step hobj hT ha hqk he hqy
    have hclass : ∀ c' y', (c', y') ∈ live n.ks → (c', y') = (c, y) ∨ (c', y') ∈ pre ++ post := by
      intro c' y' hm'
      rw [he] at hm'
      simp only [List.mem_append, List.mem_cons] at hm'
      rcases hm' with h | h | h
      · exact Or.inr (List.mem_append_left _ h)
      · exact Or.inl h
      · exact Or.inr (List.mem_append_right _ h)
    have hBy' : ∀ c' y', (c', y') ∈ live n.ks → y' ≠ q → B.obj y' = A.obj y' := by
      intro c' y' hm' hyq
      rcases hclass c' y' hm' with h | h
      · obtain ⟨_, rfl⟩ := Prod.mk.inj h
        exact hBy hyq
      · exact hside c' y' h y' (tc_self _ _ _)
    have hag : ∀ c' y', (c', y') ∈ pre ++ post →
        ∀ z ∈ reachAt A (A.fuel y') y', B.obj z = A.obj z := by
      intro c' y' h z hz
      have hm' : (c', y') ∈ live n.ks := by
        rw [he]
        rcases List.mem_append.mp h with h | h <;> simp [h]
      rw [← hG.tc_kid_eq hobj hm'] at hz
      exact hside c' y' h z hz
    obtain ⟨mq, hmq⟩ := hqk
    have hGB : Good B u lo hi := by
      refine Good.mk u lo hi n (hBu.trans hobj) hwf hhi hlo ?_ ?_ ?_ ?_
      · intro hl c' y' hm' hs
        obtain ⟨v, hv⟩ := hval hl c' y' hm' hs
        refine ⟨v, ?_⟩
        rw [hBy' c' y' hm' ?_, hv]
        intro hyq
        rw [hyq, hmq] at hv
        cases hv
      · intro c' y' hm' hk'
        obtain ⟨m, hm1, hm2, hm3⟩ := hkey c' y' hm' hk'
        by_cases hyq : y' = q
        · rw [hyq] at hm1 ⊢
          obtain ⟨n'', h1, h2, h3⟩ := hk m hm1
          exact ⟨n'', h1, by omega, h3 hm3⟩
        · rw [hBy' c' y' hm' hyq]
          exact ⟨m, hm1, hm2, hm3⟩
      · intro hl c' y' hm' hs
        rcases hclass c' y' hm' with h | h
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
          exact (ihseg hl _ _ hm' hs hTy hqy' hay).1
        · exact (hseg hl c' y' hm' hs).agree (hag c' y' h)
      · intro hl pre' c' y' post' he'
        have hm' : (c', y') ∈ live n.ks := by rw [he']; simp
        rcases hclass c' y' hm' with h | h
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
          exact (ihkid hl pre' _ _ post' he' hTy hqy' hay).1
        · exact (hkid hl pre' c' y' post' he').agree (hag c' y' h)
    refine ⟨hGB, ?_⟩
    intro hL
    have hLy : L B y = L A y := by
      cases hl : n.leaf with
      | false => exact (ihkid hl pre c y post he hTy hqy' hay).2 hL
      | true => exact (ihseg hl c y hm (hlong hl) hTy hqy' hay).2 hL
    rw [hGB.L_eq (hBu.trans hobj), hG.L_eq hobj]
    apply List.flatMap_congr
    rintro ⟨c', y'⟩ hm'
    rcases hclass c' y' hm' with h | h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact tc_klongList_long hlong hLy
    · exact tc_klongList (hside c' y' h y' (tc_self _ _ _)) (L_agree (hag c' y' h))

/-- r is sound in B. -/
theorem Good.ctx {A B : Tree} {r q : NodeId} {lo : Nat} {hi : Option Nat}
    (hG : Good A r lo hi) (hT : (reachAt A (A.fuel r) r).Nodup)
    (hq : q ∈ reachAt A (A.fuel r) r) (ha : Agree A B r q)
    (hk : KeepsKind A B q) (hloc : ∀ lo' hi', Good A q lo' hi' → Good B q lo' hi')
    (hqk : ∃ n, A.obj q = some (.key n)) :
    Good B r lo hi :=
  (tc_ctx hk hloc hqk hG hT hq ha).1

/-- r holds the same keys in B, if q does. -/
theorem ctx_L {A B : Tree} {r q : NodeId} {lo : Nat} {hi : Option Nat}
    (hG : Good A r lo hi) (hT : (reachAt A (A.fuel r) r).Nodup)
    (hq : q ∈ reachAt A (A.fuel r) r) (ha : Agree A B r q)
    (hk : KeepsKind A B q) (hloc : ∀ lo' hi', Good A q lo' hi' → Good B q lo' hi')
    (hqk : ∃ n, A.obj q = some (.key n)) (hL : L B q = L A q) : L B r = L A r :=
  (tc_ctx hk hloc hqk hG hT hq ha).2 hL

/-- The key k, from key node u, is routed to key node q with the key k' left:
in an inner node by the last live klong at or below the key's first segment,
in a segment leaf by the live klong of the key's first segment, a long one,
to the next segment's tree with the rest of the key. -/
inductive Route (s : Tree) : NodeId → Key → NodeId → Key → Prop where
  | here (q : NodeId) (k : Key) : Route s q k q k
  | inner (u : NodeId) (n : KNode) (c : Nat) (y : NodeId) (cv : Nat) (rest : Key) (q : NodeId)
      (k' : Key) : s.obj u = some (.key n) → n.leaf = false → (c, y) ∈ live n.ks → c ≤ cv →
      (∀ c' y', (c', y') ∈ live n.ks → c' ≤ cv → c' ≤ c) → Route s y (cv :: rest) q k' →
      Route s u (cv :: rest) q k'
  | leaf (u : NodeId) (n : KNode) (c : Nat) (y : NodeId) (rest : Key) (q : NodeId) (k' : Key) :
      s.obj u = some (.key n) → n.leaf = true → (c, y) ∈ live n.ks → isLong c = true →
      Route s y rest q k' → Route s u (c :: rest) q k'

/-- A change of what a node holds that is local to a key: it passes a part
before the key and a part after it, and a common first segment. `mapPut k v`
and `mapDel k` are such (`mapPut_local`, `mapDel_local`). -/
structure LocalTo (F : Key → List (Key × Nat) → List (Key × Nat)) : Prop where
  mid : ∀ (k : Key) (pre X post : List (Key × Nat)), (∀ a ∈ pre, a.1 < k) → (∀ b ∈ post, k < b.1) →
    F k (pre ++ X ++ post) = pre ++ F k X ++ post
  seg : ∀ (c : Nat) (k : Key) (X : List (Key × Nat)),
    F (c :: k) (X.map (fun kv => (c :: kv.1, kv.2))) = (F k X).map (fun kv => (c :: kv.1, kv.2))

theorem tc_mapPut_post (k : Key) (v : Nat) (post : List (Key × Nat)) (hpost : ∀ b ∈ post, k < b.1) :
    ∀ X : List (Key × Nat), mapPut k v (X ++ post) = mapPut k v X ++ post
  | [] => by
    cases post with
    | nil => rfl
    | cons b rest =>
      have h : keyLt k b.1 = true := (keyLt_iff _ _).mpr (hpost b List.mem_cons_self)
      simp [mapPut, h]
  | x :: X => by
    simp only [List.cons_append, mapPut]
    split
    · rfl
    · split
      · rfl
      · rw [tc_mapPut_post k v post hpost X]
        rfl

theorem tc_mapPut_pre (k : Key) (v : Nat) (X post : List (Key × Nat)) :
    ∀ pre : List (Key × Nat), (∀ a ∈ pre, a.1 < k) →
      mapPut k v (pre ++ (X ++ post)) = pre ++ mapPut k v (X ++ post)
  | [], _ => rfl
  | a :: pre, hpre => by
    have h1 : keyLt k a.1 = false :=
      (keyLt_false_iff _ _).mpr (le_of_lt (hpre a List.mem_cons_self))
    have h2 : k ≠ a.1 := ne_of_gt (hpre a List.mem_cons_self)
    simp only [List.cons_append, mapPut, h1, h2, Bool.false_eq_true, ite_false]
    rw [tc_mapPut_pre k v X post pre (fun b hb => hpre b (List.mem_cons_of_mem _ hb))]

theorem mapPut_local (v : Nat) : LocalTo (fun k m => mapPut k v m) := by
  constructor
  · intro k pre X post hpre hpost
    rw [List.append_assoc, tc_mapPut_pre k v X post pre hpre, tc_mapPut_post k v post hpost X,
      List.append_assoc]
  · intro c k X
    induction X with
    | nil => rfl
    | cons x X ih =>
      have h1 : keyLt (c :: k) (c :: x.1) = keyLt k x.1 := by simp [keyLt]
      simp only [List.map_cons, mapPut, h1, List.cons.injEq, true_and]
      split
      · rfl
      · split
        · rfl
        · simp only [List.map_cons, ih]

theorem mapDel_local : LocalTo (fun k m => mapDel k m) := by
  constructor
  · intro k pre X post hpre hpost
    simp only [mapDel, List.filter_append]
    have h1 : pre.filter (fun kv => kv.1 != k) = pre := by
      rw [List.filter_eq_self]
      intro a ha
      simpa using ne_of_lt (hpre a ha)
    have h2 : post.filter (fun kv => kv.1 != k) = post := by
      rw [List.filter_eq_self]
      intro b hb
      simpa using ne_of_gt (hpost b hb)
    rw [h1, h2]
  · intro c k X
    simp only [mapDel, List.filter_map]
    congr 1
    apply List.filter_congr
    intro kv _
    have : (c :: kv.1 == c :: k) = (kv.1 == k) := by
      by_cases h : kv.1 = k <;> simp [h]
    simp only [bne, Function.comp_apply]
    rw [this]

/-- A route from a sound node ends at a sound node reached from it. -/
theorem Route.tc_target {A : Tree} {u q : NodeId} {k k' : Key} (hr : Route A u k q k') :
    ∀ {lo : Nat} {hi : Option Nat}, Good A u lo hi →
      (∃ lo' hi', Good A q lo' hi') ∧ q ∈ reachAt A (A.fuel u) u := by
  induction hr with
  | here q k => intro lo hi hG; exact ⟨⟨lo, hi, hG⟩, tc_self _ _ _⟩
  | inner u n c y cv rest q k' hobj hl hm _ _ _ ih =>
    intro lo hi hG
    obtain ⟨m, lo', hi', hm1, hm2, _, hg⟩ := hG.child hobj hm (by simp [hl])
    obtain ⟨h1, h2⟩ := ih hg
    refine ⟨h1, ?_⟩
    rw [show A.fuel u = n.level + 1 by simp [Tree.fuel, hobj]]
    exact tc_kid hobj hm (by rw [hG.tc_kid_eq hobj hm]; exact h2)
  | leaf u n c y rest q k' hobj _ hm hlong _ ih =>
    intro lo hi hG
    obtain ⟨m, lo', hi', hm1, hm2, _, hg⟩ := hG.child hobj hm (fun _ => hlong)
    obtain ⟨h1, h2⟩ := ih hg
    refine ⟨h1, ?_⟩
    rw [show A.fuel u = n.level + 1 by simp [Tree.fuel, hobj]]
    exact tc_kid hobj hm (by rw [hG.tc_kid_eq hobj hm]; exact h2)

/-- In an inner node, a key below the child of a live klong before the
klong with compare value c starts below c. -/
theorem Good.tc_kid_upper {s : Tree} {u : NodeId} {lo : Nat} {hi : Option Nat}
    (h : Good s u lo hi) {n : KNode} (hobj : s.obj u = some (.key n)) (hl : n.leaf = false)
    {pre post : List (Nat × NodeId)} {c : Nat} {y : NodeId}
    (he : live n.ks = pre ++ (c, y) :: post) {c0 : Nat} {y0 : NodeId} (h0 : (c0, y0) ∈ pre) :
    ∀ k v, (k, v) ∈ L s y0 → ∃ d r', k = d :: r' ∧ d < c := by
  cases h with
  | mk _ _ _ n' hobj' hwf hhi hlo hval hkey hseg hkid =>
    rw [hobj] at hobj'
    obtain rfl : n = n' := by injection hobj' with h1; injection h1
    obtain ⟨pre1, pre2, hp⟩ := List.append_of_mem h0
    have he' : live n.ks = pre1 ++ (c0, y0) :: (pre2 ++ (c, y) :: post) := by rw [he, hp]; simp
    obtain ⟨_, _, hpp⟩ := live_split he'
    have hh : ∀ b ∈ pre2 ++ (c, y) :: post, belowHi b.1 hi = true :=
      fun b hb => hhi b.1 b.2 (by rw [he']; simp [hb])
    intro k v hkv
    obtain ⟨d, r', rfl, _, hd⟩ := (hkid hl pre1 c0 y0 _ he').range k v hkv
    exact ⟨d, r', rfl, (below_nextHi hpp hh hd).2 (c, y) (by simp)⟩

/-- What u holds in A and in B, split at the child y. -/
theorem tc_L_split {A B : Tree} {u : NodeId} {lo : Nat} {hi : Option Nat}
    (hG : Good A u lo hi) (hGB : Good B u lo hi) {n : KNode} (hobj : A.obj u = some (.key n))
    (hBu : B.obj u = A.obj u) {pre post : List (Nat × NodeId)} {c : Nat} {y : NodeId}
    (he : live n.ks = pre ++ (c, y) :: post)
    (hside : ∀ c' y', (c', y') ∈ pre ++ post → ∀ z ∈ reachAt A n.level y', B.obj z = A.obj z) :
    L B u = pre.flatMap (fun cy => klongList A n.leaf (L A) cy.1 cy.2) ++
        (klongList B n.leaf (L B) c y ++
          post.flatMap (fun cy => klongList A n.leaf (L A) cy.1 cy.2)) ∧
      L A u = pre.flatMap (fun cy => klongList A n.leaf (L A) cy.1 cy.2) ++
        (klongList A n.leaf (L A) c y ++
          post.flatMap (fun cy => klongList A n.leaf (L A) cy.1 cy.2)) := by
  have hag : ∀ c' y', (c', y') ∈ pre ++ post →
      klongList B n.leaf (L B) c' y' = klongList A n.leaf (L A) c' y' := by
    intro c' y' h
    have hm' : (c', y') ∈ live n.ks := by
      rw [he]
      rcases List.mem_append.mp h with h | h <;> simp [h]
    have hz : ∀ z ∈ reachAt A (A.fuel y') y', B.obj z = A.obj z := by
      rw [← hG.tc_kid_eq hobj hm']
      exact hside c' y' h
    exact tc_klongList (hz y' (tc_self _ _ _)) (L_agree hz)
  rw [hGB.L_eq (hBu.trans hobj), hG.L_eq hobj, he]
  simp only [List.flatMap_append, List.flatMap_cons, and_true]
  congr 1
  · apply List.flatMap_congr
    rintro ⟨c', y'⟩ h
    exact hag c' y' (List.mem_append_left _ h)
  · congr 1
    apply List.flatMap_congr
    rintro ⟨c', y'⟩ h
    exact hag c' y' (List.mem_append_right _ h)

/-- `ctx_route` by induction on the route, for any range. -/
theorem tc_route {A B : Tree} {q : NodeId} (hk : KeepsKind A B q)
    (hloc : ∀ lo' hi', Good A q lo' hi' → Good B q lo' hi')
    {F : Key → List (Key × Nat) → List (Key × Nat)} (hF : LocalTo F) {k' : Key}
    (hL : L B q = F k' (L A q)) {u : NodeId} {k : Key} (hr : Route A u k q k') :
    ∀ {lo : Nat} {hi : Option Nat}, Good A u lo hi → (reachAt A (A.fuel u) u).Nodup →
      Agree A B u q → L B u = F k (L A u) := by
  induction hr with
  | here q k => intro _ _ _ _ _; exact hL
  | inner u n c y cv rest q k' hobj hl hm _ hlast hry ih =>
    intro lo hi hG hT ha
    obtain ⟨m, lo', hi', hm1, hm2, _, hg⟩ := hG.child hobj hm (by simp [hl])
    obtain ⟨⟨_, _, hgq⟩, hqy⟩ := hry.tc_target hg
    rw [← hG.tc_kid_eq hobj hm] at hqy
    have hqk := hgq.obj
    obtain ⟨pre, post, he⟩ := List.append_of_mem hm
    obtain ⟨hBu, hside, _, _, hTy, _, hay⟩ := hG.tc_step hobj hT ha hqk he hqy
    have hq : q ∈ reachAt A (A.fuel u) u := by
      rw [show A.fuel u = n.level + 1 by simp [Tree.fuel, hobj]]
      exact tc_kid hobj hm hqy
    have hGB := (tc_ctx hk hloc hqk hG hT hq ha).1
    obtain ⟨h1, h2⟩ := tc_L_split hG hGB hobj hBu he hside
    have hmB : klongList B n.leaf (L B) c y = L B y := by simp [klongList, hl]
    have hmA : klongList A n.leaf (L A) c y = L A y := by simp [klongList, hl]
    rw [h1, h2, hmB, hmA, ih hk hloc hL hg hTy hay]
    have hflat : ∀ l : List (Nat × NodeId),
        l.flatMap (fun cy => klongList A n.leaf (L A) cy.1 cy.2) =
          l.flatMap (fun cy => L A cy.2) := by
      intro l
      apply List.flatMap_congr
      intro cy _
      simp [klongList, hl]
    rw [hflat pre, hflat post]
    obtain ⟨_, hpost, _⟩ := live_split he
    have hmid := hF.mid (cv :: rest) (pre.flatMap (fun cy => L A cy.2)) (L A y)
      (post.flatMap (fun cy => L A cy.2)) ?_ ?_
    · simp only [List.append_assoc] at hmid
      rw [hmid]
    · rintro ⟨k0, v0⟩ h0
      obtain ⟨⟨c0, y0⟩, h0, hkv⟩ := List.mem_flatMap.mp h0
      obtain ⟨d, r', rfl, hd⟩ := hG.tc_kid_upper hobj hl he h0 k0 v0 hkv
      exact cons_lt_cons_of_lt (by omega) _ _
    · rintro ⟨k2, v2⟩ h2
      obtain ⟨⟨c2, y2⟩, h2, hkv⟩ := List.mem_flatMap.mp h2
      have hm2 : (c2, y2) ∈ live n.ks := by rw [he]; simp [h2]
      have hc2 : c < c2 := hpost (c2, y2) h2
      have hcv : cv < c2 := by
        by_contra hcon
        have := hlast c2 y2 hm2 (by omega)
        omega
      obtain ⟨d, r', rfl, hd⟩ := hG.kid_lower hobj hl hm2 k2 v2 hkv
      exact cons_lt_cons_of_lt (by omega) _ _
  | leaf u n c y rest q k' hobj hl hm hlong hry ih =>
    intro lo hi hG hT ha
    obtain ⟨m, lo', hi', hm1, hm2, _, hg⟩ := hG.child hobj hm (fun _ => hlong)
    obtain ⟨⟨_, _, hgq⟩, hqy⟩ := hry.tc_target hg
    rw [← hG.tc_kid_eq hobj hm] at hqy
    have hqk := hgq.obj
    obtain ⟨pre, post, he⟩ := List.append_of_mem hm
    obtain ⟨hBu, hside, _, _, hTy, _, hay⟩ := hG.tc_step hobj hT ha hqk he hqy
    have hq : q ∈ reachAt A (A.fuel u) u := by
      rw [show A.fuel u = n.level + 1 by simp [Tree.fuel, hobj]]
      exact tc_kid hobj hm hqy
    have hGB := (tc_ctx hk hloc hqk hG hT hq ha).1
    obtain ⟨h1, h2⟩ := tc_L_split hG hGB hobj hBu he hside
    have hmB : klongList B n.leaf (L B) c y = (L B y).map (fun kv => (c :: kv.1, kv.2)) := by
      simp [klongList, hl, hlong]
    have hmA : klongList A n.leaf (L A) c y = (L A y).map (fun kv => (c :: kv.1, kv.2)) := by
      simp [klongList, hl, hlong]
    rw [h1, h2, hmB, hmA, ih hk hloc hL hg hTy hay, ← hF.seg c rest (L A y)]
    obtain ⟨hpre, hpost, _⟩ := live_split he
    have hmid := hF.mid (c :: rest)
      (pre.flatMap (fun cy => klongList A n.leaf (L A) cy.1 cy.2))
      ((L A y).map (fun kv => (c :: kv.1, kv.2)))
      (post.flatMap (fun cy => klongList A n.leaf (L A) cy.1 cy.2)) ?_ ?_
    · simp only [List.append_assoc] at hmid
      rw [hmid]
    · rintro ⟨k0, v0⟩ h0
      obtain ⟨⟨c0, y0⟩, h0, hkv⟩ := List.mem_flatMap.mp h0
      have hc0 : c0 < c := hpre (c0, y0) h0
      rcases mem_klongList.mp hkv with ⟨_, _, k1, rfl, _⟩ | ⟨_, _, rfl, _⟩ | ⟨hl', _⟩
      · exact cons_lt_cons_of_lt hc0 _ _
      · exact cons_lt_cons_of_lt hc0 _ _
      · rw [hl] at hl'
        cases hl'
    · rintro ⟨k2, v2⟩ h2
      obtain ⟨⟨c2, y2⟩, h2, hkv⟩ := List.mem_flatMap.mp h2
      have hc2 : c < c2 := hpost (c2, y2) h2
      rcases mem_klongList.mp hkv with ⟨_, _, k1, rfl, _⟩ | ⟨_, _, rfl, _⟩ | ⟨hl', _⟩
      · exact cons_lt_cons_of_lt hc2 _ _
      · exact cons_lt_cons_of_lt hc2 _ _
      · rw [hl] at hl'
        cases hl'

/-- r holds in B the keys it holds in A with the change F for the key k, if
the key is routed from r to q with k' left and q holds in B what it holds in
A with the change F for k'. For the space root: the range of r is all. -/
theorem ctx_route {A B : Tree} {r q : NodeId} (hG : Good A r 0 none)
    (hT : (reachAt A (A.fuel r) r).Nodup) (ha : Agree A B r q)
    (hk : KeepsKind A B q)
    (hloc : ∀ lo' hi', Good A q lo' hi' → Good B q lo' hi')
    {F : Key → List (Key × Nat) → List (Key × Nat)} (hF : LocalTo F) {k k' : Key}
    (hr : Route A r k q k') (hL : L B q = F k' (L A q)) : L B r = F k (L A r) :=
  tc_route hk hloc hF hL hr hG hT ha

/-- The nodes reached from u in A and in B: the same before and after those
reached from q. -/
theorem tc_reach_split {A B : Tree} {q : NodeId} (hk : KeepsKind A B q)
    (hloc : ∀ lo' hi', Good A q lo' hi' → Good B q lo' hi') (hqk : ∃ n, A.obj q = some (.key n))
    {u : NodeId} {lo : Nat} {hi : Option Nat} (hG : Good A u lo hi) :
    (reachAt A (A.fuel u) u).Nodup → q ∈ reachAt A (A.fuel u) u → Agree A B u q →
      ∃ P S, reachAt A (A.fuel u) u = P ++ reachAt A (A.fuel q) q ++ S ∧
        reachAt B (B.fuel u) u = P ++ reachAt B (B.fuel q) q ++ S := by
  induction hG with
  | mk u lo hi n hobj hwf hhi hlo hval hkey hseg hkid ihseg ihkid =>
    intro hT hq ha
    have hG : Good A u lo hi := Good.mk u lo hi n hobj hwf hhi hlo hval hkey hseg hkid
    by_cases huq : u = q
    · subst huq
      exact ⟨[], [], by simp, by simp⟩
    have hfuel : A.fuel u = n.level + 1 := by simp [Tree.fuel, hobj]
    rw [hfuel] at hq
    rcases tc_mem_succ.mp hq with h | ⟨n', ho, ⟨c, y⟩, hm, hqy⟩
    · exact absurd h.symm huq
    rw [hobj] at ho
    cases ho
    obtain ⟨pre, post, he⟩ := List.append_of_mem hm
    obtain ⟨hBu, hside, hBy, hlong, hTy, hqy', hay⟩ := hG.tc_step hobj hT ha hqk he hqy
    have hBfuel : B.fuel u = n.level + 1 := by simp [Tree.fuel, hBu, hobj]
    have hIH : ∃ P S, reachAt A (A.fuel y) y = P ++ reachAt A (A.fuel q) q ++ S ∧
        reachAt B (B.fuel y) y = P ++ reachAt B (B.fuel q) q ++ S := by
      cases hl : n.leaf with
      | false => exact ihkid hl pre c y post he hTy hqy' hay
      | true => exact ihseg hl c y hm (hlong hl) hTy hqy' hay
    obtain ⟨P, S, hPA, hPB⟩ := hIH
    obtain ⟨m, lo', hi', hm1, hm2, _, hg⟩ := hG.child hobj hm hlong
    have hGBy := (tc_ctx hk hloc hqk hg hTy hqy' hay).1
    have hBfy : B.fuel y ≤ n.level := by
      by_cases hyq : y = q
      · rw [hyq] at hm1 ⊢
        obtain ⟨n'', h1, h2, _⟩ := hk m hm1
        simp only [Tree.fuel, h1]
        omega
      · simp only [Tree.fuel, hBy hyq, hm1]
        omega
    have hyB : reachAt B n.level y = reachAt B (B.fuel y) y := hGBy.reachAt_eq n.level hBfy
    have hyA : reachAt A n.level y = reachAt A (A.fuel y) y := hG.tc_kid_eq hobj hm
    have hsB : ∀ l : List (Nat × NodeId), (∀ cy ∈ l, cy ∈ pre ++ post) →
        l.flatMap (fun cy => reachAt B n.level cy.2) =
          l.flatMap (fun cy => reachAt A n.level cy.2) := by
      intro l hl'
      apply List.flatMap_congr
      rintro ⟨c', y'⟩ h
      exact reachAt_agree n.level y' (hside c' y' (hl' _ h))
    refine ⟨u :: pre.flatMap (fun cy => reachAt A n.level cy.2) ++ P,
      S ++ post.flatMap (fun cy => reachAt A n.level cy.2), ?_, ?_⟩
    · rw [hfuel, tc_key hobj, he, List.flatMap_append, List.flatMap_cons, hyA, hPA]
      simp
    · rw [hBfuel, tc_key (hBu.trans hobj), he, List.flatMap_append, List.flatMap_cons, hyB, hPB,
        hsB pre (fun cy h => List.mem_append_left _ h),
        hsB post (fun cy h => List.mem_append_right _ h)]
      simp

/-- TREE in B: no node is reached twice from r, if none is from q, and q's
subtree in B holds only nodes of its subtree in A and nodes not reached from r
in A. And a node reached from r in B is reached from q in B, or is reached
from r in A and not from q. -/
theorem ctx_reach {A B : Tree} {r q : NodeId} {lo : Nat} {hi : Option Nat}
    (hG : Good A r lo hi) (hT : (reachAt A (A.fuel r) r).Nodup)
    (hq : q ∈ reachAt A (A.fuel r) r) (ha : Agree A B r q)
    (hk : KeepsKind A B q) (hloc : ∀ lo' hi', Good A q lo' hi' → Good B q lo' hi')
    (hqk : ∃ n, A.obj q = some (.key n))
    (hR : (reachAt B (B.fuel q) q).Nodup)
    (hnew : ∀ z ∈ reachAt B (B.fuel q) q, z ∈ reachAt A (A.fuel q) q ∨ z ∉ reachAt A (A.fuel r) r) :
    (reachAt B (B.fuel r) r).Nodup ∧
      ∀ z ∈ reachAt B (B.fuel r) r,
        (z ∈ reachAt A (A.fuel r) r ∧ z ∉ reachAt A (A.fuel q) q) ∨ z ∈ reachAt B (B.fuel q) q := by
  obtain ⟨P, S, hA, hB⟩ := tc_reach_split hk hloc hqk hG hT hq ha
  have hp : ∀ X : List NodeId, (P ++ X ++ S).Perm (P ++ S ++ X) := fun X => by
    simpa only [List.append_assoc] using (List.perm_append_comm (l₁ := X) (l₂ := S)).append_left P
  rw [hA] at hT hnew
  rw [hB, hA]
  have hT' := (hp _).nodup_iff.mp hT
  rw [List.nodup_append] at hT'
  constructor
  · rw [(hp _).nodup_iff, List.nodup_append]
    refine ⟨hT'.1, hR, ?_⟩
    intro a ha b hb hab
    subst hab
    rcases hnew a hb with h | h
    · exact hT'.2.2 a ha a h rfl
    · apply h
      simp only [List.mem_append] at ha ⊢
      tauto
  · intro z hz
    simp only [List.mem_append] at hz
    rcases hz with (hz | hz) | hz
    · exact Or.inl ⟨by simp [hz], fun h => hT'.2.2 z (by simp [hz]) z h rfl⟩
    · exact Or.inr hz
    · exact Or.inl ⟨by simp [hz], fun h => hT'.2.2 z (by simp [hz]) z h rfl⟩

end Contract
