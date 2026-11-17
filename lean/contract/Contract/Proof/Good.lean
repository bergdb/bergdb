/-
The contract package (bergdb 030-04): the invariants as a statement to prove
from. `Good s x lo hi` says of key node x and the range [lo, hi) what the
walk of Statement.lean computes (`walk_good`). From it: what a node holds
does not depend on the fuel (`L`), every key below a node starts within the
node's range, what a node holds is in strictly increasing key order, and a
node with a live klong holds a key.
-/
import Contract.Proof.Node

namespace Contract

/-- What the walk finds true of key node x with the range [lo, hi). -/
inductive Good (s : Tree) : NodeId → Nat → Option Nat → Prop where
  | mk (x : NodeId) (lo : Nat) (hi : Option Nat) (n : KNode)
      (hobj : s.obj x = some (.key n))
      (hwf : klongsWf n.ks = true)
      (hhi : ∀ c y, (c, y) ∈ live n.ks → belowHi c hi = true)
      (hlo : n.leaf = true → ∀ c y, (c, y) ∈ live n.ks → lo ≤ c)
      (hval : n.leaf = true → ∀ c y, (c, y) ∈ live n.ks → isLong c = false →
        ∃ v, s.obj y = some (.val v))
      (hkey : ∀ c y, (c, y) ∈ live n.ks → (n.leaf = true → isLong c = true) →
        ∃ m, s.obj y = some (.key m) ∧ m.level < n.level ∧ live m.ks ≠ [])
      (hseg : n.leaf = true → ∀ c y, (c, y) ∈ live n.ks → isLong c = true → Good s y 0 none)
      (hkid : n.leaf = false → ∀ pre c y post, live n.ks = pre ++ (c, y) :: post →
        Good s y (max lo c) (nextHi post hi)) :
      Good s x lo hi

variable {p : Params} {s : Tree}

theorem kidsOk_at {n : KNode} {lo : Nat} {hi : Option Nat}
    {sub : NodeId → Nat → Option Nat → Bool} :
    ∀ (l pre : List (Nat × NodeId)) (c : Nat) (y : NodeId) (post : List (Nat × NodeId)),
      kidsOk s n lo hi sub l = true → l = pre ++ (c, y) :: post →
      kidOk s n lo hi sub c y post = true
  | [], pre, c, y, post, _, he => by simp at he
  | (c', y') :: rest, [], c, y, post, h, he => by
    simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at he
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := he
    simp only [kidsOk, Bool.and_eq_true] at h
    exact h.1
  | (c', y') :: rest, a :: pre, c, y, post, h, he => by
    simp only [List.cons_append, List.cons.injEq] at he
    simp only [kidsOk, Bool.and_eq_true] at h
    exact kidsOk_at rest pre c y post h.2 he.2

/-- The walk computes `Good`. -/
theorem walk_good : ∀ (f : Nat) (x : NodeId) (lo : Nat) (hi : Option Nat),
    walk p s f x lo hi = true → Good s x lo hi
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
        obtain ⟨hn, hk⟩ := h
        simp only [nodeOk, Bool.and_eq_true] at hn
        have hkid : ∀ c y, (c, y) ∈ live n.ks → ∃ pre post, live n.ks = pre ++ (c, y) :: post ∧
            kidOk s n lo hi (fun y lo' hi' => walk p s f y lo' hi') c y post = true := by
          intro c y hm
          obtain ⟨pre, post, he⟩ := List.append_of_mem hm
          exact ⟨pre, post, he, kidsOk_at _ pre c y post hk he⟩
        refine Good.mk x lo hi n ho hn.1.2 ?_ ?_ ?_ ?_ ?_ ?_
        · intro c y hm
          obtain ⟨pre, post, _, hko⟩ := hkid c y hm
          unfold kidOk at hko
          simp only [Bool.and_eq_true] at hko
          exact hko.1
        · intro hl c y hm
          obtain ⟨pre, post, _, hko⟩ := hkid c y hm
          unfold kidOk at hko
          simp only [hl, Bool.and_eq_true, ite_true, decide_eq_true_eq] at hko
          exact hko.2.1
        · intro hl c y hm hs
          obtain ⟨pre, post, _, hko⟩ := hkid c y hm
          unfold kidOk at hko
          simp only [hl, hs, Bool.and_eq_true, ite_true] at hko
          have h3 := hko.2.2
          cases hy : s.obj y with
          | none => simp [hy] at h3
          | some o =>
            cases o with
            | val v => exact ⟨v, rfl⟩
            | key m => simp [hy] at h3
        · intro c y hm hs
          obtain ⟨pre, post, _, hko⟩ := hkid c y hm
          unfold kidOk at hko
          cases hy : s.obj y with
          | none => by_cases hl : n.leaf = true <;> simp_all
          | some o =>
            cases o with
            | val v => by_cases hl : n.leaf = true <;> simp_all
            | key m =>
              refine ⟨m, rfl, ?_⟩
              by_cases hl : n.leaf = true
              · have := hs hl
                simp [hl, this, hy] at hko
                exact ⟨hko.2.2.1.1, hko.2.2.1.2⟩
              · simp [hl, hy] at hko
                exact ⟨hko.2.1.1, hko.2.1.2⟩
        · intro hl c y hm hs
          obtain ⟨pre, post, _, hko⟩ := hkid c y hm
          unfold kidOk at hko
          cases hy : s.obj y with
          | none => simp [hl, hs, hy] at hko
          | some o =>
            cases o with
            | val v => simp [hl, hs, hy] at hko
            | key m =>
              simp [hl, hs, hy] at hko
              exact walk_good f y 0 none hko.2.2.2
        · intro hl pre c y post he
          have hko := kidsOk_at _ pre c y post hk he
          unfold kidOk at hko
          cases hy : s.obj y with
          | none => simp [hl, hy] at hko
          | some o =>
            cases o with
            | val v => simp [hl, hy] at hko
            | key m =>
              simp [hl, hy] at hko
              exact walk_good f y _ _ hko.2.2

/-! ## The live klongs in order -/

theorem live_split {ks : List Klong} {pre post : List (Nat × NodeId)} {c : Nat} {y : NodeId}
    (he : live ks = pre ++ (c, y) :: post) :
    (∀ a ∈ pre, a.1 < c) ∧ (∀ b ∈ post, c < b.1) ∧ post.Pairwise CvLt := by
  have h := live_sorted ks
  rw [he, List.pairwise_append, List.pairwise_cons] at h
  refine ⟨fun a ha => h.2.2 a ha (c, y) (List.mem_cons_self), fun b hb => h.2.1.1 b hb, h.2.1.2⟩

theorem live_unique {ks : List Klong} {c : Nat} {y y' : NodeId}
    (h : (c, y) ∈ live ks) (h' : (c, y') ∈ live ks) : y = y' := by
  obtain ⟨pre, post, he⟩ := List.append_of_mem h
  obtain ⟨h1, h2, _⟩ := live_split he
  rw [he] at h'
  rcases List.mem_append.mp h' with hp | hp
  · exact absurd (h1 _ hp) (lt_irrefl c)
  · rcases List.mem_cons.mp hp with hp | hp
    · exact (Prod.mk.inj hp).2.symm
    · exact absurd (h2 _ hp) (lt_irrefl c)

theorem belowHi_of_lt {d c : Nat} {hi : Option Nat} (h : d < c) (hc : belowHi c hi = true) :
    belowHi d hi = true := by
  cases hi with
  | none => rfl
  | some b =>
    simp only [belowHi, decide_eq_true_eq] at hc ⊢
    omega

/-- Below the bound of a child: below every later live klong, and below the
node's own bound. -/
theorem below_nextHi {d : Nat} {post : List (Nat × NodeId)} {hi : Option Nat}
    (hp : post.Pairwise CvLt) (hh : ∀ b ∈ post, belowHi b.1 hi = true)
    (h : belowHi d (nextHi post hi) = true) :
    belowHi d hi = true ∧ ∀ b ∈ post, d < b.1 := by
  cases post with
  | nil => exact ⟨h, by simp⟩
  | cons a r =>
    simp only [nextHi, belowHi, decide_eq_true_eq] at h
    rw [List.pairwise_cons] at hp
    refine ⟨belowHi_of_lt h (hh a List.mem_cons_self), ?_⟩
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact h
    · exact lt_trans h (hp.1 b hb)

/-! ## What a node holds -/

/-- What key node x holds, with the fuel of its level. -/
def L (s : Tree) (x : NodeId) : List (Key × Nat) := listAt s (s.fuel x) x

/-- The order of keys with their values: by key. -/
abbrev KvLt (a b : Key × Nat) : Prop := a.1 < b.1

theorem mem_klongList {leaf : Bool} {sub : NodeId → List (Key × Nat)} {c : Nat} {y : NodeId}
    {k : Key} {v : Nat} :
    (k, v) ∈ klongList s leaf sub c y ↔
      (leaf = true ∧ isLong c = true ∧ ∃ k', k = c :: k' ∧ (k', v) ∈ sub y) ∨
      (leaf = true ∧ isLong c = false ∧ k = [c] ∧ s.obj y = some (.val v)) ∨
      (leaf = false ∧ (k, v) ∈ sub y) := by
  unfold klongList
  cases leaf with
  | false => simp
  | true =>
    cases hl : isLong c with
    | true =>
      simp only [ite_true, List.mem_map, Prod.mk.injEq, Prod.exists, true_and, Bool.true_eq_false,
        false_and, or_false]
      constructor
      · rintro ⟨a, b, hab, rfl, rfl⟩
        exact ⟨a, rfl, hab⟩
      · rintro ⟨k', rfl, hk⟩
        exact ⟨k', v, hk, rfl, rfl⟩
    | false =>
      cases hy : s.obj y with
      | none => simp
      | some o =>
        cases o with
        | key m => simp
        | val h =>
          simp
          exact fun _ => eq_comm

theorem Good.child {x : NodeId} {lo : Nat} {hi : Option Nat} (h : Good s x lo hi) {n : KNode}
    (hobj : s.obj x = some (.key n)) {c : Nat} {y : NodeId} (hm : (c, y) ∈ live n.ks)
    (hk : n.leaf = true → isLong c = true) :
    ∃ m lo' hi', s.obj y = some (.key m) ∧ m.level < n.level ∧ live m.ks ≠ [] ∧
      Good s y lo' hi' := by
  cases h with
  | mk x lo hi n' hobj' hwf hhi hlo hval hkey hseg hkid =>
    rw [hobj] at hobj'
    obtain rfl : n = n' := by injection hobj' with h1; injection h1
    obtain ⟨m, hm1, hm2, hm3⟩ := hkey c y hm hk
    cases hl : n.leaf with
    | true => exact ⟨m, 0, none, hm1, hm2, hm3, hseg hl c y hm (hk hl)⟩
    | false =>
      obtain ⟨pre, post, he⟩ := List.append_of_mem hm
      exact ⟨m, _, _, hm1, hm2, hm3, hkid hl pre c y post he⟩

/-- What a sound node holds does not depend on the fuel, if it is enough. -/
theorem Good.listAt_eq {x : NodeId} {lo : Nat} {hi : Option Nat} (h : Good s x lo hi) :
    ∀ f, s.fuel x ≤ f → listAt s f x = L s x := by
  induction h with
  | mk x lo hi n hobj hwf hhi hlo hval hkey hseg hkid ihseg ihkid =>
    intro f hf
    have hfuel : s.fuel x = n.level + 1 := by simp [Tree.fuel, hobj]
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    unfold L
    rw [hfuel]
    simp only [listAt, hobj]
    apply List.flatMap_congr
    rintro ⟨c, y⟩ hm
    have key : (n.leaf = true → isLong c = true) → listAt s f' y = listAt s n.level y := by
      intro hk
      obtain ⟨m, hm1, hm2, _⟩ := hkey c y hm hk
      have hfy : s.fuel y = m.level + 1 := by simp [Tree.fuel, hm1]
      cases hl : n.leaf with
      | true =>
        rw [ihseg hl c y hm (hk hl) f' (by omega), ihseg hl c y hm (hk hl) n.level (by omega)]
      | false =>
        obtain ⟨pre, post, he⟩ := List.append_of_mem hm
        rw [ihkid hl pre c y post he f' (by omega), ihkid hl pre c y post he n.level (by omega)]
    unfold klongList
    cases hl : n.leaf with
    | false => simp only [Bool.false_eq_true, ite_false]; exact key (by simp [hl])
    | true =>
      cases hlong : isLong c with
      | true => simp only [ite_true]; rw [key (fun _ => hlong)]
      | false => rfl

/-- What a sound node holds, from what its live klongs hold. -/
theorem Good.L_eq {x : NodeId} {lo : Nat} {hi : Option Nat} (h : Good s x lo hi) {n : KNode}
    (hobj : s.obj x = some (.key n)) :
    L s x = (live n.ks).flatMap (fun cy => klongList s n.leaf (L s) cy.1 cy.2) := by
  have hfuel : s.fuel x = n.level + 1 := by simp [Tree.fuel, hobj]
  unfold L
  rw [hfuel]
  simp only [listAt, hobj]
  apply List.flatMap_congr
  rintro ⟨c, y⟩ hm
  have key : (n.leaf = true → isLong c = true) → listAt s n.level y = listAt s (s.fuel y) y := by
    intro hk
    obtain ⟨m, lo', hi', hm1, hm2, _, hg⟩ := h.child hobj hm hk
    have hfy : s.fuel y = m.level + 1 := by simp [Tree.fuel, hm1]
    exact hg.listAt_eq n.level (by omega)
  unfold klongList
  cases hl : n.leaf with
  | false => simp only [Bool.false_eq_true, ite_false]; exact key (by simp [hl])
  | true =>
    cases hlong : isLong c with
    | true => simp only [ite_true]; rw [key (fun _ => hlong)]
    | false => rfl

/-- Every key below a sound node has a first segment, within the node's range. -/
theorem Good.range {x : NodeId} {lo : Nat} {hi : Option Nat} (h : Good s x lo hi) :
    ∀ k v, (k, v) ∈ L s x → ∃ d r, k = d :: r ∧ lo ≤ d ∧ belowHi d hi = true := by
  induction h with
  | mk x lo hi n hobj hwf hhi hlo hval hkey hseg hkid ihseg ihkid =>
    intro k v hkv
    have hG : Good s x lo hi := Good.mk x lo hi n hobj hwf hhi hlo hval hkey hseg hkid
    rw [hG.L_eq hobj, List.mem_flatMap] at hkv
    obtain ⟨⟨c, y⟩, hm, hkv⟩ := hkv
    rcases mem_klongList.mp hkv with ⟨hl, _, k', rfl, _⟩ | ⟨hl, _, rfl, _⟩ | ⟨hl, hkv⟩
    · exact ⟨c, k', rfl, hlo hl c y hm, hhi c y hm⟩
    · exact ⟨c, [], rfl, hlo hl c y hm, hhi c y hm⟩
    · obtain ⟨pre, post, he⟩ := List.append_of_mem hm
      obtain ⟨d, r, rfl, hd1, hd2⟩ := ihkid hl pre c y post he k v hkv
      obtain ⟨_, h2, h3⟩ := live_split he
      have hpost : ∀ b ∈ post, belowHi b.1 hi = true := by
        intro b hb
        exact hhi b.1 b.2 (by rw [he]; simp [hb])
      exact ⟨d, r, rfl, le_trans (le_max_left _ _) hd1, (below_nextHi h3 hpost hd2).1⟩

/-- What a sound node holds is in strictly increasing key order. -/
theorem Good.sorted {x : NodeId} {lo : Nat} {hi : Option Nat} (h : Good s x lo hi) :
    (L s x).Pairwise KvLt := by
  induction h with
  | mk x lo hi n hobj hwf hhi hlo hval hkey hseg hkid ihseg ihkid =>
    have hG : Good s x lo hi := Good.mk x lo hi n hobj hwf hhi hlo hval hkey hseg hkid
    rw [hG.L_eq hobj]
    have main : ∀ (cs pre : List (Nat × NodeId)), live n.ks = pre ++ cs →
        (cs.flatMap (fun cy => klongList s n.leaf (L s) cy.1 cy.2)).Pairwise KvLt ∧
        ∀ k v, (k, v) ∈ cs.flatMap (fun cy => klongList s n.leaf (L s) cy.1 cy.2) →
          ∃ d r, k = d :: r ∧ ∀ c0 y0 rest, cs = (c0, y0) :: rest → c0 ≤ d := by
      intro cs
      induction cs with
      | nil => intro pre _; simp
      | cons a post ih =>
        obtain ⟨c, y⟩ := a
        intro pre he
        obtain ⟨ihp, ihh⟩ := ih (pre ++ [(c, y)]) (by simp [he])
        obtain ⟨_, hpost, hpp⟩ := live_split he
        have hm : (c, y) ∈ live n.ks := by rw [he]; simp
        have hE : (klongList s n.leaf (L s) c y).Pairwise KvLt ∧
            ∀ k v, (k, v) ∈ klongList s n.leaf (L s) c y →
              ∃ d r, k = d :: r ∧ c ≤ d ∧ ∀ b ∈ post, d < b.1 := by
          constructor
          · by_cases hl : n.leaf = true
            · by_cases hlong : isLong c = true
              · simp only [klongList, hl, hlong, ite_true]
                rw [List.pairwise_map]
                exact (ihseg hl c y hm hlong).imp
                  (fun h => List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, h⟩))
              · have hlong' : isLong c = false := by simpa using hlong
                unfold klongList
                simp only [hl, hlong', ite_true, Bool.false_eq_true, ite_false]
                split
                · exact List.pairwise_singleton _ _
                · exact List.Pairwise.nil
            · have hl' : n.leaf = false := by simpa using hl
              simp only [klongList, hl']
              exact ihkid hl' pre c y post he
          · intro k v hkv
            rcases mem_klongList.mp hkv with ⟨_, _, k', rfl, _⟩ | ⟨_, _, rfl, _⟩ | ⟨hl, hkv⟩
            · exact ⟨c, k', rfl, le_refl c, hpost⟩
            · exact ⟨c, [], rfl, le_refl c, hpost⟩
            · obtain ⟨d, r, rfl, hd1, hd2⟩ := (hkid hl pre c y post he).range k v hkv
              have := below_nextHi hpp (fun b hb => hhi b.1 b.2 (by rw [he]; simp [hb])) hd2
              exact ⟨d, r, rfl, le_trans (le_max_right _ _) hd1, this.2⟩
        simp only [List.flatMap_cons]
        constructor
        · rw [List.pairwise_append]
          refine ⟨hE.1, ihp, ?_⟩
          rintro ⟨k, v⟩ hkv ⟨k', v'⟩ hkv'
          obtain ⟨d, r, rfl, _, hd⟩ := hE.2 k v hkv
          obtain ⟨d', r', rfl, hd'⟩ := ihh k' v' hkv'
          cases post with
          | nil => simp at hkv'
          | cons b rest =>
            have h1 : d < b.1 := hd b (by simp)
            have h2 : b.1 ≤ d' := hd' b.1 b.2 rest rfl
            exact List.cons_lt_cons_iff.mpr (Or.inl (lt_of_lt_of_le h1 h2))
        · intro k v hkv
          rcases List.mem_append.mp hkv with hkv | hkv
          · obtain ⟨d, r, rfl, hd, _⟩ := hE.2 k v hkv
            refine ⟨d, r, rfl, ?_⟩
            intro c0 y0 rest he0
            injection he0 with h1 _
            injection h1 with h1 _
            omega
          · obtain ⟨d, r, rfl, hd'⟩ := ihh k v hkv
            cases post with
            | nil => simp at hkv
            | cons b rest =>
              refine ⟨d, r, rfl, ?_⟩
              intro c0 y0 rest0 he0
              have h1 : c < b.1 := hpost b (by simp)
              have h2 := hd' b.1 b.2 rest rfl
              injection he0 with h3 _
              injection h3 with h3 _
              omega
    exact (main (live n.ks) [] rfl).1

/-- A sound node with a live klong holds a key. -/
theorem Good.nonempty {x : NodeId} {lo : Nat} {hi : Option Nat} (h : Good s x lo hi) :
    ∀ n, s.obj x = some (.key n) → live n.ks ≠ [] → L s x ≠ [] := by
  induction h with
  | mk x lo hi n hobj hwf hhi hlo hval hkey hseg hkid ihseg ihkid =>
    intro n' hobj' hne
    have hG : Good s x lo hi := Good.mk x lo hi n hobj hwf hhi hlo hval hkey hseg hkid
    rw [hobj] at hobj'
    obtain rfl : n = n' := by injection hobj' with h1; injection h1
    rw [hG.L_eq hobj]
    cases hlive : live n.ks with
    | nil => exact absurd hlive hne
    | cons a post =>
      obtain ⟨c, y⟩ := a
      have hm : (c, y) ∈ live n.ks := by rw [hlive]; simp
      simp only [List.flatMap_cons]
      intro hnil
      have hE : klongList s n.leaf (L s) c y = [] := (List.append_eq_nil_iff.mp hnil).1
      by_cases hl : n.leaf = true
      · by_cases hlong : isLong c = true
        · obtain ⟨m, hm1, _, hm3⟩ := hkey c y hm (fun _ => hlong)
          have := ihseg hl c y hm hlong m hm1 hm3
          simp [klongList, hl, hlong] at hE
          exact this hE
        · have hlong' : isLong c = false := by simpa using hlong
          obtain ⟨v, hv⟩ := hval hl c y hm hlong'
          simp [klongList, hl, hlong', hv] at hE
      · have hl' : n.leaf = false := by simpa using hl
        obtain ⟨m, hm1, _, hm3⟩ := hkey c y hm (by simp [hl'])
        have := ihkid hl' [] c y post (by simpa using hlive) m hm1 hm3
        simp [klongList, hl'] at hE
        exact this hE

end Contract
