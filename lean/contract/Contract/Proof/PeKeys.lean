/-
bergdb 030-21: the keys of PE's writer, split by a key's first segment. The
contract's plain map (Statement.lean, section 4: `mapPut`, `mapDel`,
`applyOps`) is over whole keys; PE plans each segment's tree on compare
values: at segment g an operation's compare value is `segAt g op`, and a
segment leaf's entry (c, y) holds, as keys (`klongList`), [c] with y's value
for a short c, and every key of the next segment's tree at y with c in front
for a long c. What is proved here, on lists only, is that the contract's map,
split by a key's first segment, is the per-compare-value change that PE
makes:

1. The blocks (`applyOps_blocks`): a map in key order is the concatenation of
   its blocks by first segment, in order; the operations act on each block by
   the operations of its first segment.
2. The prefix (`applyOps_prefix`, `applyOps_cons_prefix`): operations whose
   keys share a front act on the map behind the front as the operations with
   the front dropped.
3. One key (`applyOps_one_key`): the operations of one key on a map of that
   key alone (or the empty map) have the last operation's effect.
4. The noops (`applyOps_dropNoops`): the deletes that `dropNoops` drops
   change nothing on a map of keys the tree can hold.
5. Relative keys (`dropKey`): the key with its first g segments dropped, and
   how `segAt`, `endsAt` and a well formed key (`keyWf`) read on it. With
   them, parts 1 to 3 at segment g: `applyOps_segment` (the blocks of a
   segment's tree whose keys share a front of g segments, by
   `applyGroups`'s groups), `applyOps_short_block` (a short compare value:
   one key, part 3) and `applyOps_cons_block` (a long one: the next
   segment's tree, part 2); and a segment leaf's `klongList` meets the
   blocks' premises (`klongList_head`, `klongList_sorted`, `klongList_short`,
   `klongList_long`).

`KvLt` (Good.lean) is the key order of Lex.lean, `keyLt` as a proposition
(`kvLt_iff_keyLt`).
-/
import Mathlib.Tactic
import Contract.PeWriter
import Contract.Proof.Lex
import Contract.Proof.Good

namespace PeProof.Keys

open Contract Contract.PE

/-! ## The plain map, one step at a time -/

/-- One operation applied to the plain map. -/
def step (m : List (Key × Nat)) : Op → List (Key × Nat)
  | .put k v => mapPut k v m
  | .del k => mapDel k m

theorem applyOps_nil' (m : List (Key × Nat)) : applyOps [] m = m := rfl

theorem applyOps_cons' (op : Op) (ops : List Op) (m : List (Key × Nat)) :
    applyOps (op :: ops) m = applyOps ops (step m op) := by
  cases op <;> rfl

theorem applyOps_append' (ops ops' : List Op) (m : List (Key × Nat)) :
    applyOps (ops ++ ops') m = applyOps ops' (applyOps ops m) := by
  induction ops generalizing m with
  | nil => rfl
  | cons op ops ih => rw [List.cons_append, applyOps_cons', applyOps_cons', ih]

theorem applyOps_concat (ops : List Op) (op : Op) (m : List (Key × Nat)) :
    applyOps (ops ++ [op]) m = step (applyOps ops m) op := by
  rw [applyOps_append', applyOps_cons', applyOps_nil']

theorem kvLt_iff_keyLt (a b : Key × Nat) : KvLt a b ↔ keyLt a.1 b.1 = true :=
  (keyLt_iff a.1 b.1).symm

/-- A map sorted strictly by `keyLt` is sorted by `KvLt`. -/
theorem pairwise_kvLt_iff (m : List (Key × Nat)) :
    m.Pairwise KvLt ↔ m.Pairwise (fun a b => keyLt a.1 b.1 = true) := by
  constructor <;> intro h <;> exact h.imp (fun hab => by simpa [kvLt_iff_keyLt] using hab)

theorem keyLt_self (k : Key) : keyLt k k = false := by
  rw [keyLt_false_iff]

/-! ## mapPut and mapDel -/

theorem mem_mapPut {k : Key} {v : Nat} {e : Key × Nat} :
    ∀ {m : List (Key × Nat)}, e ∈ mapPut k v m → e = (k, v) ∨ e ∈ m
  | [], h => by simpa [mapPut] using h
  | (k', v') :: r, h => by
    unfold mapPut at h
    split_ifs at h with h1 h2
    · simpa using h
    · simp only [List.mem_cons] at h
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)
    · simp only [List.mem_cons] at h
      rcases h with h | h
      · exact Or.inr (by simp [h])
      · rcases mem_mapPut h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)

theorem mem_mapDel {k : Key} {e : Key × Nat} {m : List (Key × Nat)} (h : e ∈ mapDel k m) :
    e ∈ m := (List.mem_filter.mp h).1

theorem mem_step {m : List (Key × Nat)} {op : Op} {e : Key × Nat} (h : e ∈ step m op) :
    e ∈ m ∨ (∃ v, op = .put e.1 v) := by
  cases op with
  | put k v =>
    rcases mem_mapPut h with h | h
    · exact Or.inr ⟨v, by simp [h]⟩
    · exact Or.inl h
  | del k => exact Or.inl (mem_mapDel h)

/-- Every key of the map after the operations is a key of the map before or
a key that an operation puts. -/
theorem mem_applyOps : ∀ {ops : List Op} {m : List (Key × Nat)} {e : Key × Nat},
    e ∈ applyOps ops m → e ∈ m ∨ ∃ op ∈ ops, ∃ v, op = .put e.1 v
  | [], _, _, h => Or.inl h
  | op :: ops, m, e, h => by
    rw [applyOps_cons'] at h
    rcases mem_applyOps h with h | ⟨op', hop', hv⟩
    · rcases mem_step h with h | h
      · exact Or.inl h
      · exact Or.inr ⟨op, by simp, h⟩
    · exact Or.inr ⟨op', List.mem_cons_of_mem _ hop', hv⟩

/-- A property of keys that holds for every key of the map and every key an
operation puts holds for every key of the map after the operations. -/
theorem applyOps_keys {Q : Key → Prop} {ops : List Op} {m : List (Key × Nat)}
    (hm : ∀ e ∈ m, Q e.1) (hops : ∀ op ∈ ops, Q op.key) :
    ∀ e ∈ applyOps ops m, Q e.1 := by
  intro e he
  rcases mem_applyOps he with h | ⟨op, hop, v, rfl⟩
  · exact hm e h
  · exact hops _ hop

/-- A put into a map whose keys are all above the key puts it first. -/
theorem mapPut_of_lt {k : Key} {v : Nat} :
    ∀ {m : List (Key × Nat)}, (∀ e ∈ m, k < e.1) → mapPut k v m = (k, v) :: m
  | [], _ => rfl
  | (k', v') :: r, h => by
    have : k < k' := h (k', v') (by simp)
    simp [mapPut, (keyLt_iff k k').mpr this]

theorem mapPut_sorted {k : Key} {v : Nat} :
    ∀ {m : List (Key × Nat)}, m.Pairwise KvLt → (mapPut k v m).Pairwise KvLt
  | [], _ => List.pairwise_singleton _ _
  | (k', v') :: r, h => by
    rw [List.pairwise_cons] at h
    unfold mapPut
    split_ifs with h1 h2
    · have h1 : k < k' := (keyLt_iff k k').mp h1
      refine List.Pairwise.cons ?_ (List.Pairwise.cons h.1 h.2)
      intro e he
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · exact h1
      · exact lt_trans h1 (h.1 e he)
    · subst h2
      exact List.Pairwise.cons h.1 h.2
    · have h3 : k' < k := by
        rcases lt_trichotomy k' k with h3 | h3 | h3
        · exact h3
        · exact absurd h3.symm h2
        · exact absurd ((keyLt_iff k k').mpr h3) h1
      refine List.Pairwise.cons ?_ (mapPut_sorted h.2)
      intro e he
      rcases mem_mapPut he with rfl | he
      · exact h3
      · exact h.1 e he

theorem step_sorted {m : List (Key × Nat)} (op : Op) (h : m.Pairwise KvLt) :
    (step m op).Pairwise KvLt := by
  cases op with
  | put k v => exact mapPut_sorted h
  | del k => exact h.filter _

/-- The operations keep a map in key order. -/
theorem applyOps_sorted : ∀ {ops : List Op} {m : List (Key × Nat)},
    m.Pairwise KvLt → (applyOps ops m).Pairwise KvLt
  | [], _, h => h
  | op :: ops, _, h => by
    rw [applyOps_cons']
    exact applyOps_sorted (step_sorted op h)

/-! ## A filter by keys commutes with the operations -/

theorem mapPut_cons_lt {k k' : Key} {v v' : Nat} {r : List (Key × Nat)} (h : k < k') :
    mapPut k v ((k', v') :: r) = (k, v) :: (k', v') :: r := by
  simp [mapPut, (keyLt_iff k k').mpr h]

theorem mapPut_cons_self {k : Key} {v v' : Nat} {r : List (Key × Nat)} :
    mapPut k v ((k, v') :: r) = (k, v) :: r := by
  simp [mapPut, keyLt_self]

theorem mapPut_cons_gt {k k' : Key} {v v' : Nat} {r : List (Key × Nat)} (h : k' < k) :
    mapPut k v ((k', v') :: r) = (k', v') :: mapPut k v r := by
  have h1 : keyLt k k' = false := (keyLt_false_iff k k').mpr (le_of_lt h)
  have h2 : k ≠ k' := fun e => lt_irrefl k (e ▸ h)
  simp [mapPut, h1, h2]

theorem mapPut_filter_pos {P : Key → Bool} {k : Key} {v : Nat} (hk : P k = true) :
    ∀ {m : List (Key × Nat)}, m.Pairwise KvLt →
      (mapPut k v m).filter (fun e => P e.1) = mapPut k v (m.filter (fun e => P e.1))
  | [], _ => by simp [mapPut, hk]
  | (k', v') :: r, h => by
    rw [List.pairwise_cons] at h
    rcases lt_trichotomy k k' with h1 | rfl | h1
    · have hall : ∀ e ∈ (k', v') :: r, k < e.1 := by
        intro e he
        rcases List.mem_cons.mp he with rfl | he
        · exact h1
        · exact lt_trans h1 (h.1 e he)
      rw [mapPut_of_lt hall, List.filter_cons_of_pos (by simpa using hk), mapPut_of_lt]
      intro e he
      exact hall e (List.mem_filter.mp he).1
    · rw [mapPut_cons_self, List.filter_cons_of_pos (by simpa using hk),
        List.filter_cons_of_pos (by simpa using hk), mapPut_cons_self]
    · rw [mapPut_cons_gt h1, List.filter_cons, List.filter_cons, mapPut_filter_pos hk h.2]
      split
      · rw [mapPut_cons_gt h1]
      · rfl

theorem mapPut_filter_neg {P : Key → Bool} {k : Key} {v : Nat} (hk : P k = false) :
    ∀ (m : List (Key × Nat)),
      (mapPut k v m).filter (fun e => P e.1) = m.filter (fun e => P e.1)
  | [] => by simp [mapPut, hk]
  | (k', v') :: r => by
    rcases lt_trichotomy k k' with h1 | rfl | h1
    · rw [mapPut_cons_lt h1, List.filter_cons_of_neg (by simp [hk])]
    · rw [mapPut_cons_self, List.filter_cons_of_neg (by simp [hk]),
        List.filter_cons_of_neg (by simp [hk])]
    · rw [mapPut_cons_gt h1, List.filter_cons, List.filter_cons, mapPut_filter_neg hk r]

theorem mapDel_filter (P : Key → Bool) (k : Key) (m : List (Key × Nat)) :
    (mapDel k m).filter (fun e => P e.1) = mapDel k (m.filter (fun e => P e.1)) := by
  simp only [mapDel, List.filter_filter]
  apply List.filter_congr
  intro x _
  exact Bool.and_comm _ _

theorem mapDel_filter_neg {P : Key → Bool} {k : Key} (hk : P k = false) (m : List (Key × Nat)) :
    (mapDel k m).filter (fun e => P e.1) = m.filter (fun e => P e.1) := by
  simp only [mapDel, List.filter_filter]
  apply List.filter_congr
  intro x _
  by_cases hx : P x.1 = true
  · have : x.1 ≠ k := fun e => by rw [e, hk] at hx; exact Bool.false_ne_true hx
    simp [hx, this]
  · simp [hx]

/-- **The filter.** On a map in key order, the operations and a filter by a
property of keys commute: the filtered map after the operations is the
filtered map after the operations of the keys that have the property. -/
theorem applyOps_filter (P : Key → Bool) : ∀ (ops : List Op) (m : List (Key × Nat)),
    m.Pairwise KvLt →
      (applyOps ops m).filter (fun e => P e.1) =
        applyOps (ops.filter (fun op => P op.key)) (m.filter (fun e => P e.1))
  | [], _, _ => rfl
  | op :: ops, m, h => by
    rw [applyOps_cons', applyOps_filter P ops _ (step_sorted op h)]
    by_cases hp : P op.key = true
    · rw [List.filter_cons_of_pos (p := fun op : Op => P op.key) hp, applyOps_cons']
      congr 1
      cases op with
      | put k v => exact mapPut_filter_pos hp h
      | del k => exact mapDel_filter P k m
    · rw [List.filter_cons_of_neg (p := fun op : Op => P op.key) hp]
      congr 1
      have hp' : P op.key = false := by simpa using hp
      cases op with
      | put k v => exact mapPut_filter_neg hp' m
      | del k => exact mapDel_filter_neg hp' m

/-! ## Maps in key order -/

/-- Two maps in key order with the same pairs are equal. -/
theorem eq_of_mem_iff : ∀ {l1 l2 : List (Key × Nat)}, l1.Pairwise KvLt → l2.Pairwise KvLt →
    (∀ e, e ∈ l1 ↔ e ∈ l2) → l1 = l2
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => absurd ((h b).mpr (by simp)) (by simp)
  | a :: _, [], _, _, h => absurd ((h a).mp (by simp)) (by simp)
  | a :: t1, b :: t2, h1, h2, h => by
    rw [List.pairwise_cons] at h1 h2
    have hab : a = b := by
      by_contra hne
      have ha : a ∈ t2 := by
        rcases List.mem_cons.mp ((h a).mp (by simp)) with h' | h'
        · exact absurd h' hne
        · exact h'
      have hb : b ∈ t1 := by
        rcases List.mem_cons.mp ((h b).mpr (by simp)) with h' | h'
        · exact absurd h'.symm hne
        · exact h'
      exact lt_asymm (h1.1 b hb) (h2.1 a ha)
    subst hab
    congr 1
    apply eq_of_mem_iff h1.2 h2.2
    intro e
    constructor
    · intro he
      rcases List.mem_cons.mp ((h e).mp (List.mem_cons_of_mem _ he)) with h' | h'
      · subst h'; exact absurd (h1.1 _ he) (lt_irrefl _)
      · exact h'
    · intro he
      rcases List.mem_cons.mp ((h e).mpr (List.mem_cons_of_mem _ he)) with h' | h'
      · subst h'; exact absurd (h2.1 _ he) (lt_irrefl _)
      · exact h'

/-- The block of compare value c of a map: its keys whose first segment is c. -/
def blk (c : Nat) (m : List (Key × Nat)) : List (Key × Nat) :=
  m.filter (fun e => decide (e.1.head? = some c))

/-- Two maps in key order, of nonempty keys, with the same block for every
compare value are equal. -/
theorem eq_of_blocks {l1 l2 : List (Key × Nat)} (h1 : l1.Pairwise KvLt) (h2 : l2.Pairwise KvLt)
    (hn1 : ∀ e ∈ l1, e.1 ≠ []) (hn2 : ∀ e ∈ l2, e.1 ≠ []) (hb : ∀ c, blk c l1 = blk c l2) :
    l1 = l2 := by
  apply eq_of_mem_iff h1 h2
  have key : ∀ (la lb : List (Key × Nat)), (∀ e ∈ la, e.1 ≠ []) → (∀ c, blk c la = blk c lb) →
      ∀ e ∈ la, e ∈ lb := by
    intro la lb hn hb e he
    obtain ⟨c, r, hcr⟩ := List.exists_cons_of_ne_nil (hn e he)
    have : e ∈ blk c la := List.mem_filter.mpr ⟨he, by simp [hcr]⟩
    rw [hb c] at this
    exact (List.mem_filter.mp this).1
  intro e
  exact ⟨key l1 l2 hn1 hb e, key l2 l1 hn2 (fun c => (hb c).symm) e⟩

/-! ## The blocks of a list of entries -/

/-- What an entry holds, by its child: nothing for none. -/
def entry (B : Nat → Nat → List (Key × Nat)) (c : Nat) : Option Nat → List (Key × Nat)
  | none => []
  | some y => B c y

/-- Entries sorted strictly by compare value. -/
abbrev CvSorted (E : List (Nat × Nat)) : Prop := E.Pairwise (fun a b => a.1 < b.1)

theorem lookup_of_mem : ∀ {E : List (Nat × Nat)} {c y : Nat}, CvSorted E → (c, y) ∈ E →
    E.lookup c = some y
  | [], _, _, _, h => absurd h (by simp)
  | (c', y') :: rest, c, y, hs, h => by
    rw [CvSorted, List.pairwise_cons] at hs
    rw [List.lookup_cons]
    rcases List.mem_cons.mp h with h | h
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp
    · have hlt : c' < c := hs.1 (c, y) h
      have : (c == c') = false := by simp; omega
      rw [this]
      exact lookup_of_mem hs.2 h

theorem mem_of_lookup {E : List (Nat × Nat)} {c y : Nat} (h : E.lookup c = some y) :
    (c, y) ∈ E := by
  obtain ⟨l1, l2, rfl, _⟩ := List.lookup_eq_some_iff.mp h
  simp

/-- The block of compare value c of the concatenation of the entries'
blocks is the block of c's entry. -/
theorem blk_flatMap (B : Nat → Nat → List (Key × Nat)) (c : Nat) :
    ∀ (E : List (Nat × Nat)), CvSorted E →
      (∀ e ∈ E, ∀ kv ∈ B e.1 e.2, kv.1.head? = some e.1) →
      blk c (E.flatMap (fun e => B e.1 e.2)) = entry B c (E.lookup c)
  | [], _, _ => rfl
  | (c', y') :: rest, hs, hb => by
    rw [CvSorted, List.pairwise_cons] at hs
    rw [blk, List.flatMap_cons, List.filter_append, List.lookup_cons]
    by_cases hc : c = c'
    · subst hc
      have h1 : (B c y').filter (fun e => decide (e.1.head? = some c)) = B c y' :=
        List.filter_eq_self.mpr (fun kv hkv => by simp [hb (c, y') (by simp) kv hkv])
      have h2 : (rest.flatMap (fun e => B e.1 e.2)).filter (fun e => decide (e.1.head? = some c))
          = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro kv hkv
        obtain ⟨e, he, hkv⟩ := List.mem_flatMap.mp hkv
        have h3 := hb e (List.mem_cons_of_mem _ he) kv hkv
        have hlt : c < e.1 := hs.1 e he
        simp only [h3, Option.some.injEq, decide_eq_true_eq]
        omega
      rw [h1, h2]
      simp [entry]
    · have h1 : (B c' y').filter (fun e => decide (e.1.head? = some c)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro kv hkv
        have h3 := hb (c', y') (by simp) kv hkv
        simp only [h3, Option.some.injEq, decide_eq_true_eq]
        omega
      have ih := blk_flatMap B c rest hs.2 (fun e he => hb e (List.mem_cons_of_mem _ he))
      rw [blk] at ih
      rw [h1, ih]
      have : (c == c') = false := by simp [hc]
      simp [this]

/-- The concatenation of blocks in key order, each of its entry's compare
value, the entries in compare order, is in key order. -/
theorem flatMap_sorted (B : Nat → Nat → List (Key × Nat)) (E : List (Nat × Nat)) (hs : CvSorted E)
    (hb : ∀ e ∈ E, ∀ kv ∈ B e.1 e.2, kv.1.head? = some e.1)
    (hbs : ∀ e ∈ E, (B e.1 e.2).Pairwise KvLt) :
    (E.flatMap (fun e => B e.1 e.2)).Pairwise KvLt := by
  rw [List.pairwise_flatMap]
  refine ⟨hbs, hs.imp_of_mem ?_⟩
  intro a b ha hb' hab x hx y hy
  obtain ⟨tx, htx⟩ := List.head?_eq_some_iff.mp (hb a ha x hx)
  obtain ⟨ty, hty⟩ := List.head?_eq_some_iff.mp (hb b hb' y hy)
  show x.1 < y.1
  rw [htx, hty]
  exact List.cons_lt_cons_iff.mpr (Or.inl hab)

theorem flatMap_ne_nil (B : Nat → Nat → List (Key × Nat)) (E : List (Nat × Nat))
    (hb : ∀ e ∈ E, ∀ kv ∈ B e.1 e.2, kv.1.head? = some e.1) :
    ∀ kv ∈ E.flatMap (fun e => B e.1 e.2), kv.1 ≠ [] := by
  intro kv hkv
  obtain ⟨e, he, hkv⟩ := List.mem_flatMap.mp hkv
  intro h
  have := hb e he kv hkv
  rw [h] at this
  simp at this

/-- **The blocks**, with a premise for every compare value. Entries E before
and E' after, sorted strictly by compare value; Bs and BT what an entry
holds before and after, each block in key order with keys that start with
its entry's compare value; operations of nonempty keys. If for every compare
value c the block of c after is the block of c before with the operations of
the keys that start with c applied, the concatenation of the blocks after is
the concatenation before with the operations applied. -/
theorem applyOps_blocks_all (Bs BT : Nat → Nat → List (Key × Nat)) (E E' : List (Nat × Nat))
    (ops : List Op) (hE : CvSorted E) (hE' : CvSorted E')
    (hBs : ∀ e ∈ E, ∀ kv ∈ Bs e.1 e.2, kv.1.head? = some e.1)
    (hBsS : ∀ e ∈ E, (Bs e.1 e.2).Pairwise KvLt)
    (hBT : ∀ e ∈ E', ∀ kv ∈ BT e.1 e.2, kv.1.head? = some e.1)
    (hBTS : ∀ e ∈ E', (BT e.1 e.2).Pairwise KvLt)
    (hops : ∀ op ∈ ops, op.key ≠ [])
    (hc : ∀ c, entry BT c (E'.lookup c) =
      applyOps (ops.filter (fun op => decide (op.key.head? = some c))) (entry Bs c (E.lookup c))) :
    E'.flatMap (fun e => BT e.1 e.2) = applyOps ops (E.flatMap (fun e => Bs e.1 e.2)) := by
  have hm := flatMap_sorted Bs E hE hBs hBsS
  apply eq_of_blocks (flatMap_sorted BT E' hE' hBT hBTS) (applyOps_sorted hm)
    (flatMap_ne_nil BT E' hBT)
    (applyOps_keys (Q := fun k => k ≠ []) (flatMap_ne_nil Bs E hBs) hops)
  intro c
  rw [blk_flatMap BT c E' hE' hBT, hc c, blk,
    applyOps_filter (fun k => decide (k.head? = some c)) ops _ hm]
  congr 1
  exact (blk_flatMap Bs c E hE hBs).symm

/-- The compare values of the operations' first segments, in the order of
their first occurrence (as `applyGroups` takes them at segment 0). -/
def firstCvs (ops : List Op) : List Nat := (ops.map (segAt 0)).eraseDups

theorem segAt_zero (op : Op) : segAt 0 op = (op.key.head?).getD 0 := by
  simp [segAt, List.head?_eq_getElem?]

theorem mem_firstCvs {ops : List Op} {op : Op} {c : Nat} (hop : op ∈ ops)
    (h : op.key.head? = some c) : c ∈ firstCvs ops := by
  rw [firstCvs, List.mem_eraseDups]
  exact List.mem_map.mpr ⟨op, hop, by simp [segAt_zero, h]⟩

theorem filter_head_nil {ops : List Op} {c : Nat} (hc : c ∉ firstCvs ops) :
    ops.filter (fun op => decide (op.key.head? = some c)) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro op hop h
  exact hc (mem_firstCvs hop (by simpa using h))

/-- **The blocks** (030-21, part 1). Entries E before and E' after, sorted
strictly by compare value; Bs and BT what an entry holds before and after;
each block before in key order, its keys starting with its entry's compare
value; operations of nonempty keys, T their first segments' compare values
(`firstCvs`). If E' agrees with E on every compare value not in T, an entry
of E whose compare value is not in T holds the same after, and for each c in
T the block of c after is the block of c before with the operations of the
keys that start with c applied, then the concatenation of the blocks after is
the concatenation before with the operations applied. -/
theorem applyOps_blocks (Bs BT : Nat → Nat → List (Key × Nat)) (E E' : List (Nat × Nat))
    (ops : List Op) (hE : CvSorted E) (hE' : CvSorted E')
    (hBs : ∀ e ∈ E, ∀ kv ∈ Bs e.1 e.2, kv.1.head? = some e.1)
    (hBsS : ∀ e ∈ E, (Bs e.1 e.2).Pairwise KvLt)
    (hops : ∀ op ∈ ops, op.key ≠ [])
    (hout : ∀ c, c ∉ firstCvs ops → E'.lookup c = E.lookup c)
    (hsame : ∀ e ∈ E, e.1 ∉ firstCvs ops → BT e.1 e.2 = Bs e.1 e.2)
    (hin : ∀ c ∈ firstCvs ops, entry BT c (E'.lookup c) =
      applyOps (ops.filter (fun op => decide (op.key.head? = some c))) (entry Bs c (E.lookup c))) :
    E'.flatMap (fun e => BT e.1 e.2) = applyOps ops (E.flatMap (fun e => Bs e.1 e.2)) := by
  have hall : ∀ c, entry BT c (E'.lookup c) =
      applyOps (ops.filter (fun op => decide (op.key.head? = some c))) (entry Bs c (E.lookup c)) := by
    intro c
    by_cases hc : c ∈ firstCvs ops
    · exact hin c hc
    · rw [filter_head_nil hc, applyOps_nil', hout c hc]
      cases hl : E.lookup c with
      | none => rfl
      | some y => exact hsame (c, y) (mem_of_lookup hl) hc
  have hent : ∀ c, (entry Bs c (E.lookup c)).Pairwise KvLt ∧
      ∀ kv ∈ entry Bs c (E.lookup c), kv.1.head? = some c := by
    intro c
    cases hl : E.lookup c with
    | none => simp [entry]
    | some y => exact ⟨hBsS (c, y) (mem_of_lookup hl), hBs (c, y) (mem_of_lookup hl)⟩
  have hBT : ∀ e ∈ E', (BT e.1 e.2).Pairwise KvLt ∧ ∀ kv ∈ BT e.1 e.2, kv.1.head? = some e.1 := by
    rintro ⟨c, y⟩ he
    have h1 := hall c
    rw [lookup_of_mem hE' he] at h1
    show (BT c y).Pairwise KvLt ∧ ∀ kv ∈ BT c y, kv.1.head? = some c
    rw [show BT c y = entry BT c (some y) from rfl, h1]
    refine ⟨applyOps_sorted (hent c).1,
      applyOps_keys (Q := fun k => k.head? = some c) (hent c).2 ?_⟩
    intro op hop
    simpa using (List.mem_filter.mp hop).2
  exact applyOps_blocks_all Bs BT E E' ops hE hE' hBs hBsS (fun e he => (hBT e he).2)
    (fun e he => (hBT e he).1) hops hall

/-! ## The prefix -/

/-- The operation with its key's first g segments dropped: its key relative
to a tree of segment g. -/
def dropKey (g : Nat) : Op → Op
  | .put k v => .put (k.drop g) v
  | .del k => .del (k.drop g)

/-- The operation with its key's first segment dropped. -/
def tailOp : Op → Op
  | .put k v => .put k.tail v
  | .del k => .del k.tail

theorem keyLt_append (p a b : Key) : keyLt (p ++ a) (p ++ b) = keyLt a b := by
  induction p with
  | nil => rfl
  | cons x p ih => simp [keyLt, ih]

theorem mapPut_prefix (p k : Key) (v : Nat) : ∀ m : List (Key × Nat),
    mapPut (p ++ k) v (m.map (fun kv => (p ++ kv.1, kv.2))) =
      (mapPut k v m).map (fun kv => (p ++ kv.1, kv.2))
  | [] => rfl
  | (k', v') :: r => by
    simp only [List.map_cons, mapPut, keyLt_append, List.append_cancel_left_eq]
    split_ifs <;> simp [mapPut_prefix p k v r]

theorem mapDel_prefix (p k : Key) (m : List (Key × Nat)) :
    mapDel (p ++ k) (m.map (fun kv => (p ++ kv.1, kv.2))) =
      (mapDel k m).map (fun kv => (p ++ kv.1, kv.2)) := by
  simp only [mapDel, List.filter_map]
  congr 1
  apply List.filter_congr
  intro x _
  show (p ++ x.1 != p ++ k) = (x.1 != k)
  rw [Bool.eq_iff_iff, bne_iff_ne, bne_iff_ne, Ne, Ne, List.append_cancel_left_eq]

/-- **The prefix**, for a front p of any length: operations whose keys start
with p act on a map of keys with p in front as the operations with p dropped
act on the map behind p. -/
theorem applyOps_prefix (p : Key) : ∀ (ops : List Op) (m : List (Key × Nat)),
    (∀ op ∈ ops, p <+: op.key) →
    applyOps ops (m.map (fun kv => (p ++ kv.1, kv.2))) =
      (applyOps (ops.map (dropKey p.length)) m).map (fun kv => (p ++ kv.1, kv.2))
  | [], _, _ => rfl
  | op :: ops, m, h => by
    rw [List.map_cons, applyOps_cons', applyOps_cons']
    have hstep : step (m.map (fun kv => (p ++ kv.1, kv.2))) op =
        (step m (dropKey p.length op)).map (fun kv => (p ++ kv.1, kv.2)) := by
      obtain ⟨t, ht⟩ := h op (by simp)
      cases op with
      | put k v =>
        simp only [Op.key] at ht
        subst ht
        simp only [step, dropKey, List.drop_left]
        exact mapPut_prefix p t v m
      | del k =>
        simp only [Op.key] at ht
        subst ht
        simp only [step, dropKey, List.drop_left]
        exact mapDel_prefix p t m
    rw [hstep]
    exact applyOps_prefix p ops _ (fun op hop => h op (List.mem_cons_of_mem _ hop))

theorem tailOp_eq_dropKey (op : Op) : tailOp op = dropKey 1 op := by
  cases op <;> simp [tailOp, dropKey, List.drop_one]

/-- **The prefix** (030-21, part 2): operations whose keys start with c act
on a map of keys with c in front as the operations with their first segment
dropped act on the map behind c. -/
theorem applyOps_cons_prefix (c : Nat) (ops : List Op) (m : List (Key × Nat))
    (h : ∀ op ∈ ops, op.key.head? = some c) :
    applyOps ops (m.map (fun kv => (c :: kv.1, kv.2))) =
      (applyOps (ops.map tailOp) m).map (fun kv => (c :: kv.1, kv.2)) := by
  have := applyOps_prefix [c] ops m (fun op hop => by
    obtain ⟨t, ht⟩ := List.head?_eq_some_iff.mp (h op hop)
    exact ⟨t, ht.symm⟩)
  have e : ops.map tailOp = ops.map (dropKey [c].length) := by
    apply List.map_congr_left
    intro op _
    exact tailOp_eq_dropKey op
  rw [e]
  exact this

/-! ## One key -/

/-- The effect of the last operation on a map of one key, or the map itself
if there is no operation: a put gives its key and value, a delete nothing. -/
def lastEffect (m' : List (Key × Nat)) : Option Op → List (Key × Nat)
  | none => m'
  | some (.put k v) => [(k, v)]
  | some (.del _) => []

theorem step_one_key {k : Key} {m' : List (Key × Nat)} {op : Op} (hop : op.key = k)
    (hm : m' = [] ∨ ∃ v, m' = [(k, v)]) : step m' op = lastEffect m' (some op) := by
  cases op with
  | put k' v =>
    simp only [Op.key] at hop
    subst hop
    rcases hm with rfl | ⟨v0, rfl⟩
    · rfl
    · exact mapPut_cons_self
  | del k' =>
    simp only [Op.key] at hop
    subst hop
    rcases hm with rfl | ⟨v0, rfl⟩
    · rfl
    · simp [step, mapDel, lastEffect]

theorem lastEffect_one_key {k : Key} {m' : List (Key × Nat)} {ops : List Op}
    (hops : ∀ op ∈ ops, op.key = k) (hm : m' = [] ∨ ∃ v, m' = [(k, v)]) :
    lastEffect m' ops.getLast? = [] ∨ ∃ v, lastEffect m' ops.getLast? = [(k, v)] := by
  cases hl : ops.getLast? with
  | none => exact hm
  | some op =>
    have hk := hops op (List.mem_of_getLast? hl)
    cases op with
    | put k' v =>
      simp only [Op.key] at hk
      subst hk
      exact Or.inr ⟨v, rfl⟩
    | del k' => exact Or.inl rfl

/-- **One key** (030-21, part 3): operations all of key k, on a map that is
empty or holds k alone, have the effect of the last one: a put of k and v
gives [(k, v)], a delete of k gives [], no operation leaves the map. -/
theorem applyOps_one_key (k : Key) (ops : List Op) (m' : List (Key × Nat))
    (hops : ∀ op ∈ ops, op.key = k) (hm : m' = [] ∨ ∃ v, m' = [(k, v)]) :
    applyOps ops m' = lastEffect m' ops.getLast? := by
  induction ops using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a ih =>
    have hl : ∀ op ∈ l, op.key = k := fun op hop => hops op (by simp [hop])
    rw [applyOps_concat, ih hl, List.getLast?_concat]
    rw [step_one_key (hops a (by simp)) (lastEffect_one_key hl hm)]
    cases a <;> rfl

/-! ## The noops -/

theorem dropNoops_put (cf : Cfg) (k : Key) (v : Nat) (ops : List Op) :
    dropNoops cf (.put k v :: ops) = .put k v :: dropNoops cf ops := by
  unfold dropNoops
  exact List.filter_cons_of_pos rfl

theorem dropNoops_del_ok (cf : Cfg) (k : Key) (ops : List Op) (hk : keyOk cf k = true) :
    dropNoops cf (.del k :: ops) = .del k :: dropNoops cf ops := by
  unfold dropNoops
  exact List.filter_cons_of_pos hk

theorem dropNoops_del_bad (cf : Cfg) (k : Key) (ops : List Op) (hk : keyOk cf k = false) :
    dropNoops cf (.del k :: ops) = dropNoops cf ops := by
  unfold dropNoops
  exact List.filter_cons_of_neg (by simp [hk])

/-- **The noops** (030-21, part 4): on a map of keys the tree can hold, if
every put is of a key the tree can hold, the deletes that `dropNoops` drops
change nothing. -/
theorem applyOps_dropNoops (cf : Cfg) : ∀ (ops : List Op) (m : List (Key × Nat)),
    (∀ e ∈ m, keyOk cf e.1 = true) → (∀ k v, Op.put k v ∈ ops → keyOk cf k = true) →
    applyOps (dropNoops cf ops) m = applyOps ops m
  | [], _, _, _ => rfl
  | op :: ops, m, hm, hp => by
    have hp' : ∀ k v, Op.put k v ∈ ops → keyOk cf k = true :=
      fun k v h => hp k v (List.mem_cons_of_mem _ h)
    cases op with
    | put k v =>
      have hk := hp k v (by simp)
      rw [dropNoops_put, applyOps_cons', applyOps_cons']
      apply applyOps_dropNoops cf ops _ _ hp'
      intro e he
      rcases mem_mapPut he with rfl | he
      · exact hk
      · exact hm e he
    | del k =>
      cases hk : keyOk cf k with
      | true =>
        rw [dropNoops_del_ok cf k ops hk, applyOps_cons', applyOps_cons']
        exact applyOps_dropNoops cf ops _ (fun e he => hm e (mem_mapDel he)) hp'
      | false =>
        rw [dropNoops_del_bad cf k ops hk, applyOps_cons']
        have : step m (.del k) = m := by
          show m.filter (fun kv => kv.1 != k) = m
          apply List.filter_eq_self.mpr
          intro e he
          have h1 := hm e he
          have : e.1 ≠ k := fun h => by rw [h, hk] at h1; exact Bool.false_ne_true h1
          simpa using this
        rw [this]
        exact applyOps_dropNoops cf ops m hm hp'

/-- The noops, with the premise that `peTx` checks: the operations kept are
of keys the tree can hold (`opsOk`). -/
theorem applyOps_dropNoops_opsOk (cf : Cfg) (ops : List Op) (m : List (Key × Nat))
    (hm : ∀ e ∈ m, keyOk cf e.1 = true) (hok : opsOk cf (dropNoops cf ops) = true) :
    applyOps (dropNoops cf ops) m = applyOps ops m := by
  apply applyOps_dropNoops cf ops m hm
  intro k v hkv
  have hmem : Op.put k v ∈ dropNoops cf ops := List.mem_filter.mpr ⟨hkv, rfl⟩
  exact List.all_eq_true.mp hok _ hmem

/-! ## Relative keys -/

theorem dropKey_key (g : Nat) (op : Op) : (dropKey g op).key = op.key.drop g := by
  cases op <;> rfl

theorem tailOp_key (op : Op) : (tailOp op).key = op.key.tail := by
  cases op <;> rfl

theorem dropKey_zero (op : Op) : dropKey 0 op = op := by
  cases op <;> rfl

theorem dropKey_dropKey (a b : Nat) (op : Op) : dropKey a (dropKey b op) = dropKey (b + a) op := by
  cases op <;> simp [dropKey, List.drop_drop]

/-- **Relative keys** (030-21, part 5): the first segment dropped from a key
relative to segment g gives the key relative to segment g + 1. -/
theorem tailOp_dropKey (g : Nat) (op : Op) : tailOp (dropKey g op) = dropKey (g + 1) op := by
  cases op <;> simp [tailOp, dropKey, List.tail_drop]

theorem segAt_dropKey (g j : Nat) (op : Op) : segAt j (dropKey g op) = segAt (g + j) op := by
  simp [segAt, dropKey_key, List.getElem?_drop]

/-- The compare value at segment 0 of the relative key is the compare value
at segment g. -/
theorem segAt_zero_dropKey (g : Nat) (op : Op) : segAt 0 (dropKey g op) = segAt g op := by
  rw [segAt_dropKey, Nat.add_zero]

theorem head_dropKey {g : Nat} {op : Op} (hg : g < op.key.length) :
    (dropKey g op).key.head? = some (segAt g op) := by
  rw [dropKey_key, List.head?_drop, segAt, List.getElem?_eq_getElem hg]
  rfl

/-- At segment g, an operation's compare value is c if and only if its key
relative to segment g starts with c (for a key of more than g segments). -/
theorem segAt_eq_iff {g : Nat} {op : Op} (c : Nat) (hg : g < op.key.length) :
    segAt g op = c ↔ (dropKey g op).key.head? = some c := by
  rw [head_dropKey hg, Option.some.injEq]

/-- An operation's key ends at segment g if and only if its key relative to
segment g has one segment. -/
theorem endsAt_iff (g : Nat) (op : Op) : endsAt g op = true ↔ (dropKey g op).key.length = 1 := by
  rw [dropKey_key, List.length_drop]
  simp only [endsAt, beq_iff_eq]
  omega

theorem dropKey_key_of_endsAt {g : Nat} {op : Op} (h : endsAt g op = true) :
    (dropKey g op).key = [segAt g op] := by
  have hl : (dropKey g op).key.length = 1 := (endsAt_iff g op).mp h
  have hg : g < op.key.length := by
    rw [dropKey_key, List.length_drop] at hl
    omega
  obtain ⟨t, ht⟩ := List.head?_eq_some_iff.mp (head_dropKey hg)
  rw [ht] at hl ⊢
  simp only [List.length_cons, Nat.add_eq_right, List.length_eq_zero_iff] at hl
  rw [hl]

/-- The compare values at segment g, in the order of their first operation
(`applyGroups`'s list), are those of the relative keys' first segments. -/
theorem firstCvs_dropKey (g : Nat) (ops : List Op) :
    firstCvs (ops.map (dropKey g)) = (ops.map (segAt g)).eraseDups := by
  rw [firstCvs, List.map_map]
  congr 1
  apply List.map_congr_left
  intro op _
  exact segAt_zero_dropKey g op

/-- `applyGroups`'s group of compare value c at segment g, its keys made
relative to segment g, is the relative operations whose keys start with c. -/
theorem filter_segAt_dropKey (g c : Nat) (ops : List Op) (hg : ∀ op ∈ ops, g < op.key.length) :
    (ops.filter (fun op => segAt g op == c)).map (dropKey g) =
      (ops.map (dropKey g)).filter (fun op => decide (op.key.head? = some c)) := by
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro op hop
  show (segAt g op == c) = decide ((dropKey g op).key.head? = some c)
  rw [head_dropKey (hg op hop), Bool.eq_iff_iff]
  simp

/-! ## Well formed keys -/

/-- In a well formed key, a segment is long if and only if it is not the
last. -/
theorem keyWf_isLong : ∀ (k : Key), keyWf k = true → ∀ (i : Nat) (hi : i < k.length),
    (isLong k[i] = true ↔ i + 1 < k.length)
  | [], h, _, _ => by simp [keyWf] at h
  | [c], h, i, hi => by
    simp only [keyWf, Bool.not_eq_eq_eq_not, Bool.not_true] at h
    simp only [List.length_singleton, Nat.lt_one_iff] at hi
    subst hi
    simp [h]
  | c :: d :: rest, h, i, hi => by
    simp only [keyWf, Bool.and_eq_true] at h
    cases i with
    | zero => simp [h.1]
    | succ i =>
      have := keyWf_isLong (d :: rest) h.2 i (by simpa using hi)
      simpa using this

/-- The segments of a well formed key from g on form a well formed key. -/
theorem keyWf_drop : ∀ (k : Key) (g : Nat), keyWf k = true → g < k.length →
    keyWf (k.drop g) = true
  | k, 0, h, _ => by simpa using h
  | [], _ + 1, _, hg => by simp at hg
  | [_], _ + 1, _, hg => by simp at hg
  | c :: d :: rest, g + 1, h, hg => by
    simp only [keyWf, Bool.and_eq_true] at h
    simpa using keyWf_drop (d :: rest) g h.2 (by simpa using hg)

/-- A well formed key ends at segment g if and only if its segment g is
short. -/
theorem endsAt_of_keyWf {g : Nat} {op : Op} (hw : keyWf op.key = true) (hg : g < op.key.length) :
    endsAt g op = !isLong (segAt g op) := by
  have h := keyWf_isLong op.key hw g hg
  have hs : segAt g op = op.key[g] := by simp [segAt, List.getElem?_eq_getElem hg]
  rw [hs]
  cases hl : isLong op.key[g] with
  | true =>
    have := h.mp hl
    simp only [endsAt, Bool.not_true, beq_eq_false_iff_ne, ne_eq]
    omega
  | false =>
    have : ¬ g + 1 < op.key.length := fun h' => by rw [h.mpr h'] at hl; exact Bool.noConfusion hl
    simp only [endsAt, Bool.not_false, beq_iff_eq]
    omega

theorem mem_grp {g c : Nat} {ops : List Op} {op : Op}
    (h : op ∈ ops.filter (fun op => segAt g op == c)) : op ∈ ops ∧ segAt g op = c := by
  simpa using List.mem_filter.mp h

/-- A group of a short compare value: every key ends at segment g, no
operation goes to a next segment's tree. -/
theorem grp_short {g c : Nat} {ops : List Op} (hw : ∀ op ∈ ops, keyWf op.key = true)
    (hg : ∀ op ∈ ops, g < op.key.length) (hc : isLong c = false) :
    (ops.filter (fun op => segAt g op == c)).filter (endsAt g) =
        ops.filter (fun op => segAt g op == c) ∧
      (ops.filter (fun op => segAt g op == c)).filter (fun op => !endsAt g op) = [] := by
  have he : ∀ op ∈ ops.filter (fun op => segAt g op == c), endsAt g op = true := by
    intro op hop
    obtain ⟨h1, h2⟩ := mem_grp hop
    rw [endsAt_of_keyWf (hw op h1) (hg op h1), h2, hc]
    rfl
  refine ⟨List.filter_eq_self.mpr he, List.filter_eq_nil_iff.mpr ?_⟩
  intro op hop
  simp [he op hop]

/-- A group of a long compare value: no key ends at segment g, every
operation goes to the next segment's tree. -/
theorem grp_long {g c : Nat} {ops : List Op} (hw : ∀ op ∈ ops, keyWf op.key = true)
    (hg : ∀ op ∈ ops, g < op.key.length) (hc : isLong c = true) :
    (ops.filter (fun op => segAt g op == c)).filter (endsAt g) = [] ∧
      (ops.filter (fun op => segAt g op == c)).filter (fun op => !endsAt g op) =
        ops.filter (fun op => segAt g op == c) := by
  have he : ∀ op ∈ ops.filter (fun op => segAt g op == c), endsAt g op = false := by
    intro op hop
    obtain ⟨h1, h2⟩ := mem_grp hop
    rw [endsAt_of_keyWf (hw op h1) (hg op h1), h2, hc]
    rfl
  refine ⟨List.filter_eq_nil_iff.mpr ?_, List.filter_eq_self.mpr ?_⟩
  · intro op hop
    simp [he op hop]
  · intro op hop
    simp [he op hop]

/-- The block of a short compare value c at segment g (parts 3 and 5): the
group's keys relative to segment g are all [c], and on a block that is empty
or holds [c] alone the group has the effect of its last operation. -/
theorem applyOps_short_block {g c : Nat} {ops : List Op} (hw : ∀ op ∈ ops, keyWf op.key = true)
    (hg : ∀ op ∈ ops, g < op.key.length) (hc : isLong c = false) (m' : List (Key × Nat))
    (hm : m' = [] ∨ ∃ v, m' = [([c], v)]) :
    applyOps ((ops.filter (fun op => segAt g op == c)).map (dropKey g)) m' =
      lastEffect m' ((ops.filter (fun op => segAt g op == c)).map (dropKey g)).getLast? := by
  apply applyOps_one_key [c] _ m' _ hm
  intro op hop
  obtain ⟨op0, hop0, rfl⟩ := List.mem_map.mp hop
  have he := (grp_short hw hg hc).1
  have h1 : endsAt g op0 = true := by
    rw [← he] at hop0
    exact (List.mem_filter.mp hop0).2
  rw [dropKey_key_of_endsAt h1, (mem_grp hop0).2]

/-- The block of a compare value c at segment g with c in front (parts 2 and
5): the group's keys relative to segment g act on the keys of the next
segment's tree with c in front as the keys relative to segment g + 1 act on
those keys. -/
theorem applyOps_cons_block {g c : Nat} {ops : List Op} (hg : ∀ op ∈ ops, g < op.key.length)
    (m : List (Key × Nat)) :
    applyOps ((ops.filter (fun op => segAt g op == c)).map (dropKey g))
        (m.map (fun kv => (c :: kv.1, kv.2))) =
      (applyOps ((ops.filter (fun op => segAt g op == c)).map (dropKey (g + 1))) m).map
        (fun kv => (c :: kv.1, kv.2)) := by
  rw [applyOps_cons_prefix c _ m, List.map_map]
  · congr 2
    apply List.map_congr_left
    intro op _
    exact tailOp_dropKey g op
  · intro op hop
    obtain ⟨op0, hop0, rfl⟩ := List.mem_map.mp hop
    obtain ⟨h1, h2⟩ := mem_grp hop0
    rw [head_dropKey (hg op0 h1), h2]

/-- **The blocks at segment g** (parts 1, 2 and 5): operations whose keys
share a front p of g segments and have more than g segments, T their compare
values at segment g in the order of their first operation (`applyGroups`'s
list). Entries E before and E' after, Bs and BT as in `applyOps_blocks`, the
keys of a block relative to segment g. If E' agrees with E outside T, an
entry of E outside T holds the same after, and for each c in T the block of c
after is the block of c before with c's group (`applyGroups`'s `grp`), its
keys relative to segment g, applied, then the concatenation of the blocks
after, with p in front, is the concatenation before, with p in front, with
the operations applied. -/
theorem applyOps_segment (p : Key) (Bs BT : Nat → Nat → List (Key × Nat))
    (E E' : List (Nat × Nat)) (ops : List Op) (hE : CvSorted E) (hE' : CvSorted E')
    (hBs : ∀ e ∈ E, ∀ kv ∈ Bs e.1 e.2, kv.1.head? = some e.1)
    (hBsS : ∀ e ∈ E, (Bs e.1 e.2).Pairwise KvLt)
    (hp : ∀ op ∈ ops, p <+: op.key) (hg : ∀ op ∈ ops, p.length < op.key.length)
    (hout : ∀ c, c ∉ (ops.map (segAt p.length)).eraseDups → E'.lookup c = E.lookup c)
    (hsame : ∀ e ∈ E, e.1 ∉ (ops.map (segAt p.length)).eraseDups → BT e.1 e.2 = Bs e.1 e.2)
    (hin : ∀ c ∈ (ops.map (segAt p.length)).eraseDups, entry BT c (E'.lookup c) =
      applyOps ((ops.filter (fun op => segAt p.length op == c)).map (dropKey p.length))
        (entry Bs c (E.lookup c))) :
    (E'.flatMap (fun e => BT e.1 e.2)).map (fun kv => (p ++ kv.1, kv.2)) =
      applyOps ops ((E.flatMap (fun e => Bs e.1 e.2)).map (fun kv => (p ++ kv.1, kv.2))) := by
  rw [applyOps_prefix p ops _ hp]
  congr 1
  apply applyOps_blocks Bs BT E E' (ops.map (dropKey p.length)) hE hE' hBs hBsS
  · intro op hop
    obtain ⟨op0, hop0, rfl⟩ := List.mem_map.mp hop
    rw [dropKey_key]
    have := hg op0 hop0
    intro h
    have := congrArg List.length h
    rw [List.length_drop] at this
    simp at this
    omega
  · rw [firstCvs_dropKey]
    exact hout
  · rw [firstCvs_dropKey]
    exact hsame
  · rw [firstCvs_dropKey]
    intro c hc
    rw [hin c hc, filter_segAt_dropKey _ c ops hg]

/-! ## A segment leaf's entries as blocks -/

/-- A segment leaf's entry (c, y) holds keys that start with c
(`klongList`, Statement.lean, section 3): it meets `applyOps_blocks`'s
premise on Bs. -/
theorem klongList_head (s : Tree) (sub : NodeId → List (Key × Nat)) (c : Nat) (y : NodeId) :
    ∀ kv ∈ klongList s true sub c y, kv.1.head? = some c := by
  intro kv hkv
  unfold klongList at hkv
  by_cases hl : isLong c = true
  · simp only [hl, ite_true, List.mem_map] at hkv
    obtain ⟨kv0, _, rfl⟩ := hkv
    rfl
  · simp only [hl, ite_true, Bool.false_eq_true, ite_false] at hkv
    split at hkv
    · simp only [List.mem_singleton] at hkv
      subst hkv
      rfl
    · simp at hkv

/-- A segment leaf's entry holds its keys in key order if the next segment's
tree does. -/
theorem klongList_sorted (s : Tree) (sub : NodeId → List (Key × Nat)) (c : Nat) (y : NodeId)
    (h : (sub y).Pairwise KvLt) : (klongList s true sub c y).Pairwise KvLt := by
  unfold klongList
  by_cases hl : isLong c = true
  · simp only [hl, ite_true]
    rw [List.pairwise_map]
    exact h.imp (fun hab => List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, hab⟩))
  · simp only [hl, Bool.false_eq_true, ite_false, ite_true]
    split
    · exact List.pairwise_singleton _ _
    · exact List.Pairwise.nil

/-- A short entry of a segment leaf holds [c] alone or nothing: part 3's map. -/
theorem klongList_short (s : Tree) (sub : NodeId → List (Key × Nat)) {c : Nat} (y : NodeId)
    (hc : isLong c = false) :
    klongList s true sub c y = [] ∨ ∃ v, klongList s true sub c y = [([c], v)] := by
  unfold klongList
  simp only [hc, Bool.false_eq_true, ite_false, ite_true]
  split
  · exact Or.inr ⟨_, rfl⟩
  · exact Or.inl rfl

/-- A long entry of a segment leaf holds the next segment's tree with c in
front: part 2's map. -/
theorem klongList_long (s : Tree) (sub : NodeId → List (Key × Nat)) {c : Nat} (y : NodeId)
    (hc : isLong c = true) :
    klongList s true sub c y = (sub y).map (fun kv => (c :: kv.1, kv.2)) := by
  simp [klongList, hc]

end PeProof.Keys
