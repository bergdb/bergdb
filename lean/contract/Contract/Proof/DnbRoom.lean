/-
bergdb 030-29: the premises of PE's acceptance (`FuelOk`, `Room`:
Contract/PeAcceptStatement.lean) hold for Java's parameters on every tree a
stream can hold, from the fill rules PE keeps (030-28, section 5, on paper).

The count. A key node at height e of its segment tree, shaped as PE's trees
(`Shaped`: each child of an inner node one height down) and filled
(`Filled`: an inner root has two live klongs at least, every other key node m
at least, m >= 2), has at least 2^e nodes in its walk (`R`), and at least
m^e if it is not a segment tree's root; so 2 m^e <= m |R| at every key node
(`count_R`). The walk of a node reached from the space root is a sublist of
the space root's walk, TREE's list `reach s` (`walk_count`), so each of these
bounds the number of nodes N of `reach s` (`reach_count`). A value has height
0. Heights are at most H (`htIn_le`).

* `room_of_bounds`: from a state PE keeps (`Inv`) whose space root is
  `Filled`, with m, h and cap at least 2, `Room` holds for p operations if
  N + p < 2^(H - e) for every e <= H that the count allows.
* `room_of_filled`: the same, given (N + p) N < 2^H.
* Java's parameters (`Cfg.java b 8192 H` at node sizes b = 8, 14, 30, 62):
  `cfgOk_java` (`Cfg.Ok`, and h, cap, m at least 2); `fuelOk_java`
  (`FuelOk` for p <= 2^20 at H <= 126: (G + 1)(H + 1)(M + p + 2 H + 6) at
  most 2^40; at H = 128 it is not, for p = 2^20); `room_java` (`Room` on every
  tree of fewer than 2^63 nodes, p <= 2^20, H >= 126); `accept_java` (both at
  H = 126); `pe_accepts_java`: so PE accepts every transaction of at most
  2^20 operations whose puts' keys the tree can hold, on every such tree.
* The count with m at H = 100: `room_java_100` (fewer than 2^63 nodes at
  node sizes 30 and 62, m = 8 and 16), `room_java_100_b14` (fewer than 2^61
  nodes at node size 14, m = 3), `room_java_100_b8` (fewer than 2^50 nodes at
  node size 8, m = 2). At node size 8, H = 100 does not leave room on every
  tree of fewer than 2^63 nodes: a segment tree of height 61 whose every
  node has two live klongs has 2^63 - 1 nodes with its values, and `Room`
  asks N + p < 2^39 at its root. `Room` is a premise that suffices, not
  PE's limit (030-21, part 3).

H is the model's free parameter, which Java does not have (030-28, section 5).
-/
import Contract.Proof.DnbFill
import Contract.Proof.PeAccept

namespace Contract.PE

variable {cf : Cfg} {s : Tree}

/-! ## Lists -/

/-- A list of k-long lists or longer, flattened. -/
theorem mul_le_flatMap_length {α β : Type} {f : α → List β} {k : Nat} :
    ∀ (l : List α), (∀ a ∈ l, k ≤ (f a).length) → l.length * k ≤ (l.flatMap f).length
  | [], _ => by simp
  | a :: l, h => by
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    have h1 := h a List.mem_cons_self
    have h2 := mul_le_flatMap_length l (fun b hb => h b (List.mem_cons_of_mem _ hb))
    omega

/-! ## Heights and children -/

/-- A node shaped at height h has the height h by its level. -/
theorem htIn_of_shaped {g h : Nat} {y : NodeId} (hsh : Shaped cf s g h y) : htIn cf s y = h := by
  obtain ⟨n, hobj, hlev, _, _, hH⟩ := shaped_obj hsh
  simp [htIn, hobj, hlev, htOf_lev cf hH]

/-- Every height is at most H. -/
theorem htIn_le (y : NodeId) : htIn cf s y ≤ cf.H := by
  unfold htIn
  split
  · exact Nat.le_of_lt_succ (Nat.mod_lt _ (Nat.succ_pos _))
  · exact Nat.zero_le _

/-- A child of a shaped inner node is shaped at its height. -/
theorem shaped_kid_inner {g e : Nat} {x : NodeId} {n : KNode} (hsh : Shaped cf s g e x)
    (hobj : s.obj x = some (.key n)) (hl : n.leaf = false) {c : Nat} {z : NodeId}
    (hcz : (c, z) ∈ live n.ks) : Shaped cf s g (htIn cf s z) z := by
  cases hsh with
  | leaf hobj' hleaf _ _ _ =>
    rw [hobj] at hobj'
    obtain rfl : n = _ := by injection hobj' with h1; injection h1
    rw [hl] at hleaf; cases hleaf
  | inner hobj' _ _ _ _ _ hk =>
    rw [hobj] at hobj'
    obtain rfl : n = _ := by injection hobj' with h1; injection h1
    have hz := hk c z hcz
    rwa [htIn_of_shaped hz]

/-- A long entry of a shaped segment leaf names a node shaped at its height in
the next segment. -/
theorem shaped_kid_leaf {g e : Nat} {x : NodeId} {n : KNode} (hsh : Shaped cf s g e x)
    (hobj : s.obj x = some (.key n)) (hl : n.leaf = true) {c : Nat} {z : NodeId}
    (hcz : (c, z) ∈ live n.ks) (hlg : isLong c = true) : Shaped cf s (g + 1) (htIn cf s z) z := by
  cases hsh with
  | leaf hobj' _ _ _ hk =>
    rw [hobj] at hobj'
    obtain rfl : n = _ := by injection hobj' with h1; injection h1
    exact hk c z hcz hlg
  | inner hobj' hleaf _ _ _ _ _ =>
    rw [hobj] at hobj'
    obtain rfl : n = _ := by injection hobj' with h1; injection h1
    rw [hl] at hleaf; cases hleaf

/-- A short entry of a sound segment leaf names a value. -/
theorem good_val {x : NodeId} {lo : Nat} {hi : Option Nat} (hg : Good s x lo hi) {n : KNode}
    (hobj : s.obj x = some (.key n)) (hl : n.leaf = true) {c : Nat} {z : NodeId}
    (hcz : (c, z) ∈ live n.ks) (hlg : isLong c = false) : ∃ v, s.obj z = some (.val v) := by
  cases hg with
  | mk _ _ _ n' hobj' _ _ _ hval _ _ _ =>
    rw [hobj] at hobj'
    obtain rfl : n = n' := by injection hobj' with h1; injection h1
    exact hval hl c z hcz hlg

/-! ## The count -/

/-- **The nodes below a filled node**: a key node shaped at height e and
filled has at least 2^e nodes in its walk, at least m^e if it is not a
segment tree's root, and so 2 m^e <= m |R| either way. -/
theorem count_R (hm : 2 ≤ cf.m) : ∀ (e : Nat) {g : Nat} {b : Bool} {y : NodeId},
    Shaped cf s g e y → Filled cf s b y →
      2 ^ e ≤ (R s y).length ∧ (b = false → cf.m ^ e ≤ (R s y).length) ∧
        2 * cf.m ^ e ≤ cf.m * (R s y).length
  | 0, g, b, y, _, _ => by
    have h1 := R_length_pos s y
    refine ⟨by simpa using h1, fun _ => by simpa using h1, ?_⟩
    simpa using Nat.mul_le_mul hm h1
  | e + 1, g, b, y, hsh, hF => by
    obtain ⟨n, hobj, -, hleaf, -, -⟩ := shaped_obj hsh
    have hl : n.leaf = false := by simpa using hleaf
    have hkids : ∀ c z, (c, z) ∈ live n.ks → Shaped cf s g e z := by
      cases hsh with
      | inner hobj' _ _ _ _ _ hk =>
        rw [hobj] at hobj'
        obtain rfl : n = _ := by injection hobj' with h1; injection h1
        exact hk
    cases hF with
    | other hno => exact absurd hobj (hno n)
    | key hobj' hroot hfill _ hinner =>
      rw [hobj] at hobj'
      obtain rfl : n = _ := by injection hobj' with h1; injection h1
      have ih : ∀ cz ∈ live n.ks, 2 ^ e ≤ (R s cz.2).length ∧ cf.m ^ e ≤ (R s cz.2).length :=
        fun cz hcz =>
          have h := count_R hm e (hkids cz.1 cz.2 hcz) (hinner cz.1 cz.2 hcz hl)
          ⟨h.1, h.2.1 rfl⟩
      have h2 : 2 ≤ (live n.ks).length := by
        cases b with
        | false => exact le_trans hm (hfill hm rfl)
        | true => exact hroot hl rfl
      have A := mul_le_flatMap_length (f := fun cy : Nat × NodeId => R s cy.2) (k := 2 ^ e) _
        (fun a ha => (ih a ha).1)
      have B := mul_le_flatMap_length (f := fun cy : Nat × NodeId => R s cy.2) (k := cf.m ^ e) _
        (fun a ha => (ih a ha).2)
      have hA : 2 * 2 ^ e ≤ (live n.ks).length * 2 ^ e := Nat.mul_le_mul_right _ h2
      have hB : 2 * cf.m ^ e ≤ (live n.ks).length * cf.m ^ e := Nat.mul_le_mul_right _ h2
      rw [R_shaped hsh hobj, List.length_cons]
      refine ⟨?_, ?_, ?_⟩
      · rw [Nat.pow_succ]; omega
      · intro hb
        have hC : cf.m * cf.m ^ e ≤ (live n.ks).length * cf.m ^ e :=
          Nat.mul_le_mul_right _ (hfill hm hb)
        rw [Nat.pow_succ]; rw [Nat.mul_comm] at hC; omega
      · have hD : cf.m * (2 * cf.m ^ e) ≤
            cf.m * ((live n.ks).flatMap (fun cy => R s cy.2)).length :=
          Nat.mul_le_mul_left _ (le_trans hB B)
        rw [Nat.pow_succ, Nat.mul_add, Nat.mul_one]
        have : 2 * (cf.m ^ e * cf.m) = cf.m * (2 * cf.m ^ e) := by ring
        omega

/-- **The count through the walk**: every node y that the walk from a sound,
shaped and filled key node x reaches has its walk as a sublist of x's, and
the count of `count_R` (values: height 0). -/
theorem walk_count (hm : 2 ≤ cf.m) {b : Bool} {x : NodeId} (hF : Filled cf s b x) :
    ∀ (g lo : Nat) (hi : Option Nat), Good s x lo hi → Shaped cf s g (htIn cf s x) x →
      ∀ y ∈ R s x, (R s y).Sublist (R s x) ∧ 2 ^ htIn cf s y ≤ (R s y).length ∧
        2 * cf.m ^ htIn cf s y ≤ cf.m * (R s y).length := by
  induction hF with
  | other hno =>
    intro g lo hi hg _
    obtain ⟨n, hn⟩ := good_obj hg
    exact absurd hn (hno n)
  | @key isRoot x n hobj hroot hfill hlong hinner ihlong ihinner =>
    intro g lo hi hg hsh y hy
    have hy' := hy
    rw [R_good hg hobj] at hy'
    rcases List.mem_cons.mp hy' with rfl | hy'
    · have hc := count_R hm _ hsh (Filled.key hobj hroot hfill hlong hinner)
      exact ⟨List.Sublist.refl _, hc.1, hc.2.2⟩
    · obtain ⟨⟨c, z⟩, hcz, hyz⟩ := List.mem_flatMap.mp hy'
      have hsub : (R s z).Sublist (R s x) := R_sub_kid hg hobj hcz
      rcases good_kids hg hobj c z hcz with ⟨m, hmz, _, lo', hi', hgz⟩ | ⟨v, hv⟩
      · cases hl : n.leaf with
        | false =>
          obtain ⟨h1, h2⟩ := ihinner c z hcz hl g lo' hi' hgz (shaped_kid_inner hsh hobj hl hcz) y hyz
          exact ⟨h1.trans hsub, h2⟩
        | true =>
          cases hlg : isLong c with
          | false =>
            obtain ⟨v, hv⟩ := good_val hg hobj hl hcz hlg
            rw [hv] at hmz; cases hmz
          | true =>
            obtain ⟨h1, h2⟩ := ihlong c z hcz hl hlg (g + 1) lo' hi' hgz
              (shaped_kid_leaf hsh hobj hl hcz hlg) y hyz
            exact ⟨h1.trans hsub, h2⟩
      · have hRz : R s z = [z] := by simp [R, Tree.fuel, hv, reachAt]
        rw [hRz, List.mem_singleton] at hyz
        subst hyz
        have h0 : htIn cf s y = 0 := by simp [htIn, hv]
        rw [hRz] at hsub ⊢
        exact ⟨hsub, by simp [h0], by simp [h0]; omega⟩

/-- **The count in the tree**: from a state PE keeps whose space root is
filled, with m at least 2, every node y of TREE's list `reach s` (N nodes) at
height e = `htIn cf s y` has 2^e <= N and 2 m^e <= m N. -/
theorem reach_count {t : Time} {tp : Top} {next : NodeId} (hI : Inv cf t s tp next)
    (hF : ∀ r, s.root = some r → Filled cf s true r) (hm : 2 ≤ cf.m) :
    ∀ y ∈ reach s, 2 ^ htIn cf s y ≤ (reach s).length ∧
      2 * cf.m ^ htIn cf s y ≤ cf.m * (reach s).length := by
  obtain ⟨r, hr, hsh⟩ := hI.shaped
  have hg := good_of_invOk hr hI.inv
  intro y hy
  rw [reach_eq_R hr] at hy ⊢
  obtain ⟨hsub, h1, h2⟩ := walk_count hm (hF r hr) 0 0 none hg hsh y hy
  have hle := hsub.length_le
  exact ⟨le_trans h1 hle, le_trans h2 (Nat.mul_le_mul_left _ hle)⟩

/-! ## Room -/

/-- **Room from the count**: from a state PE keeps whose space root is filled,
with m, h and cap at least 2, H leaves room for p operations if N + p <
2^(H - e) for every height e <= H that the count allows (2^e <= N and
2 m^e <= m N), N the nodes of TREE's list. -/
theorem room_of_bounds {t : Time} {tp : Top} {next : NodeId} {p : Nat} (hI : Inv cf t s tp next)
    (hF : ∀ r, s.root = some r → Filled cf s true r) (hm : 2 ≤ cf.m) (hh : 2 ≤ cf.h)
    (hcap : 2 ≤ cf.cap)
    (hb : ∀ e, e ≤ cf.H → 2 ^ e ≤ (reach s).length → 2 * cf.m ^ e ≤ cf.m * (reach s).length →
      (reach s).length + p < 2 ^ (cf.H - e)) : Room cf s p := by
  refine ⟨hh, hcap, fun y hy => ?_⟩
  obtain ⟨h1, h2⟩ := reach_count hI hF hm y hy
  exact hb _ (htIn_le y) h1 h2

/-- **Room** (030-29, A2 (a)): from a state PE keeps whose space root is
filled, with m, h and cap at least 2, H leaves room for p operations on a
tree of N nodes if (N + p) N < 2^H. -/
theorem room_of_filled {t : Time} {tp : Top} {next : NodeId} {p : Nat} (hI : Inv cf t s tp next)
    (hF : ∀ r, s.root = some r → Filled cf s true r) (hm : 2 ≤ cf.m) (hh : 2 ≤ cf.h)
    (hcap : 2 ≤ cf.cap) (hN : ((reach s).length + p) * (reach s).length < 2 ^ cf.H) :
    Room cf s p := by
  refine room_of_bounds hI hF hm hh hcap (fun e he h1 _ => ?_)
  have h3 : ((reach s).length + p) * 2 ^ e < 2 ^ (cf.H - e) * 2 ^ e :=
    calc ((reach s).length + p) * 2 ^ e ≤ ((reach s).length + p) * (reach s).length :=
          Nat.mul_le_mul_left _ h1
      _ < 2 ^ cf.H := hN
      _ = 2 ^ (cf.H - e) * 2 ^ e := by rw [← Nat.pow_add, Nat.sub_add_cancel he]
  exact Nat.lt_of_mul_lt_mul_right h3

/-! ## Java's parameters -/

/-- Java's parameters at the node sizes 8, 14, 30 and 62 meet `Cfg.Ok`, and
h, cap and m are at least 2 (m = 2, 3, 8, 16). -/
theorem cfgOk_java {b G H : Nat} (hb : b ∈ [8, 14, 30, 62]) :
    Cfg.Ok (Cfg.java b G H) ∧ 2 ≤ (Cfg.java b G H).h ∧ 2 ≤ (Cfg.java b G H).cap ∧
      2 ≤ (Cfg.java b G H).m := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;>
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;> simp only [Cfg.java] <;> decide

/-- **The fuel** at Java's parameters: up to node size 62, with G = 8,192 and
H at most 126, PE's fuel suffices for transactions of up to 2^20
operations. -/
theorem fuelOk_java {b H p : Nat} (hb : b ≤ 62) (hH : H ≤ 126) (hp : p ≤ 2 ^ 20) :
    FuelOk (Cfg.java b 8192 H) p := by
  unfold FuelOk
  simp only [Cfg.java, fuel]
  calc (8192 + 1) * (H + 1) * (b + p + 2 * H + 6) ≤ (8192 + 1) * 127 * (2 ^ 20 + 320) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    _ ≤ 2 ^ 40 := by norm_num

private theorem e_lt {m e j N k : Nat} (hm : 2 ≤ m) (h2 : 2 * m ^ e ≤ m * N) (hN : N < 2 ^ k)
    (hj : m * 2 ^ k ≤ 2 * m ^ j) : e < j := by
  by_contra hc
  have h3 : m ^ j ≤ m ^ e := Nat.pow_le_pow_right (by omega) (by omega)
  have h4 : m * N < m * 2 ^ k := Nat.mul_lt_mul_of_pos_left hN (by omega)
  omega

/-- **Room** at Java's parameters: at node sizes 8, 14, 30 and 62, with G =
8,192 and H at least 126, from a state PE keeps whose space root is filled,
H leaves room for p <= 2^20 operations on every tree of fewer than 2^63
nodes (a stream's nodes each have their own position below 2^63). -/
theorem room_java {b H p : Nat} {t : Time} {s : Tree} {tp : Top} {next : NodeId}
    (hb : b ∈ [8, 14, 30, 62]) (hH : 126 ≤ H) (hI : Inv (Cfg.java b 8192 H) t s tp next)
    (hF : ∀ r, s.root = some r → Filled (Cfg.java b 8192 H) s true r)
    (hN : (reach s).length < 2 ^ 63) (hp : p ≤ 2 ^ 20) : Room (Cfg.java b 8192 H) s p := by
  obtain ⟨-, hh, hcap, hm⟩ := cfgOk_java (G := 8192) (H := H) hb
  refine room_of_bounds hI hF hm hh hcap (fun e _ h1 _ => ?_)
  have he : e < 63 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp (lt_of_le_of_lt h1 hN)
  have h64 : 2 ^ 64 ≤ 2 ^ ((Cfg.java b 8192 H).H - e) :=
    Nat.pow_le_pow_right (by norm_num) (by simp only [Cfg.java]; omega)
  have k : (2 : Nat) ^ 63 + 2 ^ 20 ≤ 2 ^ 64 := by norm_num
  omega

/-- **PE's acceptance premises at Java's parameters** (030-29, A2 (b)): at
node sizes 8, 14, 30 and 62, with G = 8,192 and H = 126, from a state PE
keeps whose space root is filled, a transaction of at most 2^20 operations
on a tree of fewer than 2^63 nodes meets `FuelOk` and `Room`. -/
theorem accept_java {b p : Nat} {t : Time} {s : Tree} {tp : Top} {next : NodeId}
    (hb : b ∈ [8, 14, 30, 62]) (hI : Inv (Cfg.java b 8192 126) t s tp next)
    (hF : ∀ r, s.root = some r → Filled (Cfg.java b 8192 126) s true r)
    (hN : (reach s).length < 2 ^ 63) (hp : p ≤ 2 ^ 20) :
    FuelOk (Cfg.java b 8192 126) p ∧ Room (Cfg.java b 8192 126) s p := by
  have hb62 : b ≤ 62 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    omega
  exact ⟨fuelOk_java hb62 (le_refl _) hp, room_java hb (le_refl _) hI hF hN hp⟩

/-- The same from the trace checker's walk: a tree in which `shapeFaults`
finds no fault has its space root filled (`filled_of_shapeFaults`). -/
theorem accept_java_of_shapeFaults {b p : Nat} {t : Time} {s : Tree} {tp : Top} {next : NodeId}
    (hb : b ∈ [8, 14, 30, 62]) (hI : Inv (Cfg.java b 8192 126) t s tp next)
    (hsf : shapeFaults ⟨126, DNB.minFill b, DNB.theta b⟩ s = [])
    (hN : (reach s).length < 2 ^ 63) (hp : p ≤ 2 ^ 20) :
    FuelOk (Cfg.java b 8192 126) p ∧ Room (Cfg.java b 8192 126) s p :=
  accept_java hb hI (fun _ hr => filled_of_shapeFaults hsf hr) hN hp

/-! ## H = 100, by the count with m -/

/-- **Room at H = 100 for node sizes 30 and 62** (030-29, A2 (c)): with m = 8
or 16, a filled segment tree's root at height e holds at least 2 m^(e - 1)
nodes, so on a tree of fewer than 2^63 nodes e is at most 21 (node size 30)
or 16 (node size 62), and H = 100 leaves room for p <= 2^20 operations. -/
theorem room_java_100 {b p : Nat} {t : Time} {s : Tree} {tp : Top} {next : NodeId}
    (hb : b ∈ [30, 62]) (hI : Inv (Cfg.java b 8192 100) t s tp next)
    (hF : ∀ r, s.root = some r → Filled (Cfg.java b 8192 100) s true r)
    (hN : (reach s).length < 2 ^ 63) (hp : p ≤ 2 ^ 20) : Room (Cfg.java b 8192 100) s p := by
  have hb' : b ∈ [8, 14, 30, 62] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb ⊢; omega
  obtain ⟨-, hh, hcap, hm⟩ := cfgOk_java (G := 8192) (H := 100) hb'
  refine room_of_bounds hI hF hm hh hcap (fun e _ _ h2 => ?_)
  have he : e ≤ 21 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · have := e_lt (j := 22) hm h2 hN (by decide); omega
    · have := e_lt (j := 17) hm h2 hN (by decide); omega
  have h79 : 2 ^ 79 ≤ 2 ^ ((Cfg.java b 8192 100).H - e) :=
    Nat.pow_le_pow_right (by norm_num) (by simp only [Cfg.java]; omega)
  have k : (2 : Nat) ^ 63 + 2 ^ 20 ≤ 2 ^ 79 := by norm_num
  omega

/-- Room at H = 100 for node size 14 (m = 3): on a tree of fewer than 2^61
nodes (e at most 38), for p <= 2^20 operations. -/
theorem room_java_100_b14 {p : Nat} {t : Time} {s : Tree} {tp : Top} {next : NodeId}
    (hI : Inv (Cfg.java 14 8192 100) t s tp next)
    (hF : ∀ r, s.root = some r → Filled (Cfg.java 14 8192 100) s true r)
    (hN : (reach s).length < 2 ^ 61) (hp : p ≤ 2 ^ 20) : Room (Cfg.java 14 8192 100) s p := by
  obtain ⟨-, hh, hcap, hm⟩ := cfgOk_java (b := 14) (G := 8192) (H := 100) (by decide)
  refine room_of_bounds hI hF hm hh hcap (fun e _ _ h2 => ?_)
  have he : e < 39 := e_lt hm h2 hN (by decide)
  have h62 : 2 ^ 62 ≤ 2 ^ ((Cfg.java 14 8192 100).H - e) :=
    Nat.pow_le_pow_right (by norm_num) (by simp only [Cfg.java]; omega)
  have k : (2 : Nat) ^ 61 + 2 ^ 20 ≤ 2 ^ 62 := by norm_num
  omega

/-- Room at H = 100 for node size 8 (m = 2): on a tree of fewer than 2^50
nodes (e at most 49), for p <= 2^20 operations. -/
theorem room_java_100_b8 {p : Nat} {t : Time} {s : Tree} {tp : Top} {next : NodeId}
    (hI : Inv (Cfg.java 8 8192 100) t s tp next)
    (hF : ∀ r, s.root = some r → Filled (Cfg.java 8 8192 100) s true r)
    (hN : (reach s).length < 2 ^ 50) (hp : p ≤ 2 ^ 20) : Room (Cfg.java 8 8192 100) s p := by
  obtain ⟨-, hh, hcap, hm⟩ := cfgOk_java (b := 8) (G := 8192) (H := 100) (by decide)
  refine room_of_bounds hI hF hm hh hcap (fun e _ h1 _ => ?_)
  have he : e < 50 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp (lt_of_le_of_lt h1 hN)
  have h51 : 2 ^ 51 ≤ 2 ^ ((Cfg.java 8 8192 100).H - e) :=
    Nat.pow_le_pow_right (by norm_num) (by simp only [Cfg.java]; omega)
  have k : (2 : Nat) ^ 50 + 2 ^ 20 ≤ 2 ^ 51 := by norm_num
  omega

/-- The fuel at H = 100: transactions of up to 2^20 operations. -/
theorem fuelOk_java_100 {b p : Nat} (hb : b ≤ 62) (hp : p ≤ 2 ^ 20) :
    FuelOk (Cfg.java b 8192 100) p :=
  fuelOk_java hb (by omega) hp

/-- **PE accepts every transaction Java admits**, at Java's parameters with
the model's G = 8,192 and H = 126: at node sizes 8, 14, 30 and 62, from a
state PE keeps whose tree meets the fill rules (`FillOk`) and has fewer than
2^63 nodes, every transaction of at most 2^20 operations whose puts' keys the
tree can hold (`keyOk`: well formed, at most 8,193 segments). Java admits at
most 500 operations a user transaction (`Db.MAX_OPERATIONS`). -/
theorem pe_accepts_java {b : Nat} {t i : Time} {s : Tree} {tp : Top} {next : NodeId}
    {ops : List Op} (hb : b ∈ [8, 14, 30, 62]) (hI : Inv (Cfg.java b 8192 126) t s tp next)
    (hfill : FillOk b 126 s) (hN : (reach s).length < 2 ^ 63) (hp : ops.length ≤ 2 ^ 20)
    (hputs : ∀ k v, Op.put k v ∈ ops → keyOk (Cfg.java b 8192 126) k = true) :
    ∃ o, peTx (Cfg.java b 8192 126) i s tp next ops = some o := by
  obtain ⟨hf, hr⟩ := accept_java_of_shapeFaults hb hI hfill hN hp
  exact pe_accepts (cfgOk_java hb).1 hI hputs hf hr

end Contract.PE
