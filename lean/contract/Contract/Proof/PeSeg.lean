/-
bergdb 030-21: one segment's tree, planned, settled and emitted, and the
next segments' trees below its leaves: what `planTree` gives (`planTree_ok`,
by induction on the fuel), and the space root's step of `peTx` (`seg_space`).

The parts:

* A. The old tree: the old leaf level's walks (`content_walks`), their levels
  (`walk_below`), the keys a segment tree holds (`keys_ok`).
* B. Lists and the settle: lookups after abstract operations, payloads in
  order (`pays_sublist`), the root settled (`settle_vok`, `settle_shape`).
* C. The runs' writes, one after the other (`runs_writes`).
* D. `applyGroups`: one run for each compare value touched (`ag_runs`).
* E. The segment's step from its plan (`seg_none`, `seg_some`).
* F. `planTree_ok`, `seg_space`.

The writes are stated with `WOkV`, `WOk` with values written: a value node
that `applyGroups` writes for a put has no klongs, so `WOk`'s `times` (every
node written a key node) does not hold of a segment's writes. `SegPre` asks
no live klong of the old root: an empty space root has none.
-/
import Contract.Proof.PePost
import Contract.Proof.PeOwn
import Contract.Proof.PeKeys
import Contract.Proof.PeRuns

namespace Contract.PE

open PeProof PeProof.Abs PeProof.Keys

variable {cf : Cfg} {i : Time} {s : Tree}

/-! ## Definitions -/

/-- The old root's nodes (none: no old tree). -/
def Ro (s : Tree) : Option NodeId → List NodeId
  | some r => R s r
  | none => []

/-- The old root's keys (none: no old tree). -/
def Lo (s : Tree) : Option NodeId → List (Key × Nat)
  | some r => L s r
  | none => []

/-- What a run from acc to acc' writes, W (newest first): each node once; a
fresh id of the run or an old node of U; every time klong of a key node
written at most i; an old key node keeps its klongs and gets klongs after a
time klong of i. (`WOk`, with values written too.) -/
structure WOkV (i : Time) (s : Tree) (U : List NodeId) (acc acc' : Acc)
    (W : List (NodeId × Obj)) : Prop where
  ws : acc'.ws = W ++ acc.ws
  next : acc.next ≤ acc'.next
  nodup : (W.map (·.1)).Nodup
  ids : ∀ w ∈ W.map (·.1), (acc.next ≤ w ∧ w < acc'.next) ∨ w ∈ U
  times : ∀ p ∈ W, ∀ n, p.2 = .key n → ∀ t, Klong.time t ∈ n.ks → t ≤ i
  frame : ∀ p ∈ W, ∀ n, s.obj p.1 = some (.key n) →
    ∃ more, p.2 = .key { n with ks := n.ks ++ Klong.time i :: more }

/-- A tree T after a run's writes W, for the old nodes U the run owns: it has
the writes, every other node of U is as in s, and every node of s is a node
of T. -/
structure After (s T : Tree) (W : List (NodeId × Obj)) (U : List NodeId) : Prop where
  ws : ∀ p ∈ W, T.obj p.1 = some p.2
  keep : ∀ z ∈ U, z ∉ W.map (·.1) → T.obj z = s.obj z
  exist : ∀ z, s.obj z ≠ none → T.obj z ≠ none

/-- What a segment tree's new root r' of segment g holds in T: shaped at
height ht within H, sound as a segment tree's root, the keys Lnew, every node
reached meeting the rules of one node, the nodes reached (with its fuel or
more) among B, a live klong or a leaf. -/
structure RootIn (cf : Cfg) (T : Tree) (g ht : Nat) (r' : NodeId) (Lnew : List (Key × Nat))
    (B : List NodeId) : Prop where
  hH : ht ≤ cf.H
  shaped : Shaped cf T g ht r'
  good : Good T r' 0 none
  keys : L T r' = Lnew
  nok : NOk cf.params T r'
  reach : ∀ f, cf.lev g ht + 1 ≤ f → (reachAt T f r').Subperm B
  rootLive : ∀ m, T.obj r' = some (.key m) → m.leaf = true ∨ live m.ks ≠ []

/-- The facts of the tree before and of the operations for a run on segment g
from the old root (none: no old tree) with the next id acc.next. -/
structure SegPre (cf : Cfg) (i : Time) (s : Tree) (g : Nat) (root : Option NodeId)
    (ops : List Op) (acc : Acc) : Prop where
  sok : SOk cf i s
  fresh : ∀ x, acc.next ≤ x → s.obj x = none
  ops : ∀ op ∈ ops, keyOk cf op.key = true ∧ g < op.key.length
  root : ∀ r, root = some r → Shaped cf s g (htIn cf s r) r ∧ Good s r 0 none ∧ (R s r).Nodup

/-- What a run of `planTree` from acc to acc' on segment g gives: its writes
(each once, fresh or an old node of the old tree; an old node written is a
key node), and in any tree after them: every key node written meets the
rules of one node and has a klong; no new root, and the keys after the
operations are none; or a new root r' that holds the keys after the
operations, has a live klong, and reaches only old nodes of the old tree and
fresh ids of the run. -/
def TreeOk (cf : Cfg) (i : Time) (s : Tree) (g : Nat) (root : Option NodeId) (ops : List Op)
    (acc acc' : Acc) (res : Option NodeId) : Prop :=
  ∃ W, WOkV i s (Ro s root) acc acc' W ∧ (∀ p ∈ W, ∀ o, s.obj p.1 = some o → ∃ n, o = .key n) ∧
    ∀ T, After s T W (Ro s root) →
      (∀ p ∈ W, ∀ n, p.2 = .key n → nodeOk cf.params T n = true ∧ n.ks ≠ []) ∧
      match res with
      | none => applyOps (ops.map (dropKey g)) (Lo s root) = []
      | some r' => (∃ ht, RootIn cf T g ht r' (applyOps (ops.map (dropKey g)) (Lo s root))
          (Ro s root ++ List.range' acc.next (acc'.next - acc.next))) ∧
          ∃ m, T.obj r' = some (.key m) ∧ live m.ks ≠ []

/-- What one compare value's run of `applyGroups` at segment g does, with the
group grp of its operations, from the old entry y0 of its compare value: its
writes (as `TreeOk`'s, the old nodes those reached from y0), and in a tree
after them: every key node written meets the rules of one node; the entry it
ends with holds the old entry's keys with the group applied (relative to
segment g); and a new entry is a node of T, a sound payload of its compare
value, the shaped root of a sound next segment's tree if the compare value is
long, and reaches only the old entry's nodes and the run's fresh ids. -/
def RunOk (cf : Cfg) (i : Time) (s : Tree) (g : Nat) (grp : List Op) (y0 : Option NodeId)
    (r : Run) : Prop :=
  ∃ W, WOkV i s (Ro s y0) r.a r.a' W ∧ (∀ p ∈ W, ∀ o, s.obj p.1 = some o → ∃ n, o = .key n) ∧
    ∀ T, After s T W (Ro s y0) →
      (∀ p ∈ W, ∀ n, p.2 = .key n → nodeOk cf.params T n = true ∧ n.ks ≠ []) ∧
      entry (fun c y => klongList T true (L T) c y) r.c r.res =
        applyOps (grp.map (dropKey g)) (entry (fun c y => klongList s true (L s) c y) r.c y0) ∧
      ∀ y, r.res = some y → T.obj y ≠ none ∧ PayGood cf T g r.c y ∧
        (isLong r.c = true → Shaped cf T (g + 1) (htIn cf T y) y ∧ NOk cf.params T y) ∧
        ∀ f, cf.lev g 0 ≤ f → (reachAt T f y).Subperm
          (Ro s y0 ++ List.range' r.a.next (r.a'.next - r.a.next))

/-- `planTree`'s result at every fuel below F. -/
def TreeIH (cf : Cfg) (i : Time) (s : Tree) (F : Nat) : Prop :=
  ∀ f < F, ∀ (root : Option NodeId) (g : Nat) (ops : List Op) (acc : Acc) (res : Option NodeId)
    (acc' : Acc), SegPre cf i s g root ops acc → planTree cf i s f root g ops acc = some (res, acc') →
    TreeOk cf i s g root ops acc acc' res

/-- The facts of a segment's old tree from its root (none: no old tree), with
its old leaf level E. -/
structure OldSeg (cf : Cfg) (s : Tree) (g : Nat) (root : Option NodeId)
    (E : List (Nat × NodeId)) : Prop where
  sorted : E.Pairwise CvLtA
  pay : ∀ e ∈ E, PayGood cf s g e.1 e.2 ∧
    (isLong e.1 = true → Shaped cf s (g + 1) (htIn cf s e.2) e.2)
  nodup : (Ro s root).Nodup
  walks : (E.flatMap (fun e => R s e.2)).Subperm (Ro s root)
  exist : ∀ z ∈ Ro s root, s.obj z ≠ none
  below : ∀ e ∈ E, ∀ z ∈ R s e.2, ∀ n, s.obj z = some (.key n) → n.level < cf.lev g 0
  keys : Lo s root = E.flatMap (fun e => klongList s true (L s) e.1 e.2)

/-- The facts of a planned segment tree v of height h, from the old leaf level
E, with its runs from acc0 to acc1: one of the program's nodes; its leaf level
is the old one with operations applied, one for each compare value touched,
each a run's result; in order; the old nodes it uses and its payloads' old
parts among the old tree's; an untouched payload is the old entry; the runs
one after the other, one for each compare value touched, each meeting `RunOk`
with its group and old entry, whose walk is none of the old nodes v uses. -/
structure PlanSeg (cf : Cfg) (i : Time) (s : Tree) (g : Nat) (root : Option NodeId)
    (E : List (Nat × NodeId)) (ops : List Op) (h : Nat) (v : VN) (runs : List Run)
    (acc0 acc1 : Acc) : Prop where
  vok : VOk cf s g h v
  eok : EOk cf i s g h v
  sops : ∃ sops : List Abs.Op, content h (absV s h v) = Abs.applyOps sops E ∧
    sops.map Abs.Op.cv = touched g ops ∧ ∀ o ∈ sops, ∃ r ∈ runs, r.c = o.cv ∧ o = opOf r.c r.res
  wfe : WFE h 0 none (absV s h v)
  own : (Ui s v ++ (pays v).flatMap (oldPart s E)).Subperm (Ro s root)
  untouched : ∀ p ∈ pays v, p.1 ∉ touched g ops → E.lookup p.1 = some p.2
  chain : Chain acc0 runs acc1
  perm : (runs.map (·.c)).Perm (touched g ops)
  run : ∀ r ∈ runs, RunOk cf i s g (ops.filter (fun op => segAt g op == r.c)) (E.lookup r.c) r
  outUi : ∀ r ∈ runs, ∀ y0, E.lookup r.c = some y0 → ∀ z ∈ R s y0, z ∉ Ui s v

/-! ## A. The old tree -/

/-- The old leaf level's entries walk within the node's walk, after the node,
each once. -/
theorem a_flatMap_sublist {α β : Type} {f f' : α → List β} :
    ∀ (l : List α), (∀ a ∈ l, (f a).Sublist (f' a)) → (l.flatMap f).Sublist (l.flatMap f')
  | [], _ => by simp
  | a :: l, h => by
    simp only [List.flatMap_cons]
    exact (h a List.mem_cons_self).append
      (a_flatMap_sublist l (fun b hb => h b (List.mem_cons_of_mem _ hb)))

theorem content_walks : ∀ (h : Nat) {g : Nat} {x : NodeId} {lo : Nat} {hi : Option Nat},
    Shaped cf s g h x → Good s x lo hi →
    ((content h (view h s x)).flatMap (fun e => R s e.2)).Sublist (R s x).tail
  | 0, g, x, lo, hi, hsh, hg => by
    obtain ⟨n, hobj, _, _, _, _⟩ := hsh.inv_leaf
    rw [R_good hg hobj]
    show ((view 0 s x).flatMap (fun e => R s e.2)).Sublist _
    rw [view_zero hobj]
    exact List.Sublist.refl _
  | h + 1, g, x, lo, hi, hsh, hg => by
    obtain ⟨n, hobj, hleaf, _, _, _, _, hk⟩ := hsh.inv_inner
    rw [R_shaped hsh hobj, content_view_succ hobj, List.flatMap_assoc]
    apply a_flatMap_sublist
    rintro ⟨c, y⟩ hcy
    obtain ⟨m, lo', hi', _, _, _, hg'⟩ := hg.child hobj hcy (by simp [hleaf])
    exact (content_walks h (hk c y hcy) hg').trans (List.tail_sublist _)

/-- Every key node reached from a sound key node m is at most m's level. -/
theorem a_R_level : ∀ (k : Nat) {y : NodeId} {lo : Nat} {hi : Option Nat} {m : KNode},
    m.level < k → Good s y lo hi → s.obj y = some (.key m) →
    ∀ z ∈ R s y, ∀ n, s.obj z = some (.key n) → n.level ≤ m.level
  | 0, _, _, _, _, hk, _, _ => absurd hk (Nat.not_lt_zero _)
  | k + 1, y, lo, hi, m, hk, hg, hobj => by
    intro z hz n hzn
    rcases R_good_kids hg hobj hz with rfl | ⟨c, y', hm, hz'⟩
    · rw [hobj] at hzn
      obtain rfl : m = n := by injection hzn with h1; injection h1
      exact le_refl _
    · rcases good_kids hg hobj c y' hm with ⟨m', hm1, hm2, lo', hi', hg'⟩ | ⟨v, hv⟩
      · have := a_R_level k (by omega) hg' hm1 z hz' n hzn
        omega
      · have hR : R s y' = [y'] := reachAt_val hv _
        rw [hR, List.mem_singleton] at hz'
        subst hz'
        rw [hv] at hzn; cases hzn

theorem walk_below : ∀ (h : Nat) {g : Nat} {x : NodeId} {lo : Nat} {hi : Option Nat},
    Shaped cf s g h x → Good s x lo hi → ∀ e ∈ content h (view h s x), ∀ z ∈ R s e.2, ∀ n,
      s.obj z = some (.key n) → n.level < cf.lev g 0
  | 0, g, x, lo, hi, hsh, hg => by
    obtain ⟨n0, hobj, hleaf, hlev, _, _⟩ := hsh.inv_leaf
    intro e he z hz n hzn
    have he' : e ∈ live n0.ks := by
      have : e ∈ view 0 s x := he
      rwa [view_zero hobj] at this
    obtain ⟨c, y⟩ := e
    cases hg with
    | mk _ _ _ n' hobj' _ _ _ hval hkey hseg _ =>
      rw [hobj] at hobj'
      obtain rfl : n0 = n' := by injection hobj' with h1; injection h1
      by_cases hl : isLong c = true
      · obtain ⟨m, hm1, hm2, _⟩ := hkey c y he' (fun _ => hl)
        have := a_R_level (m.level + 1) (Nat.lt_succ_self _) (hseg hleaf c y he' hl) hm1 z hz n hzn
        omega
      · obtain ⟨v, hv⟩ := hval hleaf c y he' (by simpa using hl)
        have hR : R s y = [y] := reachAt_val hv _
        rw [hR, List.mem_singleton] at hz
        subst hz
        rw [hv] at hzn; cases hzn
  | h + 1, g, x, lo, hi, hsh, hg => by
    obtain ⟨n0, hobj, hleaf, _, _, _, _, hk⟩ := hsh.inv_inner
    intro e he
    rw [content_view_succ hobj, List.mem_flatMap] at he
    obtain ⟨⟨c, y⟩, hcy, he⟩ := he
    obtain ⟨m, lo', hi', _, _, _, hg'⟩ := hg.child hobj hcy (by simp [hleaf])
    exact walk_below h (hk c y hcy) hg' e he

theorem a_keys : ∀ (d : Nat) {g h : Nat} {r : NodeId}, cf.G + 1 - g ≤ d → Shaped cf s g h r →
    Good s r 0 none → ∀ kv ∈ L s r, keyWf kv.1 = true ∧ kv.1.length + g ≤ cf.G + 1
  | d, g, h, r, hd, hsh, hg => by
    obtain ⟨n, hobj, _, _, hG, _⟩ := shaped_obj hsh
    intro kv hkv
    rw [view_L_pays h hg hsh, List.mem_flatMap] at hkv
    obtain ⟨p, hp, hkv⟩ := hkv
    obtain ⟨hpg, hpsh⟩ := view_pay h hg hsh p hp
    obtain ⟨k, v⟩ := kv
    rcases mem_klongList.mp hkv with ⟨_, hl, k', rfl, hk'⟩ | ⟨_, hl, rfl, _⟩ | ⟨h0, _⟩
    · obtain ⟨m, _, _, _, hgy⟩ := hpg.2 hl
      cases d with
      | zero => omega
      | succ d =>
        obtain ⟨h1, h2⟩ := a_keys d (g := g + 1) (by omega) (hpsh hl) hgy (k', v) hk'
        dsimp only at h1 h2
        refine ⟨?_, by simp only [List.length_cons]; omega⟩
        cases k' with
        | nil => simp [keyWf] at h1
        | cons a r => simp [keyWf, hl, h1]
    · exact ⟨by simp [keyWf, hl], by simp only [List.length_singleton]; omega⟩
    · cases h0

theorem keys_ok {g h : Nat} {r : NodeId} (hsh : Shaped cf s g h r) (hg : Good s r 0 none) :
    ∀ kv ∈ L s r, keyWf kv.1 = true ∧ kv.1.length + g ≤ cf.G + 1 :=
  a_keys _ (le_refl _) hsh hg

/-! ## B. Lists and the settle -/

theorem b_applyOp_lookup (m : List (Nat × Nat)) (o : Abs.Op) (c : Nat) (hc : c ≠ o.cv) :
    (Abs.applyOp m o).lookup c = m.lookup c := by
  cases o with
  | put c' v =>
    simp only [Abs.Op.cv] at hc
    show (Abs.mput c' v m).lookup c = _
    rw [mput_lookup]; simp [hc]
  | del c' =>
    simp only [Abs.Op.cv] at hc
    show (m.filter (fun e => e.1 != c')).lookup c = _
    rw [filter_lookup]; simp [hc]

theorem absApply_lookup_out : ∀ (sops : List Abs.Op) (m : List (Nat × Nat)) (c : Nat),
    c ∉ sops.map Abs.Op.cv → (Abs.applyOps sops m).lookup c = m.lookup c
  | [], _, _, _ => rfl
  | o :: sops, m, c, hc => by
    simp only [List.map_cons, List.mem_cons, not_or] at hc
    show (Abs.applyOps sops (Abs.applyOp m o)).lookup c = _
    rw [absApply_lookup_out sops _ c hc.2, b_applyOp_lookup m o c hc.1]

theorem b_applyOp_opOf (m : List (Nat × Nat)) (c : Nat) (y : Option NodeId) :
    (Abs.applyOp m (opOf c y)).lookup c = y := by
  cases y with
  | some y => show (Abs.mput c y m).lookup c = some y; rw [mput_lookup]; simp
  | none => show (m.filter (fun e => e.1 != c)).lookup c = none; rw [filter_lookup]; simp

theorem absApply_lookup_opOf (sops : List Abs.Op) (m : List (Nat × Nat)) (c : Nat)
    (y : Option NodeId) (hnd : (sops.map Abs.Op.cv).Nodup) (hin : opOf c y ∈ sops) :
    (Abs.applyOps sops m).lookup c = y := by
  induction sops generalizing m with
  | nil => simp at hin
  | cons o sops ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    show (Abs.applyOps sops (Abs.applyOp m o)).lookup c = y
    rcases List.mem_cons.mp hin with h | h
    · subst h
      have hcv : (opOf c y).cv = c := by cases y <;> rfl
      rw [hcv] at hnd
      rw [absApply_lookup_out sops _ c hnd.1, b_applyOp_opOf]
    · exact ih _ hnd.2 h

theorem b_kidsWF_holds {h : Nat} (IH : ∀ lo hi (x : Node h), WF h lo hi x → Abs.Holds h lo hi x) :
    ∀ (ks : List (Nat × Node h)) (lo lo0 : Nat) (hi : Option Nat), ks ≠ [] →
      KidsWF (WF h) lo hi ks → (∀ c x, ks.head? = some (c, x) → max lo c = lo0) →
      (∀ e ∈ ks.tail, lo < e.1) → (∀ e ∈ ks, Below e.1 hi) → HoldsKids (Abs.Holds h) lo0 hi ks
  | [], _, _, _, hne, _, _, _, _ => absurd rfl hne
  | [(c, x)], lo, lo0, hi, _, ⟨h1, _⟩, hh, _, _ => by
    have := hh c x rfl
    rw [this] at h1
    exact IH _ _ x h1
  | (c, x) :: (c', y) :: r, lo, lo0, hi, _, ⟨h1, h2⟩, hh, htail, hb => by
    have e1 := hh c x rfl
    rw [e1] at h1
    have hc' : lo < c' := htail (c', y) (by simp)
    have hr := WF_range h1
    simp only [nxt, Below] at hr
    refine ⟨by omega, hb (c', y) (by simp), IH _ _ x h1,
      b_kidsWF_holds IH ((c', y) :: r) lo c' hi (by simp) h2
        (fun c0 x0 h0 => by simp only [List.head?_cons, Option.some.injEq, Prod.mk.injEq] at h0; omega)
        (fun e he => htail e (by simp at he ⊢; exact Or.inr he))
        (fun e he => hb e (List.mem_cons_of_mem _ he))⟩

/-- 026-24's order gives what `Plan.keys` needs of the old node. -/
theorem holds_of_WF : ∀ (h : Nat) {lo : Nat} {hi : Option Nat} {x : Node h}, WF h lo hi x →
    Abs.Holds h lo hi x
  | 0, _, _, _, hw => ⟨hw.2.1, hw.2.2⟩
  | h + 1, lo, hi, x, hw => by
    have htail := WF_tail_above hw
    obtain ⟨w1, _, w3, w4⟩ := hw
    show HoldsKids (Abs.Holds h) lo hi (kids x)
    refine b_kidsWF_holds (fun lo hi x hx => holds_of_WF h hx) (kids x) lo lo hi ?_ w4 ?_ htail w3
    · intro he; rw [he] at w1; cases w1
    · intro c x0 h0
      rw [h0] at w1
      simp only [Option.map_some, Option.some.injEq] at w1
      simp [w1]

/-- A planned node's payloads are a sublist of its leaf level. -/
theorem pays_sublist {g : Nat} : ∀ (h : Nat) {w : VN}, VOk cf s g h w →
    (pays w).Sublist (content h (absV s h w)) := by
  intro h w hv
  induction hv with
  | old _ _ _ => exact List.nil_sublist _
  | leaf _ _ _ =>
    simp only [pays_node, ↓reduceIte]
    exact List.Sublist.refl _
  | @inner h base join es F dec _ _ _ _ _ ih =>
    simp only [pays_node, Nat.add_one_ne_zero, ↓reduceIte]
    show (es.flatMap (fun e => pays e.2)).Sublist
      ((es.map (fun e => (e.1, absV s h e.2))).flatMap (fun e => content h e.2))
    rw [List.flatMap_map]
    exact a_flatMap_sublist es (fun e he => ih e he)

theorem b_view_ne_iff {z : NodeId} {m : KNode} (hobj : s.obj z = some (.key m)) :
    ∀ h, view h s z ≠ [] ↔ live m.ks ≠ []
  | 0 => by rw [view_zero hobj]; exact Iff.rfl
  | h + 1 => by
    have : kids (view (h + 1) s z) = (live m.ks).map (fun cy => (cy.1, view h s cy.2)) :=
      view_succ hobj
    show kids (view (h + 1) s z) ≠ [] ↔ _
    rw [this]; simp

/-- What a settle gives: one of the program's nodes, of one of three shapes. -/
theorem b_settle (hcf : cf.Ok) : ∀ (f g : Nat) (space : Bool) (h : Nat) (v v' : VN),
    VOk cf s g h v → settleRoot cf i s f g v space = some (some v') →
    (∃ h', VOk cf s g h' v') ∧ ((∃ y, v' = .old y) ∨
      (∃ b g' join es F dec, v' = .node b g' 0 join es F dec) ∨
      (∃ b g' h'' join es F dec, v' = .node b g' (h'' + 1) join es F dec ∧ F ≠ []))
  | 0, _, _, _, _, _, _, hs => by simp [settleRoot] at hs
  | f + 1, g, space, h, v, v', hv, hs => by
    unfold settleRoot at hs
    cases v with
    | old y =>
      have hdone : (∃ h', VOk cf s g h' (.old y)) ∧ ((∃ y', VN.old y = .old y') ∨
          (∃ b g' join es F dec, VN.old y = .node b g' 0 join es F dec) ∨
          (∃ b g' h'' join es F dec, VN.old y = .node b g' (h'' + 1) join es F dec ∧ F ≠ [])) :=
        ⟨⟨h, hv⟩, Or.inl ⟨y, rfl⟩⟩
      simp only at hs
      cases hgk : getKey s y with
      | none => rw [hgk] at hs; cases hs
      | some n =>
        rw [hgk] at hs
        simp only at hs
        have hobj : s.obj y = some (.key n) := by
          unfold getKey at hgk
          split at hgk
          · rename_i n' h0; cases hgk; exact h0
          · cases hgk
        split at hs
        · rename_i c z hl
          split at hs
          · simp only [Option.some.injEq] at hs; subst hs; exact hdone
          · rename_i hleaf
            cases hv with
            | old hsh hgd _ =>
              cases hsh with
              | leaf hobj' hleaf' _ _ _ =>
                rw [hobj] at hobj'
                obtain rfl : n = _ := by injection hobj' with h1; injection h1
                exact absurd hleaf' hleaf
              | @inner _ h'' _ n' hobj' hleaf' _ _ _ _ hkids =>
                rw [hobj] at hobj'
                obtain rfl : n = n' := by injection hobj' with h1; injection h1
                have hmz : (c, z) ∈ live n.ks := by rw [hl]; simp
                have hz : Shaped cf s g h'' z := hkids c z hmz
                obtain ⟨lo, hi, hgd⟩ := hgd
                obtain ⟨m, lo', hi', hm1, _, hm3, hgz⟩ := hgd.child hobj hmz (by simp [hleaf'])
                have hvz : VOk cf s g h'' (.old z) :=
                  VOk.old hz ⟨lo', hi', hgz⟩ ((b_view_ne_iff hm1 h'').mpr hm3)
                exact b_settle hcf f g space h'' (.old z) v' hvz hs
        · simp only [Option.some.injEq] at hs; subst hs; exact hdone
    | node base g' hv' join es F dec =>
      obtain ⟨hh1, hh2⟩ := hv.ht
      subst hv' g'
      simp only at hs
      split at hs
      · rename_i hF
        have hF' : F = [] := List.isEmpty_iff.mp hF
        have hes := es_nil_of_F hv hF'
        subst hes
        split at hs
        · cases hs
        · split at hs
          · rename_i hh
            simp only [Option.some.injEq] at hs; subst hs
            simp only [beq_iff_eq] at hh
            subst hh
            exact ⟨⟨0, hv⟩, Or.inr (Or.inl ⟨base, g, join, [], F, dec, rfl⟩)⟩
          · cases hm : mkNode cf i s none g 0 false [] with
            | none => rw [hm] at hs; cases hs
            | some w =>
              rw [hm] at hs
              simp only [Option.map_some, Option.some.injEq] at hs
              subst hs
              obtain ⟨⟨F2, dec2, rfl⟩, hw⟩ := mkNode_leaf hcf hm (by simp)
              exact ⟨⟨0, hw⟩, Or.inr (Or.inl ⟨none, g, false, [], F2, dec2, rfl⟩)⟩
      · rename_i hF
        have hFne : F ≠ [] := by
          intro h0; rw [h0] at hF; simp at hF
        have hdone : (∃ h', VOk cf s g h' (.node base g h join es F dec)) ∧
            ((∃ y', VN.node base g h join es F dec = .old y') ∨
            (∃ b g' join' es' F' dec', VN.node base g h join es F dec = .node b g' 0 join' es' F' dec') ∨
            (∃ b g' h'' join' es' F' dec', VN.node base g h join es F dec =
              .node b g' (h'' + 1) join' es' F' dec' ∧ F' ≠ [])) := by
          refine ⟨⟨h, hv⟩, ?_⟩
          cases h with
          | zero => exact Or.inr (Or.inl ⟨base, g, join, es, F, dec, rfl⟩)
          | succ h'' => exact Or.inr (Or.inr ⟨base, g, h'', join, es, F, dec, rfl, hFne⟩)
        split at hs
        · rename_i hone
          simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hone
          obtain ⟨hh, _⟩ := hone
          obtain ⟨h'', rfl⟩ : ∃ h'', h = h'' + 1 := ⟨h - 1, by omega⟩
          split at hs
          · rename_i c ch
            cases hv with
            | inner hk _ _ _ _ =>
              exact b_settle hcf f g space h'' ch v' (hk (c, ch) (by simp)) hs
          · cases hs
        · split at hs
          · rename_i k
            split at hs
            · cases hm : mkNode cf i s none g (h + 1) false
                  [(0, .node base g h join es F (.parts k))] with
              | none => rw [hm] at hs; cases hs
              | some r =>
                rw [hm] at hs
                simp only at hs
                have hne : (VN.node base g h join es F (.parts k)).isEmpty = false := by
                  simp only [VN.isEmpty]; simpa using hF
                obtain ⟨_, hr⟩ := mkNode_inner hcf hm
                  (by intro e he; simp at he; subst he; exact hv)
                  (by intro e he; simp at he; subst he; exact hne)
                exact b_settle hcf f g space (h + 1) _ v' hr hs
            · simp only [Option.some.injEq] at hs; subst hs; exact hdone
          · simp only [Option.some.injEq] at hs; subst hs; exact hdone

/-- A root settled from one of the program's nodes is one of them. -/
theorem settle_vok (hcf : cf.Ok) {f g : Nat} {space : Bool} {h h' : Nat} {v v' : VN}
    (hv : VOk cf s g h v) (hs : settleRoot cf i s f g v space = some (some v'))
    (hr : RootOk cf s g h' v') : VOk cf s g h' v' := by
  rcases hr with ⟨z, rfl, hz⟩ | hr
  · obtain ⟨⟨h'', hv''⟩, _⟩ := b_settle hcf f g space h v _ hv hs
    cases hv'' with
    | old hsh hgd hne =>
      obtain ⟨m, hobj, _⟩ := shaped_obj hsh
      exact VOk.old hz hgd ((b_view_ne_iff hobj h').mpr ((b_view_ne_iff hobj h'').mp hne))
  · exact hr

/-- A root settled is an untouched node, a leaf, or an inner node with a
final list. -/
theorem settle_shape (hcf : cf.Ok) : ∀ (f g : Nat) (space : Bool) (h : Nat) (v v' : VN),
    VOk cf s g h v → settleRoot cf i s f g v space = some (some v') →
    (∃ y, v' = .old y) ∨ (∃ b g' join es F dec, v' = .node b g' 0 join es F dec) ∨
      (∃ b g' h'' join es F dec, v' = .node b g' (h'' + 1) join es F dec ∧ F ≠ []) :=
  fun f g space h v v' hv hs => (b_settle hcf f g space h v v' hv hs).2

/-- A root that is not the space root settles into a tree only if it holds
something. -/
theorem settle_content (_hcf : cf.Ok) {f g h : Nat} {v v' : VN} (hv : VOk cf s g h v)
    (hw : WFE h 0 none (absV s h v)) (hs : settleRoot cf i s f g v false = some (some v')) :
    content h (absV s h v) ≠ [] := by
  have hne : absV s h v ≠ [] := by
    cases v with
    | old y => cases hv with | old _ _ hne => cases h <;> exact hne
    | node base g' h0 join es F dec =>
      apply absV_ne hv
      cases hF : F.isEmpty with
      | false => simpa [VN.isEmpty] using hF
      | true =>
        cases f with
        | zero => simp [settleRoot] at hs
        | succ f =>
          unfold settleRoot at hs
          simp [hF] at hs
  rcases hw with h0 | hw
  · exact absurd h0 hne
  · exact content_ne_nil h 0 none _ hw

/-- A root that emit writes as one node: its one piece. -/
theorem finEnts_single {h : Nat} (v : VN) (fv : Node h) (hl : (finEnts 0 v fv).length = 1) :
    finEnts 0 v fv = [(0, fv)] := by
  cases v with
  | old y => rfl
  | node base g' h' join es F dec =>
    cases dec with
    | parts k =>
      simp only [finEnts] at hl ⊢
      split at hl
      · rw [cutEnts_length, cutList_length, partSizes_length] at hl; omega
      · rename_i hk; simp [hk]
    | same => rfl
    | append => rfl

/-! ## C. The runs' writes -/

/-- Two runs' writes one after the other (`WOk.append` for `WOkV`). -/
theorem c_wokv_append {U1 U2 : List NodeId} {a0 a1 a2 : Acc} {W1 W2 : List (NodeId × Obj)}
    (hfresh : ∀ x, a0.next ≤ x → s.obj x = none) (h1 : WOkV i s U1 a0 a1 W1)
    (h2 : WOkV i s U2 a1 a2 W2) (hnd : (U1 ++ U2).Nodup) (hex : ∀ z ∈ U1 ++ U2, s.obj z ≠ none) :
    WOkV i s (U1 ++ U2) a0 a2 (W2 ++ W1) := by
  have hn1 := h1.next
  have hn2 := h2.next
  refine ⟨by rw [h2.ws, h1.ws, List.append_assoc], by nomega, ?_, ?_, ?_, ?_⟩
  · rw [List.map_append, List.nodup_append]
    refine ⟨h2.nodup, h1.nodup, ?_⟩
    intro w hw w' hw' hww
    subst hww
    rw [List.nodup_append] at hnd
    rcases h2.ids w hw with ⟨r1, r2⟩ | u2 <;> rcases h1.ids w hw' with ⟨q1, q2⟩ | u1
    · nomega
    · exact hex w (List.mem_append_left _ u1) (hfresh w (by nomega))
    · exact hex w (List.mem_append_right _ u2) (hfresh w (by nomega))
    · exact hnd.2.2 w u1 w u2 rfl
  · intro w hw
    rw [List.map_append, List.mem_append] at hw
    rcases hw with hw | hw
    · rcases h2.ids w hw with ⟨r1, r2⟩ | u2
      · left; constructor <;> nomega
      · exact Or.inr (List.mem_append_right _ u2)
    · rcases h1.ids w hw with ⟨r1, r2⟩ | u1
      · left; constructor <;> nomega
      · exact Or.inr (List.mem_append_left _ u1)
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact h2.times p hp
    · exact h1.times p hp
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact h2.frame p hp
    · exact h1.frame p hp

/-- **The runs' writes**: runs one after the other, each with its writes
(`WOkV` for its old nodes `Ur r`, and S), the old nodes distinct and nodes of
s, from a fresh Acc: their writes together, each one some run's, and each
run's writes among them, the only ones on its old nodes. -/
theorem runs_writes (S : Run → List (NodeId × Obj) → Prop) (Ur : Run → List NodeId) :
    ∀ (runs : List Run) (a a' : Acc), Chain a runs a' →
    (∀ r ∈ runs, ∃ W, WOkV i s (Ur r) r.a r.a' W ∧ S r W) →
    (runs.flatMap Ur).Nodup → (∀ z ∈ runs.flatMap Ur, s.obj z ≠ none) →
    (∀ z, a.next ≤ z → s.obj z = none) →
    ∃ W, WOkV i s (runs.flatMap Ur) a a' W ∧
      (∀ p ∈ W, ∃ r ∈ runs, ∃ Wr, WOkV i s (Ur r) r.a r.a' Wr ∧ S r Wr ∧ p ∈ Wr) ∧
      (∀ r ∈ runs, ∃ Wr, WOkV i s (Ur r) r.a r.a' Wr ∧ S r Wr ∧ (∀ p ∈ Wr, p ∈ W) ∧
        ∀ p ∈ W, p.1 ∈ Ur r → p ∈ Wr) := by
  intro runs
  induction runs with
  | nil =>
    intro a a' hch _ _ _ _
    simp only [Chain] at hch
    subst hch
    exact ⟨[], ⟨by simp, le_refl _, by simp, by simp, by simp, by simp⟩, by simp, by simp⟩
  | cons r rs ih =>
    intro a a' hch hrun hnd hex hfresh
    obtain ⟨hra, hrn, hch'⟩ := hch
    obtain ⟨Wr, hWr, hSr⟩ := hrun r (List.mem_cons_self ..)
    rw [List.flatMap_cons] at hnd hex ⊢
    have hnd' := List.nodup_append.mp hnd
    obtain ⟨_, hndrs, hdisj⟩ := hnd'
    have hfresh' : ∀ z, r.a'.next ≤ z → s.obj z = none := fun z hz =>
      hfresh z (by rw [← hra]; nomega)
    obtain ⟨Wq, hWq, hq1, hq2⟩ := ih r.a' a' hch'
      (fun r0 h0 => hrun r0 (List.mem_cons_of_mem _ h0)) hndrs
      (fun z hz => hex z (List.mem_append_right _ hz)) hfresh'
    refine ⟨Wq ++ Wr, c_wokv_append hfresh (hra ▸ hWr) hWq hnd hex, ?_, ?_⟩
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨r0, hr0, W0, h0, hS0, hp0⟩ := hq1 p hp
        exact ⟨r0, List.mem_cons_of_mem _ hr0, W0, h0, hS0, hp0⟩
      · exact ⟨r, List.mem_cons_self .., Wr, hWr, hSr, hp⟩
    · intro r0 hr0
      rcases List.mem_cons.mp hr0 with rfl | hr0
      · refine ⟨Wr, hWr, hSr, fun p hp => List.mem_append_right _ hp, ?_⟩
        intro p hp hpu
        rcases List.mem_append.mp hp with hp | hp
        · exfalso
          rcases hWq.ids p.1 (List.mem_map.mpr ⟨p, hp, rfl⟩) with ⟨q1, _⟩ | u
          · exact hex p.1 (List.mem_append_left _ hpu) (hfresh' p.1 q1)
          · exact hdisj p.1 hpu p.1 u rfl
        · exact hp
      · obtain ⟨W0, h0, hS0, hsub, hown⟩ := hq2 r0 hr0
        refine ⟨W0, h0, hS0, fun p hp => List.mem_append_left _ (hsub p hp), ?_⟩
        intro p hp hpu
        have hpu' : p.1 ∈ rs.flatMap Ur := List.mem_flatMap.mpr ⟨r0, hr0, hpu⟩
        rcases List.mem_append.mp hp with hp | hp
        · exact hown p hp hpu
        · exfalso
          rcases hWr.ids p.1 (List.mem_map.mpr ⟨p, hp, rfl⟩) with ⟨q1, _⟩ | u
          · exact hex p.1 (List.mem_append_right _ hpu') (hfresh p.1 (by rw [← hra]; exact q1))
          · exact hdisj p.1 u p.1 hpu' rfl

/-! ## D. applyGroups -/

/-- A short compare value's fold over its group (F, the step of
`applyGroups`'s fold for compare value c): one value written per put, at
consecutive fresh ids; the other compare values' lookups kept; the lookup of
c the last operation's effect. -/
theorem d_fold (c : Nat) (F : List (Nat × NodeId) × Acc → Op → List (Nat × NodeId) × Acc)
    (hFp : ∀ q k hv, F q (.put k hv) =
      (setEntry c q.2.next q.1, q.2.fresh.2.write q.2.next (.val hv)))
    (hFd : ∀ q k, F q (.del k) = (removeEntry c q.1, q.2))
    (es : List (Nat × NodeId)) (acc : Acc) : ∀ L : List Op,
    ∃ W, (L.foldl F (es, acc)).2.ws = W ++ acc.ws ∧
      acc.next ≤ (L.foldl F (es, acc)).2.next ∧
      (W.map (·.1)).Nodup ∧
      (∀ p ∈ W, (acc.next ≤ p.1 ∧ p.1 < (L.foldl F (es, acc)).2.next) ∧
        ∃ v, p.2 = .val v) ∧
      (∀ a, a ≠ c → (L.foldl F (es, acc)).1.lookup a = es.lookup a) ∧
      (∀ k hv, L.getLast? = some (.put k hv) →
        ∃ y, (L.foldl F (es, acc)).1.lookup c = some y ∧ (y, Obj.val hv) ∈ W) ∧
      (∀ k, L.getLast? = some (.del k) → (L.foldl F (es, acc)).1.lookup c = none) := by
  intro L
  induction L using List.reverseRecOn with
  | nil =>
    exact ⟨[], by simp, le_rfl, by simp, by simp, fun _ _ => rfl, by simp, by simp⟩
  | append_singleton l a ih =>
    obtain ⟨W, h1, h2, h3, h4, h5, _, _⟩ := ih
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, List.getLast?_concat]
    generalize l.foldl F (es, acc) = q at h1 h2 h4 h5
    cases a with
    | put k hv =>
      rw [hFp]
      refine ⟨(q.2.next, .val hv) :: W, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [Acc.write, Acc.fresh, h1]
      · simp only [Acc.write, Acc.fresh]
        nomega
      · rw [List.map_cons, List.nodup_cons]
        refine ⟨fun hm => ?_, h3⟩
        obtain ⟨p, hp, hpe⟩ := List.mem_map.mp hm
        have := (h4 p hp).1.2
        rw [hpe] at this
        nomega
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · simp only [Acc.write, Acc.fresh]
          exact ⟨⟨h2, by nomega⟩, hv, rfl⟩
        · obtain ⟨⟨b1, b2⟩, b3⟩ := h4 p hp
          refine ⟨⟨b1, ?_⟩, b3⟩
          simp only [Acc.write, Acc.fresh]
          nomega
      · intro a ha
        rw [setEntry_lookup, ite_eq_right ha, h5 a ha]
      · intro k' hv' he
        simp only [Option.some.injEq, Op.put.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact ⟨q.2.next, by rw [setEntry_lookup, ite_eq_left rfl], List.mem_cons_self⟩
      · intro k' he
        simp at he
    | del k =>
      rw [hFd]
      refine ⟨W, h1, h2, h3, h4, ?_, ?_, ?_⟩
      · intro a ha
        show (removeEntry c q.1).lookup a = _
        rw [removeEntry_lookup, ite_eq_right ha, h5 a ha]
      · intro k' hv' he
        simp at he
      · intro k' _
        show (removeEntry c q.1).lookup c = _
        rw [removeEntry_lookup, ite_eq_left rfl]

/-- **A short compare value's run**: its group's fold writes values only, and
ends with the last operation's effect. -/
theorem d_run_short {g c : Nat} {ops : List Op} {y0 : Option NodeId}
    {es0 es1 : List (Nat × NodeId)} {acc acc1 : Acc}
    (F : List (Nat × NodeId) × Acc → Op → List (Nat × NodeId) × Acc)
    (hq : (ops.filter (fun op => segAt g op == c)).foldl F (es0, acc) = (es1, acc1))
    (hFp : ∀ q k hv, F q (.put k hv) =
      (setEntry c q.2.next q.1, q.2.fresh.2.write q.2.next (.val hv)))
    (hFd : ∀ q k, F q (.del k) = (removeEntry c q.1, q.2))
    (hfresh : ∀ z, acc.next ≤ z → s.obj z = none)
    (hops : ∀ op ∈ ops, keyOk cf op.key = true ∧ g < op.key.length)
    (hne : ∃ op ∈ ops, segAt g op = c) (hc : isLong c = false) :
    RunOk cf i s g (ops.filter (fun op => segAt g op == c)) y0 ⟨c, es1.lookup c, acc, acc1⟩ ∧
      acc.next ≤ acc1.next ∧ ∀ a, a ≠ c → es1.lookup a = es0.lookup a := by
  have hw : ∀ op ∈ ops, keyWf op.key = true := fun op hop => by
    have := (hops op hop).1
    simp only [keyOk, Bool.and_eq_true] at this
    exact this.1
  have hg : ∀ op ∈ ops, g < op.key.length := fun op hop => (hops op hop).2
  obtain ⟨W, h1, h2, h3, h4, h5, h6, h7⟩ :=
    d_fold c F hFp hFd es0 acc (ops.filter (fun op => segAt g op == c))
  rw [hq] at h1 h2 h4 h5 h6 h7
  simp only at h1 h2 h4 h5 h6 h7
  obtain ⟨op0, hop0, hc0⟩ := hne
  have hgne : ops.filter (fun op => segAt g op == c) ≠ [] := by
    intro h
    have : op0 ∈ ops.filter (fun op => segAt g op == c) :=
      List.mem_filter.mpr ⟨hop0, by simp [hc0]⟩
    rw [h] at this
    simp at this
  obtain ⟨lop, hlop⟩ :
      ∃ lop, (ops.filter (fun op => segAt g op == c)).getLast? = some lop := by
    cases hl : (ops.filter (fun op => segAt g op == c)).getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp hl) hgne
    | some lop => exact ⟨lop, rfl⟩
  have hlopm := List.mem_of_getLast? hlop
  have hends : endsAt g lop = true := by
    obtain ⟨hm1, hm2⟩ := mem_grp hlopm
    rw [endsAt_of_keyWf (hw lop hm1) (hg lop hm1), hm2, hc]
    rfl
  have hkey : (dropKey g lop).key = [c] := by rw [dropKey_key_of_endsAt hends, (mem_grp hlopm).2]
  refine ⟨⟨W, ⟨h1, h2, h3, fun w hw' => ?_, fun p hp n hn => ?_, fun p hp n hn => ?_⟩,
    fun p hp o ho => ?_, fun T hT => ?_⟩, h2, h5⟩
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hw'
    exact Or.inl (h4 p hp).1
  · obtain ⟨v, hv⟩ := (h4 p hp).2
    rw [hv] at hn
    cases hn
  · rw [hfresh p.1 (h4 p hp).1.1] at hn
    cases hn
  · rw [hfresh p.1 (h4 p hp).1.1] at ho
    cases ho
  · have hm : entry (fun c y => klongList s true (L s) c y) c y0 = [] ∨
        ∃ v, entry (fun c y => klongList s true (L s) c y) c y0 = [([c], v)] := by
      cases y0 with
      | none => exact Or.inl rfl
      | some y => exact klongList_short s (L s) y hc
    have hblk := applyOps_short_block hw hg hc _ hm
    refine ⟨fun p hp n hn => ?_, ?_, ?_⟩
    · obtain ⟨v, hv⟩ := (h4 p hp).2
      rw [hv] at hn
      cases hn
    · show entry _ c (es1.lookup c) = _
      rw [hblk, List.getLast?_map, hlop]
      cases lop with
      | put k hv =>
        obtain ⟨y, hy, hyW⟩ := h6 k hv hlop
        rw [hy]
        have hTy : T.obj y = some (.val hv) := hT.ws _ hyW
        simp only [dropKey, Op.key] at hkey
        simp only [entry, klongList, hc, hTy, Option.map_some, dropKey, lastEffect, hkey]
        rfl
      | del k =>
        rw [h7 k hlop]
        rfl
    · intro y hy
      simp only at hy
      cases lop with
      | put k hv =>
        obtain ⟨y', hy', hyW⟩ := h6 k hv hlop
        rw [hy'] at hy
        obtain rfl : y' = y := Option.some.inj hy
        have hTy : T.obj y' = some (.val hv) := hT.ws _ hyW
        have hb := (h4 _ hyW).1
        simp only at hb
        refine ⟨by rw [hTy]; simp, payGood_val hc hTy, (fun h => by simp [hc] at h),
          fun f _ => (payload_val hTy f).trans ?_⟩
        rw [List.singleton_subperm_iff]
        refine List.mem_append_right _ (List.mem_range'_1.mpr ⟨hb.1, ?_⟩)
        show y' < acc.next + (acc1.next - acc.next)
        nomega
      | del k =>
        rw [h7 k hlop] at hy
        cases hy

/-- A long compare value's entry holds the next segment's keys with c in
front. -/
theorem d_entry_long {T : Tree} {c : Nat} (hc : isLong c = true) (y0 : Option NodeId) :
    entry (fun c y => klongList T true (L T) c y) c y0 =
      (Lo T y0).map (fun kv => (c :: kv.1, kv.2)) := by
  cases y0 with
  | none => rfl
  | some y => exact klongList_long T (L T) y hc

/-- **A long compare value's run**: the next segment's tree, by `TreeIH`. -/
theorem d_run_long {f g c : Nat} {ops : List Op} {y0 : Option NodeId}
    {acc acc1 : Acc} {res : Option NodeId}
    (hIH : TreeIH cf i s (f + 1)) (hs : SOk cf i s)
    (hfresh : ∀ z, acc.next ≤ z → s.obj z = none)
    (hops : ∀ op ∈ ops, keyOk cf op.key = true ∧ g < op.key.length) (hc : isLong c = true)
    (hroot : ∀ y, y0 = some y →
      Shaped cf s (g + 1) (htIn cf s y) y ∧ Good s y 0 none ∧ (R s y).Nodup)
    (hp : planTree cf i s f y0 (g + 1) (ops.filter (fun op => segAt g op == c)) acc =
      some (res, acc1)) :
    RunOk cf i s g (ops.filter (fun op => segAt g op == c)) y0 ⟨c, res, acc, acc1⟩ ∧
      acc.next ≤ acc1.next := by
  have hw : ∀ op ∈ ops, keyWf op.key = true := fun op hop => by
    have := (hops op hop).1
    simp only [keyOk, Bool.and_eq_true] at this
    exact this.1
  have hg : ∀ op ∈ ops, g < op.key.length := fun op hop => (hops op hop).2
  have hpre : SegPre cf i s (g + 1) y0 (ops.filter (fun op => segAt g op == c)) acc := by
    refine ⟨hs, hfresh, fun op hop => ⟨(hops op (mem_grp hop).1).1, ?_⟩, hroot⟩
    obtain ⟨hm1, hm2⟩ := mem_grp hop
    have he := endsAt_of_keyWf (hw op hm1) (hg op hm1)
    rw [hm2, hc] at he
    have := hg op hm1
    simp only [endsAt, Bool.not_true, beq_eq_false_iff_ne, ne_eq] at he
    omega
  obtain ⟨W, hW, hold, hTW⟩ := hIH f (Nat.lt_succ_self f) y0 (g + 1) _ acc res acc1 hpre hp
  refine ⟨⟨W, hW, hold, fun T hA => ?_⟩, hW.next⟩
  obtain ⟨hnode, hm⟩ := hTW T hA
  refine ⟨hnode, ?_, ?_⟩
  · show entry _ c res = _
    rw [d_entry_long hc y0, applyOps_cons_block hg]
    cases res with
    | none =>
      simp only at hm
      rw [hm]
      rfl
    | some y =>
      obtain ⟨⟨ht, hR⟩, _⟩ := hm
      show klongList T true (L T) c y = _
      rw [klongList_long T (L T) y hc, hR.keys]
  · intro y hy
    simp only at hy
    subst hy
    obtain ⟨⟨ht, hR⟩, m, hobj, hlive⟩ := hm
    obtain ⟨n, hn, hlev, _, hG, hH⟩ := shaped_obj hR.shaped
    rw [hobj] at hn
    obtain rfl : m = n := by injection hn with h1; injection h1
    have hnx := lev_next cf hG hH
    have hht : htIn cf T y = ht := by
      simp only [htIn, hobj, hlev]
      exact htOf_lev cf hH
    refine ⟨by rw [hobj]; simp, ⟨(fun h => by simp [hc] at h),
      fun _ => ⟨m, hobj, by omega, hlive, hR.good⟩⟩,
      fun _ => ⟨by rw [hht]; exact hR.shaped, hR.nok⟩,
      fun f hf => hR.reach f (by omega)⟩

/-- **applyGroups's runs**, with the old entries' premise for the compare
values to come only, and the entries of the other compare values kept. -/
theorem d_ag : ∀ (f g : Nat) (es0 : List (Nat × NodeId)) (cvs : List Nat)
    (ops : List Op) (acc : Acc) (es : List (Nat × NodeId)) (acc' : Acc),
    TreeIH cf i s f → SOk cf i s → (∀ z, acc.next ≤ z → s.obj z = none) →
    (∀ op ∈ ops, keyOk cf op.key = true ∧ g < op.key.length) →
    cvs.Nodup → (∀ c ∈ cvs, ∃ op ∈ ops, segAt g op = c) →
    (∀ c ∈ cvs, ∀ y0, es0.lookup c = some y0 → isLong c = true →
      Shaped cf s (g + 1) (htIn cf s y0) y0 ∧ Good s y0 0 none ∧ (R s y0).Nodup) →
    applyGroups cf i s f g es0 cvs ops acc = some (es, acc') →
    (∀ c, c ∉ cvs → es.lookup c = es0.lookup c) ∧
    ∃ runs : List Run, Chain acc runs acc' ∧ runs.map (·.c) = cvs ∧
      ∀ r ∈ runs, RunOk cf i s g (ops.filter (fun op => segAt g op == r.c))
        (es0.lookup r.c) r ∧ es.lookup r.c = r.res
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h => by simp [applyGroups] at h
  | f + 1, g, es0, [], ops, acc, es, acc', _, _, _, _, _, _, _, h => by
    simp only [applyGroups, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun _ _ => rfl, [], rfl, rfl, by simp⟩
  | f + 1, g, es0, cv :: cvs, ops, acc, es, acc', hIH, hs, hfresh, hops, hnd, hne, hroot, h => by
    have hIH' : TreeIH cf i s f := fun f' hf' => hIH f' (by omega)
    rw [List.nodup_cons] at hnd
    have hw : ∀ op ∈ ops, keyWf op.key = true := fun op hop => by
      have := (hops op hop).1
      simp only [keyOk, Bool.and_eq_true] at this
      exact this.1
    have hg : ∀ op ∈ ops, g < op.key.length := fun op hop => (hops op hop).2
    have fin : ∀ (es1 : List (Nat × NodeId)) (acc1 : Acc) (res : Option NodeId),
        RunOk cf i s g (ops.filter (fun op => segAt g op == cv)) (es0.lookup cv)
          ⟨cv, res, acc, acc1⟩ →
        acc.next ≤ acc1.next → (∀ a, a ≠ cv → es1.lookup a = es0.lookup a) →
        es1.lookup cv = res → applyGroups cf i s f g es1 cvs ops acc1 = some (es, acc') →
        (∀ c, c ∉ cv :: cvs → es.lookup c = es0.lookup c) ∧
        ∃ runs : List Run, Chain acc runs acc' ∧ runs.map (·.c) = cv :: cvs ∧
          ∀ r ∈ runs, RunOk cf i s g (ops.filter (fun op => segAt g op == r.c))
            (es0.lookup r.c) r ∧ es.lookup r.c = r.res := by
      intro es1 acc1 res hrun hnext hlk hres h2
      obtain ⟨hout, runs, hch, hmap, hruns⟩ := d_ag f g es1 cvs ops acc1 es acc' hIH' hs
        (fun z hz => hfresh z (by nomega)) hops hnd.2
        (fun c hc => hne c (List.mem_cons_of_mem _ hc))
        (fun c hc y0 hy0 hl => hroot c (List.mem_cons_of_mem _ hc) y0
          (by rw [← hlk c (fun h => hnd.1 (h ▸ hc))]; exact hy0) hl) h2
      refine ⟨fun a ha => ?_, ⟨cv, res, acc, acc1⟩ :: runs, ⟨rfl, hnext, hch⟩,
        by simp [hmap], ?_⟩
      · simp only [List.mem_cons, not_or] at ha
        rw [hout a ha.2, hlk a ha.1]
      · intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · exact ⟨hrun, by rw [hout cv hnd.1]; exact hres⟩
        · have hrc : r.c ∈ cvs := hmap ▸ List.mem_map_of_mem hr
          have hne' : r.c ≠ cv := fun h => hnd.1 (h ▸ hrc)
          obtain ⟨a1, a2⟩ := hruns r hr
          rw [hlk r.c hne'] at a1
          exact ⟨a1, a2⟩
    unfold applyGroups at h
    simp only at h
    generalize hq : List.foldl _ (es0, acc) _ = q at h
    obtain ⟨es1, acc1⟩ := q
    simp only at h
    cases hcl : isLong cv with
    | false =>
      rw [(grp_short hw hg hcl).1] at hq
      obtain ⟨hrun, hnext, hlk⟩ := d_run_short (y0 := es0.lookup cv) _ hq
        (by intro q k hv; rfl) (by intro q k; rfl) hfresh hops (hne cv List.mem_cons_self) hcl
      split at h
      · exact fin es1 acc1 _ hrun hnext hlk rfl h
      · rename_i hsub
        exfalso
        apply hsub
        rw [(grp_short hw hg hcl).2]
        rfl
    | true =>
      rw [(grp_long hw hg hcl).1, List.foldl_nil, Prod.mk.injEq] at hq
      obtain ⟨rfl, rfl⟩ := hq
      split at h
      · rename_i hsub
        exfalso
        rw [(grp_long hw hg hcl).2, List.isEmpty_iff] at hsub
        obtain ⟨op0, hop0, hc0⟩ := hne cv List.mem_cons_self
        have : op0 ∈ ops.filter (fun op => segAt g op == cv) :=
          List.mem_filter.mpr ⟨hop0, by simp [hc0]⟩
        rw [hsub] at this
        simp at this
      · split at h
        · cases h
        · rename_i y acc2 hp
          rw [(grp_long hw hg hcl).2] at hp
          obtain ⟨hrun, hnext⟩ := d_run_long hIH hs hfresh hops hcl
            (fun y hy => hroot cv List.mem_cons_self y hy hcl) hp
          exact fin _ acc2 (some y) hrun hnext
            (fun a ha => by rw [setEntry_lookup, ite_eq_right ha])
            (by rw [setEntry_lookup, ite_eq_left rfl]) h
        · rename_i acc2 hp
          rw [(grp_long hw hg hcl).2] at hp
          obtain ⟨hrun, hnext⟩ := d_run_long hIH hs hfresh hops hcl
            (fun y hy => hroot cv List.mem_cons_self y hy hcl) hp
          exact fin _ acc2 none hrun hnext
            (fun a ha => by rw [removeEntry_lookup, ite_eq_right ha])
            (by rw [removeEntry_lookup, ite_eq_left rfl]) h

/-- **applyGroups's runs**: one run for each compare value in cvs, in order,
each meeting `RunOk` with its group and its old entry, and giving the entry
the list ends with. -/
theorem ag_runs (_hcf : cf.Ok) : ∀ (f g : Nat) (es0 : List (Nat × NodeId)) (cvs : List Nat)
    (ops : List Op) (acc : Acc) (es : List (Nat × NodeId)) (acc' : Acc),
    TreeIH cf i s f → SOk cf i s → (∀ z, acc.next ≤ z → s.obj z = none) →
    (∀ op ∈ ops, keyOk cf op.key = true ∧ g < op.key.length) →
    cvs.Nodup → (∀ c ∈ cvs, ∃ op ∈ ops, segAt g op = c) →
    (∀ c y0, (c, y0) ∈ es0 → isLong c = true →
      Shaped cf s (g + 1) (htIn cf s y0) y0 ∧ Good s y0 0 none ∧ (R s y0).Nodup) →
    applyGroups cf i s f g es0 cvs ops acc = some (es, acc') →
    ∃ runs : List Run, Chain acc runs acc' ∧ runs.map (·.c) = cvs ∧
      ∀ r ∈ runs, RunOk cf i s g (ops.filter (fun op => segAt g op == r.c)) (es0.lookup r.c) r ∧
        es.lookup r.c = r.res := by
  intro f g es0 cvs ops acc es acc' hIH hs hfresh hops hnd hne hroot h
  obtain ⟨_, runs, hch, hmap, hr⟩ := d_ag f g es0 cvs ops acc es acc' hIH hs hfresh hops hnd hne
    (fun c _ y0 hy hl => hroot c y0 (Contract.PE.lookup_mem hy) hl) h
  exact ⟨runs, hch, hmap, hr⟩

/-! ## E. The segment's step -/

/-- The part of `RunOk` after its writes' `WOkV`, for the writes W. -/
def e_runW (cf : Cfg) (s : Tree) (g : Nat) (grp : List Op) (y0 : Option NodeId)
    (r : Run) (W : List (NodeId × Obj)) : Prop :=
  (∀ p ∈ W, ∀ o, s.obj p.1 = some o → ∃ n, o = .key n) ∧
    ∀ T, After s T W (Ro s y0) →
      (∀ p ∈ W, ∀ n, p.2 = .key n → nodeOk cf.params T n = true ∧ n.ks ≠ []) ∧
      entry (fun c y => klongList T true (L T) c y) r.c r.res =
        applyOps (grp.map (dropKey g)) (entry (fun c y => klongList s true (L s) c y) r.c y0) ∧
      ∀ y, r.res = some y → T.obj y ≠ none ∧ PayGood cf T g r.c y ∧
        (isLong r.c = true → Shaped cf T (g + 1) (htIn cf T y) y ∧ NOk cf.params T y) ∧
        ∀ f, cf.lev g 0 ≤ f → (reachAt T f y).Subperm
          (Ro s y0 ++ List.range' r.a.next (r.a'.next - r.a.next))

theorem e_subperm_nodup {α : Type} {l1 l2 : List α} (h : l1.Subperm l2) (hn : l2.Nodup) :
    l1.Nodup := by
  obtain ⟨l, hp, hs⟩ := h
  exact hp.nodup_iff.mp (hs.nodup hn)

theorem e_wokv_mono {U U' : List NodeId} {a a' : Acc} {W : List (NodeId × Obj)}
    (h : WOkV i s U a a' W) (hU : ∀ z ∈ U, z ∈ U') : WOkV i s U' a a' W where
  ws := h.ws
  next := h.next
  nodup := h.nodup
  ids w hw := (h.ids w hw).imp_right (hU w)
  times := h.times
  frame := h.frame

/-- After a part of the writes, for the old nodes no other write touches. -/
theorem e_after_sub {T : Tree} {W Wr : List (NodeId × Obj)} {U Ur : List NodeId}
    (hT : After s T W U) (hsub : ∀ p ∈ Wr, p ∈ W) (hU : ∀ z ∈ Ur, z ∈ U)
    (hown : ∀ p ∈ W, p.1 ∈ Ur → p ∈ Wr) : After s T Wr Ur where
  ws p hp := hT.ws p (hsub p hp)
  keep z hz hzW := hT.keep z (hU z hz) (by
    intro hzW'
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hzW'
    exact hzW (List.mem_map.mpr ⟨p, hown p hp hz, rfl⟩))
  exist := hT.exist

/-- The runs' compare values are distinct. -/
theorem e_runs_nodup {g h : Nat} {root : Option NodeId} {E : List (Nat × NodeId)}
    {ops : List Op} {v : VN} {runs : List Run} {acc0 acc1 : Acc}
    (hp : PlanSeg cf i s g root E ops h v runs acc0 acc1) : (runs.map (·.c)).Nodup :=
  hp.perm.nodup_iff.mpr (nodup_touched g ops)

/-- The planned leaf level at a run's compare value: the run's result. -/
theorem e_run_res {g h : Nat} {root : Option NodeId} {E : List (Nat × NodeId)}
    {ops : List Op} {v : VN} {runs : List Run} {acc0 acc1 : Acc}
    (hp : PlanSeg cf i s g root E ops h v runs acc0 acc1) {r : Run} (hr : r ∈ runs) :
    (content h (absV s h v)).lookup r.c = r.res := by
  obtain ⟨sops, hE', hcv, hsr⟩ := hp.sops
  rw [hE']
  have hnd : (sops.map Abs.Op.cv).Nodup := hcv ▸ nodup_touched g ops
  have hrc : r.c ∈ sops.map Abs.Op.cv := by
    rw [hcv]; exact hp.perm.subset (List.mem_map_of_mem hr)
  obtain ⟨o, ho, hoc⟩ := List.mem_map.mp hrc
  obtain ⟨r', hr', hrc', hor⟩ := hsr o ho
  have : r' = r := List.inj_on_of_nodup_map (e_runs_nodup hp) hr' hr (hrc'.trans hoc)
  subst this
  subst hor
  exact absApply_lookup_opOf sops E r'.c r'.res hnd ho

/-- The planned leaf level at an untouched compare value: the old one. -/
theorem e_out_res {g h : Nat} {root : Option NodeId} {E : List (Nat × NodeId)}
    {ops : List Op} {v : VN} {runs : List Run} {acc0 acc1 : Acc}
    (hp : PlanSeg cf i s g root E ops h v runs acc0 acc1) {c : Nat} (hc : c ∉ touched g ops) :
    (content h (absV s h v)).lookup c = E.lookup c := by
  obtain ⟨sops, hE', hcv, _⟩ := hp.sops
  rw [hE']
  exact absApply_lookup_out sops E c (by rw [hcv]; exact hc)

/-- A touched compare value is a run's. -/
theorem e_run_of_touched {g h : Nat} {root : Option NodeId} {E : List (Nat × NodeId)}
    {ops : List Op} {v : VN} {runs : List Run} {acc0 acc1 : Acc}
    (hp : PlanSeg cf i s g root E ops h v runs acc0 acc1) {c : Nat} (hc : c ∈ touched g ops) :
    ∃ r ∈ runs, r.c = c := by
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp (hp.perm.symm.subset hc)
  exact ⟨r, hr, rfl⟩

/-- Images of distinct elements under a map whose flatMap has distinct
nodes are disjoint. -/
theorem e_disj' {α β : Type} {l : List α} {F : α → List β} (hnd : (l.flatMap F).Nodup)
    {a b : α} (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) {z : β}
    (hza : z ∈ F a) (hzb : z ∈ F b) : False := by
  have hpw := (List.nodup_flatMap.mp hnd).2
  have : Std.Symm (Function.onFun List.Disjoint F) := ⟨fun _ _ h => h.symm⟩
  exact hpw.forall ha hb hab hza hzb

/-- The runs' old walks: distinct nodes of the old tree. -/
theorem e_walks {g : Nat} {root : Option NodeId} {E : List (Nat × NodeId)}
    (ho : OldSeg cf s g root E) {runs : List Run} (hnd : (runs.map (·.c)).Nodup) :
    (runs.flatMap (fun r => Ro s (E.lookup r.c))).Nodup ∧
      ∀ z ∈ runs.flatMap (fun r => Ro s (E.lookup r.c)), z ∈ Ro s root := by
  have hEnd : (E.flatMap (fun e => R s e.2)).Nodup := e_subperm_nodup ho.walks ho.nodup
  have hsub : ∀ r : Run, ∀ z ∈ Ro s (E.lookup r.c), ∃ y, (r.c, y) ∈ E ∧ z ∈ R s y := by
    intro r z hz
    cases hl : E.lookup r.c with
    | none => rw [hl] at hz; simp [Ro] at hz
    | some y => rw [hl] at hz; exact ⟨y, lookup_mem hl, hz⟩
  constructor
  · rw [List.nodup_flatMap]
    constructor
    · intro r _
      cases hl : E.lookup r.c with
      | none => simp [Ro]
      | some y =>
        simp only [Ro]
        exact (List.nodup_flatMap.mp hEnd).1 (r.c, y) (lookup_mem hl)
    · have hpw : runs.Pairwise (fun a b => a.c ≠ b.c) := List.pairwise_map.mp hnd
      refine hpw.imp ?_
      intro a b hab z hza hzb
      obtain ⟨ya, hya, hza⟩ := hsub a z hza
      obtain ⟨yb, hyb, hzb⟩ := hsub b z hzb
      exact e_disj' hEnd hya hyb (fun he => hab (Prod.mk.inj he).1) hza hzb
  · intro z hz
    obtain ⟨r, _, hz⟩ := List.mem_flatMap.mp hz
    obtain ⟨y, hy, hz⟩ := hsub r z hz
    exact ho.walks.subset (List.mem_flatMap.mpr ⟨(r.c, y), hy, hz⟩)

/-- What a segment leaf's old entry holds is in key order. -/
theorem e_blk_sorted {g : Nat} {root : Option NodeId} {E : List (Nat × NodeId)}
    (ho : OldSeg cf s g root E) : ∀ e ∈ E, (klongList s true (L s) e.1 e.2).Pairwise KvLt := by
  intro e he
  cases hl : isLong e.1 with
  | true =>
    obtain ⟨m, _, _, _, hgd⟩ := (ho.pay e he).1.2 hl
    exact klongList_sorted s (L s) e.1 e.2 hgd.sorted
  | false =>
    rcases klongList_short s (L s) e.2 hl with h | ⟨w, h⟩ <;> rw [h]
    · exact List.Pairwise.nil
    · exact List.pairwise_singleton _ _

/-- **The keys after**: the planned leaf level's blocks in T are the old
keys with the operations applied, if each run's block is and every untouched
old entry holds the same in T. -/
theorem e_keys {g h : Nat} {root : Option NodeId} {E : List (Nat × NodeId)}
    {ops : List Op} {v : VN} {runs : List Run} {acc0 acc1 : Acc} {T : Tree}
    (hops : ∀ op ∈ ops, keyOk cf op.key = true ∧ g < op.key.length)
    (ho : OldSeg cf s g root E) (hp : PlanSeg cf i s g root E ops h v runs acc0 acc1)
    (hrun : ∀ r ∈ runs, entry (fun c y => klongList T true (L T) c y) r.c r.res =
        applyOps ((ops.filter (fun op => segAt g op == r.c)).map (dropKey g))
          (entry (fun c y => klongList s true (L s) c y) r.c (E.lookup r.c)))
    (hsame : ∀ e ∈ E, e.1 ∉ touched g ops →
      klongList T true (L T) e.1 e.2 = klongList s true (L s) e.1 e.2)
    (hE' : CvSorted (content h (absV s h v))) :
    (content h (absV s h v)).flatMap (fun e => klongList T true (L T) e.1 e.2) =
      applyOps (ops.map (dropKey g)) (Lo s root) := by
  have hg : ∀ op ∈ ops, g < op.key.length := fun op hop => (hops op hop).2
  rw [ho.keys]
  have hft : firstCvs (ops.map (dropKey g)) = touched g ops := firstCvs_dropKey g ops
  refine applyOps_blocks (fun c y => klongList s true (L s) c y)
    (fun c y => klongList T true (L T) c y) E (content h (absV s h v)) (ops.map (dropKey g))
    ho.sorted hE' (fun e _ => klongList_head s (L s) e.1 e.2) (e_blk_sorted ho) ?_ ?_ ?_ ?_
  · intro op hop
    obtain ⟨op0, hop0, rfl⟩ := List.mem_map.mp hop
    rw [dropKey_key]
    intro hnil
    have := hg op0 hop0
    rw [List.drop_eq_nil_iff] at hnil
    omega
  · intro c hc
    rw [hft] at hc
    exact e_out_res hp hc
  · intro e he hc
    rw [hft] at hc
    exact hsame e he hc
  · intro c hc
    rw [hft] at hc
    obtain ⟨r, hr, rfl⟩ := e_run_of_touched hp hc
    rw [e_run_res hp hr, hrun r hr, filter_segAt_dropKey g r.c ops hg]

theorem e_wokv_unique {U U' : List NodeId} {a a' : Acc} {W1 W2 : List (NodeId × Obj)}
    (h1 : WOkV i s U a a' W1) (h2 : WOkV i s U' a a' W2) : W1 = W2 := by
  have := h1.ws.symm.trans h2.ws
  exact List.append_cancel_right this

/-- The runs' writes together, each run's facts in a tree after them and
other writes on none of its old nodes. -/
theorem e_runs_W {g h : Nat} {root : Option NodeId} {E : List (Nat × NodeId)}
    {ops : List Op} {v : VN} {runs : List Run} {acc0 acc1 : Acc}
    (hfresh : ∀ z, acc0.next ≤ z → s.obj z = none)
    (ho : OldSeg cf s g root E) (hp : PlanSeg cf i s g root E ops h v runs acc0 acc1) :
    ∃ W, WOkV i s (runs.flatMap (fun r => Ro s (E.lookup r.c))) acc0 acc1 W ∧
      (∀ r ∈ runs, ∃ Wr, WOkV i s (Ro s (E.lookup r.c)) r.a r.a' Wr ∧
        e_runW cf s g (ops.filter (fun op => segAt g op == r.c)) (E.lookup r.c) r Wr ∧
        (∀ p ∈ Wr, p ∈ W) ∧ ∀ p ∈ W, p.1 ∈ Ro s (E.lookup r.c) → p ∈ Wr) ∧
      (∀ p ∈ W, ∃ r ∈ runs, ∃ Wr, WOkV i s (Ro s (E.lookup r.c)) r.a r.a' Wr ∧
        e_runW cf s g (ops.filter (fun op => segAt g op == r.c)) (E.lookup r.c) r Wr ∧
        (∀ p ∈ Wr, p ∈ W) ∧ (∀ p ∈ W, p.1 ∈ Ro s (E.lookup r.c) → p ∈ Wr) ∧ p ∈ Wr) := by
  obtain ⟨hwnd, hwsub⟩ := e_walks ho (e_runs_nodup hp)
  obtain ⟨W, hW, hWmem, hWrun⟩ := runs_writes (i := i) (s := s)
    (fun r W => e_runW cf s g (ops.filter (fun op => segAt g op == r.c)) (E.lookup r.c) r W)
    (fun r => Ro s (E.lookup r.c)) runs acc0 acc1 hp.chain (fun r hr => hp.run r hr) hwnd
    (fun z hz => ho.exist z (hwsub z hz)) hfresh
  refine ⟨W, hW, hWrun, ?_⟩
  intro p hpW
  obtain ⟨r, hr, Wr, hWr, _, hpr⟩ := hWmem p hpW
  obtain ⟨Wr2, hWr2, hS2, hsub2, hown2⟩ := hWrun r hr
  rw [e_wokv_unique hWr hWr2] at hpr
  exact ⟨r, hr, Wr2, hWr2, hS2, hsub2, hown2, hpr⟩

/-- **No tree after**: a planned root that settles into no tree: its runs'
writes, and the keys after the operations are none. -/
theorem seg_none (hcf : cf.Ok) {f g h : Nat} {root : Option NodeId} {E : List (Nat × NodeId)}
    {ops : List Op} {v : VN} {runs : List Run} {acc0 acc1 : Acc} {space : Bool}
    (_hs : SOk cf i s) (hfresh : ∀ z, acc0.next ≤ z → s.obj z = none)
    (hops : ∀ op ∈ ops, keyOk cf op.key = true ∧ g < op.key.length)
    (ho : OldSeg cf s g root E) (hp : PlanSeg cf i s g root E ops h v runs acc0 acc1)
    (hset : settleRoot cf i s f g v space = some none) :
    TreeOk cf i s g root ops acc0 acc1 none := by
  have hE' : content h (absV s h v) = [] := settle_root_none hcf f g space h v (Or.inr hp.vok) hset
  have hres : ∀ r ∈ runs, r.res = none := fun r hr => by
    have := e_run_res hp hr; rw [hE'] at this; simpa using this.symm
  obtain ⟨_, hwsub⟩ := e_walks ho (e_runs_nodup hp)
  obtain ⟨W, hW, hWrun, hWmem⟩ := e_runs_W hfresh ho hp
  refine ⟨W, e_wokv_mono hW hwsub, ?_, ?_⟩
  · intro p hpW o hpo
    obtain ⟨r, _, Wr, _, hS, _, _, hpr⟩ := hWmem p hpW
    exact hS.1 p hpr o hpo
  · intro T hT
    refine ⟨?_, ?_⟩
    · intro p hpW n hpn
      obtain ⟨r, hr, Wr, _, hS, hsub, hown, hpr⟩ := hWmem p hpW
      have hTa : After s T Wr (Ro s (E.lookup r.c)) :=
        e_after_sub hT hsub (fun z hz => hwsub z (List.mem_flatMap.mpr ⟨r, hr, hz⟩)) hown
      exact (hS.2 T hTa).1 p hpr n hpn
    · have hk := e_keys (T := T) hops ho hp (fun r hr => by
          obtain ⟨Wr, _, hS, hsub, hown⟩ := hWrun r hr
          have hTa : After s T Wr (Ro s (E.lookup r.c)) :=
            e_after_sub hT hsub (fun z hz => hwsub z (List.mem_flatMap.mpr ⟨r, hr, hz⟩)) hown
          exact (hS.2 T hTa).2.1) (by
        intro e he hc
        exfalso
        have h1 := e_out_res hp hc
        rw [hE', lookup_of_mem ho.sorted he] at h1
        simp at h1) (by rw [hE']; exact List.Pairwise.nil)
      rw [← hk, hE']
      rfl


/-! ### The new root: helpers -/

/-- A run's fresh ids. -/
def e_rng (r : Run) : List NodeId := List.range' r.a.next (r.a'.next - r.a.next)

/-- The fresh ids of the run of a payload's compare value (none: none). -/
def e_RG (runs : List Run) (p : Nat × NodeId) : List NodeId :=
  (runs.filter (fun r => r.c == p.1)).flatMap e_rng

/-- Runs one after the other: each within the whole, each before the next. -/
theorem e_chain_bounds : ∀ {a a' : Acc} {runs : List Run}, Chain a runs a' →
    (∀ r ∈ runs, a.next ≤ r.a.next ∧ r.a.next ≤ r.a'.next ∧ r.a'.next ≤ a'.next) ∧
      runs.Pairwise (fun r1 r2 => r1.a'.next ≤ r2.a.next)
  | _, _, [], _ => ⟨by simp, List.Pairwise.nil⟩
  | a, a', r :: rs, h => by
    obtain ⟨e1, e2, e3⟩ := h
    obtain ⟨ih1, ih2⟩ := e_chain_bounds e3
    have hn := chain_next e3
    refine ⟨?_, List.Pairwise.cons ?_ ih2⟩
    · intro r' hr'
      rcases List.mem_cons.mp hr' with rfl | hr'
      · exact ⟨by rw [e1], e2, hn⟩
      · obtain ⟨b1, b2, b3⟩ := ih1 r' hr'
        exact ⟨by rw [← e1]; nomega, b2, b3⟩
    · intro r' hr'
      exact (ih1 r' hr').1

theorem e_rng_nodup {a a' : Acc} {runs : List Run} (hc : Chain a runs a') :
    (runs.flatMap e_rng).Nodup := by
  obtain ⟨_, hpw⟩ := e_chain_bounds hc
  rw [List.nodup_flatMap]
  refine ⟨fun r _ => List.nodup_range' _, hpw.imp ?_⟩
  intro r1 r2 h12 z hz1 hz2
  simp only [e_rng, List.mem_range'] at hz1 hz2
  obtain ⟨k1, hk1, rfl⟩ := hz1
  obtain ⟨k2, hk2, hk⟩ := hz2
  nomega

theorem e_filter_run : ∀ {runs : List Run}, (runs.map (·.c)).Nodup → ∀ {r : Run}, r ∈ runs →
    runs.filter (fun r' => r'.c == r.c) = [r]
  | [], _, _, hr => absurd hr (by simp)
  | r0 :: rest, hnd, r, hr => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hr with rfl | hr'
    · rw [List.filter_cons_of_pos (by simp), List.filter_eq_nil_iff.mpr]
      intro a ha hac
      exact hnd.1 (List.mem_map.mpr ⟨a, ha, by simpa using hac⟩)
    · have hne : r0.c ≠ r.c := fun he => hnd.1 (he ▸ List.mem_map_of_mem hr')
      rw [List.filter_cons_of_neg (by simpa using hne)]
      exact e_filter_run hnd.2 hr'

theorem e_RG_run {runs : List Run} (hnd : (runs.map (·.c)).Nodup) {r : Run} (hr : r ∈ runs)
    (y : NodeId) : e_RG runs (r.c, y) = e_rng r := by
  simp only [e_RG]
  rw [e_filter_run hnd hr]
  simp

theorem e_mem_RG {runs : List Run} {p : Nat × NodeId} {z : NodeId} (hz : z ∈ e_RG runs p) :
    ∃ r ∈ runs, r.c = p.1 ∧ z ∈ e_rng r := by
  obtain ⟨r, hr, hz⟩ := List.mem_flatMap.mp hz
  obtain ⟨hr, hc⟩ := List.mem_filter.mp hr
  exact ⟨r, hr, by simpa using hc, hz⟩

/-- The fresh ids of the payloads' runs: within the runs' range, each once. -/
theorem e_pays_RG {a a' : Acc} {runs : List Run} (hc : Chain a runs a')
    {P : List (Nat × NodeId)} (hP : P.Pairwise CvLtA) :
    (P.flatMap (e_RG runs)).Subperm (List.range' a.next (a'.next - a.next)) := by
  obtain ⟨hb, _⟩ := e_chain_bounds hc
  have hrn := e_rng_nodup hc
  apply List.Nodup.subperm
  · rw [List.nodup_flatMap]
    constructor
    · intro p _
      exact e_subperm_nodup (List.filter_sublist.flatMap e_rng).subperm hrn
    · refine hP.imp ?_
      intro p q hpq z hzp hzq
      obtain ⟨r1, hr1, hc1, hz1⟩ := e_mem_RG hzp
      obtain ⟨r2, hr2, hc2, hz2⟩ := e_mem_RG hzq
      refine e_disj' hrn hr1 hr2 ?_ hz1 hz2
      rintro rfl
      simp only [CvLtA] at hpq
      omega
  · intro z hz
    obtain ⟨p, _, hz⟩ := List.mem_flatMap.mp hz
    obtain ⟨r, hr, _, hz⟩ := e_mem_RG hz
    obtain ⟨b1, b2, b3⟩ := hb r hr
    simp only [e_rng, List.mem_range'] at hz ⊢
    obtain ⟨k, hk, rfl⟩ := hz
    exact ⟨r.a.next + k - a.next, by nomega, by nomega⟩

theorem e_oldPart (E : List (Nat × NodeId)) (p : Nat × NodeId) :
    oldPart s E p = Ro s (E.lookup p.1) := by
  unfold oldPart
  cases E.lookup p.1 <;> rfl

/-- The old tree's nodes and the fresh ids: each once. -/
theorem e_B_nodup {g : Nat} {root : Option NodeId} {E : List (Nat × NodeId)} {a : Nat}
    (ho : OldSeg cf s g root E) (hfresh : ∀ z, a ≤ z → s.obj z = none) (n : Nat) :
    (Ro s root ++ List.range' a n).Nodup := by
  rw [List.nodup_append]
  refine ⟨ho.nodup, List.nodup_range' _, ?_⟩
  intro x hx y hy hxy
  subst hxy
  obtain ⟨k, _, rfl⟩ := List.mem_range'.mp hy
  exact ho.exist _ hx (hfresh _ (by omega))

theorem e_content_sorted {h : Nat} {x : Node h} (hw : WFE h 0 none x) :
    (content h x).Pairwise CvLtA := by
  rcases hw with rfl | hw
  · cases h <;> exact List.Pairwise.nil
  · exact content_sorted h hw

/-- The planned root's bound: its old nodes and its payloads' old parts in
the old tree, the runs' fresh ids in the runs' range. -/
theorem e_hB {g h : Nat} {root : Option NodeId} {E : List (Nat × NodeId)}
    {ops : List Op} {v : VN} {runs : List Run} {acc0 acc1 : Acc}
    (hp : PlanSeg cf i s g root E ops h v runs acc0 acc1) (hP : (pays v).Pairwise CvLtA) :
    (Ui s v ++ (pays v).flatMap (fun p => oldPart s E p ++ e_RG runs p)).Subperm
      (Ro s root ++ List.range' acc0.next (acc1.next - acc0.next)) := by
  have h1 := (flatMap_append_perm (oldPart s E) (e_RG runs) (pays v)).append_left (Ui s v)
  refine h1.subperm.trans ?_
  rw [← List.append_assoc]
  exact hp.own.append (e_pays_RG hp.chain hP)

/-- A root settled is empty only as a segment leaf. -/
theorem e_empty_h0 (hcf : cf.Ok) {f g h' : Nat} {space : Bool} {h : Nat} {v v' : VN}
    (hv : VOk cf s g h v) (hs : settleRoot cf i s f g v space = some (some v'))
    (hv' : VOk cf s g h' v') (he : fin s h' v' = []) : h' = 0 := by
  rcases settle_shape hcf f g space h v v' hv hs with ⟨y, rfl⟩ | ⟨b, g', join, es, F, dec, rfl⟩ |
      ⟨b, g', h'', join, es, F, dec, rfl, hF⟩
  · exact absurd he (fin_ne hv' rfl)
  · exact (VOk.ht hv').1.symm
  · exfalso
    refine fin_ne hv' ?_ he
    simp only [VN.isEmpty, List.isEmpty_eq_false_iff]
    exact hF

/-- An empty node: what it reaches is itself. -/
theorem e_nok_empty {T : Tree} {x : NodeId} {n : KNode} (hobj : T.obj x = some (.key n))
    (hok : nodeOk cf.params T n = true) (hl : live n.ks = []) : NOk cf.params T x := by
  intro z hz m hm
  have hzx : z = x := by
    unfold R at hz
    cases hf : T.fuel x with
    | zero => rw [hf] at hz; simpa [reachAt] using hz
    | succ k => rw [hf] at hz; simpa [reachAt, hobj, hl] using hz
  subst hzx
  rw [hobj] at hm
  obtain rfl : n = m := by simpa using hm
  exact hok

theorem e_split_range (a0 a1 a2 : Nat) (h01 : a0 ≤ a1) (h12 : a1 ≤ a2) :
    List.range' a0 (a1 - a0) ++ List.range' a1 (a2 - a1) = List.range' a0 (a2 - a0) := by
  have := @List.range'_append a0 (a1 - a0) (a2 - a1) 1
  rw [show a0 + 1 * (a1 - a0) = a1 by omega, show a1 - a0 + (a2 - a1) = a2 - a0 by omega] at this
  exact this

/-- **The new root**: a planned root settled into v' and emitted as one node
r': the runs' and emit's writes, and in a tree after them r' holds the keys
after the operations. -/
theorem seg_some (hcf : cf.Ok) {f g h : Nat} {root : Option NodeId} {E : List (Nat × NodeId)}
    {ops : List Op} {v v' : VN} {runs : List Run} {acc0 acc1 acc2 : Acc} {space : Bool}
    {c0 r' : NodeId}
    (hs : SOk cf i s) (hfresh : ∀ z, acc0.next ≤ z → s.obj z = none)
    (hops : ∀ op ∈ ops, keyOk cf op.key = true ∧ g < op.key.length)
    (ho : OldSeg cf s g root E) (hp : PlanSeg cf i s g root E ops h v runs acc0 acc1)
    (hset : settleRoot cf i s f g v space = some (some v'))
    (he : emit cf i s v' acc1 = some ([(c0, r')], acc2)) :
    ∃ W, WOkV i s (Ro s root) acc0 acc2 W ∧ (∀ p ∈ W, ∀ o, s.obj p.1 = some o → ∃ n, o = .key n) ∧
      ∀ T, After s T W (Ro s root) →
        (∀ p ∈ W, ∀ n, p.2 = .key n → nodeOk cf.params T n = true ∧ n.ks ≠ []) ∧
        (∃ ht, RootIn cf T g ht r' (applyOps (ops.map (dropKey g)) (Lo s root))
          (Ro s root ++ List.range' acc0.next (acc2.next - acc0.next))) ∧
        (content h (absV s h v) ≠ [] → ∃ m, T.obj r' = some (.key m) ∧ live m.ks ≠ []) := by
  have hnd := e_runs_nodup hp
  have h01 : acc0.next ≤ acc1.next := chain_next hp.chain
  have hE's : (content h (absV s h v)).Pairwise CvLtA := e_content_sorted hp.wfe
  have hPs : (pays v).Pairwise CvLtA := hE's.sublist (pays_sublist h hp.vok)
  obtain ⟨h', hroot, hrok', heok', hB', hpv', hpin'⟩ :=
    settle_root_own hcf (Or.inr hp.vok) hp.eok (e_hB hp hPs) hset
  obtain ⟨_, _, hUi', _, _⟩ := settle_own f g space h v v' (fun _ => []) (Ui s v) hp.eok
    (by
      have : (pays v).flatMap (fun _ => ([] : List NodeId)) = [] :=
        List.flatMap_eq_nil_iff.mpr (fun _ _ => rfl)
      rw [this, List.append_nil]) hset
  have hUiv : ∀ z ∈ Ui s v', z ∈ Ui s v := fun z hz => hUi'.subset (List.mem_append_left _ hz)
  have hUiR : ∀ z ∈ Ui s v, z ∈ Ro s root := fun z hz => hp.own.subset (List.mem_append_left _ hz)
  have hvok' : VOk cf s g h' v' := settle_vok hcf hp.vok hset hrok'
  have hkeys' : content h' (fin s h' v') = content h (absV s h v) := Root.keys hroot
  have hwfe' : WFE h' 0 none (fin s h' v') := Root.wf hroot 0 hp.wfe
  have hBnd := e_B_nodup ho hfresh (acc1.next - acc0.next)
  have hUnd : (Ui s v').Nodup :=
    e_subperm_nodup ((List.sublist_append_left _ _).subperm.trans hB') hBnd
  have hfresh1 : ∀ x, acc1.next ≤ x → s.obj x = none := fun x hx => hfresh x (le_trans h01 hx)
  obtain ⟨We, hwse, hnexte, hnde, hidse, htimese, hframee, hshe, hTe⟩ :=
    emit_spec_w hcf hvok' heok' hs hfresh1 hUnd (wfe_inord hwfe') he
  obtain ⟨_, hwsub⟩ := e_walks ho hnd
  obtain ⟨Wr, hWr, hWrun, hWmem⟩ := e_runs_W hfresh ho hp
  have hEex : ∀ e ∈ E, ∀ z ∈ R s e.2, z ∈ Ro s root := fun e he z hz =>
    ho.walks.subset (List.mem_flatMap.mpr ⟨e, he, hz⟩)
  have hEnd : (E.flatMap (fun e => R s e.2)).Nodup := e_subperm_nodup ho.walks ho.nodup
  -- emit writes no node of an old entry's walk
  have hWe_old : ∀ p ∈ We, ∀ e ∈ E, p.1 ∉ R s e.2 := by
    intro p hpW e he hz
    have hex := ho.exist _ (hEex e he _ hz)
    obtain ⟨o, ho'⟩ := Option.ne_none_iff_exists'.mp hex
    obtain ⟨n, h'', rfl, hsh⟩ := hshe p hpW o ho'
    obtain ⟨n', hn', hlev, _⟩ := shaped_obj hsh
    rw [ho'] at hn'
    obtain rfl : n = n' := by simpa using hn'
    have hb := ho.below e he _ hz n ho'
    have hle : cf.lev g 0 ≤ cf.lev g h'' := by
      unfold Cfg.lev; exact Nat.add_le_add_left (Nat.zero_le h'') _
    omega
  -- a run writes no node of an untouched old entry's walk
  have hWr_old : ∀ p ∈ Wr, ∀ e ∈ E, e.1 ∉ touched g ops → p.1 ∉ R s e.2 := by
    intro p hpW e he hc hz
    have hex := ho.exist _ (hEex e he _ hz)
    rcases hWr.ids p.1 (List.mem_map_of_mem hpW) with ⟨hlo, _⟩ | hU
    · exact hex (hfresh _ hlo)
    · obtain ⟨r, hr, hzr⟩ := List.mem_flatMap.mp hU
      cases hl : E.lookup r.c with
      | none => rw [hl] at hzr; simp [Ro] at hzr
      | some y0 =>
        rw [hl] at hzr
        have hrc : r.c ∈ touched g ops := hp.perm.subset (List.mem_map_of_mem hr)
        refine e_disj' hEnd (lookup_mem hl) he ?_ hzr hz
        rintro rfl
        exact hc hrc
  -- the runs' writes on no node of Ui s v'
  have hWr_Ui : ∀ z ∈ Ui s v', z ∉ Wr.map (·.1) := by
    intro z hz h1
    rcases hWr.ids z h1 with ⟨hlo, _⟩ | hU
    · exact ho.exist z (hUiR z (hUiv z hz)) (hfresh z hlo)
    · obtain ⟨r, hr, hzr⟩ := List.mem_flatMap.mp hU
      cases hl : E.lookup r.c with
      | none => rw [hl] at hzr; simp [Ro] at hzr
      | some y0 => rw [hl] at hzr; exact hp.outUi r hr y0 hl z hzr (hUiv z hz)
  have hWall : WOkV i s (Ro s root) acc0 acc2 (We ++ Wr) := {
    ws := by rw [hwse, hWr.ws, List.append_assoc]
    next := le_trans h01 hnexte
    nodup := by
      rw [List.map_append, List.nodup_append]
      refine ⟨hnde, hWr.nodup, ?_⟩
      intro a ha b hb hab
      subst hab
      rcases hidse a ha with ⟨hlo, hhi⟩ | hUa
      · rcases hWr.ids a hb with ⟨hlo', hhi'⟩ | hUb
        · nomega
        · exact ho.exist a (hwsub a hUb) (hfresh a (le_trans h01 hlo))
      · exact hWr_Ui a hUa hb
    ids := by
      intro w hw
      rw [List.map_append, List.mem_append] at hw
      rcases hw with hw | hw
      · rcases hidse w hw with ⟨hlo, hhi⟩ | hU
        · exact Or.inl ⟨by nomega, hhi⟩
        · exact Or.inr (hUiR w (hUiv w hU))
      · rcases hWr.ids w hw with ⟨hlo, hhi⟩ | hU
        · exact Or.inl ⟨hlo, by nomega⟩
        · exact Or.inr (hwsub w hU)
    times := by
      intro p hp' n hpn
      rcases List.mem_append.mp hp' with hpe | hpr
      · obtain ⟨n', hn', ht⟩ := htimese p hpe
        rw [hpn] at hn'
        obtain rfl : n = n' := by simpa using hn'
        exact ht
      · exact hWr.times p hpr n hpn
    frame := by
      intro p hp' n hpn
      rcases List.mem_append.mp hp' with hpe | hpr
      · exact hframee p hpe n hpn
      · exact hWr.frame p hpr n hpn }
  refine ⟨We ++ Wr, hWall, ?_, ?_⟩
  · intro p hp' o hpo
    rcases List.mem_append.mp hp' with hpe | hpr
    · obtain ⟨n, _, hn, _⟩ := hshe p hpe o hpo
      exact ⟨n, hn⟩
    · obtain ⟨r, _, Wr', _, hS, _, _, hpr'⟩ := hWmem p hpr
      exact hS.1 p hpr' o hpo
  intro T hT
  -- each run's writes: the only ones on its old nodes
  have hAfter : ∀ r ∈ runs, ∀ Wr' : List (NodeId × Obj), (∀ p ∈ Wr', p ∈ Wr) →
      (∀ p ∈ Wr, p.1 ∈ Ro s (E.lookup r.c) → p ∈ Wr') → After s T Wr' (Ro s (E.lookup r.c)) := by
    intro r hr Wr' hsub hown
    refine e_after_sub hT (fun p hp' => List.mem_append_right _ (hsub p hp'))
      (fun z hz => hwsub z (List.mem_flatMap.mpr ⟨r, hr, hz⟩)) ?_
    intro p hpW hpz
    rcases List.mem_append.mp hpW with hpe | hpr
    · exfalso
      cases hl : E.lookup r.c with
      | none => rw [hl] at hpz; simp [Ro] at hpz
      | some y0 => rw [hl] at hpz; exact hWe_old p hpe (r.c, y0) (lookup_mem hl) hpz
    · exact hown p hpr hpz
  have hrunT : ∀ r ∈ runs, ∃ Wr' : List (NodeId × Obj),
      e_runW cf s g (ops.filter (fun op => segAt g op == r.c)) (E.lookup r.c) r Wr' ∧
        After s T Wr' (Ro s (E.lookup r.c)) := by
    intro r hr
    obtain ⟨Wr', _, hS, hsub, hown⟩ := hWrun r hr
    exact ⟨Wr', hS, hAfter r hr Wr' hsub hown⟩
  -- an untouched old entry's walk is as in s
  have hunt : ∀ e ∈ E, e.1 ∉ touched g ops → ∀ z ∈ R s e.2, T.obj z = s.obj z := by
    intro e he hc z hz
    refine hT.keep z (hEex e he z hz) ?_
    intro hzW
    obtain ⟨p, hpW, rfl⟩ := List.mem_map.mp hzW
    rcases List.mem_append.mp hpW with hpe | hpr
    · exact hWe_old p hpe e he hz
    · exact hWr_old p hpr e he hc hz
  -- the planned leaf level's payloads in T
  have hpayT : ∀ q ∈ content h (absV s h v), PayGood cf T g q.1 q.2 ∧
      (isLong q.1 = true → Shaped cf T (g + 1) (htIn cf T q.2) q.2 ∧ NOk cf.params T q.2) := by
    intro q hq
    have hlq : (content h (absV s h v)).lookup q.1 = some q.2 := Contract.PE.lookup_of_mem hE's hq
    by_cases hc : q.1 ∈ touched g ops
    · obtain ⟨r, hr, hrc⟩ := e_run_of_touched hp hc
      obtain ⟨Wr', hS, hA⟩ := hrunT r hr
      have hres : r.res = some q.2 := by rw [← e_run_res hp hr, hrc, hlq]
      obtain ⟨_, _, hy⟩ := hS.2 T hA
      obtain ⟨_, hpg, hlong, _⟩ := hy q.2 hres
      rw [hrc] at hpg hlong
      exact ⟨hpg, hlong⟩
    · have hqE : q ∈ E := by
        have := e_out_res hp hc
        rw [hlq] at this
        exact lookup_mem this.symm
      have hag := hunt q hqE hc
      obtain ⟨hpg, hsh⟩ := ho.pay q hqE
      have hht : htIn cf T q.2 = htIn cf s q.2 := by
        unfold htIn; rw [hag q.2 (mem_reachAt_self' s _ q.2)]
      exact ⟨payGood_transfer hpg hag, fun hl => ⟨hht ▸ shaped_transfer (hsh hl) hag,
        nok_transfer (fun x n hx => (hs x n hx).1) hT.exist hag⟩⟩
  -- emit's premise on the payloads
  have hPB : ∀ p ∈ pays v', T.obj p.2 ≠ none ∧ ∀ f, cf.lev g 0 ≤ f →
      (reachAt T f p.2).Subperm (oldPart s E p ++ e_RG runs p) := by
    intro p hp'
    have hq : p ∈ content h (absV s h v) := hkeys' ▸ hpin' p hp'
    have hlq := Contract.PE.lookup_of_mem hE's hq
    obtain ⟨c, y⟩ := p
    by_cases hc : c ∈ touched g ops
    · obtain ⟨r, hr, rfl⟩ := e_run_of_touched hp hc
      obtain ⟨Wr', hS, hA⟩ := hrunT r hr
      have hres : r.res = some y := by rw [← e_run_res hp hr]; exact hlq
      obtain ⟨_, _, hy⟩ := hS.2 T hA
      obtain ⟨hex, _, _, hreach⟩ := hy y hres
      refine ⟨hex, fun f hf => ?_⟩
      rw [e_oldPart, e_RG_run hnd hr]
      exact hreach f hf
    · have hpv : (c, y) ∈ pays v := hpv' _ hp'
      have hlE : E.lookup c = some y := hp.untouched _ hpv hc
      have hpE : (c, y) ∈ E := lookup_mem hlE
      have hag := hunt _ hpE hc
      have hsex : s.obj y ≠ none := ho.exist _ (hEex _ hpE y (mem_reachAt_self' s _ y))
      refine ⟨hT.exist _ hsex, fun f hf => ?_⟩
      have hop : oldPart s E (c, y) = R s y := by rw [e_oldPart]; simp only [hlE]; rfl
      rw [hop]
      refine List.Subperm.trans ?_ (List.sublist_append_left _ _).subperm
      cases hl : isLong c with
      | true =>
        obtain ⟨m, hm, hlev, _, hgd⟩ := (ho.pay _ hpE).1.2 hl
        rw [payload_old hgd hag f (by simp only [Tree.fuel, hm]; omega)]
      | false =>
        obtain ⟨w, hw⟩ := (ho.pay _ hpE).1.1 hl
        have hTw : T.obj y = some (.val w) := by rw [hag y (mem_reachAt_self' s _ y), hw]
        exact (payload_val hTw f).trans (List.singleton_subperm_iff.mpr (mem_reachAt_self' s _ y))
  have hkeep : ∀ z ∈ Ui s v', z ∉ We.map (·.1) → T.obj z = s.obj z := by
    intro z hz hzn
    refine hT.keep z (hUiR z (hUiv z hz)) ?_
    intro hzW
    rw [List.map_append, List.mem_append] at hzW
    rcases hzW with h1 | h1
    · exact hzn h1
    · exact hWr_Ui z hz h1
  obtain ⟨hcv, hholds, _, hreach, hnokW⟩ := hTe T (fun p => oldPart s E p ++ e_RG runs p)
    (fun p hp' => hT.ws p (List.mem_append_left _ hp')) hkeep hT.exist hPB
  -- the one entry emit gives
  have hfe : finEnts 0 v' (fin s h' v') = [(0, fin s h' v')] := by
    apply finEnts_single
    have := congrArg List.length hcv
    simpa [renameHead] using this.symm
  have hHo : Holds cf T g h' r' (fin s h' v') := by
    rw [hfe] at hholds
    exact hholds ((c0, r'), (0, fin s h' v')) (by simp)
  have hpayq : ∀ q ∈ content h' (fin s h' v'), PayGood cf T g q.1 q.2 :=
    fun q hq => (hpayT q (hkeys' ▸ hq)).1
  have hgood : Good T r' 0 none := good_of_holds_wfe hHo hwfe' hpayq
  have hL : L T r' = (content h' (fin s h' v')).flatMap (fun p => klongList T true (L T) p.1 p.2) :=
    L_of_holds_wfe hHo hwfe' hpayq
  have hkeysT : L T r' = applyOps (ops.map (dropKey g)) (Lo s root) := by
    rw [hL, hkeys']
    refine e_keys hops ho hp (fun r hr => ?_) (fun e he hc => ?_) hE's
    · obtain ⟨Wr', hS, hA⟩ := hrunT r hr
      exact (hS.2 T hA).2.1
    · have hag := hunt e he hc
      simp only [klongList, ite_true, L_transfer hag, hag e.2 (mem_reachAt_self' s _ e.2)]
  have hreachT : ∀ f, cf.lev g h' + 1 ≤ f → (reachAt T f r').Subperm
      (Ro s root ++ List.range' acc0.next (acc2.next - acc0.next)) := by
    intro f hf
    have := hreach f hf
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at this
    refine this.trans ?_
    rw [← e_split_range acc0.next acc1.next acc2.next h01 hnexte, ← List.append_assoc]
    exact hB'.append (List.Subperm.refl _)
  have hnokq : ∀ q ∈ content h' (fin s h' v'), PayGood cf T g q.1 q.2 ∧
      (isLong q.1 = true → NOk cf.params T q.2) :=
    fun q hq => ⟨(hpayT q (hkeys' ▸ hq)).1, fun hl => ((hpayT q (hkeys' ▸ hq)).2 hl).2⟩
  refine ⟨fun p hp' n hpn => ?_, ?_⟩
  · rcases List.mem_append.mp hp' with hpe | hpr
    · exact hnokW p hpe n hpn
    · obtain ⟨r, hr, Wr', _, hS, hsub, hown, hpr'⟩ := hWmem p hpr
      exact (hS.2 T (hAfter r hr Wr' hsub hown)).1 p hpr' n hpn
  by_cases hfin : fin s h' v' = []
  · obtain rfl := e_empty_h0 hcf hp.vok hset hvok' hfin
    have hE0 : content h (absV s h v) = [] := by rw [← hkeys', hfin]; rfl
    rw [hfin] at hHo
    cases hHo with
    | leaf hobj hleaf hlev hG hok hlive =>
      refine ⟨⟨0, ⟨Nat.zero_le _, Shaped.leaf hobj hleaf hlev hG (fun c y hm _ => by
          rw [hlive] at hm; nomatch hm), hgood, hkeysT, e_nok_empty hobj hok hlive,
          hreachT, fun m hm => Or.inl ?_⟩⟩, fun hne => absurd hE0 hne⟩
      rw [hobj] at hm
      obtain rfl : _ = m := by simpa using hm
      exact hleaf
  · have hWF : WF h' 0 none (fin s h' v') := hwfe'.resolve_left hfin
    obtain ⟨m, hm, _, hlivem⟩ := hHo.live_ne hfin
    obtain ⟨_, _, _, _, hHr⟩ := hHo.bounds
    refine ⟨⟨h', ⟨hHr, shaped_of_holds h' hHo hWF (fun q hq hl => ((hpayT q (hkeys' ▸ hq)).2 hl).1),
      hgood, hkeysT, nok_of_holds rfl h' hHo hWF hnokq, hreachT, fun m' hm' => Or.inr ?_⟩⟩,
      fun _ => ⟨m, hm, hlivem⟩⟩
    rw [hm] at hm'
    obtain rfl : m = m' := by simpa using hm'
    exact hlivem

/-! ## F. planTree and the space root -/

theorem f_ih_mono {F F' : Nat} (h : TreeIH cf i s F) (hle : F' ≤ F) : TreeIH cf i s F' :=
  fun f hf => h f (by omega)

/-- A segment leaf's long entries: shaped roots of the next segment, sound,
their walks without duplicates. -/
theorem f_long {g : Nat} {x : NodeId} {n : KNode} {lo : Nat} {hi : Option Nat}
    (hobj : s.obj x = some (.key n)) (hsh : Shaped cf s g 0 x) (hg : Good s x lo hi)
    (hnd : (R s x).Nodup) :
    ∀ c y0, (c, y0) ∈ live n.ks → isLong c = true →
      Shaped cf s (g + 1) (htIn cf s y0) y0 ∧ Good s y0 0 none ∧ (R s y0).Nodup := by
  intro c y0 hm hl
  obtain ⟨n', hobj', hleaf, _, _, hk⟩ := hsh.inv_leaf
  rw [hobj] at hobj'
  obtain rfl : n = n' := by injection hobj' with h1; injection h1
  refine ⟨hk c y0 hm hl, ?_, ?_⟩
  · cases hg with
    | mk _ _ _ n'' hobj'' _ _ _ _ _ hseg _ =>
      rw [hobj] at hobj''
      obtain rfl : n = n'' := by injection hobj'' with h1; injection h1
      exact hseg hleaf c y0 hm hl
  · rw [R_good hg hobj] at hnd
    have h2 := (List.nodup_cons.mp hnd).2
    exact h2.sublist (List.sublist_flatten_of_mem
      (List.mem_map_of_mem (f := fun cy : Nat × NodeId => R s cy.2) hm))

/-- `plan_runs`'s premise from `ag_runs` at every lower fuel. -/
theorem f_hAG (hcf : cf.Ok) {f g : Nat} (IH : TreeIH cf i s f) (hs : SOk cf i s) :
    ∀ f' < f, ∀ (x : NodeId) (n : KNode) (lo : Nat) (hi : Option Nat)
      (ops : List Contract.Op) (acc : Acc) (es : List (Nat × NodeId)) (acc' : Acc),
      s.obj x = some (.key n) → Shaped cf s g 0 x → Good s x lo hi → (R s x).Nodup →
      (∀ op ∈ ops, keyOk cf op.key = true ∧ g < op.key.length) →
      (∀ z, acc.next ≤ z → s.obj z = none) →
      applyGroups cf i s f' g (live n.ks) (touched g ops) ops acc = some (es, acc') →
      ∃ runs : List Run, Chain acc runs acc' ∧ runs.map (·.c) = touched g ops ∧
        ∀ r ∈ runs, (fun grp y0 r => RunOk cf i s g grp y0 r)
          (ops.filter (fun op => segAt g op == r.c)) ((live n.ks).lookup r.c) r ∧
          es.lookup r.c = r.res := by
  intro f' hf' x n lo hi ops acc es acc' hobj hsh hg hnd hq hfr hap
  exact ag_runs hcf f' g (live n.ks) (touched g ops) ops acc es acc'
    (f_ih_mono IH (by omega)) hs hfr hq (nodup_touched g ops) (fun c hc => mem_touched.mp hc)
    (f_long hobj hsh hg hnd) hap

/-- The old node read as an abstract node holds its keys (`Plan.keys`'s
premise): in order, or an empty leaf. -/
theorem f_holds : ∀ (h : Nat) {g : Nat} {x : NodeId} {lo : Nat} {hi : Option Nat},
    Shaped cf s g h x → Good s x lo hi → Abs.Holds h lo hi (view h s x)
  | 0, g, x, lo, hi, hsh, hg => by
    rcases (view_wfe 0 hg hsh).1 with he | hw
    · rw [he]; exact ⟨List.Pairwise.nil, by simp⟩
    · exact holds_of_WF 0 hw
  | h + 1, g, x, lo, hi, hsh, hg => by
    rcases (view_wfe (h + 1) hg hsh).1 with he | hw
    · exfalso
      obtain ⟨n, hobj, _, _, _, _, hhead, _⟩ := hsh.inv_inner
      refine (view_wfe (h + 1) hg hsh).2 n hobj ?_ he
      intro hl
      rw [hl] at hhead
      simp at hhead
    · exact holds_of_WF (h + 1) hw

/-- **The old root's plan**: the old tree's facts and the plan's. -/
theorem f_old (hcf : cf.Ok) {f g h : Nat} {r : NodeId} {ops : List Contract.Op} {acc acc1 : Acc}
    {v : VN} (IH : TreeIH cf i s f) (hpre : SegPre cf i s g (some r) ops acc)
    (hsh : Shaped cf s g h r) (hg : Good s r 0 none) (hnd : (R s r).Nodup)
    (hp : plan cf i s f r g h ops acc = some (v, acc1)) :
    ∃ runs, OldSeg cf s g (some r) (content h (view h s r)) ∧
      PlanSeg cf i s g (some r) (content h (view h s r)) ops h v runs acc acc1 := by
  obtain ⟨sops, runs, hplan, hcv, hvok, hch, hperm, hsops, hrun, hout⟩ :=
    plan_runs hcf (fun grp y0 r => RunOk cf i s g grp y0 r)
      (fun op => keyOk cf op.key = true ∧ g < op.key.length)
      (f_hAG hcf IH hpre.sok) r h ops acc v acc1 0 none hp hsh hg hnd hpre.ops hpre.fresh
  obtain ⟨heok, hown, _, hunt⟩ := plan_own hcf hp hsh hg
  have hwfe := (view_wfe h hg hsh).1
  have hopsB : ∀ op ∈ sops, 0 ≤ op.cv ∧ Below op.cv none :=
    fun _ _ => ⟨Nat.zero_le _, trivial⟩
  refine ⟨runs, ?_, ?_⟩
  · exact
      { sorted := view_sorted h hg hsh
        pay := view_pay h hg hsh
        nodup := hnd
        walks := ((content_walks h hsh hg).trans (List.tail_sublist _)).subperm
        exist := fun z hz => reach_exists _ hg z hz
        below := walk_below h hsh hg
        keys := view_L_pays h hg hsh }
  · exact
      { vok := hvok
        eok := heok
        sops := ⟨sops, Plan.keys h 0 none _ _ _ hplan (f_holds h hsh hg) hopsB, hcv, hsops⟩
        wfe := Plan.wf h 0 none _ _ _ hplan hwfe hopsB
        own := hown
        untouched := hunt
        chain := hch
        perm := hperm
        run := hrun
        outUi := hout }

/-- **No old root**: the new leaf's plan. -/
theorem f_new (hcf : cf.Ok) {f g : Nat} {ops : List Contract.Op} {acc acc1 : Acc} {v : VN}
    {es : List (Nat × NodeId)} (IH : TreeIH cf i s f) (hpre : SegPre cf i s g none ops acc)
    (hag : applyGroups cf i s f g [] ((ops.map (segAt g)).eraseDups) ops acc = some (es, acc1))
    (hmk : mkNode cf i s none g 0 false (es.map (fun e => (e.1, VN.old e.2))) = some v) :
    ∃ runs, OldSeg cf s g none [] ∧ PlanSeg cf i s g none [] ops 0 v runs acc acc1 := by
  obtain ⟨runs, hch, hmap, hrun⟩ := ag_runs hcf f g [] (touched g ops) ops acc es acc1 IH
    hpre.sok hpre.fresh hpre.ops (nodup_touched g ops) (fun c hc => mem_touched.mp hc)
    (by intro c y0 h; simp at h) hag
  obtain ⟨heok, hui, hpo, htch, _⟩ := plan_new_own hag hmk
  obtain ⟨⟨F, dec, rfl⟩, hvok⟩ := mkNode_leaf hcf hmk (by
    intro e he
    simp only [List.mem_map] at he
    obtain ⟨a, _, rfl⟩ := he
    exact ⟨_, rfl⟩)
  obtain ⟨hsorted, hlk⟩ := applyGroups_spec f g [] _ ops acc es acc1 hag List.Pairwise.nil
  have habs : absV s 0 (.node none g 0 false (es.map (fun e => (e.1, VN.old e.2))) F dec) = es := by
    show (es.map (fun e => (e.1, VN.old e.2))).map (fun e => (e.1, e.2.oid)) = es
    rw [List.map_map]
    conv_rhs => rw [← List.map_id es]
    apply List.map_congr_left
    intro e _
    rfl
  refine ⟨runs, ?_, ?_⟩
  · exact
      { sorted := List.Pairwise.nil
        pay := by simp
        nodup := List.nodup_nil
        walks := by simp [Ro]
        exist := by simp [Ro]
        below := by simp
        keys := rfl }
  · refine
      { vok := hvok
        eok := heok
        sops := ⟨finalOps (touched g ops) es, ?_, finalOps_cv _ _, ?_⟩
        wfe := ?_
        own := ?_
        untouched := fun p hp ht => absurd (htch p hp) ht
        chain := hch
        perm := by rw [hmap]
        run := fun r hr => (hrun r hr).1
        outUi := ?_ }
    · show absV s 0 _ = _
      rw [habs]
      exact (applyOps_finalOps (touched g ops) [] es List.Pairwise.nil hsorted
        (fun c hc => hlk c hc)).symm
    · intro o ho
      simp only [finalOps, List.mem_map] at ho
      obtain ⟨c, hc, rfl⟩ := ho
      rw [← hmap] at hc
      simp only [List.mem_map] at hc
      obtain ⟨r, hr, rfl⟩ := hc
      refine ⟨r, hr, ?_, ?_⟩
      · split <;> rfl
      · rw [(hrun r hr).2]
        cases r.res <;> rfl
    · rw [habs]
      by_cases he : es = []
      · exact Or.inl he
      · exact Or.inr ⟨he, hsorted, fun e _ => ⟨Nat.zero_le _, trivial⟩⟩
    · rw [hui, hpo]
      exact List.nil_subperm
    · intro r _ y0 hy0
      simp at hy0

/-- The tail of `planTree`: the planned root settled, and emitted. -/
theorem f_tail (hcf : cf.Ok) {f g h : Nat} {root : Option NodeId} {E : List (Nat × NodeId)}
    {ops : List Contract.Op} {v : VN} {runs : List Run} {acc0 acc1 acc' : Acc}
    {res : Option NodeId}
    (hpre : SegPre cf i s g root ops acc0)
    (ho : OldSeg cf s g root E) (hp : PlanSeg cf i s g root E ops h v runs acc0 acc1)
    (ht : (match settleRoot cf i s f g v false with
      | none => none
      | some none => some (none, acc1)
      | some (some v) =>
        match emit cf i s v acc1 with
        | some ([(_, y)], acc) => some (some y, acc)
        | _ => none) = some (res, acc')) :
    TreeOk cf i s g root ops acc0 acc' res := by
  split at ht
  · cases ht
  · rename_i hset
    simp only [Option.some.injEq, Prod.mk.injEq] at ht
    obtain ⟨rfl, rfl⟩ := ht
    exact seg_none hcf hpre.sok hpre.fresh hpre.ops ho hp hset
  · rename_i v' hset
    split at ht
    · rename_i c0 y acc2 he
      simp only [Option.some.injEq, Prod.mk.injEq] at ht
      obtain ⟨rfl, rfl⟩ := ht
      obtain ⟨W, h1, h2, h3⟩ := seg_some hcf hpre.sok hpre.fresh hpre.ops ho hp hset he
      refine ⟨W, h1, h2, fun T hT => ?_⟩
      obtain ⟨a1, a2, a3⟩ := h3 T hT
      exact ⟨a1, a2, a3 (settle_content hcf hp.vok hp.wfe hset)⟩
    · cases ht

/-- One step of the induction: `planTree` at fuel f + 1 from `TreeIH` at f. -/
theorem f_step (hcf : cf.Ok) {f : Nat} (IH : TreeIH cf i s f) :
    ∀ (root : Option NodeId) (g : Nat) (ops : List Op) (acc : Acc) (res : Option NodeId)
    (acc' : Acc), SegPre cf i s g root ops acc →
    planTree cf i s (f + 1) root g ops acc = some (res, acc') →
    TreeOk cf i s g root ops acc acc' res := by
  intro root g ops acc res acc' hpre hpt
  unfold planTree at hpt
  cases root with
  | some r =>
    cases hgk : getKey s r with
    | none => simp [hgk] at hpt
    | some n =>
      cases hplan : plan cf i s f r g (cf.htOf n.level) ops acc with
      | none => simp [hgk, hplan] at hpt
      | some p =>
        obtain ⟨v, acc1⟩ := p
        simp only [hgk, hplan] at hpt
        obtain ⟨hsh, hg, hnd⟩ := hpre.root r rfl
        have hht : htIn cf s r = cf.htOf n.level := by
          unfold htIn; rw [getKey_obj hgk]
        rw [hht] at hsh
        obtain ⟨runs, ho, hp⟩ := f_old hcf IH hpre hsh hg hnd hplan
        exact f_tail hcf hpre ho hp hpt
  | none =>
    cases hag : applyGroups cf i s f g [] ((ops.map (segAt g)).eraseDups) ops acc with
    | none => simp [hag] at hpt
    | some p =>
      obtain ⟨es, acc1⟩ := p
      cases hmk : mkNode cf i s none g 0 false (es.map (fun e => (e.1, VN.old e.2))) with
      | none => simp [hag, hmk] at hpt
      | some v =>
        simp only [hag, hmk, Option.map_some] at hpt
        obtain ⟨runs, ho, hp⟩ := f_new hcf IH hpre hag hmk
        exact f_tail hcf hpre ho hp hpt

/-- `planTree`'s result at every fuel. -/
theorem f_all (hcf : cf.Ok) : ∀ F, TreeIH cf i s F := by
  intro F
  induction F with
  | zero => intro f hf; omega
  | succ F IH =>
    intro f hf root g ops acc res acc' hpre hpt
    rcases Nat.lt_succ_iff_lt_or_eq.mp hf with hlt | rfl
    · exact IH f hlt root g ops acc res acc' hpre hpt
    · cases f with
      | zero => simp [planTree] at hpt
      | succ f =>
        exact f_step hcf (f_ih_mono IH (by omega)) root g ops acc res acc' hpre hpt

/-- **planTree's result**, for every fuel. -/
theorem planTree_ok (hcf : cf.Ok) : ∀ (f : Nat) (root : Option NodeId) (g : Nat) (ops : List Op)
    (acc : Acc) (res : Option NodeId) (acc' : Acc), SegPre cf i s g root ops acc →
    planTree cf i s f root g ops acc = some (res, acc') → TreeOk cf i s g root ops acc acc' res :=
  fun f => f_all hcf (f + 1) f (Nat.lt_succ_self f)

/-- **The space root's step**: the space root planned, settled as the space
root, and emitted as one node. -/
theorem seg_space (hcf : cf.Ok) {f : Nat} {r : NodeId} {ops : List Op} {acc0 acc1 acc2 : Acc}
    {v v' : VN} {c0 r' : NodeId}
    (hpre : SegPre cf i s 0 (some r) ops acc0)
    (hp : plan cf i s f r 0 (htIn cf s r) ops acc0 = some (v, acc1))
    (hsr : settleRoot cf i s f 0 v true = some (some v'))
    (he : emit cf i s v' acc1 = some ([(c0, r')], acc2)) :
    ∃ W, WOkV i s (R s r) acc0 acc2 W ∧ (∀ p ∈ W, ∀ o, s.obj p.1 = some o → ∃ n, o = .key n) ∧
      ∀ T, After s T W (R s r) →
        (∀ p ∈ W, ∀ n, p.2 = .key n → nodeOk cf.params T n = true ∧ n.ks ≠ []) ∧
        ∃ ht, RootIn cf T 0 ht r' (applyOps (ops.map (dropKey 0)) (L s r))
          (R s r ++ List.range' acc0.next (acc2.next - acc0.next)) := by
  obtain ⟨hsh, hg, hnd⟩ := hpre.root r rfl
  obtain ⟨runs, ho, hpl⟩ := f_old hcf (f_all hcf f) hpre hsh hg hnd hp
  obtain ⟨W, h1, h2, h3⟩ := seg_some hcf hpre.sok hpre.fresh hpre.ops ho hpl hsr he
  exact ⟨W, h1, h2, fun T hT => ⟨(h3 T hT).1, (h3 T hT).2.1⟩⟩

end Contract.PE
