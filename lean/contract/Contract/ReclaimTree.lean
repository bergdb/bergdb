/-
The contract package (bergdb 030-24): RC2 and RC3, the two conditions of
reclaim's contract RC that are about the tree, for BergDB's key tree
(bergdb 030-22, sections 4.1 and 4.2).

RC3, a value below every index node a read at the iteration's end e reaches,
follows from the writer's contract (`rc3_tree`): the contract's invariants say
that every key node a live klong names has a live klong, and that a segment
leaf's live klong names a value or a non-empty key node; so, if some key is
live at e (reclaim's last step puts its row), every key node a read at e
reaches has a value below it, and so has the top node of time e. As in the
writer's contract, a tree after transaction j is read at time j
(`(h.tree j).at j`).

RC2, every value that a read at e reaches made at the cut c or later, is
stated in the contract's words (`RC2Tree`: the value node that each live key
names at e was made by a transaction from c on), carried to the model
(`rc2_of_tree`), and follows from the iteration (`rc2_of_iteration`):
`IterationOK`, every key live before the iteration's first step s whose value
node was made before c is put again by a transaction from s to e, and VAL-NEW
(`ValNew`, 030-22, section 2.3), a put makes a new value node that the key
names, and a key that a transaction does not write keeps its value node.
That Java's iteration meets `IterationOK` is tested (C-CUT's RC2 at every
cut; 027-13, section 3, REWRITES); VAL-NEW is the writer's.
-/
import Contract.ReclaimReads
import Contract.Proof.ReclaimTree
import Contract.Proof.PeSim

namespace Contract

open SIS.Check (BVal)

/-! ## The value nodes of the live keys -/

/-- What the live klong (c, y) of a key node holds, with value nodes by id:
as `klongList`, the key with the id of the value node its klong names. -/
def idKlongList (s : Tree) (leaf : Bool) (sub : NodeId → List (Key × NodeId)) (c : Nat)
    (y : NodeId) : List (Key × NodeId) :=
  if leaf then
    if isLong c then (sub y).map (fun ky => (c :: ky.1, ky.2))
    else
      match s.obj y with
      | some (.val _) => [([c], y)]
      | _ => []
  else sub y

/-- What key node x holds, with value nodes by id: as `listAt`. -/
def idListAt (s : Tree) : Nat → NodeId → List (Key × NodeId)
  | 0, _ => []
  | f + 1, x =>
    match s.obj x with
    | some (.key n) =>
      (live n.ks).flatMap (fun cy => idKlongList s n.leaf (fun y => idListAt s f y) cy.1 cy.2)
    | _ => []

/-- The live keys of a tree with the value nodes their klongs name: as
`contents`, by id instead of by value. -/
def idContents (s : Tree) : List (Key × NodeId) :=
  match s.root with
  | some r => idListAt s (s.fuel r) r
  | none => []

/-- A value that the walk from a sound key node reaches is named by a live key
of what the node holds, by id. -/
theorem Good.mem_idListAt {s : Tree} : ∀ (f : Nat) {x : NodeId} {lo : Nat} {hi : Option Nat}
    {n : KNode}, Good s x lo hi → s.obj x = some (.key n) → n.level < f →
    ∀ v w, v ∈ reachAt s f x → s.obj v = some (.val w) → ∃ k, (k, v) ∈ idListAt s f x
  | 0, _, _, _, _, _, _, hf, _, _, _, _ => absurd hf (Nat.not_lt_zero _)
  | f + 1, x, lo, hi, n, hg, hobj, hf, v, w, hv, hvw => by
    simp only [reachAt, hobj, List.mem_cons, List.mem_flatMap] at hv
    rcases hv with rfl | ⟨⟨c, y⟩, hm, hvy⟩
    · rw [hobj] at hvw; cases hvw
    · simp only [idListAt, hobj, List.mem_flatMap]
      by_cases hk : n.leaf = true → isLong c = true
      · obtain ⟨m, lo', hi', hm1, hm2, _, hgy⟩ := hg.child hobj hm hk
        obtain ⟨k, hk'⟩ := Good.mem_idListAt f hgy hm1 (by omega) v w hvy hvw
        cases hl : n.leaf with
        | false =>
          exact ⟨k, (c, y), hm, by
            simp only [idKlongList, Bool.false_eq_true, ite_false]; exact hk'⟩
        | true =>
          refine ⟨c :: k, (c, y), hm, ?_⟩
          simp only [idKlongList, hk hl, ite_true, List.mem_map, Prod.mk.injEq]
          exact ⟨(k, v), hk', rfl, rfl⟩
      · have hl : n.leaf = true := by
          by_contra hl
          exact hk (fun h => absurd h hl)
        have hs : isLong c = false := by
          cases hc : isLong c with
          | false => rfl
          | true => exact absurd (fun _ => hc) hk
        cases hg with
        | mk _ _ _ n' hobj' _ _ _ hval _ _ _ =>
          rw [hobj] at hobj'
          obtain rfl : n = n' := by injection hobj' with h1; injection h1
          obtain ⟨w', hw'⟩ := hval hl c y hm hs
          have hvy' : v = y := by
            cases f with
            | zero => simpa [reachAt] using hvy
            | succ f =>
              simp only [reachAt, hw', List.mem_cons] at hvy
              rcases hvy with h | h
              · exact h
              · simp at h
          subst hvy'
          refine ⟨[c], (c, v), hm, ?_⟩
          simp [idKlongList, hl, hs, hw']

/-- Transaction i of the history made node y (the trace's NEW lines; 0 is the
start's change). -/
def madeAt (h : BHist) (i : Nat) (y : NodeId) : Bool :=
  ((h.chs.getD i { new := [], adds := [] }).new.any (·.id == y))

/-- The keys a transaction puts. -/
def putKeys (ops : List Op) : List Key :=
  ops.filterMap (fun op => match op with
    | .put k _ => some k
    | .del _ => none)

/-! ## RC3 -/

/-- **RC3 for BergDB's key tree** (bergdb 030-24; 030-22, section 4.1): if some
key is live after transaction e, every written index node that a read at e
reaches has a value below it then. -/
theorem rc3_tree {p : Params} {h : BHist} {top : Nat → Top} (hm : MeetsFull p h top)
    (hM : 1 ≤ p.M) (al : SIS.Algo BVal Nat) {e : Nat} (he : e ≤ h.txs.length)
    (hne : contents ((h.tree e).at e) ≠ []) :
    RC3 h.spec (SIS.run h.spec al (h.ts.take e)) e := by
  have hi := hm.meetsBridge.binv e he
  obtain ⟨n0, z, nz, y, ny, h0, hl0, hz, hlz, hly, hroot, hy, hny, -, -⟩ := hi.link
  obtain ⟨n, hn, hgr, hne'⟩ := hm.root_good hM he hroot
  rw [hy] at hn
  obtain rfl : ny = n := by injection hn with h1; injection h1
  rw [hi.timely.at_eq] at hne
  have hner := hne' hne
  -- Below a sound key node with a live klong, the model reaches a data node.
  have hval : ∀ x m lo' hi', (h.tree e).obj x = some (.key m) → live m.ks ≠ [] →
      Good (h.tree e) x lo' hi' → ∃ d M,
        d ∈ SIS.reachFrom h.spec (h.P e) e x
          { level := m.level, isData := false, hist := entriesOf m.ks } ∧
        (h.P e).get? d = some M ∧ M.isData = true := by
    intro x m lo' hi' hxm hm hg
    obtain ⟨v, w, hv, hvr⟩ := hg.val_below (m.level + 1) hxm hm (by omega)
    obtain ⟨hP, -⟩ := hi.key_live hxm
    have hrv := hi.rep.rep v (.val w) hv
    obtain ⟨t, ht⟩ := hrv
    exact ⟨v, _, hi.walk_reachFrom _ x _ hP v hvr, ht, rfl⟩
  unfold RC3
  rw [run_P h al e he]
  intro x nx hx hnd hw hr
  rcases hi.reach3 h0 hl0 hz hly hroot hy ((SIS.reachable_iff _ _ _ _).mp hr) with
    rfl | rfl | hxr
  · -- The root is not written.
    simp [SIS.written, BHist.spec, SIS.Check.bspec] at hw
  · -- The top node: the space root is below it.
    rw [hz] at hx
    injection hx with hx
    subst hx
    obtain ⟨d, M, hd, hM', hMd⟩ := hval y ny 0 none hy hner hgr
    obtain ⟨hPy, -⟩ := hi.key_live hy
    exact ⟨d, M, SIS.reachFrom_child_sub h.spec (by rw [hly]; exact List.mem_singleton_self y)
      hPy hny d hd, hM', hMd⟩
  · -- A node of the tree.
    unfold reach at hxr
    rw [hroot] at hxr
    rcases hgr.reach_cases _ x hxr with rfl | ⟨w, hw'⟩ | ⟨m, lo', hi', hxm, hm, hg⟩
    · obtain ⟨hPy, -⟩ := hi.key_live hy
      rw [hPy] at hx
      injection hx with hx
      subst hx
      exact hval x ny 0 none hy hner hgr
    · have hrx := hi.rep.rep x (.val w) hw'
      obtain ⟨t, ht⟩ := hrx
      rw [ht] at hx
      injection hx with hx
      subst hx
      simp at hnd
    · obtain ⟨hPx, -⟩ := hi.key_live hxm
      rw [hPx] at hx
      injection hx with hx
      subst hx
      exact hval x m lo' hi' hxm hm hg

/-! ## RC2 -/

/-- **RC2 in the contract's words**: every value node that a live key names
after transaction e was made by a transaction from c to e. -/
def RC2Tree (h : BHist) (c e : Nat) : Prop :=
  ∀ k y, (k, y) ∈ idContents ((h.tree e).at e) → ∃ i, c ≤ i ∧ i ≤ e ∧ madeAt h i y = true

/-- RC2 in the contract's words gives the model's RC2. -/
theorem rc2_of_tree {p : Params} {h : BHist} {top : Nat → Top} (hm : MeetsFull p h top)
    (hM : 1 ≤ p.M) (al : SIS.Algo BVal Nat) {c e : Nat} (he : e ≤ h.txs.length)
    (h2 : RC2Tree h c e) :
    RC2 h.spec (SIS.run h.spec al (h.ts.take e)) e c := by
  have hb := hm.meetsBridge
  obtain ⟨hi, ti⟩ := hm.meetsBridgeTop.inv e he
  intro d m hd hmd hr
  rw [run_P h al e he] at hd hr
  obtain ⟨n0, z, nz, y, ny, h0, hl0, hz, hlz, hly, hroot, hy, hny, -, -⟩ := hi.link
  obtain ⟨n, hn, hgr, -⟩ := hm.root_good hM he hroot
  rw [hy] at hn
  obtain rfl : ny = n := by injection hn with h1; injection h1
  -- d is a value of the tree.
  obtain ⟨w, hw⟩ : ∃ w, (h.tree e).obj d = some (.val w) := by
    cases ho : (h.tree e).obj d with
    | none =>
      exfalso
      rcases ti.other d m hd ho with rfl | ⟨tn, htn⟩
      · rw [ti.rootNode] at hd
        injection hd with hd
        rw [← hd] at hmd
        cases hmd
      · rw [(ti.topNode _ htn).1] at hd
        injection hd with hd
        rw [← hd] at hmd
        cases hmd
    | some o =>
      cases o with
      | val w => exact ⟨w, rfl⟩
      | key kn =>
        exfalso
        have := hi.rep.rep d _ ho
        simp only at this
        rw [this] at hd
        injection hd with hd
        rw [← hd] at hmd
        cases hmd
  -- So the walk reaches it, and a live key names it.
  have hreach : d ∈ reach (h.tree e) := by
    rcases hi.model_reach_cases hr with rfl | h1 | h1
    · rw [ti.s0] at hw; cases hw
    · rw [hw] at h1; cases h1
    · exact h1
  unfold reach at hreach
  rw [hroot] at hreach
  have hfuel : (h.tree e).fuel y = ny.level + 1 := by simp [Tree.fuel, hy]
  obtain ⟨k, hk⟩ := Good.mem_idListAt _ hgr hy (by rw [hfuel]; omega) d w hreach hw
  have hk' : (k, d) ∈ idContents ((h.tree e).at e) := by
    rw [hi.timely.at_eq]
    unfold idContents
    rw [hroot]
    exact hk
  obtain ⟨i, hci, hie, hmade⟩ := h2 k d hk'
  cases i with
  | zero =>
    -- The start makes no data node.
    exfalso
    have hd0 : d ∈ h.c0.new.map (·.id) := by
      simp only [madeAt, BHist.chs, Array.getD_eq_getD_getElem?,
        List.getElem?_toArray, List.getElem?_cons_zero, Option.getD_some, List.any_eq_true,
        beq_iff_eq] at hmade
      obtain ⟨nn, hnn, hid⟩ := hmade
      exact List.mem_map.mpr ⟨nn, hnn, hid⟩
    obtain ⟨nn, hnn, hid⟩ := List.mem_map.mp hd0
    have h0d : ((h.P 0).get? d).isSome = true := by
      change ((SIS.Struct.apply [] 0 h.c0).get? d).isSome = true
      rw [SIS.get?_apply]
      simp only [SIS.Struct.get?, List.lookup_nil, Option.none_or, Option.isSome_map]
      unfold SIS.newNodeOf
      simp only [SIS.Struct.get?, List.lookup_isSome_iff, List.mem_map]
      exact ⟨_, ⟨nn, hnn, rfl⟩, by simp [hid]⟩
    obtain ⟨n1, hn1⟩ := Option.isSome_iff_exists.mp h0d
    obtain ⟨n2, hn2, hd2⟩ := h.P_isData hn1 e (Nat.zero_le _) he
    rw [hd, Option.some.injEq] at hn2
    subst hn2
    rw [hd2, hm.start.p0_index hn1] at hmd
    cases hmd
  | succ j =>
    have hj : j < h.txs.length := by omega
    have hd' : d ∈ h.txs[j].c.new.map (·.id) := by
      have : (h.chs.getD (j + 1) { new := [], adds := [] }) = h.txs[j].c := by
        simp [BHist.chs, hj]
      simp only [madeAt, this, List.any_eq_true, beq_iff_eq] at hmade
      obtain ⟨nn, hnn, hid⟩ := hmade
      exact List.mem_map.mpr ⟨nn, hnn, hid⟩
    obtain ⟨u, hu, hle⟩ := hb.data_version al hj hie he hd' hd hmd
    exact ⟨u, hu, by omega⟩

/-- **VAL-NEW** (bergdb 030-22, section 2.3): in each transaction, a put makes
a new value node, which the key names after it, and a key that the
transaction does not write keeps its value node. -/
def ValNew (h : BHist) : Prop :=
  ∀ j (hj : j < h.txs.length), ∀ k,
    (k ∈ putKeys h.txs[j].ops →
      ∃ y, (idContents ((h.tree (j + 1)).at (j + 1))).lookup k = some y ∧
        madeAt h (j + 1) y = true) ∧
    (k ∉ h.txs[j].ops.map Op.key →
      (idContents ((h.tree (j + 1)).at (j + 1))).lookup k =
        (idContents ((h.tree j).at j)).lookup k)

/-- **Reclaim's iteration** in the contract's words (bergdb 030-22, section
4.2), with its cut c, its first step s and its last step e: c ≤ s ≤ e, and
every key live before s whose value node was made before c is written (put
again, or deleted) by a transaction from s to e: a step rewrites it, or the
user wrote it first. -/
def IterationOK (h : BHist) (c s e : Nat) : Prop :=
  c ≤ s ∧ 1 ≤ s ∧ s ≤ e ∧ e ≤ h.txs.length ∧
  ∀ k y, (idContents ((h.tree (s - 1)).at (s - 1))).lookup k = some y →
    (∃ i, i < c ∧ madeAt h i y = true) →
    ∃ j, ∃ hj : j < h.txs.length, s ≤ j + 1 ∧ j + 1 ≤ e ∧ k ∈ h.txs[j].ops.map Op.key

/-! ### Lemmas for RC2 from the iteration -/

/-- The keys of what a node holds by id are those of what it holds. -/
theorem idListAt_keys (s : Tree) : ∀ (f : Nat) (x : NodeId),
    (idListAt s f x).map Prod.fst = (listAt s f x).map Prod.fst
  | 0, _ => rfl
  | f + 1, x => by
    simp only [idListAt, listAt]
    cases s.obj x with
    | none => rfl
    | some o =>
      cases o with
      | val _ => rfl
      | key n =>
        simp only [List.map_flatMap]
        apply List.flatMap_congr
        rintro ⟨c, y⟩ _
        unfold idKlongList klongList
        cases n.leaf with
        | false =>
          simp only [Bool.false_eq_true, ite_false]
          exact idListAt_keys s f y
        | true =>
          cases isLong c with
          | true =>
            simp only [ite_true, List.map_map]
            have := congrArg (List.map (fun k => c :: k)) (idListAt_keys s f y)
            simpa [List.map_map, Function.comp_def] using this
          | false =>
            simp only [ite_true, Bool.false_eq_true, ite_false]
            cases s.obj y with
            | none => rfl
            | some o => cases o <;> rfl

/-- The keys of the contents by id are those of the contents. -/
theorem idContents_keys (s : Tree) : (idContents s).map Prod.fst = (contents s).map Prod.fst := by
  unfold idContents contents
  cases s.root with
  | none => rfl
  | some r => exact idListAt_keys s _ r

/-- A live key's node, by id, is a value. -/
theorem idListAt_val (s : Tree) : ∀ (f : Nat) (x : NodeId) (k : Key) (y : NodeId),
    (k, y) ∈ idListAt s f x → ∃ w, s.obj y = some (.val w)
  | 0, _, _, _, h => by simp [idListAt] at h
  | f + 1, x, k, y, h => by
    simp only [idListAt] at h
    cases hx : s.obj x with
    | none => rw [hx] at h; simp at h
    | some o =>
      rw [hx] at h
      cases o with
      | val _ => simp at h
      | key n =>
        simp only [List.mem_flatMap] at h
        obtain ⟨⟨c, z⟩, _, hz⟩ := h
        unfold idKlongList at hz
        cases hl : n.leaf with
        | false =>
          simp only [hl, Bool.false_eq_true, ite_false] at hz
          exact idListAt_val s f z k y hz
        | true =>
          cases hc : isLong c with
          | true =>
            simp only [hl, hc, ite_true, List.mem_map] at hz
            obtain ⟨⟨k', y'⟩, hk', heq⟩ := hz
            injection heq with _ h2
            subst h2
            exact idListAt_val s f z k' y' hk'
          | false =>
            simp only [hl, hc, ite_true, Bool.false_eq_true, ite_false] at hz
            split at hz
            · rename_i w hw
              simp only [List.mem_singleton, Prod.mk.injEq] at hz
              obtain ⟨_, rfl⟩ := hz
              exact ⟨w, hw⟩
            · simp at hz

/-- In a list with distinct keys, a key's pair is what `lookup` finds. -/
theorem lookup_of_mem {β : Type} : ∀ {l : List (Key × β)}, (l.map Prod.fst).Nodup →
    ∀ {k : Key} {y : β}, (k, y) ∈ l → l.lookup k = some y
  | [], _, _, _, h => by simp at h
  | (k', y') :: l, hn, k, y, h => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    rcases List.mem_cons.mp h with h1 | h1
    · injection h1 with h2 h3
      subst h2 h3
      simp [List.lookup]
    · have hkk : k ≠ k' := by
        rintro rfl
        exact hn.1 ⟨(k, y), h1, rfl⟩
      have : (k == k') = false := by simpa using hkk
      simp only [List.lookup, this]
      exact lookup_of_mem hn.2 h1

/-- A key that a list lacks: `lookup` finds nothing. -/
theorem lookup_none {β : Type} {l : List (Key × β)} {k : Key} (h : k ∉ l.map Prod.fst) :
    l.lookup k = none := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    obtain ⟨k', y'⟩ := a
    simp only [List.map_cons, List.mem_cons, not_or] at h
    have : (k == k') = false := by simpa using h.1
    simp only [List.lookup, this]
    exact ih h.2

/-- A sound tree's contents have distinct keys. -/
theorem contents_nodup {p : Params} {s : Tree} (h : invOk p s = true) :
    ((contents s).map Prod.fst).Nodup := by
  unfold invOk at h
  unfold contents
  cases hr : s.root with
  | none => simp
  | some r =>
    simp only [hr] at h
    cases ho : s.obj r with
    | none => simp [ho] at h
    | some o =>
      simp only [ho] at h
      cases o with
      | val _ => simp at h
      | key n =>
        simp only [Bool.and_eq_true] at h
        have hg := walk_good _ _ _ _ h.2
        have hs := hg.sorted
        unfold L at hs
        have : ((listAt s (s.fuel r) r).map Prod.fst).Pairwise (· < ·) :=
          List.pairwise_map.mpr hs
        exact this.imp (fun hab => ne_of_lt hab)

/-- After operations of which none puts k, and one deletes it, k is gone. -/
theorem applyOps_del_gone {k : Key} : ∀ (ops : List Op) (m : List (Key × Nat)),
    k ∉ putKeys ops → k ∈ ops.map Op.key → k ∉ (applyOps ops m).map Prod.fst
  | [], _, _, h => by simp at h
  | op :: ops, m, hp, hk => by
    have hp' : k ∉ putKeys ops := by
      intro h
      apply hp
      cases op <;> simp_all [putKeys]
    rw [PeProof.Keys.applyOps_cons']
    by_cases hk' : k ∈ ops.map Op.key
    · exact applyOps_del_gone ops _ hp' hk'
    · have hop : op = .del k := by
        have hk1 : op.key = k := by
          simp only [List.map_cons, List.mem_cons] at hk
          rcases hk with h | h
          · exact h.symm
          · exact absurd h hk'
        cases op with
        | put k' v =>
          exfalso
          apply hp
          simp only [Op.key] at hk1
          subst hk1
          simp [putKeys]
        | del k' => simp only [Op.key] at hk1; rw [hk1]
      subst hop
      intro hmem
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hmem
      rcases PeProof.Keys.mem_applyOps he with h1 | ⟨op', hop', v, hv⟩
      · have := (List.mem_filter.mp h1).2
        simp at this
      · apply hp'
        simp only [putKeys, List.mem_filterMap]
        exact ⟨op', hop', by rw [hv]⟩

section Iter

variable {p : Params} {h : BHist} {top : Nat → Top}

/-- With VAL-NEW, a key that no transaction from a to b writes keeps its
value node. -/
theorem ValNew.keep (hv : ValNew h) (k : Key) {a : Nat} :
    ∀ b, a ≤ b → b ≤ h.txs.length →
      (∀ j (hj : j < h.txs.length), a ≤ j → j < b → k ∉ h.txs[j].ops.map Op.key) →
      (idContents ((h.tree b).at b)).lookup k = (idContents ((h.tree a).at a)).lookup k
  | 0, hab, _, _ => by
    have : a = 0 := by omega
    subst this
    rfl
  | b + 1, hab, hb, hno => by
    rcases Nat.lt_or_ge a (b + 1) with hlt | hge
    · rw [(hv b (by omega) k).2 (hno b (by omega) (by omega) (by omega))]
      exact ValNew.keep hv k b (by omega) (by omega)
        (fun j hj h1 h2 => hno j hj h1 (by omega))
    · have : a = b + 1 := by omega
      subst this
      rfl

/-- Every node of the tree after transaction j was made by a transaction up to
j. -/
theorem MeetsFull.made (hm : MeetsFull p h top) : ∀ j, j ≤ h.txs.length → ∀ y,
    ((h.tree j).obj y).isSome = true → ∃ i, i ≤ j ∧ madeAt h i y = true
  | 0, _, y, hy => by
    obtain ⟨r, z, lr, lz, l0, -, -, -, -, -, -, -, hnew, -, -, hnone, -⟩ := hm.start
    have hyr : y = r := by
      by_contra hne
      change (h.s0.obj y).isSome = true at hy
      rw [hnone y hne] at hy
      cases hy
    subst hyr
    refine ⟨0, le_refl _, ?_⟩
    simp [madeAt, BHist.chs, hnew]
  | j + 1, hj, y, hy => by
    cases h0 : (h.tree j).obj y with
    | some o =>
      obtain ⟨i, hi, hmade⟩ := MeetsFull.made hm j (by omega) y (by rw [h0]; rfl)
      exact ⟨i, by omega, hmade⟩
    | none =>
      have hmade := (hm.step j (by omega)).2.2.1 y h0 hy
      refine ⟨j + 1, le_refl _, ?_⟩
      have : (h.chs.getD (j + 1) { new := [], adds := [] }) = h.txs[j].c := by
        simp [BHist.chs, show j < h.txs.length by omega]
      simp only [madeAt, this, List.any_eq_true, beq_iff_eq]
      obtain ⟨nn, hnn, hid⟩ := List.mem_map.mp hmade
      exact ⟨nn, hnn, hid⟩

/-- The last of the transactions from a to b that has a property. -/
theorem last_of {W : Nat → Prop} {a : Nat} : ∀ b, (∃ j, a ≤ j ∧ j < b ∧ W j) →
    ∃ j, a ≤ j ∧ j < b ∧ W j ∧ ∀ j', j < j' → j' < b → ¬ W j'
  | 0, ⟨j, _, hj, _⟩ => absurd hj (Nat.not_lt_zero _)
  | b + 1, hex => by
    by_cases hb : a ≤ b ∧ W b
    · exact ⟨b, hb.1, by omega, hb.2, fun j' h1 h2 => by omega⟩
    · obtain ⟨j, h1, h2, h3⟩ := hex
      have hjb : j < b := by
        rcases Nat.lt_or_ge j b with h | h
        · exact h
        · have : j = b := by omega
          subst this
          exact absurd ⟨h1, h3⟩ hb
      obtain ⟨j0, g1, g2, g3, g4⟩ := last_of b ⟨j, h1, hjb, h3⟩
      refine ⟨j0, g1, by omega, g3, fun j' k1 k2 => ?_⟩
      rcases Nat.lt_or_ge j' b with h | h
      · exact g4 j' k1 h
      · have : j' = b := by omega
        subst this
        exact fun hw => hb ⟨by omega, hw⟩

end Iter

/-- **RC2 from the iteration** (bergdb 030-24): with VAL-NEW, an iteration that
meets `IterationOK` leaves every live key's value node made at c or later. -/
theorem rc2_of_iteration {p : Params} {h : BHist} {top : Nat → Top} (hm : MeetsFull p h top)
    (hM : 1 ≤ p.M) (hv : ValNew h) {c s e : Nat} (hit : IterationOK h c s e) :
    RC2Tree h c e := by
  obtain ⟨hcs, hs1, hse, hen, hit⟩ := hit
  intro k y hky
  -- The key's value node at e, by lookup: the contents' keys are distinct.
  have hnd : ((idContents ((h.tree e).at e)).map Prod.fst).Nodup := by
    rw [idContents_keys]
    exact contents_nodup (hm.inv_at hM e hen)
  have hle := lookup_of_mem hnd hky
  -- y is a value of the tree, made by a transaction up to e.
  have hys : ((h.tree e).obj y).isSome = true := by
    unfold idContents at hky
    split at hky
    · obtain ⟨w, hw⟩ := idListAt_val _ _ _ _ _ hky
      simp only [Tree.at] at hw
      cases h' : (h.tree e).obj y with
      | none => rw [h'] at hw; cases hw
      | some _ => rfl
    · simp at hky
  obtain ⟨i0, hi0, hmade0⟩ := hm.made e hen y hys
  by_cases hex : ∃ j, s - 1 ≤ j ∧ j < e ∧ ∃ hj : j < h.txs.length, k ∈ h.txs[j].ops.map Op.key
  · -- The last transaction up to e that writes k.
    obtain ⟨j, h1, h2, ⟨hj, hw⟩, h4⟩ := last_of e hex
    have hkeep := hv.keep k (a := j + 1) e (by omega) hen
      (fun j' hj' a1 a2 hw' => h4 j' (by omega) a2 ⟨hj', hw'⟩)
    by_cases hput : k ∈ putKeys h.txs[j].ops
    · -- A put: its new value node is the one at e.
      obtain ⟨y', hy', hmade'⟩ := (hv j hj k).1 hput
      rw [hkeep, hy'] at hle
      injection hle with hle
      subst hle
      exact ⟨j + 1, by omega, by omega, hmade'⟩
    · -- A delete: k is not live after it, nor at e.
      exfalso
      have hc := (hm.step j hj).1.1
      simp only [contractOk, Bool.and_eq_true, beq_iff_eq, Nat.add_sub_cancel] at hc
      have hgone := applyOps_del_gone h.txs[j].ops (contents ((h.tree j).at j)) hput hw
      rw [← hc.2, ← idContents_keys] at hgone
      rw [hkeep, lookup_none hgone] at hle
      cases hle
  · -- No transaction from s to e writes k: its value node is the one before s.
    have hkeep := hv.keep k (a := s - 1) e (by omega) hen
      (fun j hj a1 a2 hw => hex ⟨j, a1, a2, hj, hw⟩)
    rw [hkeep] at hle
    refine ⟨i0, ?_, hi0, hmade0⟩
    by_contra hlt
    obtain ⟨j, hj, h1, h2, h3⟩ := hit k y hle ⟨i0, by omega, hmade0⟩
    exact hex ⟨j, by omega, by omega, hj, h3⟩

/-! ## The cuts of a run, with the iteration -/

/-- The cut marks of a run meet reclaim's contract with RC2 and RC3 in the
contract's words: at each mark of a cut c, c is at or after every earlier
mark's cut, and some iteration (s, e) with the cut c meets `IterationOK`, some
key is live after e (the iteration's last step puts its row), e is at most
the first available time, and RC4 holds (Java's two waits). -/
def CutsMeetIter (h : BHist) (al : SIS.Algo BVal Nat)
    (cs : List (Nat × Option Nat × List SIS.HCacheOp)) : Prop :=
  ∀ j (hjl : j < cs.length) c, cs[j].2.1 = some c →
    (∀ i (hi : i < j) c', cs[i].2.1 = some c' → c' ≤ c) ∧
    ∃ s e, IterationOK h c s e ∧ contents ((h.tree e).at e) ≠ [] ∧
      e ≤ SIS.lastFa (SIS.run h.spec al (h.ts.take (j + 1))).S ∧ RC4 h.spec al h.ts e (j + 1)

/-- With VAL-NEW, cuts that meet the iteration meet RC. -/
theorem cutsMeetRC_of_iter {p : Params} {h : BHist} {top : Nat → Top} (hm : MeetsFull p h top)
    (hM : 1 ≤ p.M) (hv : ValNew h) (al : SIS.Algo BVal Nat)
    {cs : List (Nat × Option Nat × List SIS.HCacheOp)} (hcs : cs.map (·.1) = h.ts)
    (hit : CutsMeetIter h al cs) :
    CutsMeetRC h.spec al cs := by
  intro j hjl c hc
  obtain ⟨hord, s, e, hiter, hne, hfa, hrc4⟩ := hit j hjl c hc
  refine ⟨hord, e, ?_⟩
  obtain ⟨hcs', -, hse, hen, -⟩ := id hiter
  rw [hcs]
  exact ⟨by omega, hfa, rc2_of_tree hm hM al hen (rc2_of_iteration hm hM hv hiter),
    rc3_tree hm hM al hen hne, hrc4⟩

/-- **Reclaim chooses only safe cuts, given VAL-NEW** (bergdb 030-24): for a
history in the contract's words with VAL-NEW, Java's still-dirty test and the
marking, policies that read no cut stream, and cuts whose iterations meet
`IterationOK` (with a key live at each iteration's end, the end at most the
first available time, and Java's two waits), Java's get and scan after the
run with handles, evictions and restarts from the cut streams are right at
every time from the first available time on. -/
theorem reclaim_java_reads {p : Params} {h : BHist} {top : Nat → Top} {kind : Nat → Bool}
    (hm : MeetsFull p h top) (hM : 1 ≤ p.M) (hkd : KindsOK kind h) (hv : ValNew h)
    (al : SIS.Algo BVal Nat) (hj : al.stillDirty = SIS.javaTest h.spec) (hmk : al.mark = true)
    (hpol : SIS.PolicyCutOK al) (cs : List (Nat × Option Nat × List SIS.HCacheOp))
    (hcs : cs.map (·.1) = h.ts)
    (hit : CutsMeetIter h al cs)
    (hreads : ∀ j (hjl : j < cs.length), cs[j].2.1 = none → ∀ t,
      SIS.HCacheOp.read t ∈ cs[j].2.2 →
      SIS.lastFa (SIS.run h.spec al ((cs.map (·.1)).take (j + 1))).S ≤ t ∧ t ≤ j + 1)
    {t : Nat} (hft : SIS.lastFa (SIS.run h.spec al h.ts).S ≤ t) (htn : t ≤ h.txs.length)
    (mid : Bool) (s : Tree) (tp : Top) :
    let V := SIS.view h.spec (SIS.runHandlesCut h.spec al cs).1.P t
    HoldsView V (kindOf kind V) t s →
      TopFrom (SIS.lastFa (SIS.run h.spec al h.ts).S) (top h.txs.length) tp →
      JReadsRight s tp t mid (h.txs.map (·.ops)) :=
  cut_java_reads_of_rc hm hM hkd al hj hmk hpol cs hcs (cutsMeetRC_of_iter hm hM hv al hcs hit)
    hreads hft htn mid s tp

/-! ## VAL-NEW from distinct put hashes -/

/-- An entry of the plain map after operations was there before, or one of
them put it. -/
theorem mem_applyOps_put : ∀ {ops : List Op} {m : List (Key × Nat)} {e : Key × Nat},
    e ∈ applyOps ops m → e ∈ m ∨ Op.put e.1 e.2 ∈ ops
  | [], _, _, h => Or.inl h
  | op :: ops, m, e, h => by
    rw [PeProof.Keys.applyOps_cons'] at h
    rcases mem_applyOps_put h with h | h
    · cases op with
      | put k v =>
        rcases PeProof.Keys.mem_mapPut h with rfl | h
        · exact Or.inr (by simp)
        · exact Or.inl h
      | del k => exact Or.inl (PeProof.Keys.mem_mapDel h)
    · exact Or.inr (List.mem_cons_of_mem _ h)

theorem mem_mapPut_self (k : Key) (v : Nat) : ∀ m : List (Key × Nat), (k, v) ∈ mapPut k v m
  | [] => by simp [mapPut]
  | (k', v') :: r => by
    unfold mapPut
    split_ifs with h1 h2
    · simp
    · simp
    · exact List.mem_cons_of_mem _ (mem_mapPut_self k v r)

theorem mem_mapPut_of_ne {k k' : Key} {v v' : Nat} (hne : k ≠ k') :
    ∀ {m : List (Key × Nat)}, (k, v) ∈ m → (k, v) ∈ mapPut k' v' m
  | [], h => by simp at h
  | (a, b) :: r, h => by
    unfold mapPut
    split_ifs with h1 h2
    · exact List.mem_cons_of_mem _ h
    · rcases List.mem_cons.mp h with h3 | h3
      · injection h3 with h4 _
        exact absurd (h4.trans h2.symm) hne
      · exact List.mem_cons_of_mem _ h3
    · rcases List.mem_cons.mp h with h3 | h3
      · rw [h3]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_mapPut_of_ne hne h3)

/-- Operations on other keys keep an entry. -/
theorem applyOps_keep {k : Key} {v : Nat} : ∀ (ops : List Op) (m : List (Key × Nat)),
    k ∉ ops.map Op.key → (k, v) ∈ m → (k, v) ∈ applyOps ops m
  | [], _, _, h => h
  | op :: ops, m, hk, h => by
    rw [PeProof.Keys.applyOps_cons']
    simp only [List.map_cons, List.mem_cons, not_or] at hk
    apply applyOps_keep ops _ hk.2
    cases op with
    | put k' v' => exact mem_mapPut_of_ne (by simpa [Op.key] using hk.1) h
    | del k' =>
      refine List.mem_filter.mpr ⟨h, ?_⟩
      simpa [Op.key] using hk.1

/-- With distinct keys, a put's entry is in the map after the operations. -/
theorem applyOps_put {k : Key} {v : Nat} : ∀ (ops : List Op) (m : List (Key × Nat)),
    (ops.map Op.key).Nodup → Op.put k v ∈ ops → (k, v) ∈ applyOps ops m
  | [], _, _, h => by simp at h
  | op :: ops, m, hn, h => by
    rw [PeProof.Keys.applyOps_cons']
    simp only [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.mp h with rfl | h
    · exact applyOps_keep ops _ (by simpa [Op.key] using hn.1) (mem_mapPut_self k v m)
    · exact applyOps_put ops _ hn.2 h

/-- A key that the operations do not write keeps its entries. -/
theorem applyOps_unwritten {k : Key} {v : Nat} {ops : List Op} {m : List (Key × Nat)}
    (hk : k ∉ ops.map Op.key) : (k, v) ∈ applyOps ops m ↔ (k, v) ∈ m := by
  constructor
  · intro h
    rcases mem_applyOps_put h with h | h
    · exact h
    · exact absurd (List.mem_map.mpr ⟨_, h, rfl⟩) hk
  · exact applyOps_keep ops m hk

/-- A live key's value node by id holds the value that the contents give it. -/
theorem idListAt_mem_listAt (s : Tree) : ∀ (f : Nat) (x : NodeId) (k : Key) (y : NodeId) (v : Nat),
    (k, y) ∈ idListAt s f x → s.obj y = some (.val v) → (k, v) ∈ listAt s f x
  | 0, _, _, _, _, h, _ => by simp [idListAt] at h
  | f + 1, x, k, y, v, h, hy => by
    simp only [idListAt] at h
    simp only [listAt]
    cases hx : s.obj x with
    | none => rw [hx] at h; simp at h
    | some o =>
      rw [hx] at h
      cases o with
      | val _ => simp at h
      | key n =>
        simp only [List.mem_flatMap] at h ⊢
        obtain ⟨⟨c, z⟩, hcz, hz⟩ := h
        refine ⟨(c, z), hcz, ?_⟩
        unfold idKlongList at hz
        unfold klongList
        cases hl : n.leaf with
        | false =>
          simp only [hl, Bool.false_eq_true, ite_false] at hz ⊢
          exact idListAt_mem_listAt s f z k y v hz hy
        | true =>
          cases hc : isLong c with
          | true =>
            simp only [hl, hc, ite_true, List.mem_map] at hz ⊢
            obtain ⟨⟨k', y'⟩, hk', heq⟩ := hz
            injection heq with h1 h2
            subst h1 h2
            exact ⟨(k', v), idListAt_mem_listAt s f z k' y' v hk' hy, rfl⟩
          | false =>
            simp only [hl, hc, ite_true, Bool.false_eq_true, ite_false] at hz ⊢
            split at hz
            · simp only [List.mem_singleton, Prod.mk.injEq] at hz
              obtain ⟨rfl, rfl⟩ := hz
              rw [hy]
              simp
            · simp at hz

/-- A live key's value node by id is reached by the walk. -/
theorem idListAt_reach (s : Tree) : ∀ (f : Nat) (x : NodeId) (k : Key) (y : NodeId),
    (k, y) ∈ idListAt s f x → y ∈ reachAt s f x
  | 0, _, _, _, h => by simp [idListAt] at h
  | f + 1, x, k, y, h => by
    simp only [idListAt] at h
    simp only [reachAt, List.mem_cons]
    right
    cases hx : s.obj x with
    | none => rw [hx] at h; simp at h
    | some o =>
      rw [hx] at h
      cases o with
      | val _ => simp at h
      | key n =>
        simp only [List.mem_flatMap] at h ⊢
        obtain ⟨⟨c, z⟩, hcz, hz⟩ := h
        refine ⟨(c, z), hcz, ?_⟩
        unfold idKlongList at hz
        cases hl : n.leaf with
        | false =>
          simp only [hl, Bool.false_eq_true, ite_false] at hz
          exact idListAt_reach s f z k y hz
        | true =>
          cases hc : isLong c with
          | true =>
            simp only [hl, hc, ite_true, List.mem_map] at hz
            obtain ⟨⟨k', y'⟩, hk', heq⟩ := hz
            injection heq with _ h2
            subst h2
            exact idListAt_reach s f z k' y' hk'
          | false =>
            simp only [hl, hc, ite_true, Bool.false_eq_true, ite_false] at hz
            split at hz
            · simp only [List.mem_singleton, Prod.mk.injEq] at hz
              obtain ⟨_, rfl⟩ := hz
              exact mem_reachAt_self s f y
            · simp at hz

theorem idContents_mem_contents {s : Tree} {k : Key} {y : NodeId} {v : Nat}
    (h : (k, y) ∈ idContents s) (hy : s.obj y = some (.val v)) : (k, v) ∈ contents s := by
  unfold idContents at h
  unfold contents
  cases hr : s.root with
  | none => rw [hr] at h; simp at h
  | some r => rw [hr] at h; exact idListAt_mem_listAt s _ r k y v h hy

theorem idContents_reach {s : Tree} {k : Key} {y : NodeId} (h : (k, y) ∈ idContents s) :
    y ∈ reach s := by
  unfold idContents at h
  unfold reach
  cases hr : s.root with
  | none => rw [hr] at h; simp at h
  | some r => rw [hr] at h; exact idListAt_reach s _ r k y h

theorem mem_of_lookup' {β : Type} {l : List (Key × β)} {k : Key} {y : β}
    (h : l.lookup k = some y) : (k, y) ∈ l := by
  obtain ⟨l₁, l₂, rfl, -⟩ := List.lookup_eq_some_iff.mp h
  simp

section Unique

variable {p : Params} {h : BHist} {top : Nat → Top}

/-- Every entry of the contents after j transactions was put by one of them. -/
theorem MeetsFull.contents_puts (hm : MeetsFull p h top) (hM : 1 ≤ p.M) :
    ∀ j, j ≤ h.txs.length → ∀ e ∈ contents ((h.tree j).at j),
      ∃ j0, ∃ hj0 : j0 < h.txs.length, j0 < j ∧ Op.put e.1 e.2 ∈ h.txs[j0].ops
  | 0, _, e, he => by
    change e ∈ contents (h.s0.at 0) at he
    rw [(hm.start.start hM).2] at he
    simp at he
  | j + 1, hj, e, he => by
    have hc := (hm.step j (by omega)).1.1
    simp only [contractOk, Bool.and_eq_true, beq_iff_eq, Nat.add_sub_cancel] at hc
    rw [hc.2] at he
    rcases mem_applyOps_put he with h1 | h1
    · obtain ⟨j0, hj0, h2, h3⟩ := MeetsFull.contents_puts hm hM j (by omega) e h1
      exact ⟨j0, hj0, by omega, h3⟩
    · exact ⟨j, by omega, by omega, h1⟩

/-- A node of the tree keeps its kind, and a value its hash, in the next tree. -/
theorem MeetsFull.obj_next (hm : MeetsFull p h top) {j : Nat} (hj : j < h.txs.length)
    {x : NodeId} {o : Obj} (hx : (h.tree j).obj x = some o) :
    ∃ o', (h.tree (j + 1)).obj x = some o' ∧ Ext (j + 1) o o' :=
  let ⟨o', h1, h2, _⟩ := (hm.step j hj).1.2.1 x o hx
  ⟨o', h1, h2⟩

/-- A value that the walk reaches is named by a live key. -/
theorem MeetsFull.reach_idContents (hm : MeetsFull p h top) (hM : 1 ≤ p.M) {j : Nat}
    (hj : j ≤ h.txs.length) {y : NodeId} (hy : y ∈ reach ((h.tree j).at j)) {v : Nat}
    (hv : ((h.tree j).at j).obj y = some (.val v)) :
    ∃ k, (k, y) ∈ idContents ((h.tree j).at j) := by
  have hi := hm.meetsBridge.binv j hj
  rw [hi.timely.at_eq] at hy hv ⊢
  unfold reach at hy
  unfold idContents
  cases hr : (h.tree j).root with
  | none => rw [hr] at hy; simp at hy
  | some r =>
    rw [hr] at hy
    obtain ⟨n, hn, hg, -⟩ := hm.root_good hM hj hr
    have hfuel : (h.tree j).fuel r = n.level + 1 := by simp [Tree.fuel, hn]
    exact Good.mem_idListAt _ hg hn (by rw [hfuel]; omega) y v hy hv

/-- **VAL-NEW from distinct put hashes**: in a history in the contract's
words whose transactions have distinct keys, whose puts have distinct hashes
(a hash names one transaction and one key), and whose transactions make value
nodes only with hashes they put, VAL-NEW holds. A put's key names, after its
transaction, a value node with the put's hash, which is new: an older one
would hold a hash of an older put. A key not written names a value node with
the same hash as before; if it is not the one before, it is an older value
node that the walk reached before, so a live key named it then with that
hash, which only the old key was put with. -/
theorem valNew_of_unique (hm : MeetsFull p h top) (hM : 1 ≤ p.M)
    (hk : ∀ j (hj : j < h.txs.length), (h.txs[j].ops.map Op.key).Nodup)
    (hu : ∀ j (hj : j < h.txs.length) j' (hj' : j' < h.txs.length) k k' v,
      Op.put k v ∈ h.txs[j].ops → Op.put k' v ∈ h.txs[j'].ops → j = j' ∧ k = k')
    (hmade : ∀ j (hj : j < h.txs.length) y v, y ∈ h.txs[j].c.new.map (·.id) →
      (h.tree (j + 1)).obj y = some (.val v) → ∃ k, Op.put k v ∈ h.txs[j].ops) :
    ValNew h := by
  intro j hj k
  have hc := (hm.step j hj).1.1
  simp only [contractOk, Bool.and_eq_true, beq_iff_eq, Nat.add_sub_cancel] at hc
  have hstep : contents ((h.tree (j + 1)).at (j + 1)) =
      applyOps h.txs[j].ops (contents ((h.tree j).at j)) := hc.2
  have hnd0 := contents_nodup (hm.inv_at hM j (by omega))
  have hnd1 := contents_nodup (hm.inv_at hM (j + 1) hj)
  have hind0 : ((idContents ((h.tree j).at j)).map Prod.fst).Nodup := by
    rw [idContents_keys]; exact hnd0
  have hind1 : ((idContents ((h.tree (j + 1)).at (j + 1))).map Prod.fst).Nodup := by
    rw [idContents_keys]; exact hnd1
  have hnores := (bridgeOk_parts (hm.step j hj).2.1).2.2.2.2.2
  simp only [noResOk, List.all_eq_true, Bool.or_eq_true, List.contains_iff_mem, List.any_eq_true,
    beq_iff_eq, Nat.add_sub_cancel] at hnores
  -- A value node named by a live key after j + 1: its hash, and where it was.
  have hval : ∀ k' y, (k', y) ∈ idContents ((h.tree (j + 1)).at (j + 1)) →
      ∃ v, ((h.tree (j + 1)).at (j + 1)).obj y = some (.val v) ∧
        (k', v) ∈ contents ((h.tree (j + 1)).at (j + 1)) ∧
        (y ∈ h.txs[j].c.new.map (·.id) ∨
          ∃ k2, (k2, v) ∈ contents ((h.tree j).at j)) := by
    intro k' y hy
    have hy' := hy
    unfold idContents at hy'
    split at hy'
    · obtain ⟨v, hv⟩ := idListAt_val _ _ _ _ _ hy'
      refine ⟨v, hv, idContents_mem_contents hy hv, ?_⟩
      rcases hnores y (idContents_reach hy) with hold | ⟨nn, hnn, hid⟩
      · right
        have hi := hm.meetsBridge.binv j (by omega)
        have hobj : ((h.tree j).at j).obj y ≠ none := by
          have := hi.reach_obj (by rw [← hi.timely.at_eq]; exact hold)
          rw [hi.timely.at_eq]
          intro h0; rw [h0] at this; cases this
        obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.mp hobj
        have ho' : (h.tree j).obj y = some o := by
          rw [hi.timely.at_eq] at ho; exact ho
        obtain ⟨o', ho1, hext⟩ := hm.obj_next hj ho'
        have hv' : (h.tree (j + 1)).obj y = some (.val v) := by
          have hi1 := hm.meetsBridge.binv (j + 1) hj
          rw [hi1.timely.at_eq] at hv; exact hv
        rw [hv'] at ho1
        injection ho1 with ho1
        subst ho1
        cases o with
        | key n => simp [Ext] at hext
        | val w =>
          simp only [Ext] at hext
          subst hext
          obtain ⟨k2, hk2⟩ := hm.reach_idContents hM (by omega) hold
            (by rw [hi.timely.at_eq]; exact ho')
          exact ⟨k2, idContents_mem_contents hk2 (by rw [hi.timely.at_eq]; exact ho')⟩
      · left
        exact List.mem_map.mpr ⟨nn, hnn, hid⟩
    · simp at hy'
  constructor
  · -- A put: its key names a new value node.
    intro hput
    obtain ⟨v, hv⟩ : ∃ v, Op.put k v ∈ h.txs[j].ops := by
      simp only [putKeys, List.mem_filterMap] at hput
      obtain ⟨op, hop, hk'⟩ := hput
      cases op with
      | put k' v => simp only [Option.some.injEq] at hk'; subst hk'; exact ⟨v, hop⟩
      | del k' => simp at hk'
    have hc1 : (k, v) ∈ contents ((h.tree (j + 1)).at (j + 1)) := by
      rw [hstep]; exact applyOps_put _ _ (hk j hj) hv
    have hkey : (idContents ((h.tree (j + 1)).at (j + 1))).lookup k ≠ none := by
      intro hn
      have : k ∉ (idContents ((h.tree (j + 1)).at (j + 1))).map Prod.fst := by
        intro hm'
        obtain ⟨⟨k', y'⟩, hm1, rfl⟩ := List.mem_map.mp hm'
        rw [lookup_of_mem hind1 hm1] at hn
        cases hn
      rw [idContents_keys] at this
      exact this (List.mem_map.mpr ⟨_, hc1, rfl⟩)
    obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp hkey
    refine ⟨y, hy, ?_⟩
    obtain ⟨w, -, hw, hcase⟩ := hval k y (mem_of_lookup' hy)
    have hwv : w = v := by
      have h1 := lookup_of_mem hnd1 hw
      rw [lookup_of_mem hnd1 hc1] at h1
      injection h1 with h1
      exact h1.symm
    subst hwv
    rcases hcase with hnew | ⟨k2, hk2⟩
    · obtain ⟨nn, hnn, hid⟩ := List.mem_map.mp hnew
      have : (h.chs.getD (j + 1) { new := [], adds := [] }) = h.txs[j].c := by
        simp [BHist.chs, hj]
      simp only [madeAt, this, List.any_eq_true, beq_iff_eq]
      exact ⟨nn, hnn, hid⟩
    · exfalso
      obtain ⟨j0, hj0, hlt, hp⟩ := hm.contents_puts hM j (by omega) _ hk2
      have := (hu j hj j0 hj0 k k2 w hv hp).1
      omega
  · -- A key not written: its value node is the one before.
    intro hnot
    have hiff : ∀ v, (k, v) ∈ contents ((h.tree (j + 1)).at (j + 1)) ↔
        (k, v) ∈ contents ((h.tree j).at j) := by
      intro v; rw [hstep]; exact applyOps_unwritten hnot
    cases ho : (idContents ((h.tree j).at j)).lookup k with
    | none =>
      apply lookup_none
      rw [idContents_keys]
      intro hm'
      obtain ⟨⟨k', v⟩, hm1, rfl⟩ := List.mem_map.mp hm'
      have h0 : (k', v) ∈ contents ((h.tree j).at j) := (hiff v).mp hm1
      have : k' ∈ (idContents ((h.tree j).at j)).map Prod.fst := by
        rw [idContents_keys]; exact List.mem_map.mpr ⟨_, h0, rfl⟩
      obtain ⟨⟨k'', y''⟩, hm2, rfl⟩ := List.mem_map.mp this
      rw [lookup_of_mem hind0 hm2] at ho
      cases ho
    | some yo =>
      have hyo := mem_of_lookup' ho
      have hi := hm.meetsBridge.binv j (by omega)
      have hyo' := hyo
      unfold idContents at hyo'
      split at hyo'
      · obtain ⟨vo, hvo⟩ := idListAt_val _ _ _ _ _ hyo'
        have hc0 := idContents_mem_contents hyo hvo
        have hc1 := (hiff vo).mpr hc0
        have hkey : (idContents ((h.tree (j + 1)).at (j + 1))).lookup k ≠ none := by
          intro hn
          have : k ∉ (idContents ((h.tree (j + 1)).at (j + 1))).map Prod.fst := by
            intro hm'
            obtain ⟨⟨k', y'⟩, hm1, rfl⟩ := List.mem_map.mp hm'
            rw [lookup_of_mem hind1 hm1] at hn
            cases hn
          rw [idContents_keys] at this
          exact this (List.mem_map.mpr ⟨_, hc1, rfl⟩)
        obtain ⟨yn, hyn⟩ := Option.ne_none_iff_exists'.mp hkey
        rw [hyn]
        obtain ⟨vn, hvn, hcn, hcase⟩ := hval k yn (mem_of_lookup' hyn)
        have hvv : vn = vo := by
          have h1 := lookup_of_mem hnd1 hcn
          rw [lookup_of_mem hnd1 hc1] at h1
          injection h1 with h1
          exact h1.symm
        subst hvv
        obtain ⟨j0, hj0, hlt0, hp0⟩ := hm.contents_puts hM j (by omega) _ hc0
        rcases hcase with hnew | ⟨k2, hk2⟩
        · exfalso
          have hvn' : (h.tree (j + 1)).obj yn = some (.val vn) := by
            have hi1 := hm.meetsBridge.binv (j + 1) hj
            rw [hi1.timely.at_eq] at hvn; exact hvn
          obtain ⟨k3, hk3⟩ := hmade j hj yn vn hnew hvn'
          have := (hu j hj j0 hj0 k3 k vn hk3 hp0).1
          omega
        · -- yn was reached before: the old key named it.
          -- (yn's object before is the same value.)
          have hyn_reach := idContents_reach (mem_of_lookup' hyn)
          rcases hnores yn hyn_reach with hold | ⟨nn, hnn, hid⟩
          · have hobj : ((h.tree j).at j).obj yn ≠ none := by
              have := hi.reach_obj (by rw [← hi.timely.at_eq]; exact hold)
              rw [hi.timely.at_eq]
              intro h0; rw [h0] at this; cases this
            obtain ⟨o, hoo⟩ := Option.ne_none_iff_exists'.mp hobj
            have ho' : (h.tree j).obj yn = some o := by
              rw [hi.timely.at_eq] at hoo; exact hoo
            obtain ⟨o', ho1, hext⟩ := hm.obj_next hj ho'
            have hvn' : (h.tree (j + 1)).obj yn = some (.val vn) := by
              have hi1 := hm.meetsBridge.binv (j + 1) hj
              rw [hi1.timely.at_eq] at hvn; exact hvn
            rw [hvn'] at ho1
            injection ho1 with ho1
            subst ho1
            cases o with
            | key n => simp [Ext] at hext
            | val w =>
              simp only [Ext] at hext
              subst hext
              obtain ⟨k4, hk4⟩ := hm.reach_idContents hM (by omega) hold
                (by rw [hi.timely.at_eq]; exact ho')
              have hc4 := idContents_mem_contents hk4 (by rw [hi.timely.at_eq]; exact ho')
              obtain ⟨j1, hj1, _, hp1⟩ := hm.contents_puts hM j (by omega) _ hc4
              have hk4k := (hu j1 hj1 j0 hj0 k4 k _ hp1 hp0).2
              subst hk4k
              have := lookup_of_mem hind0 hk4
              rw [ho] at this
              injection this with this
              rw [this]
          · exfalso
            have hvn' : (h.tree (j + 1)).obj yn = some (.val vn) := by
              have hi1 := hm.meetsBridge.binv (j + 1) hj
              rw [hi1.timely.at_eq] at hvn; exact hvn
            obtain ⟨k3, hk3⟩ := hmade j hj yn vn (List.mem_map.mpr ⟨nn, hnn, hid⟩) hvn'
            have := (hu j hj j0 hj0 k3 k vn hk3 hp0).1
            omega
      · simp at hyo'

end Unique

end Contract

namespace Contract.PE

variable {cf : Cfg}

/-- **Reclaim chooses only safe cuts, for PE, given VAL-NEW** (bergdb 030-24):
`reclaim_java_reads` for every history PE writes (`pe_full`), with VAL-NEW as a
premise until `pe_valNew` is proved. -/
theorem pe_reclaim_reads_of_valNew (hcf : cf.Ok) (hcap : cf.topBase ≤ 2 ^ 62)
    {txs : List (List Op)} {h : BHist} {top : Nat → Top} (hlen : txs.length < 2 ^ 48 - 1)
    (hk : ∀ ops ∈ txs, (ops.map Op.key).Nodup) (hh : peHist cf txs = some (h, top))
    (hM : 1 ≤ cf.params.M) (hv : ValNew h)
    (al : SIS.Algo SIS.Check.BVal Nat) (hj : al.stillDirty = SIS.javaTest h.spec)
    (hmk : al.mark = true) (hpol : SIS.PolicyCutOK al)
    (cs : List (Nat × Option Nat × List SIS.HCacheOp)) (hcs : cs.map (·.1) = h.ts)
    (hit : CutsMeetIter h al cs)
    (hreads : ∀ j (hjl : j < cs.length), cs[j].2.1 = none → ∀ t,
      SIS.HCacheOp.read t ∈ cs[j].2.2 →
      SIS.lastFa (SIS.run h.spec al ((cs.map (·.1)).take (j + 1))).S ≤ t ∧ t ≤ j + 1)
    {t : Nat} (hft : SIS.lastFa (SIS.run h.spec al h.ts).S ≤ t) (htn : t ≤ h.txs.length)
    (mid : Bool) (s : Tree) (tp : Top) :
    let V := SIS.view h.spec (SIS.runHandlesCut h.spec al cs).1.P t
    HoldsView V (kindOf (peKind cf) V) t s →
      TopFrom (SIS.lastFa (SIS.run h.spec al h.ts).S) (top h.txs.length) tp →
      JReadsRight s tp t mid (h.txs.map (·.ops)) := by
  obtain ⟨hm, hkd⟩ := pe_full hcf hcap hlen hk hh
  exact reclaim_java_reads hm hM hkd hv al hj hmk hpol cs hcs hit hreads hft htn mid s tp

/-! ## VAL-NEW for PE: the run with labelled puts -/

theorem obj_at_objH (σ : Nat → Nat) (t : Time) (o : Obj) :
    Obj.at t (objH σ o) = objH σ (Obj.at t o) := by
  cases o <;> rfl

theorem at_treeH (σ : Nat → Nat) (s : Tree) (t : Time) : (treeH σ s).at t = treeH σ (s.at t) := by
  simp only [Tree.at, treeH, Tree.mk.injEq, and_true]
  funext x
  cases s.obj x <;> simp [obj_at_objH]

theorem idListAt_treeH (σ : Nat → Nat) (s : Tree) : ∀ (f : Nat) (x : NodeId),
    idListAt (treeH σ s) f x = idListAt s f x
  | 0, _ => rfl
  | f + 1, x => by
    have hobj : ∀ z, (treeH σ s).obj z = (s.obj z).map (objH σ) := fun _ => rfl
    simp only [idListAt]
    rw [hobj x]
    cases hx : s.obj x with
    | none => rfl
    | some o =>
      cases o with
      | val _ => rfl
      | key n =>
        simp only [Option.map_some, objH]
        apply List.flatMap_congr
        rintro ⟨c, y⟩ _
        unfold idKlongList
        simp only [idListAt_treeH σ s f, hobj]
        cases n.leaf with
        | false => rfl
        | true =>
          cases isLong c with
          | true => rfl
          | false =>
            simp only
            cases s.obj y with
            | none => rfl
            | some o => cases o <;> rfl

theorem idContents_treeH (σ : Nat → Nat) (s : Tree) : idContents (treeH σ s) = idContents s := by
  unfold idContents
  have hroot : (treeH σ s).root = s.root := rfl
  have hfuel : ∀ x, (treeH σ s).fuel x = s.fuel x := by
    intro x
    simp only [Tree.fuel, treeH]
    cases s.obj x with
    | none => rfl
    | some o => cases o <;> rfl
  rw [hroot]
  cases s.root with
  | none => rfl
  | some r => simp only [hfuel, idListAt_treeH]

theorem putKeys_opH (σ : Nat → Nat) (ops : List Op) : putKeys (ops.map (opH σ)) = putKeys ops := by
  unfold putKeys
  rw [List.filterMap_map]
  congr 1
  funext op
  cases op <;> rfl

/-- The tree after j transactions of a history PE writes, from its run. -/
theorem peHist_tree {L : List (BTx × Top)} (j : Nat) (hj : j ≤ L.length) :
    ((startTree cf :: L.map (·.1.s))[j]?) =
      some ((⟨startTree cf, c0 cf, L.map (·.1)⟩ : BHist).tree j) := by
  cases j with
  | zero => rfl
  | succ j =>
    have hj' : j < L.length := by omega
    simp [BHist.tree, List.getElem?_map, List.getElem?_eq_getElem hj']

theorem peHist_new {L L' : List (BTx × Top)} (hlen : L.length = L'.length)
    (hnew : ∀ j (hj : j < L.length) (hj' : j < L'.length), L[j].1.c.new = L'[j].1.c.new)
    (i : Nat) :
    ((⟨startTree cf, c0 cf, L.map (·.1)⟩ : BHist).chs.getD i { new := [], adds := [] }).new =
      ((⟨startTree cf, c0 cf, L'.map (·.1)⟩ : BHist).chs.getD i { new := [], adds := [] }).new := by
  cases i with
  | zero => simp [BHist.chs]
  | succ j =>
    simp only [BHist.chs, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
      List.getElem?_cons_succ, List.getElem?_map]
    by_cases hj : j < L.length
    · have hj' : j < L'.length := by omega
      simp [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hj', hnew j hj hj']
    · have hj' : ¬ j < L'.length := by omega
      simp [List.getElem?_eq_none (Nat.le_of_not_lt hj),
        List.getElem?_eq_none (Nat.le_of_not_lt hj')]

/-- **PE meets VAL-NEW** (bergdb 030-24; 030-22, section 2.3): every history PE
writes makes a new value node for each put, which the key names after the
transaction, and keeps the value node of each key it does not write. -/
theorem pe_valNew (hcf : cf.Ok) (hcap : cf.topBase ≤ 2 ^ 62) {txs : List (List Op)}
    {h : BHist} {top : Nat → Top} (hlen : txs.length < 2 ^ 48 - 1)
    (hk : ∀ ops ∈ txs, (ops.map Op.key).Nodup) (hh : peHist cf txs = some (h, top)) :
    ValNew h := by

  have hM : 1 ≤ cf.params.M := by
    show 1 ≤ cf.M
    have := hcf.h1; have := hcf.hM; omega
  obtain ⟨L, hr, rfl, -⟩ := peHist_eq hh
  -- The run with each put labelled by its place.
  have hmap := labTxs_map txs
  rw [← hmap, ← startTree_treeH (labσ txs) cf] at hr
  obtain ⟨L', hr', hlenL, hall⟩ := peRun_mapH cf (labσ txs) (labTxs txs) (startTree cf) startTop
    startNext 0 L hr
  have hops' := peRun_ops cf _ _ _ _ _ _ hr'
  have hlenL' : L'.length = (labTxs txs).length := by rw [← hops']; simp
  have hh' : peHist cf (labTxs txs) = some (⟨startTree cf, c0 cf, L'.map (·.1)⟩,
      fun j => match j with
        | 0 => startTop
        | j + 1 => ((L'[j]?).map (·.2)).getD startTop) := by
    unfold peHist
    rw [hr']
    rfl
  have hk' : ∀ ops ∈ labTxs txs, (ops.map Op.key).Nodup := by
    intro ops hops
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hops
    rw [labTxs_get txs hj, relab_keys]
    exact hk _ (List.getElem_mem _)
  have hm' := (pe_full hcf hcap (by rw [labTxs_length]; exact hlen) hk' hh').1
  -- The labelled history's transactions are the labelled operations.
  have hopsj : ∀ j (hj : j < L'.length), L'[j].1.ops = (labTxs txs)[j]'(by omega) := by
    intro j hj
    have := congrArg (fun l => l[j]?) hops'
    simp only [List.getElem?_map, List.getElem?_eq_getElem hj, Option.map_some,
      List.getElem?_eq_getElem (show j < (labTxs txs).length by omega)] at this
    exact Option.some.inj this
  have hv' : ValNew (⟨startTree cf, c0 cf, L'.map (·.1)⟩ : BHist) := by
    apply valNew_of_unique hm' hM
    · intro j hj
      simp only [List.getElem_map]
      rw [hopsj j (by simpa using hj)]
      exact hk' _ (List.getElem_mem _)
    · intro j hj j' hj' k k' v h1 h2
      simp only [List.getElem_map] at h1 h2
      rw [hopsj j (by simpa using hj)] at h1
      rw [hopsj j' (by simpa using hj')] at h2
      exact labTxs_unique txs _ _ h1 h2
    · intro j hj y v hy hv
      have hjL : j < L'.length := by simpa using hj
      have hnone : ((⟨startTree cf, c0 cf, L'.map (·.1)⟩ : BHist).tree j).obj y = none := by
        have hn := (bridgeOk_parts (hm'.step j hj).2.1).1
        simp only [newsOk, Bool.and_eq_true, List.all_eq_true] at hn
        obtain ⟨nn, hnn, hid⟩ := List.mem_map.mp hy
        have := (hn.2 nn hnn).1
        rw [hid] at this
        simpa using this
      have htree : ((⟨startTree cf, c0 cf, L'.map (·.1)⟩ : BHist).tree (j + 1)) = L'[j].1.s := by
        simp [BHist.tree, List.getElem?_map, List.getElem?_eq_getElem hjL]
      rw [htree] at hv
      have := peRun_vals cf _ _ _ _ _ _ hr' j hjL y v hv
        (by rw [peHist_tree j (by omega), Option.bind_some]; exact hnone)
      simpa using this
  -- Back to the history: the same steps, the trees the images of the labelled ones.
  have htree : ∀ j, (⟨startTree cf, c0 cf, L.map (·.1)⟩ : BHist).tree j =
      treeH (labσ txs) ((⟨startTree cf, c0 cf, L'.map (·.1)⟩ : BHist).tree j) := by
    intro j
    cases j with
    | zero => exact (startTree_treeH _ cf).symm
    | succ j =>
      simp only [BHist.tree, List.getElem?_map]
      by_cases hj : j < L.length
      · have hj' : j < L'.length := by omega
        simp only [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hj', Option.map_some]
        exact (hall j hj hj').2.1
      · have hj' : ¬ j < L'.length := by omega
        simp only [List.getElem?_eq_none (Nat.le_of_not_lt hj),
          List.getElem?_eq_none (Nat.le_of_not_lt hj'), Option.map_none]
        exact (startTree_treeH _ cf).symm
  have hidc : ∀ j, idContents (((⟨startTree cf, c0 cf, L.map (·.1)⟩ : BHist).tree j).at j) =
      idContents (((⟨startTree cf, c0 cf, L'.map (·.1)⟩ : BHist).tree j).at j) := by
    intro j
    rw [htree j, at_treeH, idContents_treeH]
  have hmadeEq : ∀ i y, madeAt (⟨startTree cf, c0 cf, L.map (·.1)⟩ : BHist) i y =
      madeAt (⟨startTree cf, c0 cf, L'.map (·.1)⟩ : BHist) i y := by
    intro i y
    simp only [madeAt]
    rw [peHist_new hlenL (fun j hj hj' => (hall j hj hj').2.2.1) i]
  intro j hj k
  have hjL : j < L.length := by simpa using hj
  have hjL' : j < L'.length := by omega
  have hopsEq : ((L.map (fun p : BTx × Top => p.1))[j]'hj).ops =
      ((L'.map (fun p : BTx × Top => p.1))[j]'(by simpa using hjL')).ops.map (opH (labσ txs)) := by
    simp only [List.getElem_map]
    exact (hall j hjL hjL').1
  obtain ⟨A, B⟩ := hv' j (by simpa using hjL') k
  constructor
  · intro hput
    rw [hopsEq, putKeys_opH] at hput
    obtain ⟨y, hy, hm⟩ := A hput
    refine ⟨y, ?_, ?_⟩
    · rw [hidc]; exact hy
    · rw [hmadeEq]; exact hm
  · intro hnot
    rw [hopsEq, List.map_map] at hnot
    have hnot' : k ∉
        ((L'.map (fun p : BTx × Top => p.1))[j]'(by simpa using hjL')).ops.map Op.key := by
      intro hm; apply hnot
      have : (Op.key ∘ opH (labσ txs)) = Op.key := by funext op; simp
      rw [this]; exact hm
    rw [hidc, hidc]
    exact B hnot'

/-- **Reclaim chooses only safe cuts, for PE** (bergdb 030-24): for every history
PE writes, with Java's still-dirty test and the marking, policies that read no
cut stream, and cuts whose iterations meet `IterationOK` (with a key live at
each iteration's end, the end at most the first available time, and Java's
two waits), Java's get and scan after the run with handles, evictions and
restarts from the cut streams are right at every time from the first
available time on. -/
theorem pe_reclaim_reads (hcf : cf.Ok) (hcap : cf.topBase ≤ 2 ^ 62) {txs : List (List Op)}
    {h : BHist} {top : Nat → Top} (hlen : txs.length < 2 ^ 48 - 1)
    (hk : ∀ ops ∈ txs, (ops.map Op.key).Nodup) (hh : peHist cf txs = some (h, top))
    (hM : 1 ≤ cf.params.M)
    (al : SIS.Algo SIS.Check.BVal Nat) (hj : al.stillDirty = SIS.javaTest h.spec)
    (hmk : al.mark = true) (hpol : SIS.PolicyCutOK al)
    (cs : List (Nat × Option Nat × List SIS.HCacheOp)) (hcs : cs.map (·.1) = h.ts)
    (hit : CutsMeetIter h al cs)
    (hreads : ∀ j (hjl : j < cs.length), cs[j].2.1 = none → ∀ t,
      SIS.HCacheOp.read t ∈ cs[j].2.2 →
      SIS.lastFa (SIS.run h.spec al ((cs.map (·.1)).take (j + 1))).S ≤ t ∧ t ≤ j + 1)
    {t : Nat} (hft : SIS.lastFa (SIS.run h.spec al h.ts).S ≤ t) (htn : t ≤ h.txs.length)
    (mid : Bool) (s : Tree) (tp : Top) :
    let V := SIS.view h.spec (SIS.runHandlesCut h.spec al cs).1.P t
    HoldsView V (kindOf (peKind cf) V) t s →
      TopFrom (SIS.lastFa (SIS.run h.spec al h.ts).S) (top h.txs.length) tp →
      JReadsRight s tp t mid (h.txs.map (·.ops)) := by
  have hM' : 1 ≤ cf.params.M := hM
  exact pe_reclaim_reads_of_valNew hcf hcap hlen hk hh hM' (pe_valNew hcf hcap hlen hk hh) al hj
    hmk hpol cs hcs hit hreads hft htn mid s tp

end Contract.PE
