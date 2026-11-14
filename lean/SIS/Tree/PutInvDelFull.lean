import SIS.Tree.PutInvRun
import SIS.Tree.WriterTreePut2

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! `PutInv` kept by a delete into a full segment leaf (bergdb 024-12, TP10):
the leaf, which keeps a live klong, full by its size or by its dead klongs
with the bitmap, is replaced by its last version without the key's klong, by a
time split (in place for a leaf that the transaction made, else a new node
that its inner parent's klong names), the merges off. -/

/-- A delete of a key whose prefix is there, below an inner segment root:
after the descent the writer runs the upward delete at the leaf L, from a
state that reads as w, with the access path ending at L's parent q and L. -/
theorem writerWP_del_seg_leaf (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv : Nat) (rk : NodeId) (w : W)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false)
    (hidn : ∀ z, (w.nodes.lookup z).isSome = true → z < w.next)
    (hidv : ∀ z, (c.view z).isSome = true → z < w.next)
    (hinner : ∀ m, wNode c.p base w rk = some m → m.leaf = false)
    (post : Bool → W → Prop)
    (hk : ∀ L n q qn k1 d' (w3 : W), (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      (q, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w q = some qn → qn.leaf = false → (k1, L) ∈ qn.liveAt c.i → q ≠ L →
      ReadsAs c.p base w w3 →
      w3.nodes.lookup L = some n → w3.nodes.lookup q = some qn →
      (∀ z, (w3.nodes.lookup z).isSome = true → z < w.next) →
      (w3.path[d']?).map (·.2) = some q → w3.path[d' + 1]? = some (some k1, L) →
      w3.path.length - 1 = d' + 1 →
      WriterWP (do
        let noop ← deleteUpward L (d' + 1) cv (pre ++ [cv])
        if !noop then do let _ ← fresh; pure noop else pure noop) c w3 post) :
    WriterWP (putKv (.del (pre ++ [cv]))) c w post := by
  unfold putKv pathClear findRoot pathAdd
  wpSimplify
  generalize hw2 : ({ ({ w with path := [] } : W) with
    path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w2
  have hr02 : ReadsAs c.p base w w2 := by subst hw2; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hw2n : w2.nodes = w.nodes := by subst hw2; rfl
  refine writerWP_putSegs_prefix_src c base hvc (pre ++ [cv]) none cv _ pre w.top.rootKey rk w2
    (by rw [hr02.1, hr02.2.2.1]; exact ht) (by rw [hr02.1]; exact hrk) (by subst hw2; simp) ?_
  intro w2' hr2' hp2' hsrc2'
  have hr0 := ReadsAs.trans _ _ _ _ _ hr02 hr2'
  unfold setValue
  wpSimplify
  have ht2 : ∀ q ∈ eqVisits (wNode c.p base w2') c.i cv c.p.fuel rk,
      w2'.taken.contains q.1 = false := by
    rw [hr0.1, hr0.2.2.1]
    exact fun q hq => ht q (fromVisits_append _ _ _ pre cv _ rk hrk q hq)
  refine writerWP_mono (writerWP_and
    (writerWP_descendLte_path cv c base hvc c.p.fuel rk w2' ht2 hp2')
    (writerWP_descendLte_cache cv c base hvc c.p.fuel rk w2' ht2)) ?_
  intro L w3 ⟨⟨hr23, n, hn, hnl, hlk3, hvisL, _, hdp⟩, ⟨hcache3, hsrc3, _⟩⟩
  rw [hr0.1] at hn hvisL hcache3
  have hr03 := ReadsAs.trans _ _ _ _ _ hr0 hr23
  rcases hdp with ⟨hLrk, _⟩ | ⟨pre', q, k1, qn, fd, hp3, hlast, hq, hql, hqs, hc, hy, hqv⟩
  · subst hLrk
    rw [hinner n hn] at hnl
    cases hnl
  rw [hr0.1] at hq hqv
  have hsrcw3 : ∀ z, (w3.nodes.lookup z).isSome = true → z < w.next := by
    intro z hz
    rcases hsrc3 z hz with h1 | h1
    · rcases hsrc2' z h1 with h2 | h2
      · rw [hw2n] at h2; exact hidn z h2
      · exact hidv z h2
    · exact hidv z h1
  have hne : w2'.path ++ pre' ≠ [] := by
    intro he
    have : w2'.path = [] := (List.append_eq_nil_iff.mp he).1
    rw [this] at hp2'
    simp at hp2'
  obtain ⟨d', hd'⟩ : ∃ d', (w2'.path ++ pre').length = d' + 1 := by
    cases h' : (w2'.path ++ pre').length with
    | zero => exact absurd (List.eq_nil_of_length_eq_zero h') hne
    | succ k => exact ⟨k, rfl⟩
  have hlen : w3.path.length - 1 = d' + 1 := by
    rw [hp3]; simp only [List.append_assoc, List.length_append, List.length_singleton] at hd' ⊢
    omega
  have hpq : (w3.path[d']?).map (·.2) = some q := by
    rw [hp3, List.append_assoc, ← List.append_assoc w2'.path pre' [(some k1, L)],
      List.getElem?_append_left (by omega)]
    rw [List.getLast?_eq_getElem?] at hlast
    rw [hd'] at hlast
    simpa using hlast
  have hpk : w3.path[d' + 1]? = some (some k1, L) := by
    rw [hp3, List.append_assoc, ← List.append_assoc w2'.path pre' [(some k1, L)],
      List.getElem?_append_right (by omega), hd']
    simp
  have hlq : w3.nodes.lookup q = some qn := hcache3 q qn hqv hq
  have hqL : q ≠ L := by
    intro hqL'
    rw [hqL'] at hq
    rw [hn] at hq
    cases hq
    rw [hnl] at hql
    cases hql
  have hk1 : (k1, L) ∈ qn.liveAt c.i := by
    have := KNode.searchLte_mem qn c.i cv fd hqs
    rw [hc, hy] at this
    exact this
  simp only [pathSize, writerWP_bind, writerWP_get, writerWP_pure]
  rw [hlen]
  have := hk L n q qn k1 d' w3 hvisL hn hnl hqv hq hql hk1 hqL hr03 (by simpa using hlk3) hlq hsrcw3
    hpq hpk hlen
  simpa only [writerWP_bind] using this

theorem writerWP_replaceOrAdd_nil (last : KNode) (c : Ctx) (w : W) :
    WriterWP (replaceOrAdd last []) c w (fun out v => v = w ∧ out = last) := by
  unfold replaceOrAdd
  simp only [List.foldlM_nil, writerWP_bind, writerWP_read, writerWP_pure]
  exact ⟨trivial, trivial⟩

/-- The time split of a node L that existed before the transaction, with
nothing to insert and a last version `last` given, below an inner parent q with
room: a new node at the next id holds `last`, q's klong k1 names it, L keeps
its klongs before the transaction. -/
theorem writerWP_handleFullWith_timeSplit_nil (d' : Nat) (L q : NodeId) (n qn last : KNode)
    (k1 : Nat) (compact : Bool) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hlq : w.nodes.lookup q = some qn)
    (hqL : q ≠ L) (hql : qn.leaf = false) (hfirst : n.firstTime ≠ some c.i)
    (hcs : (!compact && decide (last.size > c.p.splitAbove)) = false)
    (hpq : (w.path[d']?).map (·.2) = some q) (hpk : w.path[d' + 1]? = some (some k1, L))
    (hroomq : qn.size + 1 + 1 ≤ c.p.M) (hdeadq : ∀ y, deadOver c.p (qn.add c.i (.key k1 y)) = false)
    (hny : w.nodes.lookup w.next = none) :
    WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) L [] last compact) c w
      (fun _ w' => w'.taken = w.taken ∧ w'.top = w.top ∧
        ∀ x, w'.nodes.lookup x =
          if x = L then some (n.toPrev (c.i - 1))
          else if x = q then some (qn.add c.i (.key k1 w.next))
          else if x = w.next then some ⟨n.leaf, last.ks⟩
          else w.nodes.lookup x) := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w hlk]
  refine writerWP_ghOf_cached L n c w hlk _ (fun gh => ?_)
  have hnew : (n.firstTime == some c.i) = false := by simpa using hfirst
  simp only [hnew]
  unfold parentAt pathNode
  simp only [writerWP_bind, writerWP_get]
  cases hp : w.path[d']? with
  | none => rw [hp] at hpq; cases hpq
  | some e =>
    rw [hp] at hpq
    simp only [Option.map_some, Option.some.injEq] at hpq
    simp only [writerWP_pure]
    rw [hpq]
    simp only [writerWP_bind]
    rw [writerWP_getNode_known q qn c w hlq]
    simp only [writerWP_pure, hql, hcs, Bool.false_eq_true, ↓reduceIte]
    have hfinal : ∀ w2 : W, w2.taken = w.taken → w2.top = w.top →
        w2.nodes = upsert (w.nodes ++ [(w.next, { leaf := n.leaf, ks := last.ks })]) q
          (qn.add c.i (.key k1 w.next)) →
        WriterWP (do let n ← getNode L; putNode L (n.toPrev (c.i - 1))) c w2
          (fun _ w' => w'.taken = w.taken ∧ w'.top = w.top ∧
            ∀ x, w'.nodes.lookup x =
              if x = L then some (n.toPrev (c.i - 1))
              else if x = q then some (qn.add c.i (.key k1 w.next))
              else if x = w.next then some ⟨n.leaf, last.ks⟩
              else w.nodes.lookup x) := by
      intro w2 h2t h2top h2n
      have hlk2 : w2.nodes.lookup L = some n := by
        rw [h2n, lookup_upsert, if_neg (fun h => hqL h.symm), List.lookup_append, hlk]
        rfl
      simp only [writerWP_bind]
      rw [writerWP_getNode_known L n c w2 hlk2]
      simp only [putNode, writerWP_modify]
      refine ⟨h2t, h2top, ?_⟩
      intro x
      rw [lookup_upsert, h2n, lookup_upsert]
      by_cases hxL : x = L
      · simp [hxL]
      · simp only [hxL, ↓reduceIte]
        by_cases hxq : x = q
        · simp [hxq]
        · simp only [hxq, ↓reduceIte, List.lookup_append]
          by_cases hxy : x = w.next
          · subst hxy; rw [hny]; simp [List.lookup]
          · simp only [hxy, ↓reduceIte]
            cases h : w.nodes.lookup x with
            | some m => rfl
            | none =>
              show (none : Option KNode).or ([(w.next, { leaf := n.leaf, ks := last.ks })].lookup x) = none
              rw [lookup_cons_ne _ _ _ _ hxy]; rfl
    split
    · simp only [note, writerWP_bind, writerWP_modify]
      refine writerWP_mono (writerWP_replaceOrAdd_nil last c _) ?_
      rintro l w1 ⟨hw1, hl⟩
      subst w1 hl
      split <;>
      · simp only [newKey, fresh, setMadeFor, klongAt, note, writerWP_bind, writerWP_modify,
          writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
        split <;>
        · simp only [writerWP_bind, writerWP_modify, writerWP_pure, hpk]
          refine writerWP_mono (writerWP_appendKlongs_room d' q qn k1 w.next c _
            (by simp [List.lookup_append, hlq]) hroomq (hdeadq _)) ?_
          intro _ w2 hw2
          subst hw2
          exact hfinal _ rfl rfl rfl
    · simp only [writerWP_bind]
      refine writerWP_mono (writerWP_replaceOrAdd_nil last c _) ?_
      rintro l w1 ⟨hw1, hl⟩
      subst w1 hl
      split <;>
      · simp only [newKey, fresh, setMadeFor, klongAt, note, writerWP_bind, writerWP_modify,
          writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
        split <;>
        · simp only [writerWP_bind, writerWP_modify, writerWP_pure, hpk]
          refine writerWP_mono (writerWP_appendKlongs_room d' q qn k1 w.next c _
            (by simp [List.lookup_append, hlq]) hroomq (hdeadq _)) ?_
          intro _ w2 hw2
          subst hw2
          exact hfinal _ rfl rfl rfl

/-- The time split in place of a node L that the transaction made, with nothing
to insert and a last version `last` given: L holds `last`. -/
theorem writerWP_handleFullWith_timeInPlace_nil (up : NodeId → List (Nat × NodeId) → M Unit)
    (depth : Nat) (L : NodeId) (n last : KNode) (compact : Bool)
    (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base) (w : W)
    (hlk : w.nodes.lookup L = some n) (hLt : w.taken.contains L = false)
    (hfirst : n.firstTime = some c.i)
    (hcs : (!compact && decide (last.size > c.p.splitAbove)) = false) :
    WriterWP (handleFullWith up depth L [] last compact) c w (fun _ w' =>
        w'.taken = w.taken ∧ w'.top = w.top ∧
        ∀ y, wNode c.p base w' y = if y = L then some ⟨n.leaf, last.ks⟩ else wNode c.p base w y) := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w hlk]
  refine writerWP_ghOf_cached L n c w hlk _ (fun gh => ?_)
  have hnew : (n.firstTime == some c.i) = true := by simp [hfirst]
  simp only [hnew]
  have hpar : WriterWP (parentAt depth) c w (fun _ v => v = w) := by
    unfold parentAt pathNode
    cases depth with
    | zero => simp only [writerWP_pure]
    | succ e =>
      simp only [writerWP_bind, writerWP_get]
      split
      · simp only [writerWP_pure]
      · exact writerWP_throw _ _ _ _
  refine writerWP_mono hpar ?_
  intro a w1 hw1
  subst w1
  have hrest : ∀ w2 : W, ReadsAs c.p base w w2 → w2.nodes.lookup L = some n →
      WriterWP (do
        let l ← replaceOrAdd last []
        if (l.size == 1) = true then do
            note "lone-time-klong"
            putNode L { leaf := n.leaf, ks := l.ks }
          else putNode L { leaf := n.leaf, ks := l.ks }) c w2 (fun _ w' =>
        w'.taken = w.taken ∧ w'.top = w.top ∧
        ∀ y, wNode c.p base w' y = if y = L then some ⟨n.leaf, last.ks⟩ else wNode c.p base w y) := by
    intro w2 hr2 _
    simp only [writerWP_bind]
    refine writerWP_mono (writerWP_replaceOrAdd_nil last c _) ?_
    rintro l w3 ⟨hw3, hl⟩
    subst hw3 hl
    split <;>
    · simp only [note, putNode, writerWP_bind, writerWP_modify]
      refine ⟨hr2.2.2.1, hr2.2.1, ?_⟩
      intro y
      by_cases hy : y = L
      · subst hy
        simp only [wNode, hr2.2.2.1, hLt, Bool.false_eq_true, ↓reduceIte, lookup_upsert]
      · rw [← hr2.1]
        simp only [wNode, lookup_upsert, hy, ↓reduceIte]
  simp only [note, writerWP_bind] at hrest
  cases compact with
  | true =>
    simp only [↓reduceIte, note, Bool.not_true, Bool.false_and, Bool.false_eq_true]
    cases a with
    | none =>
      simp only [writerWP_bind, writerWP_pure, writerWP_modify]
      exact hrest _ ⟨rfl, rfl, rfl, rfl, rfl⟩ hlk
    | some q =>
      simp only [writerWP_bind, writerWP_pure, writerWP_modify]
      refine writerWP_mono (writerWP_and (writerWP_getNode_reads q c w base hvc)
        (writerWP_getNode_cache2 q c w)) ?_
      rintro qn w2 ⟨⟨hr2, _, _⟩, ⟨hpre2, _⟩⟩
      have hlk2 : w2.nodes.lookup L = some n := by
        obtain ⟨t, ht⟩ := hpre2
        rw [← ht, List.lookup_append, hlk]; rfl
      exact hrest _ ⟨hr2.1, hr2.2.1, hr2.2.2.1, hr2.2.2.2.1, hr2.2.2.2.2⟩ hlk2
  | false =>
    simp only [Bool.not_false, Bool.true_and] at hcs
    simp only [hcs, ↓reduceIte, note, Bool.not_false, Bool.true_and, Bool.false_eq_true]
    cases a with
    | none =>
      simp only [writerWP_bind, writerWP_pure, writerWP_modify]
      exact hrest _ ⟨rfl, rfl, rfl, rfl, rfl⟩ hlk
    | some q =>
      simp only [writerWP_bind, writerWP_pure, writerWP_modify]
      refine writerWP_mono (writerWP_and (writerWP_getNode_reads q c w base hvc)
        (writerWP_getNode_cache2 q c w)) ?_
      rintro qn w2 ⟨⟨hr2, _, _⟩, ⟨hpre2, _⟩⟩
      have hlk2 : w2.nodes.lookup L = some n := by
        obtain ⟨t, ht⟩ := hpre2
        rw [← ht, List.lookup_append, hlk]; rfl
      exact hrest _ ⟨hr2.1, hr2.2.1, hr2.2.2.1, hr2.2.2.2.1, hr2.2.2.2.2⟩ hlk2

/-- The last version of a node without compare value cv: n's live klongs but
cv's, at time t. -/
theorem delLast_facts (n : KNode) (t : Time) (cv : Nat) :
    let last := n.lastVersionGivenDel t (bitsUnion n.lastBitmap (n.bitsOf cv))
    (⟨n.leaf, last.ks⟩ : KNode) = last ∧ (∀ s, Klong.time s ∈ last.ks → s ≤ t) ∧
    ∀ c' z, (c', z) ∈ last.live → (c', z) ∈ n.live := by
  intro last
  refine ⟨rfl, flatAt_times t _ (KNode.lastVersionGivenDel_flatAt n t _), ?_⟩
  intro c' z hz
  have hl := lookup_of_mem_nodup _ (KNode.live_keys_nodup _) c' z hz
  rw [KNode.delete_live_lookup] at hl
  by_cases hc : c' = cv
  · subst hc; simp at hl
  · have hb : (c' == cv) = false := by simpa using hc
    rw [hb] at hl
    simp only [Bool.false_eq_true, ↓reduceIte] at hl
    exact lookup_some_mem hl

/-- A delete's bitmap in a segment leaf L below an inner parent q with room,
L keeping a live klong: by the bitmap, or, full, by a time split of L's last
version without the key (in place for a leaf the transaction made), the parts
about the tree are kept. -/
theorem writerWP_appendDeleteKlong_putInvT (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (w w3 : W) (hI : PutInv c base w) (cv k1 d' : Nat) (rk L q : NodeId) (n qn : KNode)
    (hrrk : ReachS (wNode c.p base w) c.i w.top.rootKey rk)
    (hL : (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk) (hLrk : L ≠ rk)
    (hn : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (hqv : (q, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk)
    (hqn : wNode c.p base w q = some qn) (hql : qn.leaf = false) (hk1 : (k1, L) ∈ qn.liveAt c.i)
    (hqL : q ≠ L) (hr3 : ReadsAs c.p base w w3)
    (hlk3 : w3.nodes.lookup L = some n) (hlq3 : w3.nodes.lookup q = some qn)
    (hsrc3 : ∀ z, (w3.nodes.lookup z).isSome = true → z < w.next)
    (hpq : (w3.path[d']?).map (·.2) = some q) (hpk : w3.path[d' + 1]? = some (some k1, L))
    (hne : bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap)
    (hsplit : c.p.M ≤ n.size + 1 →
      (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))).size ≤ c.p.splitAbove)
    (hroomq : qn.size + 1 + 1 ≤ c.p.M) (hdeadq : ∀ y, deadOver c.p (qn.add c.i (.key k1 y)) = false) :
    WriterWP (appendDeleteKlong L (d' + 1) cv) c w3 (fun _ w4 => PutInvT c base w4) := by
  have hLt : w.taken.contains L = false := (wNode_cases _ _ _ _ _ hn).1
  have hqt : w.taken.contains q = false := (wNode_cases _ _ _ _ _ hqn).1
  have hnt := hI.times L n hn
  have hnwf := hI.wf L n hn
  have hrq : ReachS (wNode c.p base w) c.i w.top.rootKey q :=
    eqVisits_reach _ _ _ cv c.p.fuel rk q cv hrrk hqv
  have hk1l : (k1, L) ∈ qn.live := by
    rw [← KNode.liveAt_of_times qn c.i (hI.times q qn hqn)]; exact hk1
  have hnext3 : w3.next = w.next := hr3.2.2.2.2
  obtain ⟨hleq, hlt, hlsub⟩ := delLast_facts n c.i cv
  generalize hU : bitsUnion n.lastBitmap (n.bitsOf cv) = U at hne hsplit hleq hlt hlsub
  generalize hlast : n.lastVersionGivenDel c.i U = last at hleq hlt hlsub hsplit
  -- the outcome of a time split of the full leaf
  have htime0' : ∀ (compact : Bool), (!compact && decide (last.size > c.p.splitAbove)) = false →
      ∀ (s : String), WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) L [] last
        compact) c ({ w3 with trail := s :: w3.trail } : W) (fun _ w4 => PutInvT c base w4) := by
    intro compact hcs s
    generalize hw3' : ({ w3 with trail := s :: w3.trail } : W) = w3'
    have hlk3' : w3'.nodes.lookup L = some n := by rw [← hw3']; exact hlk3
    have hlq3' : w3'.nodes.lookup q = some qn := by rw [← hw3']; exact hlq3
    have hsrc3' : ∀ z, (w3'.nodes.lookup z).isSome = true → z < w.next := by rw [← hw3']; exact hsrc3
    have hpq' : (w3'.path[d']?).map (·.2) = some q := by rw [← hw3']; exact hpq
    have hpk' : w3'.path[d' + 1]? = some (some k1, L) := by rw [← hw3']; exact hpk
    have hr3' : ReadsAs c.p base w w3' := by rw [← hw3']; exact hr3
    have hnext3' : w3'.next = w.next := hr3'.2.2.2.2
    by_cases hnew : n.firstTime = some c.i
    · refine writerWP_mono (writerWP_handleFullWith_timeInPlace_nil _ (d' + 1) L n last compact c
        base hvc w3' hlk3' (by rw [hr3'.2.2.1]; exact hLt) hnew hcs) ?_
      intro _ w4 ⟨h4t, h4top, hN4⟩
      rw [hleq] at hN4
      refine putInvT_shrink c base w w4 hI L n last hn (by rw [← hleq]) hlt hlsub
        (h4t.trans hr3'.2.2.1) (h4top.trans hr3'.2.1) (by rw [hN4]; simp) ?_
      intro y hy; rw [hN4]; simp only [hy, ↓reduceIte]; rw [hr3'.1]
    · have hny : w3'.nodes.lookup w3'.next = none := by
        cases h' : w3'.nodes.lookup w3'.next with
        | none => rfl
        | some _ => have := hsrc3' _ (by rw [h']; rfl); omega
      refine writerWP_mono (writerWP_handleFullWith_timeSplit_nil d' L q n qn last k1 compact c w3'
        hlk3' hlq3' hqL hql hnew hcs hpq' hpk' hroomq hdeadq hny) ?_
      intro _ w4 ⟨h4t, h4top, h4nodes⟩
      rw [hnext3', hleq] at h4nodes
      have htk : w4.taken = w.taken := h4t.trans hr3'.2.2.1
      have hyt : w.taken.contains w.next = false := hI.untaken_of_ge _ (Nat.le_refl _)
      have hLy : L ≠ w.next := by have := hI.lt_next L n hn; omega
      have hqy : q ≠ w.next := by have := hI.lt_next q qn hqn; omega
      refine putInvT_timeSplit c base w w4 hI cv k1 (w.next + 2) w.next L q n qn last (by omega)
        (Nat.le_refl _) (by omega) hn hnl hqn hql hrq hk1l htk (h4top.trans hr3'.2.1) ?_ ?_ ?_
        (by rw [← hleq]; exact hnl) hlt (fun c' z h => Or.inr (hlsub c' z h)) ?_
        (parentBound_of_descent c base w hI cv rk L hrrk hL hLrk q qn k1 hrq hqn hk1l)
      · simp only [wNode, htk, hLt, Bool.false_eq_true, ↓reduceIte, h4nodes]
      · simp only [wNode, htk, hqt, Bool.false_eq_true, ↓reduceIte, h4nodes, hqL]
      · simp only [wNode, htk, hyt, Bool.false_eq_true, ↓reduceIte, h4nodes, hLy.symm, hqy.symm]
      · intro x hxL hxq hxy
        rw [← hr3'.1]
        simp only [wNode, htk, hr3'.2.2.1, h4nodes, hxL, hxq, hxy, ↓reduceIte]
  -- the bitmap in L: a node that loses live klongs only
  have hshrink : ∀ (n' : KNode) (s : String), n'.leaf = n.leaf →
      (∀ t, Klong.time t ∈ n'.ks → t ≤ c.i) → (∀ c' z, (c', z) ∈ n'.liveAt c.i → (c', z) ∈ n.liveAt c.i) →
      WriterWP (do note s; putNode L n'; pure false) c w3 (fun _ w4 => PutInvT c base w4) := by
    intro n' s hl' ht' hsub
    simp only [note, putNode, writerWP_bind, writerWP_modify, writerWP_pure]
    refine putInvT_shrink c base w _ hI L n n' hn hl' ht' ?_ hr3.2.2.1 hr3.2.1 ?_ ?_
    · intro c' z hz
      have h1 : (c', z) ∈ n'.liveAt c.i := by rw [KNode.liveAt_of_times _ c.i ht']; exact hz
      have := hsub c' z h1
      rwa [KNode.liveAt_of_times _ c.i hnt] at this
    · simp only [wNode, hr3.2.2.1, hLt, Bool.false_eq_true, ↓reduceIte, lookup_upsert]
    · intro y hy
      rw [← hr3.1]
      simp only [wNode, lookup_upsert, hy, ↓reduceIte]
  have hsetAt : ∀ old, n.ks.getLast? = some (.del old) → ∀ c' z,
      (c', z) ∈ (n.setAt (n.size - 1) (.del U)).liveAt c.i → (c', z) ∈ n.liveAt c.i := by
    intro old hold c' z hm
    rw [← hU] at hm
    exact (liveAt_sub_of_lookup n _ c.i cv hnt (KNode.setAt_last_del_times n c.i old _ hold hnt)
      (fun c'' => n.setAt_delete_live_lookup cv c'' old hold) c' z hm).2
  have hadd : ∀ c' z, (c', z) ∈ (n.add c.i (.del U)).liveAt c.i → (c', z) ∈ n.liveAt c.i := by
    intro c' z hm
    rw [← hU] at hm
    exact (liveAt_sub_of_lookup n _ c.i cv hnt (KNode.add_times n c.i _ (fun s h => by cases h) hnt)
      (fun c'' => n.add_delete_live_lookup c.i cv c'') c' z hm).2
  have haddt := KNode.add_times n c.i (.del U) (fun s h => by cases h) hnt
  unfold appendDeleteKlong handleFull
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w3 hlk3]
  split
  · exact writerWP_throw _ _ _ _
  · rw [hU, hlast]
    have hnb : (U == n.lastBitmap) = false := by simpa using hne
    simp only [hnb, Bool.not_false, ↓reduceIte]
    have htime : ∀ (compact : Bool) (s : String), (!compact && decide (last.size > c.p.splitAbove)) = false →
        WriterWP (do note s; handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) L [] last compact; pure false)
          c w3 (fun _ w4 => PutInvT c base w4) := by
      intro compact s hcs
      simp only [note, writerWP_bind, writerWP_modify]
      exact writerWP_mono (htime0' compact hcs s) (fun _ w4 h => by simp only [writerWP_pure]; exact h)
    have hrest : ¬ ((∃ old, n.ks.getLast? = some (.del old)) ∧ n.lastTime = some c.i) →
        WriterWP (if n.size + 1 < c.p.M then
          if deadOver c.p (n.add c.i (Klong.del U)) = true then do
            note "bitmap.dead"
            handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) L [] last true
            pure false
          else do
            note "bitmap.new"
            putNode L (n.add c.i (Klong.del U))
            pure false
        else do
          note "bitmap.full"
          handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) L [] last
          pure false) c w3 (fun _ w4 => PutInvT c base w4) := by
      intro _
      by_cases hsz : n.size + 1 < c.p.M
      · rw [if_pos hsz]
        by_cases hd : deadOver c.p (n.add c.i (Klong.del U)) = true
        · rw [if_pos hd]; exact htime true _ (by simp)
        · rw [if_neg hd]; exact hshrink _ _ (KNode.add_leaf _ _ _) haddt hadd
      · rw [if_neg hsz]
        apply htime false
        have h1 : c.p.M ≤ n.size + 1 := by omega
        have h2 := hsplit h1
        simp only [Bool.not_false, Bool.true_and, decide_eq_false_iff_not, gt_iff_lt, Nat.not_lt]
        exact h2
    cases hg : n.ks.getLast? with
    | none =>
      simp only [hg, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      exact hrest (fun ⟨⟨old, h⟩, _⟩ => by rw [hg] at h; cases h)
    | some k =>
      cases k with
      | del old =>
        cases hlt : (n.lastTime == some c.i) with
        | false =>
          simp only [hg, hlt, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
          exact hrest (fun ⟨_, h⟩ => by simp [h] at hlt)
        | true =>
          simp only [hg, hlt, Bool.and_self, ↓reduceIte]
          by_cases hd : deadOver c.p (n.setAt (n.size - 1) (Klong.del U)) = true
          · rw [if_pos hd]; exact htime true _ (by simp)
          · rw [if_neg hd]
            exact hshrink _ _ (KNode.setAt_leaf _ _ _) (KNode.setAt_last_del_times n c.i old _ hg hnt)
              (hsetAt old hg)
      | _ =>
        simp only [hg, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        exact hrest (fun ⟨⟨old, h⟩, _⟩ => by rw [hg] at h; cases h)

/-- A delete of a key whose prefix is there, below an inner segment root and an
inner parent with room, by a bitmap in its segment leaf, which keeps a live
klong, the merges off, keeps `PutInv` (the writer's tree after it given): with
room for the bitmap, or the leaf full by its size or by its dead klongs, time
split (in place for a leaf the transaction made) when its last version without
the key has at most h klongs. -/
theorem putInv_del_leafBelow (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (pre : List Nat) (cv : Nat) (rk : NodeId) (w : W)
    (hI : PutInv c base w) (hw : PutBook c B top0 w) (hmerges : c.p.merges = false)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hinner : ∀ m, wNode c.p base w rk = some m → m.leaf = false)
    (hleaf : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
      n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = false ∧
      (c.p.M ≤ n.size + 1 →
        (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))).size ≤ c.p.splitAbove))
    (hparent : ∀ q qn, (q, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w q = some qn → qn.leaf = false →
      qn.size + 1 + 1 ≤ c.p.M ∧ ∀ k y, deadOver c.p (qn.add c.i (.key k y)) = false) :
    WriterWP (putKv (.del (pre ++ [cv]))) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey → PutInv c base w') := by
  apply writerWP_putInv_of_T c base B top0 _ w hB hw
  have hrrk : ReachS (wNode c.p base w) c.i w.top.rootKey rk :=
    segRootR_reach _ _ _ _ (fun x xn _ hn => hI.wf x xn hn) pre _ rk ReachS.root hrk
  have ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false := fun q hq =>
    hI.untaken q.1 (fromVisits_reach _ _ _ _ (fun x xn _ hn => hI.wf x xn hn) _ _ q.1 q.2
      ReachS.root hq)
  apply writerWP_del_seg_leaf c base hB.coherent pre cv rk w hrk ht hI.ids.1 hI.ids.2.1 hinner
  intro L n q qn k1 d' w3 hL hn hnl hqv hqn hql hk1 hqL hr3 hlk3 hlq3 hsrc3 hpq hpk _
  obtain ⟨hne, hkeep, hsplit⟩ := hleaf L n hL hn hnl
  obtain ⟨hroomq, hdeadq⟩ := hparent q qn hqv hqn hql
  have hLrk : L ≠ rk := by
    intro he; subst he; rw [hinner n hn] at hnl; cases hnl
  unfold deleteUpward
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c _ hlk3]
  have hnb : (bitsUnion n.lastBitmap (n.bitsOf cv) == n.lastBitmap) = false := by
    simpa using hne
  simp only [hnb, Bool.false_eq_true, ↓reduceIte, hkeep, Bool.not_false]
  wpSimplify
  refine writerWP_ghOf_cached L n c _ hlk3 _ (fun gh => ?_)
  refine writerWP_mono (writerWP_appendDeleteKlong_putInvT c base hB.coherent w w3 hI cv k1 d' rk L q
    n qn hrrk hL hLrk hn hnl hqv hqn hql hk1 hqL hr3 hlk3 hlq3 hsrc3 hpq hpk hne hsplit hroomq
    (hdeadq k1)) ?_
  intro _ w4 hT4
  unfold afterDelete fresh
  wpSimplify
  simp only [hmerges, Bool.false_eq_true, ↓reduceIte, writerWP_pure]
  simp only [Bool.not_false, ↓reduceIte, writerWP_bind, writerWP_get, writerWP_set, writerWP_pure]
  exact hT4

end SIS.Tree
