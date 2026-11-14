/-
The cascade below a delete's leaf keeps the writer's tree (bergdb 024-22,
`OpTreeOK`): the leaf's time or space split of a last version given (the
delete's, `lastVersionGivenDel`), in place for a leaf the transaction made,
below an inner node or a segment leaf, then the cascade of any kind above it
(`writerWP_appendKlongs_chainG`); also a delete's leaf that is the space root.
-/
import SIS.Tree.WriterTreeChainG
import SIS.Tree.GetCascadePut
import SIS.Tree.PutInvDelRoot

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## The writer's splits of a last version given -/

/-- The writer's time split for a delete (nothing to insert, the last version
`last` given), below a parent of either kind. -/
theorem writerWP_handleFullWith_time_up_last' (d' : Nat) (x q : NodeId) (n qn : KNode) (k1 : Nat)
    (last : KNode) (compact : Bool) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup x = some n) (hlq : w.nodes.lookup q = some qn)
    (hfirst : n.firstTime ≠ some c.i)
    (hcs : (!compact && decide (last.size > c.p.splitAbove)) = false)
    (hpq : (w.path[d']?).map (·.2) = some q) (hpk : w.path[d' + 1]? = some (some k1, x))
    (Q : W → Prop)
    (hup : ∀ w1 : W, w1.nodes = w.nodes ++ [(w.next, ⟨n.leaf, last.ks⟩)] → w1.taken = w.taken →
        w1.top = w.top → w1.path = w.path → w1.next = w.next + 2 → w1.vals = w.vals →
        WriterWP (appendKlongs d' q [(k1, w.next)]) c w1 (fun _ w2 =>
          WriterWP (do let m ← getNode x; putNode x (m.toPrev (c.i - 1))) c w2 (fun _ w3 => Q w3))) :
    WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) x []
      last compact) c w (fun _ w' => Q w') := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c w hlk]
  refine writerWP_ghOf_cached x n c w hlk _ (fun gh => ?_)
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
    simp only [writerWP_pure, hcs, Bool.false_eq_true, ↓reduceIte]
    split
    · simp only [note, writerWP_bind, writerWP_modify]
      refine writerWP_mono (writerWP_replaceOrAdd_nil last c _) ?_
      rintro l w1 ⟨hw1, hl⟩
      subst w1 hl
      split <;>
      · simp only [newKey, fresh, setMadeFor, klongAt, writerWP_bind, writerWP_modify,
          writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
        split <;>
        · simp only [writerWP_bind, writerWP_modify, writerWP_pure, hpk]
          exact hup _ rfl rfl rfl rfl rfl rfl
    · simp only [writerWP_bind]
      refine writerWP_mono (writerWP_replaceOrAdd_nil last c _) ?_
      rintro l w1 ⟨hw1, hl⟩
      subst w1 hl
      split <;>
      · simp only [newKey, fresh, setMadeFor, klongAt, note, writerWP_bind, writerWP_modify,
          writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
        split <;>
        · simp only [writerWP_bind, writerWP_modify, writerWP_pure, hpk]
          exact hup _ rfl rfl rfl rfl rfl rfl

/-- The writer's time split in place of x, made by the transaction, of a last
version given: x holds it. -/
theorem writerWP_handleFullWith_timeInPlace_termL (up : NodeId → List (Nat × NodeId) → M Unit)
    (d' : Nat) (x q : NodeId) (n qn last : KNode) (compact : Bool)
    (c : Ctx) (w : W) (hlk : w.nodes.lookup x = some n) (hlq : w.nodes.lookup q = some qn)
    (hpq : (w.path[d']?).map (·.2) = some q) (hfirst : n.firstTime = some c.i)
    (hcs : (!compact && decide (last.size > c.p.splitAbove)) = false) :
    WriterWP (handleFullWith up (d' + 1) x [] last compact) c w (fun _ w' =>
      w'.taken = w.taken ∧ w'.top = w.top ∧ w'.vals = w.vals ∧ w'.next = w.next ∧
        w'.path = w.path ∧ w'.nodes = upsert w.nodes x ⟨n.leaf, last.ks⟩) := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c w hlk]
  refine writerWP_ghOf_cached x n c w hlk _ (fun gh => ?_)
  have hnew : (n.firstTime == some c.i) = true := by simp [hfirst]
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
    simp only [writerWP_pure, hcs, Bool.false_eq_true, ↓reduceIte, Bool.not_true]
    cases compact with
    | true =>
      simp only [↓reduceIte, note, writerWP_bind, writerWP_modify]
      refine writerWP_mono (writerWP_replaceOrAdd_nil last c _) ?_
      rintro l w3 ⟨hw3, hl⟩
      subst hw3 hl
      split <;>
      · simp only [putNode, writerWP_bind, writerWP_modify, writerWP_pure]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial
    | false =>
      simp only [↓reduceIte, note, writerWP_bind, writerWP_modify, Bool.false_eq_true]
      refine writerWP_mono (writerWP_replaceOrAdd_nil last c _) ?_
      rintro l w3 ⟨hw3, hl⟩
      subst hw3 hl
      split <;>
      · simp only [putNode, writerWP_bind, writerWP_modify, writerWP_pure]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial

/-- `writerWP_handleFullWith_segSpace_up` for a last version `last` given (a delete's). The writer's space split of x, which existed before the transaction, below
a segment leaf q: the halves and a new segment root over them at the next three
ids, then q gets the klong k1 to the new root (`appendKlongs d'`, whatever it
does), then x keeps its klongs before the transaction. -/
theorem writerWP_handleFullWith_segSpace_upL (d' : Nat) (x q : NodeId) (n qn last : KNode) (k1 : Nat)
    (ins : List (Nat × NodeId)) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup x = some n) (hlq : w.nodes.lookup q = some qn)
    (hql : qn.leaf = true) (hfirst : n.firstTime ≠ some c.i)
    (hsplit : c.p.splitAbove < last.size)
    (hpq : (w.path[d']?).map (·.2) = some q) (hpk : w.path[d' + 1]? = some (some k1, x))
    (Q : W → Prop)
    (hup : ∀ w1 : W, (∀ z, w1.nodes.lookup z =
        if z = w.next then some (halves n.leaf c.i last ins).1
        else if z = w.next + 2 then some (halves n.leaf c.i last ins).2.1
        else if z = w.next + 2 + 2 then some ⟨false, [.time c.i, .key 0 w.next,
          .key (halves n.leaf c.i last ins).2.2 (w.next + 2)]⟩
        else w.nodes.lookup z) → w1.taken = w.taken → w1.top = w.top → w1.path = w.path →
        w1.next = w.next + 2 + 2 + 2 → w1.vals = w.vals →
        WriterWP (appendKlongs d' q [(k1, w.next + 2 + 2)]) c w1 (fun _ w2 =>
          WriterWP (do let m ← getNode x; putNode x (m.toPrev (c.i - 1))) c w2 (fun _ w3 => Q w3))) :
    WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) x ins
      last false) c w (fun _ w' => Q w') := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c w hlk]
  refine writerWP_ghOf_cached x n c w hlk _ (fun gh => ?_)
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
    have hsz : decide (last.size > c.p.splitAbove) = true := by
      simp only [decide_eq_true_eq, gt_iff_lt]; exact hsplit
    simp only [writerWP_pure, hql, hsz, Bool.not_false, Bool.true_and, Bool.false_eq_true,
      ↓reduceIte]
    simp only [newKey, fresh, setMadeFor, note, putNode, writerWP_bind, writerWP_modify,
      writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
    split <;>
    · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
      split <;>
      · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
        refine (writerWP_klongAt (d' + 1) k1 x c _ ?_ _).mpr ?_
        · exact hpk
        refine writerWP_mono (hup _ ?_ rfl rfl rfl rfl rfl) ?_
        · intro z
          simp only [lookup_upsert, List.lookup_append]
          by_cases h3 : z = w.next + 2 + 2
          · subst h3
            simp [show w.next + 2 + 2 ≠ w.next by omega]
          · simp only [h3, ↓reduceIte]
            by_cases h2 : z = w.next + 2
            · subst h2; simp
            · simp only [h2, ↓reduceIte]
              by_cases h1 : z = w.next
              · subst h1; simp
              · simp only [h1, ↓reduceIte]
                cases h : w.nodes.lookup z with
                | some m => rfl
                | none =>
                  show (((none : Option KNode).or ([(w.next, { leaf := n.leaf, ks := [] })].lookup z)).or
                    ([(w.next + 2, { leaf := n.leaf, ks := [] })].lookup z)).or
                    ([(w.next + 2 + 2, { leaf := false, ks := [] })].lookup z) = none
                  rw [lookup_cons_ne _ _ _ _ h1, lookup_cons_ne _ _ _ _ h2, lookup_cons_ne _ _ _ _ h3]; rfl
        · intro _ w2 h
          simpa only [Bool.not_false, ↓reduceIte, writerWP_bind, putNode, writerWP_modify] using h

set_option linter.unusedSimpArgs false in
/-- `writerWP_handleFullWith_segSpaceInPlace_term` for a last version `last` given. The writer's space split in place of x, made by the transaction, below a
segment leaf q: x keeps the first half, the second at the next id, a new
segment root over them at the id after, and q's klong of the transaction to x
names the new root in place. -/
theorem writerWP_handleFullWith_segSpaceInPlace_termL (d' : Nat) (x q : NodeId) (n qn last : KNode)
    (k1 : Nat) (ins : List (Nat × NodeId)) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup x = some n) (hlq : w.nodes.lookup q = some qn)
    (hqx : q ≠ x) (hql : qn.leaf = true) (hfirst : n.firstTime = some c.i)
    (hsplit : c.p.splitAbove < last.size)
    (hpq : (w.path[d']?).map (·.2) = some q) (hpk : w.path[d' + 1]? = some (some k1, x))
    (hxn : x < w.next) (hqn : q < w.next)
    (hny : w.nodes.lookup (w.next + 2) = none) :
    WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) x ins
      last false) c w (fun _ w' =>
      ∃ j, qn.linkIndex x k1 = some j ∧
        w'.taken = w.taken ∧ w'.top = w.top ∧ w'.vals = w.vals ∧ w'.path = w.path ∧
        w.next + 2 + 2 ≤ w'.next ∧
        ∀ z, w'.nodes.lookup z =
          if z = x then some (halves n.leaf c.i last ins).1
          else if z = q then some (qn.repoint j (w.next + 2))
          else if z = w.next then some (halves n.leaf c.i last ins).2.1
          else if z = w.next + 2 then some ⟨false, [.time c.i, .key 0 x,
            .key (halves n.leaf c.i last ins).2.2 w.next]⟩
          else w.nodes.lookup z) := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c w hlk]
  refine writerWP_ghOf_cached x n c w hlk _ (fun gh => ?_)
  have hnew : (n.firstTime == some c.i) = true := by simp [hfirst]
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
    have hsz : decide (last.size > c.p.splitAbove) = true := by
      simp only [decide_eq_true_eq, gt_iff_lt]; exact hsplit
    simp only [writerWP_pure, hql, hsz, Bool.not_false, Bool.true_and, Bool.false_eq_true,
      ↓reduceIte]
    have hq1 : q ≠ w.next := by omega
    have hq2 : q ≠ w.next + 2 := by omega
    have hx1 : x ≠ w.next := by omega
    have hx2 : x ≠ w.next + 2 := by omega
    simp only [newKey, fresh, setMadeFor, replacedBy, note, putNode, writerWP_bind, writerWP_modify,
      writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
    split <;>
    · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
      split <;>
      · simp only [writerWP_bind, writerWP_modify, writerWP_pure, writerWP_get, writerWP_set]
        split <;>
        · simp only [writerWP_bind, writerWP_modify, writerWP_pure, writerWP_get, writerWP_set]
          split <;>
          · simp only [writerWP_bind, writerWP_modify, writerWP_pure, writerWP_get, writerWP_set]
            refine (writerWP_klongAt (d' + 1) k1 x c _ ?_ _).mpr ?_
            · exact hpk
            refine (writerWP_getNode_known q qn c _ ?_ _).mpr ?_
            · simp only [lookup_upsert, List.lookup_append, hq1, hq2, hqx, ↓reduceIte, hlq]
              rfl
            split
            · rename_i j hj
              split
              · simp only [writerWP_bind]
                exact writerWP_throw _ _ _ _
              · simp only [writerWP_bind, writerWP_modify, Bool.not_true, Bool.false_eq_true,
                  ↓reduceIte, writerWP_pure]
                refine ⟨j, hj, ?_, ?_, ?_, ?_, ?_, fun z => ?_⟩
                all_goals first | rfl | trivial | (simp only []; omega) | omega | skip
                simp only [lookup_upsert, List.lookup_append]
                by_cases hzx : z = x
                · subst hzx; simp [hqx.symm, hx1, hx2]
                · simp only [hzx, ↓reduceIte]
                  by_cases hzq : z = q
                  · simp [hzq]
                  · simp only [hzq, ↓reduceIte]
                    by_cases h1 : z = w.next
                    · subst h1; simp
                    · simp only [h1, ↓reduceIte]
                      by_cases h2 : z = w.next + 2
                      · subst h2
                        rw [hny]
                        have hb : (w.next + 2 == w.next) = false := by simp
                        simp [List.lookup, hb]
                      · simp only [h2, ↓reduceIte]
                        cases h : w.nodes.lookup z with
                        | some m => rfl
                        | none =>
                          show (((none : Option KNode).or ([(w.next, { leaf := n.leaf, ks := [] })].lookup z)).or
                            ([(w.next + 2, _)].lookup z)) = none
                          rw [lookup_cons_ne _ _ _ _ h1, lookup_cons_ne _ _ _ _ h2]; rfl
            · exact writerWP_throw _ _ _ _

/-! ## The cascade below a delete's leaf -/

/-- The halves of a delete's last version of a leaf (`lastVersionGivenDel`),
h at least 2: the divider r, a live klong of the leaf with a positive compare
value; the first half's links below it, the second half's from it, all of them
the last version's. -/
theorem delLast_halves (n : KNode) (t : Time) (cv sa : Nat) (hleaf : n.leaf = true)
    (hsa2 : 2 ≤ sa) :
    sa < (n.lastVersionGivenDel t (bitsUnion n.lastBitmap (n.bitsOf cv))).size →
    ∃ r : Nat × NodeId, 0 < r.1 ∧ (r.1, r.2) ∈ n.live ∧
      (halves n.leaf t (n.lastVersionGivenDel t (bitsUnion n.lastBitmap (n.bitsOf cv))) []).2.2 =
        r.1 ∧
      (∀ c' z, (c', z) ∈ (halves n.leaf t
          (n.lastVersionGivenDel t (bitsUnion n.lastBitmap (n.bitsOf cv))) []).1.liveAt t →
        c' < r.1 ∧ (c', z) ∈ (⟨n.leaf, (n.lastVersionGivenDel t
          (bitsUnion n.lastBitmap (n.bitsOf cv))).ks⟩ : KNode).liveAt t) ∧
      (∀ c' z, (c', z) ∈ (halves n.leaf t
          (n.lastVersionGivenDel t (bitsUnion n.lastBitmap (n.bitsOf cv))) []).2.1.liveAt t →
        ∃ c0, r.1 ≤ c0 ∧ c' = splitLocalCv n.leaf r.1 c0 ∧ (c0, z) ∈ (⟨n.leaf,
          (n.lastVersionGivenDel t (bitsUnion n.lastBitmap (n.bitsOf cv))).ks⟩ : KNode).liveAt t) := by
  obtain ⟨pairs, hpks, hps⟩ := KNode.lastVersionGivenDel_order n t
    (bitsUnion n.lastBitmap (n.bitsOf cv))
  obtain ⟨hleq, hlt, hlsub⟩ := delLast_facts n t cv
  generalize hlast : n.lastVersionGivenDel t (bitsUnion n.lastBitmap (n.bitsOf cv)) = last
    at hpks hleq hlt hlsub ⊢
  have hlastE : last = ⟨true, newKlongs t pairs⟩ := by
    rw [← hleq, hleaf, hpks]; rfl
  have hpn : (pairs.map Prod.fst).Nodup :=
    List.pairwise_map.mpr (hps.imp (by intro a b hab; omega))
  intro hbig
  have hlen2 : 2 ≤ pairs.length := by
    rw [hlastE] at hbig
    simp [KNode.size, newKlongs] at hbig
    omega
  obtain ⟨r, hr⟩ : ∃ r, (pairs.drop (pairs.length / 2)).head? = some r := by
    cases hd : (pairs.drop (pairs.length / 2)) with
    | nil =>
      have : pairs.length ≤ pairs.length / 2 := List.drop_eq_nil_iff.mp hd
      omega
    | cons a _ => exact ⟨a, rfl⟩
  have hrp : r ∈ pairs := List.mem_of_mem_drop (List.mem_of_head? hr)
  have hr0 : 0 < r.1 := by
    have hsplit := List.take_append_drop (pairs.length / 2) pairs
    have hps' := hps
    rw [← hsplit] at hps'
    have hpa := (List.pairwise_append.mp hps').2.2
    obtain ⟨y, hy⟩ : ∃ y, y ∈ pairs.take (pairs.length / 2) := by
      cases ht : pairs.take (pairs.length / 2) with
      | nil =>
        have := congrArg List.length ht
        simp only [List.length_take, List.length_nil] at this
        omega
      | cons y _ => exact ⟨y, by simp⟩
    have := hpa y hy r (List.mem_of_head? hr)
    omega
  have hrN : (r.1, r.2) ∈ n.live := by
    have h1 : (r.1, r.2) ∈ last.liveAt t := by
      rw [hlastE]; exact (mrg_newKlongs_liveAt_iff true t pairs hpn r.1 r.2).mpr hrp
    rw [KNode.liveAt_of_times last t hlt] at h1
    exact hlsub _ _ h1
  rw [hleaf, hlastE]
  obtain ⟨hscr, hfh, hsh⟩ := halves_nil_links t pairs hps r hr
  obtain ⟨hHt1, hHt2⟩ := halves_nil_times t pairs
  refine ⟨r, hr0, hrN, hscr, ?_, ?_⟩
  · intro c' z h
    rw [KNode.liveAt_of_times _ t hHt1] at h
    obtain ⟨h1, h2⟩ := hfh c' z h
    exact ⟨h1, (mrg_newKlongs_liveAt_iff true t pairs hpn c' z).mpr h2⟩
  · intro c' z h
    rw [KNode.liveAt_of_times _ t hHt2] at h
    obtain ⟨h1, h2⟩ := hsh c' z h
    exact ⟨c', h1, by simp [splitLocalCv], (mrg_newKlongs_liveAt_iff true t pairs hpn c' z).mpr h2⟩

end SIS.Tree
