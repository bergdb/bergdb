/-
Proofs about the physical layer with handles (bergdb item 009, phase 4a): T-PIN
over handles (`tp_handles`, `TP_handles` of SIS/HandleTheorems.lean). In every
state of a run with
handles and restarts, the object of a live handle outside the pinned set has a
position: a canonical one is of a node not in D, and not the root, which is
clean and reachable at some time, so it has been written and its latest version
is the object's position; a snapshot is the version at its position. So the
handle may be evicted, and one eviction takes the object out of memory and
kills the handle; nothing is asked of the pointers that hold the handle.
-/
import SIS.Proof.HandleRestart

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

section Pin

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : HMem V}

/-- With the invariant, a live handle whose object is not pinned may be evicted:
the object has a position. -/
theorem HEInv.evictable_of_unpinned (hm : HEInv sp db S0 k m) (hinv : Inv sp db k) (hls : LiveSub sp)
    {n : Nat} {hd : Handle} {a : Nat} (hh : m.handle? n = some hd) (hdead : hd.dead = false)
    (ha : hd.obj = some a) (hp : m.pinned db.D a = false) : m.evictable db.D n = true := by
  obtain ⟨-, ob, hob, -⟩ := hm.tbl.obj_of_handle hh ha
  have hp0 := hp
  unfold HMem.pinned at hp
  rw [hob] at hp
  simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hp
  obtain ⟨hr, hcd⟩ := hp
  have hpos : ob.pos.isSome = true := by
    cases hc : ob.canonical with
    | false =>
      obtain ⟨r, w, hpr, -⟩ := hm.snap a ob hob hc
      rw [hpr]; rfl
    | true =>
      rw [hc, Bool.true_and] at hcd
      have hcan := hm.canonicalOf_of hob hc
      have hxr : ob.node ≠ SIS.root := by
        intro hx
        obtain ⟨o0, ho0, hc0, hn0⟩ := hm.root
        have h1 := hm.canonicalOf_of ho0 hc0
        rw [hn0, ← hx, hcan, Option.some.injEq] at h1
        exact hr h1
      obtain ⟨n', hn, -⟩ := hm.cc a ob hob hc
      obtain ⟨t, ht, hrt⟩ := hinv.born ob.node (by rw [hn]; rfl)
      obtain ⟨v, hv, -⟩ := hinv.clean_good hls hcd (written_of_ne_root sp hxr) ht hrt
      rw [hm.pos a ob hob hc, hv]; rfl
  have hev : m.evictable db.D n = (!m.pinned db.D a && ob.pos.isSome) := by
    unfold HMem.evictable; rw [hh]; simp [hdead, ha, hob]
  rw [hev, hp0, hpos]; rfl

end Pin

/-- `TP_handles` (SIS/HandleTheorems.lean) holds: in a run with handles and
restarts, after any transaction and its operations or its restart, every live
handle whose object is not pinned may be evicted, and one eviction removes the
object and kills the handle. -/
theorem tp_handles (sp : Spec V T) (al : Algo V T) : TP_handles sp al := by
  intro ts hok hla hev hj hmk j hjt r m n hd a hh hdead ha hp
  have hph := physRunOK_of_evict hok hla hev
  obtain ⟨k1, -, -, hrel, hm, -⟩ := handleInvR_all hok hph hev hj hmk j hjt
  have hinv := inv_st sp al (ts.map (·.1)) hok (algOK_of sp al (Or.inl hj)) j
    (by rw [List.length_map]; exact hjt)
  have hD : r.1.D = (st sp al (ts.map (·.1)) j).D := hrel.2.1
  rw [hD] at hp ⊢
  have hev' := hm.evictable_of_unpinned hinv hok.1.liveSub hh hdead ha hp
  refine ⟨hev', ?_, ?_⟩
  · show (m.evict _ n).obj? a = none
    rw [HMem.evict_obj? hev' hh ha]; simp
  · show ((m.evict _ n).handle? n).map (·.dead) = some true
    rw [HMem.evict_handle? hev' hh ha]; simp

end SIS
