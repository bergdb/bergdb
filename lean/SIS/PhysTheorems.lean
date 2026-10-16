/-
Self-indexed streams in Lean: the theorems of the physical layer (bergdb item
001, stages 1 and 2). Trusted part: the statements. The proofs are in
SIS/Proof/; the proofs here only connect them.
-/
import SIS.Theorems
import SIS.Proof.Newer
import SIS.Proof.PhysT1

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- Lemma M (bergdb item 001, WP L2; docs/level2-alignment.md, M8). In every
run, after every transaction: if version v of node x is good for time t (5.1),
so is every version w of x written at or after v. Java relies on it when it
reads a node on its first touch after a restart: it takes the newer of the
version that the pointer names and the node's version in the startup section,
or the object it already holds. -/
theorem LM_newer (sp : Spec V T) (al : Algo V T) (ts : List T) (hok : RunOK sp al ts)
    (hst : al.stillDirty = javaTest sp ∨ (sp.virt = false ∧ al.stillDirty = exactTest sp))
    (j : Nat) (hj : j ≤ ts.length) (x : NodeId) (r r' : Nat) (v w : Version V) (t : Time)
    (hv : (run sp al (ts.take j)).S.versionAt r x = some v)
    (hw : (run sp al (ts.take j)).S.versionAt r' x = some w) (hrr : r ≤ r')
    (hg : good sp (run sp al (ts.take j)).S (run sp al (ts.take j)).P t v = true) :
    good sp (run sp al (ts.take j)).S (run sp al (ts.take j)).P t w = true := by
  have hinv := inv_st sp al ts hok (algOK_of sp al hst) j hj
  exact hinv.newer hok.1.liveSub (v.level + 1) r r' x v w (by omega) hv hw hrr t hg

/-- Lemma M with Rule R (WP L2): if a version of y is good for time t, so is
the newest version of y in R(s), ..., R(k), which Rule R follows instead of
the version a pointer names. For every startup pos s. -/
theorem LM_ruleR (sp : Spec V T) (al : Algo V T) (ts : List T) (hok : RunOK sp al ts)
    (hst : al.stillDirty = javaTest sp ∨ (sp.virt = false ∧ al.stillDirty = exactTest sp))
    (j : Nat) (hj : j ≤ ts.length) (y : NodeId) (r s : Nat) (u w : Version V) (t : Time)
    (hu : (run sp al (ts.take j)).S.versionAt r y = some u)
    (hw : newest (run sp al (ts.take j)).S s y = some w)
    (hg : good sp (run sp al (ts.take j)).S (run sp al (ts.take j)).P t u = true) :
    good sp (run sp al (ts.take j)).S (run sp al (ts.take j)).P t w = true := by
  have hinv := inv_st sp al ts hok (algOK_of sp al hst) j hj
  obtain ⟨r', -, hw', hrr⟩ := newest_ge hw hu
  exact hinv.newer hok.1.liveSub (u.level + 1) r r' y u w (by omega) hu hw' hrr t hg

/-- Lemma M, cut back (WP L2): a version cut back to time s (`Version.cutTo`;
Java cuts back a version of the startup section to the startup time) is good
for a time t ≤ s exactly when the whole version is. -/
theorem LM_cutTo (sp : Spec V T) (S : Stream V T) (P : Struct V) (w : Version V)
    {s t : Time} (ht : t ≤ s) : good sp S P t (w.cutTo s) = good sp S P t w :=
  good_cutTo sp S P w ht

/-- T1-L, lazy startup (bergdb item 001, WP L3). After a run of BergDB's
algorithm (`javaTest`) that meets the assumptions of the physical layer
(`PhysRunOK`), Java's lazy startup (`lazyStartup`) from the stream after T(k)
(the whole stream, or a prefix of it, which a crash leaves), followed by any
reads and writer follows (`Op`; admissible: `OpsOK`): a read at any time t up
to k, through `Phys.lean`'s first-touch rule, gives P at t, each node
reachable at t with its history at t. Every object in memory is canonical,
with its node's whole history, or holds a version of its node from the
stream, all of it or cut back to s; a memory slot that a canonical object's
node uses at a time t (it is reachable at t, the pointee a live child at t)
leads to a canonical object, or to one that holds a version good for t if it
holds all of it. -/
theorem T1_lazy (sp : Spec V T) (al : Algo V T) (ts : List T) (hok : RunOK sp al ts)
    (hph : PhysRunOK sp al ts) (hj : al.stillDirty = javaTest sp) (k : Nat) (hk : k ≤ ts.length)
    (ops : List Op)
    (hops : OpsOK sp ((run sp al ts).S.take (k + 1)) (run sp al (ts.take k)).P k
      (lazyStartup sp ((run sp al ts).S.take (k + 1))) ops) :
    let S : Stream V T := (run sp al ts).S.take (k + 1)
    let P := (run sp al (ts.take k)).P
    let m := ops.foldl (Mem.step sp S) (lazyStartup sp S)
    (∀ t ≤ k, (m.read sp S t).2 =
      (reachList sp P t).map (fun z => (z, ((P.get? z).map (·.hist.upTo t)).getD []))) ∧
    (∀ h o, m.obj? h = some o → o.canonical = true → (P.get? o.node).map (·.hist) = some o.hist) ∧
    (∀ h o, m.obj? h = some o → o.canonical = false → ∃ r w, o.pos = some r ∧
      S.versionAt r o.node = some w ∧ (o.hist = w.hist ∨ o.hist = w.hist.upTo (lastSp S))) ∧
    (∀ h o, m.obj? h = some o → o.canonical = true → ∀ t ≤ k, reachable sp P t o.node = true →
      ∀ y ∈ sp.live (o.hist.upTo t), ∀ h', o.slot? y = some (Slot.mem h') →
        ∃ o', m.obj? h' = some o' ∧ o'.node = y ∧ (o'.canonical = true ∨
          ∃ r w, o'.pos = some r ∧ S.versionAt r y = some w ∧
            (o'.hist = w.hist → good sp S P t w = true))) := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hpre := st_S_prefix sp al ts (j := k) (j' := ts.length) hk (Nat.le_refl _)
  have hlen := st_len sp al ts hok hst hk
  rw [st_length] at hpre
  have htake : (run sp al ts).S.take (k + 1) = (st sp al ts k).S := by
    rw [← hlen]; exact (List.prefix_iff_eq_take.mp hpre).symm
  intro S P m
  have hS : S = (st sp al ts k).S := htake
  have hP : P = (st sp al ts k).P := rfl
  rw [htake] at hops
  obtain ⟨hm, hctx, hkk⟩ := T1_lazy_strong hok hph hj hk ops hops
  have := hm.t1_facts hctx hkk
  simp only [m, hS, hP]
  exact this

end SIS
