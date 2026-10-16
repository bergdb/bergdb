/-
Self-indexed streams in Lean: the theorems of the physical layer (bergdb item
001, stages 1 and 2). Trusted part: the statements. The proofs are in
SIS/Proof/; the proofs here only connect them.
-/
import SIS.Theorems
import SIS.Proof.Newer

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

end SIS
