/-
Self-indexed streams in Lean: bounds, part 2, T4: the records at the ends of
the startup section, and the debt of D (bergdb item 007; 007-01, sections 5.1
and 6; 027-01, sis-model.md section 10, the planned T4).

Trusted part: the definitions that T4 is about, and its statements as
definitions of type `Prop`. The theorems are in SIS/BoundT4Theorems.lean, the
proofs in SIS/Proof/BoundT4.lean and SIS/Proof/BoundT4Debt.lean. Added
2026-11-13.

T4 was stated only in prose, in 007-01:

* Section 5.1, "The records at the ends": "A record holds T(i), its value
  nodes, gd(i) and the versions of the nodes taken, which come from D. So R(s)
  and R(k) cost at most a transaction plus the debt. Bounding the debt is T4
  (section 6)." (`RecordBound`, `RecordByDebt`.)
* Section 6, "T4: the size of D": "By INV-1, D holds the nodes of gd(j) for
  the transactions j of the section. A node gets into gd(j) in step 3, on the
  access path of T(j)'s change (the changed nodes and their ancestors), or in
  step 7, taken and still dirty. With the exact still-dirty test, a written
  node stays dirty only if it is reachable at a time after s with a child that
  is dirty then. So D holds the nodes changed in about the last two sections
  and their ancestors at those times: at most h times those changes, with A4
  for h and TREE (one current parent)." 007-03 ("After the plan") asks for it
  "for the exact still-dirty test first". (`DebtByChanges`.)

`RecordBound` states the first for one record, `DebtByChanges` the second with
lev(x) + 1 sections for a node x of D on level lev(x), so with h + 1 sections
for a tree of height h, in place of "about the last two sections" (see its
docstring). The count "at most h times those changes" with TREE is not stated
here: what is stated is which nodes D holds, from which the count follows by
TREE's one current parent.
-/
import SIS.Bound
import SIS.Assumptions

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- s(j), the startup pos of record R(j) of the stream S; 0 past its end. -/
def spAt (S : Stream V T) (j : Nat) : Nat := ((S[j]?).map (·.sp)).getD 0

/-- s applied n times: spIter S 0 j = j, spIter S 1 j = s(j), spIter S 2 j =
s(s(j)), the beginning of the startup section of R(s(j)), and so on. After
R(k), the startup section is R(s(k)), ..., R(k); "the last n sections" are the
transactions after spIter S n k. -/
def spIter (S : Stream V T) : Nat → Nat → Nat
  | 0, j => j
  | n + 1, j => spIter S n (spAt S j)

/-- The level of node x in P (0 if x is not in P). -/
def levelOf (P : Struct V) (x : NodeId) : Nat := ((P.get? x).map (·.level)).getD 0

/-- Node x is on the access path of the change of transaction T(τ) of the run
ts, 1 ≤ τ ≤ ts.length (step 3, 6.1): it is reachable at τ, and a node that
T(τ) creates or gives an entry is reachable from it at τ (`marked`, "the
changed nodes and their ancestors"); or T(τ)'s touch marks it
(`Changes.touch`, bergdb item 001: reclaim's touch, which step 3 marks as it
marks the access path). P and the change are those of the run: P after
T(τ-1), and T(τ)'s change made on it. -/
def onAccessPath (sp : Spec V T) (al : Algo V T) (ts : List T) (τ : Nat) (x : NodeId) : Prop :=
  0 < τ ∧ ∃ tr, ts[τ - 1]? = some tr ∧
    let db := run sp al (ts.take (τ - 1))
    let c := sp.exec tr τ (view sp db.P (τ - 1))
    marked sp (db.P.apply τ c) c τ x = true ∨ x ∈ c.touch

/-- The change of transaction T(τ) of the run ts, made on P after T(τ - 1), as
`onAccessPath` takes it; no change for τ = 0 or past the run. -/
def changeAt (sp : Spec V T) (al : Algo V T) (ts : List T) : Nat → Changes V
  | 0 => { new := [], adds := [] }
  | j + 1 =>
    match ts[j]? with
    | some tr => sp.exec tr (j + 1) (view sp (run sp al (ts.take j)).P j)
    | none => { new := [], adds := [] }

/-- T4, the record of a transaction (007-01, section 5.1: "A record holds
T(i), its value nodes, gd(i) and the versions of the nodes taken, which come
from D. So R(s) and R(k) cost at most a transaction plus the debt."). The
record R of transaction tr, appended to the database db (i = db.S.length, D =
db.D the debt before T(i), c the change of T(i)), holds:

1. T(i) itself (`trans`);
2. versions of the data nodes that T(i) creates, and versions of nodes of D,
   and nothing else: every index node it writes was in D before T(i);
3. at most (the number of data nodes that T(i) creates) + |D| versions;
4. in gd(i), besides the nodes that got dirty in T(i) (those not in D before
   it, which step 3 found on the access path of the change, or the touch), at
   most |D| nodes of D (those taken and still dirty).

So R(i) is bounded by what T(i) makes (its transaction, its value nodes, its
got-dirty nodes) plus the debt D before T(i). The model has records, not
bytes: a bound in bytes needs a bound on a version's bytes, which BergDB has
(a node holds at most a fixed number of klongs) and the model does not (its
histories grow; 007-01, 5.1). -/
def RecordBound (sp : Spec V T) (db : DB V T) (tr : T) (R : Record V T) : Prop :=
  let i := db.S.length
  let c := sp.exec tr i (view sp db.P (i - 1))
  R.trans = some tr ∧
    (∀ v ∈ R.vers, v.node ∈ (c.new.filter (·.isData)).map (·.id) ∨ inD db.D v.node = true) ∧
    R.vers.length ≤ (c.new.filter (·.isData)).length + db.D.length ∧
    (R.gd.filter (inD db.D)).length ≤ db.D.length

/-- T4 for one transaction: the record that transaction tr appends to the
database db is bounded by the debt before it (`RecordBound`). -/
def RecordByDebt (sp : Spec V T) (al : Algo V T) (db : DB V T) (tr : T) : Prop :=
  ∃ R : Record V T, (step sp al db tr).S = db.S ++ [R] ∧ RecordBound sp db tr R

/-- T4, the debt of D (007-01, section 6), with the exact still-dirty test:
after the run ts, of k = ts.length transactions, every node x of D is on the
access path of the change of a transaction T(τ) of the last lev(x) + 1
startup sections, spIter S (lev(x) + 1) k < τ ≤ k, where lev(x) is x's level
(`onAccessPath`: reachable at τ with a node changed by T(τ) below it, "the
nodes changed ... and their ancestors at those times"; or touched by T(τ)).

The prose says "about the last two sections". The proof gives lev(x) + 1:
a node taken and still dirty in T(j) is dirty through a child whose latest
version is not good, and that child may itself have been taken and still dirty
in an earlier transaction of the section, whose own section begins one section
further back, and so on down the levels (SIS/Proof/BoundT4Debt.lean). Whether
two sections always suffice, or a run needs more, is open. For the index
nodes just above the data nodes (level 1, with data nodes on level 0) the
bound is the prose's last two sections.

With BergDB's test (`javaTest`, Rule A over all pointers, live or dead) this
is not stated: a written node stays in D while any pointee is in D, also one
it no longer points to live (007-01, section 6, second point). The proof's
induction does not use the test (`debt_main`); only its start does: a node
that step 7 puts back is dirty. -/
def DebtByChanges (sp : Spec V T) (al : Algo V T) (ts : List T) : Prop :=
  let db := run sp al ts
  ∀ e ∈ db.D, ∃ τ, spIter db.S (levelOf db.P e.1 + 1) ts.length < τ ∧ τ ≤ ts.length ∧
    onAccessPath sp al ts τ e.1

end SIS
