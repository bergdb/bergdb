/-
Self-indexed streams in Lean: Level 3, reclaim (bergdb item 001, WP R3).

Plan section numbers refer to items/001-lean-model-levels-3-4/01-plan.md in
bergdb. Trusted part.

Java's reclaim (levels.md, "Level 3: reclaim") rewrites the old live values
and touches the index nodes, step by step, and cuts the front of the stream:
the records before the cut position c are gone, and lookups are required only
from the first available time f on. The touch is `Changes.touch`, which step 3
marks (`gotDirty3`); f is `Record.fa` (`firstAvail`). Here: what a cut leaves
of the stream, when a cut is safe, and runs that restart from cut streams.
-/
import SIS.Evict

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- The stub of version v, what a cut leaves of it (plan, 8.7): its node,
record number, level and kind, without its history and references. Java's
slots keep the positions of versions whose bytes a cut removed. -/
def Version.stub (v : Version V) : Version V := { v with hist := [], refs := [] }

/-- Record R when a cut removed it: the stubs of its versions, no transaction
and no gd list (startup reads neither before the startup pos); its startup
pos, top and first available time stay. -/
def Record.cut (R : Record V T) : Record V T :=
  { R with trans := none, vers := R.vers.map Version.stub, gd := [] }

/-- The stream after a cut at c: the records before c are cut. Record numbers
do not change. A cut at 0 changes nothing. -/
def cutStream (c : Nat) (S : Stream V T) : Stream V T :=
  S.mapIdx (fun r R => if r < c then R.cut else R)

/-- The versions of the stream S that a lookup at time t may read, for the
structure P: the latest version of every node reachable at t, and every version
that a pointer of one of them to a live child at t leads to, with Rule R from
the startup pos of S (`follow`), and so on down (bergdb item 001, WP R7).
Startup's reads (`readFrom`) and the physical layer's loads (`Mem.follow4`)
follow such pointers. -/
inductive ReadsAt (sp : Spec V T) (S : Stream V T) (P : Struct V) (t : Time) :
    Version V → Prop
  | latest (x : NodeId) (v : Version V) : reachable sp P t x = true → S.lv x = some v →
      ReadsAt sp S P t v
  | child (v : Version V) (y : NodeId) (w : Version V) : ReadsAt sp S P t v →
      y ∈ sp.live (v.hist.upTo t) → follow S (lastSp S) true y (v.ref? y) = some w →
      ReadsAt sp S P t w

/-- The versions of the stream S that a physical read in the running process at
time t may follow, for the structure P (bergdb item 001, register M48, option
(a), Frans 2026-10-17): those that a lookup may read (`ReadsAt`), and through a
pointer of one of them to a live child at t, every version of the child at or
after the record that the pointer names (every version if it names none), and
so on down. A memory's Rule R is that of its last startup, which can be older
than the stream's, and its canonical objects and snapshots can be newer than a
pointer; a version that either gives is at or after the record the pointer
names (WP R4 found by running that `ReadsAt` alone does not cover them:
`cutReadWitness` in SIS/ReclaimExample.lean). -/
inductive ReadsPhys (sp : Spec V T) (S : Stream V T) (P : Struct V) (t : Time) :
    Version V → Prop
  | latest (x : NodeId) (v : Version V) : reachable sp P t x = true → S.lv x = some v →
      ReadsPhys sp S P t v
  | child (v : Version V) (y : NodeId) (w : Version V) : ReadsPhys sp S P t v →
      y ∈ sp.live (v.hist.upTo t) →
      (follow S (lastSp S) true y (v.ref? y) = some w ∨
        ∃ r, S.versionAt r y = some w ∧ ∀ r0, v.ref? y = some r0 → r0 ≤ r) →
      ReadsPhys sp S P t w

/-- A cut at c is safe in state db, the state after transaction k (plan, 8.7).
With f = fa(k), the first available time of the last record:
1. c <= f (and f <= s(k) by `firstAvail`), so the startup section, and the
   record at the startup pos, are after the cut;
2. every version that a read at some time from f to k may follow, a lookup's
   or a physical read's in the running process (`ReadsPhys`), is at c or
   later: the latest versions of the nodes reachable then, and the versions
   that their pointers to live children lead to, with Rule R or not. (WP R3
   asked this of the latest versions only; WP R7 found by running that a node
   reachable at f that the change replaces later can name an older version of
   a child, the child's latest being after the cut and the older one before
   it, so that a read at f after a restart from the cut stream reads a stub:
   `staleWitness` in SIS/ReclaimExample.lean; so R7 asked it of the versions
   that lookups read, `ReadsAt`. WP R4 found that a physical read in the
   running process can follow such a pointer without Rule R, with eviction:
   `cutReadWitness`; so, since WP R6, of `ReadsPhys`, register M48, option (a),
   Frans 2026-10-17.)
3. every node in D has its latest version at c or later, or none; and every
   reference below c of that version names the latest version of its node, so
   a node not in D (Java's pSafe wait: a parent written before its child and
   kept in D by Rule A must be written again). After a cut, Java cannot read
   the node id of a slot's target below the cut (M33), so it could neither link
   such a slot to the target's object in D nor apply Rule R to it; and the
   startup reads a node of D that is no longer reachable only through such
   references (M41);
4. top(k) names a record at c or later (implied by 2; M41). -/
def CutOK (sp : Spec V T) (c : Nat) (db : DB V T) (k : Nat) : Prop :=
  c ≤ lastFa db.S ∧
  (∀ t w, lastFa db.S ≤ t → t ≤ k → ReadsPhys sp db.S db.P t w → c ≤ w.recNo) ∧
  (∀ x, inD db.D x = true → ∀ v, db.S.lv x = some v →
    c ≤ v.recNo ∧ ∀ y r, v.ref? y = some r → r < c → (db.S.lv y).map (·.recNo) = some r) ∧
  (∀ R z r, db.S.getLast? = some R → R.top = some (z, r) → c ≤ r)

/-- P and P' give the same lookups at every time from f to k: every node but a
virtual root has the same content (x@t) in both, and a virtual root the same
live children. A startup from a cut stream rebuilds a virtual root from the
root children it can read, so the root's entries for the root children that
only times before the cut need are gone; so are Java's top nodes before the
cut after such a restart. For T8 and T12 (WPs R4 and R5). -/
def SameFrom (sp : Spec V T) (f k : Time) (P P' : Struct V) : Prop :=
  ∀ t, f ≤ t → t ≤ k →
    (∀ x, (sp.virt = true → x ≠ root) → view sp P t x = view sp P' t x) ∧
    (sp.virt = true → (view sp P t root).map (fun n => sp.live n.hist) =
      (view sp P' t root).map (fun n => sp.live n.hist))

/-- With a virtual root, a transaction sees the root only through its live
children (BergDB's transactions start at the current super root of `TopDs`):
its changes are the same on two views whose roots hold entries for root
children only, and that agree on every other node and on the root's live
children. A startup or a run that restarts from a cut stream needs it (T8, WP
R4; T12, WP R5), since its root lacks the entries that the cut made
unreadable. (WP R4 added the condition on the roots' entries: without it, a
spec that reads the root's entries as slots, as example 4 does, could not meet
it, since a view's root could then hold any entries.) -/
def ExecRootOK (sp : Spec V T) : Prop :=
  sp.virt = true → ∀ (tr : T) (i : Time) (v v' : View V),
    (∀ n, v root = some n → ∀ e ∈ n.hist, ∃ z, e.val = sp.rootVal z) →
    (∀ n, v' root = some n → ∀ e ∈ n.hist, ∃ z, e.val = sp.rootVal z) →
    (∀ x, x ≠ root → v x = v' x) →
    (v root).map (fun n => sp.live n.hist) = (v' root).map (fun n => sp.live n.hist) →
    sp.exec tr i v = sp.exec tr i v'

/-- With a virtual root, its live children at a time are those of its last entry
then: for a history of entries for root children, the live pointers are the
pointers of the last entry (BergDB's TopDs: the super root at time t is the
newest top node created up to t). A startup from a cut stream rebuilds the root
without the entries that the cut made unreadable; with this, that changes no
live child from the first available time on (T8, WP R4). -/
def VirtLiveOK (sp : Spec V T) : Prop :=
  sp.virt = true → ∀ h : History V, (∀ e ∈ h, ∃ z, e.val = sp.rootVal z) →
    sp.live h = (h.getLast?.map (fun e => sp.ptrs e.val)).getD []

/-- The policies give the same startup pos and first available time on a
stream cut at or before its first available time: they do not depend on what
a cut removes. Otherwise a restart from a cut stream could choose otherwise
than the run without the cut. -/
def PolicyCutOK (al : Algo V T) : Prop :=
  ∀ (c : Nat) (S : Stream V T) (D : Dirty) (i : Time) (tr : T) (s : Nat), c ≤ lastFa S →
    startupPos al (cutStream c S) D i tr = startupPos al S D i tr ∧
    firstAvail al (cutStream c S) D i tr s = firstAvail al S D i tr s

/-- A run with restarts and cuts: after each transaction marked some c, the
database crashes, the stream is cut at c, and the database starts again from
the cut stream (c = 0: a restart without a cut). -/
def runRestartsCut (sp : Spec V T) (al : Algo V T) (ts : List (T × Option Nat)) : DB V T :=
  ts.foldl (fun db p =>
    let db := step sp al db p.1
    match p.2 with
    | some c => startup sp (cutStream c db.S)
    | none => db) (init sp)

/-- The largest cut of a list of restart marks, 0 if there is none. -/
def cutMax (cs : List (Option Nat)) : Nat :=
  cs.foldl (fun m c => max m (c.getD 0)) 0

/-- A run with eviction, restarts and cuts: as `runEvict`, but a transaction
marked some c is followed by a restart from the stream cut at c: the logical
startup, the Level 4 startup for the memory, and the cut stream for Rule R. A
transaction marked none is followed by its cache operations. -/
def runEvictCut (sp : Spec V T) (al : Algo V T) (ts : List (T × Option Nat × List CacheOp)) :
    DB V T × Mem V × Stream V T :=
  ts.foldl (fun (acc : DB V T × Mem V × Stream V T) p =>
    let r := evictTrans sp al acc.2.2 acc.1 acc.2.1 p.1
    match p.2.1 with
    | some c =>
      let S := cutStream c r.1.S
      (startup sp S, evictStartup sp S, S)
    | none => (r.1, p.2.2.foldl (Mem.cacheOp sp acc.2.2 r.1.S r.1.D) r.2, acc.2.2))
    (init sp, evictStartup sp (init sp).S, (init sp).S)

end SIS
