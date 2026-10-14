/-
Self-indexed streams in Lean: startup.

Section numbers refer to theory/sis-model.md. Trusted part.
-/
import SIS.Algorithm

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- The newest version of y in the startup section R(s+1), ..., R(k)
(6.2, step 3). -/
def newest (S : Stream V T) (s : Nat) (y : NodeId) : Option (Version V) :=
  (S.drop (s + 1)).reverse.findSome? (fun R => R.vers.find? (fun v => v.node == y))

/-- Follow the pointer of a version to node y, whose reference is ref
(none if y had not been written, BergDB's vpos) (6.2, step 4). With Rule R
(ruleR = true), a pointer to a node with a version in the section is
followed to its newest version there, whatever the reference says. -/
def follow (S : Stream V T) (s : Nat) (ruleR : Bool) (y : NodeId) (ref : Option Nat) :
    Option (Version V) :=
  match (if ruleR then newest S s y else none) with
  | some v => some v
  | none => ref.bind (fun r => S.versionAt r y)

/-- Read the stream at time t, from version v and down (6.2, step 5): the
nodes reached, each with the version it is read from. As in `good`, a
reference to a version that is not on a lower level is not followed. -/
def readFrom (sp : Spec V T) (S : Stream V T) (s : Nat) (ruleR : Bool) (t : Time)
    (v : Version V) : List (NodeId × Version V) :=
  (v.node, v) :: (sp.live (v.hist.upTo t)).flatMap (fun y =>
    match follow S s ruleR y (v.ref? y) with
    | none => []
    | some w => if w.level < v.level then readFrom sp S s ruleR t w else [])
termination_by v.level

/-- Read the stream at time t, from top(k), the latest version of root. -/
def readAt (sp : Spec V T) (S : Stream V T) (s : Nat) (ruleR : Bool) (t : Time) :
    List (NodeId × Version V) :=
  match S.getLast?.bind (·.top) with
  | some r =>
    match follow S s ruleR root (some r) with
    | some v => readFrom sp S s ruleR t v
    | none => []
  | none => []

/-- P up to time s, as read from the stream (6.2, step 5). Each node gets the
history of the version it is read from at the latest time t <= s at which
it is reached, cut at s. -/
def baseStruct (sp : Spec V T) (S : Stream V T) (s : Nat) (ruleR : Bool) : Struct V :=
  let pairs := (List.range (s + 1)).flatMap (fun t => readAt sp S s ruleR t)
  ((pairs.map (·.1)).eraseDups).filterMap (fun x =>
    (List.lookup x pairs.reverse).map (fun v =>
      (x, { level := v.level, isData := v.isData, hist := v.hist.upTo s })))

/-- The transactions of the startup section: j = s+1, ..., k. -/
def sectionIdx (S : Stream V T) (s : Nat) : List Nat :=
  List.range' (s + 1) (S.length - 1 - s)

/-- Rerun T(s+1), ..., T(k), each at its own time (6.2, step 6). -/
def rerun (sp : Spec V T) (S : Stream V T) (s : Nat) (P : Struct V) : Struct V :=
  (sectionIdx S s).foldl (fun P j =>
    match S[j]?.bind (·.trans) with
    | some tr => P.apply j (sp.exec tr j (view sp P (j - 1)))
    | none => P) P

/-- Startup from the stream R(0), ..., R(k) (6.2). ruleR switches
reconciliation on or off; the model has it on (`startup`). -/
def startupWith (sp : Spec V T) (ruleR : Bool) (S : Stream V T) : DB V T :=
  let s := lastSp S
  -- 2. D from gd(s+1), ..., gd(k).
  let D := (sectionIdx S s).flatMap (fun j =>
    match S[j]? with
    | some R => R.gd.map (fun x => (x, j))
    | none => [])
  -- 3 to 6. P up to s from the stream, then the rerun.
  let P := rerun sp S s (baseStruct sp S s ruleR)
  { P := P, D := D, S := S }

/-- Startup, with Rule R (6.2). -/
def startup (sp : Spec V T) (S : Stream V T) : DB V T :=
  startupWith sp true S

end SIS
