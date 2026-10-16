/-
Self-indexed streams in Lean: startup.

Section numbers refer to theory/sis-model.md. Trusted part.
-/
import SIS.Algorithm

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- The newest version of y in R(s), ..., R(k): the startup section and the
record at the startup pos, as in BergDB's `DbStarter.createMaps` (6.2, step 3;
R(s) added 2026-10-16, docs/level2-alignment.md, M7). -/
def newest (S : Stream V T) (s : Nat) (y : NodeId) : Option (Version V) :=
  (S.drop s).reverse.findSome? (fun R => R.vers.find? (fun v => v.node == y))

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

/-- The version that top(k) names, read with Rule R. -/
def topVersion (S : Stream V T) (s : Nat) (ruleR : Bool) : Option (Version V) :=
  match S.getLast?.bind (·.top) with
  | some (z, r) => follow S s ruleR z (some r)
  | none => none

/-- With a virtual root: the root children read from version v of a root
child, v included, through the pointers (live or dead) between root children
(BergDB's skip pointers), with Rule R as in `readFrom`. -/
def readTops (sp : Spec V T) (S : Stream V T) (s : Nat) (ruleR : Bool) (v : Version V) :
    List (Version V) :=
  v :: (pointees sp v.hist).flatMap (fun y =>
    match follow S s ruleR y (v.ref? y) with
    | none => []
    | some w => if sp.topLevel ≤ w.level ∧ w.level < v.level then readTops sp S s ruleR w else [])
termination_by v.level

/-- The root's level. It never changes. -/
def rootLevel (sp : Spec V T) : Nat := ((sp.init.get? root).map (·.level)).getD 0

/-- With a virtual root: the root, as startup rebuilds it from the versions ws
of the root children read. Its history up to s: for each time t ≤ s at which a
root child read has its entries (it was created then), the entry
(t, rootVal z); its references: to the version read of each root child. -/
def rootVersion (sp : Spec V T) (s : Nat) (ws : List (Version V)) : Version V :=
  { node := root, recNo := s, level := rootLevel sp, isData := false,
    hist := (List.range (s + 1)).filterMap (fun t =>
      (ws.find? (fun w => w.hist.any (fun e => e.time == t))).map
        (fun w => (⟨t, sp.rootVal w.node⟩ : Entry V))),
    refs := ws.map (fun w => (w.node, w.recNo)) }

/-- With a virtual root: the root children read at startup, from the version
that top(k) names. -/
def topsRead (sp : Spec V T) (S : Stream V T) (s : Nat) (ruleR : Bool) : List (Version V) :=
  match topVersion S s ruleR with
  | some v => readTops sp S s ruleR v
  | none => []

/-- The version that startup reads from: top(k)'s, or, with a virtual root,
the root rebuilt from the root children read from top(k)'s version (6.2;
docs/level2-alignment.md, 8.2). -/
def startVersion (sp : Spec V T) (S : Stream V T) (s : Nat) (ruleR : Bool) : Option (Version V) :=
  if sp.virt then some (rootVersion sp s (topsRead sp S s ruleR)) else topVersion S s ruleR

/-- Read the stream at time t, from the version startup starts from. -/
def readAt (sp : Spec V T) (S : Stream V T) (s : Nat) (ruleR : Bool) (t : Time) :
    List (NodeId × Version V) :=
  match startVersion sp S s ruleR with
  | some v => readFrom sp S s ruleR t v
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
