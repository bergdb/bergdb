/-
Self-indexed streams in Lean: the stream, good versions and dirty nodes.

Section numbers refer to theory/sis-model.md. Trusted part.
-/
import SIS.Basic

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- A node version, written to the stream (4). -/
structure Version (V : Type) where
  /-- The node. -/
  node : NodeId
  /-- The record it is written in. -/
  recNo : Nat
  level : Nat
  isData : Bool
  /-- The node's history up to the record's time: all of it so far. -/
  hist : History V
  /-- For each node y the history points to (live or dead pointer), the
  record of the version of y that this version references. A node that has
  never been written has no reference (BergDB's vpos). -/
  refs : List (NodeId × Nat)
  deriving DecidableEq, Repr

/-- A record of the stream, appended by one transaction (4). -/
structure Record (V T : Type) where
  /-- T(i), enough to rerun it. none for R(0). -/
  trans : Option T
  /-- s(i), the startup pos. -/
  sp : Nat
  /-- V(i), the versions written, in order. -/
  vers : List (Version V)
  /-- gd(i), the ids of the index nodes that got dirty in T(i). -/
  gd : List NodeId
  /-- top(i), the version that startup reads first, as its node and record:
  the latest version of root, or, with a virtual root (`Spec.virt`), the
  latest version of the root's child at s(i) (`topOf`). The node was added
  2026-10-16 for the virtual root (F1-008-11, WP E3); BergDB's topPos names a
  version, so both. -/
  top : Option (NodeId × Nat)
  deriving DecidableEq, Repr

/-- The stream: records R(0), R(1), ..., R(k). Record i is at index i. -/
abbrev Stream (V T : Type) := List (Record V T)

/-- The version of node y written in record r, if any. -/
def Stream.versionAt (S : Stream V T) (r : Nat) (y : NodeId) : Option (Version V) :=
  match S[r]? with
  | some R => R.vers.find? (fun v => v.node == y)
  | none => none

/-- The latest version of node x in the stream, lv(x) (4). -/
def Stream.lv (S : Stream V T) (x : NodeId) : Option (Version V) :=
  S.reverse.findSome? (fun R => R.vers.find? (fun v => v.node == x))

/-- The reference that version v holds for node y, as a record number. -/
def Version.ref? (v : Version V) (y : NodeId) : Option Nat :=
  List.lookup y v.refs

/-- The nodes that a history points to, live or dead, without repeats. -/
def pointees (sp : Spec V T) (h : History V) : List NodeId :=
  (h.flatMap (fun e => sp.ptrs e.val)).eraseDups

/-- The version of node x (with node n) written in record i, given the
stream S so far, which may already hold the first versions of record i
(4: "versions earlier in the same record count"). -/
def mkVersion (sp : Spec V T) (S : Stream V T) (i : Nat) (x : NodeId) (n : Node V) :
    Version V :=
  { node := x, recNo := i, level := n.level, isData := n.isData, hist := n.hist,
    refs := (pointees sp n.hist).filterMap (fun y => (S.lv y).map (fun w => (y, w.recNo))) }

/-- Version v is good for time t (5.1):
1. its history gives the node's content at t, and
2. for each child y at t, the reference for y leads to a version that is
   good for t.
A reference to a version that is not on a lower level counts as not good
(A4); this makes the recursion end. -/
def good (sp : Spec V T) (S : Stream V T) (P : Struct V) (t : Time) (v : Version V) :
    Bool :=
  (match P.get? v.node with
   | some n => v.hist.upTo t == n.hist.upTo t
   | none => false) &&
  (sp.live (v.hist.upTo t)).all (fun y =>
    match v.ref? y with
    | none => false
    | some r =>
      match S.versionAt r y with
      | none => false
      | some w => if w.level < v.level then good sp S P t w else false)
termination_by v.level

/-- Node x is dirty at time i (5.2): it has no version, or its latest version
is not good for some time t <= i at which x is reachable. -/
def dirty (sp : Spec V T) (S : Stream V T) (P : Struct V) (i : Time) (x : NodeId) : Bool :=
  match S.lv x with
  | none => true
  | some v => (List.range (i + 1)).any (fun t => reachable sp P t x && !good sp S P t v)

end SIS
