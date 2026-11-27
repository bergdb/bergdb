/-
The contract package (bergdb 030-09): the trace's completeness. The checker
(ContractCheck.lean) builds Java's tree from a trace's lines (`applyTx`,
Trace.lean); what it checks is the contract only if those lines are all of
Java's change and the transactions are a history. This file checks that a
trace is whole, line by line, before the contract is checked
(030-06, findings 1, 2 and 7):

* the first line is `TRACE 3`; a `TREE` line comes before the first
  transaction; every line is of a kind of trace format 3 (bergdb 027-02,
  sections 2 and 4), and no line is an `ERROR` line (the exporter's own
  report of a change it could not express, such as klongs of an existing node
  changed or removed);
* (bergdb 030-15) every line parses whole by the grammar of format 3
  (`lineFault`): exactly the tokens of its kind, each of its form, numbers
  of decimal digits only, one space between tokens; the lines of a
  transaction in the order of 027-02, section 2 (`placeLine`), `TX i`,
  i > 0, starting with `BASE`, and `TX 0`, the start, with no operation,
  read, touch or reclaim line;
* the transactions are numbered 0, 1, 2, ... with no gap; each `TX i` ends
  with `END i`, the lines of a transaction stand between the two, and the
  last line is `DONE n`, n the last transaction (a cut trace fails);
* in each transaction: a node of a `NEW` line is new; every `ADD` line is at
  the transaction's time and names a node that it may change (a value only
  when it is made, a top node's pointers only when it is made, the root's
  entry for a top node made with its root pointer); a `KN` line names a key
  node that exists or is made, with its klongs exactly; every index node
  made is a key node with its `KN` line or a top node with its root pointer
  (the root, node 0, is made in `TX 0`); every value made has its `ADD ... V`
  line; one `GD` and one `DIRTY` line;
* (bergdb 030-19, the three points of an independent review, Codex 3) a delete
  bitmap of a `KN` line is a number below 2^62, Java's 62 bits (`isBitmap`,
  Trace.lean); no `PROBE` line fails (run B's restart and run E's eviction
  checks, as the exporter's own `ERROR` lines); and every `TX i`, i > 0, has its
  reads: n `GET` lines, n > 0 the same in each, and one `SCAN` line (the
  exporter's `gets=N`, default 4, 027-02, section 4), so that a trace that
  passes has tested Java's readers in every transaction.

`completeFault` gives the first fault, with its line number, or none.
Nothing here needs Mathlib.
-/
import Contract.Trace

namespace Contract

/-- The first token of every kind of line of trace format 3 (bergdb 027-02,
sections 2 and 4), but `ERROR`, which fails. -/
def lineKinds : List String :=
  ["TRACE", "CONFIG", "TREE", "TX", "END", "DONE", "BASE", "OP", "NEW", "ADD", "KN", "GET",
   "SCAN", "TOUCH", "REC", "VER", "H", "F", "SKIPT", "GD", "DIRTY", "FA", "CUT", "PHYSCUT",
   "LIVE", "PROBE", "FIRST", "SLOT", "HMEM", "HTABLE", "HANDLE", "HOBJ", "HPTR"]

/-- The kinds of line of the head of a trace, before `TX 0`. -/
def headKinds : List String := ["TRACE", "CONFIG", "TREE"]

/-- What a node is, as the trace's lines made it. -/
inductive NodeKind where
  | root
  | key
  | top
  | val
  deriving DecidableEq, Repr, Inhabited

/-- The state of the line-by-line check. -/
structure LineState where
  /-- The first line is still to come. -/
  first : Bool := true
  /-- The TREE line was read. -/
  tree : Bool := false
  /-- The number of the transaction being read, if any. -/
  tx : Option Nat := none
  /-- The number of the next transaction. -/
  next : Nat := 0
  /-- The DONE line was read. -/
  done : Bool := false
  /-- The nodes made so far, by their kinds. -/
  nodes : Std.HashMap NodeId NodeKind := {}
  /-- Of the transaction being read: the nodes of its NEW lines, true for a
  value (D); the key nodes of its KN lines; the values of its V entries; the
  top nodes of the root's T entries; the top nodes with their R entry; its GD
  and DIRTY lines. -/
  news : List (NodeId × Bool) := []
  kns : List NodeId := []
  vals : List NodeId := []
  tops : List NodeId := []
  rptrs : List NodeId := []
  gd : Nat := 0
  dirty : Nat := 0
  /-- (bergdb 030-19) The GET and SCAN lines of the transaction being read, and the
  number of GET lines of each transaction after `TX 0`, once the first has ended. -/
  gets : Nat := 0
  scans : Nat := 0
  getsN : Option Nat := none
  /-- The place (`rankOf`) of the last line of the transaction being read,
  and in a version: 0 before its first VER line, then 1 after a VER line, 2
  after an H line, 3 after a SKIPT line, 4 after an F line (bergdb 030-15). -/
  rank : Nat := 0
  verPart : Nat := 0

/-- n klongs of a KN line take exactly the tokens `toks`. -/
def klongToksOk : Nat → List String → Bool
  | 0, [] => true
  | 0, _ :: _ => false
  | n + 1, "T" :: t :: r => isNum t && klongToksOk n r
  | n + 1, "K" :: c :: y :: r => isNum c && isNum y && klongToksOk n r
  | n + 1, "B" :: b :: r => isBitmap b && klongToksOk n r
  | _ + 1, _ => false

/-- A `B` klong of a KN line's tokens with a number of 2^62 or more (bergdb 030-19): in a
KN line a `B` token always starts a delete bitmap (a compare value or a pointee is a
number). -/
def wideBitmap : List String → Bool
  | "B" :: b :: r => (isNum b && !isBitmap b) || wideBitmap (b :: r)
  | _ :: r => wideBitmap r
  | [] => false

/-- All tokens are numbers (digits only: `isNum`, Trace.lean). -/
def allNums (toks : List String) : Bool := toks.all isNum

/-! ## The grammar of a line (bergdb 030-15)

Every line of a trace must parse whole by the grammar of trace format 3
(bergdb 027-02, sections 1, 2 and 4): its kind, then exactly the tokens
that kind has, each of its form (a number is decimal digits only; `-` only
where the format allows none). `lineFault` gives what is wrong with a line,
or none. Until 030-15 only the kinds were checked here and `readLine` passed
over a line of an unmatched form: a bare `OP` or `GET` line, or a SCAN in
the direction `BANANA` (read as backward), passed both checkers. -/

/-- A number or `-`. -/
def isNumOrNone (s : String) : Bool := s == "-" || isNum s

/-- The tokens after a key `n c1 ... cn` at the front, if there is one. -/
def keyRest : List String → Option (List String)
  | n :: r =>
    if isNum n then
      let k := n.toNat?.getD 0
      if k ≤ r.length && (r.take k).all isNum then some (r.drop k) else none
    else none
  | [] => none

/-- The tokens after a key or `-` at the front, if there is one. -/
def keyOrNoneRest : List String → Option (List String)
  | "-" :: r => some r
  | toks => keyRest toks

/-- n keys, each with its value, take exactly the tokens. -/
def kvsOk : Nat → List String → Bool
  | 0, toks => toks.isEmpty
  | n + 1, toks =>
    match keyRest toks with
    | some (v :: r) => isNum v && kvsOk n r
    | _ => false

/-- An entry (bergdb 027-02, section 1): `K c y`, `D n c1 ... cn`, `R y`,
`S j z`, `T z` or `V h`. -/
def entryOk : List String → Bool
  | ["K", c, y] => isNum c && isNum y
  | "D" :: n :: cs => isNum n && cs.length == n.toNat?.getD 0 && allNums cs
  | ["R", y] => isNum y
  | ["S", j, z] => isNum j && isNum z
  | ["T", z] => isNum z
  | ["V", h] => isNum h
  | _ => false

/-- What is wrong with the tokens of a line of a kind of trace format 3, or
none (the first token is the kind; `TRACE` and `ERROR` are `lineStep`'s). -/
def lineFault (toks : List String) : Option String :=
  let ok : Bool := match toks with
    | "CONFIG" :: _ => true
    | "TREE" :: r => allNums r && [4, 6, 7, 8].contains r.length
    | ["TX", i] => isNum i
    | ["END", i] => isNum i
    | ["DONE", n] => isNum n
    | ["BASE", b] => isNum b
    | "OP" :: "P" :: r => match keyRest r with
      | some [v] => isNum v
      | _ => false
    -- A copy of reclaim's step, a put with the copy mark (bergdb 031-06; 027-02, section 4).
    | "OP" :: "C" :: r => match keyRest r with
      | some [v] => isNum v
      | _ => false
    | "OP" :: "D" :: r => keyRest r == some []
    | "OP" :: "N" :: r => keyRest r == some []
    | ["NEW", x, l, k] => isNum x && isNum l && (k == "I" || k == "D")
    | "ADD" :: x :: t :: e => isNum x && isNum t && entryOk e
    | "KN" :: x :: l :: n :: r =>
      isNum x && (l == "0" || l == "1") && isNum n && klongToksOk (n.toNat?.getD 0) r
    | "GET" :: t :: r => isNum t && match keyRest r with
      | some [v] => isNumOrNone v
      | _ => false
    | "SCAN" :: t :: d :: a :: b :: n :: r =>
      isNum t && (d == "F" || d == "B") && (a == "0" || a == "1") && (b == "0" || b == "1") &&
        isNum n && match (keyOrNoneRest r).bind keyOrNoneRest with
        | some (k :: kvs) => isNum k && kvsOk (k.toNat?.getD 0) kvs
        | _ => false
    | "TOUCH" :: xs => allNums xs
    | ["REC", i, sp, top, src] =>
      isNum i && isNumOrNone sp && isNumOrNone top && (src == "field" || src == "derived")
    | ["REC", i, sp, top, src, z] =>
      isNum i && isNumOrNone sp && isNum top && (src == "field" || src == "derived") && isNum z
    | ["VER", x, k] => isNum x && (k == "I" || k == "D")
    | "H" :: t :: e => isNum t && entryOk e
    | ["F", y, r] => isNum y && isNum r
    | ["SKIPT", j, t] => isNum j && isNum t
    | "GD" :: xs => allNums xs
    | "DIRTY" :: xs => allNums xs && xs.length % 2 == 0
    | ["FA", t] => isNum t
    | ["CUT", c, t] => isNum c && isNum t
    | ["PHYSCUT", c] => isNum c
    | "LIVE" :: x :: t :: ys => isNum x && isNum t && allNums ys
    | "PROBE" :: i :: k :: _ => isNum i && (k == "ok" || k == "fail")
    | ["FIRST", x, n, r, k, c] =>
      isNum x && isNumOrNone n && isNumOrNone r &&
        (k == "canonical" || k == "version" || k == "snapshot") && (c == "0" || c == "1")
    | ["SLOT", x, y, r, k] =>
      isNum x && isNum y && isNumOrNone r &&
        (k == "canon" || k == "mem" || k == "stream" || k == "dead")
    | ["HMEM", k, c] => isNum k && isNum c
    | ["HTABLE", y, h] => isNum y && isNum h
    | ["HANDLE", h, y, st, a, w] =>
      isNum h && isNum y && (st == "live" || st == "loading" || st == "dead") &&
        isNumOrNone a && isNumOrNone w
    | ["HOBJ", a, y, k, r, e, x] =>
      isNum a && isNum y && (k == "canon" || k == "snap") && isNumOrNone r && isNum e && isNum x
    | ["HPTR", a, y, r, h] => isNum a && isNum y && isNumOrNone r && isNumOrNone h
    | _ => false
  if ok then none
  else if toks.head? == some "KN" && wideBitmap toks then
    some s!"a delete bitmap wider than Java's {bitmapBits} bits (027-02, section 4): {
      " ".intercalate toks}"
  else some s!"not of the grammar of trace format 3: {" ".intercalate toks}"

/-- The place of a kind of line in a transaction (bergdb 027-02, section 2,
"Within TX i, the order is"; section 4): the lines of a transaction come in
this order. A version's lines (`VER`, with its `H`, `SKIPT` and `F` lines)
share one place. -/
def rankOf : String → Nat
  | "BASE" => 1
  | "OP" => 2
  | "NEW" => 3
  | "ADD" => 4
  | "KN" => 5
  | "GET" => 6
  | "SCAN" => 7
  | "TOUCH" => 8
  | "REC" => 9
  | "VER" | "H" | "SKIPT" | "F" => 10
  | "GD" => 11
  | "DIRTY" => 12
  | "FA" | "CUT" | "PHYSCUT" => 13
  | "LIVE" => 14
  | "PROBE" => 15
  | "FIRST" => 16
  | "SLOT" => 17
  | "HMEM" | "HTABLE" | "HANDLE" | "HOBJ" | "HPTR" => 18
  | _ => 0

/-- The kinds of line that stand at most once in a transaction. -/
def onceKinds : List String := ["BASE", "TOUCH", "REC"]

/-- The kinds of line that `TX 0`, the start, does not have: it makes the
primordial nodes, runs no operation and reads nothing (bergdb 027-02,
section 4: BASE, OP, GET and SCAN lines are of `TX i`, i > 0; a touch and
reclaim's lines are of a step). -/
def notStartKinds : List String := ["BASE", "OP", "GET", "SCAN", "TOUCH", "FA", "CUT", "PHYSCUT"]

/-- The kind of node x if it is made, before or in the transaction being
read. An index node of a NEW line of this transaction is the root if it is
node 0, a top node once the root's entry names it, else a key node. -/
def LineState.kindOf (st : LineState) (x : NodeId) : Option NodeKind :=
  match st.news.lookup x with
  | some true => some .val
  | some false =>
    if x == 0 then some .root else if st.tops.contains x then some .top else some .key
  | none => st.nodes[x]?

/-- The checks at the END of transaction i, and the nodes it made added to
the nodes. -/
def endTx (st : LineState) (i : Nat) : Except String LineState := do
  if st.gd != 1 then throw s!"TX {i} has {st.gd} GD lines, not one"
  if st.dirty != 1 then throw s!"TX {i} has {st.dirty} DIRTY lines, not one"
  -- The reads (bergdb 030-19): n GET lines, n > 0 the same in every TX i > 0, one SCAN line.
  if i != 0 then
    if st.scans != 1 then throw s!"TX {i} has {st.scans} SCAN lines, not one"
    if st.gets == 0 then throw s!"TX {i} has no GET line"
    if let some n := st.getsN then
      if st.gets != n then throw s!"TX {i} has {st.gets} GET lines, the transactions before it {n}"
  let mut nodes := st.nodes
  for (x, isVal) in st.news do
    if isVal then
      if !st.vals.contains x then throw s!"TX {i}: value {x} is made without its V entry"
      nodes := nodes.insert x .val
    else if st.tops.contains x then
      if !st.rptrs.contains x then throw s!"TX {i}: top node {x} is made without its root pointer"
      nodes := nodes.insert x .top
    else if x == 0 then
      nodes := nodes.insert x .root
    else
      if !st.kns.contains x then throw s!"TX {i}: key node {x} is made without its KN line"
      nodes := nodes.insert x .key
  for z in st.tops do
    if !(st.news.lookup z == some false) then throw s!"TX {i}: the root's entry names {z}, no top node made"
  for z in st.rptrs do
    if !st.tops.contains z then throw s!"TX {i}: a root pointer of {z}, no top node made"
  return { st with tx := none, next := i + 1, nodes := nodes, news := [], kns := [], vals := [],
                   tops := [], rptrs := [], gd := 0, dirty := 0, rank := 0, verPart := 0,
                   gets := 0, scans := 0, getsN := if i == 0 then st.getsN else some st.gets }

/-- An ADD line `ADD x t e` of transaction i. -/
def addLine (st : LineState) (i : Nat) (toks : List String) : Except String LineState := do
  match toks with
  | x :: t :: e =>
    let x ← num x
    let t ← num t
    if t != i then throw s!"an ADD line at time {t} in TX {i}"
    match e, st.kindOf x with
    | ["V", h], some .val =>
      if !allNums [h] then throw "an ADD V line"
      if st.vals.contains x then throw s!"two V entries for value {x}"
      if !(st.news.lookup x == some true) then throw s!"a V entry for value {x}, not made in TX {i}"
      return { st with vals := x :: st.vals }
    | ["T", z], some .root =>
      let z ← num z
      if st.tops.contains z then throw s!"two root entries for top node {z}"
      return { st with tops := z :: st.tops }
    | ["R", y], some .top =>
      if !allNums [y] then throw "an ADD R line"
      if !(st.news.lookup x == some false) then throw s!"a root pointer of top node {x}, not made in TX {i}"
      if st.rptrs.contains x then throw s!"two root pointers of top node {x}"
      return { st with rptrs := x :: st.rptrs }
    | ["S", j, z], some .top =>
      if !allNums [j, z] then throw "an ADD S line"
      if !(st.news.lookup x == some false) then throw s!"a skip pointer of top node {x}, not made in TX {i}"
      return st
    | "K" :: r, some .key =>
      if r.length != 2 || !allNums r then throw "an ADD K line"
      return st
    | "D" :: n :: r, some .key =>
      let n ← num n
      if r.length != n || !allNums r then throw "an ADD D line"
      return st
    | _, k => throw s!"an ADD line for node {x} ({repr k}) that is not of its kind: {e}"
  | _ => throw "an ADD line"

/-- A line of kind k in transaction i stands in its place (bergdb 030-15):
the kinds in the order of `rankOf`, `BASE`, `TOUCH` and `REC` at most once,
an `H`, `SKIPT` or `F` line in a version after its `VER` line, in that
order; `TX i`, i > 0, starts with its `BASE` line, and `TX 0` has none of
the lines of an operation, a read or a step (`notStartKinds`). -/
def placeLine (st : LineState) (i : Nat) (k : String) : Except String LineState := do
  if i == 0 && notStartKinds.contains k then throw s!"a line of kind {k} in TX 0, the start"
  if i != 0 && st.rank == 0 && k != "BASE" then throw s!"TX {i} does not start with BASE"
  let r := rankOf k
  if r == 0 then throw s!"a line of kind {k} inside TX {i}"
  if r < st.rank || (r == st.rank && onceKinds.contains k) then
    throw s!"a line of kind {k} out of its place in TX {i} (027-02, section 2)"
  let part ← match k with
    | "VER" => pure 1
    | "H" => if 1 ≤ st.verPart && st.verPart ≤ 2 then pure 2 else throw s!"an H line not after VER or H"
    | "SKIPT" =>
      if 1 ≤ st.verPart && st.verPart ≤ 3 then pure 3 else throw s!"a SKIPT line not in a version"
    | "F" => if 1 ≤ st.verPart then pure 4 else throw s!"an F line not in a version"
    | _ => pure 0
  return { st with rank := r, verPart := part }

/-- The kinds of line whose last token is free text. -/
def textKinds : List String := ["CONFIG", "PROBE"]

/-- One line, at line number `ln`. -/
def lineStep (st : LineState) (ln : Nat) (line : String) : Except String LineState := do
  let toks := (line.splitOn " ").filter (· ≠ "")
  match toks with
  | [] => return st
  | t :: _ =>
    if t.startsWith "#" then return st
    if st.done then throw s!"line {ln}: a line after DONE"
    if st.first then
      if toks != ["TRACE", "3"] then throw s!"line {ln}: the first line is not TRACE 3"
      return { st with first := false }
    if t == "ERROR" then throw s!"line {ln}: the exporter's {line}"
    -- A PROBE line that fails (bergdb 030-19): run B's or run E's check found Java wrong.
    if t == "PROBE" && toks[2]? == some "fail" then
      throw s!"line {ln}: a PROBE line that failed (a check of run B or run E): {line}"
    if !lineKinds.contains t then throw s!"line {ln}: a line of an unknown kind: {line}"
    if !textKinds.contains t && (line.splitOn " ").length != toks.length then
      throw s!"line {ln}: tokens not separated by one space: {line}"
    if let some e := lineFault toks then throw s!"line {ln}: {e}"
    match st.tx with
    | none =>
      match toks with
      | ["TX", i] =>
        let i ← num i
        if !st.tree then throw s!"line {ln}: TX {i} before the TREE line"
        if i != st.next then throw s!"line {ln}: TX {i}, not TX {st.next}"
        return { st with tx := some i }
      | ["DONE", n] =>
        let n ← num n
        if st.next == 0 || n + 1 != st.next then
          throw s!"line {ln}: DONE {n}, but the last transaction is {st.next - 1}"
        return { st with done := true }
      | "TREE" :: _ =>
        if st.tree || st.next != 0 then throw s!"line {ln}: a second TREE line, or one after TX 0"
        return { st with tree := true }
      | k :: _ =>
        if headKinds.contains k && st.next == 0 then return st
        throw s!"line {ln}: a {k} line outside a transaction"
      | [] => return st
    | some i =>
      let st ← if t == "END" then pure st else
        match placeLine st i t with
        | .ok st' => pure st'
        | .error e => throw s!"line {ln}: {e}"
      match toks with
      | ["END", j] =>
        let j ← num j
        if j != i then throw s!"line {ln}: END {j} in TX {i}"
        match endTx st i with
        | .ok st' => return st'
        | .error e => throw s!"line {ln}: {e}"
      | "NEW" :: x :: l :: k :: [] =>
        let x ← num x
        let _ ← num l
        if k != "I" && k != "D" then throw s!"line {ln}: a NEW line of kind {k}"
        if st.nodes.contains x || (st.news.lookup x).isSome then
          throw s!"line {ln}: NEW {x}, a node made before"
        return { st with news := st.news ++ [(x, k == "D")] }
      | "ADD" :: r =>
        match addLine st i r with
        | .ok st' => return st'
        | .error e => throw s!"line {ln}: {e}"
      | "KN" :: x :: l :: n :: r =>
        let x ← num x
        let n ← num n
        if l != "0" && l != "1" then throw s!"line {ln}: a KN line's kind {l}"
        if !klongToksOk n r then throw s!"line {ln}: KN {x}: not exactly {n} klongs"
        if st.kns.contains x then throw s!"line {ln}: a second KN line for node {x} in TX {i}"
        match st.kindOf x with
        | some .key => return { st with kns := x :: st.kns }
        | some k => throw s!"line {ln}: a KN line for node {x}, which is a {repr k}"
        | none => throw s!"line {ln}: a KN line for node {x}, which no NEW line made"
      | "GD" :: r =>
        if !allNums r then throw s!"line {ln}: a GD line"
        return { st with gd := st.gd + 1 }
      | "DIRTY" :: r =>
        if !allNums r || r.length % 2 != 0 then throw s!"line {ln}: a DIRTY line"
        return { st with dirty := st.dirty + 1 }
      | "GET" :: _ => return { st with gets := st.gets + 1 }
      | "SCAN" :: _ => return { st with scans := st.scans + 1 }
      | k :: _ =>
        if headKinds.contains k || k == "TX" || k == "DONE" then
          throw s!"line {ln}: a {k} line inside TX {i}"
        return st
      | [] => return st

/-- The first fault of a trace's lines, if any (see the head of this file). -/
def completeFault (lines : Array String) : Option String := Id.run do
  let mut st : LineState := {}
  let mut ln := 0
  for line in lines do
    ln := ln + 1
    match lineStep st ln line with
    | .ok st' => st := st'
    | .error e => return some e
  if st.first then return some "an empty trace"
  if let some i := st.tx then return some s!"TX {i} has no END: the trace is cut"
  if !st.done then return some s!"no DONE line after TX {st.next - 1}: the trace is cut"
  return none

end Contract

namespace Contract

/-! ## LIVE lines: Java's searches and top search at every time

With the exporter's `live=1` a trace has, after each transaction, Java's own
live children of every node at each of its times (`LIVE x t y1 ...`,
`TraceExport.recordLive`): of a key node, the match of `KeyNode.searchEq` at
t for each compare value of its key klongs; of a top node, its root pointer;
of the root (node 0), the top node that `TopDs.findSuperRootAtTime` finds at
t. They test two of the assumptions that reads rest on (030-04, section 3.5):
Java's search is the Lean `searchEq`, and Java's top search finds the space
root of the contract's tree at every time, the record times and the times
between them (030-06, section 7). -/

/-- The compare values of the key klongs of a node, without repeats. -/
def keyCvs (ks : List Klong) : List Nat :=
  (ks.filterMap (fun k => match k with
    | .key c _ => some c
    | _ => none)).eraseDups

/-- The live children of a key node at time t as a LIVE line gives them:
`searchEq` at t of each compare value of its key klongs; in increasing
order, without repeats (Java's TreeSet). -/
def liveAt (ks : List Klong) (t : Time) : List NodeId :=
  ((keyCvs ks).filterMap (fun c => searchEq (prefixAt ks t) c)).eraseDups.mergeSort
    (fun a b => decide (a ≤ b))

/-- A LIVE line `LIVE x t ys` agrees with the heap h, `topRoot` the root
pointer of each top node. -/
def liveOk (h : Heap) (topRoot : List (NodeId × NodeId)) (x : NodeId) (t : Time)
    (ys : List NodeId) : Bool :=
  if x == 0 then
    match ys with
    | [] => (h.tree.at t).root.isNone
    | [z] => match topRoot.lookup z with
      | some y => (h.tree.at t).root == some y
      | none => false
    | _ => false
  else
    match h.objs[x]? with
    | some (.key n) => liveAt n.ks t == ys
    | _ => match topRoot.lookup x with
      | some y => ys == [y]
      | none => false

end Contract
