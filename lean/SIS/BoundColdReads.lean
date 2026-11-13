/-
Self-indexed streams in Lean: bounds, part 3, a cold start's reads counted as
reads, not as objects made (bergdb item 007; 007-03, step 6; 007-09's second
review). Trusted part: the definitions. The theorems are in
SIS/BoundColdReadsTheorems.lean, the proofs in SIS/Proof/BoundColdReads.lean.
Added 2026-11-13.

Why. The cold-read theorems of SIS/BoundColdTheorems.lean count the handles
the lazy startup gives out (`Mem.next`), one per object. The second review
(items/007-bounds/09-t4-in-lean/second-review.md) finds three kinds of reads
that make no object:

* "`sectionNodes` uses `eraseDups`, whereas Java's `StoredTrans.Parser.parse`
  retains every version with `nodeList.add(stored)`": a start parses every
  version of R(s), ..., R(k) (`sectionVersions`).
* "Java's top-node fallback, `cache.liveHandle(idOf(pos))` in
  `NodeCollection.linkToCanonical` ... Ordinary `followStreamPointer` calls
  `readNodeHeader` before finding a cached object. These reads allocate no
  object; add explicit header-read accounting." (`topHeaderReads`,
  `Mem.followReads`.)
* "Java's `Dag.merge` can read the left sibling, reject it, then read the
  right ... Count the actual operation footprint, including quiet follows."
  (the parameter `sib` of `lazyReads`.)

What a cold start reads, in Java (`DbStarter.doOrdinaryStartup`), and its count
here (`lazyReads`):

1. The section R(s), ..., R(k), every version of each record
   (`StoredTrans.Parser.parse`: `nodeList.add(stored)` for each node of the
   record): `sectionVersions`.
2. The top node of the last transaction (`DbStarter.topNodeOfLastTransaction`):
   a header read where its position is not a version of the section
   (`readNodeHeader(pos).id()`), and its version (`canonicalNode`): 2.
3. Rule 4 (`DbStarter.linkD`, `NodeCollection.linkToCanonical`): no read but
   the top-node fallback, `if (live == null && id == null && top) live =
   cache.liveHandle(idOf(pos))`, where `idOf` reads the header at `pos` once:
   at most one header read for each pointer of a top node of D
   (`topHeaderReads`). With assertions on (`AssertStatus.enabled()`, the
   tests), `checkLinkById` reads a header for every pointer of D; production
   runs without assertions, so it is not counted.
4. The rerun (`DbStarter.rerunTransaction`), as the lazy startup's step 3
   (`lazyStartup`): for each first touch of a stream pointer on the writer's
   path, `NodeCollection.followStreamPointer` reads the header at the pointer's
   position (its step 1, `nodeStream.readNodeHeader(pointerPos)`, for a
   pointer with no handle that names a written version), and then the version
   unless the node's handle holds a usable object (its step 4,
   `readVersion`): `Mem.followReads`. Each node of gd(j) without a canonical
   object is read from its version (`DbStarter.canonicalNode`,
   `readNode(pos)`): `Mem.canonicalNodeReads`. And the reads of the writer
   outside its paths, which the model's change does not show: `Dag.merge`'s
   siblings, read by `followQuietly` (`Dag.sibling`), the left one possibly
   rejected before the right one is read; `sib tr` such follows for the
   transaction tr, each a header and a version.
-/
import SIS.BoundCold

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- The versions of R(s), ..., R(k), every one of them, with repeats: what
the start parses (`StoredTrans.Parser.parse`). -/
def sectionVersions (S : Stream V T) (s : Nat) : Nat :=
  ((S.drop s).map (fun R => R.vers.length)).sum

/-- The reads of the writer's follow of the slot of object hp for pointee y
(`Mem.follow` with `writer := true`; `NodeCollection.followStreamPointer`): for
a stream slot that names a record, a header read; then, if the node table has
no usable object, the version read. A memory slot reads nothing. -/
def Mem.followReads (S : Stream V T) (m : Mem V) (hp : Nat) (y : NodeId) : Nat :=
  match (m.obj? hp).bind (·.slot? y) with
  | some (Slot.stream r) =>
    let hdr := if r.isSome then 1 else 0
    let r' := ruleRRef S m.s y r
    let usable : Bool := match m.tableOf y with
      | some h0 => match m.obj? h0 with
        | some o0 => o0.usable r'
        | none => false
      | none => false
    hdr + (if usable then 0 else
      match r' with
      | some r'' => if (S.versionAt r'' y).isSome then 1 else 0
      | none => 0)
  | _ => 0

/-- The reads of `Mem.reachOnPath`: those of its follow, if it follows. -/
def Mem.reachOnPathReads (sp : Spec V T) (S : Stream V T) (P : Struct V) (j : Time)
    (path : List NodeId) (m : Mem V) (x : NodeId) : Nat :=
  match m.canonicalOf x with
  | some _ => 0
  | none =>
    let parent := path.find? (fun p => match P.get? p, m.canonicalOf p with
      | some n, some _ => (sp.live (n.hist.upTo (j - 1))).contains x
      | _, _ => false)
    match parent with
    | some p => match m.canonicalOf p with
      | some hp => m.followReads S hp x
      | none => 0
    | none => 0

/-- The reads of `Mem.canonicalNode` (`DbStarter.canonicalNode`): the version,
if there is no canonical object and there is a version to read. -/
def Mem.canonicalNodeReads (S : Stream V T) (m : Mem V) (x : NodeId) : Nat :=
  match m.canonicalOf x with
  | some _ => 0
  | none => if ((newest S m.s x).or (S.lv x)).isSome then 1 else 0

/-- The header reads of rule 4's top-node fallback (`linkToCanonical`): one for
each pointer, live or dead, of the version that the start makes canonical for
each top node of D, the gd(j) of the section (with a virtual root, a node
other than the root on level `topLevel` or above). -/
def topHeaderReads (sp : Spec V T) (S : Stream V T) (s : Nat) : Nat :=
  ((sectionIdx S s).map (fun j =>
    match S[j]? with
    | some R => (R.gd.map (fun x =>
        match (newest S s x).or (S.lv x) with
        | some w => if sp.virt && x != root && decide (sp.topLevel ≤ w.level) then
            (pointees sp w.hist).length else 0
        | none => 0)).sum
    | none => 0)).sum

/-- The memory before the rerun: steps 1 and 2 of `lazyStartup` and its
memory slots between canonical objects, as there. -/
def lazyMemBase (sp : Spec V T) (S : Stream V T) : Mem V :=
  let s := lastSp S
  let m0 : Mem V := { objs := [], table := [], s := s, root := 0, next := 1 }
  let m1 := (sectionNodes S s).foldl (fun (m : Mem V) x =>
    match newest S s x with
    | some w =>
      if (w.hist.upTo s).isEmpty then m else
      let (m', h) := m.addObj (canonOfVersion sp S s w)
      m'.setTable x h
    | none => m) m0
  let m2 : Mem V :=
    if sp.virt then
      let rv := rootVersion sp s (topsRead sp S s true)
      let (m', h) := m1.addObj { (canonOfVersion sp S s rv) with hist := rv.hist, pos := none }
      { m'.setTable root h with root := h }
    else
      match m1.canonicalOf root with
      | some h => { m1 with root := h }
      | none =>
        match topVersion S s true with
        | some w =>
          let (m', h) := m1.addObj (canonOfVersion sp S s w)
          { m'.setTable root h with root := h }
        | none => m1
  m2.linkCanonical

/-- One transaction of the counted rerun: see `lazyReadsRun`. -/
def lazyReadStep (sp : Spec V T) (sib : T → Nat) (S : Stream V T)
    (acc : (Mem V × Struct V) × Nat) (j : Nat) : (Mem V × Struct V) × Nat :=
  match S[j]? with
  | some R =>
    match R.trans with
    | some tr =>
      let P := acc.1.2
      let c := sp.exec tr j (view sp P (j - 1))
      let path := pathOf sp P c j
      let path' := path.mergeSort (fun a b => decide
        (((P.get? b).map (·.level)).getD 0 ≤ ((P.get? a).map (·.level)).getD 0))
      let r1 := path'.foldl (fun (a : Mem V × Nat) x =>
        (a.1.reachOnPath sp S P j path x, a.2 + a.1.reachOnPathReads sp S P j path x))
        (acc.1.1, 0)
      let m := r1.1.applyChange sp P j c
      let r2 := R.gd.foldl (fun (a : Mem V × Nat) x =>
        (a.1.canonicalNode sp S x, a.2 + a.1.canonicalNodeReads S x)) (m, 0)
      ((r2.1, P.apply j c), acc.2 + r1.2 + r2.2 + 2 * sib tr)
    | none => acc
  | none => acc

/-- The rerun of `lazyStartup` (step 3), with its reads counted
(`lazyReadStep`): for each transaction T(j) of the section, the reads of the
writer's follows on its paths (`Mem.reachOnPathReads`), of the nodes of gd(j)
made canonical (`Mem.canonicalNodeReads`), and 2 `sib tr` for the writer's
follows outside its paths (`Dag.merge`'s siblings). The memory and P are those
of `lazyStartup` (`lazyReadsRun_mem`). -/
def lazyReadsRun (sp : Spec V T) (sib : T → Nat) (S : Stream V T) : (Mem V × Struct V) × Nat :=
  (sectionIdx S (lastSp S)).foldl (lazyReadStep sp sib S)
    ((lazyMemBase sp S, baseStruct sp S (lastSp S) true), 0)

/-- What a cold start from S reads (see the file's header): every version of
the section, 2 for the top node of the last transaction, the header reads of
rule 4's top-node fallback, and the rerun's reads. -/
def lazyReads (sp : Spec V T) (sib : T → Nat) (S : Stream V T) : Nat :=
  sectionVersions S (lastSp S) + 2 + topHeaderReads sp S (lastSp S) + (lazyReadsRun sp sib S).2

/-- The writer's follows outside its paths, summed over the transactions of
the section: `sib tr` for each. -/
def sibReach (sib : T → Nat) (S : Stream V T) : Nat :=
  ((sectionIdx S (lastSp S)).map (fun j =>
    match S[j]? with
    | some R => match R.trans with
      | some tr => sib tr
      | none => 0
    | none => 0)).sum

end SIS
