/-
The contract package (bergdb 030-07): the bridge's clauses in the model's
words, computed, for the trace checker (BridgeCheck.lean). `TopOK`,
`TouchOK`, A6' (`adoptAt`) and A-COPY (`CopyStep`) speak of every node of the
model's structure; here each is computed over the lists that the structure
and the change hold (`topOkB`, `touchB`, `adoptB`, `copyB`), with the model's
own functions (`reachList`, `reachFrom`, `pointees`); R4, that the top node
made reaches every older one, by the trace checker's chain of skip pointers
(`r4Fast`, lean/Check/R4.lean, proved there to give R4: the model's
`topClosure` walks every path and is exponential in the number of top nodes).
Proof/BridgeModel.lean proves that each computation gives its clause
(`topOkB_sound`, `touchB_sound`, `adoptB_sound`, `copyB_sound`).

`copyB` computes a sufficient form of A-COPY: of the nodes of the writer's
paths it takes those that the change itself changes, touches or leaves
unreachable, not their ancestors. If it holds, A-COPY holds.
Nothing here needs Mathlib.
-/
import Check.R4
import Contract.Bridge

namespace Contract

open SIS (Struct Changes Entry History Node NewNode Spec)
open SIS.Check (BVal)

variable (sp : Spec BVal Nat)

/-! ## The touch -/

/-- The touch rules, computed. -/
def touchB (P : Struct BVal) (i : Nat) (c : Changes BVal) : Bool :=
  let rl := SIS.reachList sp P (i - 1)
  c.touch.all (fun x => SIS.isIndex P x) && c.touch.all (fun x => rl.contains x) &&
  (c.touch.isEmpty || rl.all (fun q => c.touch.contains q || q == SIS.root ||
    match P.get? q with
    | some nq =>
      let sub := SIS.reachFrom sp P (i - 1) q nq
      c.touch.all (fun x => !sub.contains x)
    | none => true))

/-! ## A6' -/

/-- A6' (`adoptAt`), computed. -/
def adoptB (P : Struct BVal) (i : Nat) : Bool :=
  let rl := SIS.reachList sp P i
  rl.all (fun x => match P.get? x with
    | some n =>
      let lv := sp.live (n.hist.upTo i)
      (SIS.pointees sp n.hist).all (fun y => lv.contains y || !rl.contains y ||
        (match P.get? y with
          | some ny => ny.isData
          | none => false) ||
        (SIS.reachFrom sp P i x n).contains y)
    | none => true)

/-! ## A-COPY -/

/-- A-COPY, a sufficient form, computed: `P'` is the structure after the
change. -/
def copyB (P P' : Struct BVal) (i : Nat) (c : Changes BVal) : Bool :=
  let rl := SIS.reachList sp P (i - 1)
  let rl' := SIS.reachList sp P' i
  let touched := fun z => SIS.changed c z || c.touch.contains z ||
    (rl.contains z && !rl'.contains z)
  let S := rl.filter touched
  c.adds.all (fun a => (sp.ptrs a.2).all (fun y =>
    (c.new.map (·.id)).contains y || S.contains y ||
    S.any (fun z => match P.get? z with
      | some nz => (SIS.pointees sp nz.hist).contains y &&
          (SIS.written sp z || (sp.live (nz.hist.upTo (i - 1))).contains y)
      | none => false)))

/-! ## The top -/

/-- `VirtStep`, computed: `P'` is the structure after the change. -/
def virtB (P P' : Struct BVal) (i : Nat) (c : Changes BVal) : Bool :=
  let rl' := SIS.reachList sp P' i
  c.new.all (fun nn => !decide (sp.topLevel ≤ nn.level) ||
    (!nn.isData && c.adds.any (fun a => a.1 == nn.id) &&
      c.new.all (fun nn' => !decide (sp.topLevel ≤ nn'.level) || nn' == nn))) &&
  c.adds.all (fun a => a.1 == SIS.root ||
    match P.get? a.1 with
    | some n => decide (n.level < sp.topLevel)
    | none => true) &&
  decide (c.adds.filter (fun a => a.1 == SIS.root) =
    (c.new.filter (fun nn => decide (sp.topLevel ≤ nn.level))).map
      (fun nn => (SIS.root, sp.rootVal nn.id))) &&
  c.new.all (fun nn => !decide (sp.topLevel ≤ nn.level) ||
    match P'.get? nn.id with
    | some _ => SIS.TopBridge.r4Fast sp P P' nn.id
    | none => true) &&
  P'.all (fun q => q.1 == SIS.root || !decide (sp.topLevel ≤ q.2.level) ||
    (SIS.pointees sp q.2.hist).all (fun y => !rl'.contains y || !SIS.isTop sp P' y))

/-- The link of the model's top to the tree's space root, computed. -/
def topLinkB (P : Struct BVal) (i : Nat) (s : Tree) : Bool :=
  match P.get? SIS.root with
  | some n0 =>
    match sp.live (n0.hist.upTo i) with
    | [z] =>
      match P.get? z with
      | some nz =>
        decide (nz.level < n0.level) &&
        (match sp.live (nz.hist.upTo i) with
          | [y] =>
            s.root == some y &&
            (match s.obj y with
              | some (.key n) => decide (n.level < nz.level)
              | _ => false) &&
            (s.obj SIS.root).isNone && (s.obj z).isNone
          | _ => false)
      | none => false
    | _ => false
  | none => false

/-- The top's clauses (`TopOK`), computed: `P'` is the structure after the
change. -/
def topOkB (P P' : Struct BVal) (i : Nat) (s s' : Tree) (c : Changes BVal) : Bool :=
  let rl := SIS.reachList sp P (i - 1)
  let rl' := SIS.reachList sp P' i
  virtB sp P P' i c &&
  c.new.all (fun nn => (s.obj nn.id).isSome || (P.get? nn.id).isNone) &&
  c.adds.all (fun a => (s'.obj a.1).isSome ||
    (rl'.contains a.1 &&
      (match P.get? a.1 with
        | some n => !n.isData
        | none => true) &&
      (sp.ptrs a.2).all (fun y => match P'.get? a.1, P'.get? y with
        | some n, some m => decide (m.level < n.level)
        | _, _ => false))) &&
  c.new.all (fun nn => (s'.obj nn.id).isSome || rl'.contains nn.id) &&
  rl'.all (fun y => (s'.obj y).isSome || rl.contains y || (c.new.map (·.id)).contains y) &&
  topLinkB sp P' i s'

end Contract
