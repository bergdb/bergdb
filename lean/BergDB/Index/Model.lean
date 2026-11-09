/-
The user indexes of BergDB 2026.4 in Lean: the protocol (bergdb 020-29).

The protocol that bergdb 020-26 modelled in TLA+ (its IndexModel.tla, checked
by TLC within small bounds), here for any number of keys, writers, steps,
generations and crashes: one index name over one directory, its writers, the
build of each generation, the activation, the deletion with its marker and
the cleanup, crashes and restarts. A writer's transaction writes any keys,
which 020-26's model left out (its section 2.4). Section numbers are 020-10's (the design)
unless said otherwise; 020-18's F1, F3, F4 and F5 are in, as in the code.

This file is the trusted part: the definitions that the theorems of
BergDB/Index/Theorems.lean are about. Where the model lets a thread choose
(a step's size, the end key, the keys a cleanup reads, when a transaction
gives up), it allows every choice the code can make, and more: a theorem
over the model holds for the code's choices.
-/

namespace BergDB.Index

/-- A key of the directory, in key order: an object key, or a key with a
suffix (020-26, 2.1). -/
scoped notation "Key" => Nat

/-- A generation G (020-10, section 4.3). -/
scoped notation "Gen" => Nat

/-- A time: time t is the state just after the t-th transaction. -/
scoped notation "Time" => Nat

/-- What the model is parametric in: the values V, the index functions F (a
definition's levels, 3.3), the levels L of an entry. -/
structure Spec (V F L : Type) where
  /-- An object key. A key with a suffix is not one (3.3, rule 1). -/
  isObj : Key → Bool
  /-- The index function: the levels of the entry of the value v (none: no
  value) at the key k under the function fn, or none: each value has zero
  or one entry per index (3.3). -/
  f : F → Key → Option V → Option L
  /-- No value has no entry. -/
  f_none : ∀ fn k, f fn k none = none
  /-- A key with a suffix has no entry (3.3, rule 1). -/
  f_suffix : ∀ fn k v, isObj k = false → f fn k v = none
  /-- The refused tries of a build step before it runs under the index
  manager's lock (6.1; 3 in the code). -/
  lockedAfter : Nat

/-- The definition, the value of the key `didef` of the name (4.1, 4.2): its
generation, its function, and its state, building (`active = false`) or
active. -/
structure Def (F : Type) where
  gen : Gen
  fn : F
  active : Bool

/-- The stream: the Core's state at the latest time, what a crash keeps.

* `data k`: the value at the key k of the directory, or none.
* `dfn`: the definition, or none.
* `ent g k l`: the entry key of the generation g with the levels l for the
  key k (bkey(`/#i/dient/dNAME/`) ‖ G8 ‖ levels ‖ K, 4.1); a set.
* `mark g`: the marker of the deleted generation g, its key `didel` of the
  name and G (4.1).
* `now`: the latest transaction's time.
* `wk`, `wdef`, `wv`: the time of the last write of each key of the
  directory, of the definition's key and of the directory's virtual key
  `/#i/div/IDIR` (0: never). They are the Core's history as its conflict
  check reads it (`Db.stmCheckConflicts`): a transaction with the read time
  R is refused if a transaction that committed after R wrote a key of its
  read set. Entries and markers are in no read set, so no time is kept for
  them. -/
structure Stream (V F L : Type) where
  data : Key → Option V
  dfn : Option (Def F)
  ent : Gen → Key → L → Prop
  mark : Gen → Bool
  now : Time
  wk : Key → Time
  wdef : Time
  wv : Time

/-- The index manager's lock (5.2): free, held by a definition change, or by
the build of a generation in its locked phase (6.1). -/
inductive Lock where
  | free
  | mgr
  | bld (g : Gen)
  deriving DecidableEq

/-- A definition change between its commit and its maps (5.2). -/
inductive Admin (F : Type) where
  | idle
  | create (g : Gen) (fn : F)
  | delete (g : Gen)

/-- A writer's transaction in flight (5.1), an `rw()` or a `w()` with an object
key: it writes the keys `ws`, each with its new value `nv` (none: a delete;
several calls on one key: the last wins, 015-41). R fixed, and the previous
values `old` read at R, the data at R (`set`); then the index set S read
under the lock (`commit`). -/
inductive WSt (V F : Type) where
  | idle
  | set (ws : Key → Bool) (nv : Key → Option V) (R : Time) (old : Key → Option V)
  | commit (ws : Key → Bool) (nv : Key → Option V) (R : Time) (old : Key → Option V)
      (S : Option (Def F))

/-- Where a build is (6.1): reading its end key E, reading a step, checking
that its index is live, committing the step, waiting for the lock, or
activating its index. -/
inductive BPc where
  | readE | read | check | commit | lock | activate
  deriving DecidableEq

/-- A build thread of a generation (`IndexBuilderImp.Build`, 6.1). Its keys
below `next` are passed; its step reads the keys from `next` to below `hi` at
its read time R, their values `snap` (the data at R). -/
structure BSt (V F : Type) where
  fn : F
  pc : BPc
  E : Option Key
  next : Key
  hi : Key
  R : Time
  snap : Key → Option V
  ended : Bool
  tries : Nat
  locked : Bool

/-- A build as it starts: from the first key, its end key not read yet. -/
def BSt.init {V F : Type} (fn : F) : BSt V F :=
  { fn := fn, pc := .readE, E := none, next := 0, hi := 0, R := 0,
    snap := fun _ => none, ended := false, tries := 0, locked := false }

/-- The keys a build has passed: those below `next`, and those after its end
key E (020-18, F4). -/
def BSt.passed {V F : Type} (b : BSt V F) (k : Key) : Prop :=
  k < b.next ∨ ∃ e, b.E = some e ∧ e < k

/-- Where a cleanup is (6.2): scanning, deleting what a scan found, or ending
with the marker's deletion. -/
inductive CPc where
  | scan | del | done
  deriving DecidableEq

/-- A cleanup thread of a deleted generation; `keys`: what its scan found. -/
structure CSt (L : Type) where
  pc : CPc
  keys : Key → L → Prop

/-- A cleanup as it starts. -/
def CSt.init {L : Type} : CSt L := { pc := .scan, keys := fun _ _ => False }

/-- Memory, lost at a crash: the lock, the manager's maps for the name
(`mem`), a definition change in progress, the writers' transactions (W: the
writer threads), the build and the cleanup threads by generation. -/
structure Mem (V F L W : Type) where
  lock : Lock
  mem : Option (Def F)
  admin : Admin F
  wr : W → WSt V F
  bld : Gen → Option (BSt V F)
  cln : Gen → Option (CSt L)

/-- The system: the stream at the latest time, the streams at the earlier
times (newest first; for the lookups at those times, and for the crashes that
lose committed transactions), and memory. -/
structure Sys (V F L W : Type) where
  st : Stream V F L
  past : List (Stream V F L)
  m : Mem V F L W

/-- The function f with the value b at a. -/
def upd {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun x => if x = a then b else f x

variable {V F L W : Type}

/-- The stream of a database with the data d0 and no index. -/
def Stream.init (d0 : Key → Option V) : Stream V F L :=
  { data := d0, dfn := none, ent := fun _ _ _ => False, mark := fun _ => false,
    now := 0, wk := fun _ => 0, wdef := 0, wv := 0 }

/-- A start (`IndexManager.start`, 4.5) after a crash or a stop: the maps from
the stream's definition, a build from the first key if it is building, a
cleanup per marker; no writer in flight. (The start's check that no marker
names the live generation is theorem `start_accepted`.) -/
def restart (st : Stream V F L) : Mem V F L W :=
  { lock := .free, mem := st.dfn, admin := .idle, wr := fun _ => .idle,
    bld := fun g => match st.dfn with
      | some d => if d.gen = g ∧ d.active = false then some (BSt.init d.fn) else none
      | none => none,
    cln := fun g => if st.mark g = true then some CSt.init else none }

/-- The system at its first start, with the data d0 and no index. -/
def Sys.init (d0 : Key → Option V) : Sys V F L W :=
  ⟨Stream.init d0, [], restart (Stream.init d0)⟩

/-- A commit: the new stream, the old one kept as the previous time's. -/
def Sys.commit (s : Sys V F L W) (st' : Stream V F L) (m' : Mem V F L W) : Sys V F L W :=
  ⟨st', s.st :: s.past, m'⟩

/-- The data after a transaction that writes the keys ws with the values nv. -/
def writeData (data : Key → Option V) (ws : Key → Bool) (nv : Key → Option V) :
    Key → Option V :=
  fun k => if ws k = true then nv k else data k

/-- The last write times after a transaction at the time t that writes the
keys ws. -/
def writeTimes (wk : Key → Time) (ws : Key → Bool) (t : Time) : Key → Time :=
  fun k => if ws k = true then t else wk k

/-- The entries after a writer's commit (5.1, step 4): if S has the index, at
each key k written, f(old) deleted and f(new) put; an entry both deleted and
put stays (015-40). -/
def wEntries (sp : Spec V F L) (ent : Gen → Key → L → Prop) (S : Option (Def F))
    (ws : Key → Bool) (old nv : Key → Option V) : Gen → Key → L → Prop :=
  match S with
  | none => ent
  | some d => fun g k l =>
      (ent g k l ∧ ¬ (g = d.gen ∧ ws k = true ∧ sp.f d.fn k (old k) = some l)) ∨
      (g = d.gen ∧ ws k = true ∧ sp.f d.fn k (nv k) = some l)

/-- The entries after a build step's commit: f of each value it read (6.1). -/
def bEntries (sp : Spec V F L) (ent : Gen → Key → L → Prop) (g : Gen) (b : BSt V F) :
    Gen → Key → L → Prop :=
  fun g' k l => ent g' k l ∨ (g' = g ∧ b.next ≤ k ∧ k < b.hi ∧ sp.f b.fn k (b.snap k) = some l)

variable [DecidableEq W]

/-- The steps, each atomic; a thread's steps interleave with every other
thread's (020-26, section 2.3). A step that commits a transaction moves the
time by one. -/
inductive Step (sp : Spec V F L) : Sys V F L W → Sys V F L W → Prop where
  /-- `WSuffix`: a `w()` of keys with a suffix only: no read time, no read
  set, no lock, no index (5.1, "Which writes"); it cannot be refused. -/
  | wSuffix (s : Sys V F L W) (ws : Key → Bool) (nv : Key → Option V) :
      (∀ k, ws k = true → sp.isObj k = false) →
      Step sp s (s.commit
        { s.st with data := writeData s.st.data ws nv,
                    wk := writeTimes s.st.wk ws (s.st.now + 1), now := s.st.now + 1 } s.m)
  /-- `WStart`: R fixed first, the latest transaction's time (5.1, step 1);
  the previous values are those at R. Any keys, those with a suffix too. -/
  | wStart (s : Sys V F L W) (w : W) (ws : Key → Bool) (nv : Key → Option V) :
      s.m.wr w = .idle →
      Step sp s { s with m := { s.m with wr := upd s.m.wr w (.set ws nv s.st.now s.st.data) } }
  /-- `WReadS`: the index set S read from the maps under the lock (5.1, step 3). -/
  | wReadS (s : Sys V F L W) (w : W) (ws : Key → Bool) (nv : Key → Option V) (R : Time)
      (old : Key → Option V) :
      s.m.wr w = .set ws nv R old → s.m.lock = .free →
      Step sp s { s with m := { s.m with wr := upd s.m.wr w (.commit ws nv R old s.m.mem) } }
  /-- `WCommit`: the read set is the virtual key (step 2) and, if S has the
  index, the keys written (step 4); the Core accepts the transaction if none
  of them was written after R. At each key written, f(old) deleted and f(new)
  put. (An `rw()`'s own reads add keys to its read set: it is refused more
  often, which `wDrop` allows.) -/
  | wCommit (s : Sys V F L W) (w : W) (ws : Key → Bool) (nv : Key → Option V) (R : Time)
      (old : Key → Option V) (S : Option (Def F)) :
      s.m.wr w = .commit ws nv R old S →
      s.st.wv ≤ R → (S ≠ none → ∀ k, ws k = true → s.st.wk k ≤ R) →
      Step sp s (s.commit
        { s.st with data := writeData s.st.data ws nv, ent := wEntries sp s.st.ent S ws old nv,
                    wk := writeTimes s.st.wk ws (s.st.now + 1), now := s.st.now + 1 }
        { s.m with wr := upd s.m.wr w .idle })
  /-- A transaction in flight ends without a commit: refused by the Core's
  check (it runs again, a new `wStart`), or ended by an exception. Allowed at
  any time: more than the code does. -/
  | wDrop (s : Sys V F L W) (w : W) :
      Step sp s { s with m := { s.m with wr := upd s.m.wr w .idle } }
  /-- `ACreate`: under the lock, G the latest transaction's time (4.3); the
  definition (building) and the virtual key written in one transaction. -/
  | aCreate (s : Sys V F L W) (fn : F) :
      s.m.admin = .idle → s.m.lock = .free → s.m.mem = none →
      Step sp s (s.commit
        { s.st with dfn := some ⟨s.st.now, fn, false⟩, wdef := s.st.now + 1,
                    wv := s.st.now + 1, now := s.st.now + 1 }
        { s.m with lock := .mgr, admin := .create s.st.now fn })
  /-- `ACreateMap`: the maps, the lock released, the build's thread started. -/
  | aCreateMap (s : Sys V F L W) (g : Gen) (fn : F) :
      s.m.admin = .create g fn →
      Step sp s { s with m := { s.m with mem := s.st.dfn, lock := .free, admin := .idle,
                                         bld := upd s.m.bld g (some (BSt.init fn)) } }
  /-- `ADelete`: under the lock, the definition deleted, the marker put and
  the virtual key written in one transaction (6.2). -/
  | aDelete (s : Sys V F L W) (d : Def F) :
      s.m.admin = .idle → s.m.lock = .free → s.m.mem = some d →
      Step sp s (s.commit
        { s.st with dfn := none, mark := upd s.st.mark d.gen true, wdef := s.st.now + 1,
                    wv := s.st.now + 1, now := s.st.now + 1 }
        { s.m with lock := .mgr, admin := .delete d.gen })
  /-- `ADeleteMap`: the maps, the lock released, the cleanup's thread started. -/
  | aDeleteMap (s : Sys V F L W) (g : Gen) :
      s.m.admin = .delete g →
      Step sp s { s with m := { s.m with mem := none, lock := .free, admin := .idle,
                                         cln := upd s.m.cln g (some CSt.init) } }
  /-- `BReadE`: the end key E, read once (020-18, F4): a key after which the
  directory has no value. The code reads its last key; any key after it is
  allowed too. -/
  | bReadE (s : Sys V F L W) (g : Gen) (b : BSt V F) (e : Key) :
      s.m.bld g = some b → b.pc = .readE → (∀ k, e < k → s.st.data k = none) →
      Step sp s { s with m := { s.m with bld := upd s.m.bld g (some { b with E := some e, pc := .read }) } }
  /-- `BRead`: a step's read at its read time R, the latest time: the keys from
  `next` to below `hi`, up to E. Any `hi` is allowed (the code's: 25 values or
  1 MB, 020-18, F3); the step that reaches E ends the build. -/
  | bRead (s : Sys V F L W) (g : Gen) (b : BSt V F) (e hi : Key) :
      s.m.bld g = some b → b.pc = .read → b.E = some e → b.next ≤ hi → hi ≤ e + 1 →
      Step sp s { s with m := { s.m with bld := upd s.m.bld g (some
        { b with hi := hi, R := s.st.now, snap := s.st.data, ended := decide (hi = e + 1),
                 pc := .check }) } }
  /-- `BCheck`: `isLive`, under the lock (reentrant in the locked phase). -/
  | bCheck (s : Sys V F L W) (g : Gen) (b : BSt V F) (d : Def F) :
      s.m.bld g = some b → b.pc = .check → (s.m.lock = .free ∨ s.m.lock = .bld g) →
      s.m.mem = some d → d.gen = g →
      Step sp s { s with m := { s.m with bld := upd s.m.bld g (some { b with pc := .commit }) } }
  /-- `BCheck` of a deleted index: the build ends, FAILED "deleted", its lock
  released. -/
  | bCheckFail (s : Sys V F L W) (g : Gen) (b : BSt V F) :
      s.m.bld g = some b → b.pc = .check → (s.m.lock = .free ∨ s.m.lock = .bld g) →
      (∀ d, s.m.mem = some d → d.gen ≠ g) →
      Step sp s { s with m := { s.m with bld := upd s.m.bld g none, lock := .free } }
  /-- `BCommit`: the step's read set is the definition's key and the keys of
  the values whose entries it puts (020-18, F1); accepted if none was written
  after R. -/
  | bCommit (s : Sys V F L W) (g : Gen) (b : BSt V F) :
      s.m.bld g = some b → b.pc = .commit → s.st.wdef ≤ b.R →
      (∀ k, b.next ≤ k → k < b.hi → sp.f b.fn k (b.snap k) ≠ none → s.st.wk k ≤ b.R) →
      Step sp s (s.commit
        { s.st with ent := bEntries sp s.st.ent g b, now := s.st.now + 1 }
        { s.m with bld := upd s.m.bld g (some
                      { b with pc := if b.ended = true then .activate else .read, next := b.hi,
                               tries := 0, locked := false }),
                   lock := if b.locked = true then .free else s.m.lock })
  /-- `BCommit` refused: the step runs again, after `lockedAfter` refused tries
  in its locked phase (`runStep`). -/
  | bRefused (s : Sys V F L W) (g : Gen) (b : BSt V F) :
      s.m.bld g = some b → b.pc = .commit →
      (b.R < s.st.wdef ∨ ∃ k, b.next ≤ k ∧ k < b.hi ∧ sp.f b.fn k (b.snap k) ≠ none ∧
        b.R < s.st.wk k) →
      Step sp s { s with m := { s.m with bld := upd s.m.bld g (some
        { b with pc := if b.locked = false ∧ sp.lockedAfter ≤ b.tries + 1 then .lock else .read,
                 tries := if b.locked = true ∨ sp.lockedAfter ≤ b.tries + 1 then 0
                          else b.tries + 1 }) } }
  /-- `BLock`: the locked phase takes the lock. -/
  | bLock (s : Sys V F L W) (g : Gen) (b : BSt V F) :
      s.m.bld g = some b → b.pc = .lock → s.m.lock = .free →
      Step sp s { s with m := { s.m with lock := .bld g,
                                         bld := upd s.m.bld g (some { b with locked := true, pc := .read }) } }
  /-- `BActivate`: under the lock, the definition rewritten active, then the
  maps (`IndexManager.activate`). -/
  | bActivate (s : Sys V F L W) (g : Gen) (b : BSt V F) (d : Def F) :
      s.m.bld g = some b → b.pc = .activate → s.m.lock = .free → s.m.mem = some d → d.gen = g →
      Step sp s (s.commit
        { s.st with dfn := some ⟨g, b.fn, true⟩, wdef := s.st.now + 1, now := s.st.now + 1 }
        { s.m with mem := some ⟨g, b.fn, true⟩, bld := upd s.m.bld g none })
  /-- `BActivate` of a deleted index: the build ends, FAILED "deleted". -/
  | bActivateFail (s : Sys V F L W) (g : Gen) (b : BSt V F) :
      s.m.bld g = some b → b.pc = .activate → s.m.lock = .free →
      (∀ d, s.m.mem = some d → d.gen ≠ g) →
      Step sp s { s with m := { s.m with bld := upd s.m.bld g none } }
  /-- `CScan`: a scan of the generation's entries at the latest time; what it
  found is deleted next. Any set is allowed (the code's: 100 entries after the
  last deleted, 020-18, F5). -/
  | cScan (s : Sys V F L W) (g : Gen) (c : CSt L) (keys : Key → L → Prop) :
      s.m.cln g = some c → c.pc = .scan →
      Step sp s { s with m := { s.m with cln := upd s.m.cln g (some { c with pc := .del, keys := keys }) } }
  /-- `CScan` from the generation's prefix that finds no entry: the end. -/
  | cScanEnd (s : Sys V F L W) (g : Gen) (c : CSt L) :
      s.m.cln g = some c → c.pc = .scan → (∀ k l, ¬ s.st.ent g k l) →
      Step sp s { s with m := { s.m with cln := upd s.m.cln g (some { c with pc := .done }) } }
  /-- `CDel`: the deletion, a transaction with no read set. -/
  | cDel (s : Sys V F L W) (g : Gen) (c : CSt L) :
      s.m.cln g = some c → c.pc = .del →
      Step sp s (s.commit
        { s.st with ent := fun g' k l => s.st.ent g' k l ∧ ¬ (g' = g ∧ c.keys k l),
                    now := s.st.now + 1 }
        { s.m with cln := upd s.m.cln g (some { c with pc := .scan }) })
  /-- `CEnd`: the marker deleted, the thread ends. -/
  | cEnd (s : Sys V F L W) (g : Gen) (c : CSt L) :
      s.m.cln g = some c → c.pc = .done →
      Step sp s (s.commit { s.st with mark := upd s.st.mark g false, now := s.st.now + 1 }
        { s.m with cln := upd s.m.cln g none })
  /-- A crash or a stop, then a start: memory lost. The stream is the latest
  one or, as a crash may lose the last committed transactions (levels.md,
  section 8), one of an earlier time; the times after it are gone. -/
  | crash (s : Sys V F L W) (pre : List (Stream V F L)) (x : Stream V F L)
      (rest : List (Stream V F L)) :
      s.st :: s.past = pre ++ x :: rest →
      Step sp s ⟨x, rest, restart x⟩

/-- The reachable systems: from a database with any data and no index. -/
inductive Reach (sp : Spec V F L) : Sys V F L W → Prop where
  | init (d0 : Key → Option V) : Reach sp (Sys.init d0)
  | step {s s' : Sys V F L W} : Reach sp s → Step sp s s' → Reach sp s'

/-- The stream at the lookup time t, if the system has it: the stream of the
latest time t. -/
def Sys.at (s : Sys V F L W) (t : Time) : Option (Stream V F L) :=
  (s.st :: s.past).find? (fun x => x.now == t)

end BergDB.Index
