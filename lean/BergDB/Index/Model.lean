/-
The user indexes of BergDB 2026.4 in Lean: the protocol (bergdb 020-29).

The protocol that bergdb 020-26 modelled in TLA+ (its IndexModel.tla, checked
by TLC within small bounds), here for any number of keys, directories, index
names, writers, steps, generations and crashes: the indexes, each a name with
a definition over a directory, their writers, the build of each generation,
the activation, the deletion with its marker and the cleanup, crashes and
restarts. A writer's transaction writes any keys, in any directories, and
reads the index set of each key under the lock, as the code does; 020-26's
model has one name, one directory and transactions of one key (its section
2.4). Section numbers are 020-10's (the design) unless said otherwise;
020-18's F1, F3, F4 and F5 are in, as in the code.

This file is the trusted part: the definitions that the theorems of
BergDB/Index/Theorems.lean are about. Where the model lets a thread choose
(a step's size, the end key, the keys a cleanup reads, when a transaction
gives up), it allows every choice the code can make, and more: a theorem
over the model holds for the code's choices.
-/

namespace BergDB.Index

/-- A key of the database, in key order; each is in one directory, as an
object key or a key with a suffix (020-26, 2.1). -/
scoped notation "Key" => Nat

/-- A generation G (020-10, section 4.3). -/
scoped notation "Gen" => Nat

/-- A time: time t is the state just after the t-th transaction. -/
scoped notation "Time" => Nat

/-- An index's name. -/
scoped notation "Name" => Nat

/-- A directory, as its virtual key `/#i/div/IDIR` names it (4.1). -/
scoped notation "Dir" => Nat

/-- What the model is parametric in: the values V, the index functions F (a
definition's directory and levels, 3.3, 4.2), the levels L of an entry. -/
structure Spec (V F L : Type) where
  /-- An object key. A key with a suffix is not one (3.3, rule 1). -/
  isObj : Key → Bool
  /-- The directory of a key: its own directory, not a parent's (015-30). -/
  dirOf : Key → Dir
  /-- The directory that an index function indexes (the definition's `dir`). -/
  dirF : F → Dir
  /-- The index function: the levels of the entry of the value v (none: no
  value) at the key k under the function fn, or none: each value has zero
  or one entry per index (3.3). -/
  f : F → Key → Option V → Option L
  /-- No value has no entry. -/
  f_none : ∀ fn k, f fn k none = none
  /-- A key with a suffix has no entry (3.3, rule 1). -/
  f_suffix : ∀ fn k v, isObj k = false → f fn k v = none
  /-- A key of another directory has no entry. -/
  f_dir : ∀ fn k v, dirOf k ≠ dirF fn → f fn k v = none
  /-- The refused tries of a build step before it runs under the index
  manager's lock (6.1; 3 in the code). -/
  lockedAfter : Nat

/-- A definition, the value of the key `didef` of its name (4.1, 4.2): its
generation, its function (with its directory), and its state, building
(`active = false`) or active. -/
structure Def (F : Type) where
  gen : Gen
  fn : F
  active : Bool

/-- The stream: the Core's state at the latest time, what a crash keeps.

* `data k`: the value at the key k, or none.
* `dfn n`: the definition of the name n, or none.
* `ent n g k l`: the entry key of the name n, the generation g, the levels l,
  for the key k (bkey(`/#i/dient/dNAME/`) ‖ G8 ‖ levels ‖ K, 4.1); a set.
* `mark n g`: the marker of the deleted generation g of the name n, its key
  `didel` of the name and G (4.1).
* `now`: the latest transaction's time.
* `wk`, `wdef`, `wv`: the time of the last write of each key, of each name's
  definition key and of each directory's virtual key (0: never). They are
  the Core's history as its conflict check reads it (`Db.stmCheckConflicts`):
  a transaction with the read time R is refused if a transaction that
  committed after R wrote a key of its read set. Entries and markers are in
  no read set, so no time is kept for them. -/
structure Stream (V F L : Type) where
  data : Key → Option V
  dfn : Name → Option (Def F)
  ent : Name → Gen → Key → L → Prop
  mark : Name → Gen → Bool
  now : Time
  wk : Key → Time
  wdef : Name → Time
  wv : Dir → Time

/-- The index manager's lock (5.2): free, held by a definition change, or by
the build of a name's generation in its locked phase (6.1). -/
inductive Lock where
  | free
  | mgr
  | bld (n : Name) (g : Gen)
  deriving DecidableEq

/-- A definition change between its commit and its maps (5.2). -/
inductive Admin (F : Type) where
  | idle
  | create (n : Name) (g : Gen) (fn : F)
  | delete (n : Name) (g : Gen)

/-- The name of a definition change in progress. -/
def Admin.name {F : Type} : Admin F → Option Name
  | .idle => none
  | .create n _ _ => some n
  | .delete n _ => some n

/-- A writer's transaction in flight (5.1), an `rw()` or a `w()` with an object
key: it writes the keys `ws`, each with its new value `nv` (none: a delete;
several calls on one key: the last wins, 015-41). R is fixed and the previous
values `old` read at R, the data at R; then, for each key, the index set of
its directory read under the lock (`IndexManager.getActiveIndexesForDir`), a
key at a time as the code does: `S k`, the maps when read, or none. -/
inductive WSt (V F : Type) where
  | idle
  | run (ws : Key → Bool) (nv : Key → Option V) (R : Time) (old : Key → Option V)
      (S : Key → Option (Name → Option (Def F)))

/-- Where a build is (6.1): reading its end key E, reading a step, checking
that its index is live, committing the step, waiting for the lock, or
activating its index. -/
inductive BPc where
  | readE | read | check | commit | lock | activate
  deriving DecidableEq

/-- A build thread of a name's generation (`IndexBuilderImp.Build`, 6.1). Its
keys below `next` are passed; its step reads the keys from `next` to below
`hi` at its read time R, their values `snap` (the data at R). -/
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

/-- Memory, lost at a crash: the lock, the manager's maps (`mem`), a definition
change in progress, the writers' transactions (W: the writer threads), the
build and the cleanup threads by name and generation. -/
structure Mem (V F L W : Type) where
  lock : Lock
  mem : Name → Option (Def F)
  admin : Admin F
  wr : W → WSt V F
  bld : Name → Gen → Option (BSt V F)
  cln : Name → Gen → Option (CSt L)

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

/-- The function f of a name and a generation with the value b at (n, g). -/
def upd2 {β : Type} (f : Name → Gen → β) (n : Name) (g : Gen) (b : β) : Name → Gen → β :=
  fun n' g' => if n' = n ∧ g' = g then b else f n' g'

variable {V F L W : Type}

/-- The stream of a database with the data d0 and no index. -/
def Stream.init (d0 : Key → Option V) : Stream V F L :=
  { data := d0, dfn := fun _ => none, ent := fun _ _ _ _ => False,
    mark := fun _ _ => false, now := 0, wk := fun _ => 0, wdef := fun _ => 0,
    wv := fun _ => 0 }

/-- A start (`IndexManager.start`, 4.5) after a crash or a stop: the maps from
the stream's definitions, a build from the first key for each one building, a
cleanup per marker; no writer in flight. (The start's check that no marker
names a live generation is theorem `start_accepted`.) -/
def restart (st : Stream V F L) : Mem V F L W :=
  { lock := .free, mem := st.dfn, admin := .idle, wr := fun _ => .idle,
    bld := fun n g => match st.dfn n with
      | some d => if d.gen = g ∧ d.active = false then some (BSt.init d.fn) else none
      | none => none,
    cln := fun n g => if st.mark n g = true then some CSt.init else none }

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

/-- The index set m has an index of the directory dir. -/
def hasIdx (sp : Spec V F L) (m : Name → Option (Def F)) (dir : Dir) : Prop :=
  ∃ n d, m n = some d ∧ sp.dirF d.fn = dir

/-- The index of the name n that a writer maintains at the key k: the name's
definition in the index set it read for k, if it writes k. -/
def idxAt (ws : Key → Bool) (S : Key → Option (Name → Option (Def F))) (k : Key)
    (n : Name) : Option (Def F) :=
  if ws k = true then (match S k with | some m => m n | none => none) else none

/-- The entries after a writer's commit (5.1, step 4): at each key k written,
for each index in the set read for k, f(old) deleted and f(new) put; an entry
both deleted and put stays (015-40). -/
def wEntries (sp : Spec V F L) (ent : Name → Gen → Key → L → Prop) (ws : Key → Bool)
    (S : Key → Option (Name → Option (Def F))) (old nv : Key → Option V) :
    Name → Gen → Key → L → Prop :=
  fun n g k l =>
    match idxAt ws S k n with
    | some d => (ent n g k l ∧ ¬ (g = d.gen ∧ sp.f d.fn k (old k) = some l)) ∨
                (g = d.gen ∧ sp.f d.fn k (nv k) = some l)
    | none => ent n g k l

/-- The entries after a build step's commit: f of each value it read (6.1). -/
def bEntries (sp : Spec V F L) (ent : Name → Gen → Key → L → Prop) (n : Name) (g : Gen)
    (b : BSt V F) : Name → Gen → Key → L → Prop :=
  fun n' g' k l => ent n' g' k l ∨
    (n' = n ∧ g' = g ∧ b.next ≤ k ∧ k < b.hi ∧ sp.f b.fn k (b.snap k) = some l)

/-- The build after its step's commit. -/
def bAfter (b : BSt V F) : BSt V F :=
  { b with pc := if b.ended = true then .activate else .read, next := b.hi, tries := 0,
           locked := false }

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
      Step sp s
        { s with m :=
          { s.m with wr := upd s.m.wr w (.run ws nv s.st.now s.st.data (fun _ => none)) } }
  /-- `WReadS`: the index set of the key k's directory read from the maps,
  under the lock (5.1, step 3). -/
  | wReadS (s : Sys V F L W) (w : W) (k : Key) (ws : Key → Bool) (nv : Key → Option V)
      (R : Time) (old : Key → Option V) (S : Key → Option (Name → Option (Def F))) :
      s.m.wr w = .run ws nv R old S → s.m.lock = .free →
      Step sp s
        { s with m :=
          { s.m with wr := upd s.m.wr w (.run ws nv R old (upd S k (some s.m.mem))) } }
  /-- `WCommit`: each object key written has its index set read; the read set
  is the virtual key of each such key's directory (step 2) and each such key
  whose set has an index of its directory (step 4); the Core accepts the
  transaction if none of them was written after R. At each key written, for
  each index of its set, f(old) deleted and f(new) put. A key with a suffix in
  the transaction adds nothing to the read set (`objectOps` has object keys
  only). (An `rw()`'s own reads add keys to its read set: it is refused more
  often, which `wDrop` allows.) -/
  | wCommit (s : Sys V F L W) (w : W) (ws : Key → Bool) (nv : Key → Option V) (R : Time)
      (old : Key → Option V) (S : Key → Option (Name → Option (Def F))) :
      s.m.wr w = .run ws nv R old S →
      (∀ k, ws k = true → sp.isObj k = true → ∃ m, S k = some m ∧
        s.st.wv (sp.dirOf k) ≤ R ∧ (hasIdx sp m (sp.dirOf k) → s.st.wk k ≤ R)) →
      Step sp s (s.commit
        { s.st with data := writeData s.st.data ws nv, ent := wEntries sp s.st.ent ws S old nv,
                    wk := writeTimes s.st.wk ws (s.st.now + 1), now := s.st.now + 1 }
        { s.m with wr := upd s.m.wr w .idle })
  /-- A transaction in flight ends without a commit: refused by the Core's
  check (it runs again, a new `wStart`), or ended by an exception. Allowed at
  any time: more than the code does. -/
  | wDrop (s : Sys V F L W) (w : W) :
      Step sp s { s with m := { s.m with wr := upd s.m.wr w .idle } }
  /-- `ACreate`: under the lock, G the latest transaction's time, at least 1
  (4.3; `Math.max(1, ...)` in the code); the definition (building), and the
  virtual key of its directory, written in one transaction. -/
  | aCreate (s : Sys V F L W) (n : Name) (fn : F) :
      s.m.admin = .idle → s.m.lock = .free → s.m.mem n = none →
      Step sp s (s.commit
        { s.st with dfn := upd s.st.dfn n (some ⟨max 1 s.st.now, fn, false⟩),
                    wdef := upd s.st.wdef n (s.st.now + 1),
                    wv := upd s.st.wv (sp.dirF fn) (s.st.now + 1), now := s.st.now + 1 }
        { s.m with lock := .mgr, admin := .create n (max 1 s.st.now) fn })
  /-- `ACreateMap`: the maps, the lock released, the build's thread started. -/
  | aCreateMap (s : Sys V F L W) (n : Name) (g : Gen) (fn : F) :
      s.m.admin = .create n g fn →
      Step sp s
        { s with m :=
          { s.m with
            mem := upd s.m.mem n (s.st.dfn n), lock := .free, admin := .idle,
            bld := upd2 s.m.bld n g (some (BSt.init fn)) } }
  /-- `ADelete`: under the lock, the definition deleted, the marker put and
  the virtual key of its directory written in one transaction (6.2). -/
  | aDelete (s : Sys V F L W) (n : Name) (d : Def F) :
      s.m.admin = .idle → s.m.lock = .free → s.m.mem n = some d →
      Step sp s (s.commit
        { s.st with dfn := upd s.st.dfn n none, mark := upd2 s.st.mark n d.gen true,
                    wdef := upd s.st.wdef n (s.st.now + 1),
                    wv := upd s.st.wv (sp.dirF d.fn) (s.st.now + 1), now := s.st.now + 1 }
        { s.m with lock := .mgr, admin := .delete n d.gen })
  /-- `ADeleteMap`: the maps, the lock released, the cleanup's thread started. -/
  | aDeleteMap (s : Sys V F L W) (n : Name) (g : Gen) :
      s.m.admin = .delete n g →
      Step sp s
        { s with m :=
          { s.m with
            mem := upd s.m.mem n none, lock := .free, admin := .idle,
            cln := upd2 s.m.cln n g (some CSt.init) } }
  /-- `BReadE`: the end key E, read once (020-18, F4): a key after which no
  value has an entry. The code reads the directory's last key, after which
  the directory has no value; any key after it is allowed too. -/
  | bReadE (s : Sys V F L W) (n : Name) (g : Gen) (b : BSt V F) (e : Key) :
      s.m.bld n g = some b → b.pc = .readE →
      (∀ k, e < k → sp.f b.fn k (s.st.data k) = none) →
      Step sp s
        { s with m :=
          { s.m with bld := upd2 s.m.bld n g (some { b with E := some e, pc := .read }) } }
  /-- `BRead`: a step's read at its read time R, the latest time: the keys from
  `next` to below `hi`, up to E. Any `hi` is allowed (the code's: 25 values or
  1 MB, 020-18, F3); the step that reaches E ends the build. -/
  | bRead (s : Sys V F L W) (n : Name) (g : Gen) (b : BSt V F) (e hi : Key) :
      s.m.bld n g = some b → b.pc = .read → b.E = some e → b.next ≤ hi → hi ≤ e + 1 →
      Step sp s
        { s with m :=
          { s.m with
            bld := upd2 s.m.bld n g (some
              { b with hi := hi, R := s.st.now, snap := s.st.data,
                       ended := decide (hi = e + 1), pc := .check }) } }
  /-- `BCheck`: `isLive`, under the lock (reentrant in the locked phase). -/
  | bCheck (s : Sys V F L W) (n : Name) (g : Gen) (b : BSt V F) (d : Def F) :
      s.m.bld n g = some b → b.pc = .check → (s.m.lock = .free ∨ s.m.lock = .bld n g) →
      s.m.mem n = some d → d.gen = g →
      Step sp s
        { s with m := { s.m with bld := upd2 s.m.bld n g (some { b with pc := .commit }) } }
  /-- `BCheck` of a deleted index: the build ends, FAILED "deleted", its lock
  released. -/
  | bCheckFail (s : Sys V F L W) (n : Name) (g : Gen) (b : BSt V F) :
      s.m.bld n g = some b → b.pc = .check → (s.m.lock = .free ∨ s.m.lock = .bld n g) →
      (∀ d, s.m.mem n = some d → d.gen ≠ g) →
      Step sp s
        { s with m := { s.m with bld := upd2 s.m.bld n g none, lock := .free } }
  /-- `BCommit`: the step's read set is the definition's key and the keys of
  the values whose entries it puts (020-18, F1); accepted if none was written
  after R. -/
  | bCommit (s : Sys V F L W) (n : Name) (g : Gen) (b : BSt V F) :
      s.m.bld n g = some b → b.pc = .commit → s.st.wdef n ≤ b.R →
      (∀ k, b.next ≤ k → k < b.hi → sp.f b.fn k (b.snap k) ≠ none → s.st.wk k ≤ b.R) →
      Step sp s (s.commit
        { s.st with ent := bEntries sp s.st.ent n g b, now := s.st.now + 1 }
        { s.m with bld := upd2 s.m.bld n g (some (bAfter b)),
                   lock := if b.locked = true then .free else s.m.lock })
  /-- `BCommit` refused: the step runs again, after `lockedAfter` refused tries
  in its locked phase (`runStep`). -/
  | bRefused (s : Sys V F L W) (n : Name) (g : Gen) (b : BSt V F) :
      s.m.bld n g = some b → b.pc = .commit →
      (b.R < s.st.wdef n ∨ ∃ k, b.next ≤ k ∧ k < b.hi ∧ sp.f b.fn k (b.snap k) ≠ none ∧
        b.R < s.st.wk k) →
      Step sp s
        { s with m :=
          { s.m with
            bld := upd2 s.m.bld n g (some
              { b with
                pc := if b.locked = false ∧ sp.lockedAfter ≤ b.tries + 1 then .lock else .read,
                tries := if b.locked = true ∨ sp.lockedAfter ≤ b.tries + 1 then 0
                         else b.tries + 1 }) } }
  /-- `BLock`: the locked phase takes the lock. -/
  | bLock (s : Sys V F L W) (n : Name) (g : Gen) (b : BSt V F) :
      s.m.bld n g = some b → b.pc = .lock → s.m.lock = .free →
      Step sp s
        { s with m :=
          { s.m with
            lock := .bld n g,
            bld := upd2 s.m.bld n g (some { b with locked := true, pc := .read }) } }
  /-- `BActivate`: under the lock, the definition rewritten active, then the
  maps (`IndexManager.activate`). -/
  | bActivate (s : Sys V F L W) (n : Name) (g : Gen) (b : BSt V F) (d : Def F) :
      s.m.bld n g = some b → b.pc = .activate → s.m.lock = .free → s.m.mem n = some d →
      d.gen = g →
      Step sp s (s.commit
        { s.st with dfn := upd s.st.dfn n (some ⟨g, b.fn, true⟩),
                    wdef := upd s.st.wdef n (s.st.now + 1), now := s.st.now + 1 }
        { s.m with mem := upd s.m.mem n (some ⟨g, b.fn, true⟩),
                   bld := upd2 s.m.bld n g none })
  /-- `BActivate` of a deleted index: the build ends, FAILED "deleted". -/
  | bActivateFail (s : Sys V F L W) (n : Name) (g : Gen) (b : BSt V F) :
      s.m.bld n g = some b → b.pc = .activate → s.m.lock = .free →
      (∀ d, s.m.mem n = some d → d.gen ≠ g) →
      Step sp s { s with m := { s.m with bld := upd2 s.m.bld n g none } }
  /-- A step's try ended by an exception that the build takes again (a
  `DbException` other than a conflict, an expired read; 6.1, "Errors"): the
  step again from its start, unlocked, its tries from 0; `underLock` released
  the lock if the step held it. -/
  | bRetry (s : Sys V F L W) (n : Name) (g : Gen) (b : BSt V F) :
      s.m.bld n g = some b → (b.pc = .read ∨ b.pc = .check ∨ b.pc = .commit ∨ b.pc = .lock) →
      Step sp s
        { s with m :=
          { s.m with
            bld := upd2 s.m.bld n g (some { b with pc := .read, tries := 0, locked := false }),
            lock := if b.locked = true then .free else s.m.lock } }
  /-- A build's thread ends without its activation: FAILED by an exception that
  it does not take again, or a stop of the database (6.1, "Errors"); the lock
  released if it held it. The definition stays building until the next start. -/
  | bAbort (s : Sys V F L W) (n : Name) (g : Gen) (b : BSt V F) :
      s.m.bld n g = some b →
      Step sp s
        { s with m :=
          { s.m with
            bld := upd2 s.m.bld n g none,
            lock := if b.locked = true then .free else s.m.lock } }
  /-- `CScan`: a scan of the generation's entries at the latest time; what it
  found is deleted next. Any set is allowed (the code's: 100 entries after the
  last deleted, 020-18, F5). -/
  | cScan (s : Sys V F L W) (n : Name) (g : Gen) (c : CSt L) (keys : Key → L → Prop) :
      s.m.cln n g = some c → c.pc = .scan →
      Step sp s
        { s with m :=
          { s.m with cln := upd2 s.m.cln n g (some { c with pc := .del, keys := keys }) } }
  /-- `CScan` from the generation's prefix that finds no entry: the end. -/
  | cScanEnd (s : Sys V F L W) (n : Name) (g : Gen) (c : CSt L) :
      s.m.cln n g = some c → c.pc = .scan → (∀ k l, ¬ s.st.ent n g k l) →
      Step sp s
        { s with m := { s.m with cln := upd2 s.m.cln n g (some { c with pc := .done }) } }
  /-- `CDel`: the deletion, a transaction with no read set. -/
  | cDel (s : Sys V F L W) (n : Name) (g : Gen) (c : CSt L) :
      s.m.cln n g = some c → c.pc = .del →
      Step sp s (s.commit
        { s.st with ent := fun n' g' k l => s.st.ent n' g' k l ∧ ¬ (n' = n ∧ g' = g ∧ c.keys k l),
                    now := s.st.now + 1 }
        { s.m with cln := upd2 s.m.cln n g (some { c with pc := .scan }) })
  /-- `CEnd`: the marker deleted, the thread ends. -/
  | cEnd (s : Sys V F L W) (n : Name) (g : Gen) (c : CSt L) :
      s.m.cln n g = some c → c.pc = .done →
      Step sp s (s.commit { s.st with mark := upd2 s.st.mark n g false, now := s.st.now + 1 }
        { s.m with cln := upd2 s.m.cln n g none })
  /-- A cleanup's thread ends without its end: an exception that it does not take
  again, or a stop (6.2, "Errors"); the marker stays, and the next start
  resumes the cleanup. -/
  | cAbort (s : Sys V F L W) (n : Name) (g : Gen) (c : CSt L) :
      s.m.cln n g = some c →
      Step sp s { s with m := { s.m with cln := upd2 s.m.cln n g none } }
  /-- Reclaim's cut of lookup times: the oldest times are gone; a lookup at
  one of them is refused (`LookupTimeNotAvailableException`), and so is a
  transaction whose R is one of them, which `wDrop` and `bRetry` allow. -/
  | cut (s : Sys V F L W) (j : Nat) :
      Step sp s { s with past := s.past.take j }
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
