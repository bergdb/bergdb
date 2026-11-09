----------------------------- MODULE IndexModel -----------------------------
(***************************************************************************)
(* bergdb 020-26: a model of the user indexes of release 2026.4, their     *)
(* maintenance by writers and their jobs (020-10, sections 4 to 6, with    *)
(* 020-18's changes F1, F3, F4 and F5), for the TLC model checker.         *)
(*                                                                         *)
(* One directory with object keys and keys with a suffix; one index name,  *)
(* created, built, activated, deleted and created again, each creation a   *)
(* new generation G with its own entries; writers of the directory; the    *)
(* build of each generation, its steps, its locked phase and its           *)
(* activation; the cleanup of each deleted generation; crashes and         *)
(* restarts.                                                               *)
(*                                                                         *)
(* The Core is the state at the latest time (data, the definition, the     *)
(* entries, the markers) and its conflict check: a transaction has a read  *)
(* time R and a read set, and it is refused (it runs again) if a           *)
(* transaction that committed after R wrote a key of its read set          *)
(* (Db.stmCheckConflicts).  Instead of a history, each transaction in      *)
(* flight keeps 'ws', the tracked keys written since its R; what it reads  *)
(* at R it takes into its own state at R.  Every state of the stream is    *)
(* the latest once, so an invariant on the latest state holds at every     *)
(* lookup time.                                                            *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    ObjKeys,      \* the directory's object keys, integers in key order, e.g. {1, 3}
    SufKeys,      \* its keys with a suffix (never indexed), e.g. {2}: /d/-a.txt
    Writers,      \* the writer threads
    Values,       \* the values: "s", a String, never an object; "a", "b": objects
    Fns,          \* the index functions a creation may choose, a subset of {1, 2}
    StepMax,      \* the values of a build step (Java: 25, and 1 MB since 020-18, F3)
    CleanupMax,   \* the entries of a cleanup step (Java: 100)
    LockedAfter,  \* the refused tries of a step before it runs under the lock (Java: 3)
    MaxCreates,   \* the creations in a behaviour
    MaxCrashes,   \* the crashes in a behaviour
    TimedGen,     \* TRUE: G is the latest transaction's time (Java); FALSE: the creation's count
    Bug,          \* "none", or a planted fault for the negative controls (see the readme)
    Nil, DefKey, VKey, Mgr  \* model values: no value; /#i/didef/-NAME; /#i/div/IDIR; the lock of a definition change

AllKeys == ObjKeys \cup SufKeys
None    == 0                   \* no entry
Gens    == 1..MaxCreates       \* the generations when TimedGen is FALSE

Max(S) == CHOOSE x \in S : \A y \in S : y <= x

(* The index function f (020-10, section 3.3): the level of the entry of value v at key k
   for the definition fn, or None. A key with a suffix, a String and no value have none;
   fn 2 has no entry for "b" (its field absent, say). *)
F(fn, k, v) ==
    IF k \in SufKeys THEN None
    ELSE CASE v = "a" -> 1
           [] v = "b" -> (IF fn = 1 THEN 2 ELSE None)
           [] OTHER   -> None

(* The order of a generation's entries <<level, key>> (020-10, section 4.4). *)
Lt(x, y) == x[1] < y[1] \/ (x[1] = y[1] /\ x[2] < y[2])
MaxE(S)  == CHOOSE x \in S : \A y \in S : ~Lt(x, y)
FirstE(S, n) == {x \in S : Cardinality({y \in S : Lt(y, x)}) < n}

VARIABLES
    \* The stream: the Core's state at the latest time.
    data,       \* [AllKeys -> Values \cup {Nil}]
    def,        \* the definition /#i/didef/-NAME: Nil or [gen, fn, st]
    entries,    \* the entry keys: a set of <<G, level, key>>
    markers,    \* the markers /#i/didel/dNAME/-G16 of deleted generations: a set of G
    now,        \* the latest transaction's time (TimedGen), else 1
    \* Memory, lost at a crash.
    lock,       \* the index manager's lock: Nil, Mgr (a definition change), or a G
                \*   (a build step's locked phase)
    mem,        \* the manager's maps for the name (byName, byIdir): Nil or [gen, fn, st]
    admin,      \* a definition change between its commit and its maps: [pc, g]
    wr,         \* the writers' transactions
    bld,        \* the build threads: G -> state
    cln,        \* the cleanup threads: G -> state
    \* Ghosts, for the checks only.
    ncreate, ncrash, used, clash, refused

stream == <<data, def, entries, markers, now>>
memory == <<lock, mem, admin, wr, bld, cln>>
ghost  == <<ncreate, ncrash, used, clash, refused>>
vars   == <<stream, memory, ghost>>

Tick == now' = IF TimedGen THEN now + 1 ELSE now

IdleW       == [pc |-> "idle", k |-> 0, v |-> Nil, old |-> Nil, S |-> Nil, ws |-> {}]
IdleA       == [pc |-> "idle", g |-> 0]
InitBuild(fn) == [pc |-> "readE", fn |-> fn, E |-> Nil, from |-> 0, batch |-> {},
                  ended |-> FALSE, tries |-> 0, locked |-> FALSE, rs |-> {}, ws |-> {}]
InitClean   == [pc |-> "scan", after |-> Nil, keys |-> {}]
Remove(f, x) == [y \in DOMAIN f \ {x} |-> f[y]]

(* A commit's tracked writes, noted by every transaction in flight that has its R. A
   writer's read set is within {VKey, k}, a build step's is its 'rs', known at its read; so
   each notes only those keys (the same conflicts, fewer states). *)
WrHasR(p) == p.pc \in {"set", "commit"}
WrNoted(WS) == [w \in Writers |->
                  IF WrHasR(wr[w]) THEN [wr[w] EXCEPT !.ws = @ \cup (WS \cap {VKey, wr[w].k})]
                  ELSE wr[w]]
BldNoted(WS) == [g \in DOMAIN bld |->
                  IF bld[g].pc \in {"check", "commit"}
                  THEN [bld[g] EXCEPT !.ws = @ \cup (WS \cap bld[g].rs)] ELSE bld[g]]

-----------------------------------------------------------------------------
(* The writers (RwEnvironmentImp.indexEntries, RwTransaction.executeRw).      *)
(* One put or delete (v = Nil) per transaction.                               *)

(* A write of a key with a suffix: a w() without object operations, with no read time,
   no read set and no lock; it cannot be refused. *)
WSuffix(w, k, v) ==
    /\ wr[w].pc = "idle"
    /\ data' = [data EXCEPT ![k] = v]
    /\ wr' = WrNoted({k})
    /\ bld' = BldNoted({k})
    /\ Tick
    /\ UNCHANGED <<def, entries, markers, lock, mem, admin, cln, ghost>>

(* Step 1 of 020-10, 5.1: R is fixed first; the previous value is the one at R. With the
   planted fault "SBeforeR" (015-43) the index set is read first, then R. *)
Begin(w, k, v) ==
    IF Bug = "SBeforeR"
    THEN /\ lock = Nil
         /\ wr' = [wr EXCEPT ![w] = [pc |-> "fixR", k |-> k, v |-> v, old |-> Nil,
                                     S |-> mem, ws |-> {}]]
    ELSE wr' = [wr EXCEPT ![w] = [pc |-> "set", k |-> k, v |-> v, old |-> data[k],
                                  S |-> Nil, ws |-> {}]]

WStart(w, k, v) ==
    /\ wr[w].pc = "idle"
    /\ Begin(w, k, v)
    /\ UNCHANGED <<stream, lock, mem, admin, bld, cln, ghost>>

(* A transaction that was refused runs again, its action included: a new R. *)
WRerun(w) ==
    /\ wr[w].pc = "rerun"
    /\ Begin(w, wr[w].k, wr[w].v)
    /\ UNCHANGED <<stream, lock, mem, admin, bld, cln, ghost>>

WFixR(w) ==     \* "SBeforeR" only
    /\ wr[w].pc = "fixR"
    /\ wr' = [wr EXCEPT ![w].pc = "commit", ![w].old = data[wr[w].k], ![w].ws = {}]
    /\ UNCHANGED <<stream, lock, mem, admin, bld, cln, ghost>>

(* Steps 2 and 3: the directory's virtual key into the read set; the index set S read under
   the manager's lock (IndexManager.getActiveIndexesForDir). "NoLock": without the lock. *)
WReadS(w) ==
    /\ wr[w].pc = "set"
    /\ Bug = "NoLock" \/ lock = Nil
    /\ wr' = [wr EXCEPT ![w].pc = "commit", ![w].S = mem]
    /\ UNCHANGED <<stream, lock, mem, admin, bld, cln, ghost>>

(* Step 4 and the commit: if S has the index, the previous value's key in the read set,
   f(old) deleted and f(new) put (a put over a delete of one key stays, 015-40). *)
WCommit(w) ==
    LET p  == wr[w]
        RS == (IF Bug = "NoVhash" THEN {} ELSE {VKey})
              \cup (IF p.S # Nil /\ Bug # "NoPrevHash" THEN {p.k} ELSE {})
    IN
    /\ p.pc = "commit"
    /\ IF p.ws \cap RS # {}
       THEN /\ wr' = [wr EXCEPT ![w].pc = "rerun", ![w].old = Nil, ![w].S = Nil, ![w].ws = {}]
            /\ UNCHANGED <<stream, bld>>
       ELSE LET g   == p.S.gen
                lo  == F(p.S.fn, p.k, p.old)
                ln  == F(p.S.fn, p.k, p.v)
                Del == IF lo # None THEN {<<g, lo, p.k>>} ELSE {}
                Put == IF ln # None THEN {<<g, ln, p.k>>} ELSE {}
            IN
            /\ entries' = IF p.S = Nil THEN entries ELSE (entries \ Del) \cup Put
            /\ data' = [data EXCEPT ![p.k] = p.v]
            /\ wr' = [WrNoted({p.k}) EXCEPT ![w] = IdleW]
            /\ bld' = BldNoted({p.k})
            /\ Tick
            /\ UNCHANGED <<def, markers>>
    /\ UNCHANGED <<lock, mem, admin, cln, ghost>>

-----------------------------------------------------------------------------
(* The definitions' changes (IndexManager.create, delete), each under the     *)
(* lock: the commit, then the maps, then the lock released.                   *)

ACreate(fn) ==
    /\ admin.pc = "idle" /\ lock = Nil /\ mem = Nil /\ ncreate < MaxCreates
    /\ LET G == CASE Bug = "ConstGen" -> 1
                  [] TimedGen        -> now        \* the latest transaction's time
                  [] OTHER           -> ncreate + 1
       IN /\ def' = [gen |-> G, fn |-> fn, st |-> "building"]
          /\ lock' = Mgr
          /\ admin' = [pc |-> "create", g |-> G]
          /\ clash' = (clash \/ G \in used)
          /\ used' = used \cup {G}
    /\ wr' = WrNoted({DefKey, VKey})
    /\ bld' = BldNoted({DefKey, VKey})
    /\ ncreate' = ncreate + 1
    /\ Tick
    /\ UNCHANGED <<data, entries, markers, mem, cln, ncrash, refused>>

(* The maps, the lock released, and the build's thread started (IndexBuilderImp.startBuild,
   after the lock: 020-18, item 14). A thread's start is not a step of its own: its first
   step, BReadE, comes when it comes, after any other steps. *)
ACreateMap ==
    /\ admin.pc = "create"
    /\ mem' = def
    /\ lock' = Nil
    /\ bld' = (admin.g :> InitBuild(def.fn)) @@ bld
    /\ admin' = IdleA
    /\ UNCHANGED <<stream, wr, cln, ghost>>

ADelete ==
    /\ admin.pc = "idle" /\ lock = Nil /\ mem # Nil
    /\ def' = Nil
    /\ markers' = markers \cup {mem.gen}
    /\ lock' = Mgr
    /\ admin' = [pc |-> "delete", g |-> mem.gen]
    /\ wr' = WrNoted({DefKey, VKey})
    /\ bld' = BldNoted({DefKey, VKey})
    /\ Tick
    /\ UNCHANGED <<data, entries, mem, cln, ghost>>

(* The maps, the lock released, and the cleanup's thread started. *)
ADeleteMap ==
    /\ admin.pc = "delete"
    /\ mem' = Nil
    /\ lock' = Nil
    /\ cln' = (admin.g :> InitClean) @@ cln
    /\ admin' = IdleA
    /\ UNCHANGED <<stream, wr, bld, ghost>>

-----------------------------------------------------------------------------
(* The build of generation g (IndexBuilderImp.Build).                         *)

IsLive(g) == mem # Nil /\ mem.gen = g

(* The directory's last key at the latest time, read once, at the first step (020-18, F4).
   "NoEndKey": the build reads to the directory's end at every step, as before F4. *)
BReadE(g) ==
    /\ g \in DOMAIN bld /\ bld[g].pc = "readE"
    /\ LET Have == {k \in AllKeys : data[k] # Nil}
           E    == IF Bug = "NoEndKey" THEN Max(AllKeys)
                   ELSE IF Have = {} THEN 0 ELSE Max(Have)
       IN bld' = [bld EXCEPT ![g].E = E, ![g].pc = "read"]
    /\ UNCHANGED <<stream, lock, mem, admin, wr, cln, ghost>>

(* A step's read set (020-18, F1): the definition's key, and the keys of the values whose
   entries it puts. The planted faults: "AllHashes", every key read (before F1);
   "NoValueHash", none; "NoDefHash", not the definition's key. *)
StepRS(fn, B) ==
    (IF Bug = "NoDefHash" THEN {} ELSE {DefKey})
    \cup (CASE Bug = "AllHashes"   -> B
            [] Bug = "NoValueHash" -> {}
            [] OTHER               -> {k \in B : F(fn, k, data[k]) # None})

(* The step's getMany at its R: at most StepMax values after 'from', up to E; the step
   ends the build if it met the end before StepMax values (020-18, F3: not by the count). *)
BRead(g) ==
    /\ g \in DOMAIN bld /\ bld[g].pc = "read"
    /\ LET b == bld[g]
           C == {k \in AllKeys : b.from < k /\ k <= b.E /\ data[k] # Nil}
           B == {k \in C : Cardinality({j \in C : j < k}) < StepMax}
       IN bld' = [bld EXCEPT ![g].batch = {<<k, data[k]>> : k \in B},
                             ![g].ended = (Cardinality(C) < StepMax),
                             ![g].rs = StepRS(b.fn, B),
                             ![g].ws = {}, ![g].pc = "check"]
    /\ UNCHANGED <<stream, lock, mem, admin, wr, cln, ghost>>

(* isLive, under the lock (reentrant in the locked phase): a deleted index's build ends,
   FAILED "deleted"; a locked phase's lock is released. *)
BCheck(g) ==
    /\ g \in DOMAIN bld /\ bld[g].pc = "check"
    /\ lock \in {Nil, g}
    /\ IF IsLive(g) \/ Bug = "NoIsLive"
       THEN /\ bld' = [bld EXCEPT ![g].pc = "commit"]
            /\ UNCHANGED lock
       ELSE /\ bld' = Remove(bld, g)
            /\ lock' = Nil
    /\ UNCHANGED <<stream, mem, admin, wr, cln, ghost>>

(* The step's commit, refused if a key of its read set rs was written since its R: then it
   runs again, and after LockedAfter refusals under the lock. *)
BCommit(g) ==
    /\ g \in DOMAIN bld /\ bld[g].pc = "commit"
    /\ LET b      == bld[g]
           Hashed == {p \in b.batch : F(b.fn, p[1], p[2]) # None}
       IN IF b.ws # {}             \* ws holds only keys of the read set rs
          THEN /\ bld' = [bld EXCEPT
                     ![g].pc    = IF ~b.locked /\ b.tries + 1 >= LockedAfter
                                     /\ Bug # "NoLockedPhase"
                                  THEN "lock" ELSE "read",
                     ![g].tries = IF b.locked \/ b.tries + 1 >= LockedAfter
                                  THEN 0 ELSE b.tries + 1,
                     ![g].batch = {}, ![g].rs = {}, ![g].ws = {}]
               /\ UNCHANGED <<stream, lock>>
          ELSE /\ entries' = entries \cup {<<g, F(b.fn, p[1], p[2]), p[1]>> : p \in Hashed}
               /\ bld' = [bld EXCEPT
                     ![g].pc     = IF b.ended THEN "activate" ELSE "read",
                     ![g].from   = IF b.batch = {} THEN b.from
                                   ELSE Max({p[1] : p \in b.batch}),
                     ![g].batch  = {}, ![g].tries = 0, ![g].locked = FALSE,
                     ![g].rs     = {}, ![g].ws = {}]
               /\ lock' = IF b.locked THEN Nil ELSE lock
               /\ Tick
               /\ UNCHANGED <<data, def, markers>>
    /\ UNCHANGED <<mem, admin, wr, cln, ghost>>

BLock(g) ==
    /\ g \in DOMAIN bld /\ bld[g].pc = "lock"
    /\ lock = Nil
    /\ lock' = g
    /\ bld' = [bld EXCEPT ![g].locked = TRUE, ![g].pc = "read"]
    /\ UNCHANGED <<stream, mem, admin, wr, cln, ghost>>

(* The activation, under the lock (IndexManager.activate): the definition rewritten in state
   active, then the maps; or, if deleted, the build ends FAILED "deleted". *)
BActivate(g) ==
    /\ g \in DOMAIN bld /\ bld[g].pc = "activate"
    /\ lock = Nil
    /\ IF IsLive(g) \/ Bug = "NoActCheck"
       THEN /\ def' = [gen |-> g, fn |-> bld[g].fn, st |-> "active"]
            /\ mem' = [gen |-> g, fn |-> bld[g].fn, st |-> "active"]
            /\ wr' = WrNoted({DefKey})
            /\ bld' = Remove(BldNoted({DefKey}), g)
            /\ Tick
       ELSE /\ bld' = Remove(bld, g)
            /\ UNCHANGED <<def, mem, wr, now>>
    /\ UNCHANGED <<data, entries, markers, lock, admin, cln, ghost>>

-----------------------------------------------------------------------------
(* The cleanup of a deleted generation g (IndexManager.startCleanup), with no  *)
(* read set: a scan at the latest time after the last key deleted (020-18,     *)
(* F5), its deletion; when none is left after it, one scan from the prefix;    *)
(* when that finds none, the marker's deletion.                                *)

CScan(g) ==
    /\ g \in DOMAIN cln /\ cln[g].pc = "scan"
    /\ LET c  == cln[g]
           ES == {<<e[2], e[3]>> : e \in {x \in entries : x[1] = g}}
           A  == IF c.after = Nil THEN ES ELSE {x \in ES : Lt(c.after, x)}
       IN IF A = {}
          THEN IF c.after # Nil /\ Bug # "NoFinalCheck"
               THEN cln' = [cln EXCEPT ![g].after = Nil]
               ELSE cln' = [cln EXCEPT ![g].pc = "end"]
          ELSE cln' = [cln EXCEPT ![g].keys = FirstE(A, CleanupMax), ![g].pc = "del"]
    /\ UNCHANGED <<stream, lock, mem, admin, wr, bld, ghost>>

CDel(g) ==
    /\ g \in DOMAIN cln /\ cln[g].pc = "del"
    /\ LET c == cln[g]
       IN /\ entries' = entries \ {<<g, x[1], x[2]>> : x \in c.keys}
          /\ cln' = [cln EXCEPT ![g].after = MaxE(c.keys), ![g].keys = {}, ![g].pc = "scan"]
    /\ Tick
    /\ UNCHANGED <<data, def, markers, lock, mem, admin, wr, bld, ghost>>

CEnd(g) ==
    /\ g \in DOMAIN cln /\ cln[g].pc = "end"
    /\ markers' = markers \ {g}
    /\ cln' = Remove(cln, g)
    /\ Tick
    /\ UNCHANGED <<data, def, entries, lock, mem, admin, wr, bld, ghost>>

-----------------------------------------------------------------------------
(* A crash, or a stop: memory is lost, every committed transaction kept (a     *)
(* crash that loses a suffix of them gives a state that a crash earlier gives  *)
(* too). The start (IndexManager.start, 020-10, section 4.5) runs before any   *)
(* writer: the definition into the maps, a build for one in state building     *)
(* from the first key, a cleanup per marker; a marker of the live generation   *)
(* refuses the database.                                                       *)

CrashRestart ==
    /\ ncrash < MaxCrashes
    /\ ncrash' = ncrash + 1
    /\ lock' = Nil
    /\ admin' = IdleA
    /\ wr' = [w \in Writers |-> IdleW]
    /\ mem' = def
    /\ bld' = IF def # Nil /\ def.st = "building"
              THEN (def.gen :> InitBuild(def.fn))
              ELSE [x \in {} |-> InitBuild(1)]
    /\ cln' = [g \in markers |-> InitClean]
    /\ refused' = (refused \/ (def # Nil /\ def.gen \in markers))
    /\ UNCHANGED <<stream, ncreate, used, clash>>

-----------------------------------------------------------------------------

Init ==
    /\ data = [k \in AllKeys |-> Nil]
    /\ def = Nil
    /\ entries = {}
    /\ markers = {}
    /\ now = 1
    /\ lock = Nil
    /\ mem = Nil
    /\ admin = IdleA
    /\ wr = [w \in Writers |-> IdleW]
    /\ bld = [x \in {} |-> InitBuild(1)]
    /\ cln = [x \in {} |-> InitClean]
    /\ ncreate = 0
    /\ ncrash = 0
    /\ used = {}
    /\ clash = FALSE
    /\ refused = FALSE

BuildNext(g) == BReadE(g) \/ BRead(g) \/ BCheck(g) \/ BCommit(g) \/ BLock(g) \/ BActivate(g)
CleanNext(g) == CScan(g) \/ CDel(g) \/ CEnd(g)

Next ==
    \/ \E w \in Writers :
          \/ \E k \in SufKeys, v \in {"s", Nil} : WSuffix(w, k, v)
          \/ \E k \in ObjKeys, v \in Values \cup {Nil} : WStart(w, k, v)
          \/ WRerun(w) \/ WFixR(w) \/ WReadS(w) \/ WCommit(w)
    \/ \E fn \in Fns : ACreate(fn)
    \/ ACreateMap \/ ADelete \/ ADeleteMap
    \/ \E g \in DOMAIN bld : BuildNext(g)
    \/ \E g \in DOMAIN cln : CleanNext(g)
    \/ CrashRestart

(* Fairness: a transaction that began runs to its commit or its rerun, a definition change
   to its end, every started thread on; a writer need not begin a transaction, and may begin
   them for ever. *)
Fairness ==
    /\ \A w \in Writers : WF_vars(WRerun(w) \/ WFixR(w) \/ WReadS(w) \/ WCommit(w))
    /\ WF_vars(ACreateMap \/ ADeleteMap)
    /\ \A g \in Gens : WF_vars(BuildNext(g))
    /\ \A g \in Gens : WF_vars(CleanNext(g))

Spec     == Init /\ [][Next]_vars
FairSpec == Spec /\ Fairness

-----------------------------------------------------------------------------
(* The properties.                                                            *)

(* f over the directory's data at the latest time, for the definition fn. *)
Expected(fn) == {<<F(fn, k, data[k]), k>> : k \in {j \in ObjKeys : F(fn, j, data[j]) # None}}
EntriesOf(g) == {<<e[2], e[3]>> : e \in {x \in entries : x[1] = g}}

(* The main property (020-10, 3.4 and 9.1): at every lookup time, an active index's entries
   are f over the data, exactly: none missing, none stale. *)
IndexIsFunction == (def # Nil /\ def.st = "active") => EntriesOf(def.gen) = Expected(def.fn)

(* Stronger: while building too, no entry of the live generation is stale. *)
NoStaleEntry == def # Nil => EntriesOf(def.gen) \subseteq Expected(def.fn)

(* V3 while building (020-22, 4.2): the keys a running build has passed, and those after
   its end key E (020-18, F4: written since the creation), have their entries exactly. *)
LevelsAt(g, k)      == {e[2] : e \in {x \in entries : x[1] = g /\ x[3] = k}}
ExpectedAt(fn, k)   == IF F(fn, k, data[k]) # None THEN {F(fn, k, data[k])} ELSE {}
BuildCovers ==
    \A g \in DOMAIN bld :
        (def # Nil /\ def.gen = g) =>
            \A k \in ObjKeys :
                (k <= bld[g].from \/ (bld[g].E # Nil /\ k > bld[g].E))
                    => LevelsAt(g, k) = ExpectedAt(def.fn, k)

(* V8 (020-22, 4.2): every generation that has entries is the live definition's or has a
   marker, so no entry is out of every cleanup's reach. *)
GensAccounted == \A e \in entries : (def # Nil /\ e[1] = def.gen) \/ e[1] \in markers

(* V7 and the start (020-10, 4.5): no marker names the live generation; no start refuses. *)
MarkerNotLive == def = Nil \/ def.gen \notin markers
StartAccepted == ~refused

(* 4.3: every creation's G differs from every earlier one's. *)
GenFresh == ~clash

(* 5.2: memory and stream agree when no definition change is under way. *)
MemAgrees == admin.pc = "idle" => mem = def

(* The lock is held only by a definition change or by a build in its locked phase. *)
LockSane == /\ (lock = Mgr) <=> (admin.pc # "idle")
            /\ lock \notin {Nil, Mgr} =>
                    lock \in DOMAIN bld /\ bld[lock].locked

Safety == /\ IndexIsFunction /\ NoStaleEntry /\ BuildCovers /\ GensAccounted /\ MarkerNotLive
          /\ StartAccepted /\ GenFresh /\ MemAgrees /\ LockSane

(* Liveness, under Fairness, with MaxCrashes crashes at most: a build ends (its index active
   or deleted); a cleanup ends (its marker gone). *)
Building(g)   == def # Nil /\ def.gen = g /\ def.st = "building"
BuildEnds     == \A g \in Gens : Building(g) ~> ~Building(g)
CleanupEnds   == \A g \in Gens : (g \in markers) ~> (g \notin markers)
NoOrphans     == \A g \in Gens :
                    (\E e \in entries : e[1] = g /\ ~(def # Nil /\ def.gen = g))
                    ~> ~(\E e \in entries : e[1] = g /\ ~(def # Nil /\ def.gen = g))

(* For the timed runs: the commits in a behaviour. *)
CONSTANT MaxTime
TimeBound == now <= MaxTime

Symm == Permutations(Writers)
=============================================================================
