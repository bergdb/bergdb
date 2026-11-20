# 030-28. The tested writer is the proved writer, checked routinely

Created 2026-11-19 by Frans Lundberg. Status: done.

Java's writer PE is proved in lean/contract/Contract/PeWriter.lean (030-21;
here C). The level scripts check Java against the model on traces with the
tree checker (`treecheck`: lean/Check/Tree.lean, lean/Check/TreeRun.lean),
which runs a copy, lean/SIS/Tree/Pe.lean (here S), not C. That S and C make
the same trees was shown once, by 026-25's `pecmp`, which compared the
trees from the space roots only and was a step of no script; S was not
pinned in lean/contract/statements.pin, and `lean/contract/gate.sh`, which
checks the pins, runs only with proof work. An independent review of
030-21 (2026-11-19, finding 1) showed the risk: change how Java and S cut a
full list, and every check passes while Java differs from the proved C.
This item closes that gap, and adds a routine check of the pinned files.
Done by an agent of the day's coordinator, on the branch
`030-28-writer-copy-checked`.


# Result

- **(B), not (A)** (section 1): the checkers keep running S, and S is
  compared with C routinely. Running C in the checkers would need an
  adapter that either copies S's rule for Java's ids or checks the ids
  more weakly than today.
- **`pecmp` is a step of `level2.sh`** (step 8c; so `night.sh` runs it), on
  every trace of level 2's tree sets, small, drain and reclaim, the sets
  that the tree checker runs (section 2). It moved from 026-25's item to
  lean/pecmp/, a Lake package without Mathlib that builds C from
  lean/contract's own files, and compares more than before: the writes in
  their order, the ids' order, and the top node (its ordinal, time, root,
  skip pointers and their cached times), besides the trees. On this
  branch's traces: 41 traces, 7,195 transactions, 1,062 new top nodes, 0
  differ. Its own tests (`--cap-h`, `--top-fault`) fail as they must, and
  so does the review's counterexample (S's cut sizes larger-first: 1,232
  transactions differ).
- **S and pecmp are pinned** in statements.pin (section 3), beside the
  statements' files; `pin.sh` writes them, `gate.sh` checks them as before.
  No statement changed: the 99 earlier pins are unchanged, 7 files added.
- **The pins are checked every night**: `lean/contract/pins.sh` (the hashes
  of statements.pin, no build, no Mathlib), step 0 of `level2.sh`. It
  fails on a changed or a removed pinned file (its own test, and by hand:
  a space appended to S gives PINS FAILED, section 3).
- **The depth guard is unreachable** on a stream that Java wrote and that
  is not damaged (section 5): Java's PE refuses nothing; the guard needs a
  path of more than 1,000 key nodes in one segment tree, and a tree that
  meets the invariants that PE keeps and the tree checker checks has at
  most 63 levels in a segment tree at any node size. 030-21's acceptance
  premises (`FuelOk`, `Room`) are premises on the model's parameters G and
  H, which Java does not have, and hold for every transaction Java admits
  with G = 8,192 and H = 100. No 028 entry.
- lean/README.md's opening states the proofs' state; releases/next.md has
  the entry for PE and record format 8, with the StreamDigest digests
  before and after in section 6.


# 1. (A) or (B)

(A) was to run C itself in the checkers, through an adapter from C's
representation to the trace's. Evaluated by reading the tree checker and
the list of differences in the review:

- **The package.** lean/contract requires `sis` (lean/), so a checker in
  `sis` cannot import `Contract.*`. A checker that runs C lives in a
  package that requires `sis` and builds C's files without Mathlib, as
  lean/contractcheck/ does (028-24) and lean/pecmp/ now does. Possible.
- **The ids.** The tree checker compares Java's ids with the model's: C-T1
  compares the nodes made (NEW: id, level, kind) and the entries added
  (ADD, by node id), and C-T9's whole run (`wholeRun`) compares every
  record and D with Java's. C gives fresh ids one apart from any base and
  gives none to a delete node; Java (and S) give ids two apart and one to
  each delete that deletes (`ValueNode.createDelete`). C's output does not
  say where a delete took an id between its other fresh ids (a delete
  writes nothing in C). An adapter that maps C's ids to Java's must replay
  `applyGroups`' order of operations, which is S's rule again, a copy in
  another place; one that accepts any order-preserving renaming checks the
  ids more weakly than C-T1 and C-T9 do today.
- **The top.** C's `newTopNode` takes the whole top, the list of every
  top node with its skip pointers' cached times; the checker holds the
  super root only, and would rebuild the list from P at each transaction
  (pecmp does this now).
- **The rest is mechanical**: bitmaps as lists against sorted sets
  (normalize), the noop flags (the checker computes them from `get`, not
  from the writer), the record wrapper (S's `exec` gives `Changes` sorted
  by id, with the touch).

So (A) could not be done in this task with the checks keeping their
strength, and (B) was done: S stays the checkers' writer, compared with C
on every trace that the tree checker reads, at every transaction, so that
"Java = S" (the tree checker, node for node with the ids) and "S = C"
(pecmp) together give "Java = C" on those traces; and S is pinned, so that
a change of S shows in review as a change of the statements does.


# 2. pecmp, a step of level 2

**Where.** lean/pecmp/: `PeCmp.lean` (the tool), `check.sh` (its runs and
its own tests) and a Lake package (`lakefile.toml`) that requires `sis`
and builds C's closure (Contract.Tree, Read, Statement, Reach, Shape, Top,
PeWriter; none imports Mathlib) from lean/contract/'s own files
(`srcDir = "../contract"`), as lean/contractcheck/ builds the checkers: the
file pecmp runs is the file 030-21 proves. 026-25's copy in
items/026-release-2026-6/25-pe-java/pecmp/ stays as that item's record.

**What it compares** (PeCmp.lean's header). For each transaction of a
trace of format 3: Java's structure P before it, as the tree checker reads
it; S as the tree checker runs it (`Pe.runOps`, and `Pe.peTx` for the
writes) and C with the contract's tree of P and the whole top of P (every
top node in the order of the root's entries, with the cached time of each
skip pointer), the cut size M / 2 for both. Then:

1. both refuse, or neither (the checker's `runOps` and `peTx` too);
2. the writes in their order: the same number; the k-th write of each is
   the same old node or a node made by both; the ids of the nodes made
   correspond one to one and in the same order; each write is the same
   object (a value's hash; a key node's level, kind and klongs, children
   renamed, bitmaps as sets);
3. the trees after it, walked from the space roots (026-25's comparison),
   with the walk's renaming equal to the writes';
4. the top: a new top node from S if and only if from C; then the same
   time, root and ordinal (C's is the top's length, S's the super root's
   ordinal and one), the same skip pointers by index and target, C's
   cached time of each the target's time in P, and the new top node's id
   after every node made. Without a new top node, C's space roots are
   unchanged. Before the transaction: the root's last top node is the
   super root, and the number of top nodes is its ordinal and one.

**Its own tests** (`check.sh`, before the sets): `--cap-h` gives C the cut
size h instead of M / 2 (must fail on the drain set's d-30 traces, which
cut lists at node size 30; seed 2's does); `--top-fault` gives C a top
with one more top node at its start, so that every new top node's ordinal
is one too high (must fail on mixed-1, which makes new top nodes).

**The review's counterexample**, by hand: S's `partSizes` changed to
larger-first for every cut (as if Java and S had changed together), pecmp
built and run on the three sets: PECMP FAILED, 185 of 1,448 transactions
(small), 938 of 2,824 (drain), 109 of 2,923 (reclaim) differ; S restored,
PECMP OK. The pin check fails on the same change (section 3).

**Results** on this branch's traces (treeconf.sh with 2 seeds, reclaim 1):
small 14 traces, 1,448 transactions, 285 new top nodes; drain 22, 2,824,
621; reclaim 5, 2,923, 156; 0 differ, PECMP OK, about 5 s in all. The run
of level 2 is in section 7.

**In level2.sh**: step 8c, after 8b, on the traces that step 8 wrote:
`(cd lean/pecmp && lake build)`, then `lean/pecmp/check.sh small drain
reclaim`. night.sh runs level2.sh full, so pecmp runs every night on the
full sets (10 seeds, reclaim 3). The medium set (night.sh's
`contractconf.sh medium`) is not compared routinely: an option, a few
minutes more a night.


# 3. The pins

**S and pecmp pinned.** `lean/contract/pin.sh` writes, beside the trusted
closure of the main theorems and the files it listed before, seven files
that are no statement but whose change must show in review: S
(lean/SIS/Tree/Pe.lean), lean/pecmp/'s PeCmp.lean, check.sh, lakefile.toml,
lean-toolchain and lake-manifest.json, and lean/contract/pins.sh. Pinning
them changes no statement: statements.pin's 99 earlier lines are
unchanged, 7 lines are added (106 files). `gate.sh` is not changed: its
step 5 checks every file of statements.pin, and with a base commit that
every commit that changed a pinned file changed statements.pin too; it so
covers the new pins. GATE OK on this branch (section 7). A change of S or
pecmp now needs `pin.sh` (which needs the contract package built, with
Mathlib) and statements.pin in the same commit.

**The routine check.** `lean/contract/pins.sh` checks the hashes of
statements.pin with `shasum -a 256 -c`, without a build and without
Mathlib, in about a second; `level2.sh` runs it first (step 0), so a
pinned file changed outside proof work fails the same night. It does not
check that the closure is all pinned (that needs the build: `gate.sh`,
step 5). Its own test, in a temporary copy of the pinned files and the pin
file: the copy passes; with a space appended to the first pinned file, and
to S, it fails; with the first pinned file removed, it fails. The test
also fails if S is not pinned. By hand in the tree: a space appended to S,
`pins.sh` prints PINS FAILED with `lean/SIS/Tree/Pe.lean: FAILED`, and the
fragment of step 0 prints LEVEL 2 FAILED with the file; S restored, PINS
OK.


# 4. The descriptions

- lean/README.md: the opening said "Work in progress", not what a user
  relies on. It now states the proofs' state: the core algorithms proved,
  given tested assumptions (030's readme), Java checked on traces, the
  copy S compared with C in level 2; the four packages; and, beside the
  contract checkers' build, the pins and pecmp.
- releases/next.md: the entry for PE and record format 8 under "The
  stream" (026-25, 027-08), with the digests' reference to section 6.
- 027-08, section 5, and 027-17: pecmp a step of level2.sh, S pinned.
- 030's readme: this file, and "Where the contract's checks run".


# 5. Can a transaction admitted at the go point fail inside PE?

The question (the review's finding 4): `Db.execute` refuses a transaction
before its go point (`Db.checkLimits`: at most 500 operations, keys of at
most 111 bytes, 56 KiB of keys, 32 MiB in all; the key and value
transformations); after it, whatever throws fails the database (005-01).
PE (java/src/bergdb/dag/PeWriter.java) runs after the go point.
030-21's `pe_accepts` shows that C accepts a transaction whose puts' keys
the tree can hold, given `FuelOk` and `Room`, which Java does not check.

**What can throw in Java's PE**, by reading PeWriter.java:

- `planFrame`'s depth guard: a descent of more than `MAX_DEPTH` = 1,000 key
  nodes in one segment tree throws the follower's `cycle`, in a database
  a `StreamFormatException` (`NodeCollection.cycle`: "the pointers make a
  cycle"). The short way's
  guard (`shortWay`) returns false, and the plan runs: no failure.
- `DbException`: no root at tt; a key node that is not a segment leaf and
  has no live klong; a pointer that names a value or nothing where a key
  node is expected. Each is a damaged stream.
- `Bug`: the space root settled to nothing or emitted as more than one
  node, a segment root emitted as more than one node, a join without a
  right neighbour, a root of one entry from a cut. Each is a defect of
  the code, the cases where C would give none from a state it keeps
  (030-21, part 3).
- Nothing else refuses: Java has no level bounds G and H and no fuel
  (026-25, section 2: "nothing is refused"); 027-08, section 1, "The writer
  refuses nothing". The recursions within a segment tree (rebalance,
  settle, emit) are bounded by its height; the walk over segments is a
  loop of frames (a key of BergDB's own may have 8,193 segments).

**The depth guard on a tree Java wrote.** Every key node of a segment tree
is one height above its children (KindsOK), so every path from a segment
root to a segment leaf has the root's height plus one nodes. PE keeps the
fill: `rebalance` joins every changed child, not a root, with fewer than m
live entries with a neighbour, until it has none or no neighbour is left,
and an untouched node keeps its count; `settleRoot` makes an inner root of
one entry its child. So an inner root has at least 2 live entries
(RootsOK) and every other key node at least m (FillOK, with merges on,
m >= 2 at every node size Java uses: 2 at node size 8, 8 at 30). Both are
checked on Java's tree after every traced transaction (the tree checker's
C-T6, `Inv.lean`'s walk), with no failure in level 2's sets. A segment
tree whose root is at height e then holds at least 2 m^e live entries in
its segment leaves, each with a distinct compare value, a 64-bit number:
2 m^e <= 2^64, so e <= 63 at m = 2 and e <= 21 at m = 8. A path has at
most 64 key nodes, far below 1,000: **unreachable** but on a damaged
stream, which is what the guard is for. No test: the guard cannot be
reached through the API, and a damaged stream is the corrupt-stream tests'
matter (027-08, section 1).

**The acceptance premises.** `FuelOk` and `Room` are premises on the
model's parameters G (the most segments, less one) and H (the most
heights, less one), which number and bound the levels and decide no node:
`decideNode`, `rebalance` and `settleRoot` do not read them, and `mkNode`
only refuses a node outside them. Java has neither. For the parameters
G = 8,192 (a key of BergDB's own has at most 8,193 segments) and H = 100:

- `Room`: h = 17 and cap = 15 at node size 30 (at least 2); and
  2^(H - e) > nodes + p holds for e <= 21 (above) whenever the tree has
  fewer than 2^78 nodes, beyond any stream;
- `FuelOk`: (G + 1)(H + 1)(M + p + 2H + 6) = 8,193 * 101 * (236 + p) <=
  2^40 for p up to about 1.3 million operations; a user transaction has at
  most 500 (L1), a reclaim step puts at most 16 kB of scanned KVs and its
  row (024-17, 5.5), the start's rerun a record's KVs;
- `pe_full`'s top base, (G + 1)(H + 1) + 1 = 827,494, is below 2^62.

So every transaction that Java admits meets `pe_accepts`' premises for
those parameters, on every tree a stream can hold, and the review's
finding 4 is a premise of the proof that every Java database meets, not a
limit that Java lacks. The level scripts' traces use the small G and H of
their TREE lines, enough for their trees, or S and C would refuse there
and pecmp and the tree checker fail. **No reachable case; no 028 entry.**


# 6. The stream's digests, record format 8

For releases/next.md (its rule: a change of the stream's bytes names the
StreamDigest configurations whose digests changed and the entry that keeps
the digests). 026-25 did not keep them. `StreamDigest quick` with
`-Dmodes=plain`, before = main's Java before the merge of 026-25
(ef02ec41, the first parent of the merge 9bcbeea8), after = 9bcbeea8,
each built from `git archive`, the before build's StreamDigest class run
against both jars (its header's way): DIGESTS DIFFER, 11 of 11; every
configuration changed, l2-* and l3-*. l2-default-100MB not run (`quick`).
Length, firstAvailablePos and sha256 (the stream from the decided cut):

    l2-sd100            before 4804464 0 371584d1f52b8ba1712801bdae93d951f8c384466ec6d2d36f376fd1a9d2ab72
                        after  4803920 0 31db0e90e72cda10295d020732f465ff384cb80ca0a0906946b076d54f21737b
    l2-sd1000-node8     before 4318808 0 dd950a4a6e6c5d36e129387ae39ce3f21ff89bbe6251cb7b9dd19399651c583a
                        after  3997704 0 042943097070a9d978391516813ff567a0c690caad003586f818b97672daafb4
    l2-sd10000-node14   before 2302600 0 6c3e3af869ae82befcfbe59ca9c6d6f4770b242c76e3749b39a1ce913973d731
                        after  2279000 0 946a3db3b79cb36d8804308d25f9a6f5146fd1a049985e3842ff324ab8a6df77
    l2-sd100000-node62  before 2561000 0 6b0582293051e299fce6a9b04d738d27ed9bfd4de8ab9668a36331a52fd5162c
                        after  2482072 0 4b5cf70c32841cd266ce4602ec10eb02472fa992ec9dc2af5ef65fd62eab9c04
    l2-every1           before 492280 0 3c5d100423a305491ba58c1d9f37245294f9e1bca127f33bb7c760fdcbf08158
                        after  492760 0 712fa10b00d0ef3a9a7e3bcdc75d1b4c5d723b4dfdd750e0163d1a71f8594aab
    l2-idle-1           before 227848 0 248a27e306659d2345935e34d2a5dae6cee062226a20531b15ee2805eb0b5f83
                        after  223544 0 0a052a5f02c777dfcb78f10c82fc06eebe6b6038c761dfe671328bf146e0e299
    l2-idle-2           before 221392 0 2c574a127542cba2950f1c0fc06500c963aadc8f4d2c6ce5d33cee4c44c6caa0
                        after  221632 0 8158d0da8e06fed0df83356d166b08e3545d19533c65d574832562299b5ad90e
    l3-every1           before 1845800 1635840 216063b1e181ea9e433759f0d31a28d8d1bf249b7d7bf55b93d9454b26ae2413
                        after  1808736 1632608 731ebc7dc44d441caa592590df9dbc4aa9cce947bad777f03e981c8fa7b9fa71
    l3-node8            before 6897424 5884376 ebb88fd6e5a3764f7a3b481fdae2bdf9ce2faf1d207a035375c30c95088228ed
                        after  6323200 5461496 33965d4236baf2447db251853492608cbce645435432e5885af040cd8450c124
    l3-node14           before 1572032 1395144 dbf09b519d3fbfb84cdf145a540c95ed5ea6c35a3f61db867634f0fad43a93ea
                        after  1528208 1390752 ec6969c11e7585d7bdc7cec91b1ca73033ccca99273ceba035cae3818dcdcdbe
    l3-node62           before 8269952 7323472 f75bf3396953f04bb139dba5c7db3eb6d8fdd6f6b31ea124ccd5fffe4c4c8c3d
                        after  8347896 7227056 b12ca730ea64fa7ba5606bbc954689bcf8cb1ca24f40b64b76decaa741acca46

The l3-* "after" digests are 028-26's "before" digests (its section on
StreamDigest): 028-26 changed them again, and keeps its own.


# 7. Gates

At the branch's head:

- `java/before-commit.sh`: BEFORE COMMIT OK (73 s; no Java source changed,
  `level2.sh` only).
- `lean/contract/gate.sh`: GATE OK (85 files of the main theorems'
  closure, 106 pinned; 191 theorems, the standard axioms only).
- `java/stress/level2.sh` (full, 18 minutes at a load near 14): LEVEL 2
  OK; step 0 PINS OK (106 files); step 8c PECMP OK on the full sets: small
  70 traces, 7,240 transactions, 1,402 new top nodes; drain 110, 14,120,
  3,043; reclaim 15, 8,731, 453; 0 differ.
- `lean/contract/pins.sh` after the gates: PINS OK.


# Log

2026-11-19. Created; (B) chosen and done: pecmp in lean/pecmp/, with the
writes, the ids' order and the top compared, step 8c of level2.sh; S and
pecmp pinned; pins.sh, step 0 of level2.sh; the depth guard investigated
(unreachable); lean/README.md, releases/next.md, 027-08, 027-17, 030's
readme. Branch `030-28-writer-copy-checked`.
