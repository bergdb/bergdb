# 030-15. Strict trace parsing, one verdict, and a gate that pins the statements

Created 2026-11-17 by Frans Lundberg. Status: done.

The fixes of an independent review of the contract package (another model,
the night of 17 November; its sections 4 and 5): malformed trace lines
passed both checkers, each checker checked only half of a trace, the
contract checker's exit status was tied to its verdict by reading only, and
the gate did not pin the statements (also 030-06, finding 8). On the
branch `030-15-strict` from `main` 0b677a63 (gate base a25b8b03).


# 1. The result

All three items of the brief are done.

1. **Strict parsing.** Every line of a trace must now parse whole by the
   grammar of trace format 3 (027-02, sections 1, 2 and 4), or the trace
   fails in both checkers: exactly the tokens of its kind, each of its
   form; numbers of decimal digits only (Lean's `toNat?` also takes
   `1_000`); one space between tokens; the lines of a transaction in the
   order of 027-02, section 2; `TX i`, i > 0, starting with `BASE`; `TX 0`
   with no `BASE`, `OP`, `GET`, `SCAN`, `TOUCH`, `FA`, `CUT` or `PHYSCUT`
   line. `lineFault` and `placeLine` in Contract/Complete.lean; `readLine`
   (Contract/Trace.lean) also refuses a line of a kind it reads that it
   cannot read whole, where it used to pass it over. The review's four
   parse faults (a bare `OP` line, a bare `GET` line, the scan direction
   `BANANA`, a put in `TX 0`) passed both checkers before and fail both now,
   in a hand-made trace (`lean/contract/test/small.trace`, the review's
   trace made valid) and in Java's traces; they are in `faults.sh` and
   `bridge-faults.sh` with five more (a number with `_`, two spaces, lines
   out of order, a transaction without `BASE`, a wrong GET or a wrong key
   entry). The 195 traces of the small, drain and reclaim sets pass, and
   four traces made with every kind of line of format 2 and 3 (`probe`,
   `rune=random` and `every` with `ereads` and `erestart`, `retain`, `live`:
   PROBE, FIRST, SLOT, the handles' lines, FA, CUT, PHYSCUT, TOUCH; 686
   transactions) pass the contract checker.
2. **One verdict.** `contractcheck` passes a trace only if
   `contractVerdict` of its lines is true (Contract/Verdict.lean): whole,
   readable, `startTopOk` and `historyTopOk` on the history its lines give
   (`traceTopOk`), and Java's reads, LIVE and SKIPT lines the package's.
   Proved: `contractVerdict_sound`, a trace with that verdict is a history
   that meets the contract with TREE and the top (`MeetsTop`), with the
   operations of its OP lines; so `jget_right` and `jscan_right` hold for
   the traced tree at every time of it. The checker's loop still counts the
   failures by clause, and says so if loop and verdict disagree (never on
   the 195 traces). `check.sh` now runs both checkers on every set, and a
   set passes only if both pass every trace (the bridge checker's verdict
   was already `fullHistoryOk`, with `fullHistoryOk_meets`).
3. **The gate pins the statements.** `gate.sh`, step 5: the files of the
   trusted closure of the main theorems (section 3), with their SHA-256 in
   `lean/contract/statements.pin`, must match; a file of the closure not
   in the pin file fails; with BASE, a commit since BASE that changed a
   pinned file without changing the pin file fails, and the pinned files
   changed since BASE are listed for review. `pin.sh` writes the pin file.

What this does not do: the theorems still speak of the lines read, not of
Java; that the lines are Java's change (the exporter) and Java's reads are
the assumptions of 030-04, section 3.5. The checker's `main` (reading the
files, the exit status) is still read, not proved: it is ten lines, and it
fails a trace if `contractVerdict` is false.


# 2. Decisions

- **The grammar is 027-02's, in full, with the order.** The brief asked for
  every line to parse by the format 3 grammar; I also check the order of
  the lines in a transaction (027-02, section 2, "Within TX i, the order
  is"), since the readers' meaning depends on it: a `SKIPT` line belongs to
  the `VER` line before it (`readLine` gives it that node), an `H` or `F`
  line to its version. All 195 traces of the level 2 sets and the reclaim
  set keep the order. The kinds of format 2 that the contract does not read
  (`REC`, `H`, `F`, `FIRST`, `SLOT`, the handles' lines) are checked by
  their grammar too: a trace with a malformed line of any kind fails.
- **`TX 0`: the start's lines.** `TX 0` of every trace has only `NEW`,
  `ADD`, `KN`, `REC`, the versions, `GD`, `DIRTY` and `LIVE` lines; the
  lines of an operation, a read, a touch or reclaim fail there.
- **`BASE` required** in every `TX i`, i > 0: 027-02 says it is first in
  each such transaction, and every trace has it. `BASE`, `TOUCH` and `REC`
  at most once a transaction.
- **The `TREE` line with 4, 6, 7 or 8 numbers**, as 027-02 says (the
  review's hand-made traces had 5: they now fail for that alone, so the
  faults are made in `test/small.trace`, the review's trace with a `TREE`
  line of 4 numbers, a `BASE` line, and its `GET` and `SCAN` lines in
  their place).
- **Free text** only in `CONFIG` and `PROBE` lines and comments; there two
  spaces are allowed.
- **One verdict as a function, not a proof about the loop.** The brief
  allowed either; a function with a theorem is shorter (130 lines, the
  proof 20) and is what the bridge checker does. The loop stays for its
  messages.
- **One script: `check.sh`**, not a new one: it ran the contract checker
  alone and nothing else calls it; now it runs both checkers on each set,
  side by side, and the three fault tests. `bridge-check.sh` stays for the
  bridge checker alone and its `--model` words. The final word stays
  `CONTRACT OK`, now meaning both.
- **The pins: the closure computed, not a hand list.** A hand list goes
  stale when a statement starts to use a new file; `Statements.lean`
  computes the closure at each gate, and the gate fails if it has a file
  not pinned. Proof files are pinned when a statement uses a definition in
  them (eight `Proof/` files do); a proof edit there then needs a pin
  update, which is cheap (`pin.sh`) and visible.
- **The gate's base.** The common rules give a25b8b03; this branch starts
  from 0b677a63, which adds the coordinator's 006-30 commits
  (items/006-2026-q4/30-day-17-november.md only). Step 4 against a25b8b03
  fails on that file alone; I gate against 0b677a63, which is a25b8b03 with
  only that file changed.


# 3. What is pinned, and why

The pin file holds 65 files (`pin.sh` lists them in its header):

- **The trusted closure of the main theorems, 54 files.** The main theorems
  are those of Axioms.lean but the examples (61 of 76). `Statements.lean`
  walks from their statements through every definition they use, down to
  Lean, Std and Mathlib: the contract's definitions (Tree, Read, Statement,
  Shape, ShapeStatement, Top, Reach, Check, CheckShape, History,
  HistoryTop, Trace, TraceTop, Complete, Verdict, Rebuild, Writer), the
  bridge's (Bridge, BridgeTop, BridgeModel, BridgeHeap, BridgeFull,
  BridgePolicy, BridgeBound, BridgeTheorems and eight `Proof/` files whose
  definitions statements use), the theorem files (Theorems,
  TheoremsShape, TheoremsTop), and 18 files of the old package (lean/SIS,
  lean/Check) whose model the bridge's statements are in: a change of any
  of them can change what a theorem says.
- **The list and the tool:** Axioms.lean (which theorems are main),
  Statements.lean (how the closure is found).
- **The checkers' main files**, ContractCheck.lean and BridgeCheck.lean:
  they turn a verdict into an exit status, the one step from "the checker
  passed" to the theorem that is read, not proved.
- **The gate itself**, gate.sh: a gate that can change unseen pins nothing.
- **Lean and the libraries:** lean-toolchain, lakefile.toml and
  lake-manifest.json of both packages (Mathlib's version is in the
  manifest).

Not pinned: the examples (they show a statement is not vacuous; nobody
trusts their definitions), the proofs that no statement uses (Lean checks
them), the shell scripts but gate.sh (tests).


# 4. State note

Done; the last gated commit is in the Log. For whoever goes on:

- **The gate's step 5 and other branches.** When this lands, every later
  commit that changes a pinned file must change `statements.pin` in the
  same commit (`lean/contract/pin.sh`, then commit both). A pin fixed in a
  later commit does not help: the gate names the earlier commit; squash
  the pin into it (`git commit --amend`, or a rebase). Commits whose
  parent has no pin file are not checked, so branches started before this
  one lands pass step 5's commit check, but their tree fails the hash check
  until `pin.sh` is run: the coordinator runs `pin.sh` in the merge and
  reviews the pinned files that the gate lists as changed since BASE. A
  new theorem in Axioms.lean can add files to the closure: the gate then
  says "not in statements.pin".
- **Tools:** `lake env lean Statements.lean` (the closure's files, about 7
  s); `pin.sh`; `check.sh SET...` (both checkers); `faults.sh` and
  `bridge-faults.sh` (the strict faults, with `test/small.trace`).
- **What is left (not in this brief):** the checkers' `main` functions
  (reading the files, the exit status) are read, not proved; a combined
  executable whose verdict is `contractVerdict && fullHistoryOk` would make
  "both pass" one theorem (the bridge checker needs the old package's
  parser for its changes, so it is more than a few lines). The review's
  other findings (the leaf flag in `Rep`, restart over supplied changes,
  values as hashes) are not this item's.


Log
===

- 18:30 Started (an agent of coord-1117). Traces of the level 2
  sets made in the clone (`treeconf.sh small`, `drain`, `reclaim`:
  TREECONF OK, 195 traces).
- 18:42 Work item 1, strict parsing: `lineFault` and `placeLine`
  (Complete.lean), `readLine` strict (Trace.lean); the review's faults in
  `faults.sh` and `bridge-faults.sh`, with `test/small.trace`. FAULTS OK,
  BRIDGE FAULTS OK; `check.sh small drain reclaim` CONTRACT OK (195 traces).
  The gate against a25b8b03 fails only on the coordinator's 006-30 commits
  (items/006-2026-q4/30-day-17-november.md, in main 0b677a63 that this branch
  starts from); against 0b677a63: GATE OK.
- 18:52 Work items 2 and 3: `contractVerdict` and `contractVerdict_sound`
  (Contract/Verdict.lean), the checker passes a trace only on it;
  `check.sh` runs both checkers (small, drain, reclaim: CONTRACT OK, both,
  195 traces, 3 minutes); `Statements.lean`, `pin.sh`, `statements.pin` (65
  files), `gate.sh` step 5. GATE OK against 0b677a63 (76 theorems).
- 18:56 Four traces with every kind of line of formats 2 and 3 (probe,
  run E, retain, live) pass the strict contract checker. Done.
- 18:57 GATED 900c66a9: strict trace parsing (the review's faults fail both
  checkers), `contractVerdict_sound`, `check.sh` runs both checkers,
  `gate.sh` step 5 pins the statements (65 files). Gate against 0b677a63
  (a25b8b03 plus the coordinator's 006-30 file): GATE OK, 76 theorems.
