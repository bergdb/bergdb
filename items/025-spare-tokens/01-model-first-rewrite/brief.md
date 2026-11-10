025-01. The brief
=================

Written 2026-11-10. For the AI session that Frans starts with a "go" on
025-01, and for its subagents. It covers all of [025-01](readme.md),
section 5, steps 1 to 6: the properties, the specification in Lean, the
candidate algorithms compared by counts, the proofs of the one chosen,
the Java written from the proved model, and the comparison with the
release jar.

**No step waits for Frans** (Frans, 2026-11-10, 19:29: "This task should
run unattended as far as possible. Do not wait for me. One short
initialization, then unattended for 24h or so. That should be the
plan."). Where a plan would stop for a decision, this brief has a rule,
the session applies it, writes down what it chose and why, and goes on.
Frans may overturn a choice afterwards. The work ends with a branch and
a report; whether the new Core replaces today's is the only thing left
to him, and it is not part of the work.

The work is longer than one go. Each go runs until its end time, and the
next one continues from `state.md`, which the first go makes.

Read 025-01 first, sections 3 to 5: the aims, what "proved" means, what
the aims change, the steps. This brief says how the steps are done.


## 1. The go

Not before release 2026.4 is tagged: the work compares with that release
and describes its state.

Frans starts a new session in the repo and says something like: "Go
025-01 until Thursday 22:00." What the go gives:

* **END**, the time the go stops. Usually the time of a usage reset, as
  the work is for tokens that would otherwise be lost (Frans, 2026-11-10,
  18:28: "24h. Something like this. Depends on how long I have left
  until a token reset.").
* **What Frans may add**, with the defaults that hold if he does not:

  | What | Default |
  |---|---|
  | Subagents at a time | 4 |
  | Effort | the lead xhigh; subagents by section 3 |
  | Usage | all that is left until END |
  | Commits | this entry's files, items only, by section 3 |

**Every go starts the same way:**

1. The reading of section 2, and `state.md` if it exists: where the work
   stands and what is open.
2. A short start: two or three lines to Frans on where the work stands
   and what this go will do. A question only if something blocks that
   no rule or default of this brief covers; then one round, in text,
   each question with the default that is taken if he does not answer.
   What Frans says at the go, such as an answer to "For Frans to decide"
   in `report.md` or a choice overturned, is quoted in `state.md`.
3. The work, from where `state.md` says, without Frans.
4. In the last half hour before END: `state.md` and `report.md` brought
   up to date, the build left clean, the commit, the entry in `news.md`.


## 2. Reading, before any work

* [025-01](readme.md), all of it, and `state.md` and `report.md`.
* `items/readme.md`, and `AGENTS.md`.
* `docs/levels.md`, and what it cites for the requirements and the
  invariants: 011-01 (R1 to R7, INV-LOOKUP to INV-EVICT).
* The principles, 010-01, P1 to P12.
* The unattended way of working: 013-01, sections 4 and 6; 013-02,
  sections 6 and 9.
* `releases/2026.4/readme.md`, and `news.md`, `git log`, `git status`.
* Which other sessions work, and on what (`~/.claude/sessions/*.json`).

The rest is read by the subagent whose work needs it: `java/`, `lean/`
and its `README.md`, 007, 014, 023, 006-02, 011-02 (prior art), and
Frans's notes of 2008 to 2016 in the f1 repo
(`a/007-bergdb-261012/bergdb/doc/`).


## 3. Ground rules

013-01, section 4, holds. In short, and what differs here:

* **What may be written.** On `main`: only this entry's directory,
  `items/025-spare-tokens/01-model-first-rewrite/`, and the lines about
  it in 025's readme. Nothing in `java/`, `lean/` or `docs/` there: this
  is an experiment, and its code is the item's (items/readme.md, "Items
  and the current state"). The new Core's Java (W7) is too large for the
  entry and is written on a branch, `025-01-core`, in a worktree of its
  own, as 009 did for handles. The branch is not merged into `main`
  under this brief.
* **Where the work runs.** Scratch work, builds and raw output in
  `/Users/f/fl/bench/025-01/`. The entry takes the sources, the summary
  tables and the findings. Raw output does not go into the repo.
* **The Lean code** is a project of its own in the entry's `lean/`, with
  the toolchain of the repo's `lean/lean-toolchain` and without Mathlib,
  as the repo's. Its `.lake/` is ignored by a `.gitignore` beside it. It
  may copy from the repo's `lean/` and says where it did.
* **The machine.** Other sessions time on F53. Before a `lake build`, a
  Java run or anything that loads the cores for more than a minute: look
  for a running quiet block and with `ps` for timed runs, and wait if
  there is one. If a coordinator runs (013-02), heavy runs are asked of
  it first. Until W8 no timed measurement is made: every figure is a
  count (bytes, reads, nodes), which does not depend on the load.
* **Commits.** If a coordinator runs, finished files are reported to it
  and it commits them. If none runs, the lead commits this entry's files
  itself, in Frans's name, with no AI attribution, staged right before
  the commit, with "(items only)" in the message. What is committed
  builds: a proof in progress may hold a `sorry`, a broken file may not
  be committed.
* **Subagents.** Effort set on every call: high; xhigh for the
  specification (W2), for the design of a candidate (W4), for proofs
  (W2, W4, W6) and for the Java's concurrency (W7), unless the usage is
  tight. Each brief names this entry,
  its scratch directory, the files it may write, its stop time and the
  length of its report. Two subagents never write the same Lean file. A
  subagent that waits for a process waits on a marker file or runs in
  background mode, never on `pgrep -f` of its own command.
* **Independent reviews.** The properties, the specification, each
  candidate's design and the statements of the theorems are each
  reviewed by a fresh subagent that gets the document and its sources,
  not the author's reasoning, and is asked for what is wrong or missing.
  The author answers each finding in the document: fixed, or kept with
  the reason.
* **Decisions.** Where this brief has a rule, the rule decides. Where it
  has none, the session decides by the aims of 025-01, section 3, in
  their order, and writes the decision into `report.md`, under "For
  Frans to decide", with what it chose, the other options and the
  reason. The work goes on with the choice. Nothing is left undone
  because Frans has not answered.
* **Times** in logs come from `date`.


## 4. The work

Eight pieces, W1 to W8, in this order; W6, the proofs, is the largest.
A piece is left when its "Done when" holds, not by the clock: a go that
ends in the middle of a piece is continued by the next. When a piece is
done the next one starts at once, in the same go.

| ID | What | Output |
|---|---|---|
| W1 | The properties | `properties.md` |
| W2 | The specification in Lean, with its theorems | `lean/`, `specification.md` |
| W3 | Today's counts | `counts-today.md` |
| W4 | The candidates: designs, models, counts, theorems stated | `candidate-*.md`, `lean/` |
| W5 | The choice | `choice.md` |
| W6 | The proofs | `lean/`, `theorems.md` |
| W7 | The Java, from the proved model | the branch `025-01-core`, `java-notes.md` |
| W8 | The comparison with the release jar | `comparison.md` |

W1 comes first. W2 and W3 run side by side after W1's contract (W1, part
1). W4 starts when W2's interface builds and W3's table exists. As a
guide for a first go of 24 hours: W1 to W3 in its first third, W4 in the
rest, and W5 to W8 in the goes after it.


### W1. The properties

One document of what the new Core must do, stated as what must hold and
not as how today's code does it. At most 400 lines: Frans reads it.

1. **The Core's contract.** The Core API is less well defined than the
   Pub API (Frans, 2026-11-10). So the contract is found, not assumed:
   every method of the Core Layer that today's Pub layer (`pubimp` and
   `bergdb.pub`) calls, each with its meaning in a few lines, its
   arguments' limits and its errors. Found by a search of the code whose
   command is kept in the entry, so that it can be run again. What only
   tests and tools call is listed apart, as outside the contract. The new
   Core must carry today's Pub layer unchanged; that is the meaning of
   "the same API" for a Core-only rewrite.
2. **The properties**, each with an ID (PR-1 and on), one statement, its
   source by item and section, the script that checks it today, and how a
   new Core would be checked for it. At least: lookups, scans and history
   (INV-LOOKUP); restart and a crash at any byte (INV-RESTART, INV-CRASH,
   and 014-01's fault model for the storage); bounded startup (007, T3);
   reclaim and cleanup as 2026.4 has them (INV-RECLAIM, 023); data larger
   than memory (INV-EVICT); memory per KV (006-02); pauses and bounded
   steps (010-01); the deterministic stream; the sizes to handle, 1
   million to 100 million keys.
3. **The principles** of 010-01, each marked: binds the new Core as it
   is, or is a matter of today's design that a candidate may leave, with
   the reason. A candidate that departs from a binding principle names
   the departure for Frans; it is not dropped for it.
4. **The workloads and the counts.** The workloads that every candidate
   runs, the worst cases of large databases first: sequential and random
   puts, overwrites, a mass delete and the reclaim after it, lookups in a
   cold database, scans over deleted ranges, a start after each. The
   counts taken: stream bytes per put against the bytes of its key and
   value; nodes and bytes read per cold lookup; bytes read at a start;
   stream bytes kept after the delete and the reclaim; a measure of the
   memory per KV. Sizes: 1 million keys for all, 10 million where a model
   runs it within an hour.
5. **The performance aims as numbers**: for each count, today's figure
   (from W3, filled in when it exists), the figure that would count as
   better, and how much worse than today's a count may become for a gain
   elsewhere. Proposed by the session and marked as proposed. W5's rule
   uses them.
6. **What is free**: the stream format, the algorithm, the tree, the
   Core's inner structure. Old databases need not open.

Done when: the independent review is answered; and for part 1, today's
Pub layer compiles against a stub that has only the contract's methods.


### W2. The specification in Lean

The first layer of 025-01, section 4: what a user of the Core sees, with
no stream format and no tree.

* **Definitions.** Keys and values as bytes. The state as an abstract
  map with its history. The contract's methods (W1, part 1) as functions
  on it. The storage as a sequence of bytes that only grows and that a
  crash cuts back to some point at or after the last sync (014-01).
  And what it means that an algorithm implements the specification: its
  functions on the stream, and a function from a stream to the abstract
  state, such that every operation and every start after every allowed
  cut agree with the abstract map.
* **The assumptions** about the world, such as what the storage keeps at
  a crash, in one file, each with a name and a sentence, as
  `lean/SIS/Assumptions.lean` is today. Nothing else in the project
  assumes anything.
* **Short.** At most about 300 lines of definitions. It is the "model in
  the brain of the user"; if it needs more, the report says what made it
  long.
* **It runs.** The abstract map is also a program, the oracle of W4's
  tests.
* **Its own theorems**, proved: what a user relies on without thinking,
  stated about the abstract map. A lookup after a put gives the value; a
  delete removes; a lookup at an earlier time is not changed by a later
  put; a scan gives the keys of the lookups, in order; a start after a
  cut gives the state of a prefix of the transactions, with every synced
  one in it. They show that the definitions say what is meant, and they
  are short.
* **`specification.md`**: each definition, assumption and theorem in
  words, in the order of the Lean files, for Frans to read beside them;
  and where it differs from the top of today's model (`lean/SIS`), with
  the reason.

Done when: a clean `lake build` with no `sorry`, and `#print axioms` on
each theorem shows only Lean's standard axioms; the independent review
is answered, by a subagent that gets the Pub API's Javadoc, W1 and the
specification and looks for what a user could observe that the
specification gets wrong; and a run against the release jar agrees:
random small workloads through the jar's Core and through the oracle,
the answers compared, with the seeds logged. A difference is a fault of
the specification or a bug of the release, and the report says which.

Then one entry in `news.md`, `needs a look`: the specification is the
one thing worth Frans's reading before the proofs are far gone (section
6). The work goes on without waiting for it.


### W3. Today's counts

Where today's code spends: the counts of W1, part 4, for release 2026.4,
on the same workloads.

* From the Java at the release's tag, in a scratch clone, with the
  counters and tools that exist (`java/props.sh`, the suites of
  `java/stress/performance.sh`) and probes of its own where none does. A
  probe lives in this entry and changes nothing in `java/`.
* Each count beside a simple lower bound, such as the bytes of the key
  and the value for a put, so that the table shows where the distance is
  large. `counts-today.md` ends with the three largest distances: they
  are what a candidate is for.

Done when: each count is taken twice, by two ways where two exist (the
stream's length on disk and the code's own counter), and they agree; the
workloads' seeds are logged so that a run can be repeated.


### W4. The candidates

Two or three algorithms, each as a Lean model that runs, measured by the
same counts, with its theorems stated.

1. **Candidate A is today's algorithm**, as 2026.4 has it. Its model is
   today's Lean model if that runs the workloads at the sizes, or a
   smaller model made for counting. It is the calibration: A's counts
   from the model must agree with W3's counts from the Java, within 5 %
   at 100,000 keys and at 1 million. Until they do, the way of counting
   is not trusted and no other candidate's figures are reported.
2. **Candidates B and C** each start as a design of one or two pages,
   `candidate-b.md`: the idea; which of W3's three distances it attacks;
   the counts it expects, worked out by hand; what it costs elsewhere;
   which property of W1 is at risk and why it holds; what it asks of the
   Java beyond the model (caches, threads), and the test that would show
   each such mechanism invisible (025-01, section 4); and its
   invariants, in words. The ideas come from W3, from 011-02 and the
   literature, and from Frans's notes of 2008 to 2016. The design is
   reviewed independently before it is modelled. A design that fails a
   property on paper is not modelled; it stays in the entry as a dead
   end, with the reason.
3. **Each model** implements the specification's interface and has one
   subagent, in its own directory of the entry's `lean/`. It is tested
   against the oracle of W2: at least 1,000 random workloads with cuts
   and restarts at random points, the answers compared, the seeds
   logged. A model that fails a test is not measured until it passes.
4. **The counts**, for every candidate on every workload, in one table
   with today's figures from W3 and the aims of W1.
5. **The theorems, stated.** For each candidate, in Lean, about the
   model's own definitions: its invariant; that the invariant holds at
   the start and is kept by every operation; and the main theorem, that
   the model implements the specification (W2). Statements only, their
   proofs `sorry`. A candidate whose invariant cannot be written down is
   not understood well enough to choose.
6. **A proof probe.** For each candidate, one subagent with a fixed
   budget, the same for all (as a guide, two hours), on the lemma its
   design names as the hardest: that a put keeps the invariant. The
   result goes into the candidate's document: proved, or how far it got
   and what stood in the way. It is evidence for the choice, of how the
   proofs of this design go; for today's algorithm, `lean/SIS/Proof`
   shows it already.

Done when: A is calibrated; at least two candidates, A among them, are
tested, measured, stated and probed; and every other design is either
that far or a dead end with its reason.


### W5. The choice

The session chooses the candidate to prove, by this rule, and writes
`choice.md`: the table, the rule applied line by line, the candidate.

1. Out: a candidate that fails a test against the oracle, or leaves a
   property of W1 at risk without an answer, or whose invariant is not
   stated.
2. Out: a candidate other than A that is worse than A on a count by
   more than W1's aims allow.
3. Out: a candidate other than A that does not reach W1's aim on any of
   W3's three largest distances. It is not better enough to be worth
   new proofs.
4. Of those left: the one that reaches the most of W1's aims. Between
   equals, the one whose proof probe got further; then the one with the
   fewer invariants.
5. If only A is left, A is chosen: today's algorithm, proved against the
   new specification, with what `lean/SIS` already proves carried over.
   That too gives a proved model that is the source of its code.

A departure from the rule is allowed with its reason written in
`choice.md` and under "For Frans to decide". W6 starts at once. Frans
may overturn the choice at any go's start; the proofs made until then
for the other candidate stay in the entry.

Then one entry in `news.md`, `needs a look`, with the choice in a line.


### W6. The proofs

The chosen candidate, proved, by 025-01, section 3's meaning.

1. **The list of theorems first**, `theorems.md` and their statements in
   Lean. Each theorem names the property of W1 it covers. At least: the
   model implements the specification, for every operation and for a
   start after every allowed cut; reclaim and cleanup keep that; the
   bound on startup; and each count of W1 that can be stated as a bound,
   such as the stream bytes of a put. Each property of W1 gets a line in
   a table: its theorem, or "by test", with the reason why no theorem
   states it and the test that checks it. That table is the measure of
   the proofs' coverage.
2. **The statements are reviewed** independently before the proving
   begins: does each theorem say what its property says, for the model's
   own definitions, with no hypothesis that makes it empty? A proved
   theorem with a wrong statement is worth nothing.
3. **The statements are then fixed.** A change to a statement, to the
   specification or to the assumptions, after the review, is an event:
   it is listed in `state.md` with the old text, the new text and the
   reason, and under "For Frans to decide". A statement is never made
   weaker to let a proof through without that entry. Frans reads the
   list, not the proofs.
4. **The plan of lemmas**, in `theorems.md`: what each main theorem
   needs, in the order to prove it, and which file each lemma is in.
   Subagents prove side by side, one file each.
5. **When a proof cannot be found because the model is wrong**: the
   counterexample is written down as a finding, with the workload that
   shows it, and added to the tests. The model is corrected, its tests
   and counts are run again, and if a count moved past W1's aims, W5's
   rule is applied again. These findings are among the most useful
   results and go into the report.
6. **The state of the proofs is generated, not kept by hand.** A script
   in the entry builds the project and lists, for each main theorem,
   whether `#print axioms` still shows `sorryAx`, and every `sorry` left
   with its file and lemma. Its output is `proof-status.md`, made again
   at the end of every go.

Done when: every theorem of the list is proved; the build has no
`sorry`; `#print axioms` on each main theorem shows Lean's three
standard axioms only; the assumptions are in their one file; and the
models' tests and counts still pass on the proved definitions. Then W7
starts, and not before: no Java is written for an algorithm whose proofs
are not done (025-01, section 3).


### W7. The Java

The new Core in Java, written from the proved model, under today's Pub
layer.

1. **Where.** The branch `025-01-core`, from the tag of release 2026.4,
   in a worktree under `/Users/f/fl/bench/025-01/`. The lead commits to
   the branch, in Frans's name. `state.md` records the branch and its
   head.
2. **What changes.** The Core Layer, behind the contract of W1. The Pub
   layer (`pubimp`, `bergdb.pub`) is not changed. If it must be, the
   contract missed something: that is a finding, W1 is corrected, and
   the report says what it was.
3. **It follows the model.** Each part of the model has its class, with
   the model's names, and each method that carries out a function of the
   model cites it in a comment. What the Java has and the model has not
   (caches, buffers, threads) is listed in `java-notes.md`, each
   mechanism with the test that shows it invisible: the same work with
   and without it, or under many schedules, and the same stream and
   answers (025-01, section 4).
4. **Concurrency** is kept simple by the design: one appender, readers
   on snapshots that never change. It is outside the proofs, so it gets
   the tests of point 3 under many schedules, and an independent review
   of the code.

Done when, on the branch:

* **the model accepts the Java's stream**: the model, run as a program,
  reads the stream that the Java wrote, byte for byte, and gives the
  same answers, on traces made as `java/stress/conformance.sh` makes
  them today, on its small and medium sets;
* **the tests through the Pub API pass**: `java/f.sh`, and the unit
  tests of the Pub layer;
* **the crash, restart and invariance tests pass**: those of today's
  level scripts, run through the contract. A test that reaches into
  today's Core is adapted, or listed in `java-notes.md` with the reason
  it does not apply and the test that replaces it;
* **`java/before-commit.sh` prints `BEFORE COMMIT OK`**, with the unit
  tests of today's Core replaced by the new Core's.


### W8. The comparison

The new Core against release 2026.4's jar: function, counts and time.

1. **Function.** The same tests through the Pub API on both, and random
   workloads through both with the answers compared, the seeds logged.
2. **Counts.** The counts of W1 from the new Java, beside the model's
   (W4) and today's (W3). The Java's must agree with its model's within
   5 %; a larger difference means the Java does not follow the model's
   costs, and is found and fixed before any time is measured.
3. **Time.** `java/stress/performance.sh`, its suites, for both jars,
   from 1 million to 100 million keys, the worst cases first, by the
   rules of today's measurements (its header, and 011-09). These are the
   only timed runs of the work. They need a quiet machine: the script's
   own check decides; a coordinator, if one runs, is asked first;
   otherwise they run at night. The session starts nothing else while
   one runs.
4. **Memory and pauses.** Heap bytes per KV, and the longest pause of
   the Core's own code, as today's measurements take them.
5. **When an aim of W1 is missed.** A change of the Java alone, outside
   the model, is free: it gets its test of invisibility (W7, point 3)
   and the checks of W7 again. A change of the algorithm goes to the
   model first: the model, its tests, its counts and its proofs (W6),
   then the Java. This is repeated while goes are given and an aim is
   missed.

Done when: `comparison.md` has the three tables, with every aim of W1
marked reached or missed, and the report gives the session's
recommendation on the branch: merge, improve, or keep as an experiment,
with the reasons. Then one entry in `news.md`, `needs a look`. The merge
is Frans's.


## 5. State, stopping, and a usage limit

* **`state.md`**, in the entry, carries the work from go to go: the goes
  so far, with their times; each piece's status in a line; the chosen
  candidate; Frans's answers, quoted; the changes of statements (W6,
  point 3); what the next go starts with. A new session with this brief
  and `state.md` must be able to go on without the last session.
* **`report.md`**, for Frans, at most 200 lines, written again at the
  end of every go: what this go did; where the work stands, against W1
  to W8; the table of counts and the choice, when they exist; the
  findings; what Frans may want to read now, with its length; "For
  Frans to decide", each decision the session made in his place, with
  the other options and the reason.
* **At END the go stops**, and it does not resume by itself. The tokens
  after a reset are not spare. No check-in is scheduled past END.
* **Before END**, a usage limit or a dead session is survived as in
  013-01, section 6: the agents, their directories and the events in
  `state.md`; a check-in every hour (CronCreate) that finds what stopped
  and resumes it; and after a 5-hour limit, a check-in 3 minutes after
  its reset, if that is before END.
* **Another session's urgent work goes first**: for the machine, and for
  the usage if Frans or the coordinator says so.
* **At any stop**, each piece's output says in its first line whether it
  is complete. The order of the work is chosen so that a stop after W1,
  after W2, after W3, after W4 or after W6 leaves something of use by
  itself.


## 6. Frans's part

The go, with its end time, each time. Nothing else is needed, and the
work waits for nothing.

What he may read, when he wants, in the order of what a fault in it
would cost:

* **The specification**, when W2 is done: `specification.md` beside
  about 300 lines of Lean, and the file of assumptions. A fault found
  here late costs proofs, so this is the reading worth doing early.
* The list of changed statements (`state.md`), if there is one.
* The choice (`choice.md`), which he may overturn.
* The properties (at most 400 lines) and the report (at most 200).

At the end: whether the branch is merged.
