025-01. A model-first rewrite of BergDB
=======================================

Created 2026-11-10 by Frans Lundberg. Status: ready.

Ready for a go, not before release 2026.4: [brief.md](brief.md) is the
brief for the session that Frans starts, and for each later one, as the
work takes several goes. It covers all six steps of section 5, and no
step waits for Frans. Nothing is started. Decided so far: the aims and
their order, with a proved model first (section 3); what the work starts
from (section 7, question 1: informed, with a free algorithm); the Core
only; goes of about 24 hours, each until a usage reset, each a short
start and then unattended (section 7, questions 2 and 5).

What this entry holds: a new implementation of BergDB behind today's Pub
API, on append-only storage, with a release jar as the black box to
compare with; the assessment of 2026-11-10 of whether an AI agent can
write it and what it would give; the aims Frans chose, a model in Lean
first and performance second; what they change; the experiment; and what
must exist before it can start.


## 1. The idea

Frans, 2026-11-10, 14:50, to Claude (Fable 5.2, Claude Code), as a
discussion: "What is your (Fable 5.2) capability? Could you write BergDB
from scratch? Given only the current Pub API and append-only storage. And
a release jar and Javadoc as a blackbox for comparing functionality and
performance. Perhaps you could rewrite the whole thing for better
performance? Or for less complexity? Or for better Lean proof coverage? Or
in Lean itself?"

And at 16:08, after the answer in section 2: "Who knows? Perhaps I will do
it when I have spare tokens to throw at it."


## 2. The assessment of 2026-11-10

Claude's answer, shortened. It rests on what this repo's history shows,
not on a fresh reading of the code, and a model has no way to measure
itself from the inside: it is an estimate, and the experiment (section
5) is the way to replace it with a measurement.

In short: a working BergDB can be written from that starting point. The
code is not the limit. Knowing that it is right, and knowing what it must
be right about, are.

* **Writing it.** An implementation that passes a functional test suite
  through the Pub API: days of agent work. The nearest evidence is the C
  clone (012), Levels 0 to 4 in two days, but it had the source to follow.
* **Knowing what to build.** The hard requirements are not in the
  Javadoc: bounded startup (007), reclaim and cleanup (023), safety at a
  crash, heap bytes per KV (006-02), pauses (010), the worst cases at 100
  million keys. A black box shows them only where someone thinks to probe.
  Each mechanism of today's code answers a problem that was found; a
  rewrite that does not know the problems finds them again, one by one.
* **Knowing that it is correct.** An AI agent does not verify concurrency
  or crash recovery by reading its own code, and it writes confident
  arguments that are sometimes wrong (023-06, section 18.7, is a recent
  case). The applications of new users (020-24) and the C clone found most
  of 2026.4's bugs. Lean proofs, independent reviews and second
  implementations catch such faults.
* **Time.** Stress and performance runs at large sizes take hours whatever
  the model. Today's robustness is weeks away from a first working
  version, not days.

The four aims, in the order of likely gain:

1. **Less complexity.** The most likely gain: a second system knows all
   the requirements at the start. But 023 already simplifies the Core with
   the reasons at hand, and the black-box condition gives those reasons up.
2. **Better Lean coverage.** A real gain, and the one with the largest
   long-term value: a core written from the model outwards, with the Java
   following the Lean structure, can be proved more fully per line than a
   model fitted to existing code.
3. **Better performance.** Unknown. A rewrite gives no speed by itself;
   the gains come from design ideas, and an idea is cheaper to test as a
   prototype in today's code. Expected: the common cases match soon, the
   worst cases of large databases are wrong the first time.
4. **A core in Lean itself.** It can be done as a proved pure core (bytes
   in, state transitions out) with a thin IO shell that is not proved. It
   closes the gap between the model and the code, and reference counting
   has no tracing collector, so no pauses of that kind. As the product it
   fits poorly: BergDB is for Java, the bridge to Java is awkward, and it
   would be slower by a factor that is not known without a measurement.


## 3. The aims chosen

Frans, 2026-11-10, 18:04: "Let's look at the four aims. I want to
prioritize 1. Model-first in Lean. 2. Performance. The idea is that with
a solid model for the algorithms and smart AI to code it, we can tolerate
higher complexity if needed for high performance. Of course, the
complexity of the API and the model in the brain of the user must be kept
low. But the idea is to keep the API the same."

So, in this order:

1. **The model first, in Lean.** The algorithms are written and proved in
   Lean before the Java that follows them.
2. **Performance.** Better than the release jar's.
3. **The same API.** The Pub API and what a user must understand stay as
   they are, and stay small.

Frans, 2026-11-10, 18:46, on the brief for steps 1 to 3, which leaves
the proofs to step 4: "Hmm, I want proofs. That is the big benefit of a
model in Lean. We want a proven model." So the first aim is a proved
model, and a model that only runs and passes tests is a stage on the way,
not a result. What "proved" means here:

* the theorems of step 4 (section 5) are stated in Lean about the
  algorithm's own definitions, the ones that run, and not about a copy;
* the build has no `sorry`, and `#print axioms` on each main theorem
  shows Lean's three standard axioms and nothing else;
* what is assumed about the world, such as what the storage keeps at a
  crash, is in one file of named assumptions, as `lean/SIS/Assumptions.lean`
  is today, and Frans reads it with the specification;
* no Java is written for an algorithm before its proofs are done.

Less complexity of the implementation is no longer an aim: the code may
be more complex than today's where performance needs it. A core that runs
in Lean (aim 4 of section 2) is not asked for.


## 4. What the aims change

**The direction between model and code.** Today the model follows the
code: 001 and 009 wrote the Lean model and aligned it with Java, and
`docs/levels.md`, section 1, says what that gives: the proofs concern the
abstract model, Java's runs are checked against it, and concurrency and
resource bounds are not in it. Model first turns this around. The model
is the design, the Java is written from it, and a difference between them
is a fault in the Java.

**Three layers**, each with its own check:

* **The specification.** What a user sees through the Pub API: a map
  with transactions and history, on storage that only appends and may
  lose its unsynced tail at a crash. It names no stream format and no
  tree. This is the "model in the brain of the user" as Lean definitions,
  and it must stay short, as Frans reads it: a wrong specification is the
  one fault that no proof finds.
* **The algorithm.** The bytes of the stream and the functions on them:
  put, lookup, scan, start, reclaim. Pure functions in Lean, proved to
  refine the specification, with its bounds as theorems (startup, as
  007's T3 today). Checked by Lean itself.
* **The Java.** Written to follow the algorithm's structure, and checked
  against it by runs, as `java/stress/conformance.sh` does today: the
  model runs as a program and must accept the Java's stream, byte for
  byte.

**Where the model pays for complexity, and where it does not.** The idea
that a solid model lets the code be more complex holds for complexity of
the algorithm: what is written to the stream and when. A more intricate
node layout or reclaim order costs longer proofs, which is tokens, and
the proof is what makes it safe. It does not hold for complexity of the
running program: threads, caches, memory. A sequential model says nothing
about a race, and many of 2026.4's bugs were of that kind or at the
API's edges (021). So the design needs a rule for the second kind: a
mechanism that is not in the model must be invisible, and that is checked
by a test that runs the same work with and without it, or under many
schedules, and compares the stream and the answers, as RestartInvariance
and EvictionInvariance do today (`docs/levels.md`, section 2).
For concurrency itself the proposal is to keep it simple in the design,
as an append-only stream allows: one appender, and readers on snapshots
that never change.

**Performance, measured in the model before the Java exists.** A
performance figure has two parts. The first is the algorithm's: the
bytes written per put, the nodes read per lookup, the bytes read at a
start, the space after deletes. These are counts, and the Lean model, run
as a program on a workload, gives them for a candidate design before a
line of Java is written. That is the main thing model first gives the
second aim: several designs compared at the cost of a model each. The
second part is the constant: what the Java and the JVM make of each read
and write. Only the running Java shows it, measured against the release
jar with `java/stress/performance.sh`.

**Who checks the work.** Section 2's limit, that an AI agent writes
confident arguments that are sometimes wrong, does not apply to a proof
that Lean accepts. This makes the model the part best suited to this
item: many tokens, and a check that needs nobody. Frans's part moves from
reading code to reading statements: the specification and the theorems,
not their proofs.

**"Clean room".** Section 2 took the idea as an agent that has not seen
the source. That served two purposes: an independent implementation for
differential testing, and a measure of what the AI can do alone. Neither
is among the aims chosen, and for them the blindness has a price: the
reasons in the items, the measurements and today's model would be found
again or missed. Frans chose the informed start (section 7, question 1),
and the entry's name changed with it, from "a clean-room rewrite".


## 5. The experiment

Not a replacement of the code: an experiment after release 2026.4, on a
branch, in these steps. Each step ends with something that is useful if
the next is never made.

1. **The properties.** One document of what must hold (section 6).
   Like every step, by a session that reads all of the repo: today's
   model, the items and the measurements (section 7, question 1).
2. **The specification in Lean**, from the Pub API and the properties.
   Frans reads it.
3. **Candidate algorithms**, two or three, each as a Lean model that runs,
   one of them today's. The same workloads through each, at one million
   keys or more and with the worst cases of the properties; a table of
   the counts. Each with its main theorems stated in Lean and a short
   attempt at its hardest lemma, so that how a design can be proved
   counts in the choice. The session chooses one by a written rule (the
   brief, W5): the best counts among those that meet every property; if
   none beats today's by enough, today's algorithm is the one proved.
   Frans may overturn the choice.
4. **The proofs** for the chosen one, by section 3's meaning of
   "proved": that every operation, and every start after every cut that
   a crash may make, agrees with the specification; that reclaim and
   cleanup keep that; and its bounds, startup first, then the counts of
   step 3 that can be stated as theorems.
5. **The Java**, following the model, behind today's Pub API.
6. **The comparison** with the release jar: the f-tests through the Pub
   API (`java/f.sh`), the conformance with the model, and
   `java/stress/performance.sh` at one million to 100 million keys.

Steps 1 to 4 need no quiet machine. Steps 5 and 6 do, for the
measurements.

All six steps have one brief, [brief.md](brief.md), and take several
goes. A go runs until the end time Frans gives it; the next continues
from the entry's `state.md`, and the state of the proofs is a generated
list of the theorems still open.

No step waits for Frans (2026-11-10, 19:29: "This task should run
unattended as far as possible. Do not wait for me. One short
initialization, then unattended for 24h or so. That should be the
plan."). The choice of step 3 is made by rule. When the proofs are done
the Java starts at once, on a branch, and the comparison after it. A
decision that no rule covers is made by the session, by the aims in
their order, and written down with the other options, for Frans to
overturn if he wants. The specification is the one thing worth his
reading early, as a fault in it costs proofs; the work does not wait for
that either. What is left to him is the end: whether the branch is
merged.


## 6. Before it starts

* **The list of required properties.** It does not exist as one document
  and it is the input that must be written first: bounded startup,
  reclaim and cleanup, safety at a crash, memory per KV, pauses, the sizes
  to handle. Mostly a collection from `docs/levels.md`, 007, 010 and 023;
  it states what must hold, not how today's code does it.
* **The performance aims, as numbers.** "Better" does not end an
  experiment. Which workloads, at which sizes, measured how, and what
  result counts as better than the release jar's: the worst cases of
  large databases first, as in today's measurements. Part of the
  properties.
* **Where today's code loses.** Not known to this entry. A new algorithm
  is worth its proofs only where today's costs are high, so the
  candidates of step 3 start from a measurement of the release jar, by
  the counts of section 4.
* **The release to compare with.** 2026.4 or later, when the Pub API is
  the stable baseline. Frans, 2026-11-10, 18:28: "Yes, timing against
  2026.4." So no go before that release is tagged.

The first three of these are the work of steps 1 to 3 themselves (the
brief's W1 and W3): a go needs none of them written beforehand.


## 7. Open questions

1. **What the work starts from.** Decided by Frans, 2026-11-10, 18:21:
   "Yes, b." The three options as they were asked:
   * (a) **Blind.** The session gets the Javadoc, the jar and the
     properties, and has not read `java/`, `lean/` or `items/`. It gives
     an independent implementation and a clean measure of the AI. The
     properties must then carry everything the items know, and what they
     leave out is found again or missed.
   * (b) **Informed, with a free algorithm.** The session reads
     everything: today's model, the items' reasons, the measurements. It
     may change the stream format and the algorithm; only the Pub API and
     the properties bind it. The risk is that it stays close to today's
     design; step 3's rule of two or three candidates compared by counts
     is the guard. Recommended, for the aims of section 3. Chosen.
   * (c) **Today's algorithm kept.** The Java is written again from
     today's Lean model, which becomes the source. The smallest of the
     three, with no new proofs of the algorithm; the gain in performance
     is limited to what the Java can give, as the stream stays the same.
2. The time box. Decided by Frans, 2026-11-10, 18:28: "24h. Something
   like this. Depends on how long I have left until a token reset." Each
   go names its end, usually a usage reset, and the work does not resume
   by itself after it (the brief, sections 1 and 5). The six steps take
   as many goes as they need; each is a short start and then unattended.
3. Closed by question 1: it asked how a blind session is kept from
   the source and from the f-tests. Under (b) the session reads both.
4. Whether today's stream format must still be opened by the new code.
   2026.4 needs no backwards compatibility (020); for a later release it
   is Frans's decision.
5. The whole of BergDB, or the Core under today's Pub layer. Decided by
   Frans, 2026-11-10, 18:28: "Core only. The only thing with that is the
   Core API is less well-defined then Pub API. But, Core is a good start.
   I agree." So today's Pub layer stays, on a new Core, and the first
   piece of the work is to find and write down the Core's contract: the
   methods that the Pub layer calls (the brief, W1, part 1).
6. Whether concurrency gets a model of its own, small, for the one writer
   and its readers, or stays with tests.


## 8. Size and Frans's part

Frans's part (the brief, section 6): each go, with its end time. Nothing
else is needed. What he may read when he wants: the specification (about
300 lines of Lean, with its text and its assumptions), the list of
theorem statements that were changed, the choice, the properties (at
most 400 lines), the report (at most 200 lines). At the end: whether the
branch is merged.

Size, as estimates, in goes of 24 hours with four subagents: the
properties, the specification, today's counts and the candidates about
one go; the proofs the largest part and the hardest to estimate, several
goes (today's model and its proofs are about 52,000 lines of Lean, in
this repo since 2026-10-14); the Java and the comparison a few goes,
with the hours of the large runs. One go of 24 hours does not reach the
Java.


## Log

2026-11-10. Created at Frans's request (17:55), from the discussion of
14:50 to 16:08 with Claude (Fable 5.2, Claude Code).

2026-11-10. The aims chosen by Frans (18:04): the model first in Lean,
then performance, the API kept; the implementation may be more complex
where performance needs it. Sections 3 to 8 written for them: the three
layers, the steps, and the question of what the work starts from.

2026-11-10. Frans chose what the work starts from (18:21): (b),
informed, with a free algorithm. Renamed at his word from "a clean-room
rewrite" (`01-clean-room-rewrite`) to "a model-first rewrite".

2026-11-10. Frans's answers (18:28): the Core only; about 24 hours for
steps 1 to 3, until a usage reset; not before release 2026.4; and "Help
me with this" for the brief. The brief for steps 1 to 3 written,
`brief-steps-1-3.md`, and the status set to ready.

2026-11-10. Frans (18:46): "I want proofs. [...] We want a proven
model." Section 3 says what "proved" means and that no Java comes before
the proofs; step 4 says what is proved. How the proofs enter the go is
asked of Frans; the brief is not changed yet.

2026-11-10. Frans (19:23): "Yes." to the brief rewritten for proofs. The
brief is now [brief.md](brief.md), for steps 1 to 4 (was
`brief-steps-1-3.md`): the session chooses the candidate by a written
rule and goes on to its proofs; the work runs over several goes, each
until its end time, carried by `state.md`; proof enters from the start
(the specification's own theorems, each candidate's theorems stated and
probed before the choice); theorem statements are fixed after their
review, and a change is listed for Frans.

2026-11-10. Frans (19:29), on "the Java waits for your decision": "No!
This task should run unattended as far as possible. Do not wait for me.
One short initialization, then unattended for 24h or so. That should be
the plan." The brief now covers all six steps with no step that waits:
W7, the Java on the branch `025-01-core`, starts when the proofs are
done, and W8, the comparison, after it; decisions without a rule are
made by the session and written down for Frans to overturn; a go starts
with two or three lines, not a round of questions. The merge of the
branch is the only thing left to Frans.
