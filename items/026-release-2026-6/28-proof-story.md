# 026-28. How the proofs came to work: the story of 2026.6

Created 2026-11-24 by Frans Lundberg. Status: done (a record).

How release 2026.6 came to its theme, proven algorithms: from proof work
that was close to being given up, to BergDB's core algorithms proved, in
about ten days. An overview, told for the way of working. The dates, the
theorems and the references are in 030-40. Frans's words of 17, 18 and
24 November are quoted with his approval (2026-11-24).

Frans, looking back on the morning of the release (2026-11-24):

> I find this story interesting from a way of working perspective. I was
> just about to give up. The writer contract approach then simplified
> everything and led to a rewrite of the algorithms. A simplification
> that allows the proofs to work and also has practical testability
> (testing invariants after each transaction).


# 1. Proving the code as it was

After release 2026.5, on 13 November, the plan was to prove BergDB's
index as it was. A Lean model followed Java's writer step by step: every
split, merge and undo, one operation of a transaction at a time. Several
AI provers worked on it day and night.

It went fast, and it did not converge. In four days the model grew to
nearly 280,000 lines of Lean. Each night closed some of the open
premises and opened others. Three times a premise turned out to be false
as stated, and with it the main theorem said nothing at all. One day and
night used most of a week's AI usage. After four days the writer was
still not proved, and no one could say how far there was left.


# 2. Close to giving up

On the morning of 17 November, the day BergDB went public, Frans was
close to giving up the proofs:

> I am considering pausing the proof work. This is too much work from
> my side and too much token cost. Cost is too high for uncertain
> progress.

The plan was to pause them and perhaps come back in a year.


# 3. The contract

Instead, the question changed: not "is the writer right in every step?"
but "what does a user rely on after each transaction?". The answer is a
**contract**: one statement of what must hold when a transaction ends.
The tree is well formed, it holds the old contents with the
transaction's changes, and only the nodes it marked have changed.

Then:

1. Prove what users rely on from the contract alone: every get and every
   scan, at every time, and after crashes, restarts and eviction. These
   proofs are small, and they do not change when the writer does.
2. Do not prove the writer, at first. Check the contract on the real Java
   code after every transaction instead, in its tests and on recorded
   traces. A fault is caught in the transaction that makes it.

Frans's verdict, less than two hours after that message:

> It is 80-20. 80 percent of the value, 20 percent of the work. It is
> very practical. Being able to test each transaction in isolation is
> very strong.

The work started again from scratch, in a new package ("I think we might
be stuck in too much dependence on history"). The first trial
took an hour and a half: reads proved from the contract. By the evening,
crash recovery, restarts, eviction and reclaim's cuts followed, and Java
checked the contract itself in its tests. Frans celebrated with
champagne. A practical model, tested after every transaction, could have
been the end of it.


# 4. Changing the algorithm, not the proof

The contract also showed why the old writer was so hard to prove. It
changed the tree one operation at a time and then undid the nodes it had
made and no longer needed. A proof had to follow all those half-finished
states. Against the contract, its puts were proved in an evening; its
deletes were not.

So the next morning the question was turned around: what writer would be
easy to prove? Several simpler designs were tried in the model in a few
hours. The first made the proof smaller at a cost in bytes written, and
Frans set the bar: "the real gain would be to actually get a complete
proof." An agent with a fresh view, one that had not read the earlier
studies, proposed **"plan, then emit"**: plan the whole transaction
first, then write each node once. Nothing is made and undone.

A two-hour trial in the model said go: no fault on hundreds of traces,
and slightly fewer bytes written than the old writer. In the evening
Frans started the proof: "Go! Good luck with the proof." That night the
new writer was proved to meet the contract, completely. The same night it
was written in Java, node for node the proved one, and the next morning
it replaced the old writer. That afternoon, reclaim was proved too.
The aim was reached: **BergDB's core algorithms are proved, given tested
assumptions.**


# 5. Where it ended

Release 2026.6 ships the proved writer. Its guarantees are a closed list
of fourteen: nine proved, five tested on purpose, each with its check,
and the list was reviewed by an independent AI against the Lean. The
Lean is less than half its peak size and proves more than the old line
ever did. The price is a writer a few per cent slower in some workloads,
and faster in others.


# 6. What it says about the way of working

- **A contract tested after every operation.** State what must hold
  after each operation; prove the users' guarantees from it; check it on
  the implementation after every operation; prove that an implementation
  meets it only when that is within reach. The same contract is the
  proofs' interface and the tests' oracle.
- **Simplify the algorithm when the proof is hard.** The writer was
  changed to fit the proof, and the simpler writer was proved in a night.
  Its Java code is about as long as the old one's, but it has no undo and
  no half-finished states.
- **Stopping is a real option.** Questioning the cost of the old line is
  what opened the way. The time already spent on it was not a reason to
  go on.
- **Small trials before large efforts.** Each new direction had a trial
  of an hour or two, with criteria that could refute it, before a night
  of work was spent on it.
- **Fresh and independent views.** The new writer came from an agent
  without the history. Independent reviews, by a second AI, of what the
  theorems state found where the text claimed more, and once a real gap.
