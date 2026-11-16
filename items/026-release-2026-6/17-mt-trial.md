# 026-17. MT's trial: maintenance transactions in the model

Created 2026-11-16 by Frans Lundberg. Status: open (the plan being
written; the trial not started).

A trial, in the Lean model only, of MT (006-28, section 7.5): a user
transaction makes no merge, no upward delete and no root collapse; each
of those is one fix step in a transaction of its own, run right after the
user transaction. The trial runs MT beside today's writer on the model's
workloads and counts, before any design, proof or Java. Its result goes
to Frans's choice between MT, NW and neither, with 026-12's SF10.

Frans, 2026-11-16, 10:29, on 006-28's questions 7 to 9: "MT's trial
first. Yes, let me know what you mean by "trial" here and how we should
plan this. Do not start the work."; the provers wait for it ("Yes");
"Yes. Deletes can cost more. In general, trading performance for
simplicity can be good trade. But this is a judgement call, a tradeoff.
Let's keep measuring performance and and judge complexity so we can make
the right tradeoffs."

Frans, 10:47: "About the trial. So, you suggest model-first to
investigate this. I like this. It is a new way of working for me and I am
excited about it. Plan for the trial. Run a Fable High agent that makes a
plan for excuting the trial."

**What the trial answers** (the coordinator's outline of 10:29, which the
plan makes exact):

1. Nothing is taken back: no fix step and no user transaction makes a
   node and leaves it out. MT's point; if it fails, MT is off.
2. Every get and scan is right at every transaction boundary, between a
   user transaction and its last fix step too.
3. After the last fix step, today's invariants hold (fill, live counts,
   heights); at best the tree is today's writer's, but for the ids.
4. The fixing ends: fix steps per deleted key, mean and most.
5. The cost: nodes and bytes written per delete against today; the
   tree's height between.
6. The two new rules (a merge of an empty node, of an only child) work
   as sketched.
7. The complexity: the lines of the model's definitions that MT adds and
   removes.

The plan follows.
