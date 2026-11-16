# 026-19. The proof trial of 026-18: subtransactions in Lean

Created 2026-11-16 by Frans Lundberg. Status: open (the plan being
written; the trial not started).

A short proof trial of 026-18's idea, on MT's rules as 026-17 tried them
(`Mt.lean` on the branch `026-17-mt-trial`): prove that one fix step
keeps the invariant that holds between subtransactions, and that gets and
scans are right at the times that end a main transaction. It turns the
proofs' gain, an estimate in 006-28 and 026-17, into evidence before
Frans decides MT, NW or neither.

Frans, 2026-11-16, 13:11, on 026-18: "A "short proof trial" does seem
reasonable. Perhaps starting tonight after 22.00, we will see. Depends on
other work." 13:48: "Plane the short proof trial (3). Use a Fable High
agent."

The proposal it starts from (026-18, section 5): one or two
prover-days; (1) a step lemma: one fix step (a merge) keeps the
in-between invariant, the full invariant with holes on the paths of the
keys still being fixed; (2) gets and scans right at visible times from
the full invariant, reusing today's proofs; (3) if time allows, the holes
close when the driver ends, for one key.

The plan follows.
