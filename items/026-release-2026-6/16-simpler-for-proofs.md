# 026-16. Simpler algorithms for the remaining proofs: a study

Created 2026-11-14 by Frans Lundberg. Status: open (being written).

What could change in BergDB's algorithms to make the Lean premises that
are still open simpler to prove, without significantly degrading the
database's function or performance.

Frans, 2026-11-14, 12:45: "What could be changed in the BergDB
algorithms to simplify the Lean proofing? Without significantly
degrading the functionality or the performance of the database. The
KISS principle allows us to buy simplicity with lower performance. It
is a tradeoff. I think simplicity here is not only Java code size, but
also the Lean model specification and proofing. Actually, the Lean work
is probably a better measure of algorithm complexity than the size of
the Java code."

Frans, 12:53, on the scope: "Look at only the remaining premises. This
is to limit the scope. To not disturb what is already proven. A later
study could look at the whole model. The reasoning is that we want to
reach a fully proven model first. When we have that, we can extend it a
step at a time. And simplify it a step at a time." Changes to the stream
format may be proposed (marked as such; 026-12).
