025-spare-tokens
================

Created 2026-11-10 by Frans Lundberg. Status: open.

Things to do on BergDB with spare AI tokens: work that uses many tokens
and very little of Frans's time. An entry starts with a short dialog with
Frans and continues as long unattended work. Frans, 2026-11-10, 17:37: "an
item that list things to do with spare AI tokens. [...] Work that consumes
a lot of AI token, but very little human interaction time. Very little
time with me. Mostly just single-shot. Or rather a short dialog followed
but long unattended work."


Rules
=====

* An entry is a subitem: the idea, why it is worth the tokens, what must
  exist before it starts, how its result is judged, and its size.
* An entry's state is one of: idea (notes only), ready (what it needs
  before a start exists, so the short dialog is all that is left), running,
  done, or dropped (with the reason). Its own `Status:` line says which,
  and its line under Files repeats it.
* An entry's plan has no step that waits for Frans (Frans, 2026-11-10,
  19:29: "This task should run unattended as far as possible. Do not
  wait for me. One short initialization, then unattended for 24h or so.
  That should be the plan."). Where a decision would stop the work, the
  plan has a rule, or the session decides by the entry's aims and writes
  down what it chose, for Frans to overturn afterwards. What is left to
  him is the start and what is done with the result.
* Frans starts an entry, when he has tokens to spare. An AI agent does not
  start one on its own, and does not spend a night on one without Frans's
  word, as an entry is large by definition.
* What belongs elsewhere: a short task that an AI agent does in a day or
  two is an entry of the todo list (019, 021); a topic that needs Frans's
  thinking over time is a topic of 017. An entry here needs little of
  either: it is clear enough to hand over, and too large for a todo.


Files
=====

* [025-01](01-model-first-rewrite/readme.md). A model-first rewrite of
  BergDB behind today's Pub API, with a release jar as the black box to
  compare with, time-boxed. The aims (Frans, 2026-11-10): the model first
  in Lean, then performance; the code may be more complex where
  performance needs it. It starts informed, from all of the repo, and may
  change the algorithm and the stream format; the Core only. Ready for a
  go, not before release 2026.4: the properties, the specification in
  Lean, the candidate algorithms compared by counts, the proofs of the
  one chosen, the Java on a branch, the comparison; over several goes of
  about 24 hours, each unattended after a short start; the brief is
  [brief.md](01-model-first-rewrite/brief.md).
* [025-02](02-proof-cleanup.md). The proofs' cleanup: one name for each
  route (the F2 to F4 versions) and one top theorem for the key tree
  (024-12), the stale Lean comments of 007-09, Q2; no statement Frans
  trusts changes. Started by Frans (2026-11-14, 13:00); the plan by
  coord-1114's planning agent, the provers in the night of 14 to 15
  November under the week's ceiling of 92 %. Status: running.


Log
===

2026-11-10. Created the item, at Frans's request (17:55), with 025-01 as
its first entry, from the discussion of the same afternoon.

2026-11-10. 025-01: Frans chose its aims (18:04), the model first in
Lean and then performance, with the API kept.

2026-11-10. 025-01: Frans chose an informed start with a free algorithm
(18:21); renamed from `01-clean-room-rewrite` to `01-model-first-rewrite`.

2026-11-10. 025-01 ready for a go on its steps 1 to 3, with their brief,
after Frans's answers of 18:28: the Core only, about 24 hours, not before
release 2026.4.

2026-11-10. 025-01: the brief rewritten for proofs, at Frans's word
(18:46, 19:23): steps 1 to 4, a proved model as the result, over several
goes.

2026-11-10. The rule that an entry's plan has no step that waits for
Frans, at his word (19:29); 025-01's brief now covers all its steps, to
the Java and the comparison.

2026-11-14. 025-02, the proofs' cleanup, created and started (Frans, 13:00:
"Yes, good. Go ahead.").
