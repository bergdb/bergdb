# 025-04. The true form of hU: the plan

Created 2026-11-15 by Frans Lundberg. Status: open (the plan being
written).

`hU` (`UpUnlinkTreeOK`), a premise of the key tree's top theorem, is false
as stated (`upUnlinkTreeOK_false`, SIS/Tree/PremisesFalse.lean): it speaks
of every writer state with `PutInv` and the upward loop's end, and those
carry none of the writer's books. Its true form, at the states that runs
reach, is open: it needs an invariant on the nodes a transaction leaves
out (024-22, section 11.1). This entry is the plan for it.

Frans, 2026-11-15, 08:33, to 006-25, section 7, decision 1 (a planning
agent for that invariant before more provers): "as you recommend. [...]
The planning for hU, run it with Fable 5.2 High."
