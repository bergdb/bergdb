028-02. Fix: Reclaim's and Db's comments that disagree with the code
====================================================================

Status: open. Kind: Fix. Frans: none.
Created 2026-11-13 by Frans Lundberg.

What: nine Java comments state a rule of reclaim that the code does not
follow (`Reclaim.java`, `Db.java`), found when 027-13 (Reclaim) was
written and reviewed against the code. The list, with file:line and the
corrected wording, is 027-13's last section, "For the code's comments":
"twice" that should be "more than twice"; when a step comes; "has
passed" that should be "has reached"; what `KEY_PREFIX_SKEY` covers; a
rerun in a step cannot happen; the cut is at pCut under its real
conditions (`pretruncateIfPossible`); what `kvCount` counts; the
condition of `Db.maintain`'s new iteration; `Db.makeDirtyIfNeeded`'s
`@return` on a void method.

Why: 027 with Lean is the authority for the exact rule; comments may
repeat or summarize it, so that a reader can tell whether the code does
what it should (Frans, 2026-11-13, 11:09, 027-04's Q5). A wrong comment
misleads the next reader.

Frans: none.

Done when: each comment says what the code does, in agreement with
027-13, citing it where useful ("bergdb 027-13, section 1.4"); comments
only, no code change; `java/before-commit.sh` prints `BEFORE COMMIT OK`;
027-13's section "For the code's comments" then goes, with a Log line.

First step: read 027-13's list and each line it names on main.


Log
---

2026-11-13. Registered by coord-1113, from 027-13's review.
