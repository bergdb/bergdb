028-47. Investigate: commits give a mass delete's space back by the clock
========================================================================

Status: open. Kind: Investigate. Frans: decision.
Created 2026-11-24 by Frans Lundberg.

What: 026-13's option B (U13-4, Q1), not studied in 2026.6: a commit
begins a reclaim iteration also on `maintain()`'s rule (a quarter of R,
a cut that releases 400 kB), so that `maintain()` is optional in effect
for a slowly written database. Option A, the Javadoc, was 028-06.

Why: after a mass delete followed by slow writes, the space comes back
many R later unless the application calls `maintain()`: in 026-13's C2,
6.4 MB kept at 10 R by commits alone, 1.2 MB at 2 R with `maintain()`
after each commit; in the Pub API, at its startup distance of 5 to
1,000 MB, after about 20 to 200 MB of new puts. Frans decided on
2026-11-13 that B is studied with G4 and taken only for a clear gain
(KISS); on 2026-11-24 that it is registered here, so that it is not lost
when 026 is done.

Frans: decision, after the study: B taken or not, the options in full
with a recommendation.

Done when: a report in this entry with G4 measured at C2's settings (a
startup distance of 1 MB, R = 200 drive transactions) and at the Pub
API's default, before and after B, in a clone; what B changes in the
stream's bytes of a slowly written database (not the format) and in
reclaim's proofs and checks (027-13, 030); a recommendation. No change
lands without Frans.

First step: read 026-13, section 6 and its C2 run, 027-13's pacing of
reclaim and `maintain()`, and 028-06.
