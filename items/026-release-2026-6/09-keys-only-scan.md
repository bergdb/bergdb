# 026-09. Reclaim's scan without the values it does not rewrite

Created 2026-11-13 by Frans Lundberg. Status: open (registered; after
026-05).

For release 2026.6: option (b) of 024-34's Q34-1. A reclaim step's scan
does not follow a value pointer whose stream position is at the cut
position pCut or later (the position is known before the follow; a new
option of `GetMany`, for reclaim only), and counts such a KV as its
key's bytes plus 100, its value length unknown. At 1M keys with a 20 MB
cache these loads are 43 % of a step's loads (024-34, section 4).


Decided
=======

Frans, 2026-11-13, 09:38, "Yes", to the coordinator's recommendation:
"(b) for 2026.6, after P8 lands. P8 (026-05) changes how a reclaim step
scans, so (b) should be built and measured on top of it. It also
belongs with 2026.6's other changes to the stream's bytes, to be
measured with G3 and the reclaim cost. Until then, (a) stays as is."


What it changes
===============

* The steps' boundaries, so the stream's bytes: new StreamDigest
  digests, a new reference for the C clone; no record format.
* Reclaim's pacing: a step covers more keys when most values are new,
  so an iteration ends sooner in stream growth.
* Measured before and after: G3 (the stream kept, 024-30), ReclaimCost,
  026-04's workloads at 1M and 10M keys, the loads a step.
* Its relation to 026-05: P8's step walks keys it does not rewrite
  (026-05, Risks: "A step still loads the value of every key it walks; a
  keys-only scan would remove those loads"), so this is P8's follow-up.


Log
===

2026-11-13. Registered by coord-1113 (Frans, 09:38), from 024-34's Q34-1.
