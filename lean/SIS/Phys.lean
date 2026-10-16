/-
Self-indexed streams in Lean: the physical layer, what Java holds in memory
(bergdb item 001, stages 1 and 2; its plan, section 8.6). Trusted part.

So far only what lemma M needs (WP L2); WP L1 adds the objects, the slots,
the node table and the first touch.
-/
import SIS.Startup

namespace SIS

variable {V : Type}

/-- Version w cut back to time s: its history up to s, its references as they
are. Java cuts back a key node version of the startup section to the startup
time when it reads one (`KeyNode.toPreviousState`; `DbStarter`,
`NodeCollection.followStreamPointer`). -/
def Version.cutTo (w : Version V) (s : Time) : Version V :=
  { w with hist := w.hist.upTo s }

end SIS
