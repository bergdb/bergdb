/-
The contract package (bergdb 030-17): what Java's top must hold for its
search through the skip pointers at a time t, under eviction and after
reclaim's cut. To read and to trust, with Top.lean and RecoverJava.lean.

Java's reader holds the super root, the newest top node, and reaches the
older top nodes through skip pointers (`findTop`, `TopDs.findSuperRootAtTime`,
Top.lean). Under eviction a top node other than the super root may be out of
memory, and is loaded through its handle when the search follows a pointer to
it. After reclaim's cut the records before the cut are gone, and with them
the top nodes that only they held (bergdb 030-07, 030-11): a skip pointer may
name a top node that no longer exists.

Java's search at a lookup time t at or after a time f reads only these top
nodes: the super root; top nodes made at or after t, along the skip pointers
whose cached time is at or after t (each names a top node of that root time);
and at the end the top node of time t (the target of a lowest skip pointer
whose cached time is at or before t, the top node just before). Every one of
them is a top node made at or after f, or the top node of time f. So the
search needs only those (`findRoot_from`, RecoverCutTheorems.lean):

* `TopFrom f tp tp'`: the top tp' holds the top tp from time f: the same super
  root (the last top node), and every top node of tp made at or after f, and
  the top node of tp of time f, is in tp' as it is in tp: its root time, its
  root pointer, its skip pointers with their cached times (Java's top node
  record, `StoredTopNode`). The other top nodes of tp, those made before f
  but the top node of time f, may be missing from tp' (evicted, or gone with
  a cut) or be anything.

Everything here runs; nothing needs Mathlib.
-/
import Contract.Top

namespace Contract

/-- The top tp' holds the top tp from time f: the same super root, and each
top node of tp made at or after f, and the top node of time f, as in tp. -/
structure TopFrom (f : Time) (tp tp' : Top) : Prop where
  last : tp'.getLast? = tp.getLast?
  keep : ∀ zn ∈ tp, f ≤ zn.2.time → tp'.node zn.1 = some zn.2
  atF : ∀ zn, topAt tp f = some zn → tp'.node zn.1 = some zn.2

end Contract
