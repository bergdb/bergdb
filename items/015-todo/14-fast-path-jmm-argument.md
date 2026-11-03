015-14. Fix: the fast path's plain reads rest on the address dependency, not on the JMM
==========================================================================================

Status: open. Kind: Fix (decided). Created 2026-11-03 by Frans Lundberg.

For Frans; a known issue of 2026.2 until decided. Found by review R1
(016-06/R1 (items/016-release-2026-2/06-reviews/R1.md)), R1-F3, with the interleaving written out (to be checked by a
second agent, 016-06, section 2.6).

What: 009-02, 3.4 argues that the fast path's plain read of a pointer is
safe by the Java Memory Model. R1 shows an interleaving in which the
JMM allows the plain read to pair the handle's older object with the
pointer's older reference, which `usable` accepts, giving a version
without a change committed before the reader's lookup time. HotSpot does
not do it, as the read of the object depends on the pointer's address; so
it is a gap in the argument, not a fault seen. 015-12's fix leans on the
same dependency on the reader's side.

Options: A, acquire reads of the pointer (T6a) and of the key node's
arrays, which costs a little on AArch64 per follow and search (to be
measured in a quiet block); B, rewrite 009-02, 3.4 to state the reliance
on the dependency, as HotSpot keeps it.

Recommendation: B for 2026.2 (no change to the read path), then A
measured; if its cost is small, A.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).

2026-11-03, 17:18. Frans: ""thread safety rests on today's JVM
behaviour". This is not acceptable. Ensure this is either fixed before the
release or clearly documented as an open todo item. This needs an
investigation and a fix." So: an investigation (R1-F3's interleaving
checked; every plain read of a shared field on the read path that relies
on an address dependency, 015-12's reader side included) and a fix that
makes the read path correct by the Java Memory Model, before the release.
If it is not done by the freeze, this entry stays an open Fix and the
notes say so in their known issues.
