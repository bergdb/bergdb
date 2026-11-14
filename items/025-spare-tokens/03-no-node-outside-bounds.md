# 025-03. The top theorem with no node outside the bounds (F1)

Created 2026-11-14 by Frans Lundberg. Status: ready (accepted; to start
after 025-02's names step has landed).

F1 of 026-16, section 4.2. Frans, 2026-11-14, 13:46: "OK, good; I accept
the recommendation F1."


## 1. The idea

The tree model's descents carry fuel, (G + 1)(H + 2) + 2 steps, from the
bounds G (the largest segment of a key node) and H (the largest height
of a key node in its segment tree). Since 11 November (024-22, MF3) the
model lets a transaction make a key node outside G and H for a moment:
a delete in a full leaf splits it, the split cascades to a new root, and
the same delete's merges and root collapse take that root back (MF1).
Java never writes it, so a trace's H, taken from the nodes written, is
one too low for that moment. The node is noted (`W.outside`) and is an
error only if the transaction ends with it (`boundsOK`). Inside a
transaction "every height is at most H" is therefore false, and the
proofs go around it with the premises `htb`, `hMSF` and `hCoF`.

F1 adds one condition to the top theorem: no transaction of the run
makes a key node outside G and H (each `newKey` within the bounds; 026-16
calls it NoOutside). The theorem holds for every G and H, so for a run
of Java's an H that covers its highest moment is chosen. Java, the
stream format and the model's definitions do not change; the theorem
with the ten premises stays as it is, and the new one goes beside it.


## 2. The steps

1. **The checker.** The tree checker (lean/Check, TreeCheck) runs a
   trace with the trace's own G and H. It gets an option to run with a
   larger H (H + 1 first) and to compare a node's segment and height in
   place of its level number. On the conformance traces: how many
   transactions make a node outside the trace's own bounds, and whether
   H + 1 covers every one. The result goes here (section 3).
2. **The theorem.** Beside the top theorem (LatestTop.lean after 025-02's
   names step): the same conclusion with NoOutside in place of `htb`.
3. **`hMSF` and `hCoF`** as corollaries of the heights' walk under
   NoOutside (`SeenHeightBound` at H, `segFits_of_seenHeight`), as
   026-16, section 4.2, expects; stated for the states a run reaches.
4. **Open, not part of this entry:** a theorem that the model with a
   larger H makes the same tree, the levels apart (026-16, 4.2, "What the
   theorem then says"); now an argument from reading the definitions.

Every step is gated as 025-02's (a full build, the axiom audit, the
trusted closure's fingerprint, the statements unchanged).


## 3. Results

(None yet.)
