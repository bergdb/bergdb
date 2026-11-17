# Prover A of 026-19: final message (23:42, saved by coord-1116)

Stopped 23:42 by the coordinator's size rule. Branch 026-19-proof-trial-a at 63864ac7, clean; every t_ theorem on the standard axioms; nothing on main.

Proved:
* A1, the bridge (MtBridge.lean, 1,131 lines, 42 min, gate a-1): a run of Mt.merge is a run of today's merge ending in the same state but the notes and madeFor, given no node taken back and every live child of the parent good (a live klong, no klong of the step's time, off the path above); writerWP_mtMerge carries today's merge lemmas to MT's merge; mt_putKv_put.
* A2, the path and the target (MtPath.lean, 398 lines, 7 min, gate a-2): after Mt.path and target the writer reads as before, made nothing; its path linked from the space root, cached, every node on the key's reading; for merge at depth d: PathOK down to x, the parent inner with >= 2 live klongs, x below m (writerWP_pathTarget, fixStart_of_reads).
* A3, the fill with holes, E2 (MtMergeLive.lean 1,575 + MtLiveTop.lean 28 lines, 46 min, gate a-3): t_fixWLive_merge : MergeParamsOK p -> MergeFullLive p -> FixWLive p IsMerge fixStep (= B's FixLiveW; top t_visible_A3). Proved outright, t_fixWLive_room: a merge fix step whose parent has room keeps the fill but at the holes before and on its key's new path (into one or two, inner or leaf, empty leaves R3). Run test first: 360 merge steps, 0 counterexamples.

Reduced to (E5): MergeFullLive p, the same for a merge whose parent is full (rule O split or compaction, the cascade up the path); of l4's kind (the split cascade's fill) but local to one fix step; no premise of htbL's kind.
Refuted: nothing; no statement changed.
Open: MergeFullLive, estimated 2,500-4,000 lines, 3-6 h: the cascade walk with holes (main's writerWP_appendKlongs_chainGLX, WriterTreeChainG.lean 1,750 lines, restated for holes below inner nodes) and the key's reading through the cascade's replaced nodes (no main lemma). Over twice A3's plan: not taken.

E1: A1 1,131 lines / 0.7 h; A2 398 / 0.1 h; A3 1,603 / 0.8 h.
E2: the fill 1,603 lines in 46 min, under 3,000; for a parent with room; the full parent a premise.
E3: the bridge does not apply to empty leaves; A3 proves the fill without it, needing no live klong in the merged nodes, so FixWEmpty's live part is covered; A5 needs PutInv, PutInvG, ranges, readings only.
E6: take-back words in statements (grep): MtBridge 15 (mostly the book stripping), MtPath 3, MtMergeLive 5; "restated from" 2 in MtMergeLive; Reach.lean not run.
E7: two notes, no failures; pathTarget_nil_noMerge renamed _A (B has one of that name).
Files: pt/a/clone/lean/SIS/Tree/MtBridge.lean, MtPath.lean, MtMergeLive.lean, MtLiveTop.lean; gates pt/gates/a-1..a-3; state pt/state-A.md; run test pt/evidence/A3Test.lean.txt (written by A in the coordinator's scratchpad).
