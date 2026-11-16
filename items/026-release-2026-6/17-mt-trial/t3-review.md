# 026-17, T3: a review of lean/SIS/Tree/Mt.lean

Agent R, 2026-11-16, 11:36 to 11:51 (times from `date`). Read: 026-17,
sections 2, 3, 5.2, 6 and 7.1; `Mt.lean` at the clone's head (560 lines,
commits d8ce08ba, 452723f4, 86e60d30); `Exec.lean` (1,175 lines, as on
main). Nothing in the clone was edited. Scratch files in
`/Users/f/fl/bench/026-17/review/`: `fuel.lean` and `fuel2.lean` (finding 1), `fuzz.lean`
and `fuzz2.lean` (finding 9).

Summary: no slip against section 3, and no path found where a fix step
or a user transaction makes a node and leaves it out. One rule of the
plan that Mt.lean follows is wrong (the driver's fuel, finding 1), and
the counts a key that the plan asks for will mislead (finding 2). The
rest are notes for T2, T4 and T8.

Marks: 0 "must fix before T4", 3 "should fix" (1, 2, 9), 8 "note".


## 1. The fuel a key is not a bound: a false S3 (should fix)

- **Place:** Mt.lean:385, 399 (`fixKey`, `fixGo`: `(p.M + 2) * p.fuel`
  fix steps a key); 026-17, section 3.4 ("a level gives at most M
  merges, and a path has at most `p.fuel` levels").
- **Found:** the argument does not hold. A key's loop runs until its
  path needs no fix, and its path keeps reaching new nodes: after a
  merge into one of two empty leaves the merged node is again empty and
  is merged with the next sibling; an inner merge brings a new parent's
  children under the path. So the first deleted key (in key order) of
  a mass delete makes nearly all of its group's fix steps, about as many
  as the tree has nodes in that region. Measured (`review/fuel.lean`,
  all keys put, then all deleted in one transaction):
  - node size 8 (`Small.p8`, fuel 320): 100 keys, 56 fix steps, all of
    them key [8]'s; 200 keys, 114, all key [8]'s; **600 keys: `MT: the
    fixing does not end: key [8] at 334, after 320 fix steps`**. The same
    run with H = 20 (fuel 680, `review/fuel2.lean`) ends after 330 fix
    steps, all key [8]'s: a fixing that ends, reported as S3.
  - node size 30 (6.1's params, fuel 832): 1,000 keys, 79 fix steps, all
    of the first key.
- **Why it matters:** S3 stops MT. None of the planned runs seems to
  reach the bound (the largest one-transaction delete is family E's
  1,000 keys at 30, about 79 steps; D at 8 deletes at most 100 of 200
  keys in one transaction, about 60), but a false "does not end" would
  be a wrong verdict, and T8 must not cite 3.4's argument as a reason
  that the fixing ends.
- **Remedy:** pool the fuel over the group: `keys.length * (p.M + 2) *
  p.fuel` fix steps for the whole driver (a few characters in `fixGo`
  and `fixKey`; the message names the group's count). Keep the error
  text. Correct 3.4's sentence in the plan (or in the result): the
  bound is a guard, not a proof. Report in T4 to T6 the most steps of
  one group against the group's fuel, so that a near miss is seen.


## 2. Fix steps "for each deleted key" measure the key order, not the key (should fix)

- **Place:** 026-17, sections 2.1 Q4 and 5.6 ("fix steps for each
  deleted key ... against the number of nodes on its path, P4's 'about
  the path's length'"); Mt.lean's driver (R5) as specified.
- **Found:** as in finding 1, the first key of a group whose path
  reaches an untidy region does the region's fixing; later keys get 0
  or 1 steps. With 200 keys deleted in one transaction at node size 8,
  the counts a key are 114, 0, 0, ... The mean a key is meaningful
  (the group's sum over its deletes); the "most" and the comparison with
  one key's path length are not.
- **Why it matters:** Q4's counts and 5.6's P4 comparison would say
  "a key needs 114 fix steps against a path of 4" for a mass delete,
  which is a statement about the group.
- **Remedy (T2 and T8):** report fix steps a group (sum, most), and a
  group's sum over its deleted keys (mean, most); keep the counts a key
  only for groups of one delete, where they are the path's fixing.


## 3. Q1's second half and K6 hold by construction (note)

- **Place:** Mt.lean:261 (`MT: a fix step merges a node of its own
  transaction`), 301 (`MT: a fix step collapses a root ...`), 313 to 325
  (`fixStep`).
- **Found:** a fix step builds its path and finds its target on
  P@(i-1) before it changes anything, and makes one fix. So when
  `merge` and `collapse` test `firstTime == some tt`, no node of time
  tt exists yet: the two `MT:` errors cannot fire. Likewise no
  definition that MT calls sets `W.taken` (`takenBack` is called only by
  `takeBack`, `takeBackRoot` and today's `merge`), so K3's "W.taken is
  empty" cannot fail; and `fixStep` returns false only before any
  write, so K6 cannot fail.
- I also checked what the step writes after its fix: every node a fix
  step writes is written once (the merge's m1 and m2 when made; the
  parent p; then one node a level by the cascade of `appendKlongs`; the
  top node at most once), every node it makes is put under a klong of a
  node it writes in the same step, or is the new super root. So
  `handleFullWith`'s `toPrev` (Exec.lean:398 to 399) has nothing to take
  back in a fix step, and `newInTrans` is always false there.
- **Why it matters:** Q1 then rests on K3's reachability alone, which is
  the right check (a node left out is a node not reached); the result
  should say that the `MT:` errors are guards that cannot fire, not
  evidence.
- **Remedy:** none in the file; T8 words Q1 as "K3, every boundary";
  the `MT:` guards may stay.


## 4. The user transaction still takes back entries, by the split (note)

- **Place:** Mt.lean:62 to 104 (R1) call `appendDeleteKlong`,
  `appendKlongs` and `handleFullWith` unchanged; Exec.lean:398 to 399
  (`toPrev (tt - 1)` of a node that existed), 311 to 325 (`setMadeFor`,
  `replacedBy` in the in-place space split).
- **Found:** in a user transaction of several operations, a node that an
  earlier operation changed and a later one splits loses its klongs of
  tt (`toPrev`): today's "take-back of a change", which MT keeps. No
  node is made and left out (I found no path for that in R1: a node
  that the transaction made is split in place, and a split's new nodes
  are always under a klong of the node above). `madeFor` is still
  written by the splits, but in MT nothing reads it to take a node back.
- **Why it matters:** for Q1 nothing (Q1 is about nodes). For Q7: 5.7
  expects `replacedBy`, `setMadeFor`'s `madeFor` and `W.madeFor` to be
  freed; the dependency walk will keep them, since `handleFullWith`,
  which R1 and every fix step call, uses them. They are freeable only by
  a further edit of `handleFullWith` that the trial does not make. And
  "nothing is ever taken back inside a transaction" holds for nodes, not
  for entries: `toPrev` and Java's `toPreviousState` stay.
- **Remedy:** T7 lists `replacedBy`, `setMadeFor` and `W.madeFor` as
  "kept by the split's code, dead in MT"; T8 says what "taken back"
  means in Q1.


## 5. A fix step's cascade can leave the level bounds where today's writer would not (note)

- **Place:** Mt.lean:335 (`boundsNow` after a fix step); Exec.lean:166 to
  172 (`newKey`'s comment: a delete can make a root one above the
  bounds that root collapse takes back in the same operation, 024-22,
  MF1 and MF3).
- **Found:** if a merge's parent is the space root (or a segment root)
  at height H and full, its split makes a root at H + 1; today the
  collapse in the same operation takes it back and `boundsOK` passes,
  MT's fix step ends with `bounds:`. Section 2.3 counts this as a cost,
  and 6.1 gives room (H = 6), so it should not be seen.
- **Remedy:** T2 counts `bounds:` apart for MT and for today's writer,
  as it plans; a `bounds:` in a fix step ends the run's group, so the
  program should say which side gave it.


## 6. The merge of an empty leaf can be a merge into two (note)

- **Place:** Mt.lean:233 to 263 (the sibling's choice and `mergeKlongs`,
  unchanged from Exec.lean:878 to 907).
- **Found:** an empty leaf whose left sibling has more than c live
  klongs (a leaf can hold up to M - 2) and that has a right sibling also
  above c, or has no right sibling, is merged into two new nodes: the
  sibling's klongs redistributed. Today's UP makes no node there (a
  bitmap, or LE-b, in the parent). It is section 3.3's general rule,
  so not a deviation; but it is the costliest form of R3 (2 new nodes,
  the parent changed, nothing gained in fill).
- **Remedy:** T2 counts `fix.merge.empty` with `fix.merge.two` apart
  (both notes are in the same fix step's trail), for Q5 and Q6.


## 7. The cascades inside a fix step: not in the guards, reached in my fuzz (note)

- **Place:** Mt.lean:507 to 556 (the 10 guards); T1's log (the fuzz).
- **Found:** the only nodes a fix step makes besides m1 and m2 come from
  the cascades: `mergeParent`'s full parent (`merge.parent.full`,
  `merge.parent.dead`, then `split.time1`, `split.time2`, `split.space*`),
  the unlink's bitmap in a full segment leaf (`bitmap.full`,
  `bitmap.dead`), the collapse's `appendKlongs` into a full segment leaf.
  These are where K3 can bite, and none of the guards reaches one. My
  fuzz2 (finding 9, seeds 5 and 6, 326 fix steps) reached them inside
  fix steps, all checks green: `merge.parent.full` 107,
  `merge.parent.dead` 41, `dead.compact` 53, `split.time1` 169,
  `split.time2` 27, `split.space1` 15, `split.space2` 4, `split.space3`
  1 (a fix step that grows the tree), `rc.replace.segment` 39,
  `rc.replace.space` 15, `fix.unlink` 2, `fix.pass.onlychild` 2,
  `fix.merge.bothempty` 1. Not reached: `bitmap.full` or `bitmap.dead`
  in an unlink (a full segment leaf unlinking its tree), and a split of
  the segment leaf in a segment collapse (cannot be told from the
  notes).
- **Remedy:** T2's "what was reached" lists today's notes inside fix
  steps apart from those of user transactions (the trail is a step's
  own), and T4 checks that `merge.parent.full`, a split in a fix step,
  and `bitmap.full` in an unlink are each reached above 0 times; if
  not, the result says "not reached" for them.


## 8. Readers meet new states at untidy boundaries (note)

- **Place:** Mt.lean:62 to 69 (`deleteLeaf` leaves an empty segment
  tree under a live klong of the segment leaf above, and empty or lone
  time klong leaves that are not roots); guard 2 checks `get` only.
- **Found:** today's writer never leaves a non-space segment root empty
  at a boundary (UP unlinks it in the same operation); MT does, until
  the unlink step. A scan that enters a long segment and finds an empty
  tree, and a scan across an empty non-root leaf, are new to the
  readers.
- **Why it matters:** Q2 (S2). K1 with scans at every boundary covers it
  if the families reach it: family G (one-node segment trees that empty)
  at both sizes.
- **Remedy:** T4 checks that K1's scans ran at boundaries right after a
  user transaction that left a segment tree empty (`user.emptied` with a
  following `fix.unlink`).


## 9. Q3: the target's order and the driver (should fix: one wording; the rest note)

- **The target** (Mt.lean:179 to 210) is section 3.3 exactly: the walk
  starts at the path's lowest node (`targetGo (pathSize)` looks at depth
  pathSize - 1 first), a root by `q.leaf` as `mergeUp` (Exec.lean:943),
  the three root cases, the merge on `2 ≤ q.cnt`, R4's pass. A walk that
  returns `.none` has seen no fill fault on the path: every non-root has
  m live klongs or more, every inner root two or more, every segment
  root but the space root a live klong. Above an only child the walk
  always finds a fix (the parent has one live klong, so it is under m,
  or an inner root that collapses), as 3.3 says.
- **The driver cannot stop while a fix is needed**, by this argument: a
  node gets under the fill only by a delete in it (on that key's path)
  or by a merge, unlink or collapse below it (on the current key's
  path); a merge's new nodes have more live klongs than the node they
  replace; a cascade's time split keeps a node's live klongs and a space
  split gives halves of at least h / 2 ≥ m (TP28). So a fix for key k2
  never puts a fault on a path of an earlier key k1 that is not also on
  k2's path. K7 found no second pass in T1's fuzz or in mine.
- **It cannot loop:** the fuel; but see finding 1.
- **My fuzzes** (`review/fuzz.lean`, `fuzz2.lean`; node size 8, 150 keys
  of one, two and three segments, segment trees of up to 60 keys, so
  inner segment roots; all keys put, then random transactions of up to
  10 to 150 operations with 50 to 90 % deletes; 6 seeds): at every
  boundary K1 (`get` of all 150 keys), K3 (made key nodes reachable,
  `W.taken` empty), the fault kinds of K5 (only `NonEmptyOK`, `RootsOK`,
  `FillOK`; not the nodes); K4 at every tidy boundary; K7 after every
  group. No failure. 1,320 fix steps over the six seeds; at the user
  transactions `bitmap.full` 694 and `user.emptied` 72.
- **Should fix (wording):** the plan's K5 defines pending keys as "the
  group's deleted keys whose fixing has not ended". With this driver
  that is the current key and the keys after it; T1's fuzz used all the
  group's deleted keys, which is weaker. T2 should use the strict set,
  or K5 can pass a fault on a finished key's path.


## 10. The deviations D1 to D9 (note)

All nine are as the header says and none changes a rule of section 3:
D2 (the empty inner node at every depth) only moves an error earlier;
D3 gives the same `bounds:` as `boundsOK` would, since R1 takes nothing
back; D9's two `Bug:`s cannot fire by the walk. One addition to D5:
`pathAt` reads a key node's whole history from a later view, but every
search it makes is at t, so the path is the path at t.


## 11. Smaller points (note)

- `fix.pass.onlychild` is noted in the walk; in a call that ends in an
  error after it, the note is lost with the state, which is right. A
  pass is always followed by a fix in the same step, so counting it from
  fixed steps only is complete.
- `fixAll`'s `cut` runs the driver twice, the checking `apply` too: the
  mutant's boundaries are checked twice. Harmless. The mutant bites by
  construction: every fix step's target is a fill fault (`FillOK`,
  `NonEmptyOK` or `RootsOK`) before the step, so leaving out the last
  step leaves a fault at the tidy boundary.
- `deletedKeys` relies on `noops` being in the order of the `ops` given
  to `runUser`; T2 must pass the normalized list to both (the guards
  do).
