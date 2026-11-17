#!/bin/sh
# counts.sh: the numbers of 026-19's Result (E1, E3, E6 and the main line's
# night) by wc -l and grep, read from Git; it builds nothing.
# Usage, from the repository's root: sh items/026-release-2026-6/19-proof-trial/counts.sh > counts.txt
# 2026-11-17.

BR=${BR:-026-19-proof-trial}      # the trial's branch (5fea7405)
NIGHT0=${NIGHT0:-308299c5}        # main when the night started
MAIN1=${MAIN1:-454c05c3}          # main after htbL landed (00:56)
D=lean/SIS/Tree

files=$(git diff --name-only main...$BR -- $D | grep -v '/Mt\.lean$' | sed 's|.*/||; s|\.lean$||')

lines() { git show $BR:$D/$1.lean | wc -l | tr -d ' '; }

echo "# 1. Lines per file on $BR ($(git rev-parse --short $BR)), the trial's files (not 026-17's Mt.lean)"
total=0
for f in $files; do
  n=$(lines $f); total=$((total + n)); printf '%6d  %s\n' $n $f
done
printf '%6d  total, %d files\n' $total $(echo $files | wc -w)

echo
echo "# 2. Lines per step (the steps of 026-19, section 6.1, as the provers reported them)"
step() {
  name=$1; shift; s=0
  for f in "$@"; do s=$((s + $(lines $f))); done
  printf '%6d  %s (%s)\n' $s "$name" "$*"
}
step "P0b, the statements" MtRun MtSub
step "A1, the bridge" MtBridge
step "A2, the path and the target" MtPath
step "A3, the fill with holes" MtMergeLive MtLiveTop
step "A4, FixW for the merge" MtMerge
step "A5, the empty child" MtMergeEmpty
step "B1, the lift" MtLift MtBooks MtLiftProof
step "B2, the readers" MtReaders
step "B3, the step at the structure" MtStep
step "B4, the induction and the tops" MtTop
step "the merge's other parts" MtParts MtDead MtKinds MtKindsW MtHeights
step "E, the driver's end" MtDone
step "unlink and collapse at the structure, the fit" MtUnlink MtCollapse MtFit
step "tier 3, the unlink with room" MtUnlinkW
step "tier 3, the collapse" MtCollapseW
step "tier 3, the user's delete" MtUserDel
step "the user step reduced" MtUser
step "the user run's lift" MtUserBooks
echo "  (prover A: A1, A2, A3; prover B: the rest)"

echo
echo "# 3. E3: comments '-- restated from' (or 'restated from') per file"
for f in $files; do
  n=$(git show $BR:$D/$f.lean | grep -c 'restated from'); [ "$n" -gt 0 ] && printf '%6d  %s\n' $n $f
done
printf '%6d  total\n' $(for f in $files; do git show $BR:$D/$f.lean; done | grep -c 'restated from')

echo
echo "# 4. E6: lines naming a take-back book (taken, madeFor, TakeJ2, J2At, retarget, toPrev) per file"
W='taken|madeFor|TakeJ2|J2At|retarget|toPrev'
for f in $files; do
  n=$(git show $BR:$D/$f.lean | grep -cE "$W"); [ "$n" -gt 0 ] && printf '%6d  %s\n' $n $f
done
printf '%6d  total lines\n' $(for f in $files; do git show $BR:$D/$f.lean; done | grep -cE "$W")
printf '%6d  declaration lines (theorem, lemma, def, abbrev, structure) among them\n' \
  $(for f in $files; do git show $BR:$D/$f.lean; done | grep -E "$W" | grep -cE '^(theorem|lemma|def|abbrev|structure|private theorem) ')

echo
echo "# 5. The main line the same night: files added to main's $D, $NIGHT0..$MAIN1"
for pre in Htb Live; do
  s=0; k=0
  for f in $(git diff --name-only --diff-filter=A $NIGHT0 $MAIN1 -- "$D/$pre*.lean"); do
    n=$(git show $MAIN1:$f | wc -l | tr -d ' '); s=$((s + n)); k=$((k + 1))
    printf '%6d  %s\n' $n $(basename $f .lean)
  done
  printf '%6d  %s*.lean total, %d files\n' $s $pre $k
done

echo
echo "# 6. Sums the Result cites"
step "E1, the run's layer (lifts, parts, step, fit; unsized in 006-28)" \
  MtLift MtBooks MtLiftProof MtParts MtDead MtKinds MtKindsW MtHeights MtStep MtFit \
  MtUnlink MtCollapse MtUserBooks
mainsum() {
  name=$1; shift; s=0
  for f in "$@"; do s=$((s + $(git show $MAIN1:$D/$f.lean | wc -l | tr -d ' '))); done
  printf '%6d  %s (%s)\n' $s "$name" "$*"
}
mainsum "E2, main's merges with room inside a delete (not R1's descent)" \
  LiveHole LiveLoop LiveMergeRoom LiveMergeTail
mainsum "the frames, main's R1 (the descent finds the one hole again)" \
  LiveHoleDescent LiveRedirectDescent LiveHoleLeaf LiveUpHole
