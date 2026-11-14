#!/bin/sh
# 025-02's landing (2026-11-14): fast-forwards main to a gated cleanup commit and pushes.
# Usage: sh land.sh CLONE GATEOUT STEP
#   CLONE    the prover's clone; its HEAD is what lands (committed, nothing uncommitted in lean/)
#   GATEOUT  the gate's OUTDIR; its summary.txt says GATE PASS for a commit that HEAD contains,
#            and HEAD changes no lean/ file after it (a later merge of main that brought only
#            items is fine)
#   STEP     the step's name for the log (prune, comments, names, dups, close)
# Refuses: before 14:30 on 2026-11-14; when the main tree's HEAD is not an ancestor of the
# clone's HEAD (merge main into the clone first: git pull --no-rebase /Users/f/fl/repos/bergdb
# main; if that brings lean/ changes, gate again); when a commit message names an AI.
# Appends a line to /Users/f/fl/bench/2026-11-14/cleanup/landed.log.
CLONE=$1; G=$2; STEP=$3; M=/Users/f/fl/repos/bergdb; C=/Users/f/fl/bench/2026-11-14/cleanup
[ "$(date +%Y%m%d%H%M)" -ge 202611141430 ] || { echo "NOT LANDED: not before 14:30"; exit 1; }
[ -f $C/STOP ] && [ -z "$STOPOK" ] && { echo "NOT LANDED: STOP is set (the coordinator may land a gated commit with STOPOK=1)"; exit 1; }
grep -q '^GATE PASS' $G/summary.txt || { echo "NOT LANDED: the gate did not pass"; exit 1; }
gh=$(sed -n 's/^head: \([0-9a-f]*\) .*/\1/p' $G/summary.txt)
grep -q 'uncommitted lean files: 0' $G/summary.txt || { echo "NOT LANDED: the gate ran on uncommitted lean files"; exit 1; }
h=$(git -C $CLONE rev-parse HEAD)
[ -z "$(git -C $CLONE status --porcelain -- lean)" ] || { echo "NOT LANDED: uncommitted lean files in the clone"; exit 1; }
git -C $CLONE merge-base --is-ancestor $gh $h || { echo "NOT LANDED: the gated $gh is not in HEAD"; exit 1; }
[ -z "$(git -C $CLONE diff --name-only $gh $h -- lean)" ] || { echo "NOT LANDED: lean/ changed after the gated $gh: gate again"; exit 1; }
git -C $M merge-base --is-ancestor $(git -C $M rev-parse HEAD) $h 2>/dev/null || {
  git -C $M fetch -q $CLONE HEAD 2>/dev/null
  git -C $M merge-base --is-ancestor $(git -C $M rev-parse HEAD) FETCH_HEAD || { echo "NOT LANDED: main has moved; merge main into the clone (gate again if lean/ changed)"; exit 1; }; }
git -C $M fetch -q $CLONE HEAD || { echo "NOT LANDED: fetch failed"; exit 1; }
n=$(git -C $M log --format=%B HEAD..FETCH_HEAD | grep -icE 'co-authored|claude|anthropic|codex|openai')
[ "$n" = 0 ] || { echo "NOT LANDED: attribution words in a commit message"; exit 1; }
git -C $M merge -q --ff-only FETCH_HEAD || { echo "NOT LANDED: the fast-forward failed (a dirty file in the main tree?)"; exit 1; }
git -C $M push -q origin main || { echo "LANDED LOCALLY, PUSH FAILED: tell the coordinator"; exit 1; }
echo "$(date +%H:%M) $STEP $(git -C $M rev-parse --short HEAD) gate $G" >> $C/landed.log
echo "LANDED $STEP $(git -C $M rev-parse --short HEAD), pushed"
