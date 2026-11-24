#!/bin/sh
# Brings release 2026.6's commit A into main and pushes main (bergdb 026-27, step 12; 024-38's
# to-main.sh, adapted 2026-11-23), after A's gate and its checks of the night passed (026-27,
# step 11 and D4; this script does not read them: the lead or Frans says the night was clean).
# Run by the lead or Frans, from any directory:
#     sh to-main.sh SRC A              says what it would do (COMMIT=0)
#     COMMIT=1 sh to-main.sh SRC A     does it
# SRC is a repository that holds A (the clone of step 11), A is A's hash. It pushes main only,
# never a tag: Frans makes the tag release-2026.6 himself (release.sh prints the commands).
#   1. A's BuildInfo says 2026.6, and the tag release-2026.6 does not exist in MAIN;
#   2. MAIN (the main tree) is on branch main; A is fetched from SRC into MAIN (by its hash);
#   3. if main's HEAD H is an ancestor of A: a fast-forward of main to A (git merge --ff-only in
#      MAIN, which touches only A's changed files: other sessions' uncommitted files stay, and
#      the merge refuses if one of A's files has an uncommitted change there);
#      else, if main moved since A's base only in items/ (git diff --name-only BASE H outside
#      items/ is empty): a merge commit in a new clone of MAIN at H (R/merge), "git merge
#      --no-ff A" in Frans's name, then a fast-forward of MAIN to that commit, only if MAIN's
#      HEAD is still H; a conflict stops it;
#      else (main moved outside items/ after A's base): it stops, for a look (exit 1): A was not
#      tested with that change;
#   4. checks that A is in main's history, and with PUSH=1 (the default) runs
#      "git push REMOTE main" in MAIN (never a force) and checks that REMOTE's main is main's
#      HEAD (git ls-remote).
# Without COMMIT=1 it stops after step 3's decision and prints what it would do.
# Environment: COMMIT (0), PUSH (1), MAIN (/Users/f/fl/repos/bergdb), REMOTE (origin),
# R (the release's work directory, /Users/f/fl/bench/2026-11-24/release).
# Prints "TO MAIN OK: ..." (exit 0), "TO MAIN READY (COMMIT=0): ..." (exit 0) or
# "TO MAIN FAILED: ..." (exit 1). The record: R/out/to-main.txt.
# Created 2026-11-10 by Frans Lundberg; 2026.5's copy 2026-11-12; 2026.6's 2026-11-23.
SRC=${1:?usage: sh to-main.sh SRC A}
A=${2:?usage: sh to-main.sh SRC A}
V=2026.6
TAG=release-$V
R=${R:-/Users/f/fl/bench/2026-11-24/release}
MAIN=${MAIN:-/Users/f/fl/repos/bergdb}
REMOTE=${REMOTE:-origin}
COMMIT=${COMMIT:-0}
PUSH=${PUSH:-1}
O=$R/out
REC=$O/to-main.txt
mkdir -p "$O" || { echo "TO MAIN FAILED: cannot make $O"; exit 1; }
fail() { echo "FAILED: $*" >> "$REC"; echo "TO MAIN FAILED: $*"; exit 1; }
echo "to-main.sh $SRC $A, $(date '+%F %T'), MAIN $MAIN, COMMIT=$COMMIT PUSH=$PUSH" > "$REC"
A=$(git -C "$SRC" rev-parse --verify "$A^{commit}" 2>/dev/null) || fail "no commit $2 in $SRC"
A8=$(echo "$A" | cut -c1-8)

# 1. A is 2026.6's; no tag yet.
git -C "$SRC" show "$A:java/src/bergdb/core/BuildInfo.java" | grep -q "RELEASE = Util.identity(\"$V\")" \
    || fail "A's BuildInfo does not say $V"
git -C "$MAIN" rev-parse -q --verify "refs/tags/$TAG" > /dev/null && fail "the tag $TAG exists in $MAIN"

# 2. main and A.
br=$(git -C "$MAIN" symbolic-ref --short HEAD 2>/dev/null)
[ "$br" = main ] || fail "$MAIN is on '$br', not main"
git -C "$MAIN" fetch -q "$SRC" "$A" || fail "git fetch $SRC $A8"
[ "$(git -C "$MAIN" rev-parse FETCH_HEAD)" = "$A" ] || fail "FETCH_HEAD is not A"
H=$(git -C "$MAIN" rev-parse HEAD)
echo "A: $(git -C "$MAIN" log -1 --format='%H %ad %s' --date=format:'%F %T' "$A" | cut -c1-160)" >> "$REC"
echo "H: $(git -C "$MAIN" log -1 --format='%H %ad %s' --date=format:'%F %T' | cut -c1-160)" >> "$REC"

# 3. Fast-forward, or a merge.
if git -C "$MAIN" merge-base --is-ancestor "$H" "$A"; then
    mode=ff
    what="a fast-forward of main from $(echo "$H" | cut -c1-8) to A $A8"
else
    base=$(git -C "$MAIN" merge-base "$H" "$A")
    code=$(git -C "$MAIN" diff --name-only "$base" "$H" -- . ':(exclude)items' | head -n 5 | tr '\n' ' ')
    [ -z "$code" ] || fail "main moved outside items/ since A's base $(echo "$base" | cut -c1-8): $code(a look: not merged)"
    n=$(git -C "$MAIN" rev-list --count "$base..$H")
    mode=merge
    what="a merge of A $A8 into main $(echo "$H" | cut -c1-8) ($n items/ commits since A's base $(echo "$base" | cut -c1-8))"
fi
echo "mode: $mode: $what" >> "$REC"
if [ "$COMMIT" != 1 ]; then
    echo "TO MAIN READY (COMMIT=0): would make $what, then $( [ "$PUSH" = 1 ] && echo "git push $REMOTE main" || echo "no push (PUSH=0)"); $REC"
    exit 0
fi
if [ $mode = ff ]; then
    git -C "$MAIN" merge -q --ff-only "$A" || fail "git merge --ff-only in $MAIN (an uncommitted change of one of A's files?)"
else
    T=$R/merge
    rm -rf "$T"
    git clone -q "$MAIN" "$T" || fail "git clone $MAIN"
    git -C "$T" checkout -q main && [ "$(git -C "$T" rev-parse HEAD)" = "$H" ] || fail "the merge clone is not at H"
    git -C "$T" fetch -q "$SRC" "$A" || fail "git fetch in the merge clone"
    git -C "$T" -c user.name='Frans Lundberg' -c user.email=frans.lundberg@gmail.com merge -q --no-ff "$A" \
        -m "Release $V: merge the release's commit ($A8) into main (026-27)" \
        -m "The release's commit A is $(echo "$base" | cut -c1-8) with BuildInfo $V and releases/next.md completed, gated in a clone (026-27, step 11) and checked in its night (026-27, D4). Main had moved in items/ only since A's base." \
        || { git -C "$T" merge --abort 2>/dev/null; fail "the merge of A in $T: a conflict"; }
    MC=$(git -C "$T" rev-parse HEAD)
    [ "$(git -C "$MAIN" rev-parse HEAD)" = "$H" ] || fail "main's HEAD moved during the merge: run to-main.sh again"
    git -C "$MAIN" fetch -q "$T" main || fail "git fetch of the merge"
    git -C "$MAIN" merge -q --ff-only "$MC" || fail "git merge --ff-only of the merge in $MAIN (an uncommitted change of one of A's files?)"
    echo "merge commit: $MC" >> "$REC"
fi
NH=$(git -C "$MAIN" rev-parse HEAD)
git -C "$MAIN" merge-base --is-ancestor "$A" "$NH" || fail "A is not in main's history after the $mode"
echo "main: $NH" >> "$REC"

# 4. Push.
if [ "$PUSH" = 1 ]; then
    git -C "$MAIN" push -q "$REMOTE" main >> "$REC" 2>&1 || fail "git push $REMOTE main (main is $(echo "$NH" | cut -c1-8) locally; nothing forced)"
    rm=$(git -C "$MAIN" ls-remote "$REMOTE" refs/heads/main | cut -f1)
    [ "$rm" = "$NH" ] || fail "$REMOTE's main is $rm, not $NH, after the push"
    pushed="pushed to $REMOTE"
else
    pushed="not pushed (PUSH=0)"
fi
echo "TO MAIN OK: $NH" >> "$REC"
echo "TO MAIN OK: $what; main $(echo "$NH" | cut -c1-8); $pushed; $REC"
