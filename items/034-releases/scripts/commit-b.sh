#!/bin/sh
# Commit B and the push of main (bergdb 026-27, step 13; 024-38's commit-b.sh, adapted
# 2026-11-23 for 2026.6: no binaries in the repository, the GitHub release's command printed;
# 026, "How the release is made"), after to-main.sh (A in main) and stage-b.sh in CLONE, a
# clone of main made after A. Called by release.sh, or:
#     COMMIT=1 sh commit-b.sh CLONE A
# It makes NO tag, pushes no tag and makes no GitHub release: Frans does (026-27, steps 14 and
# 15); it prints his commands last.
#   1. CLONE's base is MAIN's HEAD (on main) and A is in its history; A's BuildInfo says 2026.6;
#      the tag release-2026.6 does not exist; the changes are only B's paths: releases/2026.6/,
#      releases/next.md, README.md, BuildInfo.java, docs/log.md; releases/2026.6/ holds
#      readme.md and SHA256SUMS and nothing else, and SHA256SUMS checks against R/out's jar
#      and Javadoc zip, the files for the GitHub release; BuildInfo says 2026.7-dev;
#   2. java/before-commit.sh in CLONE: BEFORE COMMIT OK (about 2 minutes; functional, it may
#      run beside other work);
#   3. the commit in CLONE, in Frans's name: "Release 2026.6: releases/2026.6/ (the notes and
#      SHA256SUMS); BuildInfo says 2026.7-dev";
#   4. with COMMIT=1 only: MAIN's HEAD is still the base; git fetch and git merge --ff-only in
#      MAIN (other sessions' uncommitted files stay; the merge refuses if one of B's files has
#      an uncommitted change in MAIN);
#   5. with COMMIT=1 and PUSH=1 (the default): git push REMOTE main (never a force, no tag),
#      and git ls-remote shows main at B;
#   6. prints, for Frans ("FOR FRANS:" lines), in this order: the tag on A and its push; the
#      GitHub release with the two files (026, "How the release is made"); the check of the
#      files downloaded from the release against SHA256SUMS:
#        git -C MAIN tag -a release-2026.6 A -m "BergDB 2026.6, DATE"
#        git -C MAIN push REMOTE release-2026.6
#        cd MAIN && gh release create release-2026.6 --verify-tag --title "BergDB 2026.6" \
#            --notes-file releases/2026.6/readme.md R/out/bergdb-2026.6.jar R/out/bergdb-2026.6-javadoc.zip
#        cd MAIN && ... gh release download release-2026.6 -D R/download ... shasum -a 256 -c SHA256SUMS
# Environment: COMMIT (0); PUSH (1); MAIN (/Users/f/fl/repos/bergdb); REMOTE (origin); R (the
# release's work directory, /Users/f/fl/bench/2026-11-24/release); DATE (today, the tag
# message's date); NOGATE=1 (the smoke test only: no before-commit.sh).
# Prints "COMMIT B OK: ..." (exit 0), "COMMIT B READY (not committed, COMMIT=0): ..." or
# "COMMIT B FAILED: ..." (exit 1), then (OK only) the "FOR FRANS:" lines. The record:
# R/out/commit-b.txt, the gate's output R/out/commit-b-gate.txt.
# Created 2026-11-06 by Frans Lundberg; 2026.5's copy 2026-11-12; 2026.6's 2026-11-23.
C=${1:?usage: commit-b.sh CLONE A}
A=${2:?usage: commit-b.sh CLONE A}
MAIN=${MAIN:-/Users/f/fl/repos/bergdb}
R=${R:-/Users/f/fl/bench/2026-11-24/release}
COMMIT=${COMMIT:-0}
PUSH=${PUSH:-1}
REMOTE=${REMOTE:-origin}
DATE=${DATE:-$(date +%F)}
V=2026.6
NEXT=2026.7-dev
TAG=release-$V
O=$R/out
REC=$O/commit-b.txt
export JAVA_HOME=${JAVA_HOME:-/opt/homebrew/opt/openjdk}
export PATH=$JAVA_HOME/bin:$PATH
mkdir -p "$O"
fail() { echo "FAILED: $*" >> "$REC"; echo "COMMIT B FAILED: $*"; exit 1; }
echo "commit-b.sh $C $A, $(date '+%F %T'), MAIN $MAIN, COMMIT=$COMMIT PUSH=$PUSH" > "$REC"
br=$(git -C "$MAIN" symbolic-ref --short HEAD 2>/dev/null)
[ "$br" = main ] || fail "$MAIN is on '$br', not main"
A=$(git -C "$MAIN" rev-parse --verify "$A^{commit}") || fail "no commit $A in $MAIN"
git -C "$MAIN" show "$A:java/src/bergdb/core/BuildInfo.java" | grep -q "RELEASE = Util.identity(\"$V\")" || fail "A's BuildInfo does not say $V"
git -C "$MAIN" rev-parse -q --verify "refs/tags/$TAG" > /dev/null && fail "the tag $TAG exists"
H=$(git -C "$MAIN" rev-parse HEAD)
base=$(git -C "$C" rev-parse HEAD)
[ "$base" = "$H" ] || fail "CLONE's HEAD ($(echo "$base" | cut -c1-8)) is not MAIN's ($(echo "$H" | cut -c1-8)): make the clone again"
git -C "$MAIN" merge-base --is-ancestor "$A" "$H" || fail "A is not in main's history (to-main.sh first)"
git -C "$C" add -A releases/$V releases/next.md README.md java/src/bergdb/core/BuildInfo.java docs/log.md \
    || fail "git add in CLONE"
other=$(git -C "$C" status --porcelain | grep -v '^[AM]  ')
[ -z "$other" ] || fail "CLONE has other changes than B's paths: $(echo "$other" | head -n 5 | tr '\n' ';')"
staged=$(git -C "$C" diff --cached --name-only | tr '\n' ' ')
echo "staged: $staged" >> "$REC"
inrel=$(git -C "$C" diff --cached --name-only -- "releases/$V" | tr '\n' ' ')
[ "$inrel" = "releases/$V/SHA256SUMS releases/$V/readme.md " ] || fail "releases/$V/ is not readme.md and SHA256SUMS: $inrel"
[ "$(ls -A "$C/releases/$V" | tr '\n' ' ')" = "SHA256SUMS readme.md " ] || fail "releases/$V/ holds other files: $(ls -A "$C/releases/$V" | tr '\n' ' ')"
for f in "bergdb-$V.jar" "bergdb-$V-javadoc.zip"; do
    [ -f "$O/$f" ] || fail "no $O/$f, the file for the GitHub release"
done
[ "$(wc -l < "$C/releases/$V/SHA256SUMS" | tr -d ' ')" = 2 ] || fail "SHA256SUMS has not two lines"
(cd "$O" && shasum -a 256 -c -s "$C/releases/$V/SHA256SUMS") || fail "releases/$V/SHA256SUMS does not check against $O's files"
grep -q '\[\[' "$C/releases/$V/readme.md" && fail "releases/$V/readme.md has a [[ marker"
git -C "$C" show ":java/src/bergdb/core/BuildInfo.java" | grep -q "RELEASE = Util.identity(\"$NEXT\")" || fail "BuildInfo is not $NEXT"
if [ "${NOGATE:-0}" = 1 ]; then
    g="gate skipped (NOGATE=1, the smoke test)"
else
    echo "$(date '+%T') before-commit.sh" >> "$REC"
    (cd "$C/java" && sh before-commit.sh) > "$O/commit-b-gate.txt" 2>&1
    g=$(grep '^BEFORE COMMIT' "$O/commit-b-gate.txt" | tail -n 1)
    case $g in "BEFORE COMMIT OK"*) ;; *) fail "before-commit.sh: ${g:-$(tail -n 2 "$O/commit-b-gate.txt" | tr '\n' ' ')}" ;; esac
fi
echo "$(date '+%T') gate: $g" >> "$REC"
As=$(echo "$A" | cut -c1-8)
git -C "$C" -c user.name='Frans Lundberg' -c user.email=frans.lundberg@gmail.com commit -q \
    -m "Release $V: releases/$V/ (the notes and SHA256SUMS); BuildInfo says $NEXT" \
    -m "Commit B of the release (026-27, step 13). releases/$V/ holds the release notes and SHA256SUMS of the two files of the GitHub release, bergdb-$V.jar (the users' jar) and bergdb-$V-javadoc.zip, built from commit A ($As); no binaries in the repository (026, How the release is made). next.md emptied into the notes; README.md's latest release; docs/log.md's entry. BuildInfo: $NEXT. The tag $TAG, made by Frans, names A.
Gate in a clone: $g." || fail "commit in CLONE"
B=$(git -C "$C" rev-parse HEAD)
echo "B (in CLONE): $B" >> "$REC"
if [ "$COMMIT" != 1 ]; then
    echo "COMMIT B READY (not committed, COMMIT=0): $(echo "$B" | cut -c1-8) on $(echo "$H" | cut -c1-8); $g; Frans's tag $TAG on $As after it; $REC"
    exit 0
fi
[ "$(git -C "$MAIN" rev-parse HEAD)" = "$H" ] || fail "main's HEAD moved during the gate: make the clone again"
git -C "$MAIN" fetch -q "$C" HEAD || fail "git fetch from CLONE"
git -C "$MAIN" merge -q --ff-only FETCH_HEAD || fail "git merge --ff-only in $MAIN (an uncommitted change of one of B's files in main?)"
[ "$(git -C "$MAIN" rev-parse HEAD)" = "$B" ] || fail "main's HEAD is not B after the merge"
echo "COMMIT B OK: $B on main; no tag (Frans makes $TAG on $A)" >> "$REC"
if [ "$PUSH" = 1 ]; then
    git -C "$MAIN" push -q "$REMOTE" main >> "$REC" 2>&1 || fail "git push $REMOTE main (B is made locally; nothing forced)"
    rm=$(git -C "$MAIN" ls-remote "$REMOTE" refs/heads/main | cut -f1)
    [ "$rm" = "$B" ] || fail "after the push, $REMOTE has main $rm, not B"
    pushed="pushed: $REMOTE has main at B"
else
    pushed="not pushed (PUSH=0)"
fi
git -C "$MAIN" rev-parse -q --verify "refs/tags/$TAG" > /dev/null && fail "the tag $TAG exists now (made by someone else during the run)"
DL=$R/download
echo "COMMIT B OK: B $(echo "$B" | cut -c1-8) on main; $g; $pushed; no tag made, no GitHub release made"
echo "FOR FRANS: the tag, on A $As (BuildInfo $V), then its push:"
echo "FOR FRANS:   git -C $MAIN tag -a $TAG $A -m \"BergDB $V, $DATE\""
echo "FOR FRANS:   git -C $MAIN push $REMOTE $TAG"
echo "FOR FRANS: then the GitHub release with the two files:"
echo "FOR FRANS:   cd $MAIN && gh release create $TAG --verify-tag --title \"BergDB $V\" --notes-file releases/$V/readme.md $O/bergdb-$V.jar $O/bergdb-$V-javadoc.zip"
echo "FOR FRANS: then the check of the files as published:"
echo "FOR FRANS:   cd $MAIN && rm -rf $DL && mkdir -p $DL && gh release download $TAG -D $DL && cp releases/$V/SHA256SUMS $DL/ && (cd $DL && shasum -a 256 -c SHA256SUMS)"
