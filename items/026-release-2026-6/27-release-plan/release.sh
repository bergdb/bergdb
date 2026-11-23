#!/bin/sh
# Release 2026.6's files, commit B and the push of main (bergdb 026-27, step 13; 024-38's
# release.sh, adapted 2026-11-23 for 2026.6: 026, "How the release is made"), after
# to-main.sh (A in main, pushed). Run by the lead or Frans, from any directory, in two calls,
# since Frans reads the notes before commit B is pushed (they are public at once):
#     sh release.sh A                         steps 1 to 4; stops at RELEASE WAITS
#     FROM=stage COMMIT=1 sh release.sh A     steps 1, 5 and 6, after the notes are read
# It makes NO tag, pushes no tag and makes no GitHub release: it prints last, for Frans, the
# commands of the tag release-2026.6 on A and its push, of the GitHub release with the jar
# and the Javadoc zip, and of the check of the published files against SHA256SUMS. The steps,
# each stopping the script when it does not print its OK line:
#   1. A is in MAIN's history and its BuildInfo says 2026.6; the tag does not exist; README.md
#      for after the release is ready (MAIN's README.md names the latest release 2026.6 of
#      DATE, or READMEMD does: stage-b.sh, step 3), so that a missing text stops it before
#      the build;
#   2. build-a.sh A: a new clone of MAIN at A in R/a; the jar and the Javadoc zip in R/out
#      (BUILD A OK);
#   3. finish.sh: R/out/SHA256SUMS of the two files; baseline.zip if R/out/baseline/ exists
#      (FINISH OK);
#   4. notes.sh: R/out/readme.md from A's releases/next.md (NOTES OK, or NOTES NEED EDITS).
#      Then it stops, always: "RELEASE WAITS": read R/out/readme.md, edit it there if needed
#      (each [[ marker must go), then the second call;
#   5. (FROM=stage) a new clone of MAIN in R/B, stage-b.sh there (STAGE B OK):
#      releases/2026.6/ with readme.md and SHA256SUMS only, next.md emptied, README.md,
#      docs/log.md's entry, BuildInfo 2026.7-dev;
#   6. commit-b.sh R/B A: the gate (before-commit.sh, about 2 minutes), commit B, main
#      fast-forwarded, and with PUSH=1 git push origin main; no tag.
# Without COMMIT=1, step 6 stops before main changes (COMMIT B READY).
# Environment: COMMIT (0); PUSH (1); FROM (empty, or "stage"); MAIN (/Users/f/fl/repos/bergdb);
# REMOTE (origin); R (the release's work directory, /Users/f/fl/bench/2026-11-24/release);
# DATE (today: the release's date in the notes, README.md, docs/log.md and the tag's
# message; the same in both calls); READMEMD and LOGENTRY (stage-b.sh); NOGATE=1 (the smoke
# test only).
# Prints each step's line, then "RELEASE OK: ..." (exit 0) followed by the "FOR FRANS:" lines,
# "RELEASE READY (COMMIT=0): ..." (exit 0), "RELEASE WAITS: ..." (exit 3: read the notes) or
# "RELEASE FAILED: ..." (exit 1). A failed step's last lines: R/out/release-STEP.txt.
# Created 2026-11-10 by Frans Lundberg; 2026.5's copy 2026-11-12; 2026.6's 2026-11-23.
A=${1:?usage: sh release.sh A}
S=$(cd "$(dirname "$0")" && pwd)
V=2026.6
TAG=release-$V
R=${R:-/Users/f/fl/bench/2026-11-24/release}
MAIN=${MAIN:-/Users/f/fl/repos/bergdb}
COMMIT=${COMMIT:-0}
PUSH=${PUSH:-1}
FROM=${FROM:-}
DATE=${DATE:-$(date +%F)}
export R MAIN COMMIT PUSH DATE
fail() { echo "RELEASE FAILED: $*"; exit 1; }
step() {     # step NAME OKPATTERN COMMAND...: runs it, prints its last line, stops unless it matches
    nm=$1; ok=$2; shift 2
    out=$("$@" 2>&1); l=$(echo "$out" | tail -n 1)
    echo "$nm: $l"
    case $l in $ok*) ;; *) echo "$out" | tail -n 15 > "$R/out/release-$nm.txt"; fail "$nm: $l" ;; esac
}
mkdir -p "$R/out" || fail "cannot make $R/out"
A=$(git -C "$MAIN" rev-parse --verify "$A^{commit}" 2>/dev/null) || fail "no commit $1 in $MAIN (to-main.sh first)"
echo "release.sh, $(date '+%F %T'), A $(echo "$A" | cut -c1-8), MAIN $MAIN, R $R, DATE $DATE, COMMIT=$COMMIT PUSH=$PUSH FROM=${FROM:-start}"

# 1. A, the tag, README.md.
git -C "$MAIN" merge-base --is-ancestor "$A" HEAD || fail "A is not in $MAIN's main (to-main.sh first)"
git -C "$MAIN" show "$A:java/src/bergdb/core/BuildInfo.java" | grep -q "RELEASE = Util.identity(\"$V\")" || fail "A's BuildInfo does not say $V"
git -C "$MAIN" rev-parse -q --verify "refs/tags/$TAG" > /dev/null && fail "the tag $TAG exists"
latest="the latest release, $V ($DATE, tag \`release-$V\`)"
names() { tr '\n' ' ' < "$1" | tr -s ' ' | grep -q -F "$2"; }
if ! names "$MAIN/README.md" "$latest"; then
    [ -n "${READMEMD:-}" ] && [ -f "$READMEMD" ] && names "$READMEMD" "$latest" \
        || fail "README.md for after the release: neither $MAIN/README.md nor READMEMD (${READMEMD:-not set}) names $latest (stage-b.sh, step 3)"
fi

if [ "$FROM" != stage ]; then
    # 2 to 4.
    step build-a "BUILD A OK" env SRC="$MAIN" sh "$S/build-a.sh" "$A"
    step finish "FINISH OK" sh "$S/finish.sh"
    n=$(sh "$S/notes.sh" 2>&1 | tail -n 1)
    echo "notes: $n"
    case $n in
        "NOTES OK"*) why="read the notes, $R/out/readme.md (edit them there if needed)" ;;
        "NOTES NEED EDITS"*) why="edit the notes, $R/out/readme.md, at each [[ marker ($R/out/notes.err lists them), and read them" ;;
        *) fail "notes: $n" ;;
    esac
    more="${READMEMD:+READMEMD=$READMEMD }${LOGENTRY:+LOGENTRY=$LOGENTRY }"
    echo "RELEASE WAITS: $why; then: FROM=stage COMMIT=1 DATE=$DATE $more""sh $S/release.sh $A"
    exit 3
fi

# 5 and 6.
grep -q "^commit: $A " "$R/out/build-a.txt" 2>/dev/null && grep -q '^BUILD A OK' "$R/out/build-a.txt" \
    || fail "$R/out/build-a.txt is not BUILD A OK of A: run release.sh without FROM first"
rm -rf "$R/B"
git clone -q "$MAIN" "$R/B" || fail "git clone $MAIN $R/B"
step stage-b "STAGE B OK" sh "$S/stage-b.sh" "$R/B" "$A"
out=$(sh "$S/commit-b.sh" "$R/B" "$A" 2>&1)
b=$(echo "$out" | grep -E '^COMMIT B ' | tail -n 1)
echo "commit-b: $b"
case $b in
    "COMMIT B OK"*) echo "RELEASE OK: release $V's files and commit B: $(echo "$b" | cut -c14-)"
                    echo "$out" | grep '^FOR FRANS:' ;;
    "COMMIT B READY"*) echo "RELEASE READY (COMMIT=0): $b" ;;
    *) fail "commit-b: ${b:-$(echo "$out" | tail -n 1)}" ;;
esac
