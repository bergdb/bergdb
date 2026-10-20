#!/bin/sh
# 005-10: makes the removal in a fresh clone, step by step.
#
# Usage: make-patch.sh <bergdb repo> <work dir> <plan dir> <proguard.jar>
#
# The plan dir holds (all optional but delete-files.txt):
#   delete-files.txt   files to delete (group headers "# A1." and so on)
#   edits-*.py         exact replacements (edit.py), made after the deletions
#   add/               files to add, by their path in the repo
#   config.txt         the set of entry points of the member pass (members.py):
#                      keep (the proposal's) or all (every main and test group)
#   skip-files.txt     path prefixes whose unused members stay (kept groups)
#   lean-remove.txt    Lean declarations to remove
#   api-remove.txt     public API members to remove (G1), stage 2
#   api-edits-*.py     replacements made with them, stage 2
#   api-delete-files.txt  API files to delete once nothing refers to them
#
# Stage 1: clone <repo> (HEAD only) into <work dir>/patch, delete, edit,
# add, then repeat until a round removes nothing: java-analysis.sh,
# members.py, remove.py; then the Lean declarations. Committed in the clone
# as "stage 1". Stage 2, if api-remove.txt is there: the API members, their
# edits, the member rounds again (what only they used), and the API files;
# committed as "stage 2". Last, java/build.sh and lake build.
# The patch is `git diff origin/HEAD` in the clone; stage 2 alone is
# `git diff HEAD~1`.

set -e
REPO=$1
WORK=$2
PLAN=$3
PROGUARD=$4
TOOLS=$(cd "$(dirname "$0")" && pwd)
P=$WORK/patch
OUT=$WORK/out-patch
CONFIG=$(cat "$PLAN/config.txt" 2>/dev/null || echo keep)
SKIP=
if [ -f "$PLAN/skip-files.txt" ]; then SKIP=$PLAN/skip-files.txt; fi
JAVA=${JAVA_HOME:+$JAVA_HOME/bin/}java

rm -rf "$P" "$OUT"
mkdir -p "$OUT"
git clone -q "$REPO" "$P"
if [ -d "$REPO/lean/.lake" ]; then cp -R "$REPO/lean/.lake" "$P/lean/"; fi

cd "$P"
git config user.name "005-10 scratch"
git config user.email "scratch@localhost"
grep -v '^#' "$PLAN/delete-files.txt" | sed '/^$/d' | xargs git rm -q
for e in "$PLAN"/edits-*.py; do
    if [ -f "$e" ]; then python3 -I "$TOOLS/edit.py" "$P" "$e"; fi
done
if [ -d "$PLAN/add" ]; then cp -R "$PLAN/add/." "$P/"; fi

# Removing members can leave others unused (an MBean interface whose class
# went): repeat until a round removes nothing.
rounds() {
    for round in 1 2 3 4 5; do
        O=$OUT/$1-round$round
        sh "$TOOLS/java-analysis.sh" "$P" "$O" "$PROGUARD" > "$O.txt"
        python3 -I "$TOOLS/members.py" "$P" "$O/c" "$O/idx" "$CONFIG" "$O/members.tsv" $SKIP \
            > "$O/members.txt"
        if ! grep -q '^remove' "$O/members.tsv"; then break; fi
        python3 -I "$TOOLS/remove.py" "$P" "$O/idx/decls.tsv" "$O/members.tsv" > "$O/remove.txt"
    done
}

rounds stage1
if [ -f "$PLAN/lean-remove.txt" ]; then
    (cd "$P/lean" && lake build > "$OUT/lake-before.txt" 2>&1)
    python3 -I "$TOOLS/lean_remove.py" "$P" "$PLAN/lean-remove.txt" > "$OUT/lean-remove.txt"
fi
git add -A
git commit -qm "stage 1"

if [ -f "$PLAN/api-remove.txt" ]; then
    O=$OUT/stage2-api
    mkdir -p "$O"
    (cd "$P/java" && ./build.sh > "$O/build.txt" 2>&1)
    "$JAVA" -Xmx4g "$TOOLS/Index.java" "$O" "$P/java/in/icu-for-bergdb.jar" \
        "$P/java/src" "$P/java/src-dev" "$P/java/src-icu" "$P/java/stress" \
        > "$O/index.txt" 2> "$O/index-warnings.txt"
    python3 -I "$TOOLS/api_remove.py" "$P" "$O/decls.tsv" "$PLAN/api-remove.txt" "$O/members.tsv"
    python3 -I "$TOOLS/remove.py" "$P" "$O/decls.tsv" "$O/members.tsv" > "$O/remove.txt"
    for e in "$PLAN"/api-edits-*.py; do
        if [ -f "$e" ]; then python3 -I "$TOOLS/edit.py" "$P" "$e"; fi
    done
    rounds stage2
    if [ -f "$PLAN/api-delete-files.txt" ]; then
        grep -v '^#' "$PLAN/api-delete-files.txt" | sed '/^$/d' | xargs git rm -q
    fi
    git add -A
    git commit -qm "stage 2"
fi

(cd "$P/java" && ./build.sh > "$OUT/build-after.txt" 2>&1)
(cd "$P/lean" && lake build > "$OUT/lake-after.txt" 2>&1)
git diff --stat origin/HEAD | tail -1
