#!/bin/sh
# Stages commit B's files in a clone of main after A (bergdb 034-01, step 10; 024-38's
# stage-b.sh, adapted for 2026.6 on 2026-11-23: no binaries in the repository; for every
# release on 2026-11-24), after build-a.sh, finish.sh and notes.sh. Called by release.sh, or:
#     sh stage-b.sh CLONE A
# The release V is what A's BuildInfo says (such as 2026.7); PREV, the release before it, is
# the newest releases/YYYY.N/ in CLONE before this one is made; NEXT is YYYY.(N+1)-dev with
# the int (YYYY - 2000) * 10 + N + 1, such as 2026.8-dev and 268 (BuildInfo's scheme; set NEXT
# and NEXTINT for another, such as after YYYY.9 or for a new year).
#   1. releases/V/ gets two files and no more: readme.md (the notes, R/out/readme.md, with
#      no [[ marker left) and SHA256SUMS (R/out's, two lines: bergdb-V.jar and
#      bergdb-V-javadoc.zip); the staged SHA256SUMS checks against R/out's two files
#      (shasum -a 256 -c there). The jar and the Javadoc zip go to the GitHub release, not
#      into the repository;
#   2. empties releases/next.md (its introduction kept, for the release after V: "after PREV"
#      becomes "after V");
#   3. README.md: the text of README.md after the release, a whole file that the lead or Frans
#      prepared (READMEMD), since its section on the latest release says how that release was
#      tested, which no script knows. The file must name "the latest release, V (DATE, tag
#      `release-V`)" and no longer "the latest release, PREV" (each with its lines joined).
#      Kept as it is if the clone's README.md says so already. Else it stops: STAGE B FAILED;
#   4. sets BuildInfo to NEXT and NEXTINT (set-buildinfo.sh, beside this script);
#   5. docs/log.md: the release's entry of DATE at the end (LOGENTRY, a file with the entry's
#      text, in its place if set; the default names the release item, commit A and where the
#      files are, not the release's theme).
# Stages and commits nothing: commit-b.sh does.
# Environment: DATE (today, the release's date); R (the release's work directory,
# /Users/f/fl/bench/DATE/release); NOTES (R/out/readme.md); READMEMD (none); LOGENTRY (none);
# NEXT and NEXTINT (from V).
# Prints "STAGE B OK: ..." or "STAGE B FAILED: ..." (exit 1).
# Created 2026-11-03 by Frans Lundberg (016-09); 2026.5's copy 2026-11-12; 2026.6's 2026-11-23;
# for every release 2026-11-24 (bergdb 034).
C=${1:?usage: sh stage-b.sh CLONE A}
A=${2:?usage: sh stage-b.sh CLONE A}
S=$(cd "$(dirname "$0")" && pwd)
DATE=${DATE:-$(date +%F)}
R=${R:-/Users/f/fl/bench/$DATE/release}
O=$R/out
NOTES=${NOTES:-$O/readme.md}
fail() { echo "STAGE B FAILED: $*"; exit 1; }
[ -d "$C/.git" ] || fail "$C is not a clone"
A=$(git -C "$C" rev-parse --verify "$A^{commit}" 2>/dev/null) || fail "no commit $A in $C"
git -C "$C" merge-base --is-ancestor "$A" HEAD || fail "A is not in $C's history (to-main.sh first)"
V=$(git -C "$C" show "$A:java/src/bergdb/core/BuildInfo.java" | sed -n 's/.*String RELEASE = Util\.identity("\([^"]*\)");.*/\1/p')
echo "$V" | grep -Eqx '[0-9]{4}\.[0-9]+' || fail "A's BuildInfo says '$V', not a release YYYY.N"
PREV=$(cd "$C/releases" && ls -d [0-9][0-9][0-9][0-9].[0-9]* 2>/dev/null | grep -Ex '[0-9]{4}\.[0-9]+' | grep -vx "$V" | sort -t. -k1,1n -k2,2n | tail -n 1)
[ -n "$PREV" ] || fail "no earlier release in $C/releases/"
y=${V%%.*}; n=${V#*.}
if [ -z "${NEXT:-}" ] || [ -z "${NEXTINT:-}" ]; then
    [ "$n" -lt 9 ] || fail "the release after $V: set NEXT and NEXTINT (BuildInfo's int scheme ends at YYYY.9)"
fi
NEXT=${NEXT:-$y.$((n + 1))-dev}
NEXTINT=${NEXTINT:-$(( (y - 2000) * 10 + n + 1 ))}
ITEM=$(cd "$C/items" 2>/dev/null && ls -d [0-9][0-9][0-9]-release-"$(echo "$V" | tr . -)" 2>/dev/null | head -n 1 | cut -c1-3)
D=$C/releases/$V
for f in "bergdb-$V.jar" "bergdb-$V-javadoc.zip" SHA256SUMS; do
    [ -f "$O/$f" ] || fail "no $O/$f (build-a.sh and finish.sh make them)"
done
[ -f "$NOTES" ] || fail "no $NOTES (notes.sh)"
m=$(grep -c '\[\[' "$NOTES")
[ "$m" = 0 ] || fail "$NOTES has $m lines with a [[ marker: $(grep -n '\[\[' "$NOTES" | head -n 3 | cut -c1-80 | tr '\n' ' ')"
latest="the latest release, $V ($DATE, tag \`release-$V\`)"
names() {    # names FILE TEXT: TEXT is in FILE, its lines joined
    tr '\n' ' ' < "$1" | tr -s ' ' | grep -q -F "$2"
}
if ! names "$C/README.md" "$latest"; then
    [ -n "${READMEMD:-}" ] || fail "README.md does not name $latest: prepare README.md for after the release and give it as READMEMD (its section on the latest release says how $V was tested)"
    [ -f "$READMEMD" ] || fail "no READMEMD $READMEMD"
    names "$READMEMD" "$latest" || fail "READMEMD $READMEMD does not name $latest"
fi
if [ -n "${READMEMD:-}" ]; then
    names "$READMEMD" "latest release, $PREV" && fail "READMEMD $READMEMD still names the latest release, $PREV"
fi
[ -e "$D" ] && fail "$D exists"
mkdir -p "$D" || fail "cannot make $D"
cp "$O/SHA256SUMS" "$D/SHA256SUMS" && cp "$NOTES" "$D/readme.md" || fail "cannot copy"
[ "$(wc -l < "$D/SHA256SUMS" | tr -d ' ')" = 2 ] || fail "SHA256SUMS has not two lines"
[ "$(awk '{print $2}' "$D/SHA256SUMS" | tr '\n' ' ')" = "bergdb-$V.jar bergdb-$V-javadoc.zip " ] || fail "SHA256SUMS does not list the jar and the Javadoc zip: $(cat "$D/SHA256SUMS" | tr '\n' ' ')"
c=$(cd "$O" && shasum -a 256 -c "$D/SHA256SUMS" 2>&1)
[ "$(echo "$c" | grep -c ': OK$')" = 2 ] || fail "shasum -c of the staged SHA256SUMS in $O: $c"
[ "$(ls -A "$D" | tr '\n' ' ')" = "SHA256SUMS readme.md " ] || fail "$D holds other files: $(ls -A "$D" | tr '\n' ' ')"
if [ -n "${READMEMD:-}" ]; then
    cp "$READMEMD" "$C/README.md" || fail "cannot copy READMEMD"
    rd="README.md from $READMEMD"
else
    rd="README.md names $V already"
fi
if [ -n "${LOGENTRY:-}" ]; then
    [ -f "$LOGENTRY" ] || fail "no LOGENTRY $LOGENTRY"
fi

A7=$(echo "$A" | cut -c1-7)
python3 -I - "$C" "$V" "$PREV" "$DATE" "$A7" "$NEXT" "${LOGENTRY:-}" "${ITEM:-}" <<'EOF' || fail "next.md or docs/log.md: not as expected (edit by hand)"
import re, sys, textwrap
def fill(t, indent=""):
    """Wraps at 76 columns without breaking a code span."""
    t = re.sub(r"`[^`]*`", lambda m: m.group(0).replace(" ", "\x00"), " ".join(t.split()))
    w = textwrap.fill(t, 76, initial_indent=indent, subsequent_indent="  " if indent else "", break_on_hyphens=False, break_long_words=False)
    return w.replace("\x00", " ")
c, v, prev, date, a7, nxt, logentry, item = sys.argv[1:]
# releases/next.md: the introduction kept, for the release after v; the notes gone.
p = c + "/releases/next.md"
s = open(p, encoding="utf-8").read()
title, rest = s.split("\n\n", 1)
intro = rest.split("\n\n\n", 1)[0]
intro = "\n\n".join(q for q in intro.split("\n\n") if not q.startswith("Emptied at release"))
if ("after " + prev) not in intro:
    sys.exit("next.md's introduction does not say 'after %s'" % prev)
intro = intro.replace("after " + prev, "after " + v).replace("[%s](%s/readme.md)" % (prev, prev), "[%s](%s/readme.md)" % (v, v))
open(p, "w", encoding="utf-8").write(title + "\n\n" + intro + "\n\nEmptied at release %s (%s), whose notes hold what was there.\n" % (v, date))
# docs/log.md: the release's entry, at the end.
p = c + "/docs/log.md"
s = open(p, encoding="utf-8").read().rstrip("\n")
if logentry:
    entry = open(logentry, encoding="utf-8").read().strip("\n")
else:
    planned = ("as planned in item %s (034-01)" % item) if item else "as 034-01 says"
    entry = fill((
        "%s. Release %s, %s: commit A, `%s`, where `BuildInfo` says %s. The release "
        "runs `night.sh`, `week.sh` and `timing.sh` passed on commits near A, and A's gate "
        "in a clone. The users' jar and the Pub API's Javadoc are on GitHub Releases, under "
        "the tag; `releases/%s/` holds the release notes and `SHA256SUMS`. Frans makes the "
        "tag `release-%s` on A. After it, `BuildInfo` says %s.") % (date, v, planned, a7, v, v, v, nxt))
open(p, "w", encoding="utf-8").write(s + "\n\n" + entry + "\n")
print("ok")
EOF
b=$(sh "$S/set-buildinfo.sh" "$C" "$NEXT" "$NEXTINT" | tail -n 1)
case $b in "BUILDINFO SET"*) ;; *) fail "set-buildinfo.sh: $b" ;; esac
st=$(git -C "$C" status --porcelain | tr '\n' ';' | tr -s ' ')
echo "STAGE B OK: $D has $(ls "$D" | wc -l | tr -d ' ') files ($(ls "$D" | tr '\n' ' ')); SHA256SUMS checks; next.md emptied; $rd; docs/log.md's entry; $b; git status: $st"
