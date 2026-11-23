#!/bin/sh
# Stages commit B's files in a clone of main after A (bergdb 026-27, step 13; 024-38's
# stage-b.sh, adapted 2026-11-23 for 2026.6: no binaries in the repository; 026, "How the
# release is made"), after build-a.sh, finish.sh and notes.sh. Called by release.sh, or:
#     sh stage-b.sh CLONE A
#   1. releases/2026.6/ gets two files and no more: readme.md (the notes, R/out/readme.md, with
#      no [[ marker left) and SHA256SUMS (R/out's, two lines: bergdb-2026.6.jar and
#      bergdb-2026.6-javadoc.zip); the staged SHA256SUMS checks against R/out's two files
#      (shasum -a 256 -c there). The jar and the Javadoc zip go to the GitHub release, not
#      into the repository;
#   2. empties releases/next.md (its introduction kept, for the release after 2026.6);
#   3. README.md: the text of README.md after the release, a whole file that the lead or Frans
#      prepared (READMEMD), since its section on the latest release says how that release was
#      tested, which no script knows. The file must name "the latest release, 2026.6 (DATE, tag
#      `release-2026.6`)" and no longer "the latest release, 2026.5" (each with its lines
#      joined). Kept as it is if the clone's README.md says so already. Else it stops: STAGE B
#      FAILED;
#   4. sets BuildInfo to 2026.7-dev and 267 (set-buildinfo.sh, beside this script);
#   5. docs/log.md: the release's entry of DATE at the end (LOGENTRY, a file with the entry's
#      text, in its place if set).
# Stages and commits nothing: commit-b.sh does.
# Environment: R (the release's work directory, /Users/f/fl/bench/2026-11-24/release); NOTES
# (R/out/readme.md); READMEMD (none); LOGENTRY (none); DATE (today, the release's date).
# Prints "STAGE B OK: ..." or "STAGE B FAILED: ..." (exit 1).
# Created 2026-11-03 by Frans Lundberg (016-09); 2026.5's copy 2026-11-12; 2026.6's 2026-11-23.
C=${1:?usage: sh stage-b.sh CLONE A}
A=${2:?usage: sh stage-b.sh CLONE A}
S=$(cd "$(dirname "$0")" && pwd)
R=${R:-/Users/f/fl/bench/2026-11-24/release}
O=$R/out
NOTES=${NOTES:-$O/readme.md}
DATE=${DATE:-$(date +%F)}
V=2026.6
PREV=2026.5
NEXT=2026.7-dev
NEXTINT=267
D=$C/releases/$V
fail() { echo "STAGE B FAILED: $*"; exit 1; }
[ -d "$C/.git" ] || fail "$C is not a clone"
A=$(git -C "$C" rev-parse --verify "$A^{commit}" 2>/dev/null) || fail "no commit $A in $C"
git -C "$C" merge-base --is-ancestor "$A" HEAD || fail "A is not in $C's history (to-main.sh first)"
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
python3 -I - "$C" "$V" "$PREV" "$DATE" "$A7" "$NEXT" "${LOGENTRY:-}" <<'EOF' || fail "next.md or docs/log.md: not as expected (edit by hand)"
import re, sys, textwrap
def fill(t, indent=""):
    """Wraps at 76 columns without breaking a code span."""
    t = re.sub(r"`[^`]*`", lambda m: m.group(0).replace(" ", "\x00"), " ".join(t.split()))
    w = textwrap.fill(t, 76, initial_indent=indent, subsequent_indent="  " if indent else "", break_on_hyphens=False, break_long_words=False)
    return w.replace("\x00", " ")
c, v, prev, date, a7, nxt, logentry = sys.argv[1:]
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
    entry = fill((
        "%s. Release %s, as planned in item 026 (026-27): commit A, `%s`, where "
        "`BuildInfo` says %s. Proven algorithms: BergDB's core algorithms are proved, "
        "given tested assumptions (030-26; the guarantees in 030-38). The release runs "
        "`night.sh`, `week.sh` and `timing.sh` passed on commits near A, and A's gate "
        "in a clone (026-27). Databases of %s and earlier are refused. The users' jar "
        "and the Pub API's Javadoc are on GitHub Releases, under the tag; "
        "`releases/%s/` holds the release notes and `SHA256SUMS`. Frans makes the tag "
        "`release-%s` on A. After it, `BuildInfo` says %s.") % (date, v, a7, v, prev, v, v, nxt))
open(p, "w", encoding="utf-8").write(s + "\n\n" + entry + "\n")
print("ok")
EOF
b=$(sh "$S/set-buildinfo.sh" "$C" "$NEXT" "$NEXTINT" | tail -n 1)
case $b in "BUILDINFO SET"*) ;; *) fail "set-buildinfo.sh: $b" ;; esac
st=$(git -C "$C" status --porcelain | tr '\n' ';' | tr -s ' ')
echo "STAGE B OK: $D has $(ls "$D" | wc -l | tr -d ' ') files ($(ls "$D" | tr '\n' ' ')); SHA256SUMS checks; next.md emptied; $rd; docs/log.md's entry; $b; git status: $st"
