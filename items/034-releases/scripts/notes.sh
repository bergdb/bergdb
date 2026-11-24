#!/bin/sh
# The release notes of 2026.6 (bergdb 026-27, step 13; in place of 024-38's notes.sh and
# notes.py, which filled a template from the release night's outputs: 2026.6's notes are
# releases/next.md, completed in 026-27's step 9). Called by release.sh after build-a.sh and
# finish.sh, or by hand:
#     sh notes.sh
# Writes R/out/readme.md: the title "BergDB 2026.6", the release's line (DATE, Frans Lundberg,
# item 026), "Files" (the two files on the GitHub release of the tag release-2026.6, each with
# its SHA-256; releases/2026.6/ holds the notes and SHA256SUMS; the source is the tag's
# archive), "Identity" (the tag, commit A and its date, BuildInfo's three lines, the JDK of the
# build), then "Changes": A's releases/next.md after its introduction, its ### sections as
# they are, relative links moved one directory down (next.md is in releases/, the notes in
# releases/2026.6/). A, BuildInfo, the JDK and the hashes come from build-a.sh's clone (R/a)
# and record (R/out/build-a.txt). A [[ marker that next.md still has is kept and counted:
# stage-b.sh refuses a marker. Frans reads the notes before commit B is pushed (026-27, step
# 13): release.sh stops after this script, and he may edit R/out/readme.md.
# Environment: R (the release's work directory, /Users/f/fl/bench/2026-11-24/release); DATE
# (today: the release's date); VERSION (2026.6).
# Prints "NOTES OK: ..." (exit 0), "NOTES NEED EDITS: N markers: ..." (exit 3) or
# "NOTES FAILED: ..." (exit 1). R/out/readme-generated.md keeps the script's own output.
# Created 2026-11-06 by Frans Lundberg; 2026.6's notes.sh 2026-11-23.
R=${R:-/Users/f/fl/bench/2026-11-24/release}
DATE=${DATE:-$(date +%F)}
V=${VERSION:-2026.6}
T=$R/a
O=$R/out
[ -d "$T/.git" ] || { echo "NOTES FAILED: no clone of A in $T (build-a.sh)"; exit 1; }
[ -f "$O/build-a.txt" ] && grep -q '^BUILD A OK' "$O/build-a.txt" || { echo "NOTES FAILED: no BUILD A OK in $O/build-a.txt"; exit 1; }
[ -f "$O/SHA256SUMS" ] || { echo "NOTES FAILED: no $O/SHA256SUMS (finish.sh)"; exit 1; }
C=$(git -C "$T" rev-parse HEAD)
CD=$(git -C "$T" log -1 --format=%cd --date=format:'%F %H:%M')
python3 -I - "$T/releases/next.md" "$O/build-a.txt" "$O/SHA256SUMS" "$V" "$DATE" "$C" "$CD" > "$O/readme.md" 2> "$O/notes.err" <<'EOF' || { echo "NOTES FAILED: $(tail -n 3 "$O/notes.err" | tr '\n' ' ')"; exit 1; }
import re, sys, textwrap
nextmd, rec, sums, v, date, commit, cdate = sys.argv[1:]
def fill(t, indent=""):
    """Wraps at 72 columns without breaking a code span or a link."""
    t = re.sub(r"`[^`]*`|<[^>]*>", lambda m: m.group(0).replace(" ", "\x00"), " ".join(t.split()))
    w = textwrap.fill(t, 72, initial_indent=indent, subsequent_indent="  " if indent else "",
                      break_on_hyphens=False, break_long_words=False)
    return w.replace("\x00", " ")
r = open(rec, encoding="utf-8").read()
build = re.search(r"^build: (\S+)$", r, re.M).group(1)
rint = re.search(r"^releaseInt: (\S+)$", r, re.M).group(1)
jdk = re.search(r"^jdk: (.*)$", r, re.M).group(1).strip()
m = re.search(r'"([^"]+)"', jdk)
jdk = "JDK " + m.group(1) if m else "`" + jdk + "`"
sha = {}
for line in open(sums, encoding="utf-8"):
    h, f = line.split()
    sha[f] = h
jar, jd = "bergdb-%s.jar" % v, "bergdb-%s-javadoc.zip" % v
tag = "release-" + v
s = open(nextmd, encoding="utf-8").read()
parts = s.split("\n\n\n", 1)
if len(parts) != 2 or not parts[1].strip():
    sys.exit("next.md has no sections after its introduction")
body = parts[1].strip("\n")
# Relative links: next.md is in releases/, the notes in releases/VERSION/.
body = re.sub(r"\]\((?!https?:|#|/|mailto:)([^)]+)\)", r"](../\1)", body)
title = "BergDB %s\n%s" % (v, "=" * len("BergDB " + v))
released = fill("Released %s by Frans Lundberg, as planned in bergdb item 026 "
                "([../../items/026-release-2026-6/readme.md](../../items/026-release-2026-6/readme.md))." % date)
where = fill("The files are on the GitHub release of the tag `%s`, "
             "<https://github.com/bergdb/bergdb/releases/tag/%s>:" % (tag, tag))
f1 = fill("`%s`: the users' jar, `java/build/bergdb-release.jar` made by `java/build.sh` "
          "from the release commit. SHA-256 `%s`." % (jar, sha[jar]), "* ")
f2 = fill("`%s`: the Pub API's Javadoc, made by `java/javadoc-pub.sh`, in the directory "
          "`bergdb-%s-javadoc/`. SHA-256 `%s`." % (jd, v, sha[jd]), "* ")
here = fill("`releases/%s/` in the repository holds these notes and `SHA256SUMS`; check the "
            "downloaded files with `shasum -a 256 -c SHA256SUMS`. The source is GitHub's "
            "archive of the tag." % v)
i1 = fill("Tag `%s`, commit `%s` (%s)." % (tag, commit, cdate), "* ")
i2 = fill("`BuildInfo`: release %s, release int %s, build %s; `java -cp %s "
          "bergdb.core.BuildInfo` prints them." % (v, rint, build, jar), "* ")
i3 = fill("Built by `java/build.sh` (`javac --release 17`) with %s, in a clean clone of the "
          "release commit." % jdk, "* ")
text = (title + "\n\n" + released + "\n\n\nFiles\n-----\n\n" + where + "\n\n" + f1 + "\n" + f2
        + "\n\n" + here + "\n\n\nIdentity\n--------\n\n" + i1 + "\n" + i2 + "\n" + i3
        + "\n\n\nChanges\n-------\n\n" + body)
print(text)
for i, line in enumerate(text.split("\n"), 1):
    if "[[" in line:
        print("MARKER %d: %s" % (i, line.strip()), file=sys.stderr)
EOF
cp "$O/readme.md" "$O/readme-generated.md"
n=$(grep -c '\[\[' "$O/readme.md")
if [ "$n" = 0 ]; then
    echo "NOTES OK: $O/readme.md, $(wc -l < "$O/readme.md" | tr -d ' ') lines, no marker; commit A $(echo "$C" | cut -c1-8)"
    exit 0
fi
echo "NOTES NEED EDITS: $n lines with a [[ marker in $O/readme.md: $(grep '^MARKER' "$O/notes.err" | cut -c8-120 | tr '\n' ';')"
exit 3
