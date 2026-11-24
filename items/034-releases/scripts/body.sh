#!/bin/sh
# The GitHub release's body (bergdb 034-01, steps 12 and 13, section 5; 028-49): the notes,
# releases/V/readme.md, with every relative link made absolute, since a relative link resolves
# against github.com/bergdb/bergdb/releases/ on the release's page and gives 404. Called by
# commit-b.sh after commit B, or by hand:
#     sh body.sh V                 makes BODY from MAIN's releases/V/readme.md
#     CHECK=1 sh body.sh V         the same, then every link of BODY must answer 200
#     sh body.sh test              the conversion's test (below); nothing else is written
# The body is the whole notes, their section "After the release" included (033, Rules, "Where
# they are published"). After the release, when an entry is added to that section and pushed,
# the body is made again with CHECK=1 and set with the command printed last:
#     cd MAIN && gh release edit release-V --notes-file BODY
# This script never pushes, tags or edits a GitHub release; it reads github.com only with
# CHECK=1 (curl -sIL, the status after the redirects).
#   1. Each relative link of the notes, an inline link [text](target), an image or a reference
#      definition [id]: target, outside code spans and fenced blocks, becomes
#      https://github.com/bergdb/bergdb/blob/main/P, P the path that the target resolves to
#      from releases/V/ (its #fragment kept; a bare #fragment is one of the notes' own); a
#      link text equal to its relative target becomes P, as on the page of release-2026.6
#      ("../../items/026-release-2026-6/readme.md" becomes "items/026-...") . Absolute links
#      (http:, https:, mailto:) and autolinks <...> stay. Nothing else of the text changes.
#   2. Refused (BODY FAILED): a target that leaves the repository, or whose path is not in
#      MAIN's tree (it would give 404 once public); a relative link left in BODY.
#   3. With CHECK=1: curl -sIL of every http(s) link of BODY, each once, the final status 200
#      (a second try after 5 s for one that does not). Run once the commit with the linked
#      files is on the public main (after commit B's push, or the push of an entry of "After
#      the release"); the release's own page, .../releases/tag/release-V, answers 200 once
#      the tag is pushed, before the GitHub release is made.
# The test (test): the notes of 2026.6 and 2026.5 in the repository that holds this script,
# each converted, then checked link by link against the notes, independently of the
# conversion's code: BODY has the same links in the same order; each was relative in the
# notes and is now https://github.com/bergdb/bergdb/blob/main/P with P the same file in the
# repository as the target from releases/V/ (os.path.samefile), or was absolute and is
# unchanged; its text is the notes' text, or P where the notes' text was the target; with
# every link cut out, the notes and BODY are the same text; no relative link is left.
# Environment: MAIN (/Users/f/fl/repos/bergdb, the repository of the notes); NOTES
# (MAIN/releases/V/readme.md); DATE (today); R (/Users/f/fl/bench/DATE/release); BODY
# (R/out/body-V.md); CHECK (0); REMOTE (origin, in the printed command only).
# Prints "BODY OK: ..." (exit 0) and the lines "BODY USE: ..." with the gh commands,
# "BODY TEST OK: ..." (exit 0), or "BODY FAILED: ..." / "BODY TEST FAILED: ..." (exit 1).
# Created 2026-11-24 by Frans Lundberg (bergdb 028-49).
S=$(cd "$(dirname "$0")" && pwd)
V=${1:?usage: sh body.sh V | sh body.sh test}
DATE=${DATE:-$(date +%F)}
R=${R:-/Users/f/fl/bench/$DATE/release}
CHECK=${CHECK:-0}
py() {     # py MODE ARGS...: the conversion and its test, in Python
    python3 -I - "$@" <<'EOF'
import os, posixpath, re, sys
BASE = "https://github.com/bergdb/bergdb/blob/main/"
# Fenced block, code span, inline link or image, reference definition, autolink: the first
# two are kept as they are; a link's text may span lines.
TOKEN = re.compile(r"(?ms)^ {0,3}```.*?^ {0,3}```[^\n]*$"
                   r"|`[^`]*`"
                   r"|(?P<img>!?)\[(?P<text>[^\]]*)\]\((?P<target>[^()\s]*)(?P<title>\s+\"[^\"]*\")?\)"
                   r"|^(?P<rpre> {0,3}\[[^\]]+\]:[ \t]*)(?P<rtarget>\S+)"
                   r"|<[a-zA-Z][a-zA-Z0-9+.-]*:[^>\s]*>")
def absolute(t):
    return re.match(r"(?i)(https?|mailto):", t) is not None
def links(text):
    """(start, end, text or None, target) of each link outside code."""
    out = []
    for m in TOKEN.finditer(text):
        if m.group("target") is not None:
            out.append((m.start(), m.end(), m.group("text"), m.group("target")))
        elif m.group("rtarget") is not None:
            out.append((m.start(), m.end(), None, m.group("rtarget")))
    return out
def resolve(t, notespath):
    """The repository path that a relative target resolves to, and its #fragment."""
    p, _, frag = t.partition("#")
    if p == "":
        p = notespath
    elif p.startswith("/"):
        p = p.lstrip("/")
    else:
        p = posixpath.normpath(posixpath.join(posixpath.dirname(notespath), p))
    if p == ".." or p.startswith("../"):
        raise ValueError("the target %s leaves the repository" % t)
    if t.split("#")[0].endswith("/") and not p.endswith("/"):
        p += "/"
    return p, ("#" + frag if frag else "")
def convert(text, notespath, repo):
    n = [0]
    def sub(m):
        if m.group("target") is not None:
            t = m.group("target")
            if absolute(t) or t == "":
                return m.group(0)
            p, frag = resolve(t, notespath)
            if repo and not os.path.exists(os.path.join(repo, p)):
                raise ValueError("the target %s (%s) is not in %s" % (t, p, repo))
            n[0] += 1
            txt = p if m.group("text") == t else m.group("text")
            return "%s[%s](%s%s%s%s)" % (m.group("img"), txt, BASE, p, frag, m.group("title") or "")
        if m.group("rtarget") is not None:
            t = m.group("rtarget")
            if absolute(t):
                return m.group(0)
            p, frag = resolve(t, notespath)
            if repo and not os.path.exists(os.path.join(repo, p)):
                raise ValueError("the target %s (%s) is not in %s" % (t, p, repo))
            n[0] += 1
            return m.group("rpre") + BASE + p + frag
        return m.group(0)
    return TOKEN.sub(sub, text), n[0]
CODE = re.compile(r"(?ms)^ {0,3}```.*?^ {0,3}```[^\n]*$|`[^`]*`")
def relative_left(text):
    """The relative targets left, and any "](" not followed by an absolute target, outside
    code (a link form that TOKEN does not parse)."""
    left = [t for (_, _, _, t) in links(text) if not absolute(t)]
    rest = CODE.sub("", text)
    return left + [m.group(0) for m in re.finditer(r"\]\(\s*(?!(?i:https?|mailto):)[^)\n]{0,40}", rest)]
def cut(text, ls):
    out, i = [], 0
    for (s, e, _, _) in ls:
        out.append(text[i:s]); out.append("\x00"); i = e
    out.append(text[i:])
    return "".join(out)
def test(repo, notespath, body):
    """Checks body against the notes link by link; returns a list of faults."""
    notes = open(os.path.join(repo, notespath), encoding="utf-8").read()
    ln, lb = links(notes), links(body)
    f = []
    if len(ln) != len(lb):
        return ["%d links in the notes, %d in the body" % (len(ln), len(lb))]
    d = os.path.dirname(os.path.join(repo, notespath))
    for (_, _, nt, ng), (_, _, bt, bg) in zip(ln, lb):
        if absolute(ng):
            if bg != ng: f.append("absolute %s became %s" % (ng, bg))
            if bt != nt: f.append("the text of %s changed" % ng)
            continue
        if not bg.startswith(BASE):
            f.append("%s became %s" % (ng, bg)); continue
        p = bg[len(BASE):].split("#")[0]
        np = ng.split("#")[0]
        a = os.path.join(repo, p)
        b = os.path.join(d, np) if np else os.path.join(repo, notespath)
        if not (os.path.exists(a) and os.path.exists(b) and os.path.samefile(a, b)):
            f.append("%s became %s, not the same file" % (ng, bg))
        if ng.partition("#")[2] != bg.partition("#")[2]:
            f.append("the fragment of %s changed in %s" % (ng, bg))
        want = p if nt == ng else nt
        if bt != want: f.append("the text [%s] became [%s], not [%s]" % (nt, bt, want))
    if cut(notes, ln) != cut(body, lb):
        f.append("the text outside the links differs")
    left = relative_left(body)
    if left: f.append("relative links left: %s" % " ".join(left[:5]))
    return f
mode = sys.argv[1]
if mode == "make":
    notes, notespath, repo, out = sys.argv[2:]
    text = open(notes, encoding="utf-8").read()
    try:
        body, n = convert(text, notespath, repo)
    except ValueError as e:
        sys.exit(str(e))
    left = relative_left(body)
    if left:
        sys.exit("relative links left: %s" % " ".join(left[:5]))
    open(out, "w", encoding="utf-8").write(body)
    urls = []
    for (_, _, _, t) in links(body):
        if re.match(r"(?i)https?:", t) and t not in urls: urls.append(t)
    for u in re.findall(r"<(https?:[^>\s]*)>", body):
        if u not in urls: urls.append(u)
    print("%d %d" % (n, len(links(body))))
    print("\n".join(urls))
else:
    repo = sys.argv[2]
    faults, done = [], []
    for v in sys.argv[3:]:
        notespath = "releases/%s/readme.md" % v
        text = open(os.path.join(repo, notespath), encoding="utf-8").read()
        body, n = convert(text, notespath, repo)
        fs = test(repo, notespath, body)
        faults += ["%s: %s" % (v, x) for x in fs]
        done.append("%s %d of %d links made absolute" % (v, n, len(links(body))))
    if faults:
        sys.exit("; ".join(faults[:8]))
    print(", ".join(done))
EOF
}

if [ "$V" = test ]; then
    repo=$(cd "$S/../../.." && pwd)
    r=$(py test "$repo" 2026.6 2026.5 2>&1) || { echo "BODY TEST FAILED: $(echo "$r" | tail -n 3 | tr '\n' ' ')"; exit 1; }
    echo "BODY TEST OK: $r; no relative link left, the text otherwise the same ($repo)"
    exit 0
fi

MAIN=${MAIN:-/Users/f/fl/repos/bergdb}
NOTES=${NOTES:-$MAIN/releases/$V/readme.md}
BODY=${BODY:-$R/out/body-$V.md}
REMOTE=${REMOTE:-origin}
fail() { echo "BODY FAILED: $*"; exit 1; }
echo "$V" | grep -Eqx '[0-9]{4}\.[0-9]+' || fail "'$V' is not a release YYYY.N"
[ -f "$NOTES" ] || fail "no notes $NOTES"
grep -q '\[\[' "$NOTES" && fail "$NOTES has a [[ marker"
mkdir -p "$(dirname "$BODY")" || fail "cannot make $(dirname "$BODY")"
r=$(py make "$NOTES" "releases/$V/readme.md" "$MAIN" "$BODY" 2>&1) || fail "$(echo "$r" | tail -n 2 | tr '\n' ' ')"
n=$(echo "$r" | head -n 1)
urls=$(echo "$r" | sed 1d)
msg="$BODY from $NOTES, ${n%% *} relative links made absolute, ${n#* } links in all, no relative link left"
if [ "$CHECK" = 1 ]; then
    k=0
    for u in $urls; do
        c=$(curl -sIL -o /dev/null -w '%{http_code}' --max-time 30 "$u")
        if [ "$c" != 200 ]; then
            sleep 5
            c=$(curl -sIL -o /dev/null -w '%{http_code}' --max-time 30 "$u")
        fi
        [ "$c" = 200 ] || fail "$u answers $c (the commit with the linked files on the public main? the tag pushed?); $msg"
        k=$((k + 1))
    done
    msg="$msg; all $k distinct http(s) links answer 200 (curl -sIL)"
else
    msg="$msg; links not checked (CHECK=1 checks them once the notes' commit is on the public main)"
fi
echo "BODY OK: $msg"
echo "BODY USE: the GitHub release made with it: gh release create release-$V ... --notes-file $BODY (commit-b.sh prints the whole command)"
echo "BODY USE: a release already made, its body set again (034-01, section 5): cd $MAIN && gh release edit release-$V --notes-file $BODY"
