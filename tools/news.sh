#!/bin/sh
# Adds an entry to news.md, Frans's morning news of BergDB's background work (night.sh,
# scheduled runs, unattended sessions; AGENTS.md, "News"). Written 2026-10-26.
#
# Usage: tools/news.sh STATUS SOURCE TEXT
#   STATUS  OK, FAILED or "needs a look".
#   SOURCE  who reports: night.sh, a script, a session, an item ("009-04 soaks").
#   TEXT    one or two lines: what happened, and a reference (an item such as 012-03, a
#           file, a commit). The details belong in the item, not here.
#
# The file is news.md in the main working tree of this repository (from a linked worktree
# too), or $NEWS_FILE; it is not tracked by Git. Newest entry first. Each call also prunes:
# OK entries older than the 3 weekdays before today go; FAILED and "needs a look" stay
# until Frans deletes them. A lock (news.md.lock, a directory) keeps writers apart.
[ $# = 3 ] || { echo "usage: tools/news.sh STATUS SOURCE TEXT" >&2; exit 2; }
if [ -z "$NEWS_FILE" ]; then
    common=$(git -C "$(dirname "$0")" rev-parse --path-format=absolute --git-common-dir) || exit 1
    NEWS_FILE=$(dirname "$common")/news.md
fi
LOCK=$NEWS_FILE.lock
n=0
until mkdir "$LOCK" 2>/dev/null; do
    n=$((n + 1))
    [ $n -lt 60 ] || { echo "news.sh: $LOCK held for a minute; remove it if stale" >&2; exit 1; }
    sleep 1
done
trap 'rmdir "$LOCK"' EXIT
python3 - "$NEWS_FILE" "$1" "$2" "$3" <<'PYEOF'
import datetime, os, re, sys
path, status, source, text = sys.argv[1:5]
HEADER = """News
====

BergDB's background work for Frans: night.sh, scheduled runs, unattended
sessions. Newest first; one entry per thing that finished, failed or needs a
look, with a reference to where the details are. Written by tools/news.sh,
which drops OK entries older than the 3 weekdays before today; FAILED and
"needs a look" stay until deleted. Not tracked by Git.
"""
now = datetime.datetime.now()
entries = []
if os.path.exists(path):
    body = open(path).read()
    parts = re.split(r'(?m)^(?=## \d{4}-\d{2}-\d{2} )', body)
    entries = [p.rstrip('\n') for p in parts[1:]]
def cutoff(today):
    d, k = today, 0
    while k < 3:
        d -= datetime.timedelta(days=1)
        if d.weekday() < 5:
            k += 1
    return d
cut = cutoff(now.date())
kept = []
for e in entries:
    m = re.match(r'## (\d{4}-\d{2}-\d{2}) \S+ · .* · (.+)$', e.split('\n', 1)[0])
    if m and m.group(2).strip() == 'OK' and datetime.date.fromisoformat(m.group(1)) < cut:
        continue
    kept.append(e)
new = '## %s · %s · %s\n%s' % (now.strftime('%Y-%m-%d %H:%M'), source, status, text.strip())
tmp = path + '.tmp'
with open(tmp, 'w') as f:
    f.write(HEADER + '\n' + '\n\n'.join([new] + kept) + '\n')
os.replace(tmp, path)
PYEOF
