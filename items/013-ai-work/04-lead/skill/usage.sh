#!/bin/sh
# Reads the week's usage and the lead's weekly limit, and gives a level (bergdb 013-04, plan
# section 6). Written 2026-10-28 for the coordinator (013-02); levels ok, tight and stop and
# the limit file since 2026-11-23.
#
# Usage: usage.sh [-j] [-l LOG] [-L N]
#   -j      print the JSON object instead of the text line
#   -l LOG  also append the text line, with the time, to LOG
#   -L N    set the limit to N percent (1 to 100) for the current week, then print as usual;
#           only when Frans names the number (raising it is his, class 3)
#
# It runs Claude Code's own /usage headless (claude -p /usage, stream-json). /usage is a
# local command: no model call, no usage spent, about 3 s. Its usage_report carries the
# usage endpoint's rows, as the account sees them from every session and machine.
#
# Prints one line, for example:
#   week 33 %, limit 50 %: ok; reset Mon 30 Nov 22:00, 10 % of the week gone; Fable 2 %; extra off
# The part before the first ";" is the one status.sh shows. Every row of the report is in
# the line: "week" is the row weekly_all (all models, the one the limit applies to); a row
# weekly_scoped is named by its model (on 2026-11-23 the only one is "Fable", the week of the
# Fable models alone, the screen's "Current week (Fable)"); "5h" is the row session (the
# 5-hour window, not in the report since 2026-11-08); another kind is printed by its name.
# A row's severity other than normal follows its percent. A limit set with -L ends the line
# ("limit set Tue 24 Nov 09:10"), and one of an earlier week is named as ignored.
#
# The levels, from the week (weekly_all) and the limit:
#   ok       more than 10 points below the limit;
#   tight    within 10 points below it;
#   stop     at or above it;
#   unknown  no row weekly_all (offline, or the report changed): "week ?".
#
# The limit file is /Users/f/fl/bench/lead/limit, or $LEAD_LIMIT; one file for all leads. Its
# lines: "percent N", "week_resets ISO-TIME" (the reset of the week it was set in) and
# "set ISO-TIME"; "#" starts a comment. It holds until week_resets; missing, unreadable or of
# an earlier week, the limit is 50 %.
#
# A /usage that takes more than $USAGE_TIMEOUT seconds (60) is stopped and counts as not read,
# whatever it printed, so that a hung claude holds up neither status.sh nor the watchdog.
#
# Exit codes: 0 read; 1 not read (the level unknown; -L then refuses, as the week's reset is
# not known); 2 wrong arguments. The claude binary is $CLAUDE_BIN, else claude on the PATH,
# else the newest one of the VS Code extension. For tests: $CLAUDE_BIN may be a stand-in that
# prints a canned report, and $LEAD_NOW ("YYYY-MM-DD HH:MM", local time) replaces the clock.
json=0
log=
setlimit=
while getopts jl:L: opt; do
    case $opt in
        j) json=1 ;;
        l) log=$OPTARG ;;
        L) setlimit=$OPTARG ;;
        *) echo "usage: usage.sh [-j] [-l LOG] [-L N]" >&2; exit 2 ;;
    esac
done
case $setlimit in
    '') ;;
    *[!0-9]*) echo "usage.sh: -L takes a whole percent, 1 to 100" >&2; exit 2 ;;
    *) [ "$setlimit" -ge 1 ] && [ "$setlimit" -le 100 ] ||
        { echo "usage.sh: -L takes a whole percent, 1 to 100" >&2; exit 2; } ;;
esac
limitfile=${LEAD_LIMIT:-/Users/f/fl/bench/lead/limit}
bin=${CLAUDE_BIN:-$(command -v claude)}
if [ -z "$bin" ]; then
    bin=$(ls -dt "$HOME"/.vscode/extensions/anthropic.claude-code-*/resources/native-binary/claude 2>/dev/null | head -1)
fi
[ -x "$bin" ] || { echo "usage.sh: no claude binary found; set CLAUDE_BIN" >&2; exit 1; }
report=$(mktemp "${TMPDIR:-/tmp}/usage.XXXXXX") || exit 1
trap 'rm -f "$report"' EXIT
(cd "${TMPDIR:-/tmp}" && exec python3 -c 'import os, subprocess, sys
try:
    subprocess.run(sys.argv[2:], stderr=subprocess.DEVNULL, timeout=float(sys.argv[1]))
except subprocess.TimeoutExpired:
    os.ftruncate(1, 0)' "${USAGE_TIMEOUT:-60}" "$bin" -p /usage --output-format stream-json --verbose \
    --no-session-persistence) > "$report" 2>/dev/null
python3 - "$report" "$json" "$log" "$limitfile" "$setlimit" "$LEAD_NOW" <<'PYEOF'
import datetime, json, os, sys
report, json_out, log, limitfile, setlimit, fake_now = sys.argv[1:7]
json_out = json_out == "1"
if fake_now:
    now = datetime.datetime.strptime(fake_now, "%Y-%m-%d %H:%M").astimezone()
else:
    now = datetime.datetime.now().astimezone()
DEFAULT = 50

rows, extra = None, None
for line in open(report):
    try:
        m = json.loads(line)
    except ValueError:
        continue
    if not isinstance(m, dict):
        continue
    limits = (m.get("usage_report") or {}).get("rate_limits") or {}
    if limits.get("limits") is not None:
        rows, extra = limits["limits"], limits.get("extra_usage")

def iso(t):
    return datetime.datetime.fromisoformat(t).astimezone() if t else None

def when(t, fmt):
    # To the nearest minute: the server may give a reset as 15:49:59.9.
    return (t + datetime.timedelta(seconds=30)).strftime(fmt) if t else "?"

def label(r):
    kind = r.get("kind")
    if kind == "weekly_all":
        return "week"
    if kind == "session":
        return "5h"
    if kind == "weekly_scoped":
        scope = r.get("scope") or {}
        model = (scope.get("model") or {}).get("display_name")
        surface = scope.get("surface")
        surface = surface.get("display_name") if isinstance(surface, dict) else surface
        return model or surface or "scoped"
    return kind or "?"

week = None
for r in rows or []:
    if r.get("kind") == "weekly_all":
        week = r
w = week.get("percent") if week else None
w_reset = iso(week.get("resets_at")) if week else None

def read_limit():
    # Returns (percent, set time, note).
    try:
        lines = open(limitfile).read().splitlines()
    except OSError:
        return DEFAULT, None, None
    d = {}
    for l in lines:
        l = l.split("#", 1)[0].split(None, 1)
        if len(l) == 2:
            d[l[0]] = l[1].strip()
    try:
        p, resets = int(d["percent"]), iso(d["week_resets"])
        set_at = iso(d.get("set"))
    except (KeyError, ValueError, TypeError):
        return DEFAULT, None, "limit file unreadable, ignored"
    if now >= resets:
        return DEFAULT, None, "limit %s %% of an earlier week ignored" % p
    return p, set_at, None

if setlimit:
    if w_reset is None:
        sys.stderr.write("usage.sh: limit not set: the week's reset is unknown (offline?)\n")
        sys.exit(1)
    os.makedirs(os.path.dirname(limitfile) or ".", exist_ok=True)
    tmp = limitfile + ".tmp"
    with open(tmp, "w") as f:
        f.write("# The lead's weekly limit (bergdb 013-04), written by usage.sh -L.\n"
                "percent %s\nweek_resets %s\nset %s\n" % (
                    int(setlimit), w_reset.isoformat(), now.isoformat(timespec="seconds")))
    os.rename(tmp, limitfile)

limit, limit_set, limit_note = read_limit()

if w is None:
    level = "unknown"
elif w >= limit:
    level = "stop"
elif w >= limit - 10:
    level = "tight"
else:
    level = "ok"

parts = ["week %s, limit %s %%: %s" % ("?" if w is None else "%s %%" % w, limit, level)]
if w is None:
    parts.append("/usage gave no row weekly_all (offline?)")
else:
    gone = None
    if w_reset is not None:
        left = (w_reset - now).total_seconds() / 3600
        gone = max(0, min(100, round(100 * (1 - left / (7 * 24)))))
    parts.append("reset %s, %s %% of the week gone" % (when(w_reset, "%a %-d %b %H:%M"),
                                                      "?" if gone is None else gone))
    if week.get("severity") not in (None, "normal"):
        parts[-1] += ", severity " + week["severity"]
for r in rows or []:
    if r is week:
        continue
    s = "%s %s %%" % (label(r), r.get("percent"))
    if r.get("kind") == "session":
        s += " (reset %s)" % when(iso(r.get("resets_at")), "%H:%M")
    if r.get("severity") not in (None, "normal"):
        s += ", severity " + r["severity"]
    parts.append(s)
if rows is not None:
    parts.append("extra " + ("on" if extra and extra.get("is_enabled") else "off"))
if limit_set is not None:
    parts.append("limit set " + when(limit_set, "%a %-d %b %H:%M"))
if limit_note:
    parts.append(limit_note)
text = "; ".join(parts)

data = {"time": now.isoformat(timespec="seconds"), "level": level, "week": w,
        "week_resets": w_reset.isoformat() if w_reset else None,
        "limit": limit, "limit_set": limit_set.isoformat() if limit_set else None,
        "limit_note": limit_note,
        "rows": [{"kind": r.get("kind"), "label": label(r), "percent": r.get("percent"),
                  "resets_at": r.get("resets_at"), "severity": r.get("severity"),
                  "is_active": r.get("is_active")} for r in rows or []],
        "extra_usage": bool(extra and extra.get("is_enabled")), "text": text}
print(json.dumps(data) if json_out else text)
if log:
    with open(log, "a") as f:
        f.write(now.strftime("%Y-%m-%d %H:%M ") + text + "\n")
sys.exit(1 if level == "unknown" else 0)
PYEOF
