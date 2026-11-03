#!/bin/sh
# Reads the Claude plan's usage, for the coordinator's pacing (bergdb 013-02, section 9).
# Written 2026-10-28.
#
# Usage: usage.sh [-j] [-l LOG]
#   -j      print the JSON line instead of the text line
#   -l LOG  also append the text line, with the time, to LOG
#
# It runs Claude Code's own /usage headless (claude -p /usage, stream-json). /usage is a
# local command: no model call, no usage spent, about 3 s. Its usage_report carries the
# usage endpoint's rows, as the account sees them from every session and machine.
#
# Prints one line, for example:
#   level normal: 5h 32% (reset 15:50, window 37% gone); week 46% (reset Sun 2 Nov 22:00, 23% gone); extra off
#
# The level, from the 5-hour window (5h) and the week (all models):
#   limit   5h or week at 98% or more: start nothing; resume after the reset.
#   tight   5h at 80% or more, week at 85% or more, the week 25 points or more ahead of
#           its time (used minus the share of the week gone), or the server's severity
#           warning or critical: high effort, fewer agents, put off what can wait.
#   plenty  5h below 50% and the week at most 15 points ahead of its time: xhigh.
#   normal  otherwise: xhigh, as plenty.
#
# Exit codes: 0 read; 1 not read (offline, or no rows): the line then says "level unknown".
# The claude binary is $CLAUDE_BIN, else claude on the PATH, else the newest one of the VS
# Code extension.
json=0
log=
while getopts jl: opt; do
    case $opt in
        j) json=1 ;;
        l) log=$OPTARG ;;
        *) echo "usage: usage.sh [-j] [-l LOG]" >&2; exit 2 ;;
    esac
done
bin=${CLAUDE_BIN:-$(command -v claude)}
if [ -z "$bin" ]; then
    bin=$(ls -dt "$HOME"/.vscode/extensions/anthropic.claude-code-*/resources/native-binary/claude 2>/dev/null | head -1)
fi
[ -x "$bin" ] || { echo "usage.sh: no claude binary found; set CLAUDE_BIN" >&2; exit 1; }
cd "${TMPDIR:-/tmp}" || exit 1
"$bin" -p /usage --output-format stream-json --verbose --no-session-persistence 2>/dev/null |
python3 -c '
import datetime, json, sys
json_out, log = sys.argv[1] == "1", sys.argv[2]
rows, extra = None, None
for line in sys.stdin:
    try:
        m = json.loads(line)
    except ValueError:
        continue
    report = m.get("usage_report") or {}
    limits = report.get("rate_limits") or {}
    if limits.get("limits") is not None:
        rows, extra = limits["limits"], limits.get("extra_usage")
now = datetime.datetime.now().astimezone()

def row(kind):
    for r in rows or []:
        if r.get("kind") == kind:
            reset = r.get("resets_at")
            reset = datetime.datetime.fromisoformat(reset).astimezone() if reset else None
            return r.get("percent"), reset, r.get("severity")
    return None, None, None

def gone(reset, hours):
    # The share of the window gone, in percent.
    if reset is None:
        return None
    left = (reset - now).total_seconds() / 3600
    return max(0, min(100, round(100 * (1 - left / hours))))

s, s_reset, s_sev = row("session")
w, w_reset, w_sev = row("weekly_all")
s_gone, w_gone = gone(s_reset, 5), gone(w_reset, 7 * 24)
if s is None and w is None:
    level = "unknown"
elif (s or 0) >= 98 or (w or 0) >= 98:
    level = "limit"
elif ((s or 0) >= 80 or (w or 0) >= 85 or (w_gone is not None and (w or 0) - w_gone >= 25)
        or s_sev in ("warning", "critical") or w_sev in ("warning", "critical")):
    level = "tight"
elif (s or 0) < 50 and (w_gone is None or (w or 0) - w_gone <= 15):
    level = "plenty"
else:
    level = "normal"

def when(t, fmt):
    # To the nearest minute: the server gives resets as 15:49:59.9.
    return (t + datetime.timedelta(seconds=30)).strftime(fmt) if t else "?"

if level == "unknown":
    text = "level unknown: /usage gave no rows (offline?)"
else:
    text = "level %s: 5h %s%% (reset %s, window %s%% gone); week %s%% (reset %s, %s%% gone); extra %s" % (
        level, s, when(s_reset, "%H:%M"), s_gone, w, when(w_reset, "%a %-d %b %H:%M"), w_gone,
        "on" if extra and extra.get("is_enabled") else "off")
data = {"time": now.isoformat(timespec="seconds"), "level": level,
        "five_hour": {"percent": s, "resets_at": s_reset.isoformat() if s_reset else None,
                      "gone": s_gone, "severity": s_sev},
        "week": {"percent": w, "resets_at": w_reset.isoformat() if w_reset else None,
                 "gone": w_gone, "severity": w_sev},
        "extra_usage": bool(extra and extra.get("is_enabled"))}
print(json.dumps(data) if json_out else text)
if log:
    with open(log, "a") as f:
        f.write(now.strftime("%Y-%m-%d %H:%M ") + text + "\n")
sys.exit(1 if level == "unknown" else 0)
' "$json" "$log"
