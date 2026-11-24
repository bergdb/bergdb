#!/bin/sh
# The lead's status (bergdb 013-04, plan sections 2 to 4 and 9). Written 2026-11-23.
#
# Usage: status.sh STATE_DIR
#
# The first call of every turn that Frans did not start: a check-in, an agent's report, a
# finished command. It prints one line, and then a line in capitals for each thing due,
# and appends both to STATE_DIR/status.log, whose age is the lead's heartbeat (watchdog.sh
# reads it). It changes nothing else and computes no mode. About 4 s (usage.sh). The line:
#
#   2026-11-24 22:37 Tue; week 33 %, limit 50 %: ok; watchdog up; disk 212 GB; next summary Wed 07:00
#
# with the part of usage.sh before its first ";" (levels ok, tight, stop, unknown). The
# lines in capitals, in this order:
#
#   STOP ...           STATE_DIR/STOP exists (its first line, the watchdog's reason), or
#                      the level is stop and the watchdog has not written the file yet.
#   PAUSE A to B ...   status.log was more than 45 minutes old: no wake-up from A to B. The
#                      network in watchdog.log during the gap follows ("network down 22:45
#                      to 23:40"; "network up": the account's limit or a hung turn).
#   DUE TIME NAME: DEFAULT
#                      one for each line of STATE_DIR/pending whose time has passed. A line
#                      of pending is "YYYY-MM-DD HH:MM NAME: DEFAULT" (a class 2 decision
#                      that goes ahead by default); blank lines and "#" are skipped; a line
#                      that does not parse gives "DUE ? unreadable line in pending: ...".
#   SUMMARY DUE HH:MM  Monday to Friday, from an hour before the summary's time (07:00, or
#                      HH:MM in STATE_DIR/summary-time) until the lead touches the day's
#                      marker STATE_DIR/summary-YYYY-MM-DD; only when the lead ran before
#                      that hour that day (status.log has an earlier line). "next summary"
#                      in the line is the next one not yet written.
#   WATCHDOG GONE ...  STATE_DIR/watchdog.pid is missing or names no live watchdog.sh, and
#                      STATE_DIR/closed is not there.
#   DISK LOW N GB      under 40 GB free on the volume of STATE_DIR.
#   PERMISSION MODE M  the lead's transcript shows a permission mode other than auto: a
#                      permission prompt would stop the session (plan section 9.1, item 1).
#
# The lead's process is the first ancestor of this script with a file
# ~/.claude/sessions/PID.json (or $LEAD_PID); its transcript is
# ~/.claude/projects/*/SESSION_ID.jsonl. Not found: no PERMISSION MODE line.
#
# For tests: $LEAD_NOW ("YYYY-MM-DD HH:MM") replaces the clock; $LEAD_PID the process;
# $CLAUDE_HOME replaces ~/.claude; usage.sh beside this script takes $CLAUDE_BIN and
# $LEAD_LIMIT; df on the PATH may be a stand-in.
[ $# = 1 ] && [ -d "$1" ] || { echo "usage: status.sh STATE_DIR" >&2; exit 2; }
dir=$(cd "$1" && pwd)
skill=$(cd "$(dirname "$0")" && pwd)
ch=${CLAUDE_HOME:-$HOME/.claude}

usage=$(sh "$skill/usage.sh" 2>/dev/null | head -1)
[ -n "$usage" ] || usage="week ?, limit ?: unknown; usage.sh failed"

wd=none
if [ -f "$dir/watchdog.pid" ]; then
    wpid=$(cat "$dir/watchdog.pid")
    case $(ps -p "$wpid" -o command= 2>/dev/null) in
        *watchdog.sh*) wd=up ;;
        *) wd="process $wpid gone" ;;
    esac
fi

free=$(df -k "$dir" 2>/dev/null | awk 'NR == 2 { print $4 }')

pid=$LEAD_PID
if [ -z "$pid" ]; then
    p=$$
    while [ -n "$p" ] && [ "$p" -gt 1 ]; do
        [ -f "$ch/sessions/$p.json" ] && { pid=$p; break; }
        p=$(ps -o ppid= -p "$p" 2>/dev/null | tr -d ' ')
    done
fi

python3 - "$dir" "$usage" "$wd" "$free" "$pid" "$ch" "$LEAD_NOW" <<'PYEOF'
import datetime, glob, json, os, re, sys
dir, usage, wd, free, pid, ch, fake_now = sys.argv[1:8]
D = datetime.datetime
now = D.strptime(fake_now, "%Y-%m-%d %H:%M") if fake_now else D.now().replace(second=0,
                                                                             microsecond=0)
def path(name):
    return os.path.join(dir, name)
def hm(t):
    return t.strftime("%H:%M")
def stamp(t):
    return t.strftime("%Y-%m-%d %H:%M")
def parse(s):
    return D.strptime(s, "%Y-%m-%d %H:%M")

log = path("status.log")
last = first = None
if os.path.exists(log):
    last = D.fromtimestamp(os.stat(log).st_mtime)
    with open(log) as f:
        m = re.match(r"(\d{4}-\d\d-\d\d \d\d:\d\d) ", f.readline())
        first = parse(m.group(1)) if m else None

short = usage.split(";", 1)[0].strip()
m = re.search(r":\s*(\w+)$", short)
level = m.group(1) if m else "unknown"
due = []

# STOP
if os.path.exists(path("STOP")):
    reason = open(path("STOP")).read().strip().splitlines()
    reason = reason[0] if reason else "(an empty STOP file)"
    due.append(reason if reason.startswith("STOP") else "STOP " + reason)
elif level == "stop":
    due.append("STOP %s (no STOP file yet)" % short)

# PAUSE
if last is not None and (now - last).total_seconds() > 45 * 60:
    net = "no watchdog.log"
    down = []
    wlog = path("watchdog.log")
    if os.path.exists(wlog):
        for line in open(wlog):
            m = re.match(r"(\d{4}-\d\d-\d\d \d\d:\d\d) .*\bnet=(\w+)", line)
            if m and last <= parse(m.group(1)) <= now:
                down.append((parse(m.group(1)), m.group(2)))
        downs = [t for t, n in down if n == "down"]
        if not down:
            net = "no watchdog rounds in the gap"
        elif downs:
            net = "network down %s to %s" % (hm(min(downs)), hm(max(downs)))
        else:
            net = "network up: the account's limit or a hung turn"
    mins = int((now - last).total_seconds() // 60)
    due.append("PAUSE %s to %s (%d min); %s" % (hm(last), hm(now), mins, net))

# DUE
if os.path.exists(path("pending")):
    for line in open(path("pending")):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        m = re.match(r"(\d{4}-\d\d-\d\d \d\d:\d\d)\s+(.*)$", line)
        try:
            t = parse(m.group(1))
        except (AttributeError, ValueError):
            due.append("DUE ? unreadable line in pending: " + line)
            continue
        if t <= now:
            due.append("DUE %s %s" % (stamp(t), m.group(2)))

# SUMMARY DUE, and the next summary
st = "07:00"
if os.path.exists(path("summary-time")):
    s = open(path("summary-time")).read().strip()
    if re.fullmatch(r"\d\d:\d\d", s):
        st = s
sh, sm = int(st[:2]), int(st[3:])
def at(day):
    return D(day.year, day.month, day.day, sh, sm)
def written(day):
    return os.path.exists(path("summary-" + day.strftime("%Y-%m-%d")))
today = now.date()
summary_due = False
if today.weekday() < 5 and not written(today):
    start = at(today) - datetime.timedelta(hours=1)
    if now >= start and first is not None and first < start:
        summary_due = True
        due.append("SUMMARY DUE %s (touch %s when written)" % (st, path("summary-" + str(today))))
day = today
while True:
    if day.weekday() < 5 and not written(day) and (day > today or now < at(day) or summary_due):
        break
    day += datetime.timedelta(days=1)
nxt = at(day).strftime("%a %H:%M")

# WATCHDOG GONE
if wd != "up":
    if os.path.exists(path("closed")):
        wd = "ended (closed)"
    else:
        due.append("WATCHDOG GONE (%s)" % ("no watchdog.pid" if wd == "none" else wd))
        wd = "gone"

# DISK LOW
disk = "?"
if free.isdigit():
    gb = int(free) // (1024 * 1024)
    disk = "%d GB" % gb
    if gb < 40:
        due.append("DISK LOW %d GB free (under 40 GB)" % gb)

# PERMISSION MODE
if pid:
    try:
        sid = json.load(open(os.path.join(ch, "sessions", pid + ".json")))["sessionId"]
        mode = None
        for t in glob.glob(os.path.join(ch, "projects", "*", sid + ".jsonl")):
            with open(t, "rb") as f:
                f.seek(max(0, os.path.getsize(t) - 2000000))
                for m in re.finditer(rb'"permissionMode":"([^"]*)"', f.read()):
                    mode = m.group(1).decode()
        if mode is not None and mode != "auto":
            due.append("PERMISSION MODE %s (not auto): a permission prompt would stop the "
                       "session" % mode)
    except (OSError, ValueError, KeyError):
        pass

line = "%s %s; %s; watchdog %s; disk %s; next summary %s" % (
    stamp(now), now.strftime("%a"), short, wd, disk, nxt)
out = "\n".join([line] + due)
print(out)
with open(log, "a") as f:
    f.write(out + "\n")
PYEOF
