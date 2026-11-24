#!/bin/sh
# The lead's watchdog (bergdb 013-04, plan sections 2, 6 and 9). Written 2026-10-28 for the
# coordinator (013-02); for the lead's whole life, with STOP, since 2026-11-23.
#
# Usage, by the lead at its start and at a repair (/lead):
#
#   nohup sh SKILL_DIR/watchdog.sh STATE_DIR PID >/dev/null 2>&1 &
#
#   STATE_DIR  the lead's state directory, /Users/f/fl/bench/lead/YYYY-MM-DD.
#   PID        the lead session's process ID (~/.claude/sessions/PID.json).
#
# It runs outside the session until the lead touches STATE_DIR/closed or the session's
# process is gone, and never restarts anything. A second one for the same STATE_DIR and PID
# exits at once while the first lives; one for another PID (the session was restarted, and
# /lead repairs) stops the first and takes over. It keeps the Mac from idle sleep (caffeinate -i -w; a closed
# lid still sleeps) and writes STATE_DIR/watchdog.pid. Every 5 minutes, a round: one line in
# STATE_DIR/watchdog.log, such as
#
#   2026-11-24 22:40 session=yes status=7min net=up usage=week 33 %, limit 50 %: ok
#
# (the session's process; the age of STATE_DIR/status.log, the lead's heartbeat, which
# status.sh writes; whether api.anthropic.com answers; the usage, from usage.sh, at most a
# minute, every round while the process lives, so that STOP comes within ten minutes of the
# limit), and these events, each logged once when it happens:
#
#   * the session's process is gone: news.md "needs a look", then the watchdog ends;
#   * the lead is silent, status.log 75 minutes old while the process lives (a hung turn, or
#     no check-in job): news.md "needs a look"; again only after status.log was fresh;
#   * the level is stop (usage.sh: the week at or above the limit), or the usage has been
#     unreadable for an hour: it writes STATE_DIR/STOP, one line with the reason, beginning
#     "STOP by the watchdog". Agents and the lead look for it; status.sh prints it. It
#     removes that file when the usage reads below the limit again (the limit raised with
#     usage.sh -L, or the week reset); a STOP written by someone else stays;
#   * a gap in its own rounds of more than two rounds (the Mac asleep, or the process
#     stopped): "gap ... to ..." in the log;
#   * STATE_DIR/closed: "closed", and the watchdog ends.
#
# news.md is written with tools/news.sh (or $NEWS_SH). Stop it early with
# kill $(cat STATE_DIR/watchdog.pid). For tests: $WATCHDOG_ROUND (seconds, 300),
# $WATCHDOG_SILENT (seconds, 4500), $WATCHDOG_UNREADABLE (seconds, 3600), $LEAD_NET_URL
# (https://api.anthropic.com/), $CLAUDE_HOME (~/.claude), and usage.sh's $CLAUDE_BIN,
# $LEAD_LIMIT and $USAGE_TIMEOUT.
[ $# = 2 ] && [ -d "$1" ] || { echo "usage: watchdog.sh STATE_DIR PID" >&2; exit 2; }
dir=$(cd "$1" && pwd)
pid=$2
skill=$(cd "$(dirname "$0")" && pwd)
news=${NEWS_SH:-/Users/f/fl/repos/bergdb/tools/news.sh}
round=${WATCHDOG_ROUND:-300}
silent_after=${WATCHDOG_SILENT:-4500}
unreadable_after=${WATCHDOG_UNREADABLE:-3600}
url=${LEAD_NET_URL:-https://api.anthropic.com/}
ch=${CLAUDE_HOME:-$HOME/.claude}
log=$dir/watchdog.log

replaced=
if [ -f "$dir/watchdog.pid" ]; then
    old=$(cat "$dir/watchdog.pid")
    case $(ps -p "$old" -o command= 2>/dev/null) in
        *watchdog.sh*" $pid") echo "watchdog.sh: one runs already for $dir" >&2; exit 0 ;;
        *watchdog.sh*) kill "$old" 2>/dev/null; replaced=$old ;;
    esac
fi
echo $$ > "$dir/watchdog.pid"
caffeinate -i -w $$ 2>/dev/null &
sleeper=
trap '[ "$(cat "$dir/watchdog.pid" 2>/dev/null)" = $$ ] && rm -f "$dir/watchdog.pid"' EXIT
trap '[ -z "$sleeper" ] || kill $sleeper 2>/dev/null; exit 0' TERM INT HUP

name=$(sed -n 's/.*"name":"\([^"]*\)".*/\1/p' "$ch/sessions/$pid.json" 2>/dev/null)
[ -n "$name" ] || name="the lead"
say() {
    echo "$(date '+%Y-%m-%d %H:%M') $*" >> "$log"
}
tell() {
    sh "$news" "needs a look" "lead watchdog" "$1"
}
say "watchdog started for $name, process $pid${replaced:+; replaced watchdog $replaced}"

start=$(date +%s)
last=
silent=0
unread=
while :; do
    now=$(date +%s)
    if [ -n "$last" ] && [ $((now - last)) -gt $((2 * round)) ]; then
        say "gap: no round from $(date -r "$last" +%H:%M) to $(date -r "$now" +%H:%M), $(( (now - last) / 60 )) min (the Mac asleep?)"
    fi
    last=$now
    if [ -e "$dir/closed" ]; then
        say "closed; watchdog ended"
        exit 0
    fi
    if kill -0 "$pid" 2>/dev/null; then alive=yes; else alive=no; fi
    if [ -f "$dir/status.log" ]; then
        age=$((now - $(stat -f %m "$dir/status.log")))
        beat=$((age / 60))min
    else
        age=$((now - start))
        beat=none
    fi
    code=$(curl -s -o /dev/null -m 10 -w '%{http_code}' "$url" 2>/dev/null)
    case $code in
        ''|000) net=down ;;
        *) net=up ;;
    esac
    usage=
    if [ $alive = yes ]; then
        usage=$(sh "$skill/usage.sh" 2>/dev/null | head -1 | cut -d';' -f1)
        [ -n "$usage" ] || usage="unknown: usage.sh failed"
    fi
    say "session=$alive status=$beat net=$net${usage:+ usage=$usage}"

    if [ $alive = no ]; then
        say "the session's process $pid is gone; watchdog ended"
        tell "$name: the session's process is gone (found $(date +%H:%M), network $net), and its check-ins and agents with it; state in $dir. To continue: reopen the session and type /lead (013-04)."
        exit 0
    fi

    if [ "$age" -ge "$silent_after" ]; then
        if [ $silent = 0 ]; then
            silent=1
            say "silent: no status.sh for $((age / 60)) min while the process lives"
            tell "$name: silent, no check-in for $((age / 60)) minutes while its process lives (network $net): a hung turn or no check-in job. Open the session and type /lead (013-04); see $dir/watchdog.log."
        fi
    elif [ $silent = 1 ]; then
        silent=0
        say "status.log fresh again"
    fi

    if [ -n "$usage" ]; then
        stop=
        case $usage in
            *": stop") unread=; stop="$usage" ;;
            *": ok"|*": tight") unread= ;;
            *)
                [ -n "$unread" ] || unread=$now
                if [ $((now - unread)) -ge "$unreadable_after" ]; then
                    stop="usage unreadable since $(date -r "$unread" +%H:%M)"
                fi ;;
        esac
        if [ -n "$stop" ]; then
            if [ ! -e "$dir/STOP" ]; then
                echo "STOP by the watchdog at $(date +%H:%M): $stop" > "$dir/STOP"
                say "STOP written: $stop"
            fi
        elif [ -z "$unread" ] && [ -e "$dir/STOP" ] &&
                head -1 "$dir/STOP" | grep -q '^STOP by the watchdog'; then
            rm -f "$dir/STOP"
            say "STOP removed: $usage"
        fi
    fi

    sleep "$round" &
    sleeper=$!
    wait $sleeper
    sleeper=
done
