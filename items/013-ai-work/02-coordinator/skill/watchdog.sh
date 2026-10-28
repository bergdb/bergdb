#!/bin/sh
# The coordinator's watchdog (bergdb 013-02, section 8). Written 2026-10-28. The coordinator
# starts it when it goes unattended:
#
#   nohup caffeinate -i sh watchdog.sh STATE_DIR PID "YYYY-MM-DD HH:MM" >/dev/null 2>&1 &
#
#   STATE_DIR  the coordinator's state directory, /Users/f/fl/bench/coord/YYYY-MM-DD.
#   PID        the coordinator session's process ID (~/.claude/sessions/PID.json).
#   END        when to stop: when Frans is back.
#
# caffeinate -i keeps the Mac from idle sleep while this runs. Every 5 minutes it appends a
# line to STATE_DIR/watchdog.log: whether the session's process lives, the age of
# STATE_DIR/heartbeat (each check-in touches it) and whether api.anthropic.com answers. It
# writes to news.md (tools/news.sh, or $NEWS_SH) once if the process is gone, and at END once
# if the heartbeat is more than an hour old. It never restarts anything. Stop it early with
# kill $(cat STATE_DIR/watchdog.pid).
[ $# = 3 ] || { echo "usage: watchdog.sh STATE_DIR PID 'YYYY-MM-DD HH:MM'" >&2; exit 2; }
dir=$1
pid=$2
end=$(date -j -f '%Y-%m-%d %H:%M' "$3" +%s) || exit 2
news=${NEWS_SH:-/Users/f/fl/repos/bergdb/tools/news.sh}
log=$dir/watchdog.log
name=$(sed -n 's/.*"name":"\([^"]*\)".*/\1/p' "$HOME/.claude/sessions/$pid.json" 2>/dev/null)
[ -n "$name" ] || name="the coordinator (process $pid)"
echo $$ > "$dir/watchdog.pid"
trap 'rm -f "$dir/watchdog.pid"' EXIT
sleeper=
trap '[ -z "$sleeper" ] || kill $sleeper 2>/dev/null; exit 0' TERM INT
echo "$(date '+%Y-%m-%d %H:%M') watchdog started for $name until $3" >> "$log"

gone=0
while :; do
    now=$(date +%s)
    if kill -0 "$pid" 2>/dev/null; then alive=yes; else alive=no; fi
    if [ -f "$dir/heartbeat" ]; then
        age=$(( (now - $(stat -f %m "$dir/heartbeat")) / 60 ))
        beat=${age}min
    else
        age=none
        beat=none
    fi
    code=$(curl -s -o /dev/null -m 10 -w '%{http_code}' https://api.anthropic.com/ 2>/dev/null)
    case $code in
        ''|000) net=down ;;
        *) net=up ;;
    esac
    echo "$(date '+%Y-%m-%d %H:%M') session=$alive heartbeat=$beat net=$net" >> "$log"
    if [ $alive = no ] && [ $gone = 0 ]; then
        gone=1
        sh "$news" "needs a look" "coordinator watchdog" "$name: the session's process is gone (found $(date +%H:%M), network $net), and its check-ins with it; state in $dir/state.md. To continue: resume the session, then /coordinator resume (013-02, section 8)."
    fi
    [ "$now" -lt "$end" ] || break
    sleep 300 &
    sleeper=$!
    wait $sleeper
    sleeper=
done

if [ $alive = yes ] && [ "$age" != none ] && [ "$age" -gt 60 ]; then
    sh "$news" "needs a look" "coordinator watchdog" "$name: no check-in for $age minutes at the end of the unattended time (network $net); see $dir/watchdog.log and the day's plan."
fi
echo "$(date '+%Y-%m-%d %H:%M') watchdog ended" >> "$log"
