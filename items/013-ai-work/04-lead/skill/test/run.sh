#!/bin/sh
# Tests of the lead's scripts, usage.sh, status.sh and watchdog.sh, on canned inputs (bergdb
# 013-04, plan section 12, steps 2 to 4). Written 2026-11-23. Functional; about a minute,
# most of it the watchdog's rounds in real time.
#
# Usage: sh test/run.sh   (from the skill directory or anywhere)
#
# Everything runs in a temporary directory with stand-ins: a claude that prints a canned
# /usage report ($CLAUDE_BIN), a limit file ($LEAD_LIMIT), df, tools/news.sh ($NEWS_SH), the
# session's process (a sleep) and its files ($CLAUDE_HOME), and an unreachable network
# ($LEAD_NET_URL). It touches neither /Users/f/fl/bench/lead/ nor news.md, and calls no
# model. The clock is $LEAD_NOW for usage.sh and status.sh, real time for the watchdog.
# test/report-2026-11-23.jsonl is the live report of 2026-11-23 22:16, its rows as received.
# Prints "LEAD TESTS OK" at the end, or the failures, and exits 1 on a failure.
skill=$(cd "$(dirname "$0")/.." && pwd)
T=$(mktemp -d "${TMPDIR:-/tmp}/leadtest.XXXXXX") && T=$(cd "$T" && pwd -P) || exit 1
export TZ=Europe/Stockholm
fails=0
pids=
cleanup() {
    for p in $pids; do kill "$p" 2>/dev/null; done
    [ -f "$T/state/watchdog.pid" ] && kill "$(cat "$T/state/watchdog.pid")" 2>/dev/null
    [ -n "$KEEP" ] && echo "kept $T" || rm -rf "$T"
}
trap cleanup EXIT

ok() {
    echo "ok   $1"
}
fail() {
    echo "FAIL $1"
    fails=$((fails + 1))
}
# same NAME EXPECTED ACTUAL
same() {
    if [ "$2" = "$3" ]; then ok "$1"; else fail "$1"; echo "     expected: $2"; echo "     actual:   $3"; fi
}
# count NAME N PATTERN FILE: the fixed string PATTERN is on exactly N lines of FILE
count() {
    c=$(grep -cF -- "$3" "$4" 2>/dev/null)
    c=${c:-0}
    if [ "$c" = "$2" ]; then ok "$1"; else fail "$1 ($c lines with \"$3\" in $(basename "$4"), not $2)"; fi
}
# waitcount SECONDS N PATTERN FILE: wait until PATTERN is on N lines of FILE
waitcount() {
    i=0
    while [ $i -lt $(($1 * 4)) ]; do
        [ "$(grep -cF -- "$3" "$4" 2>/dev/null)" = "$2" ] && return 0
        sleep 0.25
        i=$((i + 1))
    done
    return 1
}
# waitfor SECONDS PATTERN FILE
waitfor() {
    i=0
    while [ $i -lt $(($1 * 4)) ]; do
        grep -qF -- "$2" "$3" 2>/dev/null && return 0
        sleep 0.25
        i=$((i + 1))
    done
    return 1
}

# The stand-ins.
mkdir -p "$T/bin" "$T/claude/sessions" "$T/claude/projects/p" "$T/state"
cat > "$T/bin/claude" <<'EOF'
#!/bin/sh
[ -n "$USAGE_DELAY" ] && exec sleep "$USAGE_DELAY"
[ -f "$USAGE_CANNED" ] && cat "$USAGE_CANNED"
[ -n "$USAGE_HANG" ] && exec sleep "$USAGE_HANG"
exit 0
EOF
cat > "$T/bin/df" <<'EOF'
#!/bin/sh
echo "Filesystem   1024-blocks      Used Available Capacity  iused     ifree %iused  Mounted on"
echo "/dev/disk3s1   971350180 877381500 ${DF_FREE_KB:-222298112}    94% 20622721 650122240    3%   /"
EOF
cat > "$T/bin/news.sh" <<'EOF'
#!/bin/sh
echo "$1 | $2 | $3" >> "$NEWS_OUT"
EOF
chmod +x "$T/bin/claude" "$T/bin/df" "$T/bin/news.sh"
export CLAUDE_BIN=$T/bin/claude USAGE_CANNED=$T/report.jsonl LEAD_LIMIT=$T/limit
export CLAUDE_HOME=$T/claude NEWS_SH=$T/bin/news.sh NEWS_OUT=$T/news.txt
export LEAD_NET_URL=http://127.0.0.1:9/ PATH=$T/bin:$PATH
RESET=2026-11-30T21:00:00+00:00

# report WEEK [MORE_ROWS] [RESET]: a canned report, as claude -p /usage gives it
report() {
    r=${3:-$RESET}
    printf '{"type":"system","subtype":"init"}\n' > "$USAGE_CANNED"
    printf '{"type":"assistant","usage_report":{"rate_limits":{"limits":[{"kind":"weekly_all","group":"weekly","percent":%s,"resets_at":"%s","scope":null,"severity":"normal","is_active":true},{"kind":"weekly_scoped","group":"weekly","percent":3,"resets_at":"%s","scope":{"model":{"display_name":"Fable"},"surface":null},"severity":"normal","is_active":false}%s],"extra_usage":{"is_enabled":false}}}}\n' \
        "$1" "$r" "$r" "$2" >> "$USAGE_CANNED"
    printf '{"type":"result","subtype":"success","result":"Current week (all models): %s%% used"}\n' "$1" >> "$USAGE_CANNED"
}
offline() {
    printf '{"type":"system","subtype":"init"}\n{"type":"assistant","usage_report":{"rate_limits":null}}\n' > "$USAGE_CANNED"
}
U() {
    sh "$skill/usage.sh" "$@"
}

echo "usage.sh"
export LEAD_NOW="2026-11-24 22:37"
BASE="reset Mon 30 Nov 22:00, 15 % of the week gone"
TAIL="$BASE; Fable 3 %; extra off"
report 30
same "below: week 30 % ok" "week 30 %, limit 50 %: ok; $TAIL" "$(U)"
report 39
same "39 % is ok" "week 39 %, limit 50 %: ok" "$(U | cut -d';' -f1)"
report 40
same "within 10 points: 40 % tight" "week 40 %, limit 50 %: tight; $TAIL" "$(U)"
report 49
same "49 % tight" "week 49 %, limit 50 %: tight" "$(U | cut -d';' -f1)"
report 50
same "at the limit: 50 % stop" "week 50 %, limit 50 %: stop; $TAIL" "$(U)"
report 104
same "above the limit: stop" "week 104 %, limit 50 %: stop" "$(U | cut -d';' -f1)"
U >/dev/null
same "exit 0 when read" 0 $?

report 55
printf 'percent 80\nweek_resets 2026-11-23T22:00:00+01:00\nset 2026-11-20T09:00:00+01:00\n' > "$LEAD_LIMIT"
same "a limit of an earlier week: 50 %" "week 55 %, limit 50 %: stop; $TAIL; limit 80 % of an earlier week ignored" "$(U)"
same "-L 60 sets the limit" "week 55 %, limit 60 %: tight; $TAIL; limit set Tue 24 Nov 22:37" "$(U -L 60)"
same "the limit file" "percent 60|week_resets 2026-11-30T22:00:00+01:00|set 2026-11-24T22:37:00+01:00" \
    "$(grep -v '^#' "$LEAD_LIMIT" | tr '\n' '|' | sed 's/|$//')"
same "the limit holds on the next call" "week 55 %, limit 60 %: tight" "$(U | cut -d';' -f1)"
same "the limit ends at the week's reset" "week 55 %, limit 50 %: stop" "$(LEAD_NOW="2026-11-30 22:00" U | cut -d';' -f1)"
same "the last minute of its week" "week 55 %, limit 60 %: tight" "$(LEAD_NOW="2026-11-30 21:59" U | cut -d';' -f1)"
U -L 0 >/dev/null 2>&1; same "-L 0 refused" 2 $?
U -L 101 >/dev/null 2>&1; same "-L 101 refused" 2 $?
U -L 5x >/dev/null 2>&1; same "-L 5x refused" 2 $?
echo "percent sixty" > "$LEAD_LIMIT"
same "an unreadable limit file: 50 %" "week 55 %, limit 50 %: stop; $TAIL; limit file unreadable, ignored" "$(U)"
rm -f "$LEAD_LIMIT"

offline
same "no rows" "week ?, limit 50 %: unknown; /usage gave no row weekly_all (offline?)" "$(U)"
U >/dev/null; same "exit 1 with no rows" 1 $?
U -L 70 >/dev/null 2>&1; same "-L refused with no rows" 1 $?
[ -e "$LEAD_LIMIT" ] && fail "-L with no rows wrote the limit file" || ok "-L with no rows wrote no limit file"
rm -f "$USAGE_CANNED"
same "no report at all" "week ?, limit 50 %: unknown; /usage gave no row weekly_all (offline?)" "$(U)"
t0=$(date +%s)
out=$(USAGE_DELAY=30 USAGE_TIMEOUT=1 U); rc=$?
t1=$(date +%s)
same "a hung /usage: not read" "1 week ?, limit 50 %: unknown" "$rc $(echo "$out" | cut -d';' -f1)"
[ $((t1 - t0)) -le 5 ] && ok "a hung /usage stopped after USAGE_TIMEOUT" ||
    fail "a hung /usage stopped after USAGE_TIMEOUT ($((t1 - t0)) s)"
report 30
out=$(USAGE_HANG=30 USAGE_TIMEOUT=1 U); rc=$?
same "a /usage that hangs after its report: not read" "1 week ?, limit 50 %: unknown" \
    "$rc $(echo "$out" | cut -d';' -f1)"

report 30 ',{"kind":"session","group":"session","percent":81,"resets_at":"2026-11-24T23:50:00+00:00","severity":"warning","is_active":false},{"kind":"weekly_scoped","group":"weekly","percent":7,"resets_at":"2026-11-30T21:00:00+00:00","scope":{"model":null,"surface":{"display_name":"Claude Code"}},"severity":"normal","is_active":false},{"kind":"monthly_new","group":"monthly","percent":12,"resets_at":null,"severity":"normal","is_active":false}'
same "every row of the report" "week 30 %, limit 50 %: ok; $BASE; Fable 3 %; 5h 81 % (reset 00:50), severity warning; Claude Code 7 %; monthly_new 12 %; extra off" "$(U)"
same "-j: JSON with the level and every row" "ok 30 50 week,Fable,5h,Claude Code,monthly_new" \
    "$(U -j | python3 -c 'import json,sys; d=json.load(sys.stdin); print(d["level"], d["week"], d["limit"], ",".join(r["label"] for r in d["rows"]))')"
cp "$skill/test/report-2026-11-23.jsonl" "$USAGE_CANNED"
same "the live report of 2026-11-23" "week 0 %, limit 50 %: ok; $BASE; Fable 0 %; extra off" "$(U)"
U -l "$T/usage.log" >/dev/null
same "-l appends the line with the time" "2026-11-24 22:37 week 0 %, limit 50 %: ok" "$(cut -d';' -f1 "$T/usage.log")"

echo "status.sh"
S=$T/state
# at TIME: run status.sh at TIME, with status.log last written 10 minutes before
at() {
    if [ -f "$S/status.log" ]; then
        touch -t "$(date -j -v-10M -f '%Y-%m-%d %H:%M' "$1" +%Y%m%d%H%M)" "$S/status.log"
    fi
    LEAD_NOW=$1 sh "$skill/status.sh" "$S" > "$T/out"
}
caps() {
    sed 1d "$T/out" | tr '\n' '|' | sed 's/|$//'
}
mkdir -p "$T/fake"
printf 'while :; do sleep 1; done\n' > "$T/fake/watchdog.sh"
sh "$T/fake/watchdog.sh" >/dev/null 2>&1 &
fakewd=$!
pids="$pids $fakewd"
echo $fakewd > "$S/watchdog.pid"
echo '{"pid":4242,"sessionId":"s-4242","name":"lead-1124"}' > "$CLAUDE_HOME/sessions/4242.json"
echo '{"type":"user","permissionMode":"auto"}' > "$CLAUDE_HOME/projects/p/s-4242.jsonl"
export LEAD_PID=4242
report 30
at "2026-11-24 22:37"
same "the line, nothing due" "2026-11-24 22:37 Tue; week 30 %, limit 50 %: ok; watchdog up; disk 212 GB; next summary Wed 07:00" "$(cat "$T/out")"
same "status.log has the output" "$(cat "$T/out")" "$(cat "$S/status.log")"

printf '# class 2 decisions\n2026-11-24 23:00 fable-t7: Fable high for the T7 proof\n\n2026-11-24 22:30 push-028-91: push the fix\nsoon fix-later: unreadable\n' > "$S/pending"
at "2026-11-24 22:37"
same "DUE for a passed time only, and an unreadable line" \
    "DUE 2026-11-24 22:30 push-028-91: push the fix|DUE ? unreadable line in pending: soon fix-later: unreadable" "$(caps)"
at "2026-11-24 23:00"
same "DUE at its minute" \
    "DUE 2026-11-24 23:00 fable-t7: Fable high for the T7 proof|DUE 2026-11-24 22:30 push-028-91: push the fix|DUE ? unreadable line in pending: soon fix-later: unreadable" "$(caps)"
rm "$S/pending"

report 50
at "2026-11-24 23:10"
same "STOP from the level, before the watchdog's file" "STOP week 50 %, limit 50 %: stop (no STOP file yet)" "$(caps)"
echo "STOP by the watchdog at 23:12: week 50 %, limit 50 %: stop" > "$S/STOP"
at "2026-11-24 23:15"
same "STOP from the file, once" "STOP by the watchdog at 23:12: week 50 %, limit 50 %: stop" "$(caps)"
rm "$S/STOP"
report 30

at "2026-11-25 05:59"
same "no SUMMARY DUE at 05:59 on a Wednesday" "" "$(caps)"
same "next summary today" "next summary Wed 07:00" "$(head -1 "$T/out" | sed 's/.*; //')"
at "2026-11-25 06:00"
same "SUMMARY DUE at 06:00 on a Wednesday" "SUMMARY DUE 07:00 (touch $S/summary-2026-11-25 when written)" "$(caps)"
at "2026-11-25 08:30"
same "SUMMARY DUE until the marker" "SUMMARY DUE 07:00 (touch $S/summary-2026-11-25 when written)" "$(caps)"
touch "$S/summary-2026-11-25"
at "2026-11-25 08:40"
same "no SUMMARY DUE after the marker" "" "$(caps)"
same "next summary the next weekday" "next summary Thu 07:00" "$(head -1 "$T/out" | sed 's/.*; //')"
at "2026-11-27 06:30"
count "SUMMARY DUE on a Friday" 1 "SUMMARY DUE" "$T/out"
touch "$S/summary-2026-11-27"
at "2026-11-28 06:30"
same "no SUMMARY DUE on a Saturday" "" "$(caps)"
same "next summary Monday" "next summary Mon 07:00" "$(head -1 "$T/out" | sed 's/.*; //')"
at "2026-11-29 06:30"
same "no SUMMARY DUE on a Sunday" "" "$(caps)"
at "2026-11-30 06:00"
count "SUMMARY DUE on a Monday" 1 "SUMMARY DUE" "$T/out"
echo "08:00" > "$S/summary-time"
at "2026-11-30 06:30"
same "summary-time 08:00: not due at 06:30" "" "$(caps)"
at "2026-11-30 07:00"
same "summary-time 08:00: due at 07:00" "SUMMARY DUE 08:00 (touch $S/summary-2026-11-30 when written)" "$(caps)"
rm "$S/summary-time"
mv "$S/status.log" "$T/status.log.keep"
echo "2026-11-30 06:10 the lead started after 06:00" > "$S/status.log"
at "2026-11-30 06:40"
same "no SUMMARY DUE for a lead started after 06:00 that day" "" "$(caps)"
mv "$T/status.log.keep" "$S/status.log"

# ps STAMP TIME: status.sh at TIME, status.log last written at STAMP (touch -t)
ps_at() {
    touch -t "$1" "$S/status.log"
    LEAD_NOW=$2 sh "$skill/status.sh" "$S" > "$T/out"
}
ps_at 202612010400 "2026-12-01 05:00"
same "PAUSE with no watchdog.log" "PAUSE 04:00 to 05:00 (60 min); no watchdog.log" "$(caps)"
printf '2026-12-01 05:05 session=yes status=5min net=up\n2026-12-01 05:10 session=yes status=10min net=down\n2026-12-01 05:30 session=yes status=30min net=down\n2026-12-01 05:40 session=yes status=40min net=up\n' > "$S/watchdog.log"
ps_at 202612010500 "2026-12-01 06:01"
same "PAUSE with the network down, and SUMMARY DUE" "PAUSE 05:00 to 06:01 (61 min); network down 05:10 to 05:30|SUMMARY DUE 07:00 (touch $S/summary-2026-12-01 when written)" "$(caps)"
touch "$S/summary-2026-12-01"
ps_at 202612010534 "2026-12-01 06:20"
same "PAUSE after 46 minutes with the network up" "PAUSE 05:34 to 06:20 (46 min); network up: the account's limit or a hung turn" "$(caps)"
ps_at 202612010535 "2026-12-01 06:20"
same "no PAUSE after 45 minutes" "" "$(caps)"
ps_at 202612010550 "2026-12-01 06:40"
same "PAUSE with no watchdog rounds in the gap" "PAUSE 05:50 to 06:40 (50 min); no watchdog rounds in the gap" "$(caps)"
rm "$S/watchdog.log"

at "2026-12-01 07:00"
same "nothing due" "" "$(caps)"
kill $fakewd
wait $fakewd 2>/dev/null
at "2026-12-01 07:30"
same "WATCHDOG GONE, a dead process" "WATCHDOG GONE (process $fakewd gone)" "$(caps)"
same "watchdog gone in the line" "watchdog gone" "$(head -1 "$T/out" | cut -d';' -f3 | sed 's/^ //')"
rm "$S/watchdog.pid"
at "2026-12-01 07:40"
same "WATCHDOG GONE, no pid file" "WATCHDOG GONE (no watchdog.pid)" "$(caps)"
touch "$S/closed"
at "2026-12-01 07:50"
same "no WATCHDOG GONE once closed" "" "$(caps)"
same "watchdog ended in the line" "watchdog ended (closed)" "$(head -1 "$T/out" | cut -d';' -f3 | sed 's/^ //')"
DF_FREE_KB=41000000 at "2026-12-01 08:00"
same "DISK LOW at 39 GB" "DISK LOW 39 GB free (under 40 GB)" "$(caps)"
DF_FREE_KB=41943040 at "2026-12-01 08:10"
same "no DISK LOW at 40 GB" "" "$(caps)"
echo '{"type":"user","permissionMode":"auto"}' >> "$CLAUDE_HOME/projects/p/s-4242.jsonl"
echo '{"type":"user","permissionMode":"default"}' >> "$CLAUDE_HOME/projects/p/s-4242.jsonl"
at "2026-12-01 08:20"
same "PERMISSION MODE when the last one is not auto" "PERMISSION MODE default (not auto): a permission prompt would stop the session" "$(caps)"
echo '{"type":"user","permissionMode":"auto"}' >> "$CLAUDE_HOME/projects/p/s-4242.jsonl"
at "2026-12-01 08:30"
same "no PERMISSION MODE when back to auto" "" "$(caps)"
rm "$S/closed"

# All at once, each once, in the documented order.
report 51
echo "STOP by the watchdog at 05:40: week 51 %, limit 50 %: stop" > "$S/STOP"
echo "2026-12-02 05:00 fable-t7: Fable high for the T7 proof" > "$S/pending"
echo '{"type":"user","permissionMode":"plan"}' >> "$CLAUDE_HOME/projects/p/s-4242.jsonl"
DF_FREE_KB=10485760 ps_at 202612020500 "2026-12-02 06:15"
same "all lines in capitals, each once, in order" "STOP|PAUSE|DUE|SUMMARY|WATCHDOG|DISK|PERMISSION" "$(sed 1d "$T/out" | cut -d' ' -f1 | tr '\n' '|' | sed 's/|$//')"
same "the line with them" "2026-12-02 06:15 Wed; week 51 %, limit 50 %: stop; watchdog gone; disk 10 GB; next summary Wed 07:00" "$(head -1 "$T/out")"
rm -f "$S"/STOP "$S"/pending "$S"/summary-* "$S/status.log"
unset LEAD_NOW LEAD_PID

echo "watchdog.sh (real time, rounds of 1 s)"
export WATCHDOG_ROUND=1 WATCHDOG_SILENT=6 WATCHDOG_UNREADABLE=3
W=$S/watchdog.log
rm -f "$W" "$NEWS_OUT" "$S/closed" "$S/watchdog.pid"
sleep 600 >/dev/null 2>&1 &
lead=$!
pids="$pids $lead"
echo "{\"pid\":$lead,\"sessionId\":\"s-$lead\",\"name\":\"lead-test\"}" > "$CLAUDE_HOME/sessions/$lead.json"
# A check-in every second keeps status.log fresh, until it is stopped.
beat() {
    while :; do touch "$S/status.log"; sleep 1; done >/dev/null 2>&1 &
    beater=$!
    pids="$pids $beater"
}
stopbeat() {
    kill $beater
    wait $beater 2>/dev/null
}
beat
report 30
sh "$skill/watchdog.sh" "$S" "$lead" >/dev/null 2>&1 &
wd=$!
pids="$pids $wd"
waitfor 5 "usage=week 30 %, limit 50 %: ok" "$W" && ok "rounds with the usage" || fail "rounds with the usage"
same "watchdog.pid" "$wd" "$(cat "$S/watchdog.pid")"
sh "$skill/watchdog.sh" "$S" "$lead" 2>"$T/second"
same "a second watchdog exits at once" "0 watchdog.sh: one runs already for $S" "$? $(cat "$T/second")"
count "started once" 1 "watchdog started for lead-test, process $lead" "$W"

report 50
waitfor 5 "STOP written" "$W" && ok "STOP written at the limit" || fail "STOP written at the limit"
same "the STOP file" "STOP by the watchdog at $(date +%H:%M): week 50 %, limit 50 %: stop" "$(cat "$S/STOP" 2>/dev/null)"
sleep 3
count "STOP written once" 1 "STOP written" "$W"
printf 'percent 60\nweek_resets %s\nset 2026-11-24T09:10:00+01:00\n' "$RESET" > "$LEAD_LIMIT"
waitfor 5 "STOP removed" "$W" && ok "STOP removed when the limit is raised" || fail "STOP removed when the limit is raised"
[ -e "$S/STOP" ] && fail "no STOP file after the raise" || ok "no STOP file after the raise"
rm -f "$LEAD_LIMIT"
waitcount 5 2 "STOP written" "$W" && ok "STOP written again at the old limit" || fail "STOP written again at the old limit"
report 0 '' 2026-12-07T21:00:00+00:00
waitcount 5 2 "STOP removed" "$W" && ok "STOP removed at the week's reset" || fail "STOP removed at the week's reset"
echo "STOP by Frans: no new agents tonight" > "$S/STOP"
sleep 3
same "a STOP by someone else stays" "STOP by Frans: no new agents tonight" "$(cat "$S/STOP" 2>/dev/null)"
rm -f "$S/STOP"

offline
waitfor 8 "STOP written: usage unreadable since" "$W" && ok "STOP after the usage is unreadable for a while" || fail "STOP after the usage is unreadable for a while"
report 30
waitfor 5 "STOP removed: week 30 %" "$W" && ok "STOP removed when the usage reads again" || fail "STOP removed when the usage reads again"
count "STOP written three times in all" 3 "STOP written" "$W"
count "STOP removed three times in all" 3 "STOP removed" "$W"

stopbeat
waitfor 10 "silent:" "$W" && ok "the silent lead" || fail "the silent lead"
sleep 3
count "silent reported once" 1 "silent, no check-in" "$NEWS_OUT"
beat
waitfor 5 "status.log fresh again" "$W" && ok "fresh again" || fail "fresh again"
stopbeat
waitcount 10 2 "silent:" "$W"
sleep 3
count "a second silence, reported again" 2 "silent, no check-in" "$NEWS_OUT"
beat

kill -STOP $wd
sleep 4
kill -CONT $wd
waitfor 5 "gap: no round from" "$W" && ok "a gap in its own rounds" || fail "a gap in its own rounds"
sleep 2
count "the gap logged once" 1 "gap: no round from" "$W"

kill $lead
wait $lead 2>/dev/null
waitfor 5 "watchdog ended" "$W" && ok "the process gone" || fail "the process gone"
sleep 1
count "the process gone, reported once" 1 "the session's process is gone" "$NEWS_OUT"
kill -0 $wd 2>/dev/null && fail "the watchdog ended" || ok "the watchdog ended"
[ -e "$S/watchdog.pid" ] && fail "watchdog.pid removed" || ok "watchdog.pid removed"
same "news.md: needs a look, from the lead watchdog" "needs a look | lead watchdog | lead-test" "$(head -1 "$NEWS_OUT" | cut -d: -f1)"

sleep 600 >/dev/null 2>&1 &
lead=$!
pids="$pids $lead"
sh "$skill/watchdog.sh" "$S" "$lead" >/dev/null 2>&1 &
wd=$!
pids="$pids $wd"
waitfor 5 "process $lead" "$W"
touch "$S/closed"
waitfor 5 "closed; watchdog ended" "$W" && ok "closed ends the watchdog" || fail "closed ends the watchdog"
sleep 1
kill -0 $wd 2>/dev/null && fail "the watchdog ended when closed" || ok "the watchdog ended when closed"
count "no news when closed" 3 "" "$NEWS_OUT"
stopbeat
kill $lead
wait $lead 2>/dev/null

# A dead session is reported at once, though /usage hangs: no usage is read for it.
rm -f "$S/closed"
USAGE_DELAY=30 sh "$skill/watchdog.sh" "$S" "$lead" >/dev/null 2>&1 &
wd=$!
pids="$pids $wd"
waitfor 5 "the session's process $lead is gone" "$W" && ok "a dead session reported at once, /usage hung" ||
    fail "a dead session reported at once, /usage hung"

# After a restart of the session, /lead starts a watchdog for the new process: it replaces
# the one of the old process, which may still be in its round.
rm -f "$S/closed"
sleep 600 >/dev/null 2>&1 &
old=$!
sleep 600 >/dev/null 2>&1 &
new=$!
pids="$pids $old $new"
beat
sh "$skill/watchdog.sh" "$S" "$old" >/dev/null 2>&1 &
wd1=$!
pids="$pids $wd1"
waitfor 5 "process $old" "$W"
sh "$skill/watchdog.sh" "$S" "$new" >/dev/null 2>&1 &
wd2=$!
pids="$pids $wd2"
waitfor 5 "process $new; replaced watchdog $wd1" "$W" && ok "a watchdog for a new process replaces the old one" ||
    fail "a watchdog for a new process replaces the old one"
sleep 1
kill -0 $wd1 2>/dev/null && fail "the replaced watchdog ended" || ok "the replaced watchdog ended"
same "watchdog.pid names the new watchdog" "$wd2" "$(cat "$S/watchdog.pid" 2>/dev/null)"
touch "$S/closed"
waitcount 5 2 "closed; watchdog ended" "$W"
kill -0 $wd2 2>/dev/null && fail "the new watchdog ended when closed" || ok "the new watchdog ended when closed"
stopbeat
kill $old $new
wait $old $new 2>/dev/null

echo
if [ $fails = 0 ]; then
    echo "LEAD TESTS OK"
else
    echo "LEAD TESTS FAILED: $fails"
    exit 1
fi
