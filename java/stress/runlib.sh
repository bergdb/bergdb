# The machinery that night.sh and week.sh share (bergdb 028-27): the clone of HEAD, the
# step function, the report, the news entry and the day's number for seeds. Not a script
# to run: night.sh and week.sh source it from java/ (". ./stress/runlib.sh"). Each of them
# is a distinct set of tests; this file holds no test step.
#
#   run_start KIND TITLE [SUFFIX [LINE]]
#       KIND is night or week. Clones HEAD of this repository into build/KIND/RUN/repo (RUN
#       is the date and time; lean/.lake and lean/contractcheck/.lake are copied in, so that
#       lake builds only what changed) and writes the head of build/KIND/RUN/report.txt:
#       "TITLE RUN on HOST SUFFIX", the kind, the commit, the JDK and LINE, if given. Sets
#       RUN, SRC, REPORT, NAME (NIGHT or WEEK) and FAILED.
#   step NAME COMMAND...
#       Runs the command in the clone's java/, its output in RUN/NAME.txt, and adds a line
#       to the report: the name, ok or FAILED, the seconds and the output's last line. A
#       failure is noted in FAILED, and the run goes on. Returns the command's status.
#   step_bg NAME COMMAND...
#       As step, but in the background, beside the steps that follow it, and in a clone of
#       its own, RUN/repo-NAME, of the run's clone (lean/.lake and lean/contractcheck/.lake
#       copied in), so that its builds and theirs never meet: build.sh deletes the classes
#       and the jars before it writes them again, and a JVM that starts meanwhile fails
#       (bergdb 028-64). Its line is added to the report by step_wait.
#   step_wait
#       Waits for the steps that step_bg started, adds their lines to the report in the
#       order in which they started, and notes their failures in FAILED.
#   run_guard SECONDS
#       The whole run's hang guard (bergdb 028-64): if the run has not ended SECONDS after
#       run_start, writes RUN/hang.txt and kills the processes of the steps then running
#       (TERM, then KILL to those left), which fail with a line that says HANG; the steps
#       not yet started are not run, and the report ends "NAME FAILED: ... hang-guard". A
#       hang guard, not a time limit: SECONDS is far above the run's time.
#   run_stop
#       For a trap of INT and TERM (week.sh): kills every step's processes, the background
#       steps' too, which ignore SIGINT, and the guard, and exits with status 130.
#   run_finish
#       Copies the clones' *.txt logs (without the databases and traces) to RUN/logs/,
#       deletes the clones, ends the report with "NAME OK (N minutes)" or "NAME FAILED:
#       STEPS (N minutes)", prints it, and adds a line to news.md with tools/news.sh
#       (AGENTS.md, "News"). Returns 1 if a step failed.
#   DAY
#       The day's number (days since 1970), for seeds that are new each day; DAY=N in the
#       environment takes day N's seeds again (bergdb 030-30).
#   keep_traces DIR...
#       In a step, in the clone's java/: copies the traces that build/traces/DIR/failed.txt
#       lists (conformance.sh, treeconf.sh and contractconf.sh write it: the failing traces),
#       each with its outputs (NAME-SEED.*), to RUN/traces/DIR/, which run_finish keeps; so a
#       failing trace of new seeds stays with its seed in its name (bergdb 030-30).
#
# DRY=1: run_start, step, step_bg and run_finish print the steps with their commands
# instead of running them: no clone, no report, no news entry; a check of a script's steps
# and order.

if [ -n "${JAVA_HOME:-}" ]; then JAVA=$JAVA_HOME/bin/java; else JAVA=${JAVA:-java}; fi
DRY=${DRY:-0}
DAY=${DAY:-$(( $(date +%s) / 86400 ))}
BG=
LANES=

# clone_commit FROM DIR: a clone of FROM's HEAD in DIR, with FROM's lean/.lake and
# lean/contractcheck/.lake (no Mathlib, bergdb 028-24), so that lake builds only what changed.
clone_commit() {
    git clone -q "$1" "$2" || return 1
    if [ -d "$1/lean/.lake" ]; then
        cp -R "$1/lean/.lake" "$2/lean/" 2>/dev/null
    fi
    if [ -d "$1/lean/contractcheck/.lake" ]; then
        cp -R "$1/lean/contractcheck/.lake" "$2/lean/contractcheck/" 2>/dev/null
    fi
    return 0
}

run_start() {
    KIND=$1
    NAME=$(echo "$KIND" | tr a-z A-Z)
    FAILED=""
    START=$(date +%s)
    REPO=$(git rev-parse --show-toplevel) || { echo "$NAME FAILED: not in git"; exit 1; }
    RUN=$(pwd)/build/$KIND/$(date +%Y-%m-%d-%H%M)
    SRC=$RUN/repo
    REPORT=$RUN/report.txt
    if [ "$DRY" = 1 ]; then
        echo "$2 (DRY=1: the steps in order, none run; no clone, no report)${3:-}"
        return 0
    fi
    mkdir -p $RUN || exit 1
    clone_commit "$REPO" $SRC || { echo "$NAME FAILED: clone" | tee $REPORT; exit 1; }
    {
        echo "$2 $(basename $RUN) on $(hostname -s)${3:-}"
        echo "Kind: functional"
        echo "Commit: $(git -C $SRC log -1 --format='%h %ad %s' --date=format:'%Y-%m-%d %H:%M')"
        echo "JDK: $($JAVA -version 2>&1 | head -1)"
        if [ -n "${4:-}" ]; then echo "$4"; fi
        echo
    } > $REPORT
}

step() {
    name=$1; shift
    if [ "$DRY" = 1 ]; then
        printf '%-18s %s\n' $name "$*"
        return 0
    fi
    if [ -f $RUN/hang.txt ]; then
        printf '%-18s %-6s %7s   %s\n' $name "-" "" "not run: the hang guard ended the run" >> $REPORT
        return 1
    fi
    s=$(date +%s)
    (cd $SRC/java && "$@") > $RUN/$name.txt 2>&1
    status=$?
    t=$(( $(date +%s) - s ))
    if [ $status = 0 ]; then result=ok; else result=FAILED; FAILED="$FAILED $name"; fi
    last=$(tail -1 $RUN/$name.txt)
    if [ $status != 0 ] && [ -f $RUN/hang.txt ]; then
        last="HANG: killed by the hang guard ($(cat $RUN/hang.txt)); its last line: $last"
    fi
    printf '%-18s %-6s %5d s   %s\n' $name $result $t "$last" >> $REPORT
    return $status
}

step_bg() {
    name=$1
    if [ "$DRY" = 1 ]; then
        shift
        printf '%-18s %s   (beside the next steps, in its own clone)\n' $name "$*"
        return 0
    fi
    lane=$SRC
    if [ ! -f $RUN/hang.txt ]; then
        lane=$RUN/repo-$name
        if ! clone_commit $SRC $lane; then
            printf '%-18s %-6s %7s   %s\n' $name FAILED "" "the clone $lane failed" >> $REPORT
            FAILED="$FAILED $name"
            return 1
        fi
        LANES="$LANES $lane"
    fi
    # The step's line goes to a file of its own, added to the report by step_wait.
    (SRC=$lane; REPORT=$RUN/.line-$name; step "$@") &
    BG="$BG $name:$!"
    # The background step's own shell, which the hang guard spares, so that it writes its line.
    echo $! >> $RUN/.keep
}

step_wait() {
    [ "$DRY" = 1 ] && return 0
    for b in $BG; do
        n=${b%%:*}
        wait ${b#*:}
        if [ -f $RUN/.line-$n ]; then
            # Failed as step notes it: the result FAILED in its line.
            [ "$(awk '{print $2; exit}' $RUN/.line-$n)" = FAILED ] && FAILED="$FAILED $n"
            cat $RUN/.line-$n >> $REPORT
            rm -f $RUN/.line-$n
        else
            printf '%-18s %-6s %7s   %s\n' $n FAILED "" "its shell ended without a line" >> $REPORT
            FAILED="$FAILED $n"
        fi
    done
    BG=
}

# desc ROOTS SPARE KEEP: from ps, ROOTS that are alive and their descendants, but not the
# processes SPARE and theirs, nor the processes KEEP (their descendants yes).
desc() {
    # On one line each: awk -v takes no newline.
    set -- "$(echo $1)" "$(echo $2)" "$(echo $3)"
    ps -A -o pid= -o ppid= | awk -v roots="$1" -v spare="$2" -v keep="$3" '
        { kids[$2] = kids[$2] " " $1; alive[$1] = 1 }
        END {
            split(spare, a, " "); for (i in a) no[a[i]] = 1
            split(keep, b, " "); for (i in b) kp[b[i]] = 1
            n = split(roots, q, " ")
            for (h = 1; h <= n; h++) if (q[h] in alive && !(q[h] in kp) && !(q[h] in no)) print q[h]
            for (h = 1; h <= n; h++) {
                m = split(kids[q[h]], c, " ")
                for (j = 1; j <= m; j++) {
                    if (c[j] in no) continue
                    q[++n] = c[j]
                    if (!(c[j] in kp)) print c[j]
                }
            }
        }'
}

# kill_steps [all]: kills the processes of the steps that run, the descendants of this shell
# at the time of the call: TERM, and after 10 s KILL to those left and their children. Spares
# the hang guard and its children, and, without "all", the background steps' own shells
# (RUN/.keep), so that they write their lines. A process that this shell starts after the
# call, such as run_finish's, is not touched.
kill_steps() {
    spare=$(cat $RUN/.guard 2> /dev/null)
    keep=
    [ "${1:-}" = all ] || keep=$(cat $RUN/.keep 2> /dev/null)
    pids=$(desc $$ "$spare" "$keep" | grep -v "^$$\$")
    [ -n "$pids" ] || return 0
    kill -TERM $pids 2> /dev/null
    for i in 1 2 3 4; do
        sleep 10
        left=$(desc "$pids" "$spare" "$keep")
        [ -n "$left" ] || return 0
        kill -KILL $left 2> /dev/null
    done
}

# run_stop: for a trap of INT and TERM in a script with background steps (week.sh): kills
# every step's processes and the hang guard, and exits with status 130; the run's directory
# and clones stay.
run_stop() {
    kill_steps all
    if [ -n "${GUARD_PID:-}" ]; then kill $GUARD_PID 2> /dev/null; fi
    exit 130
}

run_guard() {
    [ "$DRY" = 1 ] && return 0
    (
        end=$((START + $1))
        while [ $(date +%s) -lt $end ]; do
            sleep 60
            # The run's shell gone (killed, or interrupted): the guard ends too.
            [ "$(ps -o ppid= -p "$(cat $RUN/.guard 2> /dev/null)" 2> /dev/null | tr -d ' ')" = $$ ] \
                || exit 0
        done
        echo "the run had not ended $1 s after its start, at $(date '+%Y-%m-%d %H:%M')" > $RUN/hang.txt
        kill_steps
    ) > /dev/null 2>&1 &
    GUARD_PID=$!
    echo $GUARD_PID > $RUN/.guard
}

keep_traces() {
    for d in "$@"; do
        f=build/traces/$d/failed.txt
        [ -s $f ] || continue
        mkdir -p $RUN/traces/$d
        cp build/traces/$d/configs.txt $RUN/traces/$d/ 2> /dev/null
        sort -u $f | while read t; do
            cp ${t%.trace}.* $RUN/traces/$d/
        done
        echo "kept: $(sort -u $f | wc -l | tr -d ' ') failing traces of build/traces/$d/ in $RUN/traces/$d/"
    done
}

run_finish() {
    [ "$DRY" = 1 ] && return 0
    if [ -n "${GUARD_PID:-}" ]; then kill $GUARD_PID 2> /dev/null; fi
    rm -f $RUN/.guard $RUN/.keep
    # The logs, without the databases and traces; then the clones.
    for d in $SRC $LANES; do
        (cd $d/java/build 2> /dev/null && find . -name '*.txt' -size -20000k | while read f; do
            mkdir -p "$RUN/logs/$(dirname "$f")"
            cp "$f" "$RUN/logs/$f"
        done)
        rm -rf $d
    done

    if [ -f $RUN/hang.txt ]; then
        echo "(the hang guard ended the run: $(cat $RUN/hang.txt))" >> $REPORT
        FAILED="$FAILED hang-guard"
    fi
    echo >> $REPORT
    if [ -z "$FAILED" ]; then
        echo "$NAME OK ($(( ($(date +%s) - START) / 60 )) minutes)" >> $REPORT
    else
        echo "$NAME FAILED:$FAILED ($(( ($(date +%s) - START) / 60 )) minutes)" >> $REPORT
    fi
    cat $REPORT

    # One line in news.md, a local file of background work's results that Git does not
    # track (AGENTS.md, "News"; tools/news.sh).
    if [ -f "$REPO/tools/news.sh" ]; then
        if [ -z "$FAILED" ]; then st=OK; else st=FAILED; fi
        sh "$REPO/tools/news.sh" "$st" $KIND.sh \
            "$(tail -1 $REPORT) on $(sed -n 's/^Commit: \([0-9a-f]*\) .*/\1/p' $REPORT). Report: java/build/$KIND/$(basename $RUN)/report.txt" \
            || echo "$KIND.sh: news.sh failed"
    fi
    [ -z "$FAILED" ]
}
