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
#   run_finish
#       Copies the clone's *.txt logs (without the databases and traces) to RUN/logs/,
#       deletes the clone, ends the report with "NAME OK (N minutes)" or "NAME FAILED: STEPS
#       (N minutes)", prints it, and adds a line to news.md with tools/news.sh (AGENTS.md,
#       "News"). Returns 1 if a step failed.
#   DAY
#       The day's number (days since 1970), for seeds that are new each day; DAY=N in the
#       environment takes day N's seeds again (bergdb 030-30).
#   keep_traces DIR...
#       In a step, in the clone's java/: copies the traces that build/traces/DIR/failed.txt
#       lists (conformance.sh, treeconf.sh and contractconf.sh write it: the failing traces),
#       each with its outputs (NAME-SEED.*), to RUN/traces/DIR/, which run_finish keeps; so a
#       failing trace of new seeds stays with its seed in its name (bergdb 030-30).
#
# DRY=1: run_start, step and run_finish print the steps with their commands instead of
# running them: no clone, no report, no news entry; a check of a script's steps and order.

if [ -n "${JAVA_HOME:-}" ]; then JAVA=$JAVA_HOME/bin/java; else JAVA=${JAVA:-java}; fi
DRY=${DRY:-0}
DAY=${DAY:-$(( $(date +%s) / 86400 ))}

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
    git clone -q "$REPO" $SRC || { echo "$NAME FAILED: clone" | tee $REPORT; exit 1; }
    if [ -d "$REPO/lean/.lake" ]; then
        cp -R "$REPO/lean/.lake" $SRC/lean/ 2>/dev/null
    fi
    # The contract checkers' .lake (lean/contractcheck/, no Mathlib, bergdb 028-24).
    if [ -d "$REPO/lean/contractcheck/.lake" ]; then
        cp -R "$REPO/lean/contractcheck/.lake" $SRC/lean/contractcheck/ 2>/dev/null
    fi
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
    s=$(date +%s)
    (cd $SRC/java && "$@") > $RUN/$name.txt 2>&1
    status=$?
    t=$(( $(date +%s) - s ))
    if [ $status = 0 ]; then result=ok; else result=FAILED; FAILED="$FAILED $name"; fi
    printf '%-18s %-6s %5d s   %s\n' $name $result $t "$(tail -1 $RUN/$name.txt)" >> $REPORT
    return $status
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
    # The logs, without the databases and traces; then the clone.
    (cd $SRC/java/build && find . -name '*.txt' -size -20000k | while read f; do
        mkdir -p "$RUN/logs/$(dirname "$f")"
        cp "$f" "$RUN/logs/$f"
    done)
    rm -rf $SRC

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
