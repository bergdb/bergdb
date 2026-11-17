#!/bin/sh
# 006-02: the sets of runs of plan.md, as they were run.
#
#   phases.sh N...    runs the phases named, 1 to 9
#
# On 2026-10-19: 1 and 2 ran 13:31 to 14:01, 3 to 5 14:03 to 14:28, 6 first at
# 14:31 to 14:38, then 6 to 9 from 14:45. Before 3 to 5: run.sh build orig-HASH for
# each commit of phase 5; before 9: run.sh maphash.

set -e
cd "$(dirname "$0")"
R=./run.sh
P1="-XX:+UseParallelGC"
P2="-XX:+UseParallelGC -XX:-UseCompactObjectHeaders"
D20=20000000
D50=50000000

for p in "$@"; do
    case "$p" in
        1)  # The main comparison: ten Props runs of each, default flags.
            $R ab main 5 2017-08-01 2026-10-19;;
        2)  # The code that cissi ran: six Props runs of each.
            $R ab cissi 3 2015-12-28 2017-07-29;;
        3)  # The collector and the object header of Java 7 and 8: two runs of each.
            JFLAGS=$P1 $R ab parallel 1 2015-12-28 2017-07-29
            JFLAGS=$P1 $R ab parallel 1 2017-08-01 2026-10-19
            JFLAGS=$P2 $R ab parallel-nocoh 1 2015-12-28 2017-07-29
            JFLAGS=$P2 $R ab parallel-nocoh 1 2017-08-01 2026-10-19;;
        4)  # The startup distance, 20 MB (2017's default) and 50 MB (2026's).
            for v in 2017-08-01 2026-10-19; do
                for d in $D20 $D50; do
                    $R class $v probe Probe006 ss $d
                done
            done
            for i in 1 2; do
                for v in 2017-08-01 2026-10-19; do
                    for d in $D20 $D50; do
                        $R class $v probe Probe006 mem $d
                        $R class $v probe Probe006 set $d
                    done
                done
            done;;
        5)  # Where between 2017-07-29 and 2017-08-01 (and the parent of the
            # 2015-12-28 commit): one Props run of each original commit.
            for c in 7a1c65e e5a21cb e8cb6e1 2b00ae3 d8cd765 3a89728 5268b64 \
                    9f5b89b 075eb5b 6758194 58ab1d0; do
                $R one orig-$c sweep
            done;;
        6)  # Added after 3 to 5: four more parallel-collector runs of the main pair
            # (phase 3 gave the 2026 code a faster get in its two runs). Run twice:
            # six runs of the first time overlapped the session's own work
            # (runs/disturbed/).
            JFLAGS=$P1 $R ab parallel 2 2017-08-01 2026-10-19;;
        7)  # Replacements for the runs of phases 1 and 3 in runs/disturbed/.
            $R one 2026-10-19 main; sleep 10
            $R one 2017-08-01 main; sleep 10
            $R one 2026-10-19 main; sleep 10
            JFLAGS=$P1 $R one 2015-12-28 parallel;;
        8)  # The four-thread test with other work on the machine: one busy process
            # (yes) during the run, against none.
            for i in 1 2; do
                $R one 2026-10-19 load-none; sleep 10
                (
                    yes > /dev/null &
                    y=$!
                    trap "kill $y" EXIT
                    IDLEMIN=0 $R one 2026-10-19 load-yes
                ); sleep 10
            done;;
        9)  # The experiment of maphash.patch (run.sh maphash first): the node
            # table's map index, against the 2026 code.
            $R ab maphash 2 2026-10-19 2026-10-19-maphash
            for i in 1 2; do
                for v in 2026-10-19 2026-10-19-maphash; do
                    $R class $v probe-maphash Probe006 set $D50
                done
            done;;
        *)
            echo "phases.sh: unknown phase $p" >&2; exit 2;;
    esac
done
