#!/bin/sh
# bergdb 020-26: the model's runs for a quiet night on F53, one JVM at a time, 8 workers,
# a heap of 12 GB; each run stopped at its cap. Results: a line per run in results.tsv,
# logs in logs/. Part 1 at most 3 h 45 min; part 2 at most 4 h 30 min.
#   sh night.sh 1     (or 2, or both: sh night.sh 1 2)
cd "$(dirname "$0")"
XMX=12g; export XMX
for part in "$@"; do
    case $part in
    1)  sh queue.sh 90 8 cfg/d2-recreate.cfg cfg/d3-writers.cfg
        sh queue.sh 45 8 cfg/d4c-timed-1key.cfg ;;
    2)  sh queue.sh 120 8 cfg/n1-all-1w.cfg
        sh queue.sh 60 8 cfg/l3-live-1key-recreate.cfg cfg/l3-live-1key-2w.cfg
        sh queue.sh 30 8 cfg/sim.cfg -- -simulate num=200000000 -depth 120 ;;
    esac
done
