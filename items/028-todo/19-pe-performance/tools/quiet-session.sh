#!/bin/sh
# bergdb 028-19: the quiet session of the night: SetLoop ABBA (main against the short way's
# change), then the Perf times of jobs-times.txt. Detached; each JVM after run.sh's quiet check.
D=$(cd "$(dirname "$0")/.." && pwd)
sh "$D/tools/setloop.sh" "$D/out-setloop1" 30 main-a sw3-b sw3-c main-d
QUIET=1 sh "$D/tools/run.sh" "$D/tools/jobs-times.txt" "$D/out-times"
echo "QUIET SESSION END $(date)" >> "$D/out-times/log.txt"
