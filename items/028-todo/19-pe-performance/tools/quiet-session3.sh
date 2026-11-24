#!/bin/sh
# bergdb 028-19: the third quiet session: CCBench at 10M (jobs-cc2.txt), r1 against sw and old.
D=$(cd "$(dirname "$0")/.." && pwd)
QUIET=1 sh "$D/tools/run2.sh" "$D/tools/jobs-cc2.txt" "$D/out-cc"
echo "QUIET SESSION 3 END $(date)" >> "$D/out-cc/log.txt"
