#!/bin/sh
# The kill-and-restart harness of the Pub layer (bergdb 020-15): objects and user indexes
# under a real kill of the process. bergdb.pubimp.KillRestartHarness's parent starts a child
# JVM on a database directory, kills it with SIGKILL (Process.destroyForcibly()) at a random
# moment, and starts the next child on the directory, a new database every PER_DB kills.
# Each child checks the database against a journal of what the earlier children did (the
# start works; the state is a prefix of what the killed child committed, with every synced
# transaction; the data, the index definitions, entries, markers and jobs as bergdb 020-10
# says), then runs a random schedule of writer threads and an index thread until it is
# killed. The class Javadoc has the details. Not a commit gate.
#
# Usage: java/stress/kill-restart.sh [KILLS [SEED]]
#   First the harness's self-check (each of four planted faults must be found; about 10
#   seconds) and its check of a late exit (bergdb 028-20; about 3 seconds), then KILLS kills
#   (default 1000; 0: the checks only), from SEED (default: the date, YYYYMMDD; printed).
#   About 20 minutes for 1,000 kills on F53 (2026-11-09).
#
# Environment: JAVA_HOME (the JDK; the PATH's otherwise), PER_DB (kills per database,
# default 40), LIMIT_S (a time limit for the kills, in seconds; default none). Builds with
# build.sh, then runs on a copy of build/bergdb.jar in build/kill-restart/, so that build.sh
# may run meanwhile. The output is in build/kill-restart/out.txt; a failure keeps its database
# directory and journal there (the last lines say which). Exits with status 1 unless it
# prints KILL RESTART OK.

cd "$(dirname "$0")/.." || exit 1

if [ -n "${JAVA_HOME:-}" ]; then JAVA=$JAVA_HOME/bin/java; else JAVA=${JAVA:-java}; fi
KILLS=${1:-1000}
SEED=${2:-$(date +%Y%m%d)}
PER_DB=${PER_DB:-40}
LIMIT_S=${LIMIT_S:-1000000}
LOG=build/kill-restart

fail() {
    echo "KILL RESTART FAILED: $1 (log: java/$LOG/out.txt)"
    exit 1
}

./build.sh > /dev/null || { echo "KILL RESTART FAILED: build"; exit 1; }
mkdir -p $LOG
rm -rf $LOG/dbs $LOG/selfcheck $LOG/lateexit
rm -f $LOG/out.txt
cp build/bergdb.jar $LOG/bergdb.jar
CP=$LOG/bergdb.jar

echo "Kill-restart harness: seed $SEED, $KILLS kills, a new database every $PER_DB" |
    tee $LOG/out.txt
$JAVA -cp $CP bergdb.pubimp.KillRestartHarness selfcheck $LOG/selfcheck $SEED >> $LOG/out.txt 2>&1
grep '^The planted\|^SELF-CHECK' $LOG/out.txt
grep -q '^SELF-CHECK OK' $LOG/out.txt || fail "self-check"
$JAVA -cp $CP bergdb.pubimp.KillRestartHarness lateexit $LOG/lateexit $SEED >> $LOG/out.txt 2>&1
grep '^LATE EXIT' $LOG/out.txt
grep -q '^LATE EXIT OK' $LOG/out.txt || fail "late exit"
if [ "$KILLS" -gt 0 ]; then
    $JAVA -cp $CP bergdb.pubimp.KillRestartHarness parent $LOG/dbs $SEED $KILLS $PER_DB \
        $LIMIT_S >> $LOG/out.txt 2>&1
    grep '^Kills by phase\|^Counts\|^KILL RESTART' $LOG/out.txt
    grep -q '^KILL RESTART OK' $LOG/out.txt || fail "kills"
else
    echo "KILL RESTART OK: the checks only"
fi
