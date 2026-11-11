#!/bin/sh
# T7's runner (bergdb 024-07): t7.sh VARIANT CMD dir=... args...
# VARIANT is main (the clone at main's head, release 2026.4's code) or fix (the branch
# 024-07-last-touch): $B/VARIANT.jar is that build's bergdb.jar, $B/cVARIANT the probe's
# classes compiled against it. The JVM settings are 024-03's (PF1's pf1.sh).
B=/Users/f/fl/bench/2026-11-11/touch
V=$1; shift
exec /opt/homebrew/opt/openjdk/bin/java -Xms8g -Xmx8g -XX:+UseG1GC -cp $B/c$V:$B/$V.jar bergdb.core.T7 "$@"
