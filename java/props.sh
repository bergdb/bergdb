#!/bin/sh
# The Props performance tests (bergdb.dev.props.Props, the 2014 to 2017
# property suite; bergdb item 006-02): MEM, heap bytes per KV; CORE, the
# speed of four Core tests (1.00 = cissi, July 2013); SS, stream bytes per
# user byte. Run without -ea, as in 2014 to 2017, since assertions slow the
# code down. MEM and SS do not depend on the machine; CORE depends on the
# machine and on what else runs. Not a gate; level1.sh checks MEM and SS
# against limits.
#
# Usage: java/props.sh
#
# Builds with build.sh, then runs the tests. Prints their output and keeps a
# copy in build/test/props.txt. Exits with status 1 unless the output has
# the MEM, CORE and SS lines. Set JAVA_HOME or PATH for the JDK; the build
# needs javac too.
#
# Kind: timing (bergdb 028-23) for CORE, whose figure means something only on a quiet
# machine (timing.sh compares it with the last release's); MEM and SS do not depend on
# speed (level1.sh checks them).

cd "$(dirname "$0")"
echo "Kind: timing"

JAVA=${JAVA:-java}
if [ -n "$JAVA_HOME" ]; then JAVA=$JAVA_HOME/bin/java; fi

LOG=build/test/props.txt

./build.sh > /dev/null || { echo "PROPS FAILED: build"; exit 1; }
mkdir -p build/test
$JAVA -cp build/bergdb.jar bergdb.dev.props.Props 2>&1 | tee $LOG
for p in MEM CORE SS; do
    grep -q "$p:[0-9]" $LOG || { echo "PROPS FAILED: no $p (log: java/$LOG)"; exit 1; }
done
