#!/bin/sh
# Compiles ReplicaProbe against java/build/bergdb.jar of this tree and runs one probe.
# Usage (from anywhere): items/005-todo/11-replication/tools/run.sh PROBE [args]
# Build first with java/build.sh. Temporary files go to java.io.tmpdir, or to the
# directory in PROBE_TMP. See ReplicaProbe.java for the probes.
#
# Assertions are on, but not in MemoryStream: its copy() fails an assertion for a stream
# whose length is a multiple of 1,000,000 bytes (assertOk expects one array too many),
# which the cut images of probe P2 hit now and then.

set -e
cd "$(dirname "$0")/../../../.."
OUT=java/build/replicaprobe
mkdir -p $OUT
javac --release 8 -Xlint:-options -nowarn -cp java/build/bergdb.jar -d $OUT \
    items/005-todo/11-replication/tools/ReplicaProbe.java
TMP_OPT=
if [ -n "$PROBE_TMP" ]; then TMP_OPT="-Dtmp=$PROBE_TMP"; fi
exec java -ea -da:bergdb.stream.MemoryStream -Xmx2g $TMP_OPT \
    -cp java/build/bergdb.jar:$OUT bergdb.core.ReplicaProbe "$@"
