#!/bin/sh
# bergdb 005-01: runs M49Probe against a build of BergDB.
#
# Usage: probe.sh JAR CLASS_DIR
#   JAR: a bergdb.jar (java/build.sh); CLASS_DIR: an empty directory for the probe's
#   classes. probe-before.txt is the output with the build of cbeb9bd (before the fix),
#   probe-after.txt with the fix.

set -e
HERE=$(cd "$(dirname "$0")" && pwd)
mkdir -p "$2"
javac --release 8 -nowarn -Xlint:-options -cp "$1" -d "$2" "$HERE/M49Probe.java"
java -cp "$1:$2" bergdb.core.M49Probe
