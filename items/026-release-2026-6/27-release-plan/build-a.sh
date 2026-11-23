#!/bin/sh
# The release's two files from commit A (bergdb 026-27, step 13; 024-38's build-a.sh, adapted
# 2026-11-23 for 2026.6: no source zip, GitHub archives the tag; 026, "How the release is
# made"). Called by release.sh, or by hand:
#     sh build-a.sh A
# In R/a, a new clone of SRC checked out at A (detached):
#   1. "git status --porcelain" empty;
#   2. java/build.sh (the two jars and build/stress), with Homebrew's JDK;
#   3. java -cp java/build/bergdb-release.jar bergdb.core.BuildInfo prints "release: 2026.6",
#      "releaseInt: 266" and "build: 2026.6.YYMMDD.HHMM";
#   4. java/javadoc-pub.sh prints JAVADOC PUB OK;
#   5. in R/out: bergdb-2026.6.jar, a copy of java/build/bergdb-release.jar, the users' jar
#      (020-10, section 7); bergdb-2026.6-javadoc.zip, java/build/javadoc-pub/ under
#      bergdb-2026.6-javadoc/, checked with unzip -l; with CANDJAR set (the jar that A's gate
#      or its night tested), the two jars' SHA-256 are noted, not compared: the jar holds
#      build times, so the bytes differ.
# A few minutes. R/out/build-a.txt keeps the record, with the JDK's version for the notes.
# Environment: R (the release's work directory, /Users/f/fl/bench/2026-11-24/release); SRC
# (the repository to clone, /Users/f/fl/repos/bergdb); CANDJAR (none); VERSION (2026.6);
# VERSION_INT (266); JAVA_HOME (/opt/homebrew/opt/openjdk).
# Prints "BUILD A OK: COMMIT, build ..., jar sha256 ..." (exit 0) or "BUILD A FAILED: ..." (exit 1).
# Created 2026-11-03 by Frans Lundberg (016-09); 2026.5's copy 2026-11-12; 2026.6's 2026-11-23.
A=${1:?usage: sh build-a.sh A}
R=${R:-/Users/f/fl/bench/2026-11-24/release}
SRC=${SRC:-/Users/f/fl/repos/bergdb}
V=${VERSION:-2026.6}
VI=${VERSION_INT:-266}
export JAVA_HOME=${JAVA_HOME:-/opt/homebrew/opt/openjdk}
export PATH=$JAVA_HOME/bin:$PATH
T=$R/a
O=$R/out
REC=$O/build-a.txt
fail() { echo "FAILED: $*" >> "$REC"; echo "BUILD A FAILED: $*"; exit 1; }
mkdir -p "$O" || { echo "BUILD A FAILED: cannot make $O"; exit 1; }
rm -f "$O/bergdb-$V.jar" "$O/bergdb-$V-javadoc.zip"
echo "build-a.sh $A, $(date '+%F %T'), SRC $SRC" > "$REC"
rm -rf "$T"
git clone -q "$SRC" "$T" || fail "git clone $SRC $T"
C=$(git -C "$T" rev-parse --verify "$A^{commit}" 2>/dev/null) || fail "no commit $A in $SRC"
git -C "$T" checkout -q --detach "$C" || fail "git checkout $C"
echo "commit: $C $(git -C "$T" log -1 --format='%ad %an: %s' --date=format:'%F %T' | cut -c1-160)" >> "$REC"
st=$(git -C "$T" status --porcelain)
[ -z "$st" ] || fail "the clone is not clean: $(echo "$st" | head -n 3 | tr '\n' ' ')"
jv=$(java -version 2>&1 | head -n 1)
echo "jdk: $jv" >> "$REC"
(cd "$T/java" && sh build.sh) > "$O/build-a-build.txt" 2>&1 || fail "java/build.sh: $(tail -n 2 "$O/build-a-build.txt" | tr '\n' ' ')"
JAR=$T/java/build/bergdb-release.jar
[ -f "$JAR" ] || fail "no $JAR after build.sh"
bi=$(java -cp "$JAR" bergdb.core.BuildInfo 2>&1)
echo "$bi" >> "$REC"
echo "$bi" | grep -qx "release: $V" || fail "BuildInfo: not release $V: $(echo "$bi" | tr '\n' ' ')"
echo "$bi" | grep -qx "releaseInt: $VI" || fail "BuildInfo: not releaseInt $VI: $(echo "$bi" | tr '\n' ' ')"
echo "$bi" | grep -Eqx "build: $(echo "$V" | sed 's/\./\\./g')\.[0-9]{6}\.[0-9]{4}" || fail "BuildInfo: build not $V.YYMMDD.HHMM: $(echo "$bi" | tr '\n' ' ')"
jd=$(cd "$T/java" && sh javadoc-pub.sh 2>&1 | tail -n 1)
echo "$jd" >> "$REC"
case $jd in "JAVADOC PUB OK"*) ;; *) fail "javadoc-pub.sh: $jd" ;; esac
cp "$JAR" "$O/bergdb-$V.jar" || fail "cannot copy the jar"
S=$O/stage-javadoc
rm -rf "$S" && mkdir -p "$S" && cp -R "$T/java/build/javadoc-pub" "$S/bergdb-$V-javadoc" || fail "cannot stage the Javadoc"
(cd "$S" && find . -name .DS_Store -delete && zip -q -r -X "$O/bergdb-$V-javadoc.zip" "bergdb-$V-javadoc") || fail "zip of the Javadoc"
rm -rf "$S"
unzip -l "$O/bergdb-$V-javadoc.zip" | grep -q " bergdb-$V-javadoc/index.html$" || fail "the Javadoc zip has no index.html"
for f in "bergdb-$V.jar" "bergdb-$V-javadoc.zip"; do
    echo "$(shasum -a 256 "$O/$f" | cut -d' ' -f1)  $f  $(wc -c < "$O/$f" | tr -d ' ') bytes" >> "$REC"
done
if [ -n "${CANDJAR:-}" ]; then
    echo "the tested jar $CANDJAR: $(shasum -a 256 "$CANDJAR" 2>&1 | cut -d' ' -f1) (not compared: build times differ)" >> "$REC"
fi
js=$(shasum -a 256 "$O/bergdb-$V.jar" | cut -d' ' -f1)
echo "BUILD A OK" >> "$REC"
echo "BUILD A OK: $(echo "$C" | cut -c1-8), $(echo "$bi" | grep '^build:' | cut -d' ' -f2); jar sha256 $js; $(du -h "$O/bergdb-$V.jar" "$O/bergdb-$V-javadoc.zip" | awk '{printf "%s %s, ", $2, $1}' | sed "s|$O/||g; s/, $//"); $REC"
