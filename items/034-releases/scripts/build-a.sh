#!/bin/sh
# The release's two files from commit A (bergdb 034-01, step 10; 024-38's build-a.sh, adapted
# for 2026.6 on 2026-11-23: no source zip, GitHub archives the tag; for every release on
# 2026-11-24). Called by release.sh, or by hand:
#     sh build-a.sh A
# In R/a, a new clone of SRC checked out at A (detached):
#   1. "git status --porcelain" empty; the release V and its int are what A's BuildInfo says
#      (V a release, YYYY.N; with VERSION or VERSION_INT set, they must agree);
#      java/src/overview-pub.html names the jar bergdb-V.jar and no other release's jar
#      (commit A sets it, 034-01, step 7);
#   2. java/build.sh (the two jars and build/stress), with Homebrew's JDK;
#   3. java -cp java/build/bergdb-release.jar bergdb.core.BuildInfo prints "release: V",
#      "releaseInt: INT" and "build: V.YYMMDD.HHMM";
#   4. java/javadoc-pub.sh prints JAVADOC PUB OK;
#   5. in R/out: bergdb-V.jar, a copy of java/build/bergdb-release.jar, the users' jar
#      (020-10, section 7); bergdb-V-javadoc.zip, java/build/javadoc-pub/ under
#      bergdb-V-javadoc/, checked with unzip -l; with CANDJAR set (the jar that A's gate
#      or its night tested), the two jars' SHA-256 are noted, not compared: the jar holds
#      build times, so the bytes differ.
# A few minutes. R/out/build-a.txt keeps the record ("release: V" for finish.sh and notes.sh),
# with the JDK's version for the notes.
# Environment: DATE (today); R (the release's work directory, /Users/f/fl/bench/DATE/release);
# SRC (the repository to clone, /Users/f/fl/repos/bergdb); CANDJAR (none); VERSION and
# VERSION_INT (none: A's BuildInfo); JAVA_HOME (/opt/homebrew/opt/openjdk).
# Prints "BUILD A OK: COMMIT, build ..., jar sha256 ..." (exit 0) or "BUILD A FAILED: ..." (exit 1).
# Created 2026-11-03 by Frans Lundberg (016-09); 2026.5's copy 2026-11-12; 2026.6's 2026-11-23;
# for every release 2026-11-24 (bergdb 034).
A=${1:?usage: sh build-a.sh A}
DATE=${DATE:-$(date +%F)}
R=${R:-/Users/f/fl/bench/$DATE/release}
SRC=${SRC:-/Users/f/fl/repos/bergdb}
export JAVA_HOME=${JAVA_HOME:-/opt/homebrew/opt/openjdk}
export PATH=$JAVA_HOME/bin:$PATH
T=$R/a
O=$R/out
REC=$O/build-a.txt
fail() { echo "FAILED: $*" >> "$REC"; echo "BUILD A FAILED: $*"; exit 1; }
mkdir -p "$O" || { echo "BUILD A FAILED: cannot make $O"; exit 1; }
rm -f "$O"/bergdb-*.jar "$O"/bergdb-*-javadoc.zip
echo "build-a.sh $A, $(date '+%F %T'), SRC $SRC" > "$REC"
rm -rf "$T"
git clone -q "$SRC" "$T" || fail "git clone $SRC $T"
C=$(git -C "$T" rev-parse --verify "$A^{commit}" 2>/dev/null) || fail "no commit $A in $SRC"
git -C "$T" checkout -q --detach "$C" || fail "git checkout $C"
echo "commit: $C $(git -C "$T" log -1 --format='%ad %an: %s' --date=format:'%F %T' | cut -c1-160)" >> "$REC"
st=$(git -C "$T" status --porcelain)
[ -z "$st" ] || fail "the clone is not clean: $(echo "$st" | head -n 3 | tr '\n' ' ')"
BI=$T/java/src/bergdb/core/BuildInfo.java
bv=$(sed -n 's/.*String RELEASE = Util\.identity("\([^"]*\)");.*/\1/p' "$BI")
bvi=$(sed -n 's/.*int RELEASE_INT = Util\.identity(\([0-9]*\));.*/\1/p' "$BI")
echo "$bv" | grep -Eqx '[0-9]{4}\.[0-9]+' || fail "A's BuildInfo says '$bv', not a release YYYY.N"
V=${VERSION:-$bv}
VI=${VERSION_INT:-$bvi}
[ "$V" = "$bv" ] && [ "$VI" = "$bvi" ] || fail "A's BuildInfo says $bv, $bvi; VERSION $V, VERSION_INT $VI"
echo "release: $V" >> "$REC"
jars=$(grep -Eo 'bergdb-[0-9]{4}\.[0-9]+\.jar' "$T/java/src/overview-pub.html" | sort -u | tr '\n' ' ')
[ -z "$jars" ] || [ "$jars" = "bergdb-$V.jar " ] || fail "java/src/overview-pub.html names $jars, not bergdb-$V.jar only (commit A sets it)"
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
