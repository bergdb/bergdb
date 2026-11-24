#!/bin/sh
# The release's checksums (bergdb 026-27, step 13; 024-38's finish.sh, adapted 2026-11-23 for
# 2026.6: 026, "How the release is made"), after build-a.sh. Called by release.sh, or by hand:
#     sh finish.sh
#   1. R/out/SHA256SUMS of the two files that go to the GitHub release, bergdb-2026.6.jar and
#      bergdb-2026.6-javadoc.zip, as uploaded (shasum -a 256, file names without a directory),
#      checked with shasum -a 256 -c: a user checks the downloads with the same command;
#   2. R/out/baseline.zip from R/out/baseline/ if that directory exists (the outputs of A's
#      gate and its night, put there by the lead; without the GC logs, *.gc.log, if it would
#      pass 10 MB). It is not published and not in SHA256SUMS: it stays with the night's
#      outputs, outside the repository. Without R/out/baseline/ there is no zip, and the
#      result line says so.
# Environment: VERSION (2026.6); R (the release's work directory,
# /Users/f/fl/bench/2026-11-24/release).
# Prints "FINISH OK: ..." with the sizes (exit 0) or "FINISH FAILED: ..." (exit 1).
# Created 2026-11-03 by Frans Lundberg (016-09); 2026.5's copy 2026-11-12; 2026.6's 2026-11-23.
V=${VERSION:-2026.6}
R=${R:-/Users/f/fl/bench/2026-11-24/release}
O=$R/out
fail() { echo "FINISH FAILED: $*"; exit 1; }
for f in "bergdb-$V.jar" "bergdb-$V-javadoc.zip"; do [ -f "$O/$f" ] || fail "no $O/$f (build-a.sh)"; done
cd "$O" || fail "cd $O"
shasum -a 256 "bergdb-$V.jar" "bergdb-$V-javadoc.zip" > SHA256SUMS || fail "shasum"
c=$(shasum -a 256 -c SHA256SUMS 2>&1)
[ "$(echo "$c" | grep -c ': OK$')" = 2 ] && [ "$(wc -l < SHA256SUMS | tr -d ' ')" = 2 ] || fail "shasum -c: $c"
rm -f baseline.zip
if [ -d baseline ]; then
    find baseline -name .DS_Store -delete
    zip -q -r -X baseline.zip baseline || fail "zip of baseline/"
    bl="baseline.zip $(wc -c < baseline.zip | tr -d ' ') bytes, GC logs kept"
    if [ "$(wc -c < baseline.zip)" -gt 10000000 ]; then
        rm -f baseline.zip
        zip -q -r -X baseline.zip baseline -x '*.gc.log' || fail "zip of baseline/ without the GC logs"
        bl="baseline.zip $(wc -c < baseline.zip | tr -d ' ') bytes, GC logs dropped (the zip passed 10 MB)"
    fi
    bl="$bl (not published, not in SHA256SUMS)"
else
    bl="no baseline/, no baseline.zip"
fi
echo "FINISH OK: $(ls -l "bergdb-$V.jar" "bergdb-$V-javadoc.zip" | awk '{printf "%s %d bytes; ", $9, $5}')SHA256SUMS of the two checks; $bl; $O"
