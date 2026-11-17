#!/bin/sh
# bergdb 006-05, T2: the step of a git bisect over F1-007's history of BergDB
# (a clone of a/007-bergdb-261012/bergdb-git.bundle in the f1 repository),
# with the terms broken (old) and fixed (new): does StartupDistanceTester pass
# when its second phase pays till 3.0e6 instead of 4.0e6?
#
# Usage, in the clone:
#   git bisect start 50786b2 2d5c2a3 --term-old=broken --term-new=fixed
#   git bisect run sh /path/to/bisect-step.sh /path/to/bergdb/java/build.sh
# The build is bergdb's java/build.sh without its stress tests, run in the
# clone's bergdb/ (src, src-dev, src-icu, in). Exit 0: broken (the test
# fails); 1: fixed (it passes); 125: skip (no build, or no such line).
BUILD=$1
cd "$(git rev-parse --show-toplevel)/bergdb" || exit 125
git checkout -q -- .
python3 -I - <<'PY' || exit 125
p = 'src-dev/bergdb/test/StartupDistanceTester.java'
s = open(p).read()
old = '''        //payTillStreamSize(3.0e6);   // NOTE result in problems
        payTillStreamSize(4.0e6);'''
if s.count(old) != 1:
    raise SystemExit(1)
open(p, 'w').write(s.replace(old, '        payTillStreamSize(3.0e6);'))
PY
sed -e '/stress\/\*\.java/d' -e '/Built stress tests/d' "$BUILD" > bisect-build.sh
sh ./bisect-build.sh > /dev/null 2>&1 || { git checkout -q -- .; exit 125; }
timeout 300 java -ea -cp build/bergdb.jar bergdb.test.StartupDistanceTester > bisect-last.txt 2>&1
r=$?
git checkout -q -- .
[ $r -eq 0 ] && exit 1
grep -q -E 'Error|Exception' bisect-last.txt && exit 0
exit 125
