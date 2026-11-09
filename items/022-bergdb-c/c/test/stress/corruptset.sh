#!/bin/sh
# The corrupt-stream set (bergdb 022-01, step 4, D4; 012-18, section 3.2, "The new harnesses
# for C", and section 4, point 5): damaged copies of streams that the release's Java writes,
# made as database directories by test/cross/java/CorruptSet.java with the release's own
# classes, nothing of Java changed. Harness 6.1's copies (CorruptStreamTester, bergdb 018-02
# to 018-08), by class, on its sample run's random choices: truncation, flip, header (a
# record's size, time, startupPos, topPos, got-dirty entry or count set), node (a node's
# field changed, its checksum made right: 019-32's damage, which corrupt.sh's bit flips do
# not reach), cut out; testFound019_32's ten copies, and testFound021_11's three and
# testFound021_12's three (bergdb 021-11 and 021-12, release 2026.4); and the cases of the
# release's refusal
# tests on the streams those tests write: DbTesterRestart's testEnlargedRecordSizeRefused
# (015-72), testCorruptStartupPosRefused, testCorruptGotDirtyIdRefused and
# testOlderTopPosRefused (015-75), testMetaBlockLastTransPosRefused (019-34) and
# testVersionHighBytesRefused (019-01), and StoredKeyNode.testRefusesBadKlongs's and
# StoredValueNode.testRefusesBadKey's changes (019-32) made to every node of a stream.
#
# Each copy is started by both dumpers, Java's Dump and C's bergdb-dump of the test build
# (under AddressSanitizer and UndefinedBehaviorSanitizer), each on a copy of its own (C's
# with -check: the start's check by node id of its links, 005-57, which Java's runs under
# -ea, and which refuses testFound021_11's third copy), and
# checked as corrupt.sh checks: the same exit status and the same text (a refused start
# prints "start error=NAME", Java's exception's name); where both started and a read failed
# later (Java's status 3, C's 5), Java's text a prefix of C's and the same position; C never
# crashes (no sanitizer report, no signal); when C refuses the start, C's copy is as it was
# (C never writes into a database it refuses), but for 014-01's known case, as harness 6.1
# counts it (Frans's decision): recovery's zero fill of a damaged size written, then the
# start refused, by both, the two directories alike; when both start, both directories
# alike after the starts. And the messages (022-01, "Texts"): a refused start's exception
# name and message, Java's (Dump's line on standard error) and C's (bergdb-dump's), byte
# for byte, C's cut at its 239 bytes; a failed read's likewise, Java's from its stack
# trace, where Java's DbFailedException holds the read's exception as its cause and C's
# text is "A read failed: " and the cause's message (src/sdb.c, fail_on_storage). A
# StreamIoException's message is compared as any other: C's is Java's, the inner
# exception's message (022-02, D6, Frans, 2026-11-09; until then a known departure,
# counted, not failed: 012-14, section 6.4's open choice). One departure is counted, not
# failed (node_text): Java's texts of KeyNode.validateStreamNode that print the key node
# (KeyNode.toString, with Object.toString's identity hash), which no program gives, against
# C's own text of the same check (bergdb 021-12's start meets them). Java writing into a
# database that it refuses is reported, not counted.
#
# Usage: test/stress/corruptset.sh [quick]
#   quick    the gate's set (before-commit.sh), about 60 copies, a few seconds: the refusal
#            tests' cases and testFound019_32's, testFound021_11's and testFound021_12's
#            copies only, the node tests' changes on the first and the last node that takes
#            each
#   OUT      (environment) /Users/f/fl/bench/022/out/corruptset by default, or
#            /Users/f/fl/bench/022/out/corruptset-quick
#   CBUILD   (environment) C's builds, build/ by default
#   SEEDS    (environment) harness 6.1's seeds, "1" by default (testSample's copies)
#   JOBS     (environment) dumps at once on each side, 4 by default
#   CONTROL  (environment) REV: the negative control. C at REV (a commit of this
#            repository, such as 86dade8, the port of 2026.2 before step 2), its c/ taken
#            by git archive into OUT/control and built there, takes C's side; it must
#            differ from Java in every base of the refusal tests' cases and of
#            testFound019_32, testFound021_11 and testFound021_12 (C before 022-02, step 2,
#            such as 3e3b704, differs in found-long-1 and found-long-3971358 alone, and C
#            before 022-02's re-pin, such as 0e4e27f, in found-long-3971358 alone). Prints
#            CORRUPTSET CONTROL CAUGHT or CORRUPTSET CONTROL MISSED.
# Needs C's test build and build/java/classes (test/cross/java-build.sh). Prints
# CORRUPTSET OK or CORRUPTSET FAILED; the copies are removed when the set passes, and OUT
# keeps list.txt (each copy, with harness 6.1's own outcome of it), results.txt (each
# copy's outcome here) and differences.txt. 6.1's
# copies whose start makes recovery's zero fill pass 1 MB (014-01) are left out, as the
# tester counts them (CorruptSet.java). The script is one compound command, read whole
# before it runs.

{
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
CDIR=$(cd "$HERE/../.." && pwd)
case ${1:-} in
quick) Q=-quick; DEF=corruptset-quick ;;
"") Q=; DEF=corruptset ;;
*) echo "Usage: test/stress/corruptset.sh [quick]"; exit 2 ;;
esac
OUT=${OUT:-/Users/f/fl/bench/022/out/$DEF}
CBUILD=${CBUILD:-$CDIR/build}
SEEDS=${SEEDS:-1}
JOBS=${JOBS:-4}
CONTROL=${CONTROL:-}
[ -n "${JAVA_HOME:-}" ] || JAVA_HOME=/opt/homebrew/opt/openjdk
JAVA=$JAVA_HOME/bin/java
CLASSES=$CDIR/build/java/classes
export ASAN_OPTIONS=exitcode=86
T0=$(date +%s)

[ -d "$CLASSES/bergdb" ] || { echo "no $CLASSES: test/cross/java-build.sh"; echo "CORRUPTSET FAILED"; exit 1; }
rm -rf "$OUT"; mkdir -p "$OUT"
if [ -n "$CONTROL" ]; then
    mkdir -p "$OUT/control"
    if ! (cd "$CDIR" && git archive --format=tar "$CONTROL" .) | tar -x -C "$OUT/control" \
            || ! (cd "$OUT/control" && ./build.sh) > "$OUT/control-build.txt" 2>&1; then
        tail -5 "$OUT/control-build.txt" 2> /dev/null
        echo "CORRUPTSET FAILED: C at $CONTROL not built"
        exit 1
    fi
    CBUILD=$OUT/control/build
fi
[ -x "$CBUILD/test/bergdb-dump" ] || { echo "no $CBUILD/test/bergdb-dump"; echo "CORRUPTSET FAILED"; exit 1; }

# shellcheck disable=SC2086
if ! "$JAVA" -ea -Xmx2g -cp "$CLASSES" bergdb.core.CorruptSet $Q "$OUT" $SEEDS \
        > "$OUT/make.txt" 2>&1; then
    tail -20 "$OUT/make.txt"
    echo "CORRUPTSET FAILED: the copies (the tester failed one, or the tool)"
    exit 1
fi
: > "$OUT/scan.jobs"
for b in "$OUT"/base/*; do
    echo "scan $b/scan.txt $b/db" >> "$OUT/scan.jobs"
done
"$JAVA" -ea -Xmx1g -cp "$CLASSES" bergdb.core.Batch "$OUT/scan.jobs" > "$OUT/scan.log" 2>&1
awk -v O="$OUT" '{ split($1, p, "/"); d = O "/v/" $1; s = O "/base/" p[1] "/scan.txt"
    print "dump " d "/dump-a.txt " d "/a " s > (O "/dump-a.jobs")
    print d "/dump-b.txt -check " d "/b " s > (O "/dump-b.jobs") }' "$OUT/list.txt"
NV=$(wc -l < "$OUT/list.txt" | tr -d ' ')
echo "copies: $NV, made in $(( $(date +%s) - T0 )) s; $(tail -1 "$OUT/make.txt")"

"$JAVA" -ea -Xmx2g -cp "$CLASSES" bergdb.core.CorruptSet -dump "$JOBS" "$OUT/dump-a.jobs" \
    > "$OUT/dump-a.log" 2>&1 &
pa=$!
# shellcheck disable=SC2016
xargs -P "$JOBS" -L 1 sh -c 'out=$1; shift; "$0" "$@" < /dev/null > "$out" 2> "$out.err"
    echo $? > "$out.exit"' "$CBUILD/test/bergdb-dump" < "$OUT/dump-b.jobs" 2> "$OUT/dump-b.log"
wait $pa
echo "dumps: $(( $(date +%s) - T0 )) s; Java's: $(tail -1 "$OUT/dump-a.log")"

python3 -I - "$OUT" "$CONTROL" <<'EOF'
import os, re, sys
out, control = sys.argv[1], sys.argv[2]
fails, notes, results = [], [], []
counts, by_base = {}, {}
TEXT = 239                      # C's text, cut at ERR_TEXT - 1 bytes (src/err.h)

def read(p):
    try:
        with open(p, 'rb') as f:
            return f.read()
    except OSError:
        return None

def tree(d):
    """A directory's files: name -> bytes, a directory as None."""
    t = {}
    for root, dirs, files in os.walk(d):
        for n in dirs:
            t[os.path.relpath(os.path.join(root, n), d) + '/'] = None
        for n in files:
            t[os.path.relpath(os.path.join(root, n), d)] = read(os.path.join(root, n))
    return t

def java_error(err):
    """Java's exception at the start (Dump's line) or of a read (the stack trace's first
    line, and a DbFailedException's cause): (simple name, message, the cause's simple
    name or None), or None."""
    lines = err.decode('utf-8', 'replace').splitlines()
    for i, line in enumerate(lines):
        m = re.match(r'Dump: the start failed: (\w+), (.*)$', line)
        if m:
            return m.group(1), m.group(2), None
        m = re.match(r'(?:[\w$]+\.)*(\w+(?:Exception|Error))(?:: (.*))?$', line)
        if m:
            name, msg = m.group(1), m.group(2) if m.group(2) is not None else 'null'
            for c in lines[i + 1:]:
                cm = re.match(r'Caused by: (?:[\w$]+\.)*(\w+)(?:: (.*))?$', c)
                if cm and name == 'DbFailedException':
                    return name, 'A read failed: ' + (cm.group(2) or 'null'), cm.group(1)
            return name, msg, None
    return None

def node_text(j, c):
    """KeyNode.validateStreamNode's texts that print the key node, which a start meets since
    bergdb 021-12 (found-long-3971358/2): Java's holds KeyNode.toString, and so
    Object.toString's identity hash ("K/3a"), and KeyNode.print's lines after it, which no
    other program gives; C's is its own text of the same check. Counted, not failed: Java's
    message taken as C's where both name the same check."""
    if j is None or c is None or j[0] != 'StreamFormatException' or c[0] != j[0]:
        return j, c
    node = r'K/\S+( -?\d+:-?\d+)?( L)?'
    for jp, cm in ((r'Bad spos of pointer \d+ of node %s\.$' % node, 'Bad spos of pointer'),
                   (r'Bad spos of pointer \d+ of node %s$' % node,
                    'Bad spos of pointer, at or before the startup time'),
                   (r'Key node with size -?\d+, %s\.$' % node, 'Key node with size 0')):
        if re.match(jp, j[1]) and c[1] == cm:
            count("known: Java's text prints the key node (KeyNode.toString's identity hash)")
            return (j[0], c[1], j[2]), c
    return j, c

def c_error(err):
    for line in err.decode('utf-8', 'replace').splitlines():
        m = re.match(r'bergdb-dump: (?:the start|a getMany|a getOne) failed: (\w+), (.*)$', line)
        if m:
            return m.group(1), m.group(2)
    return None

def same_message(j, c):
    """True if the names are equal and the messages too, C's cut at its TEXT bytes;
    a StreamIoException's too (022-02, D6)."""
    if j is None or c is None:
        return False
    if j[0] != c[0]:
        return False
    jm = j[1].encode('utf-8')
    cm = c[1].encode('utf-8')
    return jm == cm or (len(cm) == TEXT and jm[:TEXT] == cm)

def messages(j, c, what):
    if not same_message(j, c):
        fail('the %s: Java %s, C %s' % (what, j[:2] if j else j, c))

def count(k):
    counts[k] = counts.get(k, 0) + 1

with open(os.path.join(out, 'list.txt'), encoding='utf-8') as f:
    lines = [l.rstrip('\n') for l in f]
for line in lines:
    v, kind, what = line.split(' ', 2)
    base = v.split('/')[0]
    family = 'case' if base.startswith('case-') else 'found' if base.startswith('found-') else '6.1'
    d = os.path.join(out, 'v', v)
    a, b = os.path.join(d, 'dump-a.txt'), os.path.join(d, 'dump-b.txt')
    ea = (read(a + '.exit') or b'missing').decode().strip()
    eb = (read(b + '.exit') or b'missing').decode().strip()
    ta, tb = read(a) or b'', read(b) or b''
    erra, errb = read(a + '.err') or b'', read(b + '.err') or b''
    n0 = len(fails)
    def fail(why):
        fails.append('%s (%s %s): %s' % (v, kind, what[:150], why))
    if (b'Sanitizer' in errb or b'runtime error' in errb or not eb.isdigit()
            or int(eb) >= 86):
        fail('C crashed (exit %s): %s' % (eb, errb.decode('utf-8', 'replace')[:300]))
        outcome = 'C crashed'
    elif ea == '3' and eb == '5':
        la = ta.splitlines(True)
        if tb.splitlines(True)[:len(la)] != la:
            fail("a read failed after the start, and Java's text is not a prefix of C's")
        pa = re.findall(rb'spos:* ([0-9]+)', erra)[:1]
        pb = re.findall(rb'spos:* ([0-9]+)', errb)[:1]
        if pa != pb:
            fail("the failed reads' positions: Java %s, C %s" % (pa, pb))
        j, c = node_text(java_error(erra), c_error(errb))
        messages(j, c, 'failed reads')
        outcome = 'read failed (%s)' % (c[0] if c else '?')
    else:
        if ea != eb:
            fail('exit status Java %s, C %s' % (ea, eb))
        if ta != tb:
            la, lb = ta.splitlines(), tb.splitlines()
            i = 0
            while i < min(len(la), len(lb)) and la[i] == lb[i]:
                i += 1
            fail('the dumps differ at line %d: Java %r, C %r' % (i + 1,
                    la[i][:120] if i < len(la) else 'END', lb[i][:120] if i < len(lb) else 'END'))
        src = tree(os.path.join(d, 'src'))
        if eb != '0':
            tb_, ta_ = tree(os.path.join(d, 'b')), tree(os.path.join(d, 'a'))
            if tb_ != src and ea == eb and ta_ == tb_:
                count('known 014-01: both wrote the zero fill, then refused')
            elif tb_ != src:
                fail('C refused the start and changed the directory')
            elif ta_ != src:
                notes.append('note: %s: Java refused the start and changed the directory' % v)
            if eb == '1':
                j, c = node_text(java_error(erra), c_error(errb))
                messages(j, c, 'refusals')
                outcome = 'refused (%s)' % (c[0] if c else '?')
            else:
                outcome = 'exit %s' % eb
        else:
            if tree(os.path.join(d, 'a')) != tree(os.path.join(d, 'b')):
                fail('the directories after the starts differ')
            outcome = 'started'
    count('%s %s: %s' % (family, kind, outcome))
    bb = by_base.setdefault(base, [0, 0])
    bb[0] += 1
    bb[1] += len(fails) > n0
    results.append('%s %s: %s%s' % (v, kind, outcome, ' DIFFERENCE' if len(fails) > n0 else ''))

with open(os.path.join(out, 'results.txt'), 'w') as f:
    f.write('\n'.join(results) + '\n')
with open(os.path.join(out, 'differences.txt'), 'w') as f:
    f.write(''.join('DIFFERENCE %s\n' % x for x in fails))
for k in sorted(counts):
    print('  %5d  %s' % (counts[k], k))
for x in notes[:10]:
    print(x)
if len(notes) > 10:
    print('note: %d more' % (len(notes) - 10))
nd = sum(1 for x in by_base.values() if x[1])
if control:
    missed = [b for b in sorted(by_base) if (b.startswith('case-') or b.startswith('found-'))
              and by_base[b][1] == 0]
    for b in sorted(by_base):
        print('  control %s: %d of %d copies differ' % (b, by_base[b][1], by_base[b][0]))
    if missed:
        print('CORRUPTSET CONTROL MISSED: no difference in %s' % ' '.join(missed))
        sys.exit(1)
    print('CORRUPTSET CONTROL CAUGHT: %d differences, in every base of the cases and of '
          'the found copies (C at %s)' % (len(fails), control))
    sys.exit(0)
for x in fails[:40]:
    print('DIFFERENCE ' + x)
if fails:
    print('differences: %d (%d copies) in %d bases' % (len(fails), sum(by_base[b][1] for b in by_base), nd))
    sys.exit(1)
sys.exit(0)
EOF
st=$?
echo "time: $(( $(date +%s) - T0 )) s"
if [ -n "$CONTROL" ]; then
    exit $st
fi
if [ $st = 0 ]; then
    echo "CORRUPTSET OK: $NV copies, the same status and text in each"
    rm -rf "$OUT/v"
    exit 0
fi
echo "CORRUPTSET FAILED ($OUT/differences.txt)"
exit 1
}
