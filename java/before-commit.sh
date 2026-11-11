#!/bin/sh
# The check before a commit: the only one required (since 2026-10-20). It must
# print BEFORE COMMIT OK before a change to java/ is committed. The level scripts
# (stress/level1.sh to level4.sh), night.sh and perf.sh are not commit gates.
#
# Usage: java/before-commit.sh
#   About 2 minutes on F53 (10 cores, 2026-10-20; 2026-11-09: 123 s with the
#   demos, 121 s without).
#
# Builds with build.sh, checks the package dependencies with deps.py (each
# package in src uses only what its package.html lists, bergdb 005-56; under a
# second), checks with doubles.py that no double or float is used in the Core
# Layer's production code outside its list of allowed places (API conversions,
# statistics, the users' values as bits; bergdb 005-79; a few seconds), then
# runs at the same time, each in its own JVM with assertions on (-ea):
#   * the unit tests (bergdb.dev.Unit, the Nano test group "unit"), about 30 s;
#   * the f-tests (bergdb.dev.F, the Nano test group "f"), about 1 minute;
#   * the demos of the Pub API in src-dev on small sizes (since 2026-11-09), about 3 s,
#     one after the other, each in its own JVM, in build/before-commit/demos/, made
#     new each run: frans.PayDemo's create, pay, iter and access on one database of
#     10,000 accounts, frans.WebsiteCode, and bergdb.demo's Demo (put, get, delete,
#     get) and GetStarted1 to 5. A demo fails when it exits with an error, prints an
#     exception, is not done in 60 s, or lacks the line that shows its work, such as
#     iter's count of the accounts that create made and the sum of their balances,
#     1 each from create and unchanged by pay's payments.
# Logs go to build/before-commit/. Exits with status 1 unless deps.py and
# doubles.py pass, both tests print SUCCESS and the demos DEMOS OK. Set JAVA_HOME
# or PATH for the JDK; the build needs javac too; deps.py and doubles.py need
# python3, the demos' time limit perl.

cd "$(dirname "$0")"

JAVA=${JAVA:-java}
if [ -n "$JAVA_HOME" ]; then JAVA=$JAVA_HOME/bin/java; fi

LOG=build/before-commit
START=$(date +%s)
DEMOS=$LOG/demos
LIMIT=60

fail() {
    echo "BEFORE COMMIT FAILED: $1 (log: java/$2)"
    exit 1
}

./build.sh > /dev/null || { echo "BEFORE COMMIT FAILED: build"; exit 1; }
mkdir -p $LOG
rm -f $LOG/unit.txt $LOG/f.txt $LOG/demos.txt $LOG/deps.txt $LOG/doubles.txt

if ! python3 -I deps.py > $LOG/deps.txt 2>&1; then
    grep -E 'NOT ALLOWED|BAD LIST|Error' $LOG/deps.txt
    fail "package dependencies: a use that its package's package.html does not list, or a list not in the form \"Depends on: a, b, c.\"; change the code or the list" $LOG/deps.txt
fi
echo "Deps: $(tail -1 $LOG/deps.txt)"

if ! python3 -I doubles.py > $LOG/doubles.txt 2>&1; then
    grep -E 'REFUSED|SELF-TEST|doubles.py:|Error' $LOG/doubles.txt
    fail "doubles in the Core's production code outside the allowed list (bergdb 005-79): decide with integers, or add an API conversion or a statistic to ALLOWED in doubles.py with its reason" $LOG/doubles.txt
fi
echo "Doubles: $(tail -1 $LOG/doubles.txt)"

# demo NAME LINE CLASS [ARG...]: runs CLASS's main in $DEMOS with assertions on,
# killed after $LIMIT s (perl's alarm, which exec keeps), and prints its output.
# Prints "DEMO FAILED: NAME: why" and returns 1 unless it exits with 0, prints no
# exception and, when LINE is not empty, a line that LINE matches (grep -x -E).
demo() {
    name=$1; line=$2; shift 2
    echo "--- $name"
    (cd $DEMOS && perl -e 'alarm shift; exec @ARGV or die "exec $ARGV[0]: $!\n"' $LIMIT \
        "$JAVA" -ea -cp "$JAR" "$@") > $DEMOS/output.txt 2>&1
    status=$?
    cat $DEMOS/output.txt
    RUNS=$((RUNS + 1))
    if [ $status = 142 ]; then
        echo "DEMO FAILED: $name: not done in $LIMIT s"; return 1
    elif [ $status != 0 ]; then
        echo "DEMO FAILED: $name: exit status $status"; return 1
    elif grep -q -E 'Exception|Error' $DEMOS/output.txt; then
        echo "DEMO FAILED: $name: it printed an exception"; return 1
    elif [ -n "$line" ] && ! grep -q -x -E "$line" $DEMOS/output.txt; then
        echo "DEMO FAILED: $name: no line \"$line\""; return 1
    fi
}

# demos: the demos in order, each on what the ones before it made.
demos() {
    T0=$(date +%s)
    JAR=$(pwd)/build/bergdb.jar
    RUNS=0
    rm -rf $DEMOS && mkdir -p $DEMOS || { echo "DEMO FAILED: $DEMOS not made new"; return 1; }
    PAY="-Dpay.accounts=10000 -Dpay.count=2000 -Dpay.dir=pay"
    demo "PayDemo create" 'Total time: .*' $PAY frans.PayDemo create &&
    demo "PayDemo pay" 'Payments: 2000, .*' $PAY frans.PayDemo pay &&
    demo "PayDemo iter" 'Iterate\. sum: 10000, count: 10000\. .*' $PAY frans.PayDemo iter &&
    demo "PayDemo access" 'Retrieved 2000 accounts, .*' $PAY frans.PayDemo access &&
    demo WebsiteCode 'v1 = v1' frans.WebsiteCode &&
    demo "Demo put" '' bergdb.demo.Demo put &&
    demo "Demo get" 'Hello world!' bergdb.demo.Demo get &&
    demo "Demo delete" '' bergdb.demo.Demo delete &&
    demo "Demo get after delete" 'null' bergdb.demo.Demo get &&
    demo GetStarted1 'Adam' bergdb.demo.GetStarted1 &&
    demo GetStarted2 'Eve' bergdb.demo.GetStarted2 &&
    demo GetStarted3 'Adam' bergdb.demo.GetStarted3 &&
    demo GetStarted4 'Balance of /accounts/0 after the payment: 70' bergdb.demo.GetStarted4 &&
    demo GetStarted5 's: a' bergdb.demo.GetStarted5 &&
    echo "DEMOS OK, $RUNS runs in $(( $(date +%s) - T0 )) s."
}

$JAVA -ea -cp build/bergdb.jar bergdb.dev.Unit > $LOG/unit.txt 2>&1 &
$JAVA -ea -cp build/bergdb.jar bergdb.dev.F > $LOG/f.txt 2>&1 &
demos > $LOG/demos.txt 2>&1 &
wait

grep -q '^SUCCESS' $LOG/unit.txt || fail "unit tests" $LOG/unit.txt
echo "Unit: $(grep '^SUCCESS' $LOG/unit.txt)"
grep -q '^SUCCESS' $LOG/f.txt || fail "f-tests" $LOG/f.txt
echo "F:    $(grep '^SUCCESS' $LOG/f.txt)"
grep -q '^DEMOS OK' $LOG/demos.txt ||
    fail "demos: $(sed -n 's/^DEMO FAILED: //p' $LOG/demos.txt)" $LOG/demos.txt
echo "Demos: $(grep '^DEMOS OK' $LOG/demos.txt)"
echo "BEFORE COMMIT OK ($(( $(date +%s) - START )) s)"
