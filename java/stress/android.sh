#!/bin/sh
# BergDB on Android (bergdb 006-18-03): the unit tests and the Pub API's demos on an Android
# emulator, as before-commit.sh runs them on the JVM. Not a commit gate; run it before a
# release (Frans, 2026-11-09: "I think it makes sense to run an Android test before a
# release. At least on the unit tests.").
#
# Usage: java/stress/android.sh
#   About 2 minutes on F53 (2026-11-09: 119 s; the build 30 s, the boot 16 s, the unit tests
#   75 s, the demos 15 s).
#
# Needs the Android SDK: build-tools (d8), platform-tools (adb), the emulator, the platform
# of API level $API, and an AVD of that level's system image (arm64-v8a on F53); bergdb
# 006-18-03, section 3, says how they were installed without sudo. A JDK for the build and d8.
#
# Steps, stopping at the first failure:
#   1. Builds with ../build.sh.
#   2. d8 dexes build/bergdb.jar (src and src-dev, so the tests too) for API level $API, with
#      desugaring and with assertions on (d8 removes them by default; the JVM's tests run with
#      -ea), and adds the jar's resources.
#   3. Boots the AVD headless (-no-window -no-audio -no-snapshot) on port $PORT, and waits for
#      sys.boot_completed, at most 3 minutes.
#   4. Pushes the jar to /data/local/tmp/bergdb-android/ and runs, with app_process as the
#      shell user, bergdb.dev.Unit: the unit tests, of which those that check what only a JVM
#      has skip themselves and say why (bergdb.nanotest.Platform).
#   5. The demos of before-commit.sh, one after the other, each in a new process, on what the
#      ones before it made, each checked for its line: frans.PayDemo's create, pay, iter and
#      access on 10,000 accounts, frans.WebsiteCode, and bergdb.demo's GetStarted1 to 5
#      (Demo, a class that is not public, is left out: app_process calls only a public
#      class's main).
#   6. Shuts the emulator down, also after a failure or an interrupt.
# Prints ANDROID OK (N tests, M skipped) or ANDROID FAILED and the failures. Output in
# build/android/: build.txt, d8.txt, emulator.log, unit.txt, demos.txt.
#
# Environment: ANDROID_SDK, the SDK's directory (required; ANDROID_HOME if it is not set);
# ANDROID_USER_HOME (default user/ beside the SDK), whose avd/ holds the AVD; ANDROID_AVD
# (default bergdb34); API (default 34, the floor of objects); PORT (default 5580); JAVA_HOME.
#
# Kind: functional (bergdb 028-23): the result does not depend on the machine's speed or
# load; its time limits are hang guards, generous for a loaded machine.

cd "$(dirname "$0")/.."
echo "Kind: functional"
HERE=$(pwd)
SDK=${ANDROID_SDK:-$ANDROID_HOME}
if [ -z "$SDK" ] || [ ! -d "$SDK" ]; then
    echo "ANDROID FAILED: set ANDROID_SDK to the Android SDK's directory (now: '$SDK'); bergdb 006-18-03, section 3, says how to install it"
    exit 1
fi
export ANDROID_HOME="$SDK" ANDROID_SDK_ROOT="$SDK"
export ANDROID_USER_HOME="${ANDROID_USER_HOME:-$(dirname "$SDK")/user}"
export ANDROID_AVD_HOME="${ANDROID_AVD_HOME:-$ANDROID_USER_HOME/avd}"
AVD=${ANDROID_AVD:-bergdb34}
API=${API:-34}
PORT=${PORT:-5580}
JAVA=${JAVA_HOME:+$JAVA_HOME/bin/}java
OUT=build/android
DEV=/data/local/tmp/bergdb-android
ADBBIN="$SDK/platform-tools/adb"
ADB="$ADBBIN -s emulator-$PORT"
T0=$(date +%s)
EMU=

fail() {
    echo "ANDROID FAILED: $1"
    exit 1
}

# stop: shuts the emulator down, if this script started it.
stop() {
    if [ -n "$EMU" ]; then
        $ADB emu kill > /dev/null 2>&1
        i=0
        while kill -0 "$EMU" 2> /dev/null && [ $i -lt 30 ]; do
            sleep 1
            i=$((i + 1))
        done
        kill "$EMU" 2> /dev/null
        EMU=
    fi
}
trap stop EXIT
trap 'exit 1' INT TERM

D8=$(ls -d "$SDK"/build-tools/*/lib/d8.jar 2> /dev/null | tail -1)
LIB="$SDK/platforms/android-$API/android.jar"
[ -f "$D8" ] || fail "no d8.jar in $SDK/build-tools"
[ -f "$LIB" ] || fail "no $LIB"
[ -x "$SDK/emulator/emulator" ] || fail "no emulator in $SDK"
[ -x "$ADBBIN" ] || fail "no adb in $SDK/platform-tools"
[ -d "$ANDROID_AVD_HOME/$AVD.avd" ] || fail "no AVD $AVD in $ANDROID_AVD_HOME"
if "$ADBBIN" devices 2> /dev/null | grep -q "^emulator-$PORT"; then
    fail "an emulator already runs on port $PORT"
fi

mkdir -p $OUT
rm -f $OUT/build.txt $OUT/d8.txt $OUT/emulator.log $OUT/unit.txt $OUT/demos.txt \
    $OUT/bergdb-dex.jar

echo "1. Build"
sh build.sh > $OUT/build.txt 2>&1 || { tail -20 $OUT/build.txt; fail "build.sh"; }

echo "2. d8, API level $API"
"$JAVA" -Xmx4g -cp "$D8" com.android.tools.r8.D8 --release --min-api "$API" --lib "$LIB" \
    --force-enable-assertions --output $OUT/bergdb-dex.jar build/bergdb.jar \
    > $OUT/d8.txt 2>&1 || { cat $OUT/d8.txt; fail "d8"; }
RES=$(mktemp -d "${TMPDIR:-/tmp}/bergdb-android.XXXXXX")
(cd "$RES" && unzip -q "$HERE/build/bergdb.jar" -x '*.class' 'META-INF/*' &&
    find . -type d -empty -delete && zip -q -r "$HERE/$OUT/bergdb-dex.jar" .) ||
    { rm -rf "$RES"; fail "the resources"; }
rm -rf "$RES"

echo "3. Emulator $AVD on port $PORT"
"$SDK/emulator/emulator" -avd "$AVD" -port "$PORT" -no-window -no-audio -no-boot-anim \
    -no-snapshot -gpu swiftshader_indirect -no-metrics > $OUT/emulator.log 2>&1 &
EMU=$!
i=0
while [ "$($ADB shell getprop sys.boot_completed 2> /dev/null | tr -d '\r')" != 1 ]; do
    kill -0 "$EMU" 2> /dev/null || { EMU=; fail "the emulator ended (see $OUT/emulator.log)"; }
    [ $i -lt 180 ] || fail "the emulator did not boot in 3 minutes (see $OUT/emulator.log)"
    sleep 1
    i=$((i + 1))
done
echo "   booted in about $i s: Android $($ADB shell getprop ro.build.version.release |
    tr -d '\r'), API $($ADB shell getprop ro.build.version.sdk | tr -d '\r')"

echo "4. bergdb.dev.Unit"
$ADB shell "rm -rf $DEV && mkdir -p $DEV/tmp $DEV/demos" || fail "adb shell"
$ADB push $OUT/bergdb-dex.jar $DEV/bergdb.jar > /dev/null || fail "adb push"
VM="CLASSPATH=$DEV/bergdb.jar app_process -Djava.io.tmpdir=$DEV/tmp"
$ADB shell "cd $DEV && $VM /system/bin bergdb.dev.Unit 2>&1" | tr -d '\r' > $OUT/unit.txt 2>&1
RESULT=$(grep -E '^(SUCCESS|FAILURE)' $OUT/unit.txt | tail -1)
echo "   ${RESULT:-no result line (see $OUT/unit.txt)}"
grep -o 'SKIPPED .*' $OUT/unit.txt | sed 's/^/   /'
case "$RESULT" in
    SUCCESS*) ;;
    *)
        grep -E 'FAILED!' $OUT/unit.txt | head -40
        tail -5 $OUT/unit.txt
        fail "the unit tests (log: $OUT/unit.txt)"
        ;;
esac
TESTS=$(echo "$RESULT" | sed -E 's/^SUCCESS, ([0-9]+) successful tests.*/\1/')
SKIPPED=$(echo "$RESULT" | sed -nE 's/.*, ([0-9]+) skipped.*/\1/p')
SKIPPED=${SKIPPED:-0}

echo "5. Demos"
RUNS=0
# demo NAME LINE [-DPROP...] CLASS [ARG...]: runs CLASS's main in $DEV/demos; fails unless
# its output has LINE (an extended regular expression, or empty) and no exception.
demo() {
    name=$1
    line=$2
    shift 2
    props=
    while [ $# -gt 0 ] && [ "${1#-D}" != "$1" ]; do
        props="$props $1"
        shift
    done
    out=$($ADB shell "cd $DEV/demos && $VM$props /system/bin $* 2>&1" | tr -d '\r')
    printf '== %s\n%s\n' "$name" "$out" >> $OUT/demos.txt
    RUNS=$((RUNS + 1))
    if printf '%s\n' "$out" | grep -qE 'Exception|Error|^Killed'; then
        printf '%s\n' "$out" | tail -10
        fail "the demo $name threw (log: $OUT/demos.txt)"
    fi
    if [ -n "$line" ] && ! printf '%s\n' "$out" | grep -qE "^$line\$"; then
        printf '%s\n' "$out" | tail -10
        fail "the demo $name lacks the line '$line' (log: $OUT/demos.txt)"
    fi
}
PAY="-Dpay.accounts=10000 -Dpay.count=2000 -Dpay.dir=pay"
demo "PayDemo create" 'Total time: .*' $PAY frans.PayDemo create
demo "PayDemo pay" 'Payments: 2000, .*' $PAY frans.PayDemo pay
demo "PayDemo iter" 'Iterate\. sum: 10000, count: 10000\. .*' $PAY frans.PayDemo iter
demo "PayDemo access" 'Retrieved 2000 accounts, .*' $PAY frans.PayDemo access
demo WebsiteCode 'v1 = v1' frans.WebsiteCode
demo GetStarted1 'Adam' bergdb.demo.GetStarted1
demo GetStarted2 'Eve' bergdb.demo.GetStarted2
demo GetStarted3 'Adam' bergdb.demo.GetStarted3
demo GetStarted4 'Balance of /accounts/0 after the payment: 70' bergdb.demo.GetStarted4
demo GetStarted5 's: a' bergdb.demo.GetStarted5
echo "   $RUNS runs"

stop
echo "ANDROID OK ($TESTS tests, $SKIPPED skipped) in $(( $(date +%s) - T0 )) s; $RUNS demo runs"
