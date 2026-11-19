#!/bin/sh
# The week run (bergdb 028-23): the deepest functional testing, on demand, and before
# every release, near it. Frans, 2026-11-19, 10:25: "Do we need week.sh or something?
# Testing run less often and on demand. The name is only a name, it is not necessarily
# scheduled. It would always run before a release. Near a release, at least. Not
# necessarily on the exact version that ships in the release. Minor change after can be
# acceptable." Not a gate; read its report when it ends. Started by hand, or by the day's
# coordinator (013-02) as a step of its plan, from the main tree:
#     nohup caffeinate -i sh java/week.sh >/dev/null 2>&1 &
#
# Kind: functional, as night.sh: no step's result depends on the machine's speed or load;
# the time limits inside are hang guards. It may run while someone works on the machine,
# and at a low priority (nice -n 10, or taskpolicy -b on macOS; night.sh's header says
# more). Timing is timing.sh's, which also runs before every release.
#
# Usage: java/week.sh          the week run, about 11 hours on F53 (an estimate of
#                              2026-11-19 from the steps' times below)
#        java/week.sh short    a trial of the script: week's own steps small (about 25
#                              minutes), night's steps left out
#
# It is night.sh's run (night.sh week; the same clone of HEAD in build/week/RUN/repo, the
# same report, build/week/RUN/report.txt, ending WEEK OK or WEEK FAILED, the same logs and
# a tools/news.sh entry), with these steps, one after another, going on after a failure:
#   1. night.sh's steps (its header): before-commit.sh, core-build, transcheck, level1.sh to
#      level4.sh full, count-gates, lean-tests, tree-tests, the night tests, harness-soak
#      -r 2, fuzz 12 minutes, unlinkfuzz, kill-restart 1,000 kills, conformance medium,
#      contract medium; about 2.5 hours.
#   2. apps-quick, apps-soak, apps-kill: stress/apps.sh, the user applications of 024-26
#      and 026-13 (its header), built against the clone's own release jar: quick (about
#      6 minutes), soak and kill rounds with the day's number as N, new seeds each day
#      (about 40 and 30 minutes).
#   3. kill-restart-week: stress/kill-restart.sh, 1,000 kills on each of three more seeds
#      (the day's number times 10, plus 1 to 3), so 4,000 kills with night's; about 80
#      minutes. Stops at the first failure, which keeps its database.
#   4. fuzz-week: stress/fuzz.sh for 60 minutes, seeds from the day's number times 1000
#      plus 100 (night's 12 turns take those from plus 0).
#   5. unlinkfuzz-week: stress/unlinkfuzz.sh with a second block of the day's seeds (from
#      the day's number times 1000 plus 500); about 5 minutes.
#   6. harness-soak-week: stress/harness-soak.sh -r 10, other seeds than night's; about 20
#      minutes.
#   7. conformance-large: stress/conformance.sh large (night.sh large's step), 12 traces of
#      1,000 to 5,000 transactions at node sizes 8 to 62; about 5 hours.
# With "short": apps quick, kill-restart 10 kills on two seeds, fuzz 1 minute, unlinkfuzz
# one block, harness-soak -r 1, and conformance small with 1 seed in place of large.
# Not in it, by hand before a release: stress/android.sh (needs the Android SDK).
# Set JAVA_HOME or PATH for the JDK; the build needs javac too, and the Lean steps elan.

cd "$(dirname "$0")" || exit 1
if [ "$1" = short ]; then
    exec sh ./night.sh week short
fi
exec sh ./night.sh week
