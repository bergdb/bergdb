#!/bin/sh
# 009-04's two runs (items/009-handles/04-shenandoah-degenerated.md, section 6, points 1 and 2),
# scheduled by Frans for 2026-10-26, 22:30: P4's soak under Shenandoah (1) generational with a
# 12 GB heap, (2) without generations (satb) with P4's 8 GB heap; each about 50 minutes, after
# 004-02's quiet.sh. The branch's worktree build (f4e93d8, the code merged into main as 98981f8).
# Usage: sh f53-009d.sh DIR WORKTREE
D=$1
W=$2
OUT=$D/out3
mkdir -p "$OUT"
caffeinate -i -s &
CAF=$!
log() { echo "$(date '+%F %T') $*" >> "$OUT/runs.txt"; }
log "scheduled block start"
QUIETLOAD=2.0 sh "$D/quiet.sh" 32b68478-35b0-4112-9d94-6ddb9ecd9df2 110 >> "$OUT/runs.txt"
log "quiet: $(uptime | sed 's/.*load/load/')"
soak() {    # soak NAME HEAP MODE
    log "start soak $1"
    if (cd "$W" && HEAP=$2 GC=g1 JFLAGS="-XX:-UseG1GC -XX:+UseShenandoahGC -XX:ShenandoahGCMode=$3 -Devictbudget=1600000000" \
            sh java/stress/soak.sh $1 rate=200 warmup=300 warmupmax=3600 measure=1800 restarts=1 mincuts=2 extend=900) \
            >> "$OUT/runs.txt" 2>&1; then
        log "ok soak $1"
    else
        log "FAILED soak $1"
    fi
}
soak p4-009-shen-gen-12g 12g generational
soak p4-009-shen-satb-8g 8g satb
kill $CAF
gcmax=$(grep '^FINISH' "$OUT/runs.txt" | sed -E 's#.*/(p4-009-[a-z0-9-]+)/result.json: GC pauses in the measured phase: [0-9]+, total [0-9]+ ms, max ([0-9.]+) ms.*#\1 \2 ms#' | tr '\n' ';')
if grep -q "FAILED soak" "$OUT/runs.txt"; then st=FAILED; else st="needs a look"; fi
sh /Users/f/fl/repos/bergdb/tools/news.sh "$st" "009-04 soaks" \
    "P4's soak under Shenandoah, 12 GB generational and 8 GB satb, longest GC pause: $gcmax for 009-04, section 6. Log: $OUT/runs.txt"
log "F53 009-04 BLOCK DONE"
