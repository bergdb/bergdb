#!/bin/sh
# bergdb 030-21: the new writer (lean/contract/Contract/PeWriter.lean,
# `Contract.PE.peTx`) on Java's traces, with the trial program of 026-24
# (lean/pe/PeTrial.lean, here as PeTrial.lean.txt; options --pec and
# --pecrun, see its header).
#
# To build BIN: in a clone of the branch 026-24-pe-trial, copy PeTrial.lean.txt
# to lean/pe/PeTrial.lean and lean/contract/Contract/PeWriter.lean of the branch
# 030-21-pe-proof (b443d7a1) to lean/contract/Contract/; then cd lean/pe && lake
# build petrial (the binary is lean/pe/.lake/build/bin/petrial).
#
# Usage:
#   runpec.sh run BIN TRACEDIR OUTDIR "SETS" [P]
#     every trace of each set, at most P processes at a time (default 4):
#       pec     BIN pe --contract --paired --pec TRACE (the new writer beside
#               the trial's, at every transaction; --paired as 026-24's
#               runall.sh, so that RESULT is the trial's v1 line)
#       pecrun  BIN pe --pecrun TRACE (the new writer alone)
#     into OUTDIR/SET/MODE/NAME.txt; the wall time of each set and mode in
#     OUTDIR/SET/MODE.time. A job does not start once
#     /Users/f/fl/bench/2026-11-18/STOP exists; an output that ends with a
#     PETRIAL line is not run again.
#   runpec.sh sum OUTDIR V1DIR SET...
#     the summary of each set (V1DIR: 026-24's runs/v1, its mode pe
#     outputs): pec's counts, pecrun's failures and refusals, mode pe's
#     RESULT lines against v1's (the whole line; else the line without cmp's
#     `more` counts, which the trial program got after v1, commit cfe907dc),
#     pecrun's stand-in counts against v1's RESULT (madekey, versions, tops,
#     bnew, ball, btop, txs).
STOP=/Users/f/fl/bench/2026-11-18/STOP
cmd=$1; shift
case $cmd in
run)
  BIN=$1; TR=$2; OUT=$3; SETS=$4; P=${5:-4}
  for set in $SETS; do
    for mode in pec pecrun; do
      test -e $STOP && { echo "RUNPEC STOPPED"; exit 1; }
      mkdir -p $OUT/$set/$mode
      t0=$(date +%s)
      for f in $TR/$set/*.trace; do echo "$mode $f"; done | xargs -P $P -L 1 sh -c '
        test -e '"$STOP"' && exit 0
        mode=$0; f=$1
        o='"$OUT/$set"'/$mode/$(basename $f .trace).txt
        test -s $o && grep -q "^PETRIAL" $o && exit 0
        case $mode in
          pec) '"$BIN"' pe --contract --paired --pec $f > $o 2>&1 ;;
          pecrun) '"$BIN"' pe --pecrun $f > $o 2>&1 ;;
        esac'
      t1=$(date +%s)
      echo "$set $mode $(ls $TR/$set/*.trace | wc -l | tr -d ' ') traces, $((t1 - t0)) s wall, $P processes" > $OUT/$set/$mode.time
      cat $OUT/$set/$mode.time
    done
  done
  echo RUNPEC DONE
  ;;
sum)
  OUT=$1; V1=$2; shift 2
  python3 - "$OUT" "$V1" "$@" <<'PY'
import os, sys, collections
out, v1 = sys.argv[1], sys.argv[2]
def kv(line):
    d = {}
    for tok in line.split()[1:]:
        if "=" in tok:
            k, v = tok.split("=", 1)
            d[k] = v
    return d
def nomore(line):
    # cmp's counts `more` and `more.*` were added to the trial program after
    # its v1 runs (026-24, section 2.4, commit cfe907dc): left out here
    out = []
    for tok in line.split():
        if tok.startswith("cmp="):
            tok = "cmp=" + ",".join(kv for kv in tok[4:].split(",") if not kv.startswith("more"))
        out.append(tok)
    return " ".join(out)
def read(path):
    lines = open(path).read().splitlines() if os.path.exists(path) else []
    return lines
for s in sys.argv[3:]:
    print(f"== set {s}")
    tm = {}
    for mode in ("pec", "pecrun"):
        p = os.path.join(out, s, mode + ".time")
        if os.path.exists(p):
            tm[mode] = open(p).read().strip()
    # pec
    d = os.path.join(out, s, "pec")
    names = sorted(f[:-4] for f in os.listdir(d) if f.endswith(".txt")) if os.path.isdir(d) else []
    tot = collections.Counter(); ok = 0; complete = 0; resSame = 0; resDiff = []; resMissing = []
    resMore = []
    refby = collections.Counter()
    diffLines = []
    for n in names:
        L = read(os.path.join(d, n + ".txt"))
        if any(l.startswith("PETRIAL") for l in L): complete += 1
        if "PETRIAL OK" in L: ok += 1
        pec = [l for l in L if l.startswith("PEC ")]
        if pec:
            m = kv(pec[0])
            for k in ("txs", "same", "differ", "refused", "fsame", "fdiffer", "frefused", "wsdup", "nodes"):
                tot[k] += int(m[k])
            for kvp in m["refusedby"].split(","):
                if ":" in kvp:
                    a, b = kvp.rsplit(":", 1); refby[a] += int(b)
        inDiff = False; mine = []
        for l in L:
            if l.startswith("PECDIFF") or l.startswith("PECREFUSED"): inDiff = True; mine.append(l)
            elif inDiff and l.startswith("  "): mine.append(l)
            else: inDiff = False
        diffLines += mine[:8]
        res = [l for l in L if l.startswith("RESULT")]
        ref = [l for l in read(os.path.join(v1, s, "pe", n + ".txt")) if l.startswith("RESULT")]
        if not ref: resMissing.append(n)
        elif res and res[0] == ref[0]: resSame += 1
        elif res and nomore(res[0]) == nomore(ref[0]): resMore.append(n)
        else: resDiff.append(n)
    print(f"pec: {len(names)} traces, {complete} complete, PETRIAL OK {ok}; transactions {tot['txs']}: "
          f"same {tot['same']}, differ {tot['differ']}, refused {tot['refused']} {dict(refby) if refby else ''}; "
          f"the refused ones without their longdel deletes: same {tot['fsame']}, differ {tot['fdiffer']}, "
          f"refused {tot['frefused']}; wsdup {tot['wsdup']}; nodes walked {tot['nodes']}")
    print(f"pec: RESULT lines equal to v1's (whole line): {resSame} of {len(names)}"
          + (f"; equal but for cmp's `more` counts (not in v1's program): {len(resMore)} {resMore}" if resMore else "")
          + (f"; differ: {resDiff}" if resDiff else "") + (f"; no v1 line: {resMissing}" if resMissing else ""))
    refl = [l for l in diffLines if l.startswith("PECREFUSED")]
    for l in refl[:4]:
        print("  " + l[:400])
    if len(refl) > 4: print(f"  ... ({len(refl)} PECREFUSED lines printed by the traces, at most 6 a trace)")
    for l in [l for l in diffLines if not l.startswith("PECREFUSED")][:20]:
        print("  " + l[:400])
    # pecrun
    d = os.path.join(out, s, "pecrun")
    names = sorted(f[:-4] for f in os.listdir(d) if f.endswith(".txt")) if os.path.isdir(d) else []
    tot = collections.Counter(); fails = collections.Counter(); ok = 0; complete = 0
    starts = collections.Counter(); cntSame = 0; cntDiff = []; refby = collections.Counter()
    firsts = []
    for n in names:
        L = read(os.path.join(d, n + ".txt"))
        if any(l.startswith("PETRIAL") for l in L): complete += 1
        if "PETRIAL OK" in L: ok += 1
        for l in L:
            if l.startswith("PECSTART"): starts[kv(l)["start"]] += 1
        pr = [l for l in L if l.startswith("PECRUN")]
        if not pr: continue
        m = kv(pr[0])
        for k in ("txs", "ops", "refused", "gets", "jreads", "wsdup"):
            tot[k] += int(m[k])
        for kvp in m["refusedby"].split(","):
            if ":" in kvp:
                a, b = kvp.rsplit(":", 1); refby[a] += int(b)
        for kvp in m["fails"].split(","):
            if ":" in kvp:
                a, b = kvp.rsplit(":", 1); fails[a] += int(b)
        firsts += [l for l in L if l.startswith("  ")][:3]
        ref = [l for l in read(os.path.join(v1, s, "pe", n + ".txt")) if l.startswith("RESULT")]
        if ref:
            r = kv(ref[0])
            ks = ("txs", "madekey", "versions", "tops", "bnew", "ball", "btop")
            if all(r[k] == m[k] for k in ks): cntSame += 1
            else: cntDiff.append((n, {k: (r[k], m[k]) for k in ks if r[k] != m[k]}))
    print(f"pecrun: {len(names)} traces, {complete} complete, PETRIAL OK {ok}; start {dict(starts)}; "
          f"transactions {tot['txs']}, operations {tot['ops']}, refused {tot['refused']} "
          f"{dict(refby) if refby else ''}, wsdup {tot['wsdup']}; "
          f"gets {tot['gets']}, Java's reads {tot['jreads']}; failures {dict(fails) if fails else 0}")
    print(f"pecrun: txs, madekey, versions, tops, bnew, ball, btop equal to v1's RESULT: {cntSame} of {len(names)}"
          + (f"; differ: {cntDiff[:5]}" if cntDiff else ""))
    for l in [l for l in firsts if "refused" not in l][:10] + [l for l in firsts if "refused" in l][:2]:
        print("  " + l[:300])
    for mode in ("pec", "pecrun"):
        if mode in tm: print(f"time: {tm[mode]}")
PY
  ;;
*)
  echo "Usage: runpec.sh run BIN TRACEDIR OUTDIR \"SETS\" [P] | runpec.sh sum OUTDIR V1DIR SET..."; exit 2 ;;
esac
