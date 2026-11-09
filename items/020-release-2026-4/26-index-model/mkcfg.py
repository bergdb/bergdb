# bergdb 020-26: writes the TLC configs of the model's runs into cfg/.
import sys
VALS3 = "{\"s\", \"a\", \"b\"}"
VALS2 = "{\"a\", \"b\"}"
INV = ("IndexIsFunction NoStaleEntry BuildCovers GensAccounted MarkerNotLive "
       "StartAccepted GenFresh MemAgrees LockSane")
def cfg(name, keys="{1, 3}", writers="{w1}", fns="{1}", vals=VALS3, suf="{}", step=1, cmax=1, locked=1, creates=1,
        crashes=0, timed=False, maxtime=0, bug="none", live=False, symm=False):
    lines = ["CONSTANTS",
             f"  ObjKeys = {keys}", f"  SufKeys = {suf}", f"  Writers = {writers}",
             f"  Fns = {fns}", f"  Values = {vals}", f"  StepMax = {step}", f"  CleanupMax = {cmax}",
             f"  LockedAfter = {locked}", f"  MaxCreates = {creates}",
             f"  MaxCrashes = {crashes}", f"  TimedGen = {'TRUE' if timed else 'FALSE'}",
             f"  MaxTime = {maxtime}", f'  Bug = "{bug}"',
             "  Nil = Nil", "  DefKey = DefKey", "  VKey = VKey", "  Mgr = Mgr"]
    if live:
        lines += ["SPECIFICATION FairSpec", "PROPERTIES BuildEnds CleanupEnds NoOrphans"]
    else:
        lines += ["SPECIFICATION Spec", "INVARIANTS " + INV]
    if timed:
        lines += ["CONSTRAINT TimeBound"]
    if symm:
        lines += ["SYMMETRY Symm"]
    open(f"cfg/{name}.cfg", "w").write("\n".join(lines) + "\n")

# Daytime runs, each meant to end in minutes.
cfg("d1-crash",    creates=1, crashes=1)
cfg("d2-recreate", fns="{1, 2}", vals=VALS2, creates=2)
cfg("d3-writers",  writers="{w1, w2}", creates=1, symm=True)
cfg("d4-timed",    fns="{1, 2}", vals=VALS2, creates=2, crashes=1, timed=True, maxtime=8)
cfg("d5-step2",    suf="{2}", step=2, locked=2, creates=1)
cfg("l1-live",     suf="{2}", creates=1, live=True)
cfg("l1-live-AllHashes", suf="{2}", creates=1, live=True, bug="AllHashes")
# Night runs.
cfg("n1-all-1w",   suf="{2}", fns="{1, 2}", creates=2, crashes=1)
# Simulation (random traces) of the whole model, and of each planted fault.
cfg("sim", writers="{w1, w2}", fns="{1, 2}", suf="{2}", creates=2, crashes=1)
for b in ["SBeforeR", "NoVhash", "NoPrevHash", "NoLock", "NoDefHash", "NoValueHash",
          "ConstGen", "NoIsLive", "NoActCheck", "NoEndKey", "NoFinalCheck", "AllHashes"]:
    cfg("sim-" + b, writers="{w1, w2}", fns="{1, 2}", suf="{2}", creates=2, crashes=1, bug=b)
# The shortest counterexample of each planted fault: breadth-first, one worker.
for b, kw in [("SBeforeR", {}), ("NoVhash", {}), ("NoLock", {}),
              ("NoPrevHash", {"writers": "{w1, w2}"}), ("NoDefHash", {}), ("NoIsLive", {}),
              ("NoValueHash", {}), ("ConstGen", {"creates": 2}), ("NoActCheck", {})]:
    cfg("min-" + b, bug=b, **kw)
# Liveness: without the locked phase, writers of object keys can keep a build from ending.
cfg("l1-live-NoLockedPhase", creates=1, live=True, bug="NoLockedPhase")
# Two generations with larger steps (one build step and one cleanup step for the two keys).
cfg("d2b-recreate", fns="{1, 2}", vals=VALS2, creates=2, step=2, cmax=2)
cfg("d4b-timed", vals=VALS2, creates=2, crashes=1, timed=True, maxtime=8, step=2, cmax=2)
# Two generations with one key: a creation, its deletion and a new creation.
cfg("d2c-recreate-1key", keys="{1}", fns="{1, 2}", vals=VALS3, creates=2, crashes=1)
cfg("d4c-timed-1key", keys="{1}", vals=VALS2, creates=2, crashes=1, timed=True, maxtime=10)
cfg("min-ConstGen-1key", keys="{1}", creates=2, bug="ConstGen")
cfg("d3c-writers-1key", keys="{1}", writers="{w1, w2}", creates=1, crashes=1, symm=True)
# Generations as times, smaller: one key, one object value.
cfg("d4d-timed-small", keys="{1}", vals='{"a"}', creates=2, crashes=1, timed=True, maxtime=9)
# Liveness, smaller: one object key and one key with a suffix.
cfg("l2-live-1key", keys="{1}", suf="{2}", creates=1, live=True)
cfg("l2-live-1key-AllHashes", keys="{1}", suf="{2}", creates=1, live=True, bug="AllHashes")
cfg("l2-live-1key-NoLockedPhase", keys="{1}", creates=1, live=True, bug="NoLockedPhase")
cfg("l3-live-1key-recreate", keys="{1}", vals=VALS2, creates=2, crashes=1, live=True)
cfg("l3-live-1key-2w", keys="{1}", writers="{w1, w2}", vals=VALS2, creates=1, live=True)
# The changes that safety does not need, exhaustively at d1's bounds (and a key with a suffix).
for b in ["NoEndKey", "NoFinalCheck", "AllHashes"]:
    cfg("d6-" + b, suf="{2}", creates=1, crashes=1, bug=b)
cfg("d6-none", suf="{2}", creates=1, crashes=1)
# Liveness with two generations and a crash, and with two writers, smaller: one value.
cfg("l4-live-1key-recreate", keys="{1}", vals='{"a"}', creates=2, crashes=1, live=True)
cfg("l4-live-1key-2w", keys="{1}", writers="{w1, w2}", vals='{"a"}', creates=1, crashes=1, live=True)
