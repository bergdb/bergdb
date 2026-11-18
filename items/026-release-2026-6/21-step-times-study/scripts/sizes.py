#!/usr/bin/env python3
"""The size of the model writer for each design (bergdb 026-21, section 4):
the lines of each top-level definition of today's writer (Exec.lean) and of
the step-times writer (Study/ExecStep.lean, with the Fix of Study/Steps.lean),
all lines and code lines (no comment, no blank). A definition's span runs from
its doc comment to the next one's.

Usage: sizes.py EXEC.lean EXECSTEP.lean STEPS.lean
"""
import re, sys

def spans(path):
    lines = open(path).read().split("\n")
    starts = []
    for i, l in enumerate(lines):
        m = re.match(r"^(def|abbrev|structure|inductive|theorem) ([A-Za-z0-9_.?']+)", l)
        if m:
            j = i
            while j > 0 and (lines[j - 1].startswith("/--") or (lines[j - 1].strip() and not lines[j - 1].startswith(("def ", "/-!", "end ", "namespace", "open", "import")) and any(x.startswith("/--") for x in lines[max(0, j - 15):j]) and not re.match(r"^(def|abbrev|structure|inductive)", lines[j - 1]))):
                # walk back over a doc comment
                if lines[j - 1].startswith("/--"):
                    j -= 1
                    break
                j -= 1
            starts.append((j, i, m.group(2)))
    out = {}
    for k, (j, i, name) in enumerate(starts):
        end = starts[k + 1][0] if k + 1 < len(starts) else len(lines)
        body = lines[j:end]
        # trim section headers and trailing blank lines
        while body and (not body[-1].strip() or body[-1].startswith("/-!") or body[-1].startswith("end ")):
            body.pop()
        code = 0
        incomment = False
        for l in body:
            t = l.strip()
            if incomment:
                if "-/" in t:
                    incomment = False
                continue
            if t.startswith("/-"):
                if "-/" not in t:
                    incomment = True
                continue
            if not t or t.startswith("--"):
                continue
            code += 1
        out[name] = (len(body), code)
    return out

today = spans(sys.argv[1])
step = spans(sys.argv[2])
steps = spans(sys.argv[3])
replaced = [n for n in step if n in today]
new = [n for n in step if n not in today]
# today's definitions that the step writer does not use (replaced, or dead)
dead = ["setMadeFor", "replacedBy", "takenBack", "retarget", "canTakeBack", "takeBack",
        "takeBackRoot", "collapseRoot", "mergeUp", "afterDelete", "deleteUpward", "boundsOK",
        "runOpsFrom", "runOps", "exec?"]
def tot(d, names):
    return sum(d[n][0] for n in names), sum(d[n][1] for n in names)
print("today's writer, Exec.lean: definitions", len(today), "lines", tot(today, today))
print("replaced in the step writer:", ", ".join(replaced), tot(today, replaced))
print("today's, not used by the step writer:", ", ".join(n for n in dead if n in today),
      tot(today, [n for n in dead if n in today]))
kept = [n for n in today if n not in replaced and n not in dead]
print("today's, used by the step writer as they are:", len(kept), tot(today, kept))
print("the step writer's own (ExecStep.lean):", len(step), tot(step, step), "new names:", ", ".join(new))
print("Fix (Steps.lean):", steps.get("Fix"))
a = tot(today, kept); b = tot(step, step); c = steps.get("Fix", (0, 0))
print("the step writer in all: lines", a[0] + b[0] + c[0], "code lines", a[1] + b[1] + c[1])
for n in replaced:
    print(f"  {n}: today {today[n]}, step {step[n]}")
for n in dead:
    if n in today:
        print(f"  dead {n}: {today[n]}")
