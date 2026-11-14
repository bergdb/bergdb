#!/usr/bin/env python3
"""025-02 tool (2026-11-14; prune's copy: a dead declaration's doc comment goes with it): what of lean/SIS/Tree may go, from Reach.lean's output.

Usage, from the clone's lean/ directory:
  python3 prune.py reach-decls.tsv [--apply] [--keep FILE] [--report OUT]

Kept: every declaration that Reach.lean found reached (rootReach 1), and every
declaration that a kept one uses, by its proof terms (deps) or by a name in its source
text (comments stripped; this covers rfl simp lemmas, `simp only [..]`, `unfold`).
Also kept: every @[simp] declaration, every name in the text between declarations
(attribute, macro, #guard, example, open ... in), and the names in --keep FILE.
What is left may go. A range is cut only if it overlaps no kept range. A file left with
no declaration is removed, and every `import` of it is replaced by its own imports.
Without --apply it only reports (lines per file before and after, the names that go).
"""
import os, re, sys, collections

args = sys.argv[1:]
tsv = args[0]
apply_ = "--apply" in args
keepf = args[args.index("--keep") + 1] if "--keep" in args else None
report = args[args.index("--report") + 1] if "--report" in args else "prune-report.txt"

decls = {}  # name -> dict
for line in open(tsv):
    parts = line.rstrip("\n").split("\t")
    if len(parts) < 6:
        continue
    name, mod, kind, a, b, r = parts[:6]
    deps = parts[6].split(",") if len(parts) > 6 and parts[6] else []
    decls[name] = dict(mod=mod, kind=kind, a=int(a), b=int(b), r=r == "1", deps=deps)

def path_of(mod):
    return mod.replace(".", "/") + ".lean"

src = {}
for d in decls.values():
    p = path_of(d["mod"])
    if p not in src and os.path.exists(p):
        src[p] = open(p).read().split("\n")

def strip_comments(text):
    out, i, depth, n = [], 0, 0, len(text)
    while i < n:
        if text.startswith("/-", i):
            depth += 1; i += 2; continue
        if depth and text.startswith("-/", i):
            depth -= 1; i += 2; continue
        if depth:
            i += 1; continue
        if text.startswith("--", i):
            j = text.find("\n", i); i = n if j < 0 else j; continue
        out.append(text[i]); i += 1
    return "".join(out)

ident = re.compile(r"[A-Za-z_α-ω][A-Za-z0-9_'!?α-ω₀-₉]*(?:\.[A-Za-z_][A-Za-z0-9_'!?]*)*")
by_suffix = collections.defaultdict(set)
for n in decls:
    comps = n.split(".")
    for k in range(1, len(comps) + 1):
        by_suffix[".".join(comps[-k:])].add(n)

def names_in(text):
    found = set()
    for tok in ident.findall(strip_comments(text)):
        comps = tok.split(".")
        for i in range(len(comps)):
            for j in range(i + 1, len(comps) + 1):
                found |= by_suffix.get(".".join(comps[i:j]), set())
    return found

def text_of(n):
    d = decls[n]
    lines = src.get(path_of(d["mod"]))
    if not lines or d["a"] == 0:
        return ""
    return "\n".join(lines[d["a"] - 1 : d["b"]])

# the model and its statements: the SIS.Tree modules that SIS.lean imports itself
ROOT_MODS = {"SIS.Tree." + m for m in "Val Node Exec Read Spec Inv Props Bound Top MergeProps DeadProps MergeOpBoundProof".split()}
roots = {n for n, d in decls.items() if d["r"] or d["mod"] in ROOT_MODS}
# refutations and examples are results: a module named for them, a name that says not_ or
# counterexample (the statements found false, 006-26, section 6.3)
roots |= {n for n, d in decls.items()
          if re.search(r"Counterexample|Example", d["mod"]) or re.search(r"(^|[._])not_|_not_|[cC]ounterexample", n.split(".")[-1])}
simp = {n for n in decls if re.search(r"@\[[^\]]*\bsimp\b", text_of(n)[:400])}
roots |= simp
between = set()
for p, lines in src.items():
    mask = [True] * (len(lines) + 2)
    for n, d in decls.items():
        if path_of(d["mod"]) == p and d["a"]:
            for k in range(d["a"], d["b"] + 1):
                mask[k] = False
    rest = "\n".join(l for k, l in enumerate(lines, 1) if mask[k] and not l.startswith("import "))
    between |= names_in(rest)
roots |= between
if keepf:
    for l in open(keepf):
        l = l.strip()
        if l and not l.startswith("#"):
            roots |= by_suffix.get(l, set())

kept, stack = set(), list(roots)
while stack:
    n = stack.pop()
    if n in kept or n not in decls:
        continue
    kept.add(n)
    for d in decls[n]["deps"]:
        if d not in kept:
            stack.append(d)
    for d in names_in(text_of(n)):
        if d not in kept:
            stack.append(d)

dead = [n for n in decls if n not in kept]
cut = collections.defaultdict(list)  # path -> [(a, b, name)]
for n in dead:
    d = decls[n]
    if d["a"] == 0:
        continue
    p = path_of(d["mod"])
    clash = any(path_of(decls[k]["mod"]) == p and decls[k]["a"] and not (decls[k]["b"] < d["a"] or decls[k]["a"] > d["b"]) for k in kept)
    if not clash:
        a = d["a"]
        while True:
            # a `set_option ... in`, `open ... in`, `include ... in` or `omit ... in` before it goes too
            while a > 1 and re.match(r"^(set_option|open|include|omit) .* in\s*$", src[p][a - 2]):
                a -= 1
            # prune's copy (025-02, 2026-11-14): a doc comment that ends on the line before it goes
            # too (a macro's range leaves its docstring out; left alone it stands before the next
            # docstring or `end`, a parse error)
            if a > 1 and src[p][a - 2].rstrip().endswith("-/"):
                k = a - 2
                while k > 0 and "/-" not in src[p][k]:
                    k -= 1
                if src[p][k].lstrip().startswith("/--") and not any(
                        path_of(decls[q]["mod"]) == p and decls[q]["a"] and decls[q]["a"] <= a - 1 and decls[q]["b"] >= k + 1
                        for q in kept):
                    a = k + 1
                    continue
            break
        cut[p].append((a, d["b"], n))

out = []
tot_before = tot_after = 0
gone_files = []
newsrc = {}
for p, lines in sorted(src.items()):
    drop = set()
    for a, b, n in cut.get(p, []):
        drop.update(range(a, b + 1))
    keep_lines = [l for k, l in enumerate(lines, 1) if k not in drop]
    # collapse runs of blank lines left behind
    tidy = []
    for l in keep_lines:
        if l.strip() == "" and tidy and tidy[-1].strip() == "":
            continue
        tidy.append(l)
    has_decl = any(path_of(decls[k]["mod"]) == p for k in kept)
    # a file that defines a macro, syntax or notation stays (other files may use it)
    if any(re.match(r"^(local |scoped )?(macro|macro_rules|syntax|notation|infix|infixl|infixr|elab) ", l) for l in lines):
        has_decl = True
    before, after = len(lines), (len(tidy) if has_decl else 0)
    tot_before += before; tot_after += after
    if not has_decl:
        gone_files.append(p)
    newsrc[p] = tidy
    out.append(f"FILE {p} {before} -> {after}")
out.append(f"TOTAL SIS/Tree files with declarations: {len(src)}; lines {tot_before} -> {tot_after}; files removed {len(gone_files)}")
out.append(f"DECLS {len(decls)} kept {len(kept)} (reached {sum(1 for d in decls.values() if d['r'])}, simp {len(simp)}, between {len(between & set(decls))}) dead {len(dead)}")
out += [f"GONE {p}" for p in gone_files]
out += [f"DEAD {decls[n]['mod']} {decls[n]['kind']} {n}" for n in sorted(dead)]
open(report, "w").write("\n".join(out) + "\n")
print("\n".join(out[-(len(dead) + len(gone_files) + 2):][:2]) if False else out[len(src)])
print(out[len(src) + 1])

if apply_:
    gone_mods = {p[:-5].replace("/", ".") for p in gone_files}
    imports_of = {}
    for p in gone_files:
        imports_of[p[:-5].replace("/", ".")] = [l.split()[1] for l in src[p] if l.startswith("import ")]
    def expand(m, seen=None):
        seen = seen or set()
        if m not in gone_mods:
            return [m]
        res = []
        for i in imports_of[m]:
            if i not in seen:
                seen.add(i); res += expand(i, seen)
        return res
    for p in gone_files:
        os.remove(p)
    allfiles = [os.path.join(dp, f) for dp, _, fs in os.walk(".") if ".lake" not in dp for f in fs if f.endswith(".lean")]
    for f in allfiles:
        lines = newsrc.get(f[2:]) or open(f).read().split("\n")
        res, seen = [], set()
        changed = f[2:] in newsrc
        for l in lines:
            if l.startswith("import ") and l.split()[1] in gone_mods:
                changed = True
                for m in expand(l.split()[1]):
                    if m not in seen:
                        seen.add(m); res.append("import " + m)
            else:
                if l.startswith("import "):
                    if l.split()[1] in seen:
                        continue
                    seen.add(l.split()[1])
                res.append(l)
        if changed:
            open(f, "w").write("\n".join(res))
    print(f"applied: {len(gone_files)} files removed, ranges cut in {len(cut)} files")
