#!/usr/bin/env python3
"""026-17, T7: the complexity counts C1 to C5 of section 5.7.

Usage: python3 counts.py CLONE DEPS > counts.txt
  CLONE: the trial's clone (/Users/f/fl/bench/026-17/bergdb);
  DEPS: the output of `lake env lean MtDeps.lean` (deps.txt).

Lines are cut into declarations as 006-28's count.py does (a declaration with
its doc comment). "Code" lines leave out comments and blank lines.
"""
import os
import re
import sys
sys.dont_write_bytecode = True

CLONE = sys.argv[1]
DEPS = sys.argv[2]
sys.path.insert(0, os.path.join(CLONE, 'items', '006-2026-q4', '28-simpler-algorithms'))
import count  # noqa: E402

LEAN = os.path.join(CLONE, 'lean')
FILES = {'SIS.Tree.Exec': 'SIS/Tree/Exec.lean', 'SIS.Tree.Node': 'SIS/Tree/Node.lean',
         'SIS.Tree.Val': 'SIS/Tree/Val.lean', 'SIS.Basic': 'SIS/Basic.lean',
         'SIS.Tree.Mt': 'SIS/Tree/Mt.lean'}


def read(rel):
    with open(os.path.join(LEAN, rel), encoding='utf-8') as f:
        lines = f.read().split('\n')
    if lines and lines[-1] == '':
        lines.pop()
    return lines


def code_lines(lines):
    """Lines that are neither blank nor comment (block comments, doc comments, --)."""
    n = 0
    depth = 0
    for line in lines:
        s = line
        out = ''
        i = 0
        while i < len(s):
            if s.startswith('/-', i):
                depth += 1
                i += 2
            elif depth > 0 and s.startswith('-/', i):
                depth -= 1
                i += 2
            elif depth > 0:
                i += 1
            elif s.startswith('--', i):
                break
            else:
                out += s[i]
                i += 1
        if out.strip():
            n += 1
    return n


def decl_table(rel):
    """{name: (start, nlines)} for the declarations of a file."""
    t = {}
    pos = 0
    for kind, name, n in count.decls(os.path.join(LEAN, rel)):
        if kind:
            t[name] = (pos, n)
        pos += n
    return t


TABLES = {m: decl_table(r) for m, r in FILES.items()}
TEXT = {m: read(r) for m, r in FILES.items()}


def locate(module, full):
    """The declaration of a constant: its name within its namespace, or the
    longest prefix that is a declaration (a structure's field, a constructor,
    a `where` function)."""
    short = full
    for ns in ('SIS.Tree.Mt.', 'SIS.Tree.', 'SIS.'):
        if short.startswith(ns):
            short = short[len(ns):]
            break
    t = TABLES.get(module, {})
    parts = short.split('.')
    for k in range(len(parts), 0, -1):
        cand = '.'.join(parts[:k])
        if cand in t:
            return cand
    return None


def deps():
    today, mt, calls = {}, {}, []
    with open(DEPS, encoding='utf-8') as f:
        for line in f:
            w = line.split()
            if not w:
                continue
            if w[0] == 'TODAY':
                today[w[2]] = w[1]
            elif w[0] == 'MT':
                mt[w[2]] = w[1]
            elif w[0] == 'CALL':
                calls.append((w[1], w[2]))
    return today, mt, calls


def decls_of(names):
    """{(module, decl)} for constants {name: module}."""
    out = set()
    for full, module in names.items():
        d = locate(module, full)
        if d is not None:
            out.add((module, d))
    return out


def lines_of(module, d):
    s, n = TABLES[module][d]
    return n, code_lines(TEXT[module][s:s + n])


def main():
    today, mt, calls = deps()
    td, md = decls_of(today), decls_of(mt)

    # ---- C1: what MT adds, Mt.lean by part.
    mtl = TEXT['SIS.Tree.Mt']
    total = len(mtl)
    tab = TABLES['SIS.Tree.Mt']
    parts = [
        ("R1's wrappers (deleteLeaf, setValue, putSegs, putKv, boundsNow, runWith, runUser)",
         ['deleteLeaf', 'setValue', 'putSegs', 'putKv', 'boundsNow', 'runWith', 'runUser']),
        ('the path and the target (pathGo, path, Fix, targetGo, target)',
         ['pathGo', 'path', 'Fix', 'targetGo', 'target']),
        ('the merge (merge)', ['merge']),
        ('the other fixes and the step (unlinkTree, collapse, fixStep, runFix)',
         ['unlinkTree', 'collapse', 'fixStep', 'runFix']),
        ('the driver (deletedKeys, Step, groupFuel, fixKey, fixGo, fixAll)',
         ['deletedKeys', 'Step', 'groupFuel', 'fixKey', 'fixGo', 'fixAll']),
        ('for the program (pathAt)', ['pathAt']),
        ('rule added A1 (scanWith, scanFuel)', ['scanWith', 'scanFuel']),
    ]
    print('C1, added: lean/SIS/Tree/Mt.lean')
    print(f'  the file: {total} lines, {code_lines(mtl)} of code')
    used = 0
    sums = {}
    for label, names in parts:
        a = c = 0
        for nm in names:
            s, n = tab[nm]
            a += n
            c += code_lines(mtl[s:s + n])
        used += a
        sums[label] = (a, c)
        print(f'  {label}: {a} lines, {c} of code')
    # The header, the sections' comments, the small cases.
    small = [nm for nm in tab if nm not in sum((p[1] for p in parts), [])]
    s0 = min(tab[nm][0] for nm in small)
    a = total - s0
    print(f'  the small cases (namespace Small, 11 guards): {a} lines, {code_lines(mtl[s0:])} of code')
    print(f'  the rest (header with D1 to D9, section comments, imports, namespace): {total - used - a} lines')
    writer = ['R1', 'the path', 'the merge', 'the other fixes', 'the driver']
    wa = sum(v[0] for k, v in sums.items() if any(k.startswith(w) for w in writer))
    wc = sum(v[1] for k, v in sums.items() if any(k.startswith(w) for w in writer))
    copies = ['setValue', 'putSegs', 'putKv', 'runWith', 'merge']
    ca = sum(tab[nm][1] for nm in copies)
    cc = sum(code_lines(mtl[tab[nm][0]:tab[nm][0] + tab[nm][1]]) for nm in copies)
    print(f'  MT\'s writer (R1 to R5): {wa} lines, {wc} of code; of them copied with changes from'
          f' Exec.lean (setValue, putSegs, putKv, runWith as runOpsFrom, merge): {ca}, {cc} of code;'
          f' new: {wa - ca}, {wc - cc} of code')
    print()

    # ---- C2: freed.
    freed = sorted(td - md)
    print('C2, freed: today\'s definitions that exec? uses and MT\'s entry points'
          ' (runUser, runFix, fixAll, with changesOf) do not')
    copied = {'exec?', 'runOps', 'runOpsFrom', 'setValue', 'putSegs', 'putKv', 'merge'}
    iface = {'Tx', 'Changes'}
    groups = {'dead': [], 'copied': [], 'interface': []}
    for module, d in freed:
        n, c = lines_of(module, d)
        g = 'copied' if d in copied else 'interface' if d in iface else 'dead'
        groups[g].append((module, d, n, c))
    labels = {'dead': 'freed: no counterpart in MT',
              'copied': 'replaced by a copy in Mt.lean (deleteUpward\'s first lines are'
                        ' Mt.deleteLeaf; it is listed as freed above)',
              'interface': 'the interface of exec? (a transaction, its changes): stays'}
    for g in ('dead', 'copied', 'interface'):
        ta = sum(x[2] for x in groups[g])
        tc = sum(x[3] for x in groups[g])
        print(f'  {labels[g]}: {len(groups[g])} definitions, {ta} lines, {tc} of code')
        for module, d, n, c in groups[g]:
            print(f'    {module.split(".")[-1]}.lean {d}: {n} lines, {c} of code')
    exec_freed = sum(x[2] for x in groups['dead'] + groups['copied'] if x[0] == 'SIS.Tree.Exec')
    exec_freed_c = sum(x[3] for x in groups['dead'] + groups['copied'] if x[0] == 'SIS.Tree.Exec')
    dead_exec = sum(x[2] for x in groups['dead'] if x[0] == 'SIS.Tree.Exec')
    dead_exec_c = sum(x[3] for x in groups['dead'] if x[0] == 'SIS.Tree.Exec')
    # The check of 7.1: no freed definition is named by Mt.lean's code (comments out).
    mtcode = re.sub(r'/-.*?-/', '', '\n'.join(mtl), flags=re.S)
    mtcode = re.sub(r'--[^\n]*', '', mtcode)
    named = [d for m, d, n, c in groups['dead']
             if re.search(r'(?<![A-Za-z0-9_.])' + re.escape(d.split('.')[-1]) + r'(?![A-Za-z0-9_])', mtcode)]
    print(f'  check (a grep of Mt.lean\'s code, comments out): freed definitions it names: '
          f'{", ".join(named) or "none"}')
    print(f'  in Exec.lean: freed {dead_exec} lines ({dead_exec_c} of code), with the copied'
          f' originals {exec_freed} ({exec_freed_c} of code)')
    print('  new in MT (Mt.lean\'s writer): ' + ', '.join(sorted(d for m, d in md - td)))
    print()

    # The definitions MT keeps only for the split's code, and what they do in MT.
    print('Kept by MT, by the calls (the walk\'s CALL lines among MT\'s definitions);'
          ' what each does in MT, by reading (T3, findings 3 and 4):')
    what = {
        'SIS.Tree.KNode.toPrev': 'kept and live: in a user transaction a node that an earlier'
            ' operation changed and a later one splits loses its klongs of tt (the take-back of a'
            ' change, of entries, not of a node); a no-op in a fix step',
        'SIS.Tree.unlink': 'kept, dead: replaceRoot calls it, and a root that a fix step collapses'
            ' has no klong of the step\'s time',
        'SIS.Tree.replacedBy': 'kept, dead: read only to write W.madeFor again',
        'SIS.Tree.setMadeFor': 'kept, dead: writes W.madeFor, which no decision of MT reads',
    }
    for callee in ('SIS.Tree.KNode.toPrev', 'SIS.Tree.unlink', 'SIS.Tree.replacedBy',
                   'SIS.Tree.setMadeFor'):
        callers = sorted({a.replace('SIS.Tree.', '') for a, b in calls if b == callee})
        print(f'  {callee.replace("SIS.Tree.", "")}: called by {", ".join(callers)}; {what[callee]}')
    # The fields of W: who writes (field :=) and who reads (.field, not in a `with`
    # update) among the definitions MT uses, by their text.
    print('The fields of W, by text, in the definitions MT uses (Exec.lean, Mt.lean'
          ' without the small cases):')
    mtdecls = sorted((m, d) for m, d in md if m in ('SIS.Tree.Exec', 'SIS.Tree.Mt'))
    for field in ('taken', 'madeFor', 'outside', 'merges', 'spaceSplits', 'trail'):
        reads, writes = [], []
        for module, d in mtdecls:
            if module == 'SIS.Tree.Mt' and d in small:
                continue
            s, n = TABLES[module][d]
            text = '\n'.join(TEXT[module][s:s + n])
            body = re.sub(r'/-.*?-/', '', text, flags=re.S)
            if re.search(r'\b' + field + r'\s*:=', body):
                writes.append(d)
            # `p.merges` is the parameters' field, not W's.
            if any(m.group(1) not in ('p', 'Params') for m in re.finditer(r'(\w*)\.' + field + r'\b', body)):
                reads.append(d)
        print(f'  W.{field}: written by {", ".join(writes) or "none"}; read by'
              f' {", ".join(reads) or "none"}')
    print('  so: W.taken kept (changesOf), dead (never written: always empty); W.madeFor kept'
          ' (the splits), dead (read only by replacedBy, to write it again); W.outside kept and'
          ' live (newKey writes it, boundsNow decides by it, D3); merges, spaceSplits, trail:'
          ' counts for the checks, no rule reads them, as today')
    print()

    # ---- C3: net.
    exec_total = len(TEXT['SIS.Tree.Exec'])
    net = exec_total - exec_freed + wa
    net_c = code_lines(TEXT['SIS.Tree.Exec']) - exec_freed_c + wc
    print(f'C3, net: Exec.lean {exec_total} lines ({code_lines(TEXT["SIS.Tree.Exec"])} of code);'
          f' less the freed and the copied originals {exec_freed} ({exec_freed_c}); plus MT\'s'
          f' writer {wa} ({wc}): {net} lines ({net_c} of code), {net - exec_total:+d}'
          f' ({net_c - code_lines(TEXT["SIS.Tree.Exec"]):+d} of code)')
    print(f'  Node.lean besides: freed {sum(x[2] for x in groups["dead"] if x[0] == "SIS.Tree.Node")}'
          ' lines (smallestLive)')
    print()

    # ---- C4: the proofs that name what MT frees.
    tree = os.path.join(LEAN, 'SIS', 'Tree')
    files = sorted(f for f in os.listdir(tree) if f.endswith('.lean') and f != 'Mt.lean')
    data = []
    tot = 0
    for f in files:
        lines = read(os.path.join('SIS', 'Tree', f))
        tot += len(lines)
        pos = 0
        for kind, name, n in count.decls(os.path.join(tree, f)):
            data.append((f, kind, name, '\n'.join(lines[pos:pos + n]), n))
            pos += n
    dead_names = sorted({d.split('.')[-1] for m, d, n, c in groups['dead']})
    pats = [
        ('freed (C2, no counterpart): ' + ', '.join(dead_names), '|'.join(dead_names)),
        ('kept by the split\'s code, dead in MT: replacedBy, setMadeFor, madeFor, W.taken, unlink',
         r'replacedBy|setMadeFor|madeFor|MadeFor|\.taken\b|taken\s*:=|unlink'),
        ('both', '|'.join(dead_names) + r'|replacedBy|setMadeFor|madeFor|MadeFor|\.taken\b|taken\s*:=|unlink'),
        ('the copied originals, for context: merge, setValue, putSegs, putKv, runOps, exec?',
         r'\bmerge\b|setValue|putSegs|putKv|runOps|exec\?'),
    ]
    print(f'C4, the proofs that name what is freed (006-28\'s method, by text; lean/SIS/Tree'
          f' without Mt.lean: {len(files)} files, {tot} lines, {len(data)} pieces)')
    def nocomment(text):
        text = re.sub(r'/-.*?-/', '', text, flags=re.S)
        return re.sub(r'--[^\n]*', '', text)
    codes = [nocomment(x[3]) for x in data]
    for label, pat in pats:
        rx = re.compile(pat)
        fs = set()
        td_ = tl = nd = nl = cd = cl = 0
        for (f, kind, name, text, n), code in zip(data, codes):
            if rx.search(text):
                fs.add(f)
                td_ += 1
                tl += n
            if rx.search(code):
                cd += 1
                cl += n
            if kind and rx.search(name):
                nd += 1
                nl += n
        print(f'  {label}')
        print(f'    files {len(fs)}; by name {nd} declarations, {nl} lines; by text {td_}'
              f' declarations, {tl} lines, {100 * tl / tot:.1f} %; by text without comments {cd}'
              f' declarations, {cl} lines, {100 * cl / tot:.1f} %')
    print()

    # ---- C5: the invariant between.
    t = read('MtTest.lean')
    s = next(i for i, l in enumerate(t) if l.startswith('def k5Allowed'))
    j = s - 1
    while j >= 0 and (t[j].startswith('/--') or (t[j].strip() and not t[j].startswith('def ')
                                                   and t[j - 1].strip() != '')):
        if t[j].startswith('/--'):
            break
        j -= 1
    e = s + 1
    while e < len(t) and t[e].strip() != '' and not t[e].startswith('def ') \
            and not t[e].startswith('/--'):
        e += 1
    print(f'C5, the invariant between: MtTest.lean\'s k5Allowed, {e - s} lines of code'
          f' (lines {s + 1} to {e}); with the pending keys\' paths that it is given (Mt.pathAt,'
          f' {TABLES["SIS.Tree.Mt"]["pathAt"][1]} lines)')
    print('\n'.join('    ' + x for x in t[s:e]))


main()
