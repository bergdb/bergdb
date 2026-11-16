#!/usr/bin/env python3
"""026-17, T8: totals over the runs' summaries (runs/30-*.txt, runs/8-*.txt).

Usage: python3 aggregate.py RUNS_DIR > aggregate.txt
Reads only the summary lines that MtTest prints at a run's end.
"""
import glob
import os
import re
import sys

RUNS = sys.argv[1]


def parse(path):
    r = {'file': os.path.basename(path), 'reach': {}}
    for line in open(path, encoding='utf-8'):
        m = re.search(r'\[MtTest\.Mode\.(\w+)\]: (\d+) runs, (\d+) groups, (\d+) boundaries \((\d+) untidy\), (\d+) beyond the level bounds, (\d+) failures', line)
        if m:
            r['mode'] = m.group(1)
            r['runs'], r['groups'], r['bnd'], r['untidy'], r['bounds'], r['fails'] = map(int, m.groups()[1:])
        m = re.search(r'K7 second pass: (\d+)', line)
        if m:
            r['k7'] = int(m.group(1))
        m = re.search(r'K4 at tidy boundaries: (\d+)', line)
        if m:
            r['k4'] = int(m.group(1))
        if line.startswith('  5.5 cost MT/today:'):
            nums = re.findall(r'(\d+)/(\d+)', line)
            keys = ['made', 'changed', 'klongs', 'tops', 'bnew', 'ball', 'ibnew', 'iball']
            for k, (a, b) in zip(keys, nums):
                r[k] = (int(a), int(b))
        m = re.match(r'  5\.5 a deleted key \((\d+)\)', line)
        if m:
            r['dels'] = int(m.group(1))
        if line.startswith("  reached MT's fix steps:"):
            for name, n in re.findall(r'([\w.]+) (\d+)', line.split(':', 1)[1]):
                r['reach'][name] = int(n)
        m = re.match(r'  5\.6 fix steps a group with deletes .*; most (\d+); nearest the driver\'s fuel: (\d+) of (\d+)', line)
        if m:
            r['most'], r['nearA'], r['nearB'] = map(int, m.groups())
        m = re.match(r'  5\.6 height: MT\'s greatest above before and today\'s in (\d+) groups.*H needed: MT (\d+), today (\d+)', line)
        if m:
            r['hAbove'], r['hMt'], r['hToday'] = map(int, m.groups())
        m = re.match(r'  A1: .* differ: (\d+), at (\d+) boundaries', line)
        if m:
            r['a1'], r['a1b'] = map(int, m.groups())
        m = re.match(r'  5\.6 untidy: .*most such key nodes at one: (\d+)', line)
        if m:
            r['emptyIdx'] = int(m.group(1))
    return r


def total(rs, k):
    return sum(r.get(k, 0) for r in rs)


def pair(rs, k):
    return (sum(r[k][0] for r in rs if k in r), sum(r[k][1] for r in rs if k in r))


def show(label, rs):
    print(f'== {label}: {len(rs)} files, {total(rs, "runs")} runs, {total(rs, "groups")} groups,'
          f' {total(rs, "bnd")} boundaries ({total(rs, "untidy")} untidy), failures {total(rs, "fails")},'
          f' bounds {total(rs, "bounds")}, K4 faults at tidy {total(rs, "k4")}, K7 second pass {total(rs, "k7")}')
    reach = {}
    for r in rs:
        for k, v in r['reach'].items():
            reach[k] = reach.get(k, 0) + v
    fx = ['fix.merge.one', 'fix.merge.two', 'fix.merge.inner', 'fix.merge.empty', 'fix.merge.bothempty',
          'fix.unlink', 'fix.collapse.space', 'fix.collapse.segment', 'fix.pass.onlychild']
    print('  fix steps by kind: ' + ', '.join(f'{k} {reach.get(k, 0)}' for k in fx))
    print('  inside fix steps: ' + ', '.join(f'{k} {reach.get(k, 0)}' for k in
          ['merge.parent.full', 'merge.parent.dead', 'split.time1', 'split.time2', 'split.space1',
           'split.space2', 'split.space3', 'bitmap.full', 'bitmap.dead']))
    steps = reach.get('fix.merge.one', 0) + reach.get('fix.merge.two', 0) + reach.get('fix.unlink', 0) + \
        reach.get('fix.collapse.space', 0) + reach.get('fix.collapse.segment', 0)
    dels = total(rs, 'dels')
    print(f'  fix steps {steps} for {dels} deleted keys: {steps / dels:.3f} a deleted key' if dels else
          f'  fix steps {steps}')
    print(f'  most fix steps of one group: {max(r.get("most", 0) for r in rs)}'
          f' ({max(rs, key=lambda r: r.get("most", 0))["file"]})')
    for k, name in [('made', 'made'), ('changed', 'changed'), ('klongs', 'klongs'), ('bnew', 'B-new'),
                    ('ball', 'B-all'), ('ibnew', 'B-new, the index alone'), ('iball', 'B-all, the index alone')]:
        a, b = pair(rs, k)
        if b:
            print(f'  {name}: MT {a}, today {b}, {a / b:.3f}')
    a, b = pair(rs, 'bnew')
    c, d = pair(rs, 'ball')
    if dels:
        print(f'  a deleted key: B-new {(a - b) / dels:+.1f} bytes, B-all {(c - d) / dels:+.1f} bytes,'
              f' made {(pair(rs, "made")[0] - pair(rs, "made")[1]) / dels:+.3f} nodes')
    print(f'  height between: groups where MT\'s greatest is above before and today\'s:'
          f' {total(rs, "hAbove")}; H needed MT/today by file: ' +
          ', '.join(f'{r["file"]} {r.get("hMt")}/{r.get("hToday")}' for r in rs if r.get('hMt') != r.get('hToday')))
    print(f'  A1: untidy scans where scan and scanWith differ: {total(rs, "a1")} at {total(rs, "a1b")}'
          f' boundaries; most index nodes without a live key below at one boundary:'
          f' {max(r.get("emptyIdx", 0) for r in rs)}')
    print('  by file: ' + '; '.join(
        f'{r["file"]}: B-new {r["bnew"][0] / r["bnew"][1]:.2f}, B-all {r["ball"][0] / r["ball"][1]:.2f},'
        f' made {r["made"][0] / r["made"][1]:.2f}, fix/del {sum(r["reach"].get(k, 0) for k in ["fix.merge.one", "fix.merge.two", "fix.unlink", "fix.collapse.space", "fix.collapse.segment"]) / r["dels"]:.3f}'
        for r in rs if 'bnew' in r and r.get('dels')))


r30 = [parse(p) for p in sorted(glob.glob(os.path.join(RUNS, '30-*.txt')))]
r8 = [parse(p) for p in sorted(glob.glob(os.path.join(RUNS, '8-*.txt')))]
show('node size 30 (T5)', r30)
show('node size 8 (T6)', r8)
show('node size 8 without D (T6\'s treetest sets)', [r for r in r8 if r['file'] != '8-D.txt'])


def table(rs):
    print('| run | groups | bnd | untidy | dels | fix/del | most | made | B-new | B-all | idx B-new |')
    print('|---|---|---|---|---|---|---|---|---|---|---|')
    for r in rs:
        fx = sum(r['reach'].get(k, 0) for k in ['fix.merge.one', 'fix.merge.two', 'fix.unlink',
                                                'fix.collapse.space', 'fix.collapse.segment'])
        d = r.get('dels', 0)
        q = lambda k: f'{r[k][0] / r[k][1]:.2f}' if k in r and r[k][1] else '-'
        print(f'| {r["file"][:-4]} | {r["groups"]} | {r["bnd"]} | {r["untidy"]} | {d} |'
              f' {fx / d:.3f} | {r.get("most", 0)} | {q("made")} | {q("bnew")} | {q("ball")} |'
              f' {q("ibnew")} |' if d else
              f'| {r["file"][:-4]} | {r["groups"]} | {r["bnd"]} | {r["untidy"]} | 0 | - |'
              f' {r.get("most", 0)} | {q("made")} | {q("bnew")} | {q("ball")} | {q("ibnew")} |')


print()
table(r30)
print()
table(r8)
