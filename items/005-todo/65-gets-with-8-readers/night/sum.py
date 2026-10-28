#!/usr/bin/env python3
# bergdb 005-65: the summary of threads.sh's runs (ScaleBench C, 665 MB, ZGC, 4, 6 and 8
# threads, several builds in turns), from each run's JSON. One row per run and thread count,
# then each build's means, the longest gets, and the sampled readers' states. A row of a run
# ends with the eviction thread's cores; threads.sh counts those rows to check the parse.
# Written 2026-10-28 by Claude (Opus 5.5, Claude Code).
# Usage: python3 sum.py OUTDIR   (threads.sh's night/out/threads)
import glob, json, os, re, sys

out = sys.argv[1]
runs = []           # (build, round, name, json)
for f in sorted(glob.glob(os.path.join(out, 'f53-c-*.json'))):
    name = os.path.basename(f)[:-5]
    m = re.match(r'f53-c-[^-]+-b665-zgc-(.+)-(\d+)$', name)
    if not m:
        continue
    try:
        d = json.load(open(f))
    except Exception as e:
        print('%s: not read (%s)' % (name, e))
        continue
    runs.append((m.group(1), int(m.group(2)), name, d))
order = []
for b, r, n, d in sorted(runs, key=lambda x: (x[1], x[2])):
    if b not in order:
        order.append(b)
# Builds in the order of the first round as run (from runs.txt), if it is there.
try:
    started = [re.search(r'start (f53-c-\S+)', l).group(1) for l in open(os.path.join(out, 'runs.txt'))
               if re.search(r'start f53-c-', l)]
    o = []
    for n in started:
        b = re.match(r'f53-c-[^-]+-b665-zgc-(.+)-\d+$', n).group(1)
        if b not in o:
            o.append(b)
    if sorted(o) == sorted(order):
        order = o
except Exception:
    pass


def phases(d):
    return dict((p['phase'], p) for p in d['phases'] if 'phase' in p)


def cores(p, key):
    v = p.get(key)
    return None if v is None else v / 1000.0 / p['seconds']


def fmt(x, f='%.3f'):
    return '?' if x is None else f % x


print('# ScaleBench C, 665 MB, ZGC: 4, 6 and 8 threads (bergdb 005-65)\n')
print('Per run and thread count. Max and p99.9: the gets; waits: a reader\'s load waiting for the')
print('eviction thread over 10 ms, and the longest; batch wall: the eviction batches\' time by the')
print('clock; CPU in cores (CPU time over the phase\'s seconds): the readers, the rest of the')
print('process (the collector, the compiler), the eviction thread.\n')
print('| run | threads | gets a second | p99.9 us | max ms | waits > 10 ms | longest wait ms | batches | batch wall ms | eviction CPU ms | readers | rest | eviction |')
print('|---|---|---|---|---|---|---|---|---|---|---|---|---|')
agg = {}
tcounts = []
for b, r, n, d in sorted(runs, key=lambda x: (order.index(x[0]), x[1])):
    ph = phases(d)
    for k in sorted((k for k in ph if k.startswith('threads-')), key=lambda k: int(k.split('-')[1])):
        p = ph[k]
        t = int(k.split('-')[1])
        if t not in tcounts:
            tcounts.append(t)
        lat = p.get('latency', {})
        ev, rd, pr = p.get('evictionCpuMs'), p.get('readersCpuMs'), p.get('processCpuMs')
        rest = None if pr is None or rd is None else (pr - rd - (ev or 0)) / 1000.0 / p['seconds']
        print('| %s | %d | %s | %s | %s | %d | %s | %d | %d | %s | %s | %s | %s |' % (
            n, t, '{:,.0f}'.format(p['getsPerSec']), fmt(lat.get('p999Us'), '%.1f'),
            fmt(lat.get('maxUs', 0) / 1000.0, '%.2f'), p['afterLoadOver10ms'],
            fmt(p.get('afterLoadMaxMs'), '%.1f'), p['sweeps'], p['sweepMs'], fmt(ev, '%.0f'),
            fmt(cores(p, 'readersCpuMs'), '%.2f'), fmt(rest, '%.2f'), fmt(cores(p, 'evictionCpuMs'))))
        a = agg.setdefault((b, t), [])
        a.append((p['getsPerSec'], lat.get('maxUs', 0) / 1000.0, p['afterLoadOver10ms'],
                  p.get('afterLoadMaxMs') or 0, cores(p, 'evictionCpuMs'), p['sweepMs'], ev, rest))
tcounts.sort()

print('\n## Each build, the mean of its runs (longest: the most of its runs)\n')
print('| build | threads | runs | gets a second | longest get ms | waits > 10 ms a run | longest wait ms | eviction cores | batch wall over eviction CPU | rest cores |')
print('|---|---|---|---|---|---|---|---|---|---|')
for b in order:
    for t in tcounts:
        a = agg.get((b, t))
        if not a:
            continue
        n = len(a)
        evc = [x[4] for x in a if x[4] is not None]
        ratio = [x[5] / x[6] for x in a if x[6]]
        rest = [x[7] for x in a if x[7] is not None]
        print('| %s | %d | %d | %s | %.2f | %.1f | %.1f | %s | %s | %s |' % (
            b, t, n, '{:,.0f}'.format(sum(x[0] for x in a) / n), max(x[1] for x in a),
            sum(x[2] for x in a) / float(n), max(x[3] for x in a),
            fmt(sum(evc) / len(evc) if evc else None), fmt(sum(ratio) / len(ratio) if ratio else None, '%.2f'),
            fmt(sum(rest) / len(rest) if rest else None, '%.2f')))
print()
ref = order[0] if order else None
for t in tcounts:
    parts = []
    for b in order:
        a = agg.get((b, t))
        if a:
            parts.append('%s %s ms (%d waits)' % (b, ' and '.join('%.1f' % x[1] for x in a), sum(x[2] for x in a)))
    print('Longest get with %d threads, each run: %s' % (t, '; '.join(parts)))
if ref:
    for b in order[1:]:
        ch = []
        for t in tcounts:
            x, y = agg.get((ref, t)), agg.get((b, t))
            if x and y:
                gx, gy = sum(v[0] for v in x) / len(x), sum(v[0] for v in y) / len(y)
                ch.append('%d %+.1f%%' % (t, 100.0 * (gy - gx) / gx))
        print('%s against %s, gets a second: %s' % (b, ref, ', '.join(ch)))

print('\n## The sampled readers\' states (the five most frequent, and any in Eviction)\n')
for b, r, n, d in sorted(runs, key=lambda x: (order.index(x[0]), x[1])):
    for k, p in phases(d).items():
        if not k.startswith('sampled-'):
            continue
        st = p.get('statesPercent', {})
        top = sorted(st.items(), key=lambda kv: -kv[1])
        sel = top[:5] + [kv for kv in top[5:] if 'Eviction' in kv[0] or 'WAITING' in kv[0] or 'BLOCKED' in kv[0]]
        print('%s, %s, %s samples: %s' % (n, k, p.get('samples', '?'),
                                          '; '.join('%.1f%% %s' % (v, s) for s, v in sel)))
