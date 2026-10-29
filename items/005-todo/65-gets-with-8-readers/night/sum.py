#!/usr/bin/env python3
# bergdb 005-65: the summary of threads.sh's runs (ScaleBench C, 665 MB, ZGC, 4, 6 and 8
# threads, several builds in turns), from each run's JSON. One row per run and thread count,
# then each build's means, the longest gets, and the sampled readers' states. A row of a run
# ends with the eviction thread's cores; threads.sh counts those rows to check the parse.
# Then, for the entry's reading (ScaleBench-065.diff's second line for each threads phase),
# where the time went: the gets and the after-load calls over 10 ms, and whether the calls
# began under pressure; the readers' time blocked and parked; the eviction thread's time
# running, waiting and neither; the machine's busy cores and the other processes'.
# Written 2026-10-28 by Claude (Opus 5.5, Claude Code). 2026-10-29, for the rerun with 005-65's
# fix (ScaleBench-065.diff's third version): the calls that entered evictorLock, an estimate.
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

# 005-65's reading: where the time went (ScaleBench-065.diff's second line for each threads
# phase). A row's first cell is "BUILD rROUND", not the run's name: threads.sh counts the
# rows of the first table, which start with "| f53-". '?' where a run has no such figure.


def ratio(x, y, scale=1.0):
    return None if x is None or not y else scale * x / y


def runs_by_order():
    return sorted(runs, key=lambda x: (order.index(x[0]), x[1]))


def tphases(d):
    ph = phases(d)
    return [(int(k.split('-')[1]), ph[k]) for k in sorted((k for k in ph if k.startswith('threads-')),
                                                         key=lambda k: int(k.split('-')[1]))]


def blocked_pct(p, t):
    ms = p.get('readersBlockedMs')
    return None if ms is None or ms < 0 else 100.0 * ms / 1000.0 / (t * p['seconds'])


def ev_pcts(p):
    """The eviction thread's share of the phase in percent: running (its CPU time); waiting for
    a request (Object.wait), with the wait's re-entry into evictorLock, which the JVM counts as
    waited and as blocked both; and the rest: runnable without a core, or blocked on a monitor
    outside a wait. And its contended entries outside waits: blocked less waited (each wait
    that a notify ends counts one blocked entry)."""
    sec = p['seconds'] * 1000.0
    cpu, bl, wa = p.get('evictionCpuMs'), p.get('evictorBlocked'), p.get('evictorWaitedMs')
    if cpu is None or bl is None or wa is None or wa < 0:
        return None
    run, wait = 100.0 * cpu / sec, 100.0 * wa / sec
    return [run, wait, 100.0 - run - wait, bl - p.get('evictorWaited', 0)]


def others(p):
    mc, pr = p.get('machineCores'), p.get('processCpuMs')
    return None if mc is None or pr is None else mc - pr / 1000.0 / p['seconds']


print('\n## Where the time went: gets and after-load calls\n')
print('Gets over 10 ms (from the histogram); after-load calls over 10 ms, and of them those that')
print('began under pressure (the resident bytes over the trigger by more than the gap between the')
print('watermarks, so that afterLoad may park for a batch); the mean after-load call; the calls')
print('over the trigger and of them those that entered the monitor evictorLock in Eviction.wake')
print('(every call over the trigger before 005-65\'s fix; with it, only one that finds no request')
print('pending: an estimate, from the flag read just before the call; ? for a run without the')
print('figure); the calls under pressure; the longest call without pressure; the readers\' time')
print('blocked on monitors (percent of their time, and the times a second) and parked (LockSupport:')
print('afterLoad\'s wait).\n')
print('| run | threads | gets > 10 ms | after-load > 10 ms | of them under pressure | after-load ns a call | over the trigger, k a second | entering evictorLock, k a second | under pressure | longest without pressure ms | readers blocked % | blocked, k a second | readers parked ms |')
print('|---|---|---|---|---|---|---|---|---|---|---|---|---|')
for b, r, n, d in runs_by_order():
    for t, p in tphases(d):
        sec = p['seconds']
        rb = p.get('readersBlocked')
        rw = p.get('readersWaitedMs')
        print('| %s r%d | %d | %s | %d | %s | %s | %s | %s | %s | %s | %s | %s | %s |' % (
            b, r, t, fmt(p.get('getsOver10ms'), '%d'), p['afterLoadOver10ms'],
            fmt(p.get('afterLoadOver10msUnderPressure'), '%d'),
            fmt(ratio(p.get('afterLoadMs'), p.get('afterLoadCalls'), 1e6), '%.0f'),
            fmt(ratio(p.get('afterLoadWakeCalls'), sec, 1e-3), '%.0f'),
            fmt(ratio(p.get('afterLoadEnterCalls'), sec, 1e-3), '%.0f'),
            fmt(p.get('afterLoadPressureCalls'), '%d'), fmt(p.get('afterLoadMaxCalmMs'), '%.1f'),
            fmt(blocked_pct(p, t), '%.2f'), fmt(None if rb is None or rb < 0 else rb / sec / 1000.0, '%.1f'),
            fmt(None if rw is None or rw < 0 else rw, '%d')))

print('\n## Where the time went: the eviction thread and the machine\n')
print('Batches: their number, mean and the longest of the run so far (Eviction keeps no maximum')
print('per phase), by the clock, and their time by the clock over the eviction thread\'s CPU time.')
print('The eviction thread\'s share of the phase: running (its CPU time); waiting for a request')
print('(Object.wait, with the re-entry into evictorLock after it); the rest: runnable without a')
print('core, or blocked on a monitor outside a wait; and its contended monitor entries outside')
print('waits. The machine\'s busy cores (every process, of the cpus column) and the other')
print('processes\' (the machine\'s less this process\'s).\n')
print('| run | threads | batches | mean batch ms | longest batch so far ms | batch wall over eviction CPU | eviction running % | waiting % | the rest % | contended entries outside waits | machine cores | other processes\' cores |')
print('|---|---|---|---|---|---|---|---|---|---|---|---|')
for b, r, n, d in runs_by_order():
    for t, p in tphases(d):
        e = ev_pcts(p)
        print('| %s r%d | %d | %d | %s | %s | %s | %s | %s | %s | %s | %s | %s |' % (
            b, r, t, p['sweeps'], fmt(ratio(p['sweepMs'], p['sweeps']), '%.2f'),
            fmt(p.get('sweepMaxMsSoFar'), '%d'), fmt(ratio(p['sweepMs'], p.get('evictionCpuMs')), '%.2f'),
            fmt(e and e[0], '%.1f'), fmt(e and e[1], '%.1f'), fmt(e and e[2], '%.1f'), fmt(e and e[3], '%d'),
            fmt(p.get('machineCores'), '%.2f'), fmt(others(p), '%.2f')))

print('\n## Each build, the reading\'s figures (sums or means of its runs)\n')
print('| build | threads | gets > 10 ms | after-load > 10 ms | of them under pressure | after-load ns a call | entering evictorLock, k a second | readers blocked % | eviction thread, the rest % | machine cores | other processes\' cores |')
print('|---|---|---|---|---|---|---|---|---|---|---|')


def mean(xs):
    xs = [x for x in xs if x is not None]
    return sum(xs) / len(xs) if xs else None


def total(xs):
    xs = [x for x in xs if x is not None]
    return sum(xs) if xs else None


for bd in order:
    for t in tcounts:
        ps = [p for b, r, n, d in runs_by_order() if b == bd for tt, p in tphases(d) if tt == t]
        if not ps:
            continue
        print('| %s | %d | %s | %d | %s | %s | %s | %s | %s | %s | %s |' % (
            bd, t, fmt(total([p.get('getsOver10ms') for p in ps]), '%d'), sum(p['afterLoadOver10ms'] for p in ps),
            fmt(total([p.get('afterLoadOver10msUnderPressure') for p in ps]), '%d'),
            fmt(mean([ratio(p.get('afterLoadMs'), p.get('afterLoadCalls'), 1e6) for p in ps]), '%.0f'),
            fmt(mean([ratio(p.get('afterLoadEnterCalls'), p['seconds'], 1e-3) for p in ps]), '%.0f'),
            fmt(mean([blocked_pct(p, t) for p in ps]), '%.2f'),
            fmt(mean([(ev_pcts(p) or [None] * 4)[2] for p in ps]), '%.1f'),
            fmt(mean([p.get('machineCores') for p in ps]), '%.2f'), fmt(mean([others(p) for p in ps]), '%.2f')))

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
