#!/usr/bin/env python3
"""Tables of ScaleBench results for 004-02 (bergdb item 004), from the JSON files that
ScaleBench writes. Usage: python3 summarize.py DIR...   (the out/d directories)
Prints Markdown: the loads, the runs without eviction (M), the runs with a budget (C, D),
the threads, the sampled states and the slowest gets."""
import glob
import json
import os
import sys


def load(dirs):
    runs = []
    for d in dirs:
        for f in sorted(glob.glob(os.path.join(d, '*.json'))):
            with open(f) as fh:
                r = json.load(fh)
            r['_name'] = os.path.basename(f)[:-5]
            runs.append(r)
    return runs


def phase(r, name):
    for p in r.get('phases', []):
        if p.get('phase') == name:
            return p
    return None


def fmt(x, nd=1):
    if x is None:
        return ''
    if isinstance(x, float):
        if abs(x) >= 1000:
            return f'{x:,.0f}'
        return f'{x:.{nd}f}'
    if isinstance(x, int):
        return f'{x:,}'
    return str(x)


def keys_label(r):
    n = r.get('loaded', r.get('keys'))
    return f'{n / 1e6:g}M'


def regime(r):
    name = r['_name']
    if '-m-' in name:
        return 'M'
    if '-c-' in name:
        return 'C'
    if '-d-' in name:
        return 'D'
    return 'load'


def table(head, rows):
    print('| ' + ' | '.join(head) + ' |')
    print('|' + '---|' * len(head))
    for row in rows:
        print('| ' + ' | '.join(row) + ' |')
    print()


def main():
    runs = load(sys.argv[1:])
    print('### Loads\n')
    rows = []
    for r in runs:
        l = r.get('load')
        if not l:
            continue
        c = phase(r, 'census')
        rows.append([r['_name'], keys_label(r), fmt(r.get('budget', 0) / 1e6, 0), fmt(l.get('seconds')),
                     fmt(l.get('putsPerSec')), fmt(l.get('diskBytesPerKey')), fmt(l.get('heapBytesPerKey')),
                     fmt(c.get('latestIndexBytesPerKey')) if c else '', fmt(c.get('keysPerIndexNode'), 2) if c else ''])
    table(['run', 'keys', 'budget MB', 's', 'puts/s', 'disk B/key', 'heap B/key', 'latest index B/key',
           'keys/node'], rows)

    print('### Gets, one thread\n')
    rows = []
    for r in runs:
        for ph in ('uniform', 'hot'):
            p = phase(r, ph)
            if not p:
                continue
            u, t = p['untimed'], p['timed']
            lat = t['latency']
            gc = t.get('gcPauses', {})
            rows.append([r['_name'], ph, regime(r), keys_label(r), fmt(r.get('budget', 0) / 1e6, 0),
                         fmt(u.get('medianGetsPerSec')), fmt(lat['meanUs'], 2), fmt(lat['p50Us'], 2),
                         fmt(lat['p90Us'], 2), fmt(lat['p99Us'], 2), fmt(lat['p999Us'], 1), fmt(lat['maxUs'], 0),
                         fmt(t.get('loadsPerGet'), 2), fmt(t.get('streamReadsPerGet'), 2),
                         fmt(t.get('deviceReadBytesPerGet'), 0), fmt(t.get('diskReadsPerGet'), 2),
                         f"{t.get('sweeps')} / {t.get('sweepMs')}", fmt(t.get('afterLoadOver10ms')),
                         f"{gc.get('count', '')} / {fmt(gc.get('maxMs'), 0)}", fmt(t.get('stealPercent'), 2)])
    table(['run', 'phase', 'regime', 'keys', 'budget MB', 'gets/s (untimed)', 'mean us', 'p50', 'p90', 'p99',
           'p99.9', 'max us', 'loads/get', 'stream reads/get', 'device B/get', 'disk reads/get',
           'sweeps / ms', 'after-load > 10 ms', 'gc pauses / max ms', 'steal %'], rows)

    print('### Threads\n')
    rows = []
    for r in runs:
        ts = [p for p in r.get('phases', []) if p.get('phase', '').startswith('threads-')]
        if not ts:
            continue
        row = [r['_name'], regime(r), keys_label(r)]
        for p in ts:
            row.append(f"{p['threads']}: {fmt(p.get('getsPerSec'))} ({fmt(p['latency']['p99Us'], 1)})")
        rows.append(row)
    table(['run', 'regime', 'keys', 'threads: gets/s (p99 us)', '', '', ''], rows)

    print('### Read-path variants (no eviction)\n')
    rows = []
    for r in runs:
        p = phase(r, 'variants')
        if not p:
            continue
        one = p['oneThreadNsPerGet']
        many = p.get('threadsGetsPerSec', {})
        rows.append([r['_name'], keys_label(r), fmt(one.get('as it is')), fmt(one.get('no lock, no stamp')),
                     fmt(one.get('stamp, no lock')), fmt(one.get('as it is, no readSync')), str(p.get('threads', '')),
                     fmt(many.get('as it is', 0) / 1e6, 2), fmt(many.get('no lock, no stamp', 0) / 1e6, 2),
                     fmt(many.get('no lock, no stamp, no readSync', 0) / 1e6, 2)])
    table(['run', 'keys', '1 thread ns: as it is', 'no lock, no stamp', 'stamp, no lock', 'no readSync',
           'threads', 'M/s as it is', 'no lock, no stamp', 'and no readSync'], rows)

    print('### Sampled reader states (percent of samples)\n')
    for r in runs:
        ps = [p for p in r.get('phases', []) if p.get('phase', '').startswith('sampled-')]
        for p in ps:
            st = p.get('statesPercent', {})
            top = '; '.join(f'{v:.0f}% {k}' for k, v in list(st.items())[:5])
            print(f"* {r['_name']} ({p['threads']} threads, {fmt(p.get('getsPerSec'))} gets/s): {top}")
    print()

    print('### Slowest gets (timed one-thread passes)\n')
    for r in runs:
        for ph in ('uniform', 'hot'):
            p = phase(r, ph)
            if not p or 'slowestGets' not in p:
                continue
            sg = p['slowestGets']
            al = sum(1 for g in sg if any('after-load' in o for o in g['overlapping']))
            gc = sum(1 for g in sg if any(o.startswith('Pause') for o in g['overlapping']))
            print(f"* {r['_name']} {ph}: slowest {fmt(sg[0]['us'] / 1000, 1) if sg else ''} ms; of {len(sg)}: "
                  f"{al} overlap a wait after a load, {gc} a collection pause")
    print()


if __name__ == '__main__':
    main()
