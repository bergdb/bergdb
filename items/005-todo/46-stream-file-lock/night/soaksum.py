#!/usr/bin/env python3
# soaksum.py RUNDIR PREFIX: a soak's result.json (after "Soak finish") as PREFIX-summary.json,
# the keys that 009-04 kept and 005-46's (the disk's waits, the physical cuts, the slowest
# commits), and a report on stdout for 005-46's criterion (009-04, section 7.3): are the
# physical cuts still the soak's slowest commits and reads? Written 2026-10-27 for bergdb
# 005-46's night runs (night/run.sh).
import json, os, sys

run, prefix = sys.argv[1], sys.argv[2]
path = os.path.join(run, 'result.json')
if not os.path.exists(path):
    print('no result.json in ' + run)
    sys.exit(1)
r = json.load(open(path))

keep = ['ok', 'failure', 'params', 'phases', 'windows_uptime_s', 'metrics', 'latency', 'eviction',
        'restarts', 'physical_cuts', 'cut_decisions', 'slowest_commits_with_pauses',
        'slowest_durable_commits_with_pauses', 'disk_waits']
s = {k: r[k] for k in keep if k in r}
jvm = r.get('info', {}).get('jvm', {})
s['collector'] = jvm.get('collector')
s['vmFlags'] = jvm.get('vmFlags')
gc = r.get('gcLog', {})
s['gcLog_measured'] = gc.get('measured')
s['gcLog_heap_after_gc_measured'] = gc.get('heap_after_gc_measured')
json.dump(s, open(prefix + '-summary.json', 'w'), indent=1)


def rows(key):
    v = r.get(key)
    return v[1] if isinstance(v, list) and len(v) == 2 and isinstance(v[1], list) else []


m = r.get('metrics', {})
lat = r.get('latency', {})
w = r.get('windows_uptime_s', {}).get('measured')
print('soak %s: ok %s%s' % (os.path.basename(run.rstrip('/')), r.get('ok'),
                             ('; failure: %s' % r['failure']) if r.get('failure') else ''))
print('  measured phase: uptime %s s; %s s steady, %.1f commits and %.0f reads a second; physical'
      ' cuts %s (all %s); restarts %s' % (
          '%.1f to %.1f' % tuple(w) if w else '?', m.get('measured.steady_s'),
          m.get('commits_per_s', 0), m.get('reads_per_s', 0), m.get('physical_cuts'),
          m.get('physical_cuts_total'), m.get('restarts')))
cuts = [c[0] for c in rows('physical_cuts')]
print('  physical cuts (uptime s, first position MB): ' + ', '.join(
    '%.1f (%.0f)' % (c[0], c[1]) for c in rows('physical_cuts')))
slow = r.get('slowest_commits_with_pauses') or rows('slowest_commits')


def near_cut(up):
    return [c for c in cuts if abs(up - c) <= 2.0]


print('  the slowest commits (ms at uptime s; "cut": a physical cut seen within 2 s; GC overlap):')
for e in slow[:10]:
    print('    %8.1f ms at %8.2f s%s%s' % (e[0], e[1], '  cut' if near_cut(e[1]) else '',
                                         ('  ' + e[5]) if len(e) > 5 else ''))
if slow:
    floor = slow[-1][0]
    for c in cuts:
        at = [e for e in slow if abs(e[1] - c) <= 2.0]
        if w and c < w[0] + 1.0:
            print('  the cut at %.1f s: the warm-up\'s, which ended with it; its commits are not'
                  ' measured' % c)
        elif at:
            e = max(at, key=lambda x: x[0])
            rank = sorted([x[0] for x in slow], reverse=True).index(e[0]) + 1
            print('  the cut at %.1f s: its slowest commit %.1f ms at %.2f s, number %d of the slowest'
                  % (c, e[0], e[1], rank))
        else:
            print('  the cut at %.1f s: no commit among the %d slowest (the slowest kept are all over'
                  ' %.1f ms)' % (c, len(slow), floor))


def mx(key):
    v = lat.get(key)
    return '%.1f ms' % (v['max'] / 1e6) if v and v.get('max') is not None else '?'


def p999(key):
    v = lat.get(key)
    return '%.2f ms' % (v['p999'] / 1e6) if v and v.get('p999') is not None else '?'


print('  longest: commit %s (p99.9 %s), durable commit %s, pacing delay %s; latest get %s,'
      ' historical get %s, forward scan %s, backward scan %s' % (
          mx('commit_append_ns'), p999('commit_append_ns'), mx('commit_durable_ns'),
          mx('pacing_delay_ns'), mx('get_latest_ns'), mx('get_historical_ns'),
          mx('scan_forward_ns'), mx('scan_backward_ns')))
print('  the disk\'s waits (the write buffer\'s for each database object, then the forces and'
      ' deletes of the whole run):')
for d in r.get('disk_waits', []):
    for line in str(d).split('\n'):
        print('    ' + line)
g = gc.get('measured') or {}
p, sp = g.get('pauses') or {}, g.get('safepoints') or {}
print('  GC in the measured phase: %s pauses, at most %s ms; safepoints at most %s ms' % (
    p.get('count'), p.get('maxMs'), sp.get('maxMs')))
print('  ' + str(r.get('eviction')))
for x in r.get('restarts', []):
    print('  restart %s at %.1f s: startup %.2f s, %s transactions rerun, readers paused %.1f s' % (
        x.get('index'), x.get('uptime_s', 0), x.get('startup_s', 0), x.get('transactions_rerun'),
        x.get('pause_s', 0)))
