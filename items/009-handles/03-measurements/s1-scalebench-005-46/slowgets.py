import json, os, re, sys
# slowgets.py NAME.json...: for each ScaleBench run, the startup, the five slowest gets of each
# timed pass with what overlapped them (the collector's pauses, the readers' after-load waits),
# the longest get of each thread phase, and the sampled threads' share BLOCKED on a stream
# monitor (bergdb 009-03, section 9). Written 2026-10-27 by Claude (Opus 5.5, Claude Code).
for f in sys.argv[1:]:
    d = json.load(open(f))
    t = open(f[:-5] + '.txt').read()
    print('%s: startup %.1f s' % (os.path.basename(f)[:-5], d.get('startupSec', 0)))
    for p in d['phases']:
        sg = p.get('slowestGets')
        if sg:
            print('  %s, timed, slowest: %s' % (p['phase'], '; '.join(
                '%.1f ms at %.1f s%s' % (e['us'] / 1000, e['uptime'],
                                         (' (' + ', '.join(e['overlapping']) + ')') if e['overlapping'] else '')
                for e in sg[:5])))
    th = re.findall(r'threads (\d+): (\d+) gets a second; .*?max ([\d.]+) us', t)
    print('  threads: ' + ', '.join('%s: %s gets/s, max %.1f ms' % (n, g, float(m) / 1000) for n, g, m in th))
    b = re.findall(r'([\d.]+)% BLOCKED (.*)', t)
    print('  sampled: ' + ('; '.join('%s%% BLOCKED %s' % x for x in b) if b else 'none BLOCKED'))
