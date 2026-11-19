# bergdb 026-25, perf2: the JFR samples of the set test (frames under bergdb.test.Set.run) of
# a recording of bergdb.dev.props.Core: the share of the samples in each method (self) and
# under each method (total), for the methods of bergdb. Written 2026-11-19.
# Usage: jfr print --json --stack-depth 64 --events jdk.ExecutionSample X.jfr > X.json;
#        python3 jfrsets.py X.json [N]
import json, sys, collections
ev = json.load(open(sys.argv[1]))['recording']['events']
N = int(sys.argv[2]) if len(sys.argv) > 2 else 30
selfc, totc, n = collections.Counter(), collections.Counter(), 0
for e in ev:
    fr = e['values']['stackTrace']['frames'] if e['values'].get('stackTrace') else []
    names = [f['method']['type']['name'].replace('/', '.') + '.' + f['method']['name'] for f in fr]
    if not any(x.endswith('test.Set.run') for x in names):
        continue
    n += 1
    selfc[names[0]] += 1
    for x in set(names):
        totc[x] += 1
print('samples under Set.run:', n)
print('-- self')
for k, v in selfc.most_common(N): print('%5.1f %%  %s' % (100.0 * v / n, k))
print('-- total (bergdb only)')
for k, v in totc.most_common(200):
    if k.startswith('bergdb.') and not k.startswith('bergdb.test') and not k.startswith('bergdb.dev'):
        print('%5.1f %%  %s' % (100.0 * v / n, k))
