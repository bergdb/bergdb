# bergdb 028-19: allocation samples (jdk.ObjectAllocationSample, weight in bytes) of a JFR
# recording, under bergdb.test.Set.run (or all, with ALL), by allocating bergdb method and class.
# Usage: jfr print --json --stack-depth 64 --events jdk.ObjectAllocationSample X.jfr > X.json;
#        python3 jfralloc.py X.json [N [FRAME]]   (FRAME: the samples under this method, default
#        test.Set.run; ALL: every sample)
import json, sys, collections
ev = json.load(open(sys.argv[1]))['recording']['events']
N = int(sys.argv[2]) if len(sys.argv) > 2 else 25
by, byc, tot = collections.Counter(), collections.Counter(), 0
for e in ev:
    v = e['values']
    fr = v['stackTrace']['frames'] if v.get('stackTrace') else []
    names = [f['method']['type']['name'].replace('/', '.') + '.' + f['method']['name'] for f in fr]
    flt = sys.argv[3] if len(sys.argv) > 3 else 'test.Set.run'
    if flt != 'ALL' and not any(x.endswith(flt) for x in names):
        continue
    w = v['weight']
    tot += w
    first = next((x for x in names if x.startswith('bergdb.')), '?')
    by[first] += w
    byc[(first, v['objectClass']['name'])] += w
print('MB sampled:', tot / 1e6)
for k, w in by.most_common(N): print('%5.1f %%  %s' % (100.0 * w / tot, k))
print('-- by method and class')
for k, w in byc.most_common(N): print('%5.1f %%  %s  %s' % (100.0 * w / tot, k[0], k[1]))
