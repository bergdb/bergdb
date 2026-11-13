# 026-04: for each emptied run, the iteration running when the deletes end (X), its KVs at
# tStart, its end in drive transactions, and the lag; the prediction K/300 + 1,280.
import re, sys
for fn in sys.argv[1:]:
    lines = open(fn).read().split('\n')
    its = []; n = None
    for l in lines:
        m = re.search(r'n=(\d+)', l)
        if n is None and m: n = int(m.group(1))
        if 'ITER' in l:
            its.append({k: int(v) for k, v in re.findall(r'(\w+)=(-?\d+)', l)})
        if 'filled and deleted' in l or 'drive' in l and 'twin' in l:
            its = []
        if 'RESULT d' in l:
            f = l.split()[2]; lag = int(re.search(r'lag=(\d+)', l).group(1))
            fc = int(re.search(r'firstCut=(\d+)', l).group(1))
            x = [i for i in its if i['tStart'] < 0 and i['tEnd'] >= 0]
            x = x[0] if x else None
            if x:
                print(f"n={n} f={f} X: tStart={x['tStart']} kvs={x['kvs']} steps={x['steps']} "
                      f"values={x['values']} tEnd={x['tEnd']} kvs/300={x['kvs']//300} "
                      f"firstCut={fc} lag={lag} lag-tEnd={lag - x['tEnd']}")
            else:
                print(f"n={n} f={f} no X; firstCut={fc} lag={lag}")
            its = []
