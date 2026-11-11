# 024-14: candidate threshold sets in 024-11's model (sim.py), to pick the sets between P5's and the dense one
import sys
sys.path.insert(0, '/Users/f/fl/repos/bergdb/items/024-release-2026-5/11-underfill/sim')
from sim import sparse, churn, thrash
n = int(sys.argv[1]) if len(sys.argv) > 1 else 30000
sets = [(7,15,15),(8,16,16),(8,16,17),(8,17,17),(9,18,18),(9,18,19),(10,20,20),(10,20,21)]
for m,h,c in sets:
    kw = dict(m=m,h=h,c=c)
    out = []
    for order in ('asc','desc','random'):
        xs = []
        for keep in (2,3,10,100):
            r = sparse(n, keep, order, **kw); xs.append('%.2f' % r['x'])
        out.append(order + ' ' + '/'.join(xs))
    ch = churn(n, 2*n, **kw); th = thrash(**kw)
    print('m%d h%d c%d | %s | churn %.3f spl/ow %d nodes | thrash %.3f new %.3f mg %.3f sp' %
          (m,h,c,' | '.join(out), ch[0], ch[1], th[0], th[1], th[2]), flush=True)
