# 024-14: tables from THR outputs. summ2.py DIR
import sys, os, glob
sys.path.insert(0, os.path.dirname(__file__))
from summ import parse
SETS = ['main', 'p5', 'm8', 'm9', 'dense']
D = sys.argv[1]
runs = {}
for f in glob.glob(os.path.join(D, '*.txt')):
    b = os.path.basename(f)[:-4]
    shape, s = b.rsplit('-', 1)
    runs[(shape, s)] = parse(f)
def g(d, k, f, conv=float):
    try: return conv(d[k][f])
    except Exception: return None
def fmt(x, p=2):
    if x is None: return '-'
    if isinstance(x, int) or (isinstance(x, float) and p == 0): return '{:,}'.format(int(round(x)))
    return ('%.' + str(p) + 'f') % x
shapes = sorted(set(k[0] for k in runs))
for sh in shapes:
    print('==', sh)
    for s in SETS:
        d = runs.get((sh, s))
        if not d: continue
        ph = 'OVER' if 'OVER' in d else ('CHURN' if 'CHURN' in d else 'DELETE')
        nf = g(d, 'NODES:fill', 'keyNodes'); ns = g(d, 'NODES:shape', 'keyNodes') or g(d, 'NODES:over', 'keyNodes')
        nd = g(d, 'NODES:drive', 'keyNodes'); tf = g(d, 'TWIN NODES:fill', 'keyNodes'); td = g(d, 'TWIN NODES:drive', 'keyNodes')
        r1 = ns / tf if ns and tf else None; r2 = nd / td if nd and td else None
        kd = g(d, 'STATE:drive', 'kept'); tk = g(d, 'TWIN STATE:drive', 'kept')
        print(' %-5s fill: %s nodes %s/s rec/op %s ssplit/op %s tsplit/op %s | %s: %s/s rec/op %s stream/op %s merge/op %s m2/op %s ssplit/op %s tsplit/op %s taken/op %s | nodes %s twin %s x%s | drive nodes %s twin %s x%s | drive rec/tx %s twin %s | kept %s twin %s | scan %s twin %s | kpn %s'
              % (s, fmt(nf,0), fmt(g(d,'FILL','ops/s'),0), fmt(g(d,'FILL','rec/op'),1), fmt(g(d,'FILL','ssplit/op'),4), fmt(g(d,'FILL','tsplit/op'),4),
                 ph, fmt(g(d,ph,'ops/s'),0), fmt(g(d,ph,'rec/op'),1), fmt(g(d,ph,'stream/op'),1), fmt(g(d,ph,'merge/op'),4), fmt(g(d,ph,'merge2/op'),4),
                 fmt(g(d,ph,'ssplit/op'),4), fmt(g(d,ph,'tsplit/op'),4), fmt(g(d,ph,'taken/op'),4),
                 fmt(ns,0), fmt(tf,0), fmt(r1), fmt(nd,0), fmt(td,0), fmt(r2),
                 fmt(g(d,'DRIVE','rec/tx'),0), fmt(g(d,'TWIN DRIVE','rec/tx'),0),
                 fmt(kd/1e6 if kd else None,0), fmt(tk/1e6 if tk else None,0),
                 fmt(g(d,'SCAN:shape-again','ms') or g(d,'SCAN:over-again','ms'),0), fmt(g(d,'TWIN SCAN:fill-again','ms'),0),
                 fmt(g(d,'NODES:shape','keys/node') or g(d,'NODES:over','keys/node'))))
