"""Bergdb item 002 (M46): hops of a top node search for a query within the last W top
nodes, from heads of large ordinals. Times equal ordinals; a query at the time of top a
(the search returns a). Java's TopDs.findSuperRootAtTime, as in height_decrease.py."""
import random

def hops(head, a):
    # Follow the highest slot whose target is >= a (cached time >= t); count jumps.
    n, h = head, 0
    if a >= n:
        return 0
    while True:
        best = None
        for k in range(n.bit_length() - 1, -1, -1):
            if n >> k & 1:
                t = ((n >> k) << k) - 1
                if t >= a:
                    best = t
                    break
        if best is None:
            break
        n, h = best, h + 1
    return h if n == a else h + 1

rnd = random.Random(3)
for bits in [20, 30, 40, 47]:
    for wbits in [8, 12, 16]:
        worst = 0
        for _ in range(300):
            head = (1 << bits) + rnd.randrange(1 << bits)
            for _ in range(200):
                a = head - rnd.randrange(1 << wbits)
                worst = max(worst, hops(head, a))
        print("heads of %d bits, queries within the last 2^%d tops: at most %d hops (sampled)" % (bits + 1, wbits, worst))
