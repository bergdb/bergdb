#!/usr/bin/env python3
"""024-11: a model of one segment tree of live klongs with the klongs used in each node (layer A
of 024-11, section 5, with layer B's sizes), to check V1, V2, V4, CB3 and CB4 and to compare
thresholds and sibling rules. Not BergDB's code: a study tool, 2026-11-11. Keys are ints.

A node: live entries (leaf: keys; inner: bounds and kids, the first bound None = the empty key),
'used' klongs of its array, the transaction of its last TIME klong and of its last bitmap, and the
transaction that made it. Rule O (handleFullNode), remove, fix and merge as in 024-11, 5.2, 5.3.
"""
import bisect, random, sys

class Node:
    __slots__ = ('leaf', 'keys', 'kids', 'ktx', 'used', 'ttime', 'dtime', 'made')
    def __init__(self, leaf, tx):
        self.leaf = leaf; self.keys = []; self.kids = []; self.ktx = []
        self.used = 1; self.ttime = tx; self.dtime = -1; self.made = tx
    def cnt(self): return len(self.keys)

class Tree:
    def __init__(self, B=30, m=None, h=None, c=None, sibling='p5', merges=True):
        self.B = B; self.h = h if h else B // 2; self.m = m if m else max(2, B // 4)
        self.c = c if c else B // 2
        self.sibling = sibling; self.merges = merges
        self.tx = 0; self.root = Node(True, 0)
        self.n_merge = self.n_two = self.n_space = self.n_time = self.n_new = self.n_del = 0
        self.n_sib = 0

    # ---- klongs
    def fits(self, node, k, d=False):
        need = k + (1 if d and node.dtime != self.tx else 0) + (1 if node.ttime != self.tx else 0)
        if node.used + need > self.B: return False
        node.used += need; node.ttime = self.tx
        if d: node.dtime = self.tx
        return True

    def new(self, leaf):
        self.n_new += 1; return Node(leaf, self.tx)

    # ---- descent
    def path(self, key):
        p = []; n = self.root
        while not n.leaf:
            i = bisect.bisect_right(n.keys, key, lo=1) - 1
            p.append((n, i)); n = n.kids[i]
        p.append((n, -1)); return p

    # ---- rule O: 'node' (path[d]) has its change applied to keys/kids already; 'lbefore' is the
    # live count that decides (Java decides a put's split before the insert).
    def overflow(self, path, d, lbefore=None):
        node = path[d][0]; L = node.cnt(); dec = L if lbefore is None else lbefore
        tx = self.tx
        if 1 + dec <= self.h:                      # time split
            self.n_time += 1
            if node.made == tx:
                node.used = 1 + L; node.dtime = -1
                return
            nn = self.new(node.leaf); nn.keys = node.keys; nn.kids = node.kids
            nn.ktx = node.ktx; nn.used = 1 + L
            self.replace(path, d, [nn], None)
            return
        self.n_space += 1                          # space split
        k = dec // 2
        if lbefore is not None and L > dec:
            # the inserted key goes to the half it belongs to: cut by the old entries
            ins = self._ins; pos = bisect.bisect_left(node.keys, ins)
            if pos < k: k += 1
        a_keys, b_keys = node.keys[:k], node.keys[k:]
        a_kids, b_kids = node.kids[:k], node.kids[k:]
        a_ktx, b_ktx = node.ktx[:k], node.ktx[k:]
        sep = b_keys[0]
        if not node.leaf: b_keys = [None] + b_keys[1:]
        if node.made == tx:
            node.keys, node.kids, node.ktx = a_keys, a_kids, a_ktx
            node.used = 1 + len(a_keys); node.dtime = -1
            b = self.new(node.leaf); b.keys, b.kids, b.ktx = b_keys, b_kids, b_ktx
            b.used = 1 + len(b_keys)
            self.replace(path, d, [node, b], sep, inplace=True)
        else:
            a = self.new(node.leaf); a.keys, a.kids, a.ktx = a_keys, a_kids, a_ktx
            a.used = 1 + len(a_keys)
            b = self.new(node.leaf); b.keys, b.kids, b.ktx = b_keys, b_kids, b_ktx
            b.used = 1 + len(b_keys)
            self.replace(path, d, [a, b], sep)

    # the parent's change after rule O on path[d]: one node (a repoint) or two (and a new bound)
    def replace(self, path, d, nodes, sep, inplace=False):
        tx = self.tx
        if d == 0:
            if len(nodes) == 1: self.root = nodes[0]; return
            r = self.new(False); r.keys = [None, sep]; r.kids = nodes; r.ktx = [tx, tx]
            r.used = 3; self.root = r; return
        p, i = path[d - 1]
        k = 0
        if not inplace:
            if p.ktx[i] != tx: k += 1
            p.kids[i] = nodes[0]; p.ktx[i] = tx
        if len(nodes) == 2:
            p.keys.insert(i + 1, sep); p.kids.insert(i + 1, nodes[1]); p.ktx.insert(i + 1, tx)
            k += 1
        if not self.fits(p, k):
            self.overflow(path, d - 1)

    # ---- operations
    def begin(self): self.tx += 1

    def put(self, key):
        path = self.path(key); leaf = path[-1][0]; d = len(path) - 1
        i = bisect.bisect_left(leaf.keys, key)
        if i < len(leaf.keys) and leaf.keys[i] == key:      # an overwrite: a shadowing klong
            if not self.fits(leaf, 1): 
                self.overflow(path, d)
                leaf = self.path(key)[-1][0]; leaf.used += 1
            return
        L = leaf.cnt(); leaf.keys.insert(i, key)
        if not self.fits(leaf, 1):
            self._ins = key
            self.overflow(path, d, lbefore=L)
            leaf = self.path(key)[-1][0]; leaf.used += 1

    def delete(self, key):
        path = self.path(key); leaf = path[-1][0]; d = len(path) - 1
        i = bisect.bisect_left(leaf.keys, key)
        if i >= len(leaf.keys) or leaf.keys[i] != key: return
        self.n_del += 1
        del leaf.keys[i]
        if not self.fits(leaf, 0, d=True):
            self.overflow(path, d)
        if self.merges: self.fix(key)

    def fix(self, key):
        while True:
            path = self.path(key); d = len(path) - 1
            # the lowest node on the path below m, bottom-up: only one can be, by V1
            while d > 0 and path[d][0].cnt() >= self.m: d -= 1
            if d == 0:
                r = self.root
                while not r.leaf and r.cnt() == 1: r = r.kids[0]
                self.root = r; return
            if not self.merge(path, d): return

    def merge(self, path, d):
        """Merges path[d]; True if into one node (the parent lost a klong)."""
        x = path[d][0]; p, i = path[d - 1]; tx = self.tx; c = self.c
        left = p.kids[i - 1] if i > 0 else None
        right = p.kids[i + 1] if i + 1 < p.cnt() else None
        rule = self.sibling
        if rule == 'p5':
            if left is not None: self.n_sib += 1
            use_left = left is not None and (right is None or left.cnt() + x.cnt() <= c)
            if not use_left: self.n_sib += 1
        elif rule == 'prev':
            use_left = left is not None; self.n_sib += 1
        elif rule == 'next':
            use_left = right is None; self.n_sib += 1
        elif rule == 'fewer':
            self.n_sib += (left is not None) + (right is not None)
            use_left = left is not None and (right is None or left.cnt() <= right.cnt())
        elif rule == 'fits':     # one that fits in one node, the previous first; else the fuller
            self.n_sib += (left is not None) + (right is not None)
            lf = left is not None and left.cnt() + x.cnt() <= c
            rf = right is not None and right.cnt() + x.cnt() <= c
            if lf: use_left = True
            elif rf: use_left = False
            else: use_left = left is not None and (right is None or left.cnt() >= right.cnt())
        il = i - 1 if use_left else i
        l, r = p.kids[il], p.kids[il + 1]
        er = p.keys[il + 1]
        keys = l.keys + ([er] + r.keys[1:] if not x.leaf else r.keys)
        kids = l.kids + r.kids; ktx = l.ktx + r.ktx
        n = len(keys); self.n_merge += 1
        k = 0 if p.ktx[il] == tx else 1
        if n <= c:
            n1 = self.new(x.leaf); n1.keys, n1.kids, n1.ktx = keys, kids, ktx; n1.used = 1 + n
            p.kids[il] = n1; p.ktx[il] = tx
            del p.keys[il + 1]; del p.kids[il + 1]; del p.ktx[il + 1]
            if not self.fits(p, k, d=True): self.overflow(path, d - 1)
            return True
        self.n_two += 1
        h = (n + 1) // 2
        n1 = self.new(x.leaf); n1.keys, n1.kids, n1.ktx = keys[:h], kids[:h], ktx[:h]
        n2 = self.new(x.leaf); n2.keys, n2.kids, n2.ktx = keys[h:], kids[h:], ktx[h:]
        g = n2.keys[0]
        if not x.leaf: n2.keys = [None] + n2.keys[1:]
        n1.used = 1 + len(n1.keys); n2.used = 1 + len(n2.keys)
        p.kids[il] = n1; p.ktx[il] = tx
        dele = g != er
        k += 0 if (not dele and p.ktx[il + 1] == tx) else 1
        p.keys[il + 1] = g; p.kids[il + 1] = n2; p.ktx[il + 1] = tx
        if not self.fits(p, k, d=dele): self.overflow(path, d - 1)
        return False

    # ---- checks and counts
    def walk(self):
        """(key nodes, live keys, klongs used); checks V1, V2, V4 with merges on."""
        nodes = keys = used = 0; depth = None
        st = [(self.root, 0)]
        while st:
            n, dp = st.pop(); nodes += 1; used += n.used
            assert n.used <= self.B, 'V5'
            if self.merges and n is not self.root: assert n.cnt() >= self.m, ('V1', n.cnt())
            if n.leaf:
                keys += n.cnt()
                if depth is None: depth = dp
                assert depth == dp, 'V4'
            else:
                if self.merges and n is self.root: assert n.cnt() >= 2, 'V2'
                assert n.keys[0] is None, 'V3'
                st.extend((k, dp + 1) for k in n.kids)
        return nodes, keys, used

def fill(t, keys, batch=100):
    for i in range(0, len(keys), batch):
        t.begin()
        for k in keys[i:i + batch]: t.put(k)

def sparse(n, keep, order, seed=1, batch=100, **kw):
    t = Tree(**kw); fill(t, list(range(n)), batch)
    filled = t.walk()[0]
    o = list(range(n))
    if order == 'desc': o.reverse()
    elif order == 'random': random.Random(seed).shuffle(o)
    new0 = t.n_new
    for i in range(0, n, batch):
        ks = [j for j in o[i:i + batch] if j % keep != 0]
        if ks:
            t.begin()
            for k in ks: t.delete(k)
    tw = Tree(**kw); fill(tw, [j for j in range(n) if j % keep == 0], batch)
    nodes, live, used = t.walk(); tn, tl, tu = tw.walk()
    assert live == tl
    if t.merges:
        assert t.n_merge <= t.n_del + 2 * t.n_space, 'CB3'
        m = t.m; assert nodes <= 1 + live / (m - 1), 'BU1'
    return dict(filled=filled, twin=tn, nodes=nodes, x=nodes / tn, merges=t.n_merge, two=t.n_two,
                dels=t.n_del, sib=t.n_sib, new=t.n_new - new0, klongs=used, tklongs=tu)

def fuzz(B, seed, txs=3000, space=400, **kw):
    """Random puts, overwrites and deletes; V1, V2, V4, V5 after every transaction; CB3 at the end."""
    rnd = random.Random(seed); t = Tree(B=B, **kw); live = set()
    for _ in range(txs):
        t.begin(); pdel = rnd.choice((0.2, 0.5, 0.8))
        for k in rnd.sample(range(space), rnd.randint(1, 30)):     # one operation a key
            if k in live and rnd.random() < pdel: t.delete(k); live.discard(k)
            else: t.put(k); live.add(k)
        nodes, keys, used = t.walk()
        assert keys == len(live)
        assert nodes <= 1 + keys / (t.m - 1), 'BU1'
    assert t.n_merge <= t.n_del + 2 * t.n_space, 'CB3'
    return t.n_merge, t.n_del, t.n_space

def churn(n, ops, seed=1, **kw):
    """After a fill in key order: single-key overwrites at random; splits an overwrite, the shape."""
    t = Tree(**kw); fill(t, list(range(n))); rnd = random.Random(seed)
    s0 = t.n_time + t.n_space
    for _ in range(ops):
        t.begin(); t.put(rnd.randrange(n))
    nodes, keys, used = t.walk()
    return (t.n_time + t.n_space - s0) / ops, nodes, used / nodes

def thrash(ops=20000, seed=1, **kw):
    """Puts and deletes, one a transaction, in a window of keys held near c live keys a node."""
    t = Tree(**kw); n = 3000; fill(t, list(range(0, n, 2))); rnd = random.Random(seed)
    lo, w = 1000, 4 * t.c; live = set(k for k in range(lo, lo + w) if k % 2 == 0)
    new0 = t.n_new; m0 = t.n_merge; s0 = t.n_space
    for i in range(ops):
        t.begin()
        if (len(live) > w // 2 and rnd.random() < 0.9) or len(live) == w:
            k = rnd.choice(sorted(live)); t.delete(k); live.discard(k)
        else:
            k = rnd.choice([x for x in range(lo, lo + w) if x not in live]); t.put(k); live.add(k)
    t.walk()
    return (t.n_new - new0) / ops, (t.n_merge - m0) / ops, (t.n_space - s0) / ops

if __name__ == '__main__':
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 100000
    sets = [('P5', dict()), ('c 22', dict(c=22)), ('dense', dict(m=10, h=20, c=20))]
    for B, kw in ((8, {}), (14, {}), (30, {}), (62, {}), (30, dict(c=22)), (30, dict(m=10, h=20, c=20)),
                  (30, dict(sibling='fits')), (30, dict(sibling='fewer')), (30, dict(sibling='prev'))):
        tot = [0, 0, 0]
        for seed in range(20):
            r = fuzz(B, seed, **kw); tot = [a + b for a, b in zip(tot, r)]
        print('fuzz B=%d %s: 20 seeds x 3000 transactions, V1 V2 V4 V5 BU1 CB3 hold; merges %d, '
              'deletes %d, space splits %d' % (B, kw, tot[0], tot[1], tot[2]))
    for name, kw in sets:
        print('churn %s: %.3f splits an overwrite, %d nodes, %.1f klongs a node' % ((name,) + churn(n, 2 * n, **kw)))
        print('thrash %s: %.3f new nodes, %.3f merges, %.3f space splits an operation' % ((name,) + thrash(**kw)))
    variants = [
        ('P5: m 7, h 15, c 15', dict()),
        ('no merges', dict(merges=False)),
        ('c 22 (3B/4)', dict(c=22)),
        ('dense: m 10, h 20, c 20', dict(m=10, h=20, c=20)),
        ('sibling prev', dict(sibling='prev')),
        ('sibling fewer', dict(sibling='fewer')),
        ('sibling fits', dict(sibling='fits')),
    ]
    for name, kw in variants:
        print('==', name)
        for order in ('asc', 'desc', 'random'):
            row = []
            for keep in (2, 3, 5, 10, 30, 100, 1000):
                r = sparse(n, keep, order, **kw)
                row.append('%d: %d/%d %.2f (%.2f m/d, %.1f s/m)' % (keep, r['nodes'], r['twin'], r['x'],
                           r['merges'] / r['dels'], r['sib'] / max(1, r['merges'])))
            print(' ', order, 'filled', r['filled'], '|', ' | '.join(row))
