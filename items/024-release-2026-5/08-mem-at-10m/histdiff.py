#!/usr/bin/env python3
# Class histograms minus the empty database's, in bytes a KV (bergdb 024-08).
# Usage: histdiff.py EMPTY.hist NAME:N:FILE ...
import sys, re
def load(f):
    d = {}
    for line in open(f):
        m = re.match(r'\s*\d+:\s+(\d+)\s+(\d+)\s+(\S+)', line)
        if m: d[m.group(3)] = (int(m.group(1)), int(m.group(2)))
        m = re.match(r'Total\s+(\d+)\s+(\d+)', line)
        if m: d['Total'] = (int(m.group(1)), int(m.group(2)))
    return d
e = load(sys.argv[1])
runs = [a.split(':', 2) for a in sys.argv[2:]]
hs = [(n, int(c), load(f)) for n, c, f in runs]
classes = set()
for n, c, h in hs:
    for k, (i, b) in h.items():
        if abs(b - e.get(k, (0, 0))[1]) / c >= 0.05: classes.add(k)
order = sorted(classes, key=lambda k: -max(h.get(k, (0, 0))[1] for _, _, h in hs))
short = {'[J': 'long[]', '[B': 'byte[]', '[Lbergdb.dag.Pointee;': 'Pointee[]',
         '[Ljava.util.HashMap$Node;': 'HashMap$Node[]', '[Ljava.lang.Object;': 'Object[]',
         '[Ljdk.internal.vm.FillerElement;': 'FillerElement[] (G1 filler)'}
print('%-34s' % 'class' + ''.join('%22s' % n for n, _, _ in hs))
print('%-34s' % '' + ''.join('%22s' % 'bytes/KV (inst/KV)' for _ in hs))
for k in order:
    row = '%-34s' % short.get(k, k.replace('java.util.', '').replace('java.lang.', ''))
    for n, c, h in hs:
        i, b = h.get(k, (0, 0)); i0, b0 = e.get(k, (0, 0))
        row += '%14.2f (%5.3f)' % ((b - b0) / c, (i - i0) / c)
    print(row)
