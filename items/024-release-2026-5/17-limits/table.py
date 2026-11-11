# 024-17, section 4.1: a LimitProbe output (stdin) to a Markdown table, random and
# consecutive keys side by side ("rand / seq"). Usage: python3 table.py counts|times < file
import sys
mode = sys.argv[1]
d = {}
for l in sys.stdin:
    if l[:3] in ("put", "del"):
        r = l.split()
        d[(r[0][:3], r[1], int(r[2]))] = r
def pair(op, b, i, f):
    return f(d[(op, "rand", b)][i]) + " / " + f(d[(op, "seq", b)][i])
sizes = sorted({k[2] for k in d})
if mode == "counts":
    print("| Op  | Batch   | B/op      | Dirty/op    | Largest rec kB    | Bound, first      |")
    print("|-----|--------:|-----------|-------------|-------------------|-------------------|")
    for op in ("put", "del"):
        for b in sizes:
            print(f"| {op} | {b:>7,} | {pair(op,b,6,str):<9} | {pair(op,b,13,lambda x: f'{float(x):.2f}'):<11} "
                  f"| {pair(op,b,9,lambda x: f'{int(x)/1000:,.0f}'):<17} | {pair(op,b,11,lambda x: f'{int(x):,}'):<17} |")
else:
    print("| Op  | Batch   | us/op       | p50 ms          | max ms        |")
    print("|-----|--------:|-------------|-----------------|---------------|")
    for op in ("put", "del"):
        for b in sizes:
            print(f"| {op} | {b:>7,} | {pair(op,b,5,lambda x: f'{int(x)/1000:.1f}'):<11} "
                  f"| {pair(op,b,8,lambda x: f'{float(x):.2f}'):<15} | {pair(op,b,7,lambda x: f'{float(x):.1f}'):<13} |")
