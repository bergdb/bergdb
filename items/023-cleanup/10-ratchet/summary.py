#!/usr/bin/env python3
"""Summarizes CleanupRatchet outputs (023-10): per segment between disturbances, D's top
nodes and inversions of the twin and the disturbed database.

Usage: python3 summary.py FILE [an]     (an: the allowance a_n; default 10 + the run's
h_fill, or 10 + 7, T1's h_fill at 1M, if the run did not measure it)
"""
import re
import sys

LINE = re.compile(r'^(twin|dist) q=(\d+) ([\w-]+): D=(\d+) tops=(\d+) inv=(\d+) rootDirty=(\d+) '
                  r'span=(\d+) made=(\d+) res=(\d+) handles=(\d+) kept=(\d+) len=(\d+) '
                  r'lag=(\d+)ms iters=(\d+) cuts=(\d+) reach=(\d+) qhead=(\d+) '
                  r'maxS: D=(\d+) tops=(\d+) inv=(\d+)')


def main():
    path = sys.argv[1]
    text = open(path).read()
    hf = [int(h) for h in re.findall(r'hFill=(\d+)', text)]
    an = int(sys.argv[2]) if len(sys.argv) > 2 else 10 + (max(hf) if hf else 7)
    hdr = re.search(r'CleanupRatchet \{(.*)\}', text).group(1)
    props = dict(kv.split('=') for kv in hdr.split(', '))
    m = int(props.get('m', 1000000))
    dist = int(props.get('dist', 200000))
    warm = 10000
    rows = {}
    for line in text.splitlines():
        x = LINE.match(line)
        if not x:
            continue
        lab, q, ph = x.group(1), int(x.group(2)), x.group(3)
        v = dict(D=int(x.group(4)), tops=int(x.group(5)), inv=int(x.group(6)),
                 made=int(x.group(9)), res=int(x.group(10)), kept=int(x.group(12)),
                 lag=int(x.group(14)), cuts=int(x.group(16)), reach=int(x.group(17)),
                 qhead=int(x.group(18)), sD=int(x.group(19)), sTops=int(x.group(20)),
                 sInv=int(x.group(21)))
        rows.setdefault(lab, []).append((q, ph, v))
    nseg = (m + dist - 1) // dist

    def seg_stats(lab, s):
        start, end = s * dist, min(m, (s + 1) * dist)
        cps = [(q, v) for q, ph, v in rows.get(lab, []) if ph == 'cp' and start < q <= end]
        if s == 0:
            cps = [(q, v) for q, v in cps if q >= warm]
        if not cps:
            return None
        late = [v for q, v in cps if q - start >= (end - start) // 2] or [cps[-1][1]]
        return dict(
            tops=(min(v['tops'] for v in late), max(v['tops'] for v in late)),
            inv=(min(v['inv'] for v in late), max(v['inv'] for v in late)),
            stops=max(v['sTops'] for q, v in cps),
            sinv=max(v['sInv'] for q, v in cps),
            sD=max(v['sD'] for q, v in cps),
            last=cps[-1][1])

    tw = [seg_stats('twin', s) for s in range(nseg)]
    di = [seg_stats('dist', s) for s in range(nseg)]
    twmax = max((t['stops'] for t in tw if t), default=0)
    twinv = max((t['sinv'] for t in tw if t), default=0)
    print(f'{path}: m={m} dist={dist} n={props.get("n")} work={props.get("work", "queue")}')
    print(f'twin steady (after {warm}): most dirty top nodes sampled {twmax}, '
          f'most inversions {twinv}; a_n = {an}; bound twin + a_n = {twmax + an}')
    print('| Seg | Twin tops | Twin inv | Dist tops | Dist inv | Dist most tops | Dist most D | Within |')
    print('|---|---|---|---|---|---|---|---|')
    for s in range(nseg):
        t, d = tw[s], di[s]
        if not d:
            continue
        fmt = lambda r: f'{r[0]}' if r[0] == r[1] else f'{r[0]}-{r[1]}'
        ok = 'yes' if d['stops'] <= twmax + an else 'no'
        print(f'| {s} | {fmt(t["tops"]) if t else "-"} | {fmt(t["inv"]) if t else "-"} | '
              f'{fmt(d["tops"])} | {fmt(d["inv"])} | {d["stops"]} | {d["sD"]} | {ok} |')
    ends = [(d['last']['tops'], d['last']['inv']) for d in di[1:] if d]
    if ends:
        rising = len(ends) > 1 and all(ends[k + 1][1] > ends[k][1] for k in range(len(ends) - 1))
        print('dist after each disturbance, at its segment end (tops/inv): '
              + ', '.join(f'{t}/{i}' for t, i in ends)
              + f'; inversions rising at every disturbance: {"yes" if rising else "no"}')
    for lab in ('twin', 'dist'):
        last = rows.get(lab, [])[-1] if rows.get(lab) else None
        if last:
            v = last[2]
            print(f'{lab} end: D={v["D"]} tops={v["tops"]} inv={v["inv"]} made={v["made"]} '
                  f'res={v["res"]} kept={v["kept"]} lag={v["lag"]}ms cuts={v["cuts"]} '
                  f'reach={v["reach"]} qhead={v["qhead"]}')
    for line in text.splitlines():
        if 'reclaim:' in line or 'hFill' in line or 'DONE' in line or line.startswith('real'):
            print('  ' + line)


if __name__ == '__main__':
    main()
