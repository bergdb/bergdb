# 024-14: parse THR outputs into rows. summ.py DIR -> one line per run, key=value
import sys, os, re, glob
def parse(f):
    d = {}
    for line in open(f):
        line = line.strip()
        m = re.match(r'\[[\d.]+s\] (TWIN )?(\w+) (.*)', line)
        if not m: continue
        twin, kind, rest = m.group(1) or '', m.group(2), m.group(3)
        kv = dict(re.findall(r'([\w/.]+)=(-?[\d.]+)', rest))
        if kind in ('NODES', 'SCAN', 'STATE'):
            label = rest.split()[0]
            d[twin + kind + ':' + label] = kv
        elif kind in ('FILL', 'OVER', 'DELETE', 'CHURN', 'DRIVE') and 'tx' in kv and 'ops/s' in kv:
            d[twin + kind] = kv
        if line.startswith('rc='): d['rc'] = line
    for line in open(f):
        if line.startswith('rc='): d['rc'] = line.split()[0]
    return d
if __name__ == '__main__':
    for f in sorted(glob.glob(os.path.join(sys.argv[1], '*.txt'))):
        d = parse(f)
        name = os.path.basename(f)[:-4]
        g = lambda k, f: d.get(k, {}).get(f, '-')
        print(name, d.get('rc'), 'fillNodes', g('NODES:fill','keyNodes'), 'fill/s', g('FILL','ops/s'),
              'fillRec/op', g('FILL','rec/op'), 'shapeNodes', g('NODES:shape','keyNodes'),
              'twin', g('TWIN NODES:fill','keyNodes'), 'driveNodes', g('NODES:drive','keyNodes'),
              'twinDrive', g('TWIN NODES:drive','keyNodes'))
