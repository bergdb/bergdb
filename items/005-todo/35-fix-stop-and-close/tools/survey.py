"""Bergdb 005-35 (2026-10-24): finds the calls of stop() and close() on Db and Database
objects in bergdb's Java, by a heuristic: the receiver's declared type in the same file
(Db, Database, DatabaseImp), or a call on a builder's start(). For each call: whether a
sync() (or a close()) comes in the 5 lines before it. Prints a summary; writes one line
per call to OUT. Usage: python3 survey.py JAVA_DIR OUT"""
import os, re, sys, collections

root = sys.argv[1]
call = re.compile(r'(\b[\w.()]+?)\.(stop|close)\(\)\s*;')
types = ('Db', 'Database', 'DatabaseImp')
rows = []
for d in ('src', 'src-dev', 'stress', 'bench'):
    for dirpath, _, files in os.walk(os.path.join(root, d)):
        for f in files:
            if not f.endswith('.java'):
                continue
            p = os.path.join(dirpath, f)
            lines = open(p, encoding='utf-8', errors='replace').read().split('\n')
            text = '\n'.join(lines)
            for i, line in enumerate(lines):
                for m in call.finditer(line):
                    recv, meth = m.group(1), m.group(2)
                    name = recv.split('.')[-1]
                    kind = None
                    if recv.endswith('start()') or recv.endswith('build()'):
                        kind = 'builder'
                    else:
                        for t in types:
                            if re.search(r'\b' + t + r'\s+' + re.escape(name) + r'\b', text):
                                kind = t
                                break
                        if kind is None and name in ('db', 'database'):
                            kind = '?' + name
                    if kind is None:
                        continue
                    before = '\n'.join(lines[max(0, i - 5):i])
                    synced = 'sync(' in before or 'close()' in before
                    rows.append((os.path.relpath(p, root), i + 1, kind, meth, synced, line.strip()))
by = collections.Counter((r[2] if not r[2].startswith('?') else 'Db?', r[3]) for r in rows)
print('calls by receiver type and method:', dict(by))
for meth in ('stop', 'close'):
    rs = [r for r in rows if r[3] == meth]
    print('\n%s(): %d calls, %d with a sync in the 5 lines before' % (meth, len(rs), sum(r[4] for r in rs)))
    files = collections.Counter(r[0] for r in rs)
    for f, n in files.most_common():
        ns = sum(1 for r in rs if r[0] == f and r[4])
        print('  %-55s %3d  (%d after a sync)' % (f, n, ns))
with open(sys.argv[2], 'w') as out:
    for r in rows:
        out.write('%s:%d %s.%s() sync-before=%s | %s\n' % r)
