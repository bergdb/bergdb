# bergdb 020-26: prints a TLC error trace as its actions and the variables each changed.
import re, sys
log = open(sys.argv[1]).read()
i = log.find('Error: The following behavior')
if i < 0:
    i = log.find('The behavior up to this point')
body = log[i:]
parts = re.split(r'\n(?=State \d+:|Back to state)', body)[1:]
prev = {}
for p in parts:
    head = p.split('\n')[0]
    act = re.search(r'<(\w+)', head)
    vs = {}
    for m in re.finditer(r'/\\ (\w+) = (.*?)(?=\n/\\ |\Z)', p, re.S):
        vs[m.group(1)] = ' '.join(m.group(2).split())
    ch = [f'{k}={v}' for k, v in vs.items() if prev.get(k) != v and k not in ('ncreate', 'used', 'now')]
    print(head.split(':')[0], act.group(1) if act else '', '|', '; '.join(ch)[:600])
    prev = vs
