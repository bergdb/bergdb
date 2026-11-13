# Prints a Java file's Javadoc comments and the public declaration after each, no bodies.
import sys, re
src = open(sys.argv[1], encoding='utf-8').read()
i = 0
out = []
for m in re.finditer(r'/\*\*(.*?)\*/\s*((?:@\w+(?:\([^)]*\))?\s*)*)([^;{]*)', src, re.S):
    doc = m.group(1)
    decl = ' '.join(m.group(3).split())
    if 'private' in decl.split('(')[0].split() : continue
    lines = [re.sub(r'^\s*\* ?', '', l) for l in doc.split('\n')]
    out.append('\n'.join(l for l in lines).strip())
    out.append('  >> ' + decl)
    out.append('')
print('\n'.join(out))
