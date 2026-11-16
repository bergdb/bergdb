#!/usr/bin/env python3
"""006-28: where the lines of lean/ go, by the writer's rule and by concern.

Usage: python3 count.py LEAN_DIR > counts.txt

A rough count, by names. Each .lean file is cut into declarations (a line
that starts a theorem, lemma, def, abbrev, structure, inductive, instance or
example, with the doc comment before it). A declaration gets:

* a RULE: the part of the writer it is about, from its own name, else from
  its file's name (first match in RULES' order);
* a CONCERN: the invariant it carries, from its file's name, else its own
  name (first match in CONCERNS' order).

Lines before the first declaration of a file (imports, headers) count with
the file's name alone. Nothing is built; a name can mislead.
"""
import os
import re
import sys
from collections import defaultdict

DECL = re.compile(
    r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*'
    r'(theorem|lemma|def|abbrev|structure|inductive|instance|example|opaque|class)\b\s*([^\s:({\[]*)')

# First match wins. Patterns are searched in the declaration's name, then in
# the file's name (case-insensitive).
RULES = [
    ('merge', r'merge|sibling'),
    ('root collapse', r'collapse|replaceroot|takebackroot|delroot|replacefull'),
    ('upward delete, stop node, LE-b', r'upward|climb|leb|emptykeynext|stop|upcasc|upunlink|delstepsup|emptyany|emptyroom|delempty|upholder|upall|getup|takeup|deadup'),
    ('delete: leaf bitmap and its steps', r'del|bitmap'),
    ('split and cascade', r'handlefull|appendklongs|split|casc|chain|full|halves|replaceoradd'),
    ('new segments', r'newseg|setnode|putsegs|segroot|newkey'),
    ('put: leaf with room, setValue', r'put|setvalue|room|inplace'),
    ('top node, skip pointers', r'supr|superroot|newsuperroot|findroot|top(?!theorem)|skip|rootwalk'),
    ('scan', r'scan'),
    ('earlier times', r'histor|prefix|export'),
    ('key node: klongs, searches, encoding', r'klong|search|knode|encod|cv|bits|interval|keyhist|entries|nodemap|sorted|keywell|keylevel'),
]

CONCERNS = [
    ('fuel and heights', r'height|fuel|fit|nooutside|stratum|outside|^ht|depth|under'),
    ('dead klongs (theta)', r'dead'),
    ('live counts (fill)', r'live(?!append)|fill|nonempty'),
    ('take-back, previous versions, made-for, books', r'take|taken|madefor|book|good|j2|hole|chk|unlink|holder|prev|retarget|commute|swap'),
    ('reading (TP10)', r'^get|writerget|read|latest'),
    ('key order and ranges', r'range|sorted|ord'),
    ('scan (TP11)', r'scan'),
    ('earlier times', r'histor|prefix|export'),
    ('tree shape: pointers, kinds, sizes, cache', r'writertree|ptrs|pointer|kinds|left|size|cache|frame|shape|walk|children|linked|alloc|fields|stateinv|putinv|inv|overlay|level|balance|count'),
    ('key node: klongs, searches, encoding', r'klong|search|node|encod|cv|bits|interval|keyhist|entries|key'),
]


def classify(name, fname, table):
    for label, pat in table:
        if re.search(pat, name, re.I):
            return label
    for label, pat in table:
        if re.search(pat, fname, re.I):
            return label
    return 'general'


def decls(path):
    """Yield (kind, name, nlines) for a file; kind None for the header."""
    with open(path, encoding='utf-8') as f:
        lines = f.read().split('\n')
    if lines and lines[-1] == '':
        lines.pop()
    starts = []
    doc_start = None
    in_doc = False
    for i, line in enumerate(lines):
        if line.startswith('/--'):
            doc_start = i
            in_doc = '-/' not in line
            continue
        if in_doc:
            if '-/' in line:
                in_doc = False
            continue
        m = DECL.match(line)
        if m:
            s = doc_start if doc_start is not None else i
            starts.append((s, m.group(1), m.group(2)))
            doc_start = None
        elif line.strip() and not line.startswith('@[') and doc_start is not None \
                and not line.startswith(' '):
            doc_start = None
    n = len(lines)
    if not starts:
        yield (None, '', n)
        return
    if starts[0][0] > 0:
        yield (None, '', starts[0][0])
    for j, (s, kind, name) in enumerate(starts):
        e = starts[j + 1][0] if j + 1 < len(starts) else n
        yield (kind, name, e - s)


def main():
    root = sys.argv[1]
    by_dir = defaultdict(lambda: [0, 0, 0])            # files, lines, theorems
    kinds = defaultdict(lambda: defaultdict(int))      # dir -> kind -> lines
    rule = defaultdict(lambda: [0, 0])                 # label -> decls, lines
    concern = defaultdict(lambda: [0, 0])
    cross = defaultdict(int)                           # (rule, concern) -> lines
    general = defaultdict(int)                         # file -> lines with no rule
    for dp, dn, fn in os.walk(root):
        if '.lake' in dp:
            continue
        for f in sorted(fn):
            if not f.endswith('.lean'):
                continue
            path = os.path.join(dp, f)
            d = os.path.relpath(dp, root)
            by_dir[d][0] += 1
            base = f[:-5]
            for kind, name, n in decls(path):
                by_dir[d][1] += n
                if kind in ('theorem', 'lemma'):
                    by_dir[d][2] += 1
                kinds[d][kind or 'header'] += n
                if d != os.path.join('SIS', 'Tree'):
                    continue
                r = classify(name, base, RULES)
                if r == 'general':
                    general[base] += n
                c = classify('', base, CONCERNS)
                if c == 'general':
                    c = classify(name, '', CONCERNS)
                rule[r][0] += 1
                rule[r][1] += n
                concern[c][0] += 1
                concern[c][1] += n
                cross[(r, c)] += n

    print('== lean/ by directory: files, lines, theorems and lemmas')
    for d in sorted(by_dir):
        print(f'{d:12} {by_dir[d][0]:5} {by_dir[d][1]:8} {by_dir[d][2]:6}')
    print('total', sum(v[0] for v in by_dir.values()), sum(v[1] for v in by_dir.values()),
          sum(v[2] for v in by_dir.values()))
    print()
    print('== lines by kind of declaration')
    for d in sorted(kinds):
        ks = ', '.join(f'{k} {v}' for k, v in sorted(kinds[d].items(), key=lambda x: -x[1]))
        print(f'{d}: {ks}')
    tot = sum(v[1] for v in rule.values())
    print()
    print(f'== SIS/Tree by the writer\'s rule ({tot} lines): declarations, lines, share')
    for k, v in sorted(rule.items(), key=lambda x: -x[1][1]):
        print(f'{k:42} {v[0]:6} {v[1]:7} {100 * v[1] / tot:5.1f} %')
    print()
    print('== SIS/Tree by concern: declarations, lines, share')
    for k, v in sorted(concern.items(), key=lambda x: -x[1][1]):
        print(f'{k:50} {v[0]:6} {v[1]:7} {100 * v[1] / tot:5.1f} %')
    print()
    print('== SIS/Tree, rule by concern, lines (cells of 800 lines or more)')
    for (r, c), n in sorted(cross.items(), key=lambda x: -x[1]):
        if n >= 800:
            print(f'{n:7}  {r}  /  {c}')
    print()
    print('== SIS/Tree, the files with most lines under no rule ("general")')
    print('; '.join(f'{f} {n}' for f, n in sorted(general.items(), key=lambda x: -x[1])[:60]))


if __name__ == '__main__':
    main()
