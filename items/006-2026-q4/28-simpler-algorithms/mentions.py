#!/usr/bin/env python3
"""006-28: how much of lean/SIS/Tree names each mechanism.

Usage: python3 mentions.py LEAN_DIR > mentions.txt

For each mechanism, a pattern over identifiers. Counted, over the
declarations of lean/SIS/Tree (cut as in count.py):

* files: files with a match anywhere;
* by name: declarations whose own name matches, and their lines;
* by text: declarations whose text matches (name, statement or proof), and
  their lines.

The counts overlap: a declaration that names two mechanisms counts for
both. "By text" is an upper bound of what a change to the mechanism
touches; "by name" is nearer to what is about it.
"""
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import count  # noqa: E402

MECH = [
    ('the fuel (fuel, SegFits, Fits)', r'fuel|SegFits|Fits\b|FitsOK'),
    ('heights (gh, Ht, height)', r'\bgh\b|ghOf|Ht[A-Z]|\bht_|[Hh]eight'),
    ('outside the level bounds (outside, boundsOK, NoOutside)', r'outside|boundsOK|NoOutside'),
    ('the take-back (taken, takeBack, takenBack)', r'taken|takeBack|TakeJ|takeJ'),
    ('retarget', r'retarget'),
    ('the previous version (toPrev, unlink)', r'toPrev|unlink'),
    ('made-for ids (madeFor, replacedBy)', r'madeFor|MadeFor|replacedBy'),
    ('the merge (merge, sibling)', r'[Mm]erge|sibling'),
    ('root collapse (collapseRoot, replaceRoot, takeBackRoot)', r'[Cc]ollapse|replaceRoot|takeBackRoot'),
    ('the upward delete (deleteUpward, climb, stop node)', r'deleteUpward|climb|[Ss]top[A-Z_]|upCasc|UpCasc'),
    ('LE-b (emptyKeyNext, leb)', r'emptyKeyNext|[Ll]eb[A-Z_]|_leb\b|Leb\b'),
    ('dead klongs and theta (dead, theta)', r'[Dd]ead|theta'),
    ('live counts, the fill (LiveCounts, LiveEdges, mergeBelow)', r'LiveCounts|LiveEdges|QLive|mergeBelow|liveCount'),
    ('the split and its cascade (handleFull, appendKlongs)', r'handleFull|appendKlongs|replaceOrAdd'),
    ('new segments (newSeg, setNode, putSegs)', r'[Nn]ewSeg|setNode|putSegs'),
    ('segment roots and leaves (segRoot, descendToSegmentRoot, SegRoot)', r'[Ss]egRoot|descendToSegmentRoot|segLeaf|SegLeaf'),
    ('the top node and skip pointers (newSuperRoot, skips, topAt)', r'newSuperRoot|skips|topAt|superRoot'),
    ('the scan (scan, Scan, chain of GetMany)', r'[Ss]can|chainSetup|nextGo|setupGo'),
    ('earlier times (Historical, hist prefix)', r'Historical|historical|HistPrefix|upTo'),
    ('reclaim\'s touch (touch)', r'[Tt]ouch'),
]


def main():
    root = os.path.join(sys.argv[1], 'SIS', 'Tree')
    files = sorted(f for f in os.listdir(root) if f.endswith('.lean'))
    data = []
    total = 0
    for f in files:
        with open(os.path.join(root, f), encoding='utf-8') as fh:
            lines = fh.read().split('\n')
        if lines and lines[-1] == '':
            lines.pop()
        total += len(lines)
        pos = 0
        for kind, name, n in count.decls(os.path.join(root, f)):
            data.append((f, kind, name, '\n'.join(lines[pos:pos + n]), n))
            pos += n
    print(f'lean/SIS/Tree: {len(files)} files, {total} lines, {len(data)} pieces')
    print()
    print(f'{"mechanism":66} {"files":>5} {"by name":>14} {"by text":>15}')
    for label, pat in MECH:
        rx = re.compile(pat)
        fs = set()
        nd = nl = td = tl = 0
        for f, kind, name, text, n in data:
            if rx.search(text):
                fs.add(f)
                td += 1
                tl += n
            if kind and rx.search(name):
                nd += 1
                nl += n
        print(f'{label:66} {len(fs):5} {nd:6} {nl:7} {td:6} {tl:8}  {100 * tl / total:4.1f} %')


if __name__ == '__main__':
    main()
