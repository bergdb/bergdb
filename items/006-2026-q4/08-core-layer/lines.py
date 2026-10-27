"""Counts the lines of Java source files (bergdb 006-08).

Usage: python3 -I lines.py [--each] FILE...

Prints the number of lines and of code lines, the lines with code on them:
not blank, not only a comment. With --each, one line per file first: its
code lines, its lines and its path.
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from strip import mask


def main(args):
    each = args[:1] == ["--each"]
    total = code = 0
    for path in args[1:] if each else args:
        src = open(path, encoding="utf-8").read()
        n = src.count("\n")
        c = sum(1 for line in mask(src).split("\n") if line.strip())
        if each:
            print("%6d %6d %s" % (c, n, path))
        total += n
        code += c
    print("%d lines, %d code lines" % (total, code))


if __name__ == "__main__":
    main(sys.argv[1:])
