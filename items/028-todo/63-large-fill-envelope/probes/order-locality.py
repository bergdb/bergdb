#!/usr/bin/env python3
"""The locality of LargeReclaimRun's key order (bergdb 028-63).

keyAt(s) = (a s + offset) mod n, with a = 1,000,003 + seed mod 100,000, raised to the
next number coprime with n. Slots s and s + d write keys at a distance a d mod n. For
each seed this prints the smallest slot distance d at which the order writes a key
within W keys of an earlier one (a d = t mod n with 0 < |t| <= W): the smaller d, the
more puts land in the same key nodes while they are dirty.

Usage: python3 order-locality.py FIRST_SEED LAST_SEED [KEYS [W]]
"""
import sys
from math import gcd


def multiplier(seed, n):
    a = 1_000_003 + seed % 100_000
    while gcd(a, n) != 1:
        a += 1
    return a


def locality(a, n, w):
    inv = pow(a, -1, n)
    return min((t * inv) % n for t in range(-w, w + 1) if t)


def main():
    first, last = int(sys.argv[1]), int(sys.argv[2])
    n = int(sys.argv[3]) if len(sys.argv) > 3 else 10_000_000
    w = int(sys.argv[4]) if len(sys.argv) > 4 else 8
    for seed in range(first, last + 1):
        a = multiplier(seed, n)
        print(seed, a, locality(a, n, w))


if __name__ == "__main__":
    main()
