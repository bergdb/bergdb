#!/usr/bin/env python3
"""The study's own workloads (bergdb 026-21, section 3) as model inputs: files
with the lines of trace format 3 (027-02) that `steptimes` reads, TREE, TX and
OP; no structure (the model makes its own). Node size 30 (the users' size,
026-08): TREE 30 G H 1 8 17 17 7, record format 7's thresholds and theta.

Keys as Keys.toSegments makes them: a segment's compare value is its bytes
(here a number) shifted left by 6, with its length in bits 3 to 5; a long
segment (7 bytes) continues in the next segment's tree.

  bulk-B    20,000 keys put in key order, B a transaction (B = 500, 100, 10):
            a sorted bulk load, 026-20's first bad case for step times.
  pub-K     a Pub-like index (the Pub layer's index updates, 026-20's second
            bad case): 5,000 objects, each a key [O, id] with an index entry
            [I, value.id]; loaded 50 objects a transaction; then
            transactions of K changes to random objects (K = 1, 10, 100):
            80 % an update (put the object, delete the old index entry, put
            the new one), 10 % a delete (the object and its entry), 10 % a
            new object (its key and its entry). One operation a key, in key
            order, as Java's Dag gets them.

Usage: workloads.py OUTDIR
"""
import random, sys, os

def seg(payload, length):
    return (payload << 6) | (length << 3)

def short(n):      # a short last segment of 6 bytes
    return seg(n, 6)

O = seg(0x4F4F4F4F4F4F4F, 7)   # "OOOOOOO", a long segment
I = seg(0x49494949494949, 7)   # "IIIIIII"

def key_str(k):
    return f"{len(k)} " + " ".join(str(c) for c in k)

def write(path, G, H, txs):
    with open(path, "w") as f:
        f.write("TRACE 3\n")
        f.write(f"TREE 30 {G} {H} 1 8 17 17 7\n")
        f.write("TX 0\nEND 0\n")
        for i, ops in enumerate(txs, start=1):
            f.write(f"TX {i}\n")
            for op in sorted(ops, key=lambda o: o[1]):
                if op[0] == "P":
                    f.write(f"OP P {key_str(op[1])} {op[2]}\n")
                else:
                    f.write(f"OP D {key_str(op[1])}\n")
            f.write(f"END {i}\n")

def bulk(B, n=20000, seed=1):
    rnd = random.Random(seed)
    keys = [(short(1000 + i),) for i in range(n)]
    return [[("P", k, rnd.randrange(1, 2**40)) for k in keys[j:j + B]] for j in range(0, n, B)]

def pub(K, n=5000, txs=None, seed=1):
    rnd = random.Random(seed * 7919 + K)
    val = {}
    out = []
    ids = list(range(n))
    for j in range(0, n, 50):
        ops = []
        for o in ids[j:j + 50]:
            v = rnd.randrange(1, 2**20)
            val[o] = v
            ops.append(("P", (O, short(o)), rnd.randrange(1, 2**40)))
            ops.append(("P", (I, short((v << 20) | o)), rnd.randrange(1, 2**40)))
        out.append(ops)
    nxt = n
    txs = txs or max(100, 20000 // K)
    for _ in range(txs):
        ops = {}
        live = list(val.keys())
        chosen = rnd.sample(live, min(K, len(live)))
        for o in chosen:
            r = rnd.random()
            if r < 0.8:
                v = rnd.randrange(1, 2**20)
                while v == val[o]:
                    v = rnd.randrange(1, 2**20)
                ops[(O, short(o))] = ("P", (O, short(o)), rnd.randrange(1, 2**40))
                ops[(I, short((val[o] << 20) | o))] = ("D", (I, short((val[o] << 20) | o)))
                ops[(I, short((v << 20) | o))] = ("P", (I, short((v << 20) | o)), rnd.randrange(1, 2**40))
                val[o] = v
            elif r < 0.9:
                ops[(O, short(o))] = ("D", (O, short(o)))
                ops[(I, short((val[o] << 20) | o))] = ("D", (I, short((val[o] << 20) | o)))
                del val[o]
            else:
                o2 = nxt
                nxt += 1
                v = rnd.randrange(1, 2**20)
                ops[(O, short(o2))] = ("P", (O, short(o2)), rnd.randrange(1, 2**40))
                ops[(I, short((v << 20) | o2))] = ("P", (I, short((v << 20) | o2)), rnd.randrange(1, 2**40))
                val[o2] = v
        out.append(list(ops.values()))
    return out

def main():
    outdir = sys.argv[1]
    os.makedirs(outdir, exist_ok=True)
    for B in (500, 100, 10):
        write(os.path.join(outdir, f"bulk-{B}.trace"), 0, 4, bulk(B))
    for K, txs in ((1, 4000), (10, 1000), (100, 200)):
        write(os.path.join(outdir, f"pub-{K}.trace"), 1, 4, pub(K, txs=txs))

if __name__ == "__main__":
    main()
