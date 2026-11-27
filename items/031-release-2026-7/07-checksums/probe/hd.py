"""031-07: the Hamming distance of CRC-32C truncated to 24 bits over a record header
(028-67's check): 16 bytes of database id, 8 of position, 29 of header fields (size 4,
format 1, time 8, startupPos 8, topPos 8); only the header's 29 bytes and the 24-bit field
are stored, so only they can be damaged."""
import itertools, sys

POLY = 0x82F63B78
TABLE = []
for b in range(256):
    c = b
    for _ in range(8):
        c = (c >> 1) ^ POLY if c & 1 else c >> 1
    TABLE.append(c)

def crc_lin(data):            # init 0, no final xor: linear in the data
    c = 0
    for x in data:
        c = TABLE[(c ^ x) & 0xff] ^ (c >> 8)
    return c

def crc32c(data):
    c = 0xffffffff
    for x in data:
        c = TABLE[(c ^ x) & 0xff] ^ (c >> 8)
    return c ^ 0xffffffff

assert crc32c(b"123456789") == 0xe3069283

def syndromes(n, stored, mask, shift):
    out = []
    for i in stored:
        for j in range(8):
            m = bytearray(n); m[i] = 1 << j
            out.append((crc_lin(m) >> shift) & mask)
    return out

def hd(syn, checkbits, maxw=4):
    # minimal weight of an undetected nonzero error: data error e (weight w) with the
    # check field's error equal to its syndrome (weight popcount)
    best = None
    k = len(syn)
    for w in range(1, maxw + 1):
        for comb in itertools.combinations(range(k), w):
            s = 0
            for c in comb:
                s ^= syn[c]
            tot = w + bin(s).count("1")
            if best is None or tot < best[0]:
                best = (tot, comb, s)
        if best is not None and best[0] <= w + 1:
            break
        if w >= 3 and k > 150:
            break
    return best

n = 16 + 8 + 29
for order, stored in (("id, pos, header", list(range(24, 53))), ("header, id, pos", list(range(0, 29)))):
    for name, mask, shift in (("low 24 bits", 0xffffff, 0), ("high 24 bits", 0xffffff, 8),
                              ("all 32 bits", 0xffffffff, 0)):
        syn = syndromes(n, stored, mask, shift)
        zero1 = sum(1 for s in syn if s == 0)
        dup = len(syn) - len(set(syn))
        w1 = min(bin(s).count("1") for s in syn)
        res = hd(syn, 24 if mask == 0xffffff else 32, 3)
        print(f"{order}; {name}: single errors undetected {zero1}; equal syndromes "
              f"(double errors undetected) {dup}; least syndrome weight {w1}; "
              f"least undetected weight found (data errors up to 3 bits) {res[0]}")
