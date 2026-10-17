"""Bergdb item 002 (M46): the 2012 idea of decreasing the height of top nodes.

Part 1 checks, exhaustively for small heads, that dropping the skip slots whose target is
older than the cut changes no search from a later head for a query at or after the time
of the oldest kept top (the top live at the first available time). The search is Java's
TopDs.findSuperRootAtTime: from the head, follow the highest populated slot whose cached
time is >= t; stop when there is none; return the node if its time equals t, else follow
the lowest populated slot (the predecessor) if its time is <= t.

Part 2 computes the stored size of top nodes (40 + 16 bytes per stored slot) with the
full layout, with the dropped slots, with only the set slots stored, and with both.
"""
import random
import sys


def target(n, k):
    """The top that slot k of top n names: n with bits below k cleared, minus one."""
    return ((n >> k) << k) - 1


def slots(n, cut):
    """Slots of top n: {k: target} for set bits k of n, without those older than cut."""
    out = {}
    for k in range(n.bit_length()):
        if n >> k & 1:
            t = target(n, k)
            if t >= cut:
                out[k] = t
    return out


def search(head, t, time, layout):
    n, hops = head, 0
    if t >= time[n]:
        return n, hops
    while True:
        best = None
        for k in sorted(layout[n], reverse=True):      # highest slot first
            if time[layout[n][k]] >= t:
                best = layout[n][k]
                break
        if best is None:
            break
        n, hops = best, hops + 1
    if time[n] == t:
        return n, hops
    if not layout[n]:
        return None, hops
    low = layout[n][min(layout[n])]                    # the predecessor
    if t >= time[low]:
        return low, hops + 1
    return None, hops


def part1(max_head, seed):
    rnd = random.Random(seed)
    checked = 0
    for head in range(1, max_head + 1):
        # Increasing times with gaps, so that queries fall between tops too.
        time = []
        x = 0
        for n in range(head + 1):
            x += rnd.choice([1, 2, 3, 7])
            time.append(x)
        full = {n: slots(n, 0) for n in range(head + 1)}
        for w in [1, 2, 3, 5, 8, 13, 64, head]:
            # Top n was made when the cut was c(n) = max(0, n - w) (non-decreasing); the
            # newest cut is the head's.
            cut_of = [max(0, n - w) for n in range(head + 1)]
            cut = cut_of[head]
            trunc = {n: slots(n, cut_of[n]) for n in range(head + 1)}
            for t in range(time[cut], time[head] + 2):
                a = search(head, t, time, full)
                b = search(head, t, time, trunc)
                if a != b:
                    print("DIFFERENT", head, w, t, a, b)
                    return False
                checked += 1
    print("part 1: %d searches from heads 1 to %d, every window: the same answer and hops" % (checked, max_head))
    return True


def size(nslots):
    return 40 + 16 * nslots


def part2():
    rnd = random.Random(1)
    print("part 2: average stored bytes per top node (40 + 16 per stored slot)")
    print("%-8s %-8s %8s %8s %8s %8s" % ("age", "window", "full", "dropped", "set-only", "both"))
    for age_bits in [20, 30, 40, 47]:
        for w_bits in [10, 16, 20, 24]:
            if w_bits >= age_bits:
                continue
            tot = [0, 0, 0, 0]
            m = 20000
            for _ in range(m):
                n = (1 << age_bits) + rnd.randrange(1 << age_bits)       # ordinals of that age
                cut = n - (1 << w_bits)
                kept = slots(n, cut)
                tot[0] += size(n.bit_length())                           # today: every slot below the height
                tot[1] += size(max(kept) + 1 if kept else 0)              # dropped: up to the highest kept slot
                tot[2] += size(bin(n).count("1"))                         # only the set slots
                tot[3] += size(len(kept))                                 # both
            print("%-8s %-8s %8.0f %8.0f %8.0f %8.0f" % ("2^%d" % age_bits, "2^%d" % w_bits,
                  tot[0] / m, tot[1] / m, tot[2] / m, tot[3] / m))


if __name__ == "__main__":
    ok = part1(int(sys.argv[1]) if len(sys.argv) > 1 else 300, 7)
    part2()
    sys.exit(0 if ok else 1)
