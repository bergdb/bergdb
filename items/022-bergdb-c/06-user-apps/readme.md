# 022-06 New users of the C library

Created 2026-11-09 by Frans Lundberg. Status: done.

coord-1109 and Frans (17:19, Frans: "Good idea, I think."): test the C port
as a black-box user, the way the day's new-user applications tested Java
(006-20). Three users, each with only what a user of the C library has (a
kit of `bergdb.h`, `c/readme.md`, the examples and the two built libraries
of 022's 2026.4 at `391c3cf5`), wrote a real application with an oracle of
its own, from 17:25 to about 18:25, and reported; fixers then took the
findings, until about 19:15. Where a finding could be Java's too, it was
run in Java first: C follows Java's Core, so C changes only where C alone
is at fault.

* [u1-device-store.md](u1-device-store.md), 022-06-1: an embedded store of
  device configuration and events (binary keys of every byte, long keys,
  prefix scans, past times, restarts, kill -9). No lost or wrong data in
  about 810,000 checks.
* [u2-error-paths.md](u2-error-paths.md), 022-06-2: every error a
  deployment meets (a full disk, deleted files, locks, bad arguments,
  allocation failures). Every listed refusal as documented.
* [u3-audit-log.md](u3-audit-log.md), 022-06-3: an audit log with
  retention, read at past times. Time travel exact in 8,620 checks.
* The fixers' records: [u3-reclaim-fifo.md](u3-reclaim-fifo.md) (U3-1 and
  U3-2 in Java), [u2-in-java.md](u2-in-java.md) (U2-2, U2-3, U2-6, U2-8 and
  U1-1, U1-2 in Java; C's two quadratics fixed), [u1-eviction.md](u1-eviction.md)
  (U1-3, U1-4 fixed in C), [fixes.md](fixes.md) (the documentation and the
  small C fixes).


# 1. What came of each finding

| Finding     | Severity | Outcome                                                         |
|---|---|---|
| U3-1, U3-2  | medium   | Java's too, since 2026.3: 021-25, a known issue of 2026.4; fix to Frans |
| U1-1        | high     | shared-prefix part C's own, fixed; the rest Java's still-dirty loop |
| U2-3        | medium   | the long key's own put C's own, fixed; the later put Java's        |
| U1-2        | medium   | Java's design: the same stream length                            |
| U1-3, U1-4  | medium   | C's own eviction: fixed (u1-eviction.md)                         |
| U2-1        | medium   | a regression in Java from Z1: fixed in Java as 021-26; C follows |
| U2-4, U1-8  | medium   | Java's too: 021-27, documented in 2026.4; a fix to Frans         |
| U2-2        | medium   | Java's too (014-01's zero fill)                                  |
| U2-6, U2-8  | low      | Java's too; a check at sync or a refusal of "/#" puts: to Frans  |
| U2-10, U2-14 | low     | C's own: fixed (BERGDB_IO at the open; NULL test clock refused)  |
| U2-13, U1-5 | low      | C's own: pinned_bytes counted twice and too much; fixed          |
| the others  | low      | words in `bergdb.h` and `c/readme.md` (fixes.md)                 |

C faults fixed in all: six (two quadratics in the dirty-node bound, two in
eviction, two in `pinned_bytes`), and two refusals (U2-10, U2-14). Java
issues found or confirmed: 021-25 (reclaim and a log keyed by time),
021-26 (the clock past the maximum, fixed), 021-27 (`getTrans` at a wrong
position), the still-dirty loop's cost with long keys, and two smaller ones
(U2-6, U2-8). For Frans's decision: a read-only open, a buffer-size option,
a close that gives its error's text (fixes.md, section 1.3), and the
departure of `bergdb_close` after a reported failure (022-05).
