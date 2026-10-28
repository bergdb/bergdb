012-15. Task: speed, memory and size against Java
=================================================

Created 2026-10-27 by Claude (Opus 5.5, Claude Code), with 012-01, for
Frans Lundberg. **Status: draft, for Frans's approval with 012-01.**
Phase E (012-01, section 8). Effort: high. After: 012-13.


# 1. The goal

Numbers, not targets (012-01, section 1, item 8): how fast and how large
the C clone is against Java on F53, measured the same way, for 012-16's
report and for the decision on what comes next.

Done when this file has, with the method, the commits and the raw
outputs:

1. **Writes**: transactions a second for single puts and for batches,
   without and with `sync`, for 1M and 10M keys; bytes appended per put
   (equal by construction, so a check).
2. **Reads**: `getOne` a second, latest and historical, from memory and
   with a small budget; `getMany` keys a second.
3. **Startup**: the time to open a database of 10M keys at startup
   distances of 50 and 200 MB, warm (in the OS cache), as 007-05 measures
   Java's.
4. **Memory**: C's bytes per key (resident set and the budget's count)
   against Java's heap bytes per key (Props MEM, 006-02).
5. **Size**: lines of C (code lines, as 006-08 counts them, against its
   estimate of 10,000 to 17,000) and the library's machine code at `-O2`
   and `-Os` on arm64, against 006-08's estimate and LMDB's 53 kB.
6. One thread for both, as C has one caller; Java's numbers with several
   readers noted beside, as what C does not do.


# 2. Read first

* 006-02 (Props: MEM, CORE, SS), 007-05 (startup time), 009-03 (Java's
  measurements), `java/props.sh`, `java/perf.sh`,
  `java/stress/performance.sh`; 006-08, sections 5 and 6.3.
* The memory notes on timing on F53: quiet windows, no own activity during
  a run, startup distances of 50 MB and more.


# 3. The work

1. C programs for each measurement, and Java's counterparts from the
   existing tools where they exist (Props, `StartupBench`), or small ones
   in the harness.
2. The runs in quiet windows, Java and C in turns, each at least three
   times; medians reported.
3. The table and a short reading of it.


# 4. Tests

None; the measurements run on code that passed 012-14.


# 5. Notes

* Timing runs disturb, and are disturbed by, other sessions: run only in
  a quiet window, in the background, with this session idle until they
  end.
* Optimizations are not this task's: if C is slow somewhere, say where,
  and propose; a change must keep the bytes (012-01, 4.2).


# 6. Progress

Not started.
