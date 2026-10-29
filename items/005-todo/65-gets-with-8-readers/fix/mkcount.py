# bergdb 005-65's fix: a copy of Eviction.java with counters of the entries into evictorLock,
# for EntriesProbe (run.sh): wake's entries and, with the fix, its skips; the thread's entries;
# the after-load calls over the trigger; the requests the thread took (series). Works on the
# code before the fix and on the fix. Written 2026-10-29 by Claude (Opus 5.5, Claude Code).
# Usage: python3 -I mkcount.py IN OUT
import sys

s = open(sys.argv[1]).read()


def rep(old, new):
    global s
    assert s.count(old) == 1, (old, s.count(old))
    s = s.replace(old, new)


L = 'java.util.concurrent.atomic.LongAdder'
rep("""    private final Object evictorLock = new Object();""",
    """    private final Object evictorLock = new Object();
    public static final %s WAKE_ENTRIES = new %s(), WAKE_SKIPS = new %s(),
            THREAD_ENTRIES = new %s(), OVER = new %s(), SERIES = new %s();
    public long batchesSoFar() { return batches; }""" % ((L,) * 6))
rep("""        if (bytes <= trigger) return;
        if (Thread.holdsLock(in.getWriteLock()) || !in.isActive()) return;""",
    """        if (bytes <= trigger) return;
        OVER.increment();
        if (Thread.holdsLock(in.getWriteLock()) || !in.isActive()) return;""")
if "        if (wanted) return;\n" in s:
    rep("""        if (wanted) return;
        synchronized (evictorLock) {
            wanted = true;""", """        if (wanted) {
            WAKE_SKIPS.increment();
            return;
        }
        synchronized (evictorLock) {
            WAKE_ENTRIES.increment();
            wanted = true;""")
else:
    rep("""        synchronized (evictorLock) {
            wanted = true;""", """        synchronized (evictorLock) {
            WAKE_ENTRIES.increment();
            wanted = true;""")
rep("""                synchronized (evictorLock) {
                    while (!wanted) {""", """                synchronized (evictorLock) {
                    THREAD_ENTRIES.increment();
                    while (!wanted) {""")
rep("""                    wanted = false;
                    running = true;""", """                    wanted = false;
                    running = true;
                    SERIES.increment();""")
rep("""                    synchronized (evictorLock) {
                        running = false;""", """                    synchronized (evictorLock) {
                        THREAD_ENTRIES.increment();
                        running = false;""")
open(sys.argv[2], 'w').write(s)
