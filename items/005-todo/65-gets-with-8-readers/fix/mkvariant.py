# bergdb 005-65's fix: a deliberately broken copy of Eviction.java, for the race tests
# (run.sh). Written 2026-10-29 by Claude (Opus 5.5, Claude Code).
# Usage: python3 -I mkvariant.py NAME IN OUT
#   norecheck     the thread waits after its batches without checking for a request first
#   lateclear     the thread clears wanted after its batches, not when it takes the request
#   oldinterrupt  an interrupt ends the thread also with a request pending (the code before)
import sys

name, src, out = sys.argv[1], open(sys.argv[2]).read(), sys.argv[3]


def rep(s, old, new):
    assert s.count(old) == 1, (name, old)
    return s.replace(old, new)


FINALLY = """                    synchronized (evictorLock) {
                        running = false;
                        evictorLock.notifyAll();
                    }"""
if name == 'norecheck':
    s = rep(src, FINALLY, """                    synchronized (evictorLock) {
                        running = false;
                        evictorLock.notifyAll();
                        if (in.isActive()) {
                            try {
                                evictorLock.wait();     // BROKEN: no check of wanted first
                            } catch (InterruptedException e) {
                                // as a wake-up
                            }
                        }
                    }""")
elif name == 'lateclear':
    s = rep(src, """                    wanted = false;
                    running = true;""", """                    running = true;""")
    s = rep(s, FINALLY, """                    synchronized (evictorLock) {
                        wanted = false;         // BROKEN: after the batches
                        running = false;
                        evictorLock.notifyAll();
                    }""")
elif name == 'oldinterrupt':
    s = rep(src, """                            if (!wanted) {      // not with a request pending (wake, 3)
                                evictor = null;
                                return;
                            }""", """                            evictor = null;     // BROKEN: also with a request pending
                            return;""")
else:
    raise SystemExit('unknown variant ' + name)
open(out, 'w').write(s)
