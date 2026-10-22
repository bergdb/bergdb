import sys
p, which = sys.argv[1], sys.argv[2]
s = open(p).read()
def rep(a, b):
    global s
    assert s.count(a) == 1, (which, a[:100])
    s = s.replace(a, b)
END = """                dbClock.transactionEnd();
                
                stmRecordKeys(t);"""
TRY = """            try {
                putKvs();
"""
if which in ('A', 'B'):
    # transactionEnd() in a finally around putKvs(), as before 005-01.
    rep(END, """                
                stmRecordKeys(t);""")
    rep(TRY, """            try {
                try {
                    putKvs();
                } finally {
                    dbClock.transactionEnd();
                }
""")
if which == 'A':
    # And no fail-stop: exceptions pass as they are, the state stays ACTIVE.
    rep("""            } catch (Throwable e) {
                throw fail(t, e);
            }""", """            } finally {
            }""")
if which == 'C':
    # No state check under the lock.
    rep("""            assertDbStateIsActive("execute");
            
            // The end of the top node ordinals""", """            // The end of the top node ordinals""")
open(p, 'w').write(s)
