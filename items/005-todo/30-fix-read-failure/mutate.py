# bergdb 005-30: takes one part of the fix out of core/Db.java (see mutations.sh).
import sys
p, which = sys.argv[1], sys.argv[2]
s = open(p, encoding='utf-8').read()
def rep(a, b):
    global s
    assert s.count(a) == 1, (which, a[:100])
    s = s.replace(a, b)
if which == 'A':
    # A read that fails on the storage does not fail the database, as before.
    rep('return expired != e ? expired : failOnStorage(e, "A read");', 'return expired;')
if which == 'B':
    # getTrans() does not check the state.
    rep('        assertDbStateIsActive("getTrans");\n', '')
if which == 'C':
    # A sync that fails does not fail the database.
    rep('throw failOnStorage(new StreamIoException(e), "A sync");',
        'throw new StreamIoException(e);')
if which == 'D':
    # An interrupted sync is taken as a failure of the storage.
    rep('            } catch (InterruptedIOException e) {\n'
        '                // Not a failure of the storage (bergdb 005-30).\n'
        '                throw new StreamIoException(e);\n', '')
if which == 'E':
    # A read while the database is stopping gets a DbFailedException.
    rep('        if (before != DbState.ACTIVE && before != DbState.FAILED) {\n'
        '            return e;\n'
        '        }\n', '')
if which == 'F':
    # getTrans() fails the database on a format error too.
    rep('        } catch (StreamIoException e) {\n            if (isReadBelowCut(e)) {',
        '        } catch (StreamException e) {\n            if (isReadBelowCut(e)) {')
if which == 'G':
    # getTrans() fails the database on a read below the cut.
    rep('            if (isReadBelowCut(e)) {\n                LookupTimeNotAvailableException ex',
        '            if (false) {\n                LookupTimeNotAvailableException ex')
open(p, 'w', encoding='utf-8').write(s)
