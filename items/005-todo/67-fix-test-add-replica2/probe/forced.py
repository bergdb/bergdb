"""bergdb 005-67. Makes the instrumented copy: adds three sleeps, each set by a system
property in milliseconds (0, the default, changes nothing), to a copy of java/:

  r67.replicaFlushDelay  BufferedStream.flushToStream sleeps before it writes, for a
                         buffer under 10,000 bytes only (the tests' replicas have 1,000):
                         a replica's buffer is written late, as on a busy machine.
  r67.afterAppend        StorageManager.append sleeps before it returns: the writer is
                         descheduled after its append.
  r67.syncPause          SynchingStorage.sync sleeps, with the write lock, after it has
                         read the main's and the replica's lengths.
  r67.closePause         BufferedStream.close sleeps after its wait for the buffer to
                         empty, before stop(), for a buffer under 10,000 bytes only: the
                         window of 2015's failure (Old2015.java, old2015.py).

Usage: python3 -I forced.py JAVA_DIR   (the copy's java/, changed in place)
"""
import sys

def patch(path, old, new):
    s = open(path).read()
    assert s.count(old) == 1, (path, old)
    open(path, 'w').write(s.replace(old, new))

def sleep(prop, cond='true'):
    return ('{ int r67 = Integer.getInteger("%s", 0); if (r67 > 0 && %s) '
            '{ try { Thread.sleep(r67); } catch (InterruptedException e) { '
            'Thread.currentThread().interrupt(); } } }' % (prop, cond))

java = sys.argv[1]
patch(java + '/src/bergdb/storage/BufferedStream.java',
      '    private void flushToStream() {\n',
      '    private void flushToStream() {\n        ' + sleep('r67.replicaFlushDelay', 'bufferCapacity < 10000')
      + '    // bergdb 005-67, instrumented copy\n')
patch(java + '/src/bergdb/storage/StorageManager.java',
      '        this.streamLength += length;\n',
      '        this.streamLength += length;\n        ' + sleep('r67.afterAppend')
      + '    // bergdb 005-67, instrumented copy\n')
patch(java + '/src/bergdb/storage/StorageManager.java',
      '                        diff = mainLength - replicaLength;\n',
      '                        diff = mainLength - replicaLength;\n                        '
      + sleep('r67.syncPause') + '    // bergdb 005-67, instrumented copy\n')
patch(java + '/src/bergdb/storage/BufferedStream.java',
      '            }\n        }\n\n        stop();\n',
      '            }\n        }\n\n        ' + sleep('r67.closePause', 'bufferCapacity < 10000')
      + '    // bergdb 005-67, instrumented copy\n        stop();\n')
print('instrumented', java)
