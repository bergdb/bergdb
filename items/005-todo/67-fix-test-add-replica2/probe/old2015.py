"""bergdb 005-67. Instruments the BufferedStream of 2015-07-23 (c08e4ce of the 2013 to 2017
history) for Old2015.java: two sleeps set by system properties in milliseconds (0, the
default, changes nothing), for a buffer under 10,000 bytes only (the test's replica):

  r67.closePause      close() sleeps after its wait for the buffer to empty, before
                      stop(): the window in which the consumer could wake.
  r67.betweenAppends  flushToStream() sleeps between the two appends of a flush that wraps
                      around the ring buffer.

Usage: python3 -I old2015.py BufferedStream.java   (changed in place)
"""
import sys

def sleep(prop):
    return ('{ int r67 = Integer.getInteger("%s", 0); if (r67 > 0 && bufferCapacity < 10000) '
            '{ try { Thread.sleep(r67); } catch (InterruptedException e) { } } }' % prop)

p = sys.argv[1]
s = open(p).read()
old1 = '                stream.append(buffer, index1, bufferCapacity - index1);\n'
assert s.count(old1) == 1
s = s.replace(old1, old1 + '                ' + sleep('r67.betweenAppends') + '\n')
old2 = '        }\n\n        stop();\n\n        stream.close();\n'
assert s.count(old2) == 1, 'close'
s = s.replace(old2, '        }\n\n        ' + sleep('r67.closePause') + '\n        stop();\n\n        stream.close();\n')
open(p, 'w').write(s)
print('instrumented', p)
