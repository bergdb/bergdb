#!/usr/bin/env python3
"""Waits until FILE contains TEXT, at most SECONDS (default 570); prints done or still running."""
import sys, time
f, text = sys.argv[1], sys.argv[2]
limit = float(sys.argv[3]) if len(sys.argv) > 3 else 570
t0 = time.time()
while time.time() - t0 < limit:
    if text in open(f).read():
        print('done: ' + text)
        break
    time.sleep(10)
else:
    print('still running: ' + text)
