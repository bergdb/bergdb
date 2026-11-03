#!/bin/sh
# build.sh's one call of unzip, "unzip -q -o ZIP -x 'META-INF/*'", done by python3, for s1,
# which has no unzip (bergdb 016-08, section 4.3). Installed as /opt/bergdb-bench/016/bin/unzip
# and put first on the PATH of the runs there. Extracts ZIP ($3) into the current directory,
# without META-INF/, overwriting.
exec python3 -I -c '
import sys, zipfile
z = zipfile.ZipFile(sys.argv[1])
for n in z.namelist():
    if not n.startswith("META-INF/"):
        z.extract(n)
' "$3"
