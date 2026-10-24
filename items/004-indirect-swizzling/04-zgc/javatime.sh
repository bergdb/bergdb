#!/bin/sh
# java under /usr/bin/time -l, for 004-04: the process's CPU time and peak memory go to
# TIMEDIR/NAME.time, NAME from -Dsb.label= (ScaleBench) or -Dsoak.out= (Soak); other calls
# (java -version) run plainly. Needs REALJAVA (the java to run) and TIMEDIR.
name=
for a in "$@"; do
    case $a in
    -Dsb.label=*) name=${a#-Dsb.label=} ;;
    -Dsoak.out=*) name=$(basename "${a#-Dsoak.out=}") ;;
    esac
done
[ -n "$name" ] || exec "$REALJAVA" "$@"
exec /usr/bin/time -l -o "$TIMEDIR/$name.time" "$REALJAVA" "$@"
