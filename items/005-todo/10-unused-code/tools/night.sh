#!/bin/sh
# Runs the night tests (bergdb.dev.Night) of a clone, at most LIMIT seconds.
R=$1; OUT=$2; LIMIT=${3:-1800}
cd "$R/java" || exit 1
start=$(date +%s)
java -ea -cp build/bergdb.jar bergdb.dev.Night > "$OUT" 2>&1 &
pid=$!
while kill -0 $pid 2>/dev/null; do
    if [ $(( $(date +%s) - start )) -gt "$LIMIT" ]; then
        kill $pid; echo "night: stopped after $LIMIT s"; exit 2
    fi
    sleep 5
done
wait $pid
echo "night: exit $?, $(( $(date +%s) - start )) s: $(tail -1 "$OUT")"
