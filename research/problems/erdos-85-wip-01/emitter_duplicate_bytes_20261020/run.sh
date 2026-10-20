#!/bin/sh
# Reproduces the 2026-08-14 "duplicated trailing bytes" symptom (no Mathlib; ~150 MB RSS).
set -eu
cd "$(dirname "$0")"
lake build
B=.lake/build/bin/emitbug
N=613276
"$B" whole "$N" > ref.cnf
"$B" chunk "$N" > chunk.cnf
cmp ref.cnf chunk.cnf && echo "single process: whole-string == chunked ($(wc -c < ref.cnf) bytes)"
# Race: a slow writer holding 340 buffered bytes, then a second writer, both redirected to one file.
rm -f race.cnf
"$B" late "$N" 3000 > race.cnf &
"$B" delay "$N" 4000 > race.cnf
wait
ref=$(wc -c < ref.cnf); got=$(wc -c < race.cnf)
echo "race: ref=$ref race=$got extra=$((got-ref))"
cmp -n "$ref" ref.cnf race.cnf && echo "race: first $ref bytes equal the reference"
tail -c 340 ref.cnf > a.tail; tail -c 340 race.cnf > b.tail
cmp a.tail b.tail && echo "race: the extra 340 bytes repeat the reference's last 340 bytes"
