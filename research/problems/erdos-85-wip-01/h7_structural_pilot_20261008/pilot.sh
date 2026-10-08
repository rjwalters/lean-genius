#!/usr/bin/env bash
# Host-side driver (runs on the e85 builder in the branch worktree root).
#   pilot.sh gen  <root> <facts> <tag>          -> $W/cnf/<root>.<tag>.cnf (+ .json stats)
#   pilot.sh solve <cap_s> <tag-glob...>        -> parallel cadical (<= $PAR jobs), $W/out/*.log
#   pilot.sh batch <cap_s> <root:facts:tag>...  -> gen all (parallel) then solve all
# W=/home/ec2-user/h7pilot ; cadical = pinned 3.0.1 from the public checker kit.
set -uo pipefail
W=${W:-/home/ec2-user/h7pilot}
PAR=${PAR:-6}
HERE=$(cd "$(dirname "$0")" && pwd)
CAD=$W/bin/cadical
mkdir -p "$W/cnf" "$W/out"
gen() {
  local root=$1 facts=$2 tag=$3
  local out=$W/cnf/$root.$tag.cnf
  if [[ -s $out ]]; then echo "have $out"; return; fi
  python3 "$HERE/gen_pilot.py" --root "$root" --facts "$facts" --out "$out.tmp" > "$W/cnf/$root.$tag.json" \
    && mv "$out.tmp" "$out" && echo "gen $root.$tag $(head -c 300 "$W/cnf/$root.$tag.json")"
}
solve_one() {
  local cnf=$1 cap=$2 name; name=$(basename "$cnf" .cnf)
  local log=$W/out/$name.cap$cap.log
  local t0; t0=$(date +%s)
  "$CAD" -t "$cap" "$cnf" > "$log" 2>&1; local rc=$?
  local res=UNKNOWN; [[ $rc == 20 ]] && res=UNSAT; [[ $rc == 10 ]] && res=SAT
  echo -e "$name\tcap=$cap\t$res\t$(( $(date +%s) - t0 ))s\t$(grep -E "^c conflicts:" "$log" | awk '{print $3}')conf" | tee -a "$W/out/results.tsv"
}
cert_one() {  # solve with binary LRAT streamed through a FIFO into cake_lpr (never stored)
  local cnf=$1 cap=$2 name; name=$(basename "$cnf" .cnf)
  local fifo=/home/ec2-user/h7pilot/out/$name.fifo log=/home/ec2-user/h7pilot/out/$name.cert.log
  mkfifo "$fifo"
  local t0; t0=$(date +%s)
  /home/ec2-user/h7pilot/bin/cake_lpr "$cnf" "$fifo" --CML_HEAP_SIZE=4000 --CML_STACK_SIZE=1000 > "$log.cake" 2>&1 &
  local cpid=$!
  "$CAD" -t "$cap" --lrat=true --binary=true "$cnf" "$fifo" > "$log" 2>&1; local rc=$?
  wait $cpid; unlink "$fifo"
  local verdict; verdict=$(grep -c "^s VERIFIED UNSAT" "$log.cake")
  echo -e "$name\tcert cap=$cap\tcadical_rc=$rc\tcake_verified=$verdict\t$(( $(date +%s) - t0 ))s\tcnf_sha=$(sha256sum "$cnf" | cut -c1-16)" | tee -a "$W/out/cert.tsv"
}
case $1 in
  gen) shift; gen "$@" ;;
  leaves)  # leaves <root> <facts> <tag> <N> <cap_s> : sample N hsb leaf cubes and solve each
    shift; root=$1; facts=$2; tag=$3; n=$4; cap=$5; pd=${6:-0}; SOLVER=${7:-solve_one}
    out=$W/cnf/$root.$tag.cnf
    python3 "$HERE/gen_pilot.py" --root "$root" --facts "$facts" --out "$out" --sample-leaves "$n" --probe-depth "$pd" > "$W/cnf/$root.$tag.json" || exit 1
    cut -c1-400 "$W/cnf/$root.$tag.json"; echo
    export -f solve_one; export W CAD
    export -f cert_one
    ls "$out".leaf*.cnf | xargs -P "$PAR" -I{} bash -c "${SOLVER:-solve_one} {} $cap; unlink {}"
    ;;
  batch)
    shift; cap=$1; shift
    pids=(); n=0
    for spec in "$@"; do IFS=: read -r r f t <<<"$spec"; gen "$r" "$f" "$t" & n=$((n+1)); if (( n % PAR == 0 )); then wait; fi; done; wait
    export -f solve_one; export W CAD
    for spec in "$@"; do IFS=: read -r r f t <<<"$spec"; echo "$W/cnf/$r.$t.cnf"; done \
      | xargs -P "$PAR" -I{} bash -c "solve_one {} $cap"
    ;;
  *) echo "usage"; exit 2 ;;
esac
