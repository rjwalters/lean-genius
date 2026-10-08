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
  "$CAD" -q -t "$cap" "$cnf" > "$log" 2>&1; local rc=$?
  local res=UNKNOWN; [[ $rc == 20 ]] && res=UNSAT; [[ $rc == 10 ]] && res=SAT
  echo -e "$name\tcap=$cap\t$res\t$(( $(date +%s) - t0 ))s" | tee -a "$W/out/results.tsv"
}
case $1 in
  gen) shift; gen "$@" ;;
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
