#!/bin/bash
# Plain (no-proof) CaDiCaL difficulty probe, at most 2 concurrent cells.
# usage: plain_probe.sh <label> <cnf> [cap_seconds=1800]
# Uses `cadical -t` so the host memguard (pkill -f 'cadical -t') can stop it.
set -u
OUT=/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/h35-probe-20261007/plain
mkdir -p "$OUT" 2>/dev/null || true
label=$1; cnf=$2; cap=${3:-1800}
log="$OUT/$label.cadical.log"
start=$(date +%s)
/opt/homebrew/bin/cadical -t "$cap" "$cnf" > "$log" 2>&1 < /dev/null
rc=$?
end=$(date +%s)
sha=$(shasum -a 256 "$cnf" | cut -d' ' -f1)
res=$(grep -m1 -E '^(s |c UNKNOWN)' "$log" | sed 's/^[sc] //')
printf '{"label":"%s","cnf":"%s","cnf_sha256":"%s","cap_s":%s,"rc":%s,"result":"%s","wall_s":%s,"cadical":"%s"}\n' \
  "$label" "$cnf" "$sha" "$cap" "$rc" "${res:-NONE}" "$((end-start))" "$(/opt/homebrew/bin/cadical --version)" >> "$OUT/plain_results.jsonl" || true
