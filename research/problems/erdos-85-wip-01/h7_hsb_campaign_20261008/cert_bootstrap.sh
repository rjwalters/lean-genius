#!/bin/bash
# Erdős 85 H7 t=0 hsb3 certificate campaign: node bootstrap (check-then-discard). claude, 2026-10-08.
# Modelled on ../h1_cert_full_20261001/cert_bootstrap.sh. Runs as root from a pinned sparse checkout on
# an AL2023 arm64 spot host. No Lean image and no emitter on the node: the CNF inputs are the pinned
# freight (inputs.json sha256 = E85_INPUTS_SHA; every file re-hashed by h7_common.Cube before use).
# Pinned CaDiCaL 3.0.1 from the verdict freight and the approved cake_lpr binary from this campaign's
# freight (both hash-checked; nothing is compiled on the node),
# preflight of solver + checker (incl. a must-REJECT case), S3 claim self-test, then cert_worker.py.
# A bootstrap failure uploads the log and powers off.
set -u
B=2am-erdos85-certs; VP=sat49/verdict-only-20260921; PP=sat49/h7hsb-20261008
E85_LIFETIME=${E85_LIFETIME:-100800}
E85_INPUTS_SHA=${E85_INPUTS_SHA:?inputs.json sha required}
E85_MANIFEST_SHA=${E85_MANIFEST_SHA:?manifest sha required}
E85_MANIFEST_KEY=${E85_MANIFEST_KEY:-}
E85_HEAP_MB=${E85_HEAP_MB:-2000}
E85_CAP=${E85_CAP:-3600}
E85_ONLY=${E85_ONLY:-}
E85_MAX_BATCHES=${E85_MAX_BATCHES:-0}
CAKE_LPR_SHA=4d47ffdd19fc6a80e24025f8c5d27d89c4309c9931bdad6d389d87e35be5464b   # = h7_common.CAKE_LPR_SHA256
HERE=$(cd "$(dirname "$0")" && pwd); REPO=$(git -C "$HERE" rev-parse --show-toplevel)
LOG=/var/log/e85-bootstrap.log; exec >> $LOG 2>&1
export AWS_DEFAULT_REGION=us-east-1
TOKEN=$(curl -s -X PUT http://169.254.169.254/latest/api/token -H 'X-aws-ec2-metadata-token-ttl-seconds: 21600')
IID=$(curl -s -H "X-aws-ec2-metadata-token: $TOKEN" http://169.254.169.254/latest/meta-data/instance-id)
ITYPE=$(curl -s -H "X-aws-ec2-metadata-token: $TOKEN" http://169.254.169.254/latest/meta-data/instance-type)
AWS0=$(command -v aws)
fail() { echo "BOOTSTRAP-FAIL: $*"; $AWS0 s3 cp --only-show-errors $LOG s3://$B/$PP/nodes/$IID/bootstrap-FAILED.log; /usr/sbin/poweroff; exit 1; }
HEAD=$(git -C $REPO rev-parse HEAD)
echo "$(date -u +%FT%TZ) h7hsb bootstrap start iid=$IID type=$ITYPE head=$HEAD inputs=$E85_INPUTS_SHA manifest=$E85_MANIFEST_SHA only=$E85_ONLY"
systemd-run --on-active=$E85_LIFETIME --unit=e85-lifetime /usr/sbin/poweroff   # hard stop, independent of the worker
for try in 1 2 3 4 5; do dnf -y install python3.12 zstd tar unzip git && break; sleep 30; done
command -v python3.12 >/dev/null && command -v zstd >/dev/null || fail "package install"
( cd /tmp && curl -fsSL -o awscliv2.zip https://awscli.amazonaws.com/awscli-exe-linux-aarch64.zip && unzip -q -o awscliv2.zip && ./aws/install --update -i /opt/aws-cli -b /usr/local/bin ) || fail "awscli install"
AWS=/usr/local/bin/aws; $AWS --version || fail "awscli run"
mkdir -p /scratch/freight /scratch/out /scratch/inputs /dev/shm/h7camp
# Pinned CaDiCaL (verdict-pass freight, verified by hash).
$AWS s3 cp --only-show-errors s3://$B/$VP/freight/bin/solvers.sha256 /scratch/freight/solvers.sha256 && $AWS s3 cp --only-show-errors s3://$B/$VP/freight/bin/cadical /usr/local/bin/cadical || fail "cadical download"
chmod 755 /usr/local/bin/cadical; ( cd /usr/local/bin && grep ' cadical$' /scratch/freight/solvers.sha256 | sha256sum -c ) || fail "cadical sha mismatch"
[ "$(sha256sum /usr/local/bin/cadical | cut -d' ' -f1)" = "fd601b827c2f6e72c255dd27d6bfa9d7f982414181195fe3ea07ec81385772a2" ] || fail "cadical is not the pinned 3.0.1 build"
[ "$(/usr/local/bin/cadical --version)" = "3.0.1" ] || fail "cadical version"
# cake_lpr: the ONE approved checker binary (h7_common.CAKE_LPR_SHA256), shipped as freight. It is the
# Linux arm64 build of tanyongkiam/cake_lpr @ a36874a8 (cake_lpr_arm8.S sha256 95b64883...f00c) used for
# the cost sample and the cover receipts. Nodes never rebuild it: a locally linked checker would have an
# unreviewed hash, and collect_receipts.py rejects every receipt whose checker hash is not the approved one.
$AWS s3 cp --only-show-errors s3://$B/$PP/freight/cake_lpr /usr/local/bin/cake_lpr || fail "cake_lpr download"
chmod 755 /usr/local/bin/cake_lpr
[ "$(sha256sum /usr/local/bin/cake_lpr | cut -d' ' -f1)" = "$CAKE_LPR_SHA" ] || fail "cake_lpr is not the approved build"
( sha256sum /usr/local/bin/cake_lpr /usr/local/bin/cadical; uname -a; cat /etc/os-release | head -2 ) > /scratch/freight/tools.build.txt
# Preflight: solver proves a tiny UNSAT CNF; checker VERIFIES its proof and REJECTS a corrupted one.
# cake_lpr exits 0 even when a check fails: only the stdout line `s VERIFIED UNSAT` counts.
printf 'p cnf 2 4\n1 2 0\n-1 2 0\n1 -2 0\n-1 -2 0\n' > /scratch/freight/unsat.cnf
/usr/local/bin/cadical --lrat=true --binary=true /scratch/freight/unsat.cnf /scratch/freight/unsat.lrat | grep -qx 's UNSATISFIABLE' || fail "cadical preflight"
/usr/local/bin/cake_lpr /scratch/freight/unsat.cnf /scratch/freight/unsat.lrat | grep -qx 's VERIFIED UNSAT' || fail "cake_lpr preflight (accept)"
head -c 3 /scratch/freight/unsat.lrat > /scratch/freight/bad.lrat
if /usr/local/bin/cake_lpr /scratch/freight/unsat.cnf /scratch/freight/bad.lrat | grep -q 'VERIFIED'; then fail "cake_lpr preflight: accepted a truncated proof"; fi
# Freight: pinned inputs (canonical body, per-cube units / hsb / cover, inputs.json).
$AWS s3 cp --only-show-errors s3://$B/$PP/freight/h7-inputs.tar.zst /scratch/freight/ && zstd -dc /scratch/freight/h7-inputs.tar.zst | tar -C /scratch/inputs -xf - || fail "inputs freight"
[ "$(sha256sum /scratch/inputs/inputs.json | cut -d' ' -f1)" = "$E85_INPUTS_SHA" ] || fail "inputs.json sha mismatch"
MANIFEST_ARGS=()
if [ -n "$E85_MANIFEST_KEY" ]; then
  $AWS s3 cp --only-show-errors s3://$B/$PP/$E85_MANIFEST_KEY /scratch/freight/manifest.jsonl || fail "manifest download"
  MANIFEST_ARGS=(--manifest /scratch/freight/manifest.jsonl)
fi
# S3 claim primitive self-test (conditional put must be exclusive).
echo $IID > /scratch/freight/node
$AWS s3api put-object --bucket $B --key $PP/selftest/$IID --body /scratch/freight/node --if-none-match '*' >/dev/null || fail "selftest first put"
if $AWS s3api put-object --bucket $B --key $PP/selftest/$IID --body /scratch/freight/node --if-none-match '*' >/dev/null 2>/scratch/freight/put2.err; then fail "conditional put is not exclusive"; fi
grep -q PreconditionFailed /scratch/freight/put2.err || fail "unexpected conditional put error"
$AWS s3 cp --only-show-errors /scratch/freight/tools.build.txt s3://$B/$PP/nodes/$IID/tools.build.txt
echo "$(date -u +%FT%TZ) bootstrap ok"; $AWS s3 cp --only-show-errors $LOG s3://$B/$PP/nodes/$IID/bootstrap.log
( while true; do
    { date -u +%FT%TZ; uptime; free -g; df -h /dev/shm | tail -1; ps -eo pid,ppid,stat,etimes,pcpu,rss,comm,args --sort=-pcpu | head -40 | cut -c1-200; } > /scratch/out/ps.txt 2>&1
    for f in /var/log/e85-h7hsb.err /var/log/e85-h7hsb.log /scratch/out/ps.txt; do [ -f $f ] && $AWS s3 cp --only-show-errors $f s3://$B/$PP/nodes/$IID/$(basename $f) >/dev/null 2>&1; done
    sleep 60
  done ) &
UPLOADER=$!
MEM_GB=$(awk '/MemTotal/{printf "%d", $2/1048576}' /proc/meminfo)
# Slots: one per vCPU, but never more than the memory budget allows. The checker heap is fixed for
# the whole run (no in-batch escalation), so slots x (heap + 1.5 GB) is the true peak.
BUDGET_GB=$((MEM_GB - 8))
FIT=$(( BUDGET_GB * 1000 / (E85_HEAP_MB + 1500) ))
SLOTS=${E85_SLOTS:-$(nproc)}; [ "$SLOTS" -gt "$FIT" ] && SLOTS=$FIT
[ "$SLOTS" -ge 1 ] || fail "no slot fits: heap $E85_HEAP_MB MB on $MEM_GB GB"
export PYTHONFAULTHANDLER=1 PYTHONUNBUFFERED=1
CMD=(python3.12 -B $HERE/cert_worker.py --inputs /scratch/inputs --inputs-sha256 $E85_INPUTS_SHA --manifest-sha256 $E85_MANIFEST_SHA
  "${MANIFEST_ARGS[@]}" --iid $IID --itype $ITYPE --head $HEAD --slots "$SLOTS" --mem-gb $BUDGET_GB --heap-mb $E85_HEAP_MB
  --lifetime $E85_LIFETIME --cap $E85_CAP --max-batches $E85_MAX_BATCHES --no-poweroff)
[ -n "$E85_ONLY" ] && CMD+=(--only "$E85_ONLY")
echo "$(date -u +%FT%TZ) worker command: ${CMD[*]}"
"${CMD[@]}" 2>> /var/log/e85-h7hsb.err
RC=$?; echo "$(date -u +%FT%TZ) worker exited rc=$RC"; kill $UPLOADER 2>/dev/null
for f in /var/log/e85-h7hsb.err /var/log/e85-h7hsb.log /scratch/out/status.json; do [ -f $f ] && $AWS s3 cp --only-show-errors $f s3://$B/$PP/nodes/$IID/$(basename $f); done
$AWS s3 cp --only-show-errors $LOG s3://$B/$PP/nodes/$IID/bootstrap.log
sleep 300; /usr/sbin/poweroff
