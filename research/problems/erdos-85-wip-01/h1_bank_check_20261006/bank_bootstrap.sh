#!/bin/bash
# Erdős 85 H1 certificate-BANK re-validation node bootstrap (2026-10-06): stream each 2026-08 bank proof
# from S3 into cake_lpr against the pinned-emitter CNF. Adapted from ../h1_cert_full_20261001/cert_bootstrap.sh.
# Runs as root from a pinned checkout on an AL2023 arm64 spot host (r7g). Reuses the verdict pass's
# verified freight (pinned Lean image, v2cnf emitter, CaDiCaL 3.0.1 build, all hash-checked), builds
# cake_lpr from its pinned commit, preflights solver + checker (incl. a must-REJECT case), self-tests
# the S3 claim primitive, then runs cert_worker.py. A bootstrap failure uploads the log and powers off.
set -u
B=2am-erdos85-certs; PP=sat49/bankcheck-20261006
E85_LIFETIME=${E85_LIFETIME:-43200}   # 12 h: checking only, no solving
E85_MANIFEST_SHA=${E85_MANIFEST_SHA:?manifest sha required}
E85_HEAP_MB=${E85_HEAP_MB:-8000}
E85_CAP=${E85_CAP:-86400}   # CaDiCaL -t seconds; the 19.7 h census row needs > 24 h with proof logging
E85_ONLY=${E85_ONLY:-}
CAKE_COMMIT=a36874a8b750b43fe4b385b8ddbf5b033e46a3fa
IMAGE_ID=sha256:a5ca6c4e3328a1832d5f9b814ab7c1e35616903b3956341962a5b1a96fb6dff6
EMITTER_SHA=4bd9604c6d670ad65a8ca332a26dbf35132418634a3b0678c177c8b2cfff4bf6
EMITTER=/scratch/freight/v2cnf
HERE=$(cd "$(dirname "$0")" && pwd); REPO=$(git -C "$HERE" rev-parse --show-toplevel)
LOG=/var/log/e85-bootstrap.log; exec >> $LOG 2>&1
export AWS_DEFAULT_REGION=us-east-1
TOKEN=$(curl -s -X PUT http://169.254.169.254/latest/api/token -H 'X-aws-ec2-metadata-token-ttl-seconds: 21600')
IID=$(curl -s -H "X-aws-ec2-metadata-token: $TOKEN" http://169.254.169.254/latest/meta-data/instance-id)
ITYPE=$(curl -s -H "X-aws-ec2-metadata-token: $TOKEN" http://169.254.169.254/latest/meta-data/instance-type)
AWS0=$(command -v aws)
fail() { echo "BOOTSTRAP-FAIL: $*"; $AWS0 s3 cp --only-show-errors $LOG s3://$B/$PP/nodes/$IID/bootstrap-FAILED.log; /usr/sbin/poweroff; exit 1; }
echo "$(date -u +%FT%TZ) cert bootstrap start iid=$IID type=$ITYPE head=$(git -C $REPO rev-parse HEAD) manifest=$E85_MANIFEST_SHA only=$E85_ONLY"
systemd-run --on-active=$E85_LIFETIME --unit=e85-lifetime /usr/sbin/poweroff
for try in 1 2 3 4 5; do dnf -y install docker python3.12 zstd gcc make tar unzip git && break; sleep 30; done
command -v docker >/dev/null && command -v python3.12 >/dev/null && command -v zstd >/dev/null && command -v gcc >/dev/null || fail "package install"
( cd /tmp && curl -fsSL -o awscliv2.zip https://awscli.amazonaws.com/awscli-exe-linux-aarch64.zip && unzip -q -o awscliv2.zip && ./aws/install --update -i /opt/aws-cli -b /usr/local/bin ) || fail "awscli install"
AWS=/usr/local/bin/aws; $AWS --version || fail "awscli run"
mkdir -p /etc/docker && echo '{"features":{"containerd-snapshotter":true}}' > /etc/docker/daemon.json
systemctl enable --now docker || fail "docker start"
mkdir -p /scratch/freight /scratch/cert /scratch/out
# Pinned image + emitter: this pass's freight, verified by hash.
$AWS s3 cp --only-show-errors s3://$B/$PP/freight/lean4-arm64-v4.31.0.oci.tar.zst /scratch/freight/ || fail "image download"
zstd -dc /scratch/freight/lean4-arm64-v4.31.0.oci.tar.zst | docker load || fail "docker load"; rm -f /scratch/freight/lean4-arm64-v4.31.0.oci.tar.zst
[ "$(docker image inspect $IMAGE_ID --format '{{.Id}}' 2>&1)" = "$IMAGE_ID" ] || fail "image identity mismatch"
$AWS s3 cp --only-show-errors s3://$B/$PP/freight/v2cnf.zst /scratch/freight/ && zstd -dc /scratch/freight/v2cnf.zst > $EMITTER && chmod 755 $EMITTER || fail "emitter download"
[ "$(sha256sum $EMITTER | cut -d' ' -f1)" = "$EMITTER_SHA" ] || fail "emitter sha mismatch"
# cake_lpr: CakeML-compiled arm8 assembly from the pinned commit, linked locally.
( cd /scratch && git clone -q https://github.com/tanyongkiam/cake_lpr && cd cake_lpr && git checkout -q $CAKE_COMMIT && gcc basis_ffi.c cake_lpr_arm8.S -o cake_lpr -std=c99 ) || fail "cake_lpr build"
install -m 755 /scratch/cake_lpr/cake_lpr /usr/local/bin/cake_lpr
( sha256sum /scratch/cake_lpr/cake_lpr_arm8.S /usr/local/bin/cake_lpr; git -C /scratch/cake_lpr rev-parse HEAD; gcc --version | head -1; uname -a ) > /scratch/freight/cake_lpr.build.txt
# Preflight: checker VERIFIES a hand-written LRAT proof and REJECTS a corrupted one.
printf 'p cnf 2 4\n1 2 0\n-1 2 0\n1 -2 0\n-1 -2 0\n' > /scratch/freight/unsat.cnf
printf '5 1 0 1 3 0\n6 -1 0 2 4 0\n7 0 5 6 0\n' > /scratch/freight/unsat.lrat
/usr/local/bin/cake_lpr /scratch/freight/unsat.cnf /scratch/freight/unsat.lrat | grep -qx 's VERIFIED UNSAT' || fail "cake_lpr preflight (accept)"
printf '5 1 0 1 3 0\n7 0 5 0\n' > /scratch/freight/bad.lrat
if /usr/local/bin/cake_lpr /scratch/freight/unsat.cnf /scratch/freight/bad.lrat | grep -q 'VERIFIED'; then fail "cake_lpr preflight: accepted a truncated proof"; fi
# Freight: manifest + tables.
mkdir -p /scratch/freight/bank && $AWS s3 cp --only-show-errors s3://$B/$PP/freight/bank_manifest.jsonl /scratch/freight/bank/manifest.jsonl || fail "bank manifest"
[ "$(sha256sum /scratch/freight/bank/manifest.jsonl | cut -d' ' -f1)" = "$E85_MANIFEST_SHA" ] || fail "manifest sha mismatch"
INVENTORY=$REPO/proofs/Proofs/Certificates/h1_orbit_inventory.compact
[ -s "$INVENTORY" ] || fail "orbit inventory missing from checkout"
# S3 claim primitive self-test.
echo $IID > /scratch/freight/node
$AWS s3api put-object --bucket $B --key $PP/selftest/$IID --body /scratch/freight/node --if-none-match '*' >/dev/null || fail "selftest first put"
if $AWS s3api put-object --bucket $B --key $PP/selftest/$IID --body /scratch/freight/node --if-none-match '*' >/dev/null 2>/scratch/freight/put2.err; then fail "conditional put is not exclusive"; fi
grep -q PreconditionFailed /scratch/freight/put2.err || fail "unexpected conditional put error"
$AWS s3 cp --only-show-errors /scratch/freight/cake_lpr.build.txt s3://$B/$PP/nodes/$IID/cake_lpr.build.txt
echo "$(date -u +%FT%TZ) bootstrap ok"; $AWS s3 cp --only-show-errors $LOG s3://$B/$PP/nodes/$IID/bootstrap.log
( while true; do
    { date -u +%FT%TZ; uptime; free -g; df -h /scratch | tail -1; ps -eo pid,ppid,stat,etimes,pcpu,rss,comm,args --sort=-pcpu | head -40 | cut -c1-200; } > /scratch/out/ps.txt 2>&1
    for f in /var/log/e85-cert.err /var/log/e85-cert.log /scratch/out/ps.txt; do [ -f $f ] && $AWS s3 cp --only-show-errors $f s3://$B/$PP/nodes/$IID/$(basename $f) >/dev/null 2>&1; done
    sleep 60
  done ) &
UPLOADER=$!
MEM_GB=$(awk '/MemTotal/{printf "%d", $2/1048576}' /proc/meminfo)
export PYTHONFAULTHANDLER=1 PYTHONUNBUFFERED=1
CMD=(python3.12 -B $HERE/bank_worker.py --repo $REPO --freight /scratch/freight/bank --manifest-sha256 $E85_MANIFEST_SHA --inventory $INVENTORY
  --iid $IID --itype $ITYPE --slots "${E85_SLOTS:-$(nproc)}" --mem-budget-gb $((MEM_GB > 48 ? MEM_GB - 24 : MEM_GB - 8)) --heap-mb $E85_HEAP_MB
  --lifetime $E85_LIFETIME --v2cnf $EMITTER --no-poweroff)
[ -n "$E85_ONLY" ] && CMD+=(--only "$E85_ONLY")
echo "$(date -u +%FT%TZ) worker command: ${CMD[*]}"
"${CMD[@]}" 2>> /var/log/e85-cert.err
RC=$?; echo "$(date -u +%FT%TZ) worker exited rc=$RC"; kill $UPLOADER 2>/dev/null
for f in /var/log/e85-cert.err /var/log/e85-cert.log /scratch/out/status.json; do [ -f $f ] && $AWS s3 cp --only-show-errors $f s3://$B/$PP/nodes/$IID/$(basename $f); done
$AWS s3 cp --only-show-errors $LOG s3://$B/$PP/nodes/$IID/bootstrap.log
sleep 600; /usr/sbin/poweroff
