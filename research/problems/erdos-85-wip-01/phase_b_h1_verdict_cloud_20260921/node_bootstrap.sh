#!/bin/bash
# Erdős 85 H1 verdict-only cloud node bootstrap (board goal #44). SINGLE-SEAT (claude, 2026-09-21).
# Runs as root from a pinned checkout of erdos85/integration on an AL2023 arm64 spot host.
# It installs Docker with the containerd image store, loads the pinned Lean image, installs the
# pinned emitter and the two solvers, self-tests the S3 claim primitive, then starts node_worker.py.
# The reviewed dispatcher, materializer and runner are executed UNCHANGED from the checkout.
# No proof logging, no certificates, no Lean build. A bootstrap failure uploads the log and powers off.
set -u
B=2am-erdos85-certs; P=sat49/verdict-only-20260921
# Pass selection (pass 1 defaults). The launch template's user data exports E85_* for later passes.
E85_PASS=${E85_PASS:-}; PP="$P${E85_PASS:+/$E85_PASS}"
CONFIG_COMMIT=${E85_CONFIG_COMMIT:-bf95b3937e894956d07f09b55401dc41ffa904a6}
E85_CONFIG=${E85_CONFIG:-research/problems/erdos-85-wip-01/phase_b_h1_verdict_20260916/config.draft.json}
E85_QUEUE=${E85_QUEUE:-queue-1137.ids}
E85_QUEUE_SHA=${E85_QUEUE_SHA:-d9e4548ff356dfbd23db82b09d6a02d9a1d348f7c9aa4378e5dc6e8bc9e6fe87}
E85_DIRECT=${E85_DIRECT:-0}
E85_LIFETIME=${E85_LIFETIME:-108000}   # seconds; pass 2 uses 144000 (40 h) because one row can take 24 h
IMAGE_ID=sha256:a5ca6c4e3328a1832d5f9b814ab7c1e35616903b3956341962a5b1a96fb6dff6
EMITTER_SHA=4bd9604c6d670ad65a8ca332a26dbf35132418634a3b0678c177c8b2cfff4bf6
EMITTER=/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/campaign-20260825.noindex/h1fleet/v3freight-rebuild-20260905/stage/freight/v2cnf
HERE=$(cd "$(dirname "$0")" && pwd); REPO=$(git -C "$HERE" rev-parse --show-toplevel)
LOG=/var/log/e85-bootstrap.log; exec >> $LOG 2>&1
export AWS_DEFAULT_REGION=us-east-1
TOKEN=$(curl -s -X PUT http://169.254.169.254/latest/api/token -H 'X-aws-ec2-metadata-token-ttl-seconds: 21600')
IID=$(curl -s -H "X-aws-ec2-metadata-token: $TOKEN" http://169.254.169.254/latest/meta-data/instance-id)
ITYPE=$(curl -s -H "X-aws-ec2-metadata-token: $TOKEN" http://169.254.169.254/latest/meta-data/instance-type)
AWS0=$(command -v aws)
fail() { echo "BOOTSTRAP-FAIL: $*"; $AWS0 s3 cp --only-show-errors $LOG s3://$B/$PP/nodes/$IID/bootstrap-FAILED.log; /usr/sbin/poweroff; exit 1; }
echo "$(date -u +%FT%TZ) bootstrap start iid=$IID type=$ITYPE head=$(git -C $REPO rev-parse HEAD) pass=${E85_PASS:-1} config=$E85_CONFIG@$CONFIG_COMMIT queue=$E85_QUEUE direct=$E85_DIRECT"
# Hard lifetime backstop. Instance-initiated power-off terminates the instance (launch template).
systemd-run --on-active=$E85_LIFETIME --unit=e85-lifetime /usr/sbin/poweroff
for try in 1 2 3 4 5; do dnf -y install docker python3.12 zstd gcc gcc-c++ make tar unzip && break; sleep 30; done
command -v docker >/dev/null && command -v python3.12 >/dev/null && command -v zstd >/dev/null || fail "package install"
# Latest AWS CLI v2: put-object --if-none-match is required for atomic claims.
( cd /tmp && curl -fsSL -o awscliv2.zip https://awscli.amazonaws.com/awscli-exe-linux-aarch64.zip && unzip -q -o awscliv2.zip && ./aws/install --update -i /opt/aws-cli -b /usr/local/bin ) || fail "awscli install"
AWS=/usr/local/bin/aws; $AWS --version || fail "awscli run"
mkdir -p /etc/docker && echo '{"features":{"containerd-snapshotter":true}}' > /etc/docker/daemon.json
systemctl enable --now docker || fail "docker start"
ln -sf "$(command -v docker)" /usr/local/bin/docker
docker info --format 'driver={{.Driver}} {{.DriverStatus}}'
mkdir -p /scratch/freight /scratch/runs /scratch/out
$AWS s3 cp --only-show-errors s3://$B/$P/freight/lean4-arm64-v4.31.0.oci.tar.zst /scratch/freight/ || fail "image download"
zstd -dc /scratch/freight/lean4-arm64-v4.31.0.oci.tar.zst | docker load || fail "docker load"
rm -f /scratch/freight/lean4-arm64-v4.31.0.oci.tar.zst
GOT=$(docker image inspect $IMAGE_ID --format '{{.Id}}' 2>&1)
[ "$GOT" = "$IMAGE_ID" ] || { docker images --digests --no-trunc; fail "image identity mismatch: $GOT"; }
mkdir -p "$(dirname $EMITTER)"
$AWS s3 cp --only-show-errors s3://$B/$P/freight/v2cnf.zst /scratch/freight/ && zstd -dc /scratch/freight/v2cnf.zst > $EMITTER && chmod 755 $EMITTER || fail "emitter download"
[ "$(sha256sum $EMITTER | cut -d' ' -f1)" = "$EMITTER_SHA" ] || fail "emitter sha mismatch"
# Solvers: one shared build for every cloud node. The first node builds and publishes; later nodes verify the published hashes.
if $AWS s3 cp --only-show-errors s3://$B/$P/freight/bin/solvers.sha256 /scratch/freight/solvers.sha256; then
  $AWS s3 cp --only-show-errors s3://$B/$P/freight/bin/kissat /usr/local/bin/kissat && $AWS s3 cp --only-show-errors s3://$B/$P/freight/bin/cadical /usr/local/bin/cadical || fail "solver download"
  chmod 755 /usr/local/bin/kissat /usr/local/bin/cadical
  ( cd /usr/local/bin && sha256sum -c /scratch/freight/solvers.sha256 ) || fail "solver sha mismatch"
else
  ( cd /scratch && git clone -q --depth 1 -b rel-4.0.4 https://github.com/arminbiere/kissat && cd kissat && ./configure && make -j"$(nproc)" ) || fail "kissat build"
  ( cd /scratch && git clone -q --depth 1 -b rel-3.0.1 https://github.com/arminbiere/cadical && cd cadical && ./configure && make -j"$(nproc)" ) || fail "cadical build"
  install -m 755 /scratch/kissat/build/kissat /usr/local/bin/kissat; install -m 755 /scratch/cadical/build/cadical /usr/local/bin/cadical
  ( cd /usr/local/bin && sha256sum kissat cadical > /scratch/freight/solvers.sha256 )
  ( git -C /scratch/kissat rev-parse HEAD; git -C /scratch/cadical rev-parse HEAD; gcc --version | head -1; uname -a ) > /scratch/freight/solvers.build.txt
  if $AWS s3api put-object --bucket $B --key $P/freight/bin/solvers.sha256 --body /scratch/freight/solvers.sha256 --if-none-match '*' >/dev/null 2>/scratch/freight/put.err; then
    $AWS s3 cp --only-show-errors /usr/local/bin/kissat s3://$B/$P/freight/bin/kissat; $AWS s3 cp --only-show-errors /usr/local/bin/cadical s3://$B/$P/freight/bin/cadical
    $AWS s3 cp --only-show-errors /scratch/freight/solvers.build.txt s3://$B/$P/freight/bin/solvers.build.txt
  else
    grep -q PreconditionFailed /scratch/freight/put.err || fail "solver publish: $(cat /scratch/freight/put.err)"
    sleep 90   # another node won the publish race; adopt its binaries
    $AWS s3 cp --only-show-errors s3://$B/$P/freight/bin/solvers.sha256 /scratch/freight/solvers.sha256 && $AWS s3 cp --only-show-errors s3://$B/$P/freight/bin/kissat /usr/local/bin/kissat && $AWS s3 cp --only-show-errors s3://$B/$P/freight/bin/cadical /usr/local/bin/cadical || fail "solver adopt"
    chmod 755 /usr/local/bin/kissat /usr/local/bin/cadical; ( cd /usr/local/bin && sha256sum -c /scratch/freight/solvers.sha256 ) || fail "adopted solver sha mismatch"
  fi
fi
[ "$(/usr/local/bin/kissat --version)" = "4.0.4" ] || fail "kissat version $(/usr/local/bin/kissat --version)"
[ "$(/usr/local/bin/cadical --version)" = "3.0.1" ] || fail "cadical version $(/usr/local/bin/cadical --version)"
printf 'p cnf 1 2\n1 0\n-1 0\n' > /scratch/freight/unsat.cnf
/usr/local/bin/kissat /scratch/freight/unsat.cnf | grep -qx 's UNSATISFIABLE' || fail "kissat preflight"
/usr/local/bin/cadical /scratch/freight/unsat.cnf | grep -qx 's UNSATISFIABLE' || fail "cadical preflight"
# S3 claim primitive self-test: a second conditional PUT of the same key must fail with PreconditionFailed.
echo $IID > /scratch/freight/node
$AWS s3api put-object --bucket $B --key $PP/selftest/$IID --body /scratch/freight/node --if-none-match '*' >/dev/null || fail "selftest first put"
if $AWS s3api put-object --bucket $B --key $PP/selftest/$IID --body /scratch/freight/node --if-none-match '*' >/dev/null 2>/scratch/freight/put2.err; then fail "conditional put is not exclusive"; fi
grep -q PreconditionFailed /scratch/freight/put2.err || fail "unexpected conditional put error: $(cat /scratch/freight/put2.err)"
# Prefetch every banked dependency blob once, single-threaded (partial clone), then a read-only dry run.
while read -r f; do git -C $REPO show $CONFIG_COMMIT:"$f" > /dev/null || fail "prefetch $f"; done < $HERE/captured-paths.txt
git -C $REPO show $CONFIG_COMMIT:research/problems/erdos-85-wip-01/sat49/dispatch_h1_residual_verdict_only.py > /dev/null || fail "prefetch wrapper"
( cd $REPO && python3.12 -B research/problems/erdos-85-wip-01/sat49/dispatch_h1_residual_verdict_only.py --config research/problems/erdos-85-wip-01/phase_b_h1_verdict_20260916/config.draft.json --workers 1 | cut -c1-200 | grep -q '"selected_cases": 1161' ) || fail "dry run census"
echo "$(date -u +%FT%TZ) bootstrap ok"; $AWS s3 cp --only-show-errors $LOG s3://$B/$PP/nodes/$IID/bootstrap.log
exec # Background evidence uploader: worker stderr/log, a process snapshot and disk state every 60 s,
# so a wedged or crashed worker can be diagnosed without host access.
( while true; do
    { date -u +%FT%TZ; uptime; df -h /scratch | tail -1; ps -eo pid,ppid,stat,etimes,pcpu,rss,comm,args --sort=-pcpu | head -40 | cut -c1-200; } > /scratch/out/ps.txt 2>&1
    for f in /var/log/e85-worker.err /var/log/e85-worker.log /scratch/out/ps.txt; do [ -f $f ] && $AWS s3 cp --only-show-errors $f s3://$B/$PP/nodes/$IID/$(basename $f) >/dev/null 2>&1; done
    sleep 60
  done ) &
UPLOADER=$!
export PYTHONFAULTHANDLER=1 PYTHONUNBUFFERED=1
python3.12 -B $HERE/node_worker.py --repo $REPO --iid $IID --itype $ITYPE --slots "${E85_SLOTS:-$(nproc)}"
