#!/bin/bash
# Prepare an Amazon Linux 2023 arm64 instance as the erdos85 Lean builder, then snapshot it
# as the private AMI `erdos85-lean-builder-<date>` (see build_ami.sh, which drives this).
#
# Usage (as root, on the instance):
#   E85_REF=erdos85/h7t0-formal-20261007 \
#   E85_WARM_MODULES="Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalCnfSatisfaction" \
#   bash ami_setup.sh
#
# Needs the instance role Erdos85LeanBuilder (S3 read on lean-builder/ and the checker-kit image).
set -euo pipefail
E85_REF=${E85_REF:-erdos85/h7t0-formal-20261007}
E85_WARM_MODULES=${E85_WARM_MODULES:-Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalCnfSatisfaction}
E85_WARM_MEM_GB=${E85_WARM_MEM_GB:-100}
BUCKET=s3://2am-erdos85-certs
IMAGE_TAR=$BUCKET/public/erdos85-h1-checker-kit/bin/lean4-arm64-v4.31.0.oci.tar.zst
IMAGE_ID=sha256:a5ca6c4e3328a1832d5f9b814ab7c1e35616903b3956341962a5b1a96fb6dff6
ARTIFACTS=/Volumes/Stripe/lean-genius/artifacts
export AWS_DEFAULT_REGION=us-east-1
U=ec2-user

echo "== packages"
dnf -y -q install docker git python3.12 zstd tmux bc jq rsync util-linux-user >/dev/null
mkdir -p /etc/docker && echo '{"features":{"containerd-snapshotter":true},"log-driver":"local"}' > /etc/docker/daemon.json
systemctl enable --now docker
usermod -aG docker $U

echo "== pinned Lean image"
if ! docker image inspect lean4-arm64:v4.31.0 >/dev/null 2>&1; then
    aws s3 cp --only-show-errors --request-payer requester "$IMAGE_TAR" - | zstd -dc | docker load
fi
[ "$(docker image inspect "$IMAGE_ID" --format '{{.Id}}')" = "$IMAGE_ID" ]
docker tag "$IMAGE_ID" erdos85/lean4-arm64:v4.31.0-pinned-a5ca6c4e
docker tag "$IMAGE_ID" lean4-arm64:v4.31.0          # the name proofs/scripts/docker-build.sh expects

echo "== repo clone /opt/lean-genius ($E85_REF)"
if [ ! -d /opt/lean-genius/.git ]; then
    git clone -q --filter=blob:none --no-checkout https://github.com/rjwalters/lean-genius /opt/lean-genius
fi
git -C /opt/lean-genius fetch -q origin "+refs/heads/$E85_REF:refs/remotes/origin/$E85_REF"
git -C /opt/lean-genius checkout -q -f --detach "origin/$E85_REF"
chown -R $U:$U /opt/lean-genius

echo "== tooling /opt/e85/bin"
LB=/opt/lean-genius/research/problems/erdos-85-wip-01/lean_builder
mkdir -p /opt/e85/bin /opt/e85/wt /opt/e85/jobs /opt/e85/locks
install -m 755 $LB/e85-host.sh /opt/e85/bin/e85-host
install -m 755 /opt/lean-genius/proofs/scripts/docker-build.sh /opt/e85/bin/docker-build.sh
install -m 755 $LB/e85-watchdog.sh /usr/local/sbin/e85-watchdog
ln -sf /opt/e85/bin/e85-host /usr/local/bin/e85-host
chown -R $U:$U /opt/e85
[ -e /etc/e85-builder.conf ] || printf 'IDLE_MINUTES=60\nWALL_HOURS=10\n' > /etc/e85-builder.conf
cat > /etc/systemd/system/e85-watchdog.service <<'UNIT'
[Unit]
Description=erdos85 builder idle / daily-wall watchdog
[Service]
Type=oneshot
ExecStart=/usr/local/sbin/e85-watchdog
UNIT
cat > /etc/systemd/system/e85-watchdog.timer <<'UNIT'
[Unit]
Description=run e85-watchdog every minute
[Timer]
OnBootSec=2min
OnUnitActiveSec=1min
AccuracySec=10s
[Install]
WantedBy=timers.target
UNIT
systemctl daemon-reload
# Enabled for the NEXT boot only: the watchdog must not stop the instance mid-setup.
systemctl enable e85-watchdog.timer

echo "== include_str artifacts -> $ARTIFACTS"
mkdir -p "$ARTIFACTS"
aws s3 sync --only-show-errors "$BUCKET/lean-builder/artifacts/" "$ARTIFACTS/"
chown -R $U:$U /Volumes/Stripe
du -sh "$ARTIFACTS"

echo "== warm Mathlib packages + base build volume"
docker volume inspect lean-mathlib-cache >/dev/null 2>&1 || docker volume create lean-mathlib-cache >/dev/null
docker volume inspect lean-mathlib-packages >/dev/null 2>&1 || docker volume create lean-mathlib-packages >/dev/null
# E85_VOLUME=lean-mathlib-cache builds straight into the base volume that seeds every
# per-branch volume; the first module also runs `lake exe cache get` (--cache).
cache_flag=--cache
for m in $E85_WARM_MODULES; do
    sudo -u $U E85_VOLUME=lean-mathlib-cache /opt/e85/bin/e85-host build "$E85_REF" "$m" \
        --mem "$E85_WARM_MEM_GB" --timeout 6h $cache_flag
    cache_flag=
done

echo "== clean for imaging"
rm -rf /opt/e85/jobs/* /var/lib/e85-watchdog
git -C /opt/lean-genius worktree list
docker system df
echo "e85 lean builder ready"
