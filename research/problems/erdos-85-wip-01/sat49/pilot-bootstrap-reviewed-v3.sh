#!/usr/bin/env bash
set -euo pipefail
umask 077

BUCKET=2am-erdos85-certs
PREFIX=sat49/campaign-20260825/h1-replay
FREIGHT_PREFIX="$PREFIX/freight/pilot-4c7cbb5159"
ROOT=/opt/replay
AWS_ZIP_SHA=2b9d9305db94af64baee48106f54b6652ede5732494c0ba61ae305720ac72505
REPO_SHA=aa85aa8f3f4467ec18b7fbc42f6fb680d213e9bb9d995431fb90ffd7b3551597
OVERLAY_SHA=2c7f6868e86a6ace0eb3f451977a4d65bd4c333d4611a00001d91672b6d17460
IMAGE_ARCHIVE_SHA=43bfb618d125971ea9d397fafb337ba83ce19b3d04623cbaf05938ecd18a19bf
IMAGE_EVIDENCE_RECEIPT_SHA=429eeeaee64b5e46989a2b929edcd093b12c93528bfa08010e9e1e598869582c
IMAGE_EVIDENCE_PRODUCER_SHA=7c8beb0bf1ad8347fba39dbd5656892129e5a1ad6954dfae0b02379960130e8b
QUEUE_SHA=7feaf4cc4cf4c390beb0fc8ec245603ee855a42c9d5345504199ae76b851e3d9
MANIFEST_SHA=1ad8d04421570640b098a1b400e1f5dbc3b04fa8594debff5f88c20323592824
OVERLAY_MANIFEST_SHA=47c9caccc3ab7546b59bdd1fd5e3c924575d15ec54c030cd66a28a688708f8a0
OVERLAY_RECEIPT_SHA=bd53ce093e53654fdb32d97b66c6251cd3aafdcacaffb65dd1f67bbe2d02657a
OVERLAY_IDENTITY_SHA=df16b5f2be9748f1dbf9290a3e0da1e6079e735dd00f33c3fa5623a4dfa538b9
IMAGE_CONFIG_ID=sha256:39a805ad21da2e79dbd2e446c1333e4cdb975e44d401af95a29f7ca6b5a2995e
IMAGE_OCI_DIGEST=lean4-arm64@sha256:a5ca6c4e3328a1832d5f9b814ab7c1e35616903b3956341962a5b1a96fb6dff6
PHASE=initializing
INSTANCE_ID=unknown

# shellcheck disable=SC2329 # invoked indirectly by the EXIT trap
finish() {
  rc=$?
  trap - EXIT
  set +e
  terminal=/tmp/erdos85-replay-bootstrap-terminal.json
  /usr/bin/python3 - "$INSTANCE_ID" "$PHASE" "$rc" > "$terminal" <<'PY'
import json, sys
print(json.dumps({
    "schema": "erdos85-h1-replay-bootstrap-terminal-v1",
    "instance_id": sys.argv[1], "phase": sys.argv[2],
    "returncode": int(sys.argv[3]),
}, sort_keys=True, separators=(",", ":")))
PY
  if test "$INSTANCE_ID" != unknown && test -x /usr/local/bin/aws; then
    /usr/local/bin/aws s3api put-object --bucket "$BUCKET" \
      --key "$PREFIX/bootstrap-terminal/$INSTANCE_ID.json" \
      --body "$terminal" --if-none-match '*' --output json || true
  fi
  /usr/sbin/shutdown -h now || /usr/bin/systemctl poweroff --no-block || true
  exit "$rc"
}
trap finish EXIT

exec > >(tee -a /var/log/erdos85-replay-bootstrap.log) 2>&1
export DEBIAN_FRONTEND=noninteractive HOME=/root AWS_PAGER=
export AWS_RETRY_MODE=standard AWS_MAX_ATTEMPTS=5
PHASE=installing-tools
if test -f /etc/apt/sources.list.d/ubuntu.sources; then
  sed -i \
    -e 's/us-east-1\.ec2\.ports\.ubuntu\.com/ports.ubuntu.com/g' \
    -e 's/us-east-1\.ec2\.archive\.ubuntu\.com/archive.ubuntu.com/g' \
    /etc/apt/sources.list.d/ubuntu.sources
fi
apt-get -o Acquire::Retries=5 update
apt-get -o Acquire::Retries=5 install -y --no-install-recommends \
  ca-certificates curl docker.io jq unzip zstd
systemctl enable --now docker
mkdir -p "$ROOT/freight" "$ROOT/repo" "$ROOT/state" "$ROOT/overlay-publication"

curl -fL --retry 5 --retry-all-errors --connect-timeout 15 --max-time 1800 \
  https://awscli.amazonaws.com/awscli-exe-linux-aarch64-2.36.34.zip \
  -o "$ROOT/freight/awscliv2.zip"
printf '%s  %s\n' "$AWS_ZIP_SHA" "$ROOT/freight/awscliv2.zip" | sha256sum -c -
unzip -q "$ROOT/freight/awscliv2.zip" -d "$ROOT/freight/awscli"
"$ROOT/freight/awscli/aws/install" --update

TOKEN=$(curl -fsS --retry 5 --retry-all-errors --connect-timeout 3 --max-time 30 \
  -X PUT -H 'X-aws-ec2-metadata-token-ttl-seconds: 21600' \
  http://169.254.169.254/latest/api/token)
IDENTITY=$(curl -fsS --retry 5 --retry-all-errors --connect-timeout 3 --max-time 30 \
  -H "X-aws-ec2-metadata-token: $TOKEN" \
  http://169.254.169.254/latest/dynamic/instance-identity/document)
INSTANCE_ID=$(printf '%s' "$IDENTITY" | jq -er .instanceId)
AMI_ID=$(printf '%s' "$IDENTITY" | jq -er .imageId)
INSTANCE_TYPE=$(printf '%s' "$IDENTITY" | jq -er .instanceType)
REGION=$(printf '%s' "$IDENTITY" | jq -er .region)
test "$AMI_ID" = ami-02c4144237becae44
test "$INSTANCE_TYPE" = r7g.2xlarge
test "$REGION" = us-east-1

AWS_ID=$(/usr/local/bin/aws --version 2>&1)
ZSTD_ID=$(/usr/bin/zstd --version | head -1)
DOCKER_ID=$(/usr/bin/docker --version)
PYTHON_ID=$(/usr/bin/python3 --version)
PHASE=materializing-freight
for name in repo-4c7cbb5159.tar.zst complete-overlay-4c7cbb5159-import-data.tar.zst \
  lean4-arm64-a5ca6c4e.docker.tar.zst queue.jsonl manifest.json; do
  /usr/local/bin/aws s3api get-object --bucket "$BUCKET" \
    --key "$FREIGHT_PREFIX/$name" "$ROOT/freight/$name" --output json
done
mkdir "$ROOT/freight/image-evidence"
for name in archive-config.json archive-manifest.json docker-context.txt \
  docker-version.json fresh-save-config.json fresh-save-manifest.json \
  live-inspect.json receipt.json capture-image-identity.py; do
  /usr/local/bin/aws s3api get-object --bucket "$BUCKET" \
    --key "$FREIGHT_PREFIX/image-evidence/$name" \
    "$ROOT/freight/image-evidence/$name" --output json
done
printf '%s  %s\n' \
  "$REPO_SHA" "$ROOT/freight/repo-4c7cbb5159.tar.zst" \
  "$OVERLAY_SHA" "$ROOT/freight/complete-overlay-4c7cbb5159-import-data.tar.zst" \
  "$IMAGE_ARCHIVE_SHA" "$ROOT/freight/lean4-arm64-a5ca6c4e.docker.tar.zst" \
  "$IMAGE_EVIDENCE_RECEIPT_SHA" "$ROOT/freight/image-evidence/receipt.json" \
  "$IMAGE_EVIDENCE_PRODUCER_SHA" "$ROOT/freight/image-evidence/capture-image-identity.py" \
  "$QUEUE_SHA" "$ROOT/freight/queue.jsonl" \
  "$MANIFEST_SHA" "$ROOT/freight/manifest.json" | sha256sum -c -

zstd -dc "$ROOT/freight/repo-4c7cbb5159.tar.zst" | tar -C "$ROOT/repo" -xf -
zstd -t "$ROOT/freight/complete-overlay-4c7cbb5159-import-data.tar.zst"
zstd -dc "$ROOT/freight/complete-overlay-4c7cbb5159-import-data.tar.zst" | \
  tar -C "$ROOT/overlay-publication" -xf -
printf '%s  %s\n' \
  "$OVERLAY_MANIFEST_SHA" "$ROOT/overlay-publication/manifest.json" \
  "$OVERLAY_RECEIPT_SHA" "$ROOT/overlay-publication/receipt.json" | sha256sum -c -
python3 - "$ROOT/repo" "$ROOT/overlay-publication" "$OVERLAY_IDENTITY_SHA" <<'PY'
import json, pathlib, sys
repo = pathlib.Path(sys.argv[1])
publication = pathlib.Path(sys.argv[2])
expected_identity = sys.argv[3]
sys.path.insert(0, str(repo / "h1fleet"))
import build_replay_overlay_archive as archive
identity = archive.validate_publication(publication)
if identity["overlay_identity_sha256"] != expected_identity:
    raise SystemExit("overlay identity mismatch")
print(json.dumps(identity, sort_keys=True, separators=(",", ":")))
PY
mv "$ROOT/overlay-publication/overlay" "$ROOT/overlay"

ARCHIVE_CONFIG_PATH=$(zstd -dc \
  "$ROOT/freight/lean4-arm64-a5ca6c4e.docker.tar.zst" | \
  tar -xOf - manifest.json | jq -er \
  'if length == 1 and (.[0].RepoTags == ["lean4-arm64:v4.31.0"]) then .[0].Config else error("image save manifest mismatch") end')
test "$ARCHIVE_CONFIG_PATH" = "blobs/sha256/${IMAGE_CONFIG_ID#sha256:}"
zstd -dc "$ROOT/freight/lean4-arm64-a5ca6c4e.docker.tar.zst" | docker load
LOADED_CONFIG_ID=$(docker image inspect lean4-arm64:v4.31.0 --format '{{.Id}}')
test "$LOADED_CONFIG_ID" = "$IMAGE_CONFIG_ID"
LOADED_ROOTFS=$(docker image inspect lean4-arm64:v4.31.0 --format '{{json .RootFS.Layers}}')
python3 - "$ROOT/freight/image-evidence" "$IMAGE_ARCHIVE_SHA" \
  "$LOADED_CONFIG_ID" "$IMAGE_OCI_DIGEST" "$LOADED_ROOTFS" <<'PY'
import hashlib, json, pathlib, sys
root = pathlib.Path(sys.argv[1]); receipt = json.load(open(root / "receipt.json"))
assert receipt["schema"] == "erdos85-h1-replay-image-identity-evidence-v1"
assert receipt["archive_sha256"] == sys.argv[2]
assert receipt["archive_config_digest"] == sys.argv[3]
assert receipt["live_repo_digest"] == sys.argv[4]
for row in receipt["files"]:
    data = (root / row["path"]).read_bytes()
    assert len(data) == row["bytes"]
    assert hashlib.sha256(data).hexdigest() == row["sha256"]
producer = (root / "capture-image-identity.py").read_bytes()
assert hashlib.sha256(producer).hexdigest() == receipt["producer_sha256"]
live = json.load(open(root / "live-inspect.json"))[0]
fresh_manifest = json.load(open(root / "fresh-save-manifest.json"))
archive_manifest = json.load(open(root / "archive-manifest.json"))
fresh_config = json.load(open(root / "fresh-save-config.json"))
archive_config = json.load(open(root / "archive-config.json"))
assert fresh_manifest == archive_manifest == receipt["fresh_archive_manifest"]
assert fresh_config == archive_config
assert live["RepoTags"] == [receipt["image"]]
assert live["RepoDigests"] == [receipt["live_repo_digest"]]
assert live["RootFS"]["Layers"] == fresh_config["rootfs"]["diff_ids"]
assert live["RootFS"]["Layers"] == json.loads(sys.argv[5])
PY

PHASE=publishing-identity
jq -n --arg instance_id "$INSTANCE_ID" --arg ami_id "$AMI_ID" \
  --arg instance_type "$INSTANCE_TYPE" --arg region "$REGION" \
  --arg aws_cli_identity "$AWS_ID" --arg zstd_identity "$ZSTD_ID" \
  --arg docker_identity "$DOCKER_ID" --arg python_identity "$PYTHON_ID" \
  --arg image_archive_sha256 "$IMAGE_ARCHIVE_SHA" \
  --arg image_evidence_receipt_sha256 "$IMAGE_EVIDENCE_RECEIPT_SHA" \
  --arg image_config_id "$LOADED_CONFIG_ID" --arg image_oci_digest "$IMAGE_OCI_DIGEST" \
  '{schema:"erdos85-h1-replay-bootstrap-identity-v2",instance_id:$instance_id,
    ami_id:$ami_id,instance_type:$instance_type,region:$region,
    aws_cli_identity:$aws_cli_identity,zstd_identity:$zstd_identity,
    docker_identity:$docker_identity,python_identity:$python_identity,
    image_archive_sha256:$image_archive_sha256,
    image_evidence_receipt_sha256:$image_evidence_receipt_sha256,
    image_config_id:$image_config_id,
    reviewed_image_oci_digest:$image_oci_digest}' > "$ROOT/bootstrap-identity.json"
/usr/local/bin/aws s3api put-object --bucket "$BUCKET" \
  --key "$PREFIX/bootstrap/$INSTANCE_ID.json" --body "$ROOT/bootstrap-identity.json" \
  --if-none-match '*' --output json

python3 - "$ROOT/freight/manifest.json" "$AWS_ID" "$ZSTD_ID" \
  "$IMAGE_OCI_DIGEST" <<'PY'
import json, sys
manifest = json.load(open(sys.argv[1]))
assert manifest["aws_cli_identity"] == sys.argv[2]
assert manifest["zstd_identity"] == sys.argv[3]
assert manifest["worker_image_digest"] == sys.argv[4]
assert manifest["repository_commit"] == "4c7cbb515934254e0795916001617150587559f5"
assert manifest["worker_ami_id"] == "ami-02c4144237becae44"
assert manifest["worker_instance_type"] == "r7g.2xlarge"
assert manifest["aws_region"] == "us-east-1"
assert manifest["queue_sha256"] == "7feaf4cc4cf4c390beb0fc8ec245603ee855a42c9d5345504199ae76b851e3d9"
assert manifest["overlay_archive_sha256"] == "2c7f6868e86a6ace0eb3f451977a4d65bd4c333d4611a00001d91672b6d17460"
PY

PHASE=running-dispatcher
set +e
/usr/bin/python3 "$ROOT/repo/h1fleet/run_replay_queue.py" \
  --manifest "$ROOT/freight/manifest.json" --queue "$ROOT/freight/queue.jsonl" \
  --state-dir "$ROOT/state" --parallelism 1 --execute YES \
  --s3-bucket "$BUCKET" --aws /usr/local/bin/aws
RC=$?
set -e
PHASE=dispatcher-complete
exit "$RC"
