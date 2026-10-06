#!/bin/bash
# Prepare an Amazon Linux 2023 arm64 host as an Erdős 85 H1 checker (this is what the public AMI was
# built with; a third party can also run it on a fresh AL2023 arm64 instance instead of using the AMI).
# Usage (as root): E85_COMMIT=<repo commit> bash ami_setup.sh
# Reads the checker kit from the Requester Pays bucket with the instance's own credentials.
set -euo pipefail
B=s3://2am-erdos85-certs/public/erdos85-h1-checker-kit
E85_COMMIT=${E85_COMMIT:?set E85_COMMIT to the release commit}
CAKE_COMMIT=a36874a8b750b43fe4b385b8ddbf5b033e46a3fa
IMAGE_ID=sha256:a5ca6c4e3328a1832d5f9b814ab7c1e35616903b3956341962a5b1a96fb6dff6
export AWS_DEFAULT_REGION=us-east-1
dnf -y install docker python3.12 zstd gcc make tar unzip git >/dev/null
( cd /tmp && curl -fsSL -o awscliv2.zip https://awscli.amazonaws.com/awscli-exe-linux-aarch64.zip && unzip -q -o awscliv2.zip && ./aws/install --update -i /opt/aws-cli -b /usr/local/bin )
AWS=/usr/local/bin/aws
mkdir -p /etc/docker && echo '{"features":{"containerd-snapshotter":true}}' > /etc/docker/daemon.json
systemctl enable --now docker
mkdir -p /opt/e85/kit /opt/e85/bin /scratch && chmod 1777 /scratch
$AWS s3 sync --only-show-errors --request-payer requester $B/ /opt/e85/kit/
( cd /opt/e85/kit && sha256sum -c --quiet MANIFEST.sha256 )
zstd -dc /opt/e85/kit/bin/lean4-arm64-v4.31.0.oci.tar.zst | docker load
[ "$(docker image inspect $IMAGE_ID --format '{{.Id}}')" = "$IMAGE_ID" ]
rm /opt/e85/kit/bin/lean4-arm64-v4.31.0.oci.tar.zst
zstd -dc /opt/e85/kit/bin/v2cnf.zst > /opt/e85/bin/v2cnf && chmod 755 /opt/e85/bin/v2cnf
[ "$(sha256sum /opt/e85/bin/v2cnf | cut -d' ' -f1)" = 4bd9604c6d670ad65a8ca332a26dbf35132418634a3b0678c177c8b2cfff4bf6 ]
install -m 755 /opt/e85/kit/bin/cadical /usr/local/bin/cadical
( cd /opt/e85/kit/bin && grep ' cadical$' solvers.sha256 | sha256sum -c --quiet )
( cd /opt && git clone -q https://github.com/tanyongkiam/cake_lpr && cd cake_lpr && git checkout -q $CAKE_COMMIT && gcc basis_ffi.c cake_lpr_arm8.S -o cake_lpr -std=c99 )
install -m 755 /opt/cake_lpr/cake_lpr /usr/local/bin/cake_lpr
( cd /opt/e85 && git clone -q --filter=blob:none https://github.com/rjwalters/lean-genius repo && cd repo && git checkout -q $E85_COMMIT )
printf '#!/bin/sh\nexec python3.12 /opt/e85/repo/research/problems/erdos-85-wip-01/h1_checker_kit/e85-check "$@"\n' > /usr/local/bin/e85-check
chmod 755 /usr/local/bin/e85-check
id ec2-user >/dev/null 2>&1 && usermod -aG docker ec2-user
# Self-test: the checker must accept a valid proof and reject a corrupted one.
printf 'p cnf 2 4\n1 2 0\n-1 2 0\n1 -2 0\n-1 -2 0\n' > /tmp/u.cnf
printf '5 1 0 1 3 0\n6 -1 0 2 4 0\n7 0 5 6 0\n' > /tmp/u.lrat
printf '5 1 0 1 3 0\n7 0 5 0\n' > /tmp/bad.lrat
cake_lpr /tmp/u.cnf /tmp/u.lrat | grep -qx 's VERIFIED UNSAT'
! cake_lpr /tmp/u.cnf /tmp/bad.lrat | grep -q VERIFIED
echo "e85 checker host ready: run 'e85-check --help'"
