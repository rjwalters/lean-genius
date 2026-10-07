#!/usr/bin/env bash
# Provision the erdos85 Lean builder from the Mac (operator tool; agents use e85-remote).
#
#   provision.sh setup-instance           launch a fresh AL2023 arm64 instance (Role=ami-setup)
#   provision.sh run-setup <iid>          copy ami_setup.sh over SSM and run it (in tmux, logged)
#   provision.sh create-ami <iid>         stop it, image it as erdos85-lean-builder-<date> (private)
#   provision.sh launch <ami-id>          launch the long-lived builder (Role=builder) from the AMI
#
# One-time prerequisites (already created in account 221082181346, us-east-1):
#   IAM role + instance profile Erdos85LeanBuilder (AmazonSSMManagedInstanceCore + S3 read on
#   s3://2am-erdos85-certs/lean-builder/* and the checker-kit image), EC2 key pair
#   e85-lean-builder (private key ~/.ssh/e85-lean-builder), security group
#   erdos85-lean-builder (NO inbound rules: all access is SSH tunnelled through SSM).
set -euo pipefail
export AWS_PROFILE=${E85_AWS_PROFILE:-2am-admin}
export AWS_DEFAULT_REGION=us-east-1
HERE=$(cd "$(dirname "$0")" && pwd)
TYPE=${E85_INSTANCE_TYPE:-r7g.4xlarge}
SUBNET=${E85_SUBNET:-subnet-08f3348aed146a9bc}   # us-east-1a (avoid us-east-1d)
ROOT_GB=${E85_ROOT_GB:-200}
sg() { aws ec2 describe-security-groups --filters Name=group-name,Values=erdos85-lean-builder --query 'SecurityGroups[0].GroupId' --output text; }

launch() {  # <ami> <role> <name>
    aws ec2 run-instances --image-id "$1" --instance-type "$TYPE" --subnet-id "$SUBNET" \
        --security-group-ids "$(sg)" --key-name e85-lean-builder \
        --iam-instance-profile Name=Erdos85LeanBuilder \
        --instance-initiated-shutdown-behavior stop \
        --metadata-options HttpTokens=required,HttpEndpoint=enabled,InstanceMetadataTags=enabled \
        --block-device-mappings "DeviceName=/dev/xvda,Ebs={VolumeSize=$ROOT_GB,VolumeType=gp3,Iops=4000,Throughput=250,DeleteOnTermination=true}" \
        --tag-specifications "ResourceType=instance,Tags=[{Key=Project,Value=erdos85-lean-builder},{Key=Role,Value=$2},{Key=Name,Value=$3}]" \
                             "ResourceType=volume,Tags=[{Key=Project,Value=erdos85-lean-builder},{Key=Name,Value=$3}]" \
        --query 'Instances[0].InstanceId' --output text
}

case ${1:-} in
    setup-instance)
        ami=$(aws ssm get-parameter --name /aws/service/ami-amazon-linux-latest/al2023-ami-kernel-default-arm64 --query Parameter.Value --output text)
        launch "$ami" ami-setup erdos85-lean-builder-ami-setup ;;
    run-setup)
        iid=${2:?instance id}
        E85_INSTANCE_ID=$iid "$HERE/e85-remote" ssh "cat > /tmp/ami_setup.sh" < "$HERE/ami_setup.sh"
        E85_INSTANCE_ID=$iid "$HERE/e85-remote" ssh "sudo dnf -y -q install tmux >/dev/null && sudo tmux new -d -s setup 'bash /tmp/ami_setup.sh 2>&1 | tee /var/log/e85-ami-setup.log; echo EXIT=\${PIPESTATUS[0]} >> /var/log/e85-ami-setup.log'"
        echo "running; follow with: E85_INSTANCE_ID=$iid $HERE/e85-remote ssh tail -f /var/log/e85-ami-setup.log" ;;
    create-ami)
        iid=${2:?instance id}; name="erdos85-lean-builder-$(date -u +%Y%m%d-%H%M)"
        aws ec2 stop-instances --instance-ids "$iid" >/dev/null; aws ec2 wait instance-stopped --instance-ids "$iid"
        ami=$(aws ec2 create-image --instance-id "$iid" --name "$name" \
            --description "erdos85 Lean builder: pinned lean4 v4.31.0 image, warm Mathlib, /opt/lean-genius (private)" \
            --tag-specifications "ResourceType=image,Tags=[{Key=Project,Value=erdos85-lean-builder},{Key=Name,Value=$name}]" \
                                 "ResourceType=snapshot,Tags=[{Key=Project,Value=erdos85-lean-builder},{Key=Name,Value=$name}]" \
            --query ImageId --output text)
        echo "$ami ($name) creating"; aws ec2 wait image-available --image-ids "$ami" && echo "$ami available"
        aws ec2 describe-images --image-ids "$ami" --query 'Images[0].Public' --output text ;;
    launch)
        launch "${2:?ami id}" builder erdos85-lean-builder ;;
    *) sed -n '2,15p' "$0"; exit 2 ;;
esac
