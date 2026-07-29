# UNAPPLIED SKELETON — see README.md.
# TODO: review before applying.
#
# Least-privilege role for a worker instance: consume jobs from the queue, write
# results/diag blocks to the result bucket. Deliberately does NOT grant any
# EC2/ASG/AMI/IAM permissions — provisioning the compute fleet itself is out of scope
# for this skeleton (see README "What this is NOT") and would need its own, separately
# reviewed policy.

data "aws_iam_policy_document" "remote_build_worker_assume_role" {
  statement {
    effect  = "Allow"
    actions = ["sts:AssumeRole"]

    principals {
      type        = "Service"
      identifiers = ["ec2.amazonaws.com"]
    }
  }
}

resource "aws_iam_role" "remote_build_worker" {
  # TODO: review before applying.
  name               = "lean-remote-build-worker"
  assume_role_policy = data.aws_iam_policy_document.remote_build_worker_assume_role.json
}

data "aws_iam_policy_document" "remote_build_worker_permissions" {
  statement {
    sid    = "ConsumeJobQueue"
    effect = "Allow"
    actions = [
      "sqs:ReceiveMessage",
      "sqs:DeleteMessage",
      "sqs:GetQueueAttributes",
    ]
    resources = [aws_sqs_queue.remote_build_jobs.arn]
  }

  statement {
    sid    = "WriteJobResults"
    effect = "Allow"
    actions = [
      "s3:PutObject",
      "s3:GetObject",
    ]
    resources = ["${aws_s3_bucket.remote_build_results.arn}/*"]
  }

  statement {
    sid       = "ListResultBucket"
    effect    = "Allow"
    actions   = ["s3:ListBucket"]
    resources = [aws_s3_bucket.remote_build_results.arn]
  }
}

resource "aws_iam_role_policy" "remote_build_worker" {
  # TODO: review before applying.
  name   = "lean-remote-build-worker-permissions"
  role   = aws_iam_role.remote_build_worker.id
  policy = data.aws_iam_policy_document.remote_build_worker_permissions.json
}

resource "aws_iam_instance_profile" "remote_build_worker" {
  # TODO: review before applying.
  name = "lean-remote-build-worker"
  role = aws_iam_role.remote_build_worker.name
}
