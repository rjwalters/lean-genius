# UNAPPLIED SKELETON — see README.md.
# TODO: review before applying.
#
# Job queue + dead-letter queue backing the "Autoscaling approach" diagram in
# research/remote-build-pool-design.md §6. ASG target-tracking (not declared in this
# skeleton — see README "What this is NOT") would scale workers on
# ApproximateNumberOfMessagesVisible against `remote_build_jobs`.

resource "aws_sqs_queue" "remote_build_jobs_dlq" {
  # TODO: review before applying.
  name                      = "${var.queue_name}-dlq"
  message_retention_seconds = 1209600 # 14 days — max SQS allows; give a human time to notice + drain.
}

resource "aws_sqs_queue" "remote_build_jobs" {
  # TODO: review before applying.
  name                       = var.queue_name
  visibility_timeout_seconds = var.visibility_timeout_seconds
  message_retention_seconds  = var.message_retention_seconds

  # A job re-delivered `max_receive_count` times (e.g. worker spot-interrupted before
  # ack) is dead-lettered rather than retried forever. Verification jobs are
  # deterministic/idempotent (design doc §6 "Idempotency"), so redelivery itself is
  # safe; the DLQ exists to surface jobs that fail deterministically every time
  # (a genuinely broken target) rather than let them loop silently.
  redrive_policy = jsonencode({
    deadLetterTargetArn = aws_sqs_queue.remote_build_jobs_dlq.arn
    maxReceiveCount     = var.max_receive_count
  })
}
