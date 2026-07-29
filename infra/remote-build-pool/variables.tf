# UNAPPLIED SKELETON — see README.md.
# TODO: review before applying.

variable "aws_region" {
  description = "AWS region for the job queue and result store. Graviton (arm64) worker capacity availability should drive this; us-west-2 is used as the default reference region in research/remote-build-pool-design.md §2."
  type        = string
  default     = "us-west-2"
}

variable "environment" {
  description = "Deployment environment tag (e.g. \"dev\", \"prod\"). Kept separate from Terraform workspaces so a human can decide the isolation strategy at apply time."
  type        = string
  default     = "dev"
}

variable "queue_name" {
  description = "Name of the SQS job-submission queue (§6 of the design doc)."
  type        = string
  default     = "lean-remote-build-jobs"
}

variable "result_bucket_name" {
  description = <<-EOT
    Name of the S3 bucket that stores job results/diag blocks (§3, §7 of the design
    doc). S3 bucket names are globally unique across ALL AWS accounts, so there is
    intentionally NO default here — a human must supply a concrete, already-verified-
    available name in terraform.tfvars before this could ever be applied.
  EOT
  type        = string
}

variable "result_retention_days" {
  description = "Days to retain job result/diag objects before S3 lifecycle expiration (§7: \"S3 lifecycle: expire job result/diag objects after N days; the ledger keeps the durable copy\")."
  type        = number
  default     = 30
}

variable "visibility_timeout_seconds" {
  description = "SQS visibility timeout. Must exceed the longest expected per-target build time (per_target_timeout_s in the job contract, §3) so an in-flight job isn't redelivered to a second worker before the first finishes."
  type        = number
  default     = 900 # 15 min; comfortably above the design doc's per_target_timeout_s=300 default with headroom for cold-start + queueing.
}

variable "message_retention_seconds" {
  description = "How long an undelivered job message stays in the queue before AWS drops it."
  type        = number
  default     = 86400 # 1 day
}

variable "max_receive_count" {
  description = "Number of delivery attempts before a job message is moved to the dead-letter queue (e.g. spot-interrupted workers that never ack)."
  type        = number
  default     = 3
}
