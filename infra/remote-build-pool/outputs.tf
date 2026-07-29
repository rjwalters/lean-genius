# UNAPPLIED SKELETON — see README.md.

output "job_queue_url" {
  description = "SQS URL a submitter (e.g. a future live mode of scripts/remote-build/submit-job.sh) would send job requests to."
  value       = aws_sqs_queue.remote_build_jobs.url
}

output "job_queue_arn" {
  value = aws_sqs_queue.remote_build_jobs.arn
}

output "job_queue_dlq_arn" {
  value = aws_sqs_queue.remote_build_jobs_dlq.arn
}

output "result_bucket_name" {
  value = aws_s3_bucket.remote_build_results.bucket
}

output "result_bucket_arn" {
  value = aws_s3_bucket.remote_build_results.arn
}

output "worker_iam_role_arn" {
  description = "Attach to the (not-yet-declared) worker launch template via worker_instance_profile_name."
  value       = aws_iam_role.remote_build_worker.arn
}

output "worker_instance_profile_name" {
  value = aws_iam_instance_profile.remote_build_worker.name
}
