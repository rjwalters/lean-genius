# UNAPPLIED SKELETON — see README.md.
# TODO: review before applying.
#
# Result store for job outputs (§3 "Response" — results[] per target) and diag blocks
# (§3 "Two derived artifacts"). The durable copy of pass/fail state is the
# verify-results.tsv ledger, not this bucket (§7: "the ledger keeps the durable copy"),
# so this bucket is intentionally short-retention scratch space, not a permanent store.

resource "aws_s3_bucket" "remote_build_results" {
  # TODO: review before applying. Bucket name must be globally unique; no default is
  # provided (see variables.tf) so this cannot be applied without a human supplying one.
  bucket = var.result_bucket_name
}

resource "aws_s3_bucket_public_access_block" "remote_build_results" {
  bucket = aws_s3_bucket.remote_build_results.id

  block_public_acls       = true
  block_public_policy     = true
  ignore_public_acls      = true
  restrict_public_buckets = true
}

resource "aws_s3_bucket_lifecycle_configuration" "remote_build_results" {
  bucket = aws_s3_bucket.remote_build_results.id

  rule {
    id     = "expire-job-results"
    status = "Enabled"

    # Applies to every object in the bucket — this bucket is single-purpose scratch
    # space for job results/diag blocks, not shared with other data.
    filter {}

    expiration {
      days = var.result_retention_days
    }
  }
}

resource "aws_s3_bucket_server_side_encryption_configuration" "remote_build_results" {
  bucket = aws_s3_bucket.remote_build_results.id

  rule {
    apply_server_side_encryption_by_default {
      sse_algorithm = "AES256"
    }
  }
}
