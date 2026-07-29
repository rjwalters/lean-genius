# UNAPPLIED SKELETON — see README.md. Do not run terraform init/plan/apply from an
# agent session. This file exists for human review only.
#
# TODO: review before applying. In particular: add a remote backend (S3 + DynamoDB
# lock table) before any real `apply` — local state is not appropriate for shared,
# team-reviewed infrastructure. No backend block is declared here on purpose so this
# skeleton cannot accidentally initialize local state if someone runs `terraform init`
# without reading the README first.

terraform {
  required_version = ">= 1.5.0"

  required_providers {
    aws = {
      source  = "hashicorp/aws"
      version = "~> 5.0"
    }
  }

  # TODO: review before applying — add a `backend "s3" { ... }` block here, pointing
  # at a pre-existing state bucket + DynamoDB lock table, before running `apply` for
  # real. Left unset intentionally.
}

provider "aws" {
  region = var.aws_region

  default_tags {
    tags = {
      Project     = "lean-genius-remote-build-pool"
      ManagedBy   = "terraform"
      Issue       = "38684"
      Environment = var.environment
    }
  }
}
