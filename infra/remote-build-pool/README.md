# Remote Build Pool — Terraform Skeleton (UNAPPLIED)

Part of #38684. See `research/remote-build-pool-design.md` for the full design and
`research/remote-build-pool-cost-estimate.md` for rough cost sizing.

## What this is

A **skeleton, not a deployment.** It declares the two lowest-risk pieces of §10 item 1
of the design doc — an SQS job queue (+ dead-letter queue) and an S3 result-store bucket
with a worker IAM role — in Terraform HCL, so a human reviewer can see the intended
resource shape, tighten it, and decide whether to run it.

**Nothing in this directory has been run.** No `terraform init`, `plan`, or `apply` has
been executed against any AWS account, by an agent or otherwise. Every resource block is
marked `# TODO: review before applying`.

## What this is NOT

- Not the AMI / worker launch template (§10 item 2-3 of the design doc — needs the AMI
  bake step first).
- Not the ASG / autoscaling policy (§10 item 3 — blocked on the §2 EC2 vCPU quota
  increase, which has not been requested yet).
- Not a working pipeline. There is no Lambda, no worker, no consumer wired to the queue.
  `scripts/remote-build/submit-job.sh` remains dry-run-only and does not point at any
  queue created from this skeleton.

## Hard safety constraint (do not remove this section)

This is real AWS infrastructure-as-code. Applying it costs money and requires real AWS
credentials that no agent session in this repository has or should have.

**No agent may run `terraform init`, `terraform plan`, `terraform apply`, or any AWS
CLI/SDK command against these files.** This directory exists purely for human review.
A human operator, outside of any agent's autonomy, with their own AWS credentials, is
responsible for:

1. Reviewing every resource block (they are intentionally conservative but unaudited).
2. Filling in `terraform.tfvars` (no committed defaults for bucket names / account IDs).
3. Confirming the §2 EC2 vCPU quota increase has landed if/when the worker fleet
   (out of scope here) is added on top of this.
4. Running `terraform init` / `plan` / `apply` themselves, reviewing the plan output
   before confirming apply.

## Layout

| File | Declares |
|------|----------|
| `versions.tf` | Terraform + AWS provider version constraints. No backend configured — a real deployment must add a remote backend (S3 + DynamoDB lock table) before `apply`; local state is not appropriate for shared infra. |
| `variables.tf` | Inputs: region, project/environment tags, bucket name (no default — must be globally unique), queue name, result retention days. |
| `sqs.tf` | `remote_build_jobs` queue + `remote_build_jobs_dlq` dead-letter queue. Visibility timeout sized off `per_target_timeout_s` in the job contract (`research/remote-build-pool-design.md` §3). |
| `s3.tf` | Result-store bucket (job results / diag blocks, §3 and §7 of the design doc) with public access blocked and a lifecycle rule expiring objects after `var.result_retention_days`. |
| `iam.tf` | `remote_build_worker` IAM role + instance profile: least-privilege SQS receive/delete on the job queue and S3 read/write scoped to the result bucket only. No EC2/ASG/AMI permissions — provisioning the fleet is a separate, later step. |
| `outputs.tf` | Queue URL/ARN, bucket name/ARN, role/instance-profile ARNs — for wiring into the (not-yet-written) worker launch template. |
| `terraform.tfvars.example` | Example values. Copy to `terraform.tfvars` (gitignored) and fill in before a human runs `plan`. |

## Estimated cost of *this* skeleton alone

SQS and S3 at rest cost effectively nothing when idle (S3 storage for a handful of small
JSON result objects; SQS has no idle charge, only per-request pricing). The real cost
driver is the compute fleet (§10 items 2-3), not these two resources — see
`research/remote-build-pool-cost-estimate.md` for that estimate. This skeleton could be
applied in isolation (queue + bucket + IAM role, no compute) for negligible spend if a
human wanted to unblock later worker development, but that decision is explicitly left
to a human, not this PR.
