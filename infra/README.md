# infra/

Infrastructure-as-code. Currently a single, **unapplied** Terraform skeleton:

- `remote-build-pool/` — SQS job queue (+ dead-letter queue), S3 result bucket, and a
  worker IAM role for a remote Lean verification pool (issue #38684). Nothing here
  has been `init`/`plan`/`apply`-ed against any account; every resource is marked
  `# TODO: review before applying`. Read `remote-build-pool/README.md` first.

Related material:

- Design and cost sizing: `research/remote-build-pool-design.md`,
  `research/remote-build-pool-cost-estimate.md`.
- Client side: `scripts/remote-build/submit-job.sh` builds a job request for the pool.
- Local variable values go in `remote-build-pool/terraform.tfvars` (gitignored there;
  `terraform.tfvars.example` shows the shape).
