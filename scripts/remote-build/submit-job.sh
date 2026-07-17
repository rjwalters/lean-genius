#!/usr/bin/env bash
#
# submit-job.sh — build a spec-conformant remote-build job request and (optionally)
# submit it to a remote Lean verification pool.
#
# This is a SCAFFOLDING STUB for issue #38684. See research/remote-build-pool-design.md
# for the full design. By default it makes NO network calls and provisions NOTHING —
# it only prints the JSON job request so the contract shape can be reviewed and tested.
#
# The job request mirrors proofs/batch2/runner2.sh's per-file recheck contract:
#     { files, toolchain, git ref } -> { EXIT, first-N error lines }
#
# Usage:
#   scripts/remote-build/submit-job.sh Erdos1026OQ05Mirsky WeakGoldbachBounds
#   scripts/remote-build/submit-job.sh --list targets.txt
#   scripts/remote-build/submit-job.sh --git-ref a1b2c3d Erdos1026OQ05Mirsky
#
# Environment:
#   REMOTE_BUILD_LIVE     If "1", actually POST the request to REMOTE_BUILD_ENDPOINT.
#                         Default unset => dry-run: print the request and exit 0.
#   REMOTE_BUILD_ENDPOINT Submit URL (required only when REMOTE_BUILD_LIVE=1).
#   TOOLCHAIN             Lean toolchain (default: leanprover/lean4:v4.31.0).
#   WORKER_IMAGE          Worker image tag (default: lean4-arm64:v4.31.0).
#   PER_TARGET_TIMEOUT_S  Per-target recheck timeout (default: 300, matches runner2.sh).
#   BULK_TIMEOUT_S        Bulk warm-pass timeout (default: 2400, matches runner2.sh).
#   MEMORY_LIMIT_MB       Per-container --memory (default: 32768, matches docker-build.sh).
#
# SAFETY: This script NEVER runs `aws ec2 run-instances` or creates any cloud resource.
# The only network action it can take — and only under REMOTE_BUILD_LIVE=1 — is a single
# HTTP POST to an endpoint YOU supply. Provisioning the pool itself is out of scope; see
# research/remote-build-pool-design.md sections 2, 6, and 10.

set -euo pipefail

TOOLCHAIN="${TOOLCHAIN:-leanprover/lean4:v4.31.0}"
WORKER_IMAGE="${WORKER_IMAGE:-lean4-arm64:v4.31.0}"
PER_TARGET_TIMEOUT_S="${PER_TARGET_TIMEOUT_S:-300}"
BULK_TIMEOUT_S="${BULK_TIMEOUT_S:-2400}"
MEMORY_LIMIT_MB="${MEMORY_LIMIT_MB:-32768}"

GIT_REF=""
LIST_FILE=""
declare -a TARGETS=()

usage() {
  sed -n '2,40p' "$0" | sed 's/^# \{0,1\}//'
  exit "${1:-0}"
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    -h|--help)     usage 0 ;;
    --git-ref)     GIT_REF="$2"; shift 2 ;;
    --list)        LIST_FILE="$2"; shift 2 ;;
    --)            shift; while [[ $# -gt 0 ]]; do TARGETS+=("$1"); shift; done ;;
    -*)            echo "unknown flag: $1" >&2; usage 1 ;;
    *)             TARGETS+=("$1"); shift ;;
  esac
done

# Gather targets from --list file (one bare module name per line, runner2.sh <LIST> format).
if [[ -n "$LIST_FILE" ]]; then
  if [[ ! -f "$LIST_FILE" ]]; then
    echo "list file not found: $LIST_FILE" >&2
    exit 1
  fi
  while IFS= read -r line; do
    line="${line%%#*}"                       # strip comments
    line="$(echo "$line" | tr -d '[:space:]')"
    [[ -n "$line" ]] && TARGETS+=("$line")
  done < "$LIST_FILE"
fi

if [[ ${#TARGETS[@]} -eq 0 ]]; then
  echo "error: no targets given (pass module names as args or via --list FILE)" >&2
  usage 1
fi

# Default git ref to the current HEAD so the request is reproducible.
if [[ -z "$GIT_REF" ]]; then
  GIT_REF="$(git rev-parse --short HEAD 2>/dev/null || echo "UNKNOWN")"
fi

JOB_ID="$(uuidgen 2>/dev/null | tr '[:upper:]' '[:lower:]' || echo "job-$(date +%s)-$$")"

# Build the targets JSON array (bare module names — no "Proofs." prefix, matching runner2.sh).
targets_json="$(
  printf '%s\n' "${TARGETS[@]}" \
    | awk 'BEGIN{printf "["} {printf "%s\"%s\"", (NR>1?",":""), $0} END{printf "]"}'
)"

REQUEST_JSON="$(cat <<EOF
{
  "job_id": "${JOB_ID}",
  "toolchain": "${TOOLCHAIN}",
  "image": "${WORKER_IMAGE}",
  "git_ref": "${GIT_REF}",
  "targets": ${targets_json},
  "per_target_timeout_s": ${PER_TARGET_TIMEOUT_S},
  "bulk_timeout_s": ${BULK_TIMEOUT_S},
  "memory_limit_mb": ${MEMORY_LIMIT_MB}
}
EOF
)"

if [[ "${REMOTE_BUILD_LIVE:-}" != "1" ]]; then
  echo "# DRY RUN (set REMOTE_BUILD_LIVE=1 and REMOTE_BUILD_ENDPOINT to submit)." >&2
  echo "# No AWS calls made; no resources created." >&2
  echo "$REQUEST_JSON"
  exit 0
fi

# --- Live submission path (opt-in only) ---------------------------------------
if [[ -z "${REMOTE_BUILD_ENDPOINT:-}" ]]; then
  echo "error: REMOTE_BUILD_LIVE=1 but REMOTE_BUILD_ENDPOINT is not set" >&2
  exit 1
fi

echo "# Submitting job ${JOB_ID} to ${REMOTE_BUILD_ENDPOINT}" >&2
curl -fsSL -X POST \
  -H 'Content-Type: application/json' \
  --data "$REQUEST_JSON" \
  "$REMOTE_BUILD_ENDPOINT"
