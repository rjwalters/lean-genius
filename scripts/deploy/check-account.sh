#!/bin/bash
#
# check-account.sh - Verify wrangler is authenticated to the correct Cloudflare account
#
# This prevents accidental deployments to the wrong account.
# The lean-genius site must deploy to the Personal Account.
#
# Usage:
#   ./scripts/deploy/check-account.sh        # Exits 0 if correct, 1 if wrong
#   ./scripts/deploy/check-account.sh --help # Show expected account details
#   source scripts/deploy/check-account.sh   # Can be sourced by other scripts

set -euo pipefail

EXPECTED_ACCOUNT_ID="251e6e8626d921603fdc3f0d75576bc6"
EXPECTED_ACCOUNT_NAME="Personal Account"
EXPECTED_EMAIL="r.j.walters@gmail.com"

usage() {
    cat <<EOF
Usage: ./scripts/deploy/check-account.sh

Verify wrangler is authenticated to the Cloudflare account used for
lean-genius deployments.

Expected account:
  Name:  $EXPECTED_ACCOUNT_NAME
  Email: $EXPECTED_EMAIL
  ID:    $EXPECTED_ACCOUNT_ID

Options:
  --help, -h  Show this help message without running wrangler
EOF
}

case "${1:-}" in
    --help|-h)
        usage
        exit 0
        ;;
    "")
        ;;
    *)
        echo "Unknown option: $1" >&2
        usage >&2
        exit 1
        ;;
esac

# Get current wrangler account
if [[ -n "${WRANGLER_WHOAMI_OUTPUT:-}" ]]; then
    WHOAMI_OUTPUT="$WRANGLER_WHOAMI_OUTPUT"
else
    WHOAMI_OUTPUT=$(wrangler whoami 2>&1) || {
        echo "ERROR: wrangler whoami failed. Are you logged in?" >&2
        echo "  Run: wrangler login" >&2
        exit 1
    }
fi

CURRENT_ACCOUNT_ID=$(echo "$WHOAMI_OUTPUT" | grep -oE '[a-f0-9]{32}' | head -1)
CURRENT_EMAIL=$(echo "$WHOAMI_OUTPUT" | grep -oE 'associated with the email [^ ]+' | sed 's/associated with the email //; s/[[:punct:]]$//')

if [[ "$CURRENT_ACCOUNT_ID" != "$EXPECTED_ACCOUNT_ID" ]]; then
    echo "============================================================" >&2
    echo "  DEPLOY BLOCKED: Wrong Cloudflare account!" >&2
    echo "============================================================" >&2
    echo "" >&2
    echo "  Current:  $CURRENT_EMAIL ($CURRENT_ACCOUNT_ID)" >&2
    echo "  Expected: $EXPECTED_EMAIL ($EXPECTED_ACCOUNT_ID)" >&2
    echo "" >&2
    echo "  Fix: wrangler login  (then select Personal Account)" >&2
    echo "============================================================" >&2
    exit 1
fi

echo "✓ Cloudflare account verified: $EXPECTED_EMAIL"
