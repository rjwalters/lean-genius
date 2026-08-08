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

# Pinned as a SHA-256 digest, not a literal: this is a public repo and an
# account identifier does not need publishing. Reading it from the
# environment would be weaker -- the guard exists to catch a wrong account
# that is already logged in, so an expectation the environment can move is
# one a wrong environment moves with it. 128 bits of hex, so not brute-forceable.
EXPECTED_ACCOUNT_ID_SHA256="04e8eb2a99d37a555c87220b1d4cd1c018afbe5b65360bdd2224eb8e9f6b69c2"
EXPECTED_ACCOUNT_NAME="Personal Account"

# Portable sha256 (sha256sum on Linux, shasum on macOS).
sha256_of() {
    if command -v sha256sum >/dev/null 2>&1; then
        printf '%s' "$1" | sha256sum | awk '{print $1}'
    elif command -v shasum >/dev/null 2>&1; then
        printf '%s' "$1" | shasum -a 256 | awk '{print $1}'
    else
        echo "ERROR: neither sha256sum nor shasum found - cannot verify account." >&2
        exit 1
    fi
}

usage() {
    cat <<EOF
Usage: ./scripts/deploy/check-account.sh

Verify wrangler is authenticated to the Cloudflare account used for
lean-genius deployments.

Expected account:
  Name:      $EXPECTED_ACCOUNT_NAME
  ID sha256: $EXPECTED_ACCOUNT_ID_SHA256

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

CURRENT_ACCOUNT_SHA256=$(sha256_of "$CURRENT_ACCOUNT_ID")

if [[ "$CURRENT_ACCOUNT_SHA256" != "$EXPECTED_ACCOUNT_ID_SHA256" ]]; then
    echo "============================================================" >&2
    echo "  DEPLOY BLOCKED: Wrong Cloudflare account!" >&2
    echo "============================================================" >&2
    echo "" >&2
    echo "  Current  sha256: ${CURRENT_ACCOUNT_SHA256:0:12}..." >&2
    echo "  Expected sha256: ${EXPECTED_ACCOUNT_ID_SHA256:0:12}..." >&2
    echo "" >&2
    echo "  Fix: wrangler login  (then select Personal Account)" >&2
    echo "============================================================" >&2
    exit 1
fi

echo "✓ Cloudflare account verified: $EXPECTED_ACCOUNT_NAME"
