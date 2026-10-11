#!/usr/bin/env bash
# Fetch the 13 packed LRAT certificates read (via include_str) by
# proofs/Proofs/Erdos85OrderFortyNineSevenHighT*Rep*Certificate.lean into
# proofs/Proofs/Certificates/strata-lrat/, and verify each against
# proofs/Proofs/Certificates/strata-lrat.MANIFEST.sha256.
#
# The files (2,574,916,357 bytes in all) are public in a Requester Pays S3 bucket:
# the requester pays the transfer. Use valid AWS credentials with permission
# for Requester Pays S3 downloads, e.g.
#   AWS_PROFILE=<yours> proofs/scripts/fetch-h7-certificates.sh
# Inside AWS us-east-1 the transfer is free of data-transfer charges.
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"     # proofs/
dest="$here/Proofs/Certificates/strata-lrat"
manifest="$here/Proofs/Certificates/strata-lrat.MANIFEST.sha256"
src="s3://2am-erdos85-certs/public/erdos85-h7-positive-triple-lrat"
mkdir -p "$dest"
sha() { if command -v sha256sum >/dev/null; then sha256sum "$1" | cut -d' ' -f1; else shasum -a 256 "$1" | cut -d' ' -f1; fi; }
fail=0
while read -r want name; do
  [ -n "$name" ] || continue
  f="$dest/$name"
  if [ ! -f "$f" ] || [ "$(sha "$f")" != "$want" ]; then
    aws s3 cp --only-show-errors --request-payer requester "$src/$name" "$f"
  fi
  got="$(sha "$f")"
  if [ "$got" = "$want" ]; then echo "OK   $name"; else echo "BAD  $name ($got)"; fail=1; fi
done < "$manifest"
exit $fail
