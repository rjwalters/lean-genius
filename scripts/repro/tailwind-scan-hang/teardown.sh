#!/usr/bin/env bash
#
# Teardown for the synthetic Tailwind v4 oxide scan-hang fixture.
# See setup.sh and issue #21009.

set -euo pipefail

ROOT="$(git rev-parse --show-toplevel)"
FIXTURE_ROOT="${ROOT}/tmp-tailwind-repro"

if [[ ! -d "${FIXTURE_ROOT}" ]]; then
  echo "Nothing to remove: ${FIXTURE_ROOT} does not exist."
  exit 0
fi

if [[ ! -f "${FIXTURE_ROOT}/.fixture-marker" ]]; then
  echo "Refusing to remove ${FIXTURE_ROOT}: missing .fixture-marker." >&2
  echo "This directory does not appear to be a synthetic fixture." >&2
  exit 1
fi

echo "Removing fixture root ${FIXTURE_ROOT}..."
rm -rf "${FIXTURE_ROOT}"
echo "Done."
