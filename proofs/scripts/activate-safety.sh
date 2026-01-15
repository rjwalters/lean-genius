#!/bin/bash
# Activate the lake build safety wrapper
#
# Usage: source ./proofs/scripts/activate-safety.sh
#
# This adds proofs/bin to your PATH, which contains a wrapper script
# that intercepts 'lake build' and redirects to the safe Docker wrapper.

# Find the project root
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$(dirname "$SCRIPT_DIR")")"

# Add safety wrapper to PATH
export PATH="$PROJECT_ROOT/proofs/bin:$PATH"

echo "Safety wrapper activated."
echo ""
echo "  'lake build' is now intercepted and will show safe alternatives."
echo "  Use './proofs/scripts/docker-build.sh' for builds."
echo ""
echo "To deactivate, start a new shell or run:"
echo "  export PATH=\"\${PATH#$PROJECT_ROOT/proofs/bin:}\""
