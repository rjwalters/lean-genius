#!/usr/bin/env bash
# Install e85-remote on the Mac: copies the wrapper + host tooling into
# ~/.local/share/e85-remote and links ~/.local/bin/e85-remote (already on PATH here).
# Re-run after pulling changes to this directory.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
DEST=${E85_REMOTE_HOME:-$HOME/.local/share/e85-remote}
BIN=${E85_REMOTE_BIN:-$HOME/.local/bin}
mkdir -p "$DEST" "$BIN"
install -m 755 "$HERE/e85-remote" "$HERE/e85-host.sh" "$HERE/e85-watchdog.sh" "$DEST/"
install -m 755 "$HERE/../../../../proofs/scripts/docker-build.sh" "$DEST/docker-build.sh"
ln -sf "$DEST/e85-remote" "$BIN/e85-remote"
[[ -f "$HOME/.ssh/e85-lean-builder" ]] || echo "NOTE: SSH key ~/.ssh/e85-lean-builder missing (the private half of EC2 key pair e85-lean-builder)"
command -v session-manager-plugin >/dev/null || echo "NOTE: install the SSM plugin: brew install --cask session-manager-plugin"
echo "installed: $BIN/e85-remote -> $DEST/e85-remote"
