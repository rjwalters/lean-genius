#!/usr/bin/env bash
# resync-installed.sh - Refresh installed Anvil surfaces from the recorded source (#894 — C7).
#
# Anvil is a COPY installer: `scripts/install-anvil.sh` copies framework
# code, roles, skill bodies, and the Claude/agent registration shims from an
# Anvil source checkout into a consumer repo's `.anvil/` and `.claude/`
# trees. A fix merged to the source repo's `main` does NOT reach an
# already-installed consumer until the installer is re-run — the same class
# of drift Loom's `resync-installed.sh` (`.loom/scripts/resync-installed.sh`)
# and Repo Skills' resync command close for their own copy footprints.
#
# This script ships INTO a consumer repo at `.anvil/scripts/resync-installed.sh`
# (written by `scripts/install-anvil.sh`, mirroring this file). It is a thin,
# deliberately non-reimplementing delegator: it resolves the recorded Anvil
# source checkout, reads the currently-installed skill set from the tracked
# manifest, and re-invokes THAT source's own `scripts/install-anvil.sh`
# against the consumer repo with exactly that skill set and no `--force`.
#
# Why delegate instead of re-copying files itself (unlike Loom's resync,
# which walks defaults/ directly): `install-anvil.sh` already owns the full
# safety contract this needs —
#   * per-skill hash-tracked "consumer modified? preserve; else auto-upgrade"
#     decision (Stage 7) — reimplementing that here would either duplicate a
#     few hundred lines of tested logic or silently regress its precision;
#   * skip-if-exists writes for consumer-owned scaffolds (gitignore, themes,
#     voice docs);
#   * `--dry-run` that reports every planned write without touching disk;
#   * Stage 7.6's removed-skill prune, which by construction NEVER fires here
#     (see NEVER UNINSTALLS below).
# Re-running the installer with the SAME skill selection and no `--force` IS
# the non-destructive refresh — this script's whole job is resolving *which*
# installer to re-run and *which* skills to pass it.
#
# NEVER UNINSTALLS: the skill set passed to the re-invoked installer is read
# directly from the target's OWN `.anvil/install-metadata.json` `installed_skills`
# (the same list a bare re-run of the installer would reconcile against, per
# Stage 7.6's provenance-checked prune). Passing back exactly what was already
# installed means the prune's "previously installed, not in the current
# selection" removal condition can never be satisfied by this script.
#
# SOURCE RESOLUTION (sidecar-then-inline fallback, matching the
# `/repo:update-tools` contract documented in `.claude/commands/repo/update-tools.md`):
#   1. `.anvil/.install-local.json` (gitignored sidecar, issue #894) — `anvil_source`.
#   2. `.anvil/install-metadata.json`'s `anvil_source` field — legacy inline
#      installs that predate the #894 sidecar split still carry it there.
#   3. Neither resolves -> error (nothing to resync from; re-run the
#      installer manually from a source checkout instead).
#
# Usage:
#   ./.anvil/scripts/resync-installed.sh              # sync; report what changed
#   ./.anvil/scripts/resync-installed.sh --dry-run     # preview only; write nothing
#   ./.anvil/scripts/resync-installed.sh --quiet       # only report the summary + errors
#   ./.anvil/scripts/resync-installed.sh --help        # show this usage
#
# Exit codes:
#   0 - Success (or --dry-run with no error).
#   1 - Error (no .anvil/ install found, no manifest, no resolvable source
#       checkout, or the re-invoked installer itself exited non-zero).
set -euo pipefail

if [[ -t 1 ]]; then
  RED=$'\033[0;31m'
  GREEN=$'\033[0;32m'
  BLUE=$'\033[0;34m'
  YELLOW=$'\033[1;33m'
  NC=$'\033[0m'
else
  RED=""; GREEN=""; BLUE=""; YELLOW=""; NC=""
fi

err()  { echo "${RED}error: $*${NC}" >&2; }
info() { echo "${BLUE}> $*${NC}"; }
ok()   { echo "${GREEN}  ok: $*${NC}"; }
warn() { echo "${YELLOW}  warn: $*${NC}"; }

usage() {
  awk 'NR==1 { next } /^#/ { sub(/^# ?/, ""); print; next } { exit }' "$0"
  exit 0
}

DRY_RUN=false
QUIET=false
for arg in "$@"; do
  case "$arg" in
    --dry-run) DRY_RUN=true ;;
    --quiet|-q) QUIET=true ;;
    -h|--help) usage ;;
    *)
      err "unknown argument: $arg (try --help)"
      exit 1
      ;;
  esac
done

# ----- resolve the consumer repo root ---------------------------------------
# This script is always installed at a fixed relative location within a
# consumer install (<repo>/.anvil/scripts/resync-installed.sh), so resolve
# the repo root from the script's OWN path first -- deterministic regardless
# of the caller's cwd or git state, forge-optional (Anvil never requires git
# in the target), and immune to a stray git repo elsewhere on the invoker's
# cwd stack. Falls back to the git toplevel (for a checked-out copy of this
# file invoked standalone, e.g. under test), then the current directory.
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT=""
if [[ "$(basename "$SCRIPT_DIR")" == "scripts" && "$(basename "$(dirname "$SCRIPT_DIR")")" == ".anvil" ]]; then
  REPO_ROOT="$(dirname "$(dirname "$SCRIPT_DIR")")"
fi
if [[ -z "$REPO_ROOT" || ! -d "$REPO_ROOT/.anvil" ]]; then
  if GIT_TOP="$(git rev-parse --show-toplevel 2>/dev/null)" && [[ -d "$GIT_TOP/.anvil" ]]; then
    REPO_ROOT="$GIT_TOP"
  fi
fi
[[ -n "$REPO_ROOT" ]] || REPO_ROOT="$(pwd)"

[[ -d "$REPO_ROOT/.anvil" ]] || { err "no .anvil/ found at $REPO_ROOT -- nothing to resync (run the installer first)"; exit 1; }

MANIFEST="$REPO_ROOT/.anvil/install-metadata.json"
[[ -f "$MANIFEST" ]] || { err "no .anvil/install-metadata.json found at $REPO_ROOT -- nothing to resync"; exit 1; }

SIDECAR="$REPO_ROOT/.anvil/.install-local.json"

# ----- resolve the Anvil source checkout (sidecar -> legacy inline) --------
read_json_string_field() {
  # $1 = file, $2 = field name. Pure-bash grep/sed (no jq dependency),
  # mirroring install-anvil.sh's own manifest-parsing helpers. Flattens
  # newlines first so the parse is independent of one-line vs. pretty-printed
  # JSON; `|| true` guards the no-match branch under `set -o pipefail`.
  local file="$1" field="$2"
  [[ -f "$file" ]] || { echo ""; return; }
  tr '\n' ' ' < "$file" \
    | grep -oE "\"$field\"[[:space:]]*:[[:space:]]*\"[^\"]*\"" \
    | head -n1 \
    | sed -E "s/.*\"$field\"[[:space:]]*:[[:space:]]*\"([^\"]*)\".*/\\1/" \
    || true
}

ANVIL_SOURCE=""
SOURCE_FROM=""
if [[ -f "$SIDECAR" ]]; then
  ANVIL_SOURCE="$(read_json_string_field "$SIDECAR" "anvil_source")"
  [[ -n "$ANVIL_SOURCE" ]] && SOURCE_FROM="sidecar ($SIDECAR)"
fi
if [[ -z "$ANVIL_SOURCE" ]]; then
  # Legacy inline fallback: pre-#894 installs wrote anvil_source directly
  # into the tracked manifest.
  ANVIL_SOURCE="$(read_json_string_field "$MANIFEST" "anvil_source")"
  [[ -n "$ANVIL_SOURCE" ]] && SOURCE_FROM="legacy inline field in $MANIFEST"
fi

if [[ -z "$ANVIL_SOURCE" ]]; then
  err "could not resolve the Anvil source checkout (checked $SIDECAR and $MANIFEST)"
  err "re-run scripts/install-anvil.sh manually from a source checkout instead"
  exit 1
fi
if [[ ! -d "$ANVIL_SOURCE" ]]; then
  err "recorded Anvil source ($ANVIL_SOURCE, from $SOURCE_FROM) does not exist on this machine"
  exit 1
fi
INSTALLER="$ANVIL_SOURCE/scripts/install-anvil.sh"
[[ -f "$INSTALLER" ]] || { err "recorded Anvil source ($ANVIL_SOURCE) has no scripts/install-anvil.sh"; exit 1; }

info "resolved Anvil source: $ANVIL_SOURCE (via $SOURCE_FROM)"

# ----- resolve the currently-installed skill set ----------------------------
INSTALLED_SKILLS_BLOCK="$(tr '\n' ' ' < "$MANIFEST" \
  | grep -oE '"installed_skills"[[:space:]]*:[[:space:]]*\[[^]]*\]' \
  | head -n1)" || true

if [[ -z "$INSTALLED_SKILLS_BLOCK" ]]; then
  err "manifest at $MANIFEST has no installed_skills -- nothing to resync"
  exit 1
fi

INSTALLED_SKILLS_CSV="$(printf '%s' "$INSTALLED_SKILLS_BLOCK" \
  | sed -E 's/.*\[([^]]*)\].*/\1/' \
  | tr ',' '\n' \
  | sed -E 's/^[[:space:]]*"//; s/"[[:space:]]*$//' \
  | sed '/^$/d' \
  | paste -sd, -)"

if [[ -z "$INSTALLED_SKILLS_CSV" ]]; then
  err "manifest's installed_skills is empty -- nothing to resync"
  exit 1
fi

info "installed skill set (from manifest, unchanged by this resync): $INSTALLED_SKILLS_CSV"

# ----- re-invoke the resolved installer, non-destructively -----------------
# Never --force (preserves consumer-modified skill bodies via the existing
# hash-tracked skip logic); always passes back exactly the recorded skill
# selection (never uninstalls, see header note).
INSTALLER_ARGS=(-y "--skills=$INSTALLED_SKILLS_CSV")
$DRY_RUN && INSTALLER_ARGS+=(--dry-run)

info "running: $INSTALLER ${INSTALLER_ARGS[*]} $REPO_ROOT"

set +e
if $QUIET; then
  RESYNC_OUTPUT="$(bash "$INSTALLER" "${INSTALLER_ARGS[@]}" "$REPO_ROOT" 2>&1)"
  RESYNC_STATUS=$?
  # Quiet mode: surface only the lines that matter -- errors, warnings, the
  # per-file dry-run preview, and the Stage 11 summary block.
  printf '%s\n' "$RESYNC_OUTPUT" | grep -E \
    'error:|warn:|\[dry-run\]|^  (installed skills|would install|skipped overrides|would skip|target|would target):' \
    || true
else
  bash "$INSTALLER" "${INSTALLER_ARGS[@]}" "$REPO_ROOT"
  RESYNC_STATUS=$?
fi
set -e

if [[ "$RESYNC_STATUS" -ne 0 ]]; then
  err "the re-invoked installer exited non-zero ($RESYNC_STATUS)"
  exit 1
fi

if $DRY_RUN; then
  ok "dry-run complete -- no files were written"
else
  ok "resync complete"
fi
exit 0
