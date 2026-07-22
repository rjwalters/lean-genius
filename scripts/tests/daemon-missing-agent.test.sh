#!/bin/bash
# Isolated harness for the configured-but-missing-session detection added to
# scripts/lean/launch.sh (issue #39652).
#
# Background: the lean daemon had `deployer: 1` in its config yet no deployer
# tmux session existed for ~7 days, and nothing surfaced it -- `/lean health`
# just omitted the row and the daemon log stayed silent. These tests exercise
# the new helpers that make a persistent absence VISIBLE:
#   - count_agent_sessions    : live tmux sessions per agent type
#   - print_missing_agent_rows: red MISSING rows in `/lean health`
#   - get/set_missing_cycles  : consecutive-cycle escalation counter
#   - write_missing_agents    : persists the missing set into STATE_FILE
# plus a replica of the daemon's detection loop showing that a WARN fires only
# after MISSING_SESSION_ALERT_CYCLES consecutive absent cycles (no false alarm
# for a normally-running agent).
#
# Run: bash scripts/tests/daemon-missing-agent.test.sh
# Exits non-zero if any assertion fails.
set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LAUNCH="$SCRIPT_DIR/../lean/launch.sh"

# --- Fake tmux -------------------------------------------------------------
# FAKE_SESSIONS is a space-separated list of "live" session names. The launch.sh
# helpers only depend on `tmux has-session -t <name>`; everything else is a
# no-op success.
FAKE_SESSIONS=""
tmux() {
    case "${1:-}" in
        has-session)
            local name="${3:-}"
            local s
            for s in $FAKE_SESSIONS; do
                [[ "$s" == "$name" ]] && return 0
            done
            return 1
            ;;
        *)
            return 0
            ;;
    esac
}

# Source launch.sh WITHOUT running main (source guard added in #39652).
# shellcheck source=../lean/launch.sh
source "$LAUNCH"

# Redirect state to a throwaway sandbox so we never touch real daemon state.
SANDBOX="$(mktemp -d)"
trap 'rm -rf "$SANDBOX"' EXIT
STATE_FILE="$SANDBOX/lean-daemon-state.json"
ARISTOTLE_SCALED_MARKER="$SANDBOX/aristotle-scaled-to-zero"
DAEMON_LOG_FILE="$SANDBOX/daemon.log"

# Strip ANSI color codes so assertions match plain text.
strip_ansi() { sed $'s/\x1b\\[[0-9;]*m//g'; }

PASS=0
FAIL=0
ok()   { echo "  ok: $1"; PASS=$((PASS + 1)); }
bad()  { echo "  FAIL: $1"; FAIL=$((FAIL + 1)); }

assert_contains() { # <desc> <haystack> <needle>
    if printf '%s' "$2" | grep -qF -- "$3"; then ok "$1"; else
        bad "$1 -- expected to contain: $3"
        printf '        got: %s\n' "$2"
    fi
}
assert_not_contains() { # <desc> <haystack> <needle>
    if printf '%s' "$2" | grep -qF -- "$3"; then
        bad "$1 -- expected NOT to contain: $3"
        printf '        got: %s\n' "$2"
    else ok "$1"; fi
}
assert_eq() { # <desc> <actual> <expected>
    if [[ "$2" == "$3" ]]; then ok "$1"; else
        bad "$1 -- expected '$3', got '$2'"
    fi
}

write_state() { # <deployer_cfg> <researcher_cfg>
    cat > "$STATE_FILE" <<EOF
{ "config": { "deployer": $1, "researcher": $2, "enricher": 0, "aristotle": 0,
  "auditor": 0, "seeker": 0, "herald": 0, "mechanic": 0, "tester": 0 } }
EOF
}

echo "== count_agent_sessions =="
FAKE_SESSIONS=""
assert_eq "deployer absent -> 0" "$(count_agent_sessions deployer)" "0"
FAKE_SESSIONS="deployer"
assert_eq "deployer present -> 1" "$(count_agent_sessions deployer)" "1"
FAKE_SESSIONS="researcher-1 researcher-3"
assert_eq "two researchers present -> 2" "$(count_agent_sessions researcher)" "2"

# Run print_missing_agent_rows directly in the current shell (redirect to a
# file, NOT a pipe or $() subshell) so its MISSING_AGENTS_FOUND global survives;
# read the rendered rows back from the file afterwards.
echo "== print_missing_agent_rows: configured deployer, no session =="
write_state 1 0
FAKE_SESSIONS=""
print_missing_agent_rows > "$SANDBOX/rows.txt"
out="$(strip_ansi < "$SANDBOX/rows.txt")"
assert_contains "renders a MISSING deployer row" "$out" "MISSING"
assert_contains "shows configured:1 running:0" "$out" "configured:1 running:0"
assert_eq "MISSING_AGENTS_FOUND == 1" "$MISSING_AGENTS_FOUND" "1"

echo "== print_missing_agent_rows: no false alarm when running =="
write_state 1 0
FAKE_SESSIONS="deployer"
print_missing_agent_rows > "$SANDBOX/rows.txt"
out="$(strip_ansi < "$SANDBOX/rows.txt")"
assert_not_contains "no MISSING row when deployer runs" "$out" "MISSING"
assert_eq "MISSING_AGENTS_FOUND == 0" "$MISSING_AGENTS_FOUND" "0"

echo "== print_missing_agent_rows: not-configured agent is never MISSING =="
write_state 0 0
FAKE_SESSIONS=""
print_missing_agent_rows >/dev/null
assert_eq "config all zero -> 0 missing" "$MISSING_AGENTS_FOUND" "0"

echo "== write_missing_agents persists to STATE_FILE =="
write_state 1 0
write_missing_agents '[{"type":"deployer","configured":1,"running":0,"missing_cycles":3}]'
persisted="$(jq -r '.missing_agents[0].type' "$STATE_FILE")"
assert_eq "missing_agents[0].type == deployer" "$persisted" "deployer"
cyc="$(jq -r '.missing_agents[0].missing_cycles' "$STATE_FILE")"
assert_eq "missing_agents[0].missing_cycles == 3" "$cyc" "3"

echo "== cmd_health surfaces MISSING when the whole pool is dead =="
write_state 1 0
FAKE_SESSIONS=""   # get_all_agent_sessions returns empty -> empty-branch path
health_out="$(cmd_health 2>/dev/null | strip_ansi)"
assert_contains "health shows MISSING deployer row" "$health_out" "MISSING"
assert_contains "health shows configured:1 running:0" "$health_out" "configured:1 running:0"

echo "== daemon detection loop: WARN only after N consecutive absent cycles =="
# Replicate the escalation the daemon cycle performs for one agent type.
write_state 1 0
set_missing_cycles deployer 0
warned=""
simulate_cycle() { # <active> <target>
    local mactive="$1" mtarget="$2" mc
    if [[ "$mactive" -lt "$mtarget" ]]; then
        mc=$(get_missing_cycles deployer); mc=$((mc + 1)); set_missing_cycles deployer "$mc"
        if [[ "$mc" -ge "$MISSING_SESSION_ALERT_CYCLES" ]]; then
            daemon_log "WARN" "Agent 'deployer' MISSING: configured=$mtarget running=$mactive for $mc consecutive cycles" >> "$DAEMON_LOG_FILE"
            warned=yes
        fi
    else
        set_missing_cycles deployer 0
    fi
}
assert_eq "threshold default is 3" "$MISSING_SESSION_ALERT_CYCLES" "3"
warned=""; : > "$DAEMON_LOG_FILE"
simulate_cycle 0 1   # cycle 1
assert_eq "cycle 1: no warn yet" "$warned" ""
simulate_cycle 0 1   # cycle 2
assert_eq "cycle 2: no warn yet" "$warned" ""
simulate_cycle 0 1   # cycle 3 -> threshold
assert_eq "cycle 3: warn fired" "$warned" "yes"
assert_contains "daemon log has WARN MISSING" "$(cat "$DAEMON_LOG_FILE")" "WARN: Agent 'deployer' MISSING"

echo "== a single mid-respawn cycle does not false-alarm, and recovery resets =="
set_missing_cycles deployer 0
warned=""
simulate_cycle 0 1   # absent one cycle
simulate_cycle 1 1   # came back -> reset
assert_eq "one absent cycle then recovery: no warn" "$warned" ""
assert_eq "counter reset to 0 after recovery" "$(get_missing_cycles deployer)" "0"

echo ""
echo "Results: $PASS passed, $FAIL failed"
[[ "$FAIL" -eq 0 ]]
