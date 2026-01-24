# Lean Genius Makefile
# Convenience aliases for common development tasks

.DEFAULT_GOAL := help

.PHONY: help clean clean-all clean-enhancers clean-research clean-loom \
        status status-enhancers status-research status-aristotle \
        build test lint \
        enhance research aristotle aristotle-loop \
        deploy deployer deployer-stop deployer-attach deployer-logs deployer-status \
        restart-all restart-research restart-deployer restart-aristotle restart-enhancers \
        continue pause stop signals \
        prune

# Default target
help:
	@echo "Lean Genius - Development Commands"
	@echo ""
	@echo "Cleanup:"
	@echo "  make clean            - Run all cleanup scripts (dry-run)"
	@echo "  make clean-all        - Run all cleanup scripts (deep, force)"
	@echo "  make clean-enhancers  - Clean enhancement agent artifacts"
	@echo "  make clean-research   - Clean research agent artifacts"
	@echo "  make clean-loom       - Clean loom worktrees and branches"
	@echo "  make prune            - Prune git worktrees and remote branches"
	@echo ""
	@echo "Status:"
	@echo "  make status           - Show all agent claim status"
	@echo "  make status-enhancers - Show enhancement claims"
	@echo "  make status-research  - Show research claims"
	@echo "  make status-aristotle - Show Aristotle job status"
	@echo ""
	@echo "Build:"
	@echo "  make build            - Build the project (pnpm build)"
	@echo "  make test             - Run tests"
	@echo "  make lint             - Run linter"
	@echo ""
	@echo "Agents:"
	@echo "  make enhance N=3      - Launch N parallel enhancer agents"
	@echo "  make research N=2     - Launch N parallel research agents (WAIT=15 for retry interval)"
	@echo "  make aristotle        - Launch Aristotle queue management agent"
	@echo ""
	@echo "Deploy:"
	@echo "  make deploy           - Run deploy pipeline once (merge PRs, sync, build, deploy)"
	@echo "  make deployer         - Launch autonomous deployer agent (default 30min interval)"
	@echo "  make deployer-stop    - Stop the deployer agent"
	@echo "  make deployer-attach  - Attach to deployer session"
	@echo "  make deployer-logs    - Tail deployer logs"
	@echo "  make deployer-status  - Check deployer status"
	@echo ""
	@echo "Signals:"
	@echo "  make continue         - Signal all agents to continue work"
	@echo "  make pause            - Signal all agents to pause"
	@echo "  make stop             - Signal all agents to stop gracefully"
	@echo "  make signals          - Show current signal status"
	@echo ""
	@echo "Restart (relaunch stopped agents):"
	@echo "  make restart-all      - Restart all stopped agents"
	@echo "  make restart-research - Restart research agents if stopped"
	@echo "  make restart-deployer - Restart deployer if stopped"
	@echo "  make restart-aristotle - Restart aristotle if stopped"
	@echo "  make restart-enhancers - Restart enhancer agents if stopped"
	@echo ""
	@echo "Options:
	@echo "  DEEP=1    - Enable deep cleaning (worktrees, branches, logs)"
	@echo "  FORCE=1   - Non-interactive mode"
	@echo "  DRY=1     - Dry-run mode (show what would be done)"

# ============================================================================
# Cleanup targets
# ============================================================================

# Build cleanup flags from environment
CLEAN_FLAGS :=
ifdef DRY
CLEAN_FLAGS += --dry-run
endif
ifdef DEEP
CLEAN_FLAGS += --deep
endif
ifdef FORCE
CLEAN_FLAGS += --force
endif

clean:
	@echo "=== Cleanup Preview (add DEEP=1 FORCE=1 to execute) ==="
	./scripts/erdos/clean-enhancers.sh --dry-run
	./scripts/research/clean-research.sh --dry-run
	./.loom/scripts/clean.sh --dry-run

clean-all:
	@echo "=== Deep Cleanup (all agents) ==="
	./scripts/erdos/clean-enhancers.sh --deep --force
	./scripts/research/clean-research.sh --deep --force
	./.loom/scripts/clean.sh --deep --force

clean-enhancers:
	./scripts/erdos/clean-enhancers.sh $(CLEAN_FLAGS)

clean-research:
	./scripts/research/clean-research.sh $(CLEAN_FLAGS)

clean-loom:
	./.loom/scripts/clean.sh $(CLEAN_FLAGS)

prune:
	@echo "=== Pruning git worktrees ==="
	git worktree prune --verbose
	@echo ""
	@echo "=== Pruning remote tracking branches ==="
	git fetch --prune

# ============================================================================
# Status targets
# ============================================================================

status: status-enhancers status-research status-aristotle

status-enhancers:
	@echo ""
	./scripts/erdos/claim-stub.sh status

status-research:
	@echo ""
	./scripts/research/claim-problem.sh status

status-aristotle:
	@echo ""
	./scripts/aristotle/aristotle-agent.sh --status

# ============================================================================
# Build targets
# ============================================================================

build:
	pnpm build

test:
	pnpm test

lint:
	pnpm lint

# ============================================================================
# Agent launch targets
# ============================================================================

# Default agent counts
N ?= 3

enhance:
	./scripts/erdos/parallel-enhance.sh $(N)

# WAIT defaults to 15 minutes (when no work available)
WAIT ?= 15

research:
	RESEARCHER_WAIT_INTERVAL=$(WAIT) ./scripts/research/parallel-research.sh $(N)

# Aristotle agent (maintains ~20 active proof search jobs)
# TARGET defaults to 20, INTERVAL defaults to 30 minutes
TARGET ?= 20
INTERVAL ?= 30

aristotle:
	ARISTOTLE_TARGET=$(TARGET) ARISTOTLE_INTERVAL=$(INTERVAL) ./scripts/aristotle/launch-agent.sh

aristotle-stop:
	./scripts/aristotle/launch-agent.sh --stop

aristotle-attach:
	./scripts/aristotle/launch-agent.sh --attach

aristotle-logs:
	./scripts/aristotle/launch-agent.sh --logs

# ============================================================================
# Deploy targets
# ============================================================================

# Run deploy pipeline once (manual)
deploy:
	./scripts/deploy/sync-and-deploy.sh

# Deployer agent (merges PRs, syncs data, builds, deploys)
# INTERVAL defaults to 30 minutes
deployer:
	DEPLOYER_INTERVAL=$(INTERVAL) ./scripts/deploy/launch-agent.sh

deployer-stop:
	./scripts/deploy/launch-agent.sh --stop

deployer-attach:
	./scripts/deploy/launch-agent.sh --attach

deployer-logs:
	./scripts/deploy/launch-agent.sh --logs

deployer-status:
	./scripts/deploy/launch-agent.sh --status

# ============================================================================
# Signal management targets
# ============================================================================

continue:
	@./scripts/agents/signal.sh continue

pause:
	@./scripts/agents/signal.sh pause

stop:
	@./scripts/agents/signal.sh stop

signals:
	@./scripts/agents/signal.sh status

# ============================================================================
# Restart targets (relaunch stopped agents)
# ============================================================================

# Restart all stopped agents
restart-all: restart-deployer restart-aristotle restart-research restart-enhancers
	@echo "All agents checked and restarted if needed."

# Helper: check if claude is actively running in a tmux session
# Returns 0 if idle (needs restart), 1 if active
define check_agent_idle
	@tmux has-session -t $(1) 2>/dev/null && \
		! tmux list-panes -t $(1) -F '#{pane_pid}' | xargs -I{} ps -p {} -o command= 2>/dev/null | grep -q claude
endef

# Restart research agents if not running or idle
restart-research:
	@if ! tmux has-session -t researcher-1 2>/dev/null || \
		! (tmux list-panes -t researcher-1 -F '#{pane_pid}' | xargs -I{} ps -p {} -o command= 2>/dev/null | grep -q claude); then \
		echo "Restarting research agents..."; \
		./scripts/research/parallel-research.sh --stop 2>/dev/null || true; \
		sleep 1; \
		RESEARCHER_WAIT_INTERVAL=$(WAIT) ./scripts/research/parallel-research.sh $(N); \
	else \
		echo "Research agents actively running."; \
	fi

# Restart deployer if not running or idle
restart-deployer:
	@if ! tmux has-session -t deployer 2>/dev/null || \
		! (tmux list-panes -t deployer -F '#{pane_pid}' | xargs -I{} ps -p {} -o command= 2>/dev/null | grep -q claude); then \
		echo "Restarting deployer..."; \
		./scripts/deploy/launch-agent.sh --stop 2>/dev/null || true; \
		sleep 1; \
		DEPLOYER_INTERVAL=$(INTERVAL) ./scripts/deploy/launch-agent.sh; \
	else \
		echo "Deployer actively running."; \
	fi

# Restart aristotle if not running or idle
restart-aristotle:
	@if ! tmux has-session -t aristotle-agent 2>/dev/null || \
		! (tmux list-panes -t aristotle-agent -F '#{pane_pid}' | xargs -I{} ps -p {} -o command= 2>/dev/null | grep -q claude); then \
		echo "Restarting aristotle..."; \
		./scripts/aristotle/launch-agent.sh --stop 2>/dev/null || true; \
		sleep 1; \
		ARISTOTLE_TARGET=$(TARGET) ARISTOTLE_INTERVAL=$(INTERVAL) ./scripts/aristotle/launch-agent.sh; \
	else \
		echo "Aristotle actively running."; \
	fi

# Restart enhancers if not running or idle (checks enhancer-1 as proxy)
restart-enhancers:
	@if ! tmux has-session -t erdos-enhancer-1 2>/dev/null || \
		! (tmux list-panes -t erdos-enhancer-1 -F '#{pane_pid}' | xargs -I{} ps -p {} -o command= 2>/dev/null | grep -q claude); then \
		echo "Restarting enhancer agents..."; \
		./scripts/erdos/parallel-enhance.sh --stop 2>/dev/null || true; \
		sleep 1; \
		./scripts/erdos/parallel-enhance.sh $(N); \
	else \
		echo "Enhancer agents actively running."; \
	fi
