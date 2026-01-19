# Lean Genius Makefile
# Convenience aliases for common development tasks

.PHONY: help clean clean-all clean-enhancers clean-research clean-loom \
        status status-enhancers status-research \
        build test lint \
        enhance research \
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
	@echo ""
	@echo "Build:"
	@echo "  make build            - Build the project (pnpm build)"
	@echo "  make test             - Run tests"
	@echo "  make lint             - Run linter"
	@echo ""
	@echo "Agents:"
	@echo "  make enhance N=3      - Launch N parallel enhancer agents"
	@echo "  make research N=2     - Launch N parallel research agents"
	@echo ""
	@echo "Options:"
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

status: status-enhancers status-research

status-enhancers:
	@echo ""
	./scripts/erdos/claim-stub.sh status

status-research:
	@echo ""
	./scripts/research/claim-problem.sh status

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

research:
	./scripts/research/parallel-research.sh $(N)
