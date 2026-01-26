# Lean Genius

Lean Genius is a formal mathematics project that formalizes mathematical theorems and problems (including Erdős problems) in Lean 4 and presents them in an interactive web gallery.

## Two Orchestration Systems

This project uses **two distinct AI agent orchestration systems** for different purposes:

### 1. Loom (Development Orchestration)

**Purpose**: Software development workflow - building features, reviewing PRs, managing issues.

| Agent | Purpose | Mode |
|-------|---------|------|
| **Builder** | Implements features and fixes | Manual |
| **Judge** | Reviews pull requests | Autonomous (5min) |
| **Curator** | Enhances and organizes issues | Autonomous (5min) |
| **Architect** | Creates architectural proposals | Autonomous (15min) |
| **Hermit** | Identifies simplification opportunities | Autonomous (15min) |
| **Doctor** | Fixes bugs and PR feedback | Manual |
| **Guide** | Prioritizes and triages issues | Autonomous (15min) |

**Invoke via**: `/builder`, `/judge`, `/curator`, etc.

### 2. Lean Genius Mathematical Orchestration

**Purpose**: Mathematical work - formalizing proofs, enhancing problem entries, running automated proof search.

| Agent | Purpose | Mode |
|-------|---------|------|
| **Erdős Enhancer** | Enhances Erdős problem stubs with Lean formalizations | Autonomous |
| **Aristotle** | Manages queue of proofs for Aristotle proof search system | Autonomous |
| **Researcher** | Works on open mathematical problems, proves theorems | Autonomous |
| **Deployer** | Merges PRs, syncs data, deploys website to Cloudflare | Autonomous (30min) |

**Invoke via**: `/erdos`, `/aristotle`, `/research`, `/deploy`

**Team orchestration**: `/lean` - Start/stop/scale the full mathematical agent team

### When to Use Which

- **Writing code, fixing bugs, reviewing PRs** → Use Loom agents (Builder, Judge, etc.)
- **Formalizing math, proving theorems, enhancing Erdős problems** → Use Lean Genius agents (Erdős, Aristotle, Researcher)
- **Deploying the website** → Use Deployer
- **Starting the full mathematical team** → Use `/lean`

---

# /lean - Mathematical Team Orchestration

The `/lean` skill provides a unified interface to start, stop, and scale the mathematical agent team.

## Quick Start

```bash
# Start with defaults (2 erdos, 1 aristotle, 1 researcher, 1 deployer)
/lean

# Start with custom pool sizes
/lean start --erdos 3 --researcher 2

# Check status
/lean status

# Stop all agents
/lean stop
```

## Commands

| Command | Description |
|---------|-------------|
| `/lean` | Start daemon with default pool |
| `/lean status` | Show work queue and agent status |
| `/lean start [options]` | Start with custom pool sizes |
| `/lean spawn <type>` | Add one agent (erdos, aristotle, researcher, deployer) |
| `/lean scale <type> <N>` | Scale pool to N agents |
| `/lean stop` | Graceful shutdown of all agents |

## Pool Limits

| Agent | Default | Max |
|-------|---------|-----|
| Erdős Enhancer | 2 | 5 |
| Aristotle | 1 | 2 |
| Researcher | 1 | 3 |
| Deployer | 1 | 1 |

## Helper Scripts

```bash
# Status (also works outside /lean skill)
./scripts/lean/status.sh
./scripts/lean/status.sh --json

# Launch/stop (also works outside /lean skill)
./scripts/lean/launch.sh start --erdos 2
./scripts/lean/launch.sh stop
./scripts/lean/launch.sh spawn erdos
./scripts/lean/launch.sh scale erdos 3
```

---

<!-- BEGIN LOOM ORCHESTRATION -->
# Loom Development Orchestration

**Loom Version**: 0.2.0
**Loom Commit**: 7eed7c6
**Installation Date**: 2026-01-24

## What is Loom?

Loom is a multi-terminal desktop application for macOS that orchestrates AI-powered development workers using git worktrees and GitHub as the coordination layer. It enables both automated orchestration (Tauri App Mode) and manual coordination (Manual Orchestration Mode).

**Loom Repository**: https://github.com/loomhq/loom

## Usage Modes

Loom supports two complementary workflows:

### 1. Manual Orchestration Mode (MOM)

Use Claude Code terminals with specialized roles for hands-on development coordination.

**Setup**:
1. Open Claude Code in this repository
2. Use slash commands to assume roles: `/builder`, `/judge`, `/curator`, etc.
3. Each terminal acts as a specialized agent following role guidelines

**When to use MOM**:
- Learning Loom workflows
- Direct control over agent actions
- Debugging and iterating on processes
- Working with smaller teams

**Example workflow**:
```bash
# Terminal 1: Builder working on feature
/builder
# Claims loom:ready issue, implements, creates PR

# Terminal 2: Judge reviewing PRs
/judge
# Reviews PR with loom:review-requested, provides feedback

# Terminal 3: Curator maintaining issues
/curator
# Enhances unlabeled issues, marks as loom:ready
```

### 2. Tauri App Mode

Launch the Loom desktop application for automated orchestration with visual terminal management.

**Setup**:
1. Install Loom app (see main repository for download)
2. Open Loom application
3. Select this repository as workspace
4. Configure terminals with roles and intervals
5. Start engine - terminals launch automatically

**When to use Tauri App**:
- Production-scale development
- Fully autonomous agent workflows
- Visual monitoring of multiple agents
- Hands-off orchestration

**Features**:
- Visual terminal multiplexing
- Real-time agent monitoring
- Autonomous mode with configurable intervals
- Persistent workspace configuration

## Agent Roles

Loom provides specialized roles for different development tasks. Each role follows specific guidelines and uses GitHub labels for coordination.

### Available Roles

**Builder** (Manual, `builder.md`)
- **Purpose**: Implement features and fixes
- **Workflow**: Claims `loom:issue` → implements → tests → creates PR with `loom:review-requested`
- **When to use**: Feature development, bug fixes, refactoring

**Judge** (Autonomous 5min, `judge.md`)
- **Purpose**: Review pull requests
- **Workflow**: Finds `loom:review-requested` PRs → reviews → approves or requests changes
- **When to use**: Code quality assurance, automated reviews

**Curator** (Autonomous 5min, `curator.md`)
- **Purpose**: Enhance and organize issues
- **Workflow**: Finds unlabeled issues → adds context → marks as `loom:issue`
- **When to use**: Issue backlog maintenance, quality improvement

**Architect** (Autonomous 15min, `architect.md`)
- **Purpose**: Create architectural proposals
- **Workflow**: Analyzes codebase → creates proposal issues with `loom:architect`
- **When to use**: System design, technical decision making

**Hermit** (Autonomous 15min, `hermit.md`)
- **Purpose**: Identify code simplification opportunities
- **Workflow**: Analyzes complexity → creates removal proposals with `loom:hermit`
- **When to use**: Code simplification, reducing technical debt

**Doctor** (Manual, `doctor.md`)
- **Purpose**: Fix bugs and address PR feedback
- **Workflow**: Claims bug reports or addresses PR comments → fixes → pushes changes
- **When to use**: Bug fixes, PR maintenance

**Guide** (Autonomous 15min, `guide.md`)
- **Purpose**: Prioritize and triage issues
- **Workflow**: Reviews issue backlog → updates priorities → organizes labels
- **When to use**: Project planning, issue organization

**Driver** (Manual, `driver.md`)
- **Purpose**: Direct command execution
- **Workflow**: Plain shell environment for custom tasks
- **When to use**: Ad-hoc tasks, debugging, manual operations

### Role Definitions

Full role definitions with detailed guidelines are available in:
- `.loom/roles/builder.md`
- `.loom/roles/judge.md`
- `.loom/roles/curator.md`
- And more...

## Label-Based Workflow

Agents coordinate work through GitHub labels. This enables autonomous operation without direct communication.

### Label Flow

**Issue Lifecycle**:
```
(created) → loom:issue → loom:building → (closed)
           ↑ Curator      ↑ Builder
```

**PR Lifecycle**:
```
(created) → loom:review-requested → loom:pr → (merged)
           ↑ Builder                ↑ Judge    ↑ Human
```

**Proposal Lifecycle**:
```
(created) → loom:architect → (approved) → loom:issue
           ↑ Architect       ↑ Human      ↑ Ready for Builder

(created) → loom:hermit → (approved) → loom:issue
           ↑ Hermit       ↑ Human      ↑ Ready for Builder
```

### Label Definitions

- **`loom:issue`**: Issue approved for work, ready for Builder to claim
- **`loom:building`**: Issue being implemented OR PR under review
- **`loom:review-requested`**: PR ready for Judge to review
- **`loom:pr`**: PR approved by Judge, ready for human to merge
- **`loom:architect`**: Architectural proposal awaiting user approval
- **`loom:hermit`**: Simplification proposal awaiting user approval
- **`loom:curated`**: Issue enhanced by Curator, awaiting approval
- **`loom:blocked`**: Implementation blocked, needs help
- **`loom:urgent`**: Critical issue requiring immediate attention

## Git Worktree Workflow

Loom uses git worktrees to isolate agent work. Loom supports two types of worktrees depending on the usage mode:

### Worktree Strategy Overview

**Terminal Worktrees** (`.loom/worktrees/terminal-N`):
- **Purpose**: Agent isolation in Tauri App Mode
- **When**: Created automatically for each terminal in the Loom desktop application
- **Why**: Allows multiple autonomous agents to work on different branches simultaneously without conflicts
- **Scope**: Per terminal/agent (persistent across app restarts)
- **Used in**: Tauri App Mode only

**Issue Worktrees** (`.loom/worktrees/issue-N`):
- **Purpose**: Issue-specific work isolation for Builder agents
- **When**: Created manually by Builder when claiming an issue (both MOM and Tauri App)
- **Why**: Isolates work on specific issues with dedicated feature branches
- **Scope**: Per issue (temporary, cleaned up when PR is merged)
- **Used in**: Both Manual Orchestration Mode and Tauri App Mode

### When to Use Which Worktree Type

**Manual Orchestration Mode (Claude Code CLI)**:
- No terminal worktrees (agents work in main workspace initially)
- Builder creates issue worktrees via `./.loom/scripts/worktree.sh <issue-number>`
- Single agent per terminal, human-controlled

**Tauri App Mode (Autonomous Agents)**:
- Automatic terminal worktrees for agent isolation (`.loom/worktrees/terminal-N`)
- Builder ALSO creates issue worktrees when claiming work (`.loom/worktrees/issue-N`)
- Multiple autonomous agents can run simultaneously
- Builder works in issue worktree, not terminal worktree

### Creating Worktrees (for Agents)

When claiming an issue, create a worktree:

```bash
# Agent claims issue #42
gh issue edit 42 --remove-label "loom:issue" --add-label "loom:building"

# Create worktree for issue
./.loom/scripts/worktree.sh 42
# Creates: .loom/worktrees/issue-42
# Branch: feature/issue-42

# Change to worktree
cd .loom/worktrees/issue-42

# Do the work...
# ... implement, test, commit ...

# Push and create PR
git push -u origin feature/issue-42
gh pr create --label "loom:review-requested"
```

### Worktree Best Practices

- **Always use the helper script**: `./.loom/scripts/worktree.sh <issue-number>`
- **Never run git worktree directly**: The helper prevents nested worktrees
- **One worktree per issue**: Keeps work isolated and organized
- **Semantic naming**: Worktrees named `.loom/worktrees/issue-{number}`
- **Clean up when done**: Worktrees are automatically removed when PRs are merged

### Worktree Helper Commands

```bash
# Create worktree for issue
./.loom/scripts/worktree.sh 42

# Check if you're in a worktree
./.loom/scripts/worktree.sh --check

# Show help
./.loom/scripts/worktree.sh --help
```

## Development Workflow

### As a Builder (Manual Mode)

1. **Find ready issue**:
   ```bash
   gh issue list --label="loom:issue"
   ```

2. **Claim issue**:
   ```bash
   gh issue edit 42 --remove-label "loom:issue" --add-label "loom:building"
   ```

3. **Create worktree**:
   ```bash
   ./.loom/scripts/worktree.sh 42
   cd .loom/worktrees/issue-42
   ```

4. **Implement and test**:
   ```bash
   # Make changes...
   # Run tests...
   git add -A
   git commit -m "Implement feature X"
   ```

5. **Create PR**:
   ```bash
   git push -u origin feature/issue-42
   gh pr create --label "loom:review-requested" --body "Closes #42"
   ```

### As a Judge (Autonomous or Manual)

1. **Find PR to review**:
   ```bash
   gh pr list --label="loom:review-requested"
   ```

2. **Review PR**:
   ```bash
   gh pr checkout 123
   # Review code, run tests, check for issues
   ```

3. **Provide feedback**:
   ```bash
   # If changes needed:
   gh pr review 123 --request-changes --body "Feedback here"
   gh pr edit 123 --remove-label "loom:review-requested"

   # If approved:
   gh pr review 123 --approve
   gh pr edit 123 --remove-label "loom:review-requested" --add-label "loom:pr"
   ```

### As a Curator (Autonomous or Manual)

1. **Find unlabeled issues**:
   ```bash
   gh issue list --label="!loom:issue,!loom:building,!loom:architect,!loom:hermit"
   ```

2. **Enhance issue**:
   ```bash
   # Add technical details, acceptance criteria, references
   gh issue edit 42 --body "Enhanced description..."
   ```

3. **Mark as ready**:
   ```bash
   gh issue edit 42 --add-label "loom:issue"
   ```

## Configuration

### Workspace Configuration

Configuration is stored in `.loom/config.json` (gitignored, local to your machine):

```json
{
  "nextAgentNumber": 3,
  "terminals": [
    {
      "id": "terminal-1",
      "name": "Builder",
      "role": "builder",
      "roleConfig": {
        "workerType": "claude",
        "roleFile": "builder.md",
        "targetInterval": 0,
        "intervalPrompt": ""
      }
    }
  ]
}
```

### Custom Roles

Create custom roles by adding files to `.loom/roles/`:

```bash
# Create custom role definition
cat > .loom/roles/my-role.md <<EOF
# My Custom Role

You are a specialist in {{workspace}}.

## Your Role
...
EOF

# Optional: Add metadata
cat > .loom/roles/my-role.json <<EOF
{
  "name": "My Custom Role",
  "description": "Brief description",
  "defaultInterval": 300000,
  "defaultIntervalPrompt": "Continue working",
  "autonomousRecommended": false,
  "suggestedWorkerType": "claude"
}
EOF
```

### Branch Protection

Loom works best with branch protection enabled on your default branch. Branch protection ensures all changes go through the PR workflow and prevents accidental direct commits.

#### During Installation

The installation script optionally configures branch protection:

**Interactive mode**: Prompts you to enable protection
```bash
./scripts/install-loom.sh /path/to/repo
# Will prompt: Configure branch protection rules for 'main' branch? (y/N)
```

**Non-interactive mode**: Skips branch protection (configure manually)
```bash
./scripts/install-loom.sh --yes /path/to/repo
# Skips protection setup for automation safety
```

#### Manual Configuration

Configure branch protection after installation:

```bash
./scripts/install/setup-branch-protection.sh /path/to/repo main
```

Or configure via GitHub Settings:
1. Go to: `Settings > Branches` in your repository
2. Add rule for your default branch (usually `main`)
3. Enable:
   - Require pull request reviews (1 approval)
   - Dismiss stale reviews on new commits
   - Prevent force pushes
   - Prevent branch deletion

#### Protection Rules Applied

The setup script configures these rules:
- ✅ Require pull request before merging
- ✅ Require 1 approval (can be bypassed by admins)
- ✅ Dismiss stale reviews when new commits pushed
- ✅ Prevent force pushes
- ✅ Prevent branch deletion

#### Why Branch Protection?

**Enforces Loom workflow**:
- All changes require pull requests
- PRs require Judge review before merge
- Prevents bypassing label-based coordination
- Maintains audit trail of all changes

**Requirements**:
- Admin permissions on target repository
- GitHub CLI authenticated
- Default branch must exist

**Troubleshooting**:
If setup fails, it's usually due to:
- Lacking admin permissions (ask repo owner)
- Branch doesn't exist yet (push at least one commit)
- GitHub API unreachable (check network/auth)
<!-- END LOOM ORCHESTRATION -->

---

# Lean Proofs

This repository contains formal mathematical proofs in Lean 4. Building Lean proofs can be memory-intensive.

## DANGER: Memory Safety

```
+======================================================================+
|  NEVER RUN `lake build` DIRECTLY - USE DOCKER WRAPPER INSTEAD        |
|                                                                      |
|  Direct `lake build` can consume 100GB+ memory in seconds and        |
|  crash the host system before any monitoring can react.              |
|                                                                      |
|  ALWAYS USE: ./proofs/scripts/docker-build.sh Proofs.YourProof       |
+======================================================================+
```

## Building Proofs Safely

**NEVER run `lake build` directly** - always use Docker or the safe-build script. Tactics like `grind` can consume all system memory before external monitoring can react.

```bash
# ALWAYS use this:
./proofs/scripts/docker-build.sh Proofs.YourProof

# NEVER use this directly:
# lake build Proofs.YourProof  # DANGEROUS - no memory limits
```

**CRITICAL**: Some proofs can consume memory faster than external monitoring can detect. Use Docker for hard memory enforcement:

**Option 1: Docker Build (Recommended)**
```bash
# Hard memory limit enforced via Linux cgroups
./proofs/scripts/docker-build.sh                           # Build all
./proofs/scripts/docker-build.sh Proofs.OnePlusOne         # Specific target

# Custom memory limit (default: 32GB)
LEAN_MEMORY_LIMIT=8192 ./proofs/scripts/docker-build.sh    # 8GB limit
LEAN_BUILD_TIMEOUT=30m ./proofs/scripts/docker-build.sh    # 30min timeout
```

The first run will build a native ARM64 Lean Docker image (~1 min).

**Option 2: Build Safe Subset**
```bash
# Builds all proofs EXCEPT known memory-intensive ones
./proofs/scripts/build-safe-subset.sh
```

## Safety Wrapper (Automatic Protection)

This repository includes a `lake` wrapper script in `proofs/bin/` that **automatically intercepts** `lake build` commands and shows safe alternatives. When activated:

```bash
$ lake build Proofs.Something
# Output:
# +======================================================================+
# |  BLOCKED: Direct 'lake build' can crash your system                 |
# +======================================================================+
#
# Safe alternative:
#   ./proofs/scripts/docker-build.sh Proofs.Something
```

**Activation methods:**

1. **direnv (automatic)**: Run `direnv allow` in project root
2. **Manual**: `source ./proofs/scripts/activate-safety.sh`
3. **Shell profile**: Add `export PATH="/path/to/lean-genius/proofs/bin:$PATH"`

**Bypass (dangerous)**: `LAKE_UNSAFE=1 lake build ...`

## Proof Organization

- `proofs/` - Lean 4 project root
- `proofs/Proofs/` - Individual proof files
- `proofs/lakefile.toml` - Lake build configuration
- `proofs/scripts/` - Build and utility scripts

## Adding New Proofs

1. Create proof file in `proofs/Proofs/YourProof.lean`
2. Add gallery integration in `src/data/proofs/your-proof/`
3. Run `./proofs/scripts/safe-build.sh` to verify
4. Run `pnpm build` to verify gallery integration

---

# Aristotle (Proof Search)

Aristotle is an external proof search tool for Lean 4. It can automatically prove theorem sorries by searching for proofs.

## When to Use Aristotle

| Tool | Strength | Use For |
|------|----------|---------|
| **Claude** | Creative reasoning | OPEN problems, proof architecture |
| **Aristotle** | Proof search | KNOWN results needing formalization |

## Key Limitations

**CRITICAL: Aristotle only proves theorem/lemma sorries. It skips definitions and axioms entirely.**

This is the most important thing to understand about Aristotle:
- **Axioms** = "assume this is true" → Aristotle never attempts to prove them
- **Theorem sorries** = "prove this" → Aristotle will search for proofs

```lean
-- ✅ Aristotle CAN prove:
theorem sidon_bound : A.card ≤ n := by sorry
lemma computeA_22 : computeA β = 10 := by sorry

-- ❌ Aristotle SKIPS (will NOT attempt):
def chromaticNumber (G : SimpleGraph V) : ℕ := by sorry   -- Definition sorry
def danzerPoints : Finset Point := sorry                   -- Definition sorry
axiom jss_counterexample : ∃ G, ...                        -- Axiom (treated as given)
theorem placeholder : True := by sorry                     -- No mathematical content
```

**Implication for Erdős formalizations**: Our files use `axiom` for deep results (Ramsey bounds, probabilistic lemmas, etc.). These are semantically correct but Aristotle-unfriendly. Convert to theorem sorries before submission.

## Pre-Submission Checklist

1. **No definition sorries** - Aristotle will skip these and dependent theorems fail
2. **Convert axioms to theorem sorries** - Axioms are unprovable; convert to `theorem X : ... := by sorry`
3. **No placeholder True theorems** - Provide real mathematical content
4. **No OPEN conjectures** - Aristotle searches for existing proofs, can't discover new ones
5. **No `/-!` docstring sections** - Use `/-` instead (causes parsing errors)
6. **Simple namespace structure** - Complex nesting may fail to load

```bash
# Check for problems
grep -n "def.*:=.*sorry" your-file.lean          # Definition sorries
grep -n "^axiom " your-file.lean                  # Axioms (convert to theorems)
grep -n "theorem.*: True" your-file.lean         # Placeholder theorems
grep -n "theorem erdos_[0-9]*\s*:" your-file.lean # Potential OPEN problems
grep -n "/-!" your-file.lean                      # Docstring sections (may fail)
```

## Preparing Files for Aristotle

**IMPORTANT**: Most Erdős formalizations use `axiom` for deep mathematical results. These MUST be converted to theorem sorries before Aristotle can attempt proofs.

```lean
-- BEFORE (in main file - Aristotle will SKIP):
axiom keevash_sudakov_bound (n : ℕ) : countEdges n ≤ n^2 / 4

-- AFTER (for Aristotle submission - Aristotle will ATTEMPT):
theorem keevash_sudakov_bound (n : ℕ) : countEdges n ≤ n^2 / 4 := by sorry
```

**Quick conversion command**:
```bash
# Convert all axioms to theorem sorries (creates backup)
sed -i.bak 's/^axiom \([^:]*\):/theorem \1 :=/; s/theorem \([^:]*\) :=$/theorem \1 := by sorry/' file.lean
```

**Why this works**: Aristotle searches Mathlib and known results. If the result exists in Mathlib or can be derived from it, Aristotle will find the proof. Axioms are treated as "given" and never attempted.

**Workflow for axiom-heavy files**:
1. Copy the file to a `-provable.lean` variant
2. Convert all `axiom` declarations to `theorem ... := by sorry`
3. Verify no definition sorries exist (these block everything)
4. Submit the provable variant to Aristotle
5. Merge successful proofs back to the main file (keep working axioms as axioms if not proven)

**Writing Aristotle-friendly files from the start**:
If you plan to submit to Aristotle, consider using `theorem ... := by sorry` instead of `axiom` for results that might be provable from Mathlib. Reserve `axiom` only for:
- Results definitely NOT in Mathlib (recent papers, etc.)
- Foundational assumptions you truly want as axioms
- OPEN problems (conjectures)

## Syntax Compatibility

**Aristotle's parser differs from local Mathlib.** Files that compile locally may fail to load.

| Issue | Symptom | Fix |
|-------|---------|-----|
| `/-!` docstrings | "unexpected token" | Use `/-` |
| Complex namespaces | "unexpected name after end" | Flatten structure |
| Type inference | "function expected" | Add type annotations |

See `research/SORRY-CLASSIFICATION.md` for full compatibility guide.

## Workflow

```bash
# Submit file for overnight processing
./research/scripts/aristotle-submit.sh proofs/Proofs/MyProof.lean my-problem "Notes"

# Check status of all jobs
./research/scripts/aristotle-status.sh

# Retrieve completed solutions
./research/scripts/aristotle-status.sh --retrieve
```

## Job Tracking

Jobs are tracked in `research/aristotle-jobs.json`:

```bash
# View active jobs
cat research/aristotle-jobs.json | jq '.jobs[] | select(.status == "submitted")'

# Count by status
cat research/aristotle-jobs.json | jq '[.jobs[] | .status] | group_by(.) | map({status: .[0], count: length})'
```

## Success Patterns

- **MotivicFlagMapsProvable**: 10/10 theorems proved (all definitions complete)
- **Erdős #728**: 6-hour overnight run, 1416 lines of proof
- **Erdős #1**: 3/3 theorems proved in 44 minutes

## Failure Patterns

| Problem | Issue | Result |
|---------|-------|--------|
| erdos-58 | `chromaticNumber` def sorry | Theorems axiomatized |
| erdos-97 | `danzerPoints` def sorry | Construction skipped |
| erdos-39 | Placeholder `True` theorem | No progress |
| erdos-1030 | Axiom-heavy file (no conversion) | No proofs attempted |
| erdos-1026 | Axiom-heavy file (no conversion) | No proofs attempted |
| erdos-630 | Definition sorries | Blocked dependent theorems |

**Key Learnings**:
- **Axiom-heavy files** (#1030, #1026): Had many `axiom` declarations for deep results. Aristotle treated these as "given" and had nothing to prove. **Fix**: Convert axioms to theorem sorries before submission.
- **Definition sorries** (#630): When definitions use `sorry`, all dependent theorems fail to typecheck. Aristotle can't prove theorems that reference undefined values. **Fix**: Complete all definitions before submission.

**Lesson**: Only submit files where all definitions are complete AND axioms have been converted to theorem sorries.

## Documentation

- `research/SORRY-CLASSIFICATION.md` - Classification guide
- `research/aristotle-jobs.json` - Job history and learnings

---

# Quick Commands (Makefile)

This repository includes a Makefile with convenient aliases for common tasks. Run `make` or `make help` to see all available commands.

## Cleanup Commands

```bash
make clean            # Preview all cleanup (dry-run)
make clean-all        # Deep clean everything (force mode)
make clean-enhancers  # Clean enhancement agent artifacts
make clean-research   # Clean research agent artifacts
make clean-loom       # Clean loom worktrees and branches
make prune            # Prune git worktrees and remote branches
```

Cleanup flags (can be combined):
- `DEEP=1` - Include worktrees, branches, and logs
- `FORCE=1` - Non-interactive mode (for CI/automation)
- `DRY=1` - Preview what would be cleaned

```bash
# Examples
make clean-enhancers DEEP=1 FORCE=1  # Deep clean enhancers non-interactively
make clean-research DRY=1            # Preview research cleanup
```

## Status Commands

```bash
make status           # Show all agent claim status
make status-enhancers # Show enhancement claims only
make status-research  # Show research claims only
```

## Build Commands

```bash
make build            # Build the project (pnpm build)
make test             # Run tests
make lint             # Run linter
```

## Agent Launch Commands

```bash
make enhance N=3      # Launch 3 parallel enhancer agents (default)
make enhance N=5      # Launch 5 parallel enhancer agents
make research N=2     # Launch 2 parallel research agents (default)
```

---

# Troubleshooting

## Common Issues

**Cleaning Up Stale Worktrees and Branches**:

Use `make clean-all` to clean everything, or use the individual cleanup scripts:

```bash
# Preferred: Use Makefile commands
make clean-all                           # Deep clean everything
make clean-enhancers DEEP=1 FORCE=1      # Clean enhancement artifacts
make clean-research DEEP=1 FORCE=1       # Clean research artifacts
make clean-loom DEEP=1 FORCE=1           # Clean loom artifacts

# Or use scripts directly
./.loom/scripts/clean.sh --deep --force  # Loom worktrees/branches
./scripts/erdos/clean-enhancers.sh --deep --force   # Enhancement agents
./scripts/research/clean-research.sh --deep --force # Research agents
```

**What gets cleaned**:
- **clean-loom**: Loom worktrees, feature branches for closed issues, tmux sessions
- **clean-enhancers**: Enhancement claims, erdos-N worktrees, enhancer branches, logs
- **clean-research**: Research claims, researcher worktrees, researcher branches, logs

**IMPORTANT**: For **CI pipelines and automation**, always use `--force` flag or `FORCE=1`:
```bash
make clean-all  # Already uses --force internally
```

**Manual cleanup** (if needed):
```bash
# List worktrees
git worktree list

# Remove specific stale worktree
git worktree remove .loom/worktrees/issue-42 --force

# Prune orphaned worktrees
git worktree prune
```

**Labels out of sync**:
```bash
# Re-sync labels from configuration
gh label sync --file .github/labels.yml
```

**Terminal won't start (Tauri App)**:
```bash
# Check daemon logs
tail -f ~/.loom/daemon.log

# Check terminal logs
tail -f /tmp/loom-terminal-1.out
```

**Claude Code not found**:
```bash
# Ensure Claude Code CLI is in PATH
which claude

# Install if missing (see Claude Code documentation)
```

## Resources

### Loom Documentation

- **Main Repository**: https://github.com/loomhq/loom
- **Getting Started**: https://github.com/loomhq/loom#getting-started
- **Role Definitions**: See `.loom/roles/*.md` in this repository
- **Workflow Details**: See `.loom/AGENTS.md` in this repository

### Local Configuration

- **Configuration**: `.loom/config.json` (your local terminal setup)
- **Role Definitions**: `.loom/roles/*.md` (default and custom roles)
- **Scripts**: `.loom/scripts/` (helper scripts for worktrees, etc.)
- **GitHub Labels**: `.github/labels.yml` (label definitions)

## Support

For issues with Loom itself:
- **GitHub Issues**: https://github.com/loomhq/loom/issues
- **Documentation**: https://github.com/loomhq/loom/blob/main/CLAUDE.md

For issues specific to this repository:
- Use the repository's normal issue tracker
- Tag issues with Loom-related labels when applicable

---

**Lean Genius Project Guide**
Last updated: 2026-01-24
