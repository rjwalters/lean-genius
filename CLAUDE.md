# Lean Genius

Lean Genius is a formal mathematics project that formalizes mathematical theorems and problems (including Erdős problems) in Lean 4 and presents them in an interactive web gallery.

## Canonical Branch

`main` is the sole canonical branch. All PRs must target `main`. Never use `master` as a PR base or branch origin. If `git remote show origin` or `git symbolic-ref refs/remotes/origin/HEAD` returns `master`, fix it locally:

```bash
git remote set-head origin main
```

(See #13577 — `master` was retired after a 33/339-commit divergence and merged into `main`.)

## Making Code Changes

**Always work in a branch and worktree when editing code.** Direct pushes to main are blocked by branch protection. Multiple agents run concurrently and can overwrite uncommitted changes on main.

```bash
# Create a worktree for your changes
git worktree add .claude/worktrees/my-fix -b fix/my-fix main
cd .claude/worktrees/my-fix

# Make changes, commit, push, create PR
git add ... && git commit -m "..." && git push -u origin fix/my-fix
gh pr create --title "..." --body "..."

# Return to main when done
cd /Users/rwalters/GitHub/lean-genius
git worktree remove .claude/worktrees/my-fix
```

Or use the Claude Code `isolation: "worktree"` agent option for automatic worktree management.

### Worktree location

Fleet and Loom worktrees honor a configurable worktree root (resolved by
`scripts/lib/worktree-root.sh`, precedence: `LOOM_WORKTREE_ROOT` env var >
`.loom/config.json` → `worktree.root` > default `$REPO_ROOT/.loom/worktrees`).
On this fleet's host the operator sets `worktree.root = "/Volumes/Stripe"`
in `.loom/config.json` (runtime state — gitignored, NOT tracked), so agent
worktrees (`enricher-N`, `researcher-N`, `erdos-N`, `aristotle`, …) resolve
to `/Volumes/Stripe/lean-genius/<name>` on the dedicated 3.6 TiB volume
instead of the boot disk. Overrides are namespaced by repo basename; an
override must be an absolute path (a relative value warns and falls back to
the default).
Cleanup/GC (`scripts/clean-branches.sh`, `scripts/lean/infra-guardian.sh`)
services worktrees at both the resolved root and the legacy
`.loom/worktrees/` location during the transition.

---

## DANGER: Never Run `lake build` Directly

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

```bash
# ALWAYS use this:
./proofs/scripts/docker-build.sh Proofs.YourProof

# Custom limits (defaults: 32GB memory, 60min timeout)
LEAN_MEMORY_LIMIT=8192 ./proofs/scripts/docker-build.sh
LEAN_BUILD_TIMEOUT=30m ./proofs/scripts/docker-build.sh

# Or build the safe subset (excludes memory-intensive proofs)
./proofs/scripts/build-safe-subset.sh
```

A `lake` wrapper in `proofs/bin/` blocks direct `lake build` calls when activated via `direnv allow` or `source ./proofs/scripts/activate-safety.sh`. Bypass with `LAKE_UNSAFE=1` (dangerous).

---

## Agent Systems

This project uses two distinct AI agent orchestration systems.

### Loom (Development Orchestration)

Software development workflow. See `.loom/roles/*.md` for detailed role definitions.

| Agent | Purpose | Mode |
|-------|---------|------|
| **Builder** | Implements features and fixes | Manual |
| **Judge** | Reviews pull requests | Autonomous (5min) |
| **Curator** | Enhances and organizes issues | Autonomous (5min) |
| **Architect** | Creates architectural proposals | Autonomous (15min) |
| **Hermit** | Identifies simplification opportunities | Autonomous (15min) |
| **Doctor** | Fixes bugs and PR feedback | Manual |
| **Guide** | Prioritizes and triages issues | Autonomous (15min) |

Invoke via: `/builder`, `/judge`, `/curator`, `/architect`, `/hermit`, `/doctor`, `/guide`

### Lean Genius (Mathematical Orchestration)

Mathematical work: formalizing proofs, enhancing entries, automated proof search.

| Agent | Purpose | Mode |
|-------|---------|------|
| **Enricher** | Enriches gallery proofs with annotations, cross-references, context | Autonomous |
| **Aristotle** | Manages queue for Aristotle proof search system | Autonomous |
| **Researcher** | Works on open mathematical problems, proves theorems | Autonomous |
| **Scout** | Surveys gallery proofs, techniques, and literature | On-demand |
| **Seeker** | Selects research problems when candidate pool runs low | Autonomous (15min) |
| **Deployer** | Merges PRs, syncs data, deploys website to Cloudflare | Autonomous (30min) |
| **Peer Reviewer** | Deep qualitative review of gallery proofs | On-demand |
| **Auditor** | Validates gallery integrity: proof claims vs Lean source | Autonomous (10min) |
| **Mechanic** | Repairs issues found by auditors and peer reviewers | Autonomous (15min) |
| **Tester** | Tests random proof pages on the live site | Autonomous (30min) |
| **Herald** | Posts noteworthy research results to Mathstodon | Autonomous (6h) |

**Team orchestration**: `/lean` manages Enricher, Aristotle, Researcher, Auditor, Mechanic, Seeker, Deployer, Tester, Herald. Run `/lean` for commands and pool configuration.

**Legacy**: Erdos Enhancer (`make enhance`) — stub creation is complete (0 stubs remaining).

### When to Use Which

| Task | Use |
|------|-----|
| Writing code, fixing bugs, reviewing PRs | Loom agents (`/builder`, `/judge`, etc.) |
| Enriching existing gallery proofs | `/lean` (enricher) |
| Formalizing math, proving theorems | `/lean` (researcher) |
| Automated proof search | `/lean` (aristotle) |
| Surveying literature and techniques | `/lean-scout` |
| Selecting research problems | `/lean-seeker` |
| Deep qualitative review of a proof | `/peer-review` |
| Deploying the website | `/lean` (deployer) |
| Starting the full mathematical team | `/lean` |

### PR Labels for Math Agents

**Math agents (Researcher, Enricher, Aristotle, Erdos Enhancer) must NOT add `loom:review-requested` to their PRs.** The deployer merges math PRs directly without Judge review. Only add content-specific labels like `research`, `enrichment`, or `aristotle-integration`.

If you want a specific PR to go through Loom Judge review, manually add `loom:review-requested` — the deployer will skip it until a Judge approves it.

---

## Axiom Integrity Policy

Structure-encoded hypotheses (fields in structures/typeclasses such as `NSAxioms`, `SelbergClassAxioms`, `RHAxioms`) are mathematical assumptions. Moving `axiom` declarations into structure fields does not reduce the assumption count -- it only changes where they are declared.

**Rules for all agents:**
- `axiomCount` in meta.json must reflect ALL assumptions: `axiom` declarations + assumption-carrying structure fields
- When reporting "0 axioms" or "axiom-free", confirm there are no assumptions encoded in structures
- Restructuring axioms into structures is a valid proof architecture choice, but it does not change the mathematical status
- `grep -c "^axiom "` alone is NOT sufficient to count assumptions — always inspect structure fields too

**`native_decide` rule:** `native_decide` trusts the Lean compiler's kernel reduction and so depends on the `Lean.ofReduceBool` axiom (`#print axioms` lists it; the proof is *not* axiom-free). When `native_decide` discharges a **substantive** result the entry presents as verified, count it: `axiomCount ≥ 1`, `status: "axiomatized"`, `badge: "axiom"`, and disclose `Lean.ofReduceBool` in `assumptions`. (`leanFile.axiomCount` still counts only literal `axiom` declarations, so it may legitimately read 0 while `meta.axiomCount` is 1.) The ordinary foundational axioms `propext` / `Classical.choice` / `Quot.sound` do NOT count — only `Lean.ofReduceBool` (and `sorryAx`) do. This is the conservative reading of "when in doubt, axiomatized."

**Status field definitions** (meta.json `status` and `badge`):

| Status | Badge | Meaning | Requirements |
|--------|-------|---------|--------------|
| `verified` | `original` or `verified` | Fully machine-checked, no assumptions | 0 sorries, 0 `axiom` declarations, 0 structure-encoded assumptions |
| `axiomatized` | `axiom` | Formalized with stated assumptions | Has `axiom` declarations OR structure-encoded assumptions |
| `formalized` | varies | Lean formalization exists | Has sorries remaining |

- Millennium Prize problems, Clay problems, and open conjectures: always `"axiomatized"`
- Never use `"conditional"` — use `"axiomatized"` and describe the conditions in the `assumptions` field
- When in doubt, use `"axiomatized"` — overclaiming `"verified"` damages credibility

---

## Aristotle (Proof Search)

Aristotle is an external proof search tool for Lean 4 that automatically proves theorem sorries. Full guide: `research/SORRY-CLASSIFICATION.md`

### Key Rule

**Aristotle only proves theorem/lemma sorries. It skips definitions and axioms entirely.**

```lean
-- Aristotle CAN prove:
theorem sidon_bound : A.card <= n := by sorry

-- Aristotle SKIPS:
def chromaticNumber (G : SimpleGraph V) : Nat := by sorry   -- Definition sorry
axiom jss_counterexample : exists G, ...                      -- Axiom
```

### Pre-Submission Requirements

1. All definitions must be complete (no `sorry` in `def`)
2. Convert `axiom` declarations to `theorem ... := by sorry` for companion files
3. No placeholder `True` theorems
4. No `/-!` docstring sections (use `/-` instead — parser incompatibility)

### Companion Files

Use `*Aristotle.lean` companion files to expose only provable supporting lemmas (not the main open conjecture). See `research/SORRY-CLASSIFICATION.md` for the template and full guidelines.

### Workflow

```bash
./scripts/aristotle/find-candidates.sh          # Find candidates
./scripts/aristotle/submit-batch.sh --target 5   # Submit batch
./scripts/aristotle/check-jobs.sh --update        # Check status
./scripts/aristotle/retrieve-integrate.sh         # Integrate solutions
```

Jobs tracked in `research/aristotle-jobs.json`. The Aristotle agent handles this automatically when spawned via `/lean`.

---

## Proof Organization

- `proofs/` — Lean 4 project root
- `proofs/Proofs/` — Individual proof files
- `proofs/lakefile.toml` — Lake build configuration
- `src/data/proofs/<proof-name>/` — Gallery integration (meta.json, annotations, etc.)

Adding a new proof:
1. Create `proofs/Proofs/YourProof.lean`
2. Add gallery data in `src/data/proofs/your-proof/`
3. Build: `./proofs/scripts/docker-build.sh Proofs.YourProof`
4. Verify gallery: `pnpm build`

---

## Quick Commands

Run `make help` for all available commands.

```bash
# Build & test
make build                    # pnpm build
make test                     # Run tests
make lint                     # Run linter

# Cleanup
make clean-all                # Deep clean everything
make prune                    # Prune git worktrees and remote branches

# Agent status
make status                   # Show all agent claim status
./scripts/lean/launch.sh health   # Check lean agent health

# Lean agents
./scripts/lean/launch.sh start --researcher 3   # Start agents
./scripts/lean/launch.sh stop --force            # Force stop all
./scripts/lean/launch.sh daemon                  # Continuous monitoring
```

---

## Troubleshooting

**Stale worktrees/branches**: `make clean-all` or use individual cleanup: `make clean-loom`, `make clean-research`, `make clean-enhancers`. Add `DEEP=1 FORCE=1` for non-interactive deep clean.

**Labels out of sync**: `gh label sync --file .github/labels.yml`

<!-- BEGIN REPO-SKILLS -->
This repository has [Repo Skills](https://github.com/rjwalters/repo) v0.6.1 installed —
general repository hygiene and environment commands invoked as `/repo:<command>`. Run
`/repo:help` for the command list, or see `.claude/skills/repo/SKILL.md` for the full
guide. Hygiene commands apply safe, reversible fixes by default and report each
change; run with `--ask` to review first, and `--prune` to allow irreversible
removals. Managed by `install.sh` — edit outside the markers only.
<!-- END REPO-SKILLS -->

<!-- BEGIN LOOM ORCHESTRATION -->
This repository uses [Loom](https://github.com/rjwalters/loom) for AI-powered development orchestration — see the Loom repository for the full guide (roles, labels, worktrees, configuration). When installed, Loom also writes a locally-substituted copy of that guide to `.loom/CLAUDE.md`.
<!-- END LOOM ORCHESTRATION -->
