# LeanGenius

> *"The Truth Mines were a honeycomb of abstract constructs..."*
> — Greg Egan, *Diaspora*

An interactive gallery of formal mathematics — annotated Lean 4 proofs with line-by-line explanations, plus tooling for AI-assisted formalization of open problems.

**Live site**: [leangenius.org](https://leangenius.org)

## Goals

- Formalize the [Erdos Problems](https://erdosproblems.com) in Lean 4
- Build infrastructure for human-AI collaborative proof development
- Create an accessible gallery for exploring verified mathematics

See [ROADMAP.md](ROADMAP.md) for current plans.

## Status

| Metric | Count |
|--------|-------|
| Lean proof files | 6,000+ |
| Gallery proofs | 4,800+ |
| Erdos problems formalized | 1,500+ |
| Research problems tracked | 2,600+ |

### Infrastructure

- **Multi-agent orchestration**: Autonomous researcher, enricher, auditor, and deployer agents
- **Aristotle integration**: Automated proof search via [Harmonic's Aristotle](https://harmonic.fun)
- **Smart account management**: Load balancing across multiple OAuth accounts with usage-aware scheduling
- **Docker builds**: Memory-safe Lean compilation (direct `lake build` can consume 100GB+)
- **Continuous deployment**: Automated PR merging, data sync, and Cloudflare deployment

## Related Projects

| Project | Focus |
|---------|-------|
| [erdosproblems.com](https://erdosproblems.com) | Canonical Erdos problem database |
| [Mathlib](https://github.com/leanprover-community/mathlib4) | Lean 4 mathematical library |
| [Erdosproblems-LLM-Hunter](https://github.com/mehmetmars7/Erdosproblems-llm-hunter) | Tracking informal LLM solution attempts |

## Tech Stack

**Frontend**
- React 19 + TypeScript
- Vite
- Tailwind CSS 4
- Radix UI primitives
- KaTeX for math rendering
- React Router

**Backend**
- Cloudflare Workers
- Cloudflare D1 (SQLite)
- Drizzle ORM

**Proofs**
- Lean 4.31.0
- Mathlib

## Getting Started

### Prerequisites

- Node.js 20.19+ (Vite 7 and React Router 7 require it)
- pnpm
- Docker (for building proofs)
- Wrangler CLI (for backend development)

### Installation

```bash
pnpm install
```

### Development

Start the frontend dev server:

```bash
pnpm dev
```

### Build

```bash
pnpm build
```

### Linting

```bash
pnpm lint
```

## Project Structure

```
src/
├── assets/           # Static assets bundled by Vite
├── components/       # React components
│   ├── auth/         # Authentication (login, signup, profile)
│   ├── comments/     # Threaded discussion system
│   ├── proof/        # Proof viewer, gallery cards, annotations
│   ├── research/     # Research problem cards and phase indicators
│   ├── ui/           # Shared UI primitives
│   └── visualizations/ # Proof-specific visualizations (e.g. knight's tour)
├── contexts/         # React contexts (auth)
├── data/proofs/      # Proof content (annotations, metadata) — one dir per proof
├── data/research/    # Research problem JSON (synced from research/problems/*/meta.json)
├── hooks/            # Shared React hooks
├── lib/              # Utilities (Lean tokenizer, gallery search, OQ slugs)
├── pages/            # Route pages
├── types/            # TypeScript types
└── utils/            # Misc helpers

proofs/
├── Proofs/           # Individual Lean proof files
├── Proofs.lean       # Root module (no imports; modules discovered by lakefile globs)
├── lakefile.toml     # Lean 4 project config (Mathlib dependency)
├── lean-toolchain    # Lean version pin
├── Dockerfile        # Memory-limited build image used by scripts/docker-build.sh
├── bin/              # `lake` safety wrapper that blocks direct `lake build`
├── batch2/           # v4.26→v4.31 migration ledger (verify-results.tsv) and diagnostics
├── data/             # Supporting data (e.g. Knuth tour extraction)
├── scripts/          # Build and extraction scripts (docker-build.sh, setup.sh, ...)
├── MATHLIB_STYLE.md  # Style/naming notes for files headed to Mathlib
└── BADGE_TAXONOMY.md # Proof badge definitions

functions/            # Cloudflare Workers API endpoints
shared/               # Shared code between frontend and backend
drizzle/              # Database migrations
scripts/              # Build, agent, and deployment scripts
research/             # Research problem tracking and state
infra/                # Infrastructure-as-code (unapplied Terraform skeleton)
mcp-servers/          # MCP server implementations
external/             # Git submodules (erdosproblems, formal-conjectures)
public/               # Build-generated static assets (gitignored)
aristotle-results/    # Retrieved Aristotle proof-search output (gitignored)
```

Top-level documents and helpers:

| File | Purpose |
|------|---------|
| `CLAUDE.md` / `AGENTS.md` | Agent instructions (Claude Code reads `CLAUDE.md`; Codex and other AGENTS.md-aware runtimes read `AGENTS.md`) |
| `CONTRIBUTING.md` | Contribution workflow and data architecture |
| `ROADMAP.md` / `PROOFS_ROADMAP.md` | Project plans / curated list of proofs to add |
| `START_WORK.md` / `STOP_WORK.md` | Recipes for launching and gracefully stopping the agent team |
| `Makefile` | `make help` lists build, cleanup, and agent-control targets |
| `loom.sh` | Wrapper to start the Loom daemon from the repo root |

## Working with Proofs

Lean proofs are in the `proofs/` directory, a Lean 4 project with Mathlib.

### Building Proofs

**Always use the Docker wrapper** — direct `lake build` can consume 100GB+ memory and crash the host.

```bash
# Build a specific proof
./proofs/scripts/docker-build.sh Proofs.YourProof

# Build with custom memory limit (default: 32GB)
LEAN_MEMORY_LIMIT=8192 ./proofs/scripts/docker-build.sh Proofs.YourProof
```

### Adding a New Proof

1. Create the Lean proof in `proofs/Proofs/YourProof.lean`
2. Build: `./proofs/scripts/docker-build.sh Proofs.YourProof`
3. Create gallery data in `src/data/proofs/your-proof/`:
   - `meta.json` — Proof metadata, sections, overview
   - `annotations.json` — Line-by-line annotations
4. Verify: `pnpm build`
