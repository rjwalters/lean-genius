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
- Lean 4.26.0
- Mathlib

## Getting Started

### Prerequisites

- Node.js 18+
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
├── components/       # React components
│   ├── auth/         # Authentication (login, signup, profile)
│   ├── comments/     # Threaded discussion system
│   ├── proof/        # Proof viewer and annotations
│   └── ui/           # Shared UI primitives
├── contexts/         # React contexts (auth)
├── data/proofs/      # Proof content (Lean source, annotations, metadata)
├── lib/              # Utilities (Lean tokenizer, etc.)
├── pages/            # Route pages
└── types/            # TypeScript types

proofs/
├── Proofs/           # Individual Lean proof files
├── lakefile.toml     # Lean 4 project config (Mathlib dependency)
├── lean-toolchain    # Lean version pin
└── scripts/          # Build and extraction scripts

functions/            # Cloudflare Workers API endpoints
shared/               # Shared code between frontend and backend
drizzle/              # Database migrations
scripts/              # Build, agent, and deployment scripts
research/             # Research problem tracking and state
infra/                # Infrastructure-as-code (unapplied Terraform skeleton)
mcp-servers/          # MCP server implementations
external/             # Vendored external artifacts
public/               # Build-generated static assets (gitignored)
aristotle-results/    # Retrieved Aristotle proof-search output
```

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
