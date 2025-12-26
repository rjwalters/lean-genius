# LeanGenius

An interactive web application for viewing annotated Lean 4 proofs with line-by-line explanations, threaded discussions, and user accounts.

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

## Getting Started

### Prerequisites

- Node.js 18+
- pnpm
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

functions/            # Cloudflare Workers API endpoints
shared/               # Shared code between frontend and backend
drizzle/              # Database migrations
scripts/              # Build and import scripts
```

## Working with Proofs

Lean proofs are in the `proofs/` directory, a Lean 4 project with Mathlib.

### Project Structure

```
proofs/
├── Proofs/              # Individual Lean proof files
├── Proofs.lean          # Main import file
├── lakefile.toml        # Mathlib @ 05147a76b4
├── lean-toolchain       # Lean 4.10.0
└── scripts/             # Build and extraction scripts
```

### Building Proofs

```bash
cd proofs
./scripts/setup.sh       # First-time setup
lake build               # Build all proofs
```

### Importing Proof Data

After running LeanInk on a proof, import the tactic states:

```bash
# List available proofs
node scripts/import-proof.cjs --list

# Import a specific proof
node scripts/import-proof.cjs Sqrt2Irrational

# Import all proofs with LeanInk output
node scripts/import-proof.cjs --all
```

### Adding a New Proof

1. Create the Lean proof in `proofs/Proofs/YourProof.lean`
2. Add import to `proofs/Proofs.lean`
3. Build: `cd proofs && lake build`
4. Run LeanInk: `./scripts/extract-proof-info.sh Proofs/YourProof.lean`
5. Create the frontend structure in `src/data/proofs/your-proof/`:
   - `meta.json` - Proof metadata, sections, overview
   - `annotations.json` - Line-by-line annotations
   - `index.ts` - Import from `proofs/Proofs/YourProof.lean`
6. Run `node scripts/import-proof.cjs YourProof` to import tactic states
7. Add to `src/data/proofs/index.ts`
