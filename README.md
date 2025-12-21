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

Lean proofs are maintained in a separate repository to isolate the Lean toolchain (elan, lake, Mathlib) from the web stack.

**Proofs Repository:** [lean-genius-proofs](https://github.com/rjwalters/lean-genius-proofs)

### Importing Proof Data

After running LeanInk on a proof in the proofs repo, import the tactic states:

```bash
# List available proofs
node scripts/import-proof.cjs --list

# Import a specific proof
node scripts/import-proof.cjs Sqrt2Irrational

# Import all proofs with LeanInk output
node scripts/import-proof.cjs --all
```

### Adding a New Proof

1. Create the Lean proof in `lean-genius-proofs/Proofs/`
2. Run LeanInk: `lake exe leanink Proofs/YourProof.lean`
3. Create the frontend structure in `src/data/proofs/your-proof/`:
   - `meta.json` - Proof metadata, sections, overview
   - `source.lean` - The Lean source code
   - `annotations.json` - Line-by-line annotations
   - `index.ts` - Export the proof data
4. Run `node scripts/import-proof.cjs YourProof` to import tactic states
5. Add to `src/data/proofs/index.ts`
