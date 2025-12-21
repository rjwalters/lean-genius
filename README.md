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
```
