# Contributing to Lean Genius

Thank you for your interest in contributing to the Lean Genius proof gallery! This guide covers the research contribution workflow.

## Overview

Lean Genius maintains a gallery of formalized mathematical proofs in Lean 4, along with research documentation tracking progress on open problems. Contributors can help by:

- Researching new problems and documenting findings
- Improving existing proofs
- Building missing Mathlib infrastructure
- Reviewing and testing proofs

## Getting Started

### Prerequisites

- [Lean 4](https://leanprover.github.io/lean4/doc/setup.html) and Lake
- [Node.js](https://nodejs.org/) (v20+) and pnpm
- Git and GitHub CLI (`gh`)

### Setup

1. **Fork the repository** on GitHub

2. **Clone your fork:**
   ```bash
   git clone https://github.com/YOUR_USERNAME/lean-genius.git
   cd lean-genius
   ```

3. **Install dependencies:**
   ```bash
   pnpm install
   ```

4. **Rebuild the local database:**
   ```bash
   pnpm db:rebuild
   ```
   This creates `research/db/knowledge.db` from the SQL dump files.

5. **Build proofs** (optional, only if modifying Lean files):
   ```bash
   cd proofs && lake build
   ```

## Research Contribution Workflow

### 1. Create a Branch

```bash
git checkout -b research/your-topic
```

### 2. Run Research

Use the `/research` skill in Claude Code, or manually:

1. Check available problems:
   ```bash
   jq '.candidates[] | select(.status == "available")' research/candidate-pool.json
   ```

2. Work on a problem - update these files:
   - `src/data/research/problems/<id>.json` - structured knowledge
   - `research/problems/<id>/knowledge.md` - session logs (if exists)
   - `research/candidate-pool.json` - status updates

### 3. Export Database Changes

If you made database changes (new sessions, insights, etc.):

```bash
pnpm db:export
```

This exports the database to merge-friendly SQL files in `research/db/data/`.

### 4. Commit and Push

```bash
git add -A
git commit -m "Research: <problem-id> - brief description"
git push -u origin research/your-topic
```

### 5. Open a Pull Request

```bash
gh pr create --title "Research: <topic>" --body "Summary of findings..."
```

## Data Architecture

### Source of Truth

| File Type | Purpose | Version Controlled |
|-----------|---------|-------------------|
| `src/data/research/problems/*.json` | Problem definitions, current knowledge | Yes |
| `research/candidate-pool.json` | Problem registry and status | Yes |
| `research/db/data/*.sql` | Historical sessions, detailed records | Yes |
| `research/db/schema.sql` | Database schema | Yes |
| `research/db/knowledge.db` | Local SQLite database | No (gitignored) |

### Database Workflow

The SQLite database is a **local working copy** rebuilt from SQL dump files:

```
SQL files (tracked) ──db:rebuild──> Local DB (gitignored) ──db:export──> SQL files
```

- `pnpm db:rebuild` - Create local DB from SQL files (run after clone/pull)
- `pnpm db:export` - Export DB changes to SQL files (run before commit)

### Contributor Attribution

All database tables with contributor data include a `github_username` column. This:
- Tracks who contributed what
- Prevents ID collisions (rows are namespaced by contributor)
- Enables filtering by contributor

Your GitHub username is automatically captured when you run research sessions.

## Avoiding Merge Conflicts

### JSON Files

JSON files may conflict when multiple contributors modify the same problem. To minimize conflicts:

- Make focused changes to specific problems
- Coordinate via GitHub issues for high-activity problems
- Keep array additions small and atomic

### SQL Files

SQL dump files are designed to be merge-friendly:
- Each INSERT is on its own line
- Git can merge additions from different contributors
- The `github_username` column prevents ID collisions

If you do get conflicts:
1. Accept both versions of INSERT statements
2. Run `pnpm db:rebuild` to verify the merged SQL is valid
3. If IDs truly conflict, manually renumber one contributor's rows

## Coordination

### Claiming Problems

Before starting significant work on a problem:

1. Check if someone else is working on it:
   ```bash
   jq '.candidates[] | select(.id == "problem-id")' research/candidate-pool.json
   ```

2. Consider opening a GitHub issue to announce your work

3. Update the pool status to `in-progress` early in your branch

### Communication

- Use GitHub issues for coordination
- Reference issues in your PR descriptions
- Check recent PRs before starting work on a problem

## Code Standards

### Lean Proofs

- Follow Mathlib conventions
- Use `sorry` sparingly - document what's needed to remove it
- Include docstrings for theorems
- Add examples demonstrating usage

### Research Documentation

- Use clear, dated session entries in knowledge.md
- Update the `progressSummary` in JSON files
- Document blockers and next steps
- Reference sources (papers, Mathlib docs, etc.)

## Review Process

1. PRs are reviewed for:
   - Proof correctness (if Lean files changed)
   - Documentation quality
   - Merge conflict risk

2. CI will build proofs and validate data files

3. Maintainers may request changes or ask questions

4. Once approved, PRs are merged and deployed

## Quick Reference

```bash
# Initial setup
pnpm install && pnpm db:rebuild

# Start work
git checkout -b research/topic

# After research
pnpm db:export
git add -A && git commit -m "Research: topic"
git push -u origin research/topic
gh pr create

# After pulling changes
pnpm db:rebuild
```

## Questions?

- Open a GitHub issue for questions
- Check existing issues and PRs for context
- Review the `/research` skill documentation in Claude Code
