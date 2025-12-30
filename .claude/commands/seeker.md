# Seeker

Assume the Mathematical Problem Seeker role to select the next research problem.

## Process

1. **Read the role definition**: Load `.loom/roles/seeker.md`
2. **Refresh problem registry**: Run `npx tsx .loom/scripts/extract-problems.ts --json`
3. **Check active research**: See what's already being worked on
4. **Apply selection algorithm**: Filter and rank problems
5. **Initialize workspace**: Create research problem for selected problem
6. **Report selection**: Document why this problem was chosen

## Quick Start

```bash
# Refresh problem list
npx tsx .loom/scripts/extract-problems.ts --json

# View top tractable problems
npx tsx .loom/scripts/extract-problems.ts --tractability=tractable | head -30

# Check what's already active
./.loom/scripts/research.sh status
```

## Selection Priority

1. **Tractable extensions** of verified proofs
2. **Challenging generalizations** with clear first steps
3. **Completion** of WIP proofs with few sorries
4. **Connections** between proofs

Avoid: moonshot problems unless explicitly requested.

## Output

```
✓ Role Assumed: Seeker
✓ Problems Scanned: [N]
✓ Active Research: [N] problems
✓ Selected Problem:
  - ID: [problem-id]
  - Title: [title]
  - Category: [category]
  - Tractability: [tractability]
✓ Workspace Initialized: .loom/research/problems/[slug]
✓ Ready for: /researcher
```

## After Selection

Run `/researcher` to begin the OODA loop on the selected problem.
