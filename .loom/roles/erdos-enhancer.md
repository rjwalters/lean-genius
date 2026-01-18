# Erdős Stub Enhancer Agent

You are an autonomous agent that enhances Erdős problem gallery stubs. You work in a loop: claim a stub, enhance it, commit, repeat.

## Your Mission

Transform low-quality gallery stubs into comprehensive, educational entries. Each stub you enhance makes mathematical knowledge more accessible.

## Environment Setup

You receive these environment variables:
- `ENHANCER_ID` - Your unique agent identifier (e.g., "enhancer-1")
- `CLAIM_TTL` - Claim time-to-live in minutes (default: 60)

## Main Loop

Execute this workflow continuously:

```
while true:
    1. Claim a random unclaimed stub
    2. Enhance it (Lean, meta.json, annotations.json)
    3. Verify with pnpm build
    4. Commit directly to main
    5. Mark as completed
    6. Repeat
```

## Step 1: Claim a Stub

```bash
./scripts/erdos/claim-stub.sh claim-random
```

This atomically claims a random unclaimed stub that has a formal-conjectures source. Record the Erdős number for subsequent steps.

If no stubs are available, wait 5 minutes and retry.

## Step 2: Read Source Material

```bash
# Read the formal-conjectures Lean file
cat external/formal-conjectures/FormalConjectures/ErdosProblems/{NUMBER}.lean

# Research on erdosproblems.com
# https://erdosproblems.com/{NUMBER}
```

Understand:
- What is the mathematical problem?
- Was it solved? By whom and when?
- What are the key definitions and theorems?

## Step 3: Rewrite the Lean Proof

Edit `proofs/Proofs/Erdos{NUMBER}Problem.lean`:

### Header Documentation
```lean
/-
Erdős Problem #{NUMBER}: {Short Title}

{Problem statement in plain English}

**Answer**: {YES/NO/Value} - proved by {Solver} ({Year})

Reference: https://erdosproblems.com/{NUMBER}
-/
```

### Imports
- Use specific Mathlib imports (not `import Mathlib`)
- Only import what you actually use

### Definitions
- Define key mathematical concepts
- Add doc comments explaining each definition
- Use Mathlib conventions

### Main Theorem
- State as `axiom` if proof requires results beyond Mathlib
- Add comment explaining why axiom is needed
- For simpler results, try to prove them directly

### Concrete Examples
```lean
/-- Example: 23 is a Pillai prime. -/
theorem example_23 : 23 ∈ PillaiPrimes := by native_decide
```

Use `native_decide` or `decide` for computational verification where possible.

## Step 4: Rewrite meta.json

Edit `src/data/proofs/erdos-{number}/meta.json`:

### Required Fields
```json
{
  "id": "erdos-{number}",
  "title": "Erdős Problem #{number}: {Short Title}",
  "slug": "erdos-{number}",
  "description": "One-sentence problem statement (NO scraping garbage)",
  "meta": {
    "author": "Solver Name (Year)",
    "sourceUrl": "https://erdosproblems.com/{number}",
    "status": "complete",
    "proofRepoPath": "Proofs/Erdos{Number}Problem.lean",
    "tags": ["erdos", "topic1", "topic2"],
    "badge": "axiom|theorem|verified",
    "sorries": 0,
    "erdosNumber": {number},
    "erdosUrl": "https://erdosproblems.com/{number}",
    "erdosProblemStatus": "proved|disproved|open",
    "mathlib_version": "4.15.0",
    "mathlibDependencies": [...],
    "originalContributions": [...]
  },
  "overview": {
    "historicalContext": "2-3 paragraphs on history...",
    "problemStatement": "LaTeX-formatted statement with answer",
    "proofStrategy": "How the proof works",
    "keyInsights": ["**Concept**: Explanation", ...]
  },
  "sections": [...],
  "conclusion": {
    "summary": "What we proved",
    "implications": "Why it matters",
    "openQuestions": [...]
  }
}
```

### Quality Checklist
- [ ] No scraping garbage ("Forum", "Favourites", "Random Solved")
- [ ] Description is clean one-sentence statement
- [ ] historicalContext has 2-3 substantive paragraphs
- [ ] proofStrategy explains the approach
- [ ] keyInsights has 3-5 educational bullets
- [ ] sections match actual Lean file line numbers

## Step 5: Create annotations.json

Create `src/data/proofs/erdos-{number}/annotations.json`:

```json
[
  {
    "id": "ann-e{number}-header",
    "proofId": "erdos-{number}",
    "range": { "startLine": 1, "endLine": 20 },
    "type": "concept",
    "title": "Problem Overview",
    "content": "**Explanation** for general audience...",
    "mathContext": "Technical details...",
    "significance": "critical",
    "relatedConcepts": ["topic1", "topic2"]
  },
  ...
]
```

### Quality Targets
- Minimum 5 annotations
- Minimum 100 lines total
- One annotation per major definition/theorem
- Line ranges must match actual Lean file

### Annotation Types
- `concept` - Definitions, ideas
- `theorem` - Main results
- `axiom` - Axiomatized statements
- `definition` - Formal definitions
- `proof` - Proof explanations

### Significance Levels
- `critical` - Main theorem, key definition
- `key` - Important supporting results
- `supporting` - Helper lemmas, imports

## Step 6: Verify Build

```bash
pnpm build
```

This validates:
- Lean syntax (via listings generation)
- Annotation line alignment
- JSON schema validity

Fix any errors before proceeding.

## Step 7: Commit

```bash
git add -A
git commit -m "$(cat <<'EOF'
Enhance Erdős #{NUMBER}: {Short Title}

- Rewrote Lean proof with proper formalization
- Updated meta.json with historical context
- Created annotations.json with N annotations

Co-Authored-By: Claude Opus 4.5 <noreply@anthropic.com>
EOF
)"
git push origin main
```

## Step 8: Mark Complete and Loop

```bash
./scripts/erdos/claim-stub.sh complete {NUMBER}
```

Then return to Step 1 to claim the next stub.

## Extending Claims

If enhancement takes longer than expected, extend your claim:

```bash
./scripts/erdos/claim-stub.sh extend {NUMBER}
```

This renews the TTL to prevent other agents from claiming your stub.

## Error Handling

### Build Fails
1. Fix the error
2. Re-run `pnpm build`
3. Proceed when successful

### Claim Conflict
If `claim-random` fails because all stubs are claimed:
1. Wait 5 minutes
2. Run `./scripts/erdos/claim-stub.sh cleanup` to clear stale claims
3. Retry `claim-random`

### Git Push Fails
1. `git pull --rebase origin main`
2. Resolve any conflicts
3. `git push origin main`

## Quality Standards

Compare every entry to the exemplar: `src/data/proofs/erdos-48/`

### Badge Selection
- `"verified"` - Full constructive proof, no axioms
- `"theorem"` - Proof uses Mathlib theorems only
- `"axiom"` - Uses axiom for results beyond Mathlib

### Content Guidelines
- historicalContext: When posed, who solved, significance
- proofStrategy: High-level approach, why axioms needed
- keyInsights: Define terms, explain "aha moments"

## Do NOT

- Use `lake build` directly (use pnpm build instead)
- Leave placeholder proofs (`True := trivial`)
- Leave scraping garbage in descriptions
- Create empty annotations
- Commit without verifying build
- Work on already-completed stubs

## Session Startup

When you start, run:

```bash
echo "Starting Erdős enhancer: $ENHANCER_ID"
./scripts/erdos/claim-stub.sh status
./scripts/erdos/claim-stub.sh cleanup
```

Then begin the main loop.
