# Erdős Problems Pipeline

You are managing the Erdős problems collection pipeline for lean-genius.

## Overview

This skill orchestrates:
1. **Submodule sync** - Keep external/formal-conjectures and external/erdosproblems updated
2. **Scraping** - Fetch problem descriptions from erdosproblems.com
3. **Gallery processing** - Add solved problems to proof gallery with annotations
4. **Research processing** - Add open problems to research queue

## Quick Status Check

First, always assess current state:

```bash
# Check scraping progress
npx tsx scripts/erdos/index.ts --status

# Check submodule freshness
git submodule status

# Count gallery vs research entries
ls src/data/proofs/erdos-* 2>/dev/null | wc -l
ls research/problems/erdos-* 2>/dev/null | wc -l
```

## Pipeline Commands

### 1. Sync Submodules

Update external data sources:

```bash
cd external/formal-conjectures && git pull origin main && cd ../..
cd external/erdosproblems && git pull origin main && cd ../..

# Regenerate cross-reference data
npx tsx scripts/erdos/external-sync.ts
npx tsx scripts/erdos/cross-reference.ts
```

### 2. Continue Scraping

Scrape more problems from erdosproblems.com:

```bash
# Scrape next batch (50 problems, ~50 min with slow mode)
npx tsx scripts/erdos/index.ts --batch 50 --playwright --slow

# Or run in background for longer batches
npx tsx scripts/erdos/index.ts --batch 100 --playwright --slow &
```

**Rate Limiting Options:**
- `--slow` - 60s between requests (recommended)
- `--very-slow` - 3 min between requests (safest)
- `--playwright` - Use browser to avoid blocks

### 3. Process Solved Problems into Gallery

For each SOLVED problem, create a complete gallery entry:

**Step A: Find candidates**
```bash
# List solved problems with Lean formalizations ready
cat scripts/erdos/data/gallery-candidates.json | jq '.[] | select(.status == "proved") | .number'
```

**Step B: For each candidate, create gallery entry**

1. **Check if formal-conjectures has Lean code:**
   ```bash
   ls external/formal-conjectures/FormalConjectures/ErdosProblems/{NUMBER}.lean
   ```

2. **If Lean exists, adapt it:**
   - Copy to `proofs/Proofs/Erdos{NUMBER}.lean`
   - Remove `sorry` placeholders (fill with actual proofs or axioms)
   - Add educational annotations explaining the proof
   - Verify it builds: `lake build Proofs.Erdos{NUMBER}`

3. **Create gallery metadata:**
   - `src/data/proofs/erdos-{number}/metadata.json`
   - `src/data/proofs/erdos-{number}/annotations.json` (or `.source.json`)

4. **Verify integration:**
   ```bash
   pnpm build
   ```

### 4. Process Open Problems into Research

For OPEN problems, create research entries:

```bash
# This is already automated by the scraper
npx tsx scripts/erdos/index.ts --research-only
```

Research entries go to `research/problems/erdos-{number}/` with:
- `problem.md` - Problem statement
- `state.md` - Current research state
- `knowledge.md` - Session logs

### 5. Aristotle Candidates

High-tractability problems are added to Aristotle queue:

```bash
# View current candidates
cat research/aristotle-jobs.json | jq '.candidates | length'

# Update candidates from scraped data
npx tsx scripts/erdos/update-aristotle-candidates.ts
```

## Priority Processing Order

When processing the backlog, prioritize:

1. **Gallery candidates with Lean code** (36 problems)
   - These have formal-conjectures formalizations
   - Status: proved/disproved
   - Easiest to complete

2. **Undergraduate-level problems** (24 problems)
   - Marked as easy in metadata
   - Good for building out collection quickly

3. **Prize problems** (103 problems)
   - High visibility
   - Worth extra annotation effort

4. **Remaining solved problems**
   - Create stubs even without Lean code
   - Can be filled in later

## Gallery Entry Checklist

For each problem added to gallery:

- [ ] Lean proof file exists in `proofs/Proofs/`
- [ ] Proof builds without errors (`lake build`)
- [ ] No `sorry` in final proof (or documented as axiom)
- [ ] Metadata JSON has correct fields
- [ ] Annotations explain key proof steps
- [ ] Problem statement matches erdosproblems.com
- [ ] Tags are appropriate
- [ ] `pnpm build` succeeds

## Quality Guidelines

Compare every gallery entry to the exemplar: `src/data/proofs/sqrt2-irrational/`

### meta.json Requirements

**Required fields:**
```json
{
  "id": "erdos-{number}",
  "title": "Erdős Problem #{number}: {short title}",
  "slug": "erdos-{number}",
  "description": "One-sentence problem statement",
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
    "mathlibDependencies": [
      {
        "theorem": "Mathlib.Name",
        "description": "What it provides",
        "module": "Mathlib.Module.Path"
      }
    ],
    "originalContributions": [
      "What we added beyond formal-conjectures",
      "Educational value we provide"
    ]
  },
  "overview": {
    "historicalContext": "2-3 paragraphs on the problem's history and significance",
    "problemStatement": "LaTeX-formatted mathematical statement with answer",
    "proofStrategy": "High-level proof approach explanation",
    "keyInsights": [
      "**Concept name**: Explanation",
      "**Another concept**: Explanation"
    ]
  },
  "sections": [
    {
      "id": "imports",
      "title": "Imports and Setup",
      "startLine": 1,
      "endLine": 20,
      "summary": "What this section does"
    }
  ],
  "conclusion": {
    "summary": "What we proved and how",
    "implications": "Why this matters",
    "openQuestions": ["Related unsolved questions"]
  }
}
```

### annotations.json Requirements

Create **one annotation per significant element**:

1. **Import annotations** (type: "concept") - Explain Mathlib dependencies
2. **Definition annotations** (type: "definition") - Explain custom definitions
3. **Main theorem** (type: "theorem", significance: "critical") - The problem statement
4. **Key lemmas** (type: "lemma", significance: "key") - Supporting results
5. **Examples** (type: "example" or "theorem") - Concrete instances

**Annotation structure:**
```json
{
  "id": "ann-e{number}-{element}",
  "proofId": "erdos-{number}",
  "range": {
    "startLine": 24,
    "endLine": 25
  },
  "type": "definition|theorem|lemma|concept|example|insight",
  "title": "Short descriptive title",
  "content": "**Markdown** explanation for general audience",
  "mathContext": "Technical Lean/math details for advanced readers",
  "significance": "critical|key|supporting",
  "relatedConcepts": ["concept1", "concept2"]
}
```

**Quality targets (compare to sqrt2-irrational):**
- sqrt2-irrational: 15 annotations, 334 lines
- Minimum for Erdős entries: 5+ annotations, 100+ lines
- Every definition and theorem should have an annotation

### Content Guidelines

**historicalContext should explain:**
- When was this problem posed?
- Who solved it and when?
- What mathematical significance does it have?
- Connections to other areas of mathematics

**proofStrategy should explain:**
- The high-level approach (contradiction, induction, construction, etc.)
- Why axioms are used (if applicable)
- What concrete examples we verify

**keyInsights should be educational:**
- Define key terms for non-experts
- Explain the "aha moment" of the proof
- Connect to familiar concepts when possible

### Badge Selection

- `"badge": "verified"` - Full constructive proof, no axioms
- `"badge": "theorem"` - Proof uses Mathlib theorems only
- `"badge": "axiom"` - Uses axiom for results beyond Mathlib (e.g., analytic number theory)

## Workflow Example

**Process Erdős #494 (proved, has Lean):**

```bash
# Option A: Use the helper script (recommended)
npx tsx scripts/erdos/process-gallery-candidate.ts 494

# Option B: Process next unprocessed candidate automatically
npx tsx scripts/erdos/process-gallery-candidate.ts --next

# Option C: List all candidates to choose from
npx tsx scripts/erdos/process-gallery-candidate.ts --list
```

**Manual workflow (if needed):**

```bash
# 1. Check formal-conjectures
cat external/formal-conjectures/FormalConjectures/ErdosProblems/494.lean

# 2. Copy and adapt
cp external/formal-conjectures/FormalConjectures/ErdosProblems/494.lean \
   proofs/Proofs/Erdos494Problem.lean

# 3. Edit to remove sorry, add imports, add annotations
# ... manual editing ...

# 4. Build and verify
cd proofs && lake build Proofs.Erdos494Problem

# 5. Create gallery entry
mkdir -p src/data/proofs/erdos-494
# ... create metadata.json and annotations ...

# 6. Full build
pnpm build
```

## Cross-Reference Data

Key files for finding problems to process:

| File | Content |
|------|---------|
| `scripts/erdos/data/gallery-candidates.json` | 36 proved problems with Lean |
| `scripts/erdos/data/proof-targets.json` | 317 problems with Lean statements |
| `scripts/erdos/data/enriched-problems.json` | All 1135 problems with metadata |
| `scripts/erdos/data/cross-reference.json` | Our coverage vs external |

## Session Workflow

A typical `/erdos` session:

1. **Status** - Check where we are
2. **Sync** - Update submodules if stale
3. **Scrape** - Continue if < 100% cached
4. **Process** - Pick 3-5 gallery candidates to complete
5. **Verify** - Build and test
6. **Commit** - Save progress

## Notes

- Scraping is rate-limited; run batches throughout the day
- formal-conjectures proofs all have `sorry` - we need to fill them
- Gallery entries need annotations to be educational
- Research entries are mostly automated
- Prioritize problems that are both SOLVED and have Lean formalizations
