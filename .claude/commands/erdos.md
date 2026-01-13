# Erdős Problems Pipeline

You are managing the Erdős problems collection pipeline for lean-genius.

## Overview

This skill orchestrates:
1. **Stub enhancement** - Upgrade existing gallery stubs to quality entries (PRIMARY WORK)
2. **Submodule sync** - Keep external/formal-conjectures and external/erdosproblems updated
3. **Scraping** - Fetch problem descriptions from erdosproblems.com (SECONDARY)
4. **Research processing** - Add open problems to research queue

## Critical: Most Gallery Entries Are Stubs

**98.5% of gallery entries (461/468) are stubs.** These have:
- Placeholder Lean proofs (`theorem X : True := trivial`)
- Empty annotations.json (0 lines)
- Garbage meta.json descriptions (scraping artifacts like "Forum\nFavourites...")

**Scraping does NOT help** - we already have the stubs. The bottleneck is **enhancement**.

## Quick Status Check

First, always assess current state:

```bash
# Check stub status (PRIMARY)
npx tsx scripts/erdos/find-stubs.ts --stats

# Check scraping progress (SECONDARY)
npx tsx scripts/erdos/index.ts --status

# Check submodule freshness
git submodule status
```

## Autonomous Decision Flow

**When operating autonomously, follow this priority order:**

```
1. ENHANCE STUBS WITH SOURCES
   └─ Run: npx tsx scripts/erdos/find-stubs.ts --next
   └─ These have formal-conjectures Lean to adapt (127 available)
   └─ ~15-30 min per stub

2. ENHANCE STUBS WITHOUT SOURCES
   └─ Only if all sourced stubs are done
   └─ Requires writing Lean from scratch
   └─ More difficult, lower priority

3. SCRAPE FOR NEW CANDIDATES
   └─ Only if no stubs remain AND new candidates exist above scraping progress
   └─ Scraping is SLOW (~1 min per problem)

4. CONTINUE BATCH SCRAPING
   └─ Lowest priority
   └─ Only when nothing else to do
```

## Primary Workflow: Enhance a Stub

### Step 1: Find the Next Stub

```bash
npx tsx scripts/erdos/find-stubs.ts --next
```

This shows:
- The highest-priority stub (has source, solved status, low number)
- All quality issues (placeholder proof, empty annotations, garbage description)
- The formal-conjectures source path (if available)
- Detailed enhancement steps

### Step 2: Read the Source Material

```bash
# Read formal-conjectures Lean (if available)
cat external/formal-conjectures/FormalConjectures/ErdosProblems/{NUMBER}.lean

# Read the problem on erdosproblems.com
# https://erdosproblems.com/{NUMBER}
```

### Step 3: Rewrite the Lean Proof

Edit `proofs/Proofs/Erdos{NUMBER}Problem.lean`:

1. **Add header documentation**:
   ```lean
   /-
   Erdős Problem #{NUMBER}: {Short Title}

   {Problem statement}

   **Answer**: {YES/NO/Value} - proved by {Solver} ({Year})

   Reference: https://erdosproblems.com/{NUMBER}
   -/
   ```

2. **Add proper imports** from Mathlib

3. **Define key concepts** with doc comments

4. **State the main theorem**:
   - Use `axiom` if proof requires results beyond Mathlib
   - Include justification comment explaining why axiom is needed

5. **Add verified examples** where possible:
   ```lean
   /-- Concrete example: ... -/
   theorem example_N : ... := by native_decide
   ```

### Step 4: Build and Verify Lean

```bash
lake build Proofs.Erdos{NUMBER}Problem
```

### Step 5: Rewrite meta.json

Edit `src/data/proofs/erdos-{number}/meta.json`:

**Fix these fields:**
- `description` - Remove scraping garbage, write clean one-sentence statement
- `meta.author` - Add solver name and year
- `meta.status` - Set to "complete"
- `meta.badge` - Set to "axiom", "theorem", or "verified"
- `meta.sorries` - Set to 0
- `overview.historicalContext` - 2-3 paragraphs on history
- `overview.problemStatement` - LaTeX-formatted statement with answer
- `overview.proofStrategy` - How the proof works
- `overview.keyInsights` - Educational bullet points
- `sections` - Define code sections with line ranges
- `conclusion` - Summary, implications, open questions

### Step 6: Create annotations.json

Create `src/data/proofs/erdos-{number}/annotations.json`:

```json
[
  {
    "id": "ann-e{number}-imports",
    "proofId": "erdos-{number}",
    "range": { "startLine": 1, "endLine": 15 },
    "type": "concept",
    "title": "Imports and Setup",
    "content": "**Explanation** for general audience...",
    "mathContext": "Technical details...",
    "significance": "supporting",
    "relatedConcepts": ["mathlib", "imports"]
  },
  {
    "id": "ann-e{number}-main",
    "proofId": "erdos-{number}",
    "range": { "startLine": 20, "endLine": 25 },
    "type": "theorem",
    "title": "Main Theorem",
    "content": "**The core result**...",
    "mathContext": "Formal statement...",
    "significance": "critical",
    "relatedConcepts": ["erdos", "topic"]
  }
]
```

**Quality targets:**
- Minimum 5 annotations, 100+ lines
- One annotation per definition/theorem/key concept
- Compare to exemplar: `src/data/proofs/erdos-48/`

### Step 7: Final Verification

```bash
pnpm build
```

## Secondary Workflow: Scraping

Only pursue scraping when:
1. All 127 stubs with sources are enhanced, AND
2. New gallery candidates exist above scraping progress

### Check Scraping Status

```bash
npx tsx scripts/erdos/index.ts --status
# Shows: Cached: N / 1200
```

### Scrape Specific Problem

```bash
npx tsx scripts/erdos/index.ts --range {NUMBER}-{NUMBER} --playwright --slow
```

### Continue Batch Scraping

```bash
npx tsx scripts/erdos/index.ts --batch 10 --playwright --slow
```

**Rate Limiting Options:**
- `--slow` - 60s between requests (recommended)
- `--very-slow` - 3 min between requests (safest)
- `--playwright` - Use browser to avoid blocks

## Pipeline Commands Reference

| Command | Purpose |
|---------|---------|
| `npx tsx scripts/erdos/find-stubs.ts` | List all stubs needing enhancement |
| `npx tsx scripts/erdos/find-stubs.ts --next` | Get next stub with enhancement guide |
| `npx tsx scripts/erdos/find-stubs.ts --stats` | Show quality statistics |
| `npx tsx scripts/erdos/find-stubs.ts --json` | Output as JSON |
| `npx tsx scripts/erdos/index.ts --status` | Show scraping progress |
| `npx tsx scripts/erdos/process-gallery-candidate.ts --list` | List new candidates (above scraping) |

## Quality Guidelines

Compare every entry to the exemplar: `src/data/proofs/erdos-48/`

### meta.json Template

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
    "historicalContext": "2-3 paragraphs on the problem's history...",
    "problemStatement": "LaTeX-formatted statement with answer",
    "proofStrategy": "High-level proof approach",
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

### Badge Selection

- `"badge": "verified"` - Full constructive proof, no axioms
- `"badge": "theorem"` - Proof uses Mathlib theorems only
- `"badge": "axiom"` - Uses axiom for results beyond Mathlib

### Content Guidelines

**historicalContext:**
- When was this problem posed?
- Who solved it and when?
- Mathematical significance
- Connections to other areas

**proofStrategy:**
- High-level approach (contradiction, induction, construction)
- Why axioms are used (if applicable)
- What concrete examples we verify

**keyInsights:**
- Define key terms for non-experts
- Explain the "aha moment"
- Connect to familiar concepts

## Gallery Entry Checklist

Before marking a stub as enhanced:

- [ ] Lean proof builds: `lake build Proofs.Erdos{N}Problem`
- [ ] No placeholder (`True := trivial`) in Lean
- [ ] `meta.json` description is clean (no scraping garbage)
- [ ] `meta.json` has historicalContext, proofStrategy, keyInsights
- [ ] `annotations.json` has 5+ annotations, 100+ lines
- [ ] `pnpm build` succeeds

## Sync Submodules

Update external data sources periodically:

```bash
cd external/formal-conjectures && git pull origin main && cd ../..
cd external/erdosproblems && git pull origin main && cd ../..

# Regenerate cross-reference data
npx tsx scripts/erdos/external-sync.ts
npx tsx scripts/erdos/cross-reference.ts
```

## Time Estimates

- Enhancing one stub (with source): ~15-30 minutes
- Enhancing one stub (no source): ~30-60 minutes
- Scraping 10 problems: ~10 minutes
- Full Lake build: ~3 minutes
- Full pnpm build: ~10 seconds

## Notes

- **Stub enhancement is the bottleneck** - not scraping
- 127 stubs have formal-conjectures sources (easier to enhance)
- 334 stubs need manual Lean (harder)
- formal-conjectures proofs have `sorry` - we adapt and improve them
- Gallery entries need annotations to be educational
- Compare every entry to erdos-48 exemplar
