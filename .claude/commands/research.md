# Research

You are a Lean theorem proving researcher. Run one research iteration on the lean-genius proof gallery.

## Your Task

Execute a single research cycle: pick a problem, assess feasibility, and either SKIP, SURVEY, or DEEP DIVE.

## Step 1: Claim a Problem

First, claim an available problem using the coordination system:

```bash
./.loom/scripts/research-available.sh --random --claim
```

If no problems available, report this and stop.

Save the claimed problem ID for later.

## Step 2: Feasibility Check (15-30 minutes)

For the claimed problem, do a quick feasibility assessment:

1. **Search Mathlib** - Check what infrastructure exists
   - Use WebSearch for "Mathlib4 Lean [topic] 2025"
   - Check if key lemmas/definitions exist

2. **Check Codebase** - Look for existing related proofs
   - `grep -r "keyword" proofs/Proofs/`
   - Read any related files

3. **Assess Tractability**
   - What's already in Mathlib?
   - What needs to be built from scratch?
   - Are there blocking dependencies?

## Step 3: Decision

Based on feasibility, decide:

| Decision | Criteria | Action |
|----------|----------|--------|
| **SKIP** | Missing infrastructure, already done, or requires multi-week effort | Update notes, release claim with `--status skipped` |
| **SURVEY** | Can define/state but not fully prove | Create stub file with definitions, axioms, release with `--status surveyed` |
| **DEEP DIVE** | Tractable milestones exist | Create full proof file, release with `--status completed` |

## Step 4: Implement

### For SKIP:
```bash
# Update candidate-pool.json with SKIPPED note
./.loom/scripts/research-release.sh <problem-id> --status skipped
```

### For SURVEY:
1. Create `proofs/Proofs/<ProblemName>.lean` with:
   - Definitions
   - Key lemmas as axioms
   - Simple derived theorems
2. Release claim:
```bash
./.loom/scripts/research-release.sh <problem-id> --status surveyed
```

### For DEEP DIVE:
1. Create `proofs/Proofs/<ProblemName>.lean` with full proof
2. Build and verify: `lake build Proofs.<ProblemName>`
3. Fix any errors
4. Release claim:
```bash
./.loom/scripts/research-release.sh <problem-id> --status completed
```

## Step 5: Report

End with a summary:

```
## Research Iteration Complete

**Problem**: [id] - [name]
**Decision**: SKIP | SURVEY | DEEP DIVE
**Outcome**: [what was accomplished]
**File**: [path to created file, if any]

### Key Findings
- [finding 1]
- [finding 2]

### Pool Status
- Available: N problems remaining
```

## Parallel Safety

This workflow is safe for multiple agents:
- Claims prevent duplicate work
- 60-minute TTL prevents stale locks
- Release updates pool status atomically

## Files Reference

| File | Purpose |
|------|---------|
| `research/candidate-pool.json` | Problem registry with status |
| `research/claims/*.json` | Active claims |
| `proofs/Proofs/*.lean` | Proof files |

## Example Session

```
> /research

Claiming problem...
Selected: hurwitz-impossibility - Hurwitz Quaternion Theorem

Feasibility Check:
- Searching Mathlib for quaternions... Found Mathlib.Algebra.Quaternion
- Checking for normed division algebras... Limited support
- Tractability: 7/10 - Can prove Frobenius (n=1,2,4) easily

Decision: DEEP DIVE

Creating proofs/Proofs/HurwitzTheorem.lean...
Building... Success!

## Research Iteration Complete
**Problem**: hurwitz-impossibility
**Decision**: DEEP DIVE
**Outcome**: Proved Frobenius theorem for associative case
**File**: proofs/Proofs/HurwitzTheorem.lean

Pool Status: 4 problems remaining
```
