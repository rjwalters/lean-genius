# Feasibility Check: Szemerédi's Theorem

**Date**: 2025-12-31
**Time spent**: ~20 minutes

## The Problem

**Szemerédi's Theorem**: For every positive integer k and real δ > 0, there exists N such that every subset of {1, ..., N} with at least δN elements contains an arithmetic progression of length k.

## Step 1: Mathlib Search Results

| Component | In Mathlib? | File/Location |
|-----------|-------------|---------------|
| ThreeAPFree (k=3) | **YES** | `Combinatorics.Additive.AP.Three.Defs` |
| rothNumberNat | **YES** | `Combinatorics.Additive.AP.Three.Defs` |
| Roth's Theorem (k=3) | **YES** | `Combinatorics.Additive.Corner.Roth` |
| Corners Theorem | **YES** | `Combinatorics.Additive.Corner.Roth` |
| Triangle Removal Lemma | **YES** | `Combinatorics.SimpleGraph.Triangle.Removal` |
| Szemerédi Regularity Lemma | **YES** | `Combinatorics.SimpleGraph.Regularity.Lemma` |
| Hales-Jewett Theorem | **YES** | `Combinatorics.HalesJewett` |
| Van der Waerden Theorem | **YES** | via Hales-Jewett corollary |
| k-AP-free (general k) | **NO** | Only k=3 defined |
| Full Szemerédi Theorem | **NO** | Not formalized |

## Step 2: Prerequisite Mapping

### What we HAVE (strong foundation)
- Regularity lemma machinery (graph partitions, energy, uniformity)
- Roth's theorem via corners → triangle removal → regularity
- Hales-Jewett (Ramsey-theoretic, different approach)

### What we LACK

| Missing Piece | Difficulty to Add |
|---------------|-------------------|
| General k-AP definition | **Easy** - straightforward generalization |
| k-Corners definition | **Medium** - generalizes 2D corners to k-1 dimensions |
| Hypergraph regularity | **Hard** - needed for k>3 via regularity method |
| Hypergraph removal lemma | **Hard** - generalizes triangle removal |
| Furstenberg ergodic proof | **Research** - requires ergodic theory infrastructure |

### Key Insight

Szemerédi (density) ≠ Van der Waerden (coloring):
- Van der Waerden: k-color [1,N] → monochromatic k-AP (in Mathlib via Hales-Jewett)
- Szemerédi: δN elements in [1,N] → k-AP (NOT in Mathlib)

The density version is significantly harder.

## Step 3: Milestone Tractability

| Milestone | Tractability | Notes |
|-----------|--------------|-------|
| State full theorem formally | **8/10** | Straightforward definition |
| Prove k=3 case | **10/10** | Already done (Roth) |
| Prove k=4 case | **2/10** | Requires hypergraph regularity |
| State Furstenberg formulation | **5/10** | Ergodic formulation as axiom |
| General k proof | **1/10** | Major research project |
| Link to Van der Waerden | **4/10** | Show density implies VdW |

## Step 4: Decision Matrix

**Situation**:
- Only trivial milestones tractable (statement, k=3 already done)
- Medium milestone (k=4) requires building significant new machinery
- High milestone (general k) is a multi-month research project

**Assessment**: SURVEY MODE

## Decision: SURVEY

**Rationale**:
- k=3 (Roth) already formalized - no new mathematical content there
- k=4+ requires hypergraph regularity lemma (massive undertaking)
- Stating the theorem is valuable but low-effort
- Better to document gaps than commit to dead-end deep dive

**Survey deliverables**:
1. Formal statement of full Szemerédi theorem
2. Definition of general k-AP predicate
3. Verification that k=3 case follows from Roth
4. Document what's needed for k≥4

**Time budget**: 1-2 hours max

## References

- Dillies & Mehta, "Formalising Szemerédi's Regularity Lemma in Lean" (ITP 2022)
- Mathlib `Combinatorics.Additive.Corner.Roth`
- Mathlib `Combinatorics.HalesJewett`
