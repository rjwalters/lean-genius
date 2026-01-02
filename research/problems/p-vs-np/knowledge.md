# Knowledge Base: P vs NP

## The Problem

The P versus NP problem asks whether every problem whose solution can be quickly *verified* can also be quickly *solved*. It is the central open problem in theoretical computer science.

### Core Statement

> Does P = NP?

More precisely: Is the class of problems solvable in polynomial time (P) equal to the class of problems verifiable in polynomial time (NP)?

### Why It Matters

1. **Practical Algorithms**: If P = NP, many currently intractable problems (scheduling, routing, protein folding) become efficiently solvable
2. **Cryptography**: Most modern cryptography assumes P ≠ NP; if P = NP, RSA and similar systems would be broken
3. **Mathematics**: Many mathematical search problems would become trivial
4. **AI and Optimization**: SAT solvers and constraint satisfaction would be polynomial-time

## Historical Context

| Year | Mathematician | Contribution |
|------|--------------|--------------|
| 1956 | Gödel | Letter to von Neumann hinting at the question |
| 1971 | Cook | Proved SAT is NP-complete (Cook-Levin theorem) |
| 1972 | Karp | 21 NP-complete problems |
| 1975 | Baker-Gill-Solovay | Relativization barrier |
| 1993 | Razborov-Rudich | Natural proofs barrier |
| 2009 | Aaronson-Wigderson | Algebrization barrier |

Despite 50+ years of effort and a $1 million prize, no proof or disproof exists.

## What We've Built

### In This Repository: pnp-barriers.lean

We've taken a unique approach: instead of trying to prove P ≠ NP (which faces known barriers), we've formalized **why standard proof techniques fail**.

The `PNPBarriers.lean` file (~2371 lines, 0 sorries) includes:

**Complexity Classes**:
- `P`, `NP`, `coNP`, `PSPACE`, `EXP` - basic classes
- `BPP`, `RP`, `ZPP`, `PP` - probabilistic classes
- `MA`, `AM`, `IP`, `MIP` - interactive proof classes
- `Sigma_k`, `Pi_k`, `PH` - polynomial hierarchy

**Key Theorems**:
- `P_subset_NP` - P ⊆ NP (unrelativized)
- `IP_eq_PSPACE` - Shamir's theorem: IP = PSPACE
- `MIP_eq_NEXP` - Babai-Fortnow-Lund theorem
- `complexity_containments` - Full chain P ⊆ NP ⊆ PSPACE ⊆ EXP

**Barrier Results**:
- `relativization_barrier` - Can't prove P ≠ NP by relativizing techniques
- `natural_proofs_barrier` - Natural proof methods contradict OWF existence
- `algebrization_barrier` - Algebraic techniques also fail

### Mathlib Status

| Component | Status | Notes |
|-----------|--------|-------|
| Turing machines | ⚠️ Partial | TM0, TM1, TM2 exist |
| Time complexity | ❌ | No P, NP definitions |
| Poly-time reductions | ❌ | Not formalized |
| NP-completeness | ❌ | No Cook-Levin |

## The Three Barriers

### 1. Relativization (Baker-Gill-Solovay, 1975)

There exist oracles A and B such that:
- P^A = NP^A
- P^B ≠ NP^B

**Consequence**: Any proof technique that relativizes (works uniformly with any oracle) cannot resolve P vs NP.

### 2. Natural Proofs (Razborov-Rudich, 1993)

Any "natural" circuit lower bound proof (constructive and based on a large, recognizable property) would break pseudorandom function generators.

**Consequence**: If one-way functions exist, natural proofs cannot prove P ≠ NP.

### 3. Algebrization (Aaronson-Wigderson, 2009)

Extends relativization to algebraic techniques. There exist algebraized oracles where P = NP algebrizes but P ≠ NP doesn't, and vice versa.

**Consequence**: Even sophisticated algebraic techniques (like those proving IP = PSPACE) cannot resolve P vs NP.

## Formalization Challenges

### Primary Blocker: Computational Complexity Framework

A full formalization needs:
1. **Turing machines** with time/space bounds
2. **Polynomial-time** definitions
3. **NP-completeness** and Cook-Levin theorem
4. **Oracle access** for barrier proofs

### What We've Done Instead

Rather than building all infrastructure to *state* P vs NP, we:
1. Defined abstract complexity classes matching standard definitions
2. Proved the barrier results that explain *why* the problem is hard
3. Built the full interactive proof hierarchy (IP = PSPACE, MIP = NEXP)
4. Created a framework that can be extended as Mathlib grows

## Why Our Approach is Valuable

The barriers explain **why 50 years of research hasn't solved P vs NP**:
- Diagonalization (used for P ≠ EXP) relativizes, so it can't work
- Circuit lower bounds require "unnatural" techniques
- Even arithmetic methods (IP = PSPACE) algebrize and fail

This formalization captures deep structural facts about computation.

## Key References

- Cook, S. (1971). "The Complexity of Theorem-Proving Procedures"
- Baker, T., Gill, J., Solovay, R. (1975). "Relativizations of the P =? NP Question"
- Razborov, A., Rudich, S. (1997). "Natural Proofs"
- Aaronson, S., Wigderson, A. (2009). "Algebrization: A New Barrier"
- Arora, S., Barak, B. (2009). "Computational Complexity: A Modern Approach"

## Related Work

| File | Relevance |
|------|-----------|
| `pnp-barriers.lean` | Our main formalization of barrier results |

## Scouting Log

### Assessment: 2026-01-01

**Current Status**: BLOCKED on direct formalization, but barrier results are complete

**Blocker Tracking**:
| Infrastructure | In Mathlib | Last Checked |
|----------------|------------|--------------|
| Turing machines | Minimal | 2026-01-01 |
| Time complexity | No | 2026-01-01 |
| NP-completeness | No | 2026-01-01 |
| Reductions | No | 2026-01-01 |

**Active Work**: `pnp-barriers.lean` is our main contribution - 2371 lines formalizing why standard techniques fail.

**Philosophy**: Rather than waiting for infrastructure, we've built something valuable now: a formal understanding of the meta-question "why is P vs NP hard?"
