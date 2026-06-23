# Feasibility Check: Legendre's Conjecture (`bertrands-postulate-oq-02`)

**Date**: 2026-05-30
**Researcher**: researcher-1
**Time spent**: ~30 minutes (survey of literature + Mathlib state)

## The Problem

**Legendre's conjecture** (open since 1798): for every $n \geq 1$, there is a
prime $p$ with $n^2 < p < (n+1)^2$.

One of Landau's four problems (1912). Believed true. Verified computationally
to $n \leq 1.5 \times 10^{18}$. **Not implied by RH** (RH gives only
$g(p_k) \ll \sqrt{p_k} \log p_k$, off by one log).

## Step 1: Mathlib Search Results

| Component | In Mathlib? | Notes |
|-----------|-------------|-------|
| Legendre's conjecture statement | **No** | Not formalized |
| `Nat.bertrand` | **Yes** | Prime in $(n, 2n]$ — too weak by factor $\sim n$ |
| Decidable primality | **Yes** | `Nat.decidablePrime`, fast on small $n$ |
| Prime counting function | **Yes** | `Nat.primesBelow` |
| Prime gap function | **No** | Not defined |
| Cramér's conjecture | **No** | Not stated |
| Riemann Hypothesis | **Defined** | `RiemannHypothesis` Prop in Mathlib |
| Short-interval prime theorems (Hoheisel, Huxley, BHP) | **No** | Far from Mathlib |

## Step 2: Analysis

### Full Conjecture: Infeasible

Tractability **0/10**. Open problem since 1798. Not implied by RH. Best
unconditional gap bound (Baker–Harman–Pintz, $\theta = 0.525$) misses Legendre
($\theta = 0.5$).

### Computational Extension: Tractable but Low Value

`legendre-partial` already verified $n = 1, \dots, 20$. Extending to
$n = 21, \dots, 100$ via `native_decide` is tractability **9/10** but
mathematically trivial; risks being judged as padding.

### Equivalence Formulation: Tractable and Valuable

Reformulate Legendre as a prime-gap statement and prove the equivalence.
No number-theoretic content needed beyond definitions; pure formal unwinding.
Yields a reusable `primeGap` definition for the gallery. Tractability
**6–8/10** depending on how we handle "the $k$-th prime" in Mathlib.

### Conditional Implication: Tractable and High-Value

Prove: "Cramér's conjecture implies Legendre's conjecture for all sufficiently
large $n$." This is a textbook implication (no open content) but requires
stating Cramér's conjecture, which Mathlib doesn't have. Tractability
**7/10**.

## Step 3: Milestone Tractability

| Milestone | Tractability | Notes |
|-----------|--------------|-------|
| State the conjecture | **10/10** | Done in `legendre-partial` |
| Extend `native_decide` to $n = 50$ | **9/10** | Trivial padding |
| Equivalence with prime-gap bound (Sub-Milestone B) | **6–8/10** | Recommended for iteration 2 |
| "Cramér ⇒ Legendre eventually" (Sub-Milestone A) | **7/10** | High-value implication |
| RH ⇒ Legendre | **0/10** | Not true |
| Full conjecture | **0/10** | Open since 1798 |

## Step 4: Decision

**Assessment**: SURVEY (this iteration) → DEEP DIVE on Sub-Milestone B next.

**Rationale**:
1. Full conjecture is infeasible.
2. Pure computational extension is low-value.
3. The equivalence formulation (Sub-Milestone B) is mathematically clean,
   delivers a reusable `primeGap` definition, and converts an "open problem"
   page into useful infrastructure.
4. Sub-Milestone A (conditional Cramér implication) is a strong follow-up
   once the equivalence is established.

## Next Iteration Plan

**Phase**: DEEP DIVE — Sub-Milestone B (equivalence)

1. Locate or define a prime-gap function in Mathlib idiom.
2. Draft `proofs/Proofs/LegendreGapEquivalence.lean` skeleton.
3. Prove both directions; expect ~3–4 short lemmas.
4. If straightforward, also prove that `legendre-partial`'s `LegendreAt 1..20`
   implies the gap bound for the corresponding primes.

## Time Budget

Iteration 2: ~1–2 hours to draft + verify the equivalence Lean file.
