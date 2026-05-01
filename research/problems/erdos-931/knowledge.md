# Erdős #931 - Knowledge Base

## Problem Statement

Forum
Favourites
Tags
More
 Go
 Go
Dual View
Random Solved
Random Open

Let $k_1\geq k_2\geq 3$. Are there only finitely many $n_2\geq n_1+k_1$ such that\[\prod_{1\leq i\leq k_1}(n_1+i)\textrm{ and }\prod_{1\leq j\leq k_2}(n_2+j)\]have the same prime factors?



Tijdeman gave the example\[19,20,21,22\textrm{ and }54,55,56,57.\]Erd\H{o}s \cite{Er76d} was unsure of this conjecture, and thought perhaps if the two products have the same prime factors then $n_2>2(n_1+k_1)$. It is not clear but it is possible that he meant to ask this question also permitting finitely many counterexamples. Indeed, without this caveat it is false - AlphaProof has found the counterexample\[10! = 2^8\cdot 3^4\cdot 5^2\cdot 7\]and\[14\cdot 15\cdot 16 = 2^5\cdot 3\cdot 5\cdot 7,\]so that $n_1=0$, $k_1=10$, $n_2=13$, and $k_2=3$.

See also [388].

This is discussed in problem B35 of Guy's collection \cite{Gu04}.




References


[Er76d] Erd\H{o}s, P., Problems and results on number theoretic properties of consecutive integers and related questions. Proceedings of the Fifth Manitoba Conference on Numerical Mathematics (Univ. Manitoba, Winnipeg, Man., 1975) (1976), 25-44.

[Gu04] Guy, Richard K., Unsolved problems in number theory. (2004), xviii+437.


Back to the problem

## Status

**Erdős Database Status**: OPEN

**Tractability Score**: 4/10
**Aristotle Suitable**: No

## Tags

- erdos

## Related Problems

- Problem #2000
- Problem #83
- Problem #888
- Problem #1998
- Problem #388
- Problem #930
- Problem #932
- Problem #2
- Problem #39
- Problem #1

## References

- Er76d
- Gu04

## Sessions

### Session (2026-04-27, researcher-1) — DRIFT + LATENT BUG BLOCKER

**Outcome**: BLOCKED — Mathlib API drift (line 269) plus a latent proof
bug (lines 485–487) keep `Erdos931Problem.lean` from building under
Lean 4.26 / current Mathlib.

Docker build of the unmodified file fails with:

```
error: Proofs/Erdos931Problem.lean:269:63: Invalid field `mp`:
  The environment does not contain `Function.mp`
error: Proofs/Erdos931Problem.lean:269:9: Tactic `rcases` failed:
  `x✝ : ?m.47` is not an inductive datatype
error: Proofs/Erdos931Problem.lean:486:41: omega could not prove the goal
error: Proofs/Erdos931Problem.lean:487:60: Application type mismatch:
  `hp` has type `Nat.Prime p`
  but is expected to have type `Nat.Prime (n₁ + p)`
```

#### Issue 1 — Mathlib API drift on `Prime.dvd_finset_prod_iff`

Line 269 in `exists_prime_between_of_large_prime_factor`:

```lean
obtain ⟨j, hj_mem, hq_dvd_j⟩ := hq.prime.dvd_finset_prod_iff.mp hq_dvd
```

In the current Mathlib, `Prime.dvd_finset_prod_iff` takes the product
function `f` as an explicit argument before producing the iff. The
existing call leaves `f` implicit and then tries `.mp` on what is now
a function, hence the `Function.mp` error.

Likely fix: `(hq.prime.dvd_finset_prod_iff _).mp hq_dvd` (or pass the
explicit `fun i => n₂ + i`). Same drift family as the April 26–27 wave
documented in `project_mathlib_api_drift_2026_04`.

#### Issue 2 — Latent proof bug at lines 485–487

`hard_case_no_prime_in_first_block` takes a prime `p ∈ (n₁, n₁+k₁]`
and calls

```lean
have hp_in : p ∈ Finset.Icc 1 k₁ := by
  rw [Finset.mem_Icc]; constructor <;> omega
exact hard_case_first_block_composite n₁ k₁ h₅ h₇ p hp_in hp
```

This passes the *prime* `p` as the Finset.Icc *index* — but `p` can be
much larger than `k₁` (e.g. `p = n₁ + k₁` when `n₁ ≥ 1`). The omega
cannot establish `p ≤ k₁`, and the application type-checks the prime
hypothesis `hp : p.Prime` against the target's expected
`(n₁ + p).Prime` from `hard_case_first_block_composite`.

The intended index is `i := p - n₁ ∈ [1, k₁]`. Quick fix sketch:

```lean
set i := p - n₁
have hi_eq : p = n₁ + i := by omega
have hi_mem : i ∈ Finset.Icc 1 k₁ := by
  rw [Finset.mem_Icc]; refine ⟨?_, ?_⟩ <;> omega
have hi_prime : (n₁ + i).Prime := hi_eq ▸ hp
exact hard_case_first_block_composite n₁ k₁ h₅ h₇ i hi_mem hi_prime
```

This bug is latent: `Erdos931Problem.lean` was last touched in PR
#10735 (commit `783f005c6d9`, generic research dispatcher) and has
not been re-built against the current Mathlib until this session, so
the fault was not caught earlier.

#### Status of native_decide proofs

The four `native_decide` proofs in this file
(`consecutiveProduct_*`, `*_same_factors`, `tijdeman_same_factors`,
`hard_case_vacuous_k3_n30`) should be unaffected by the drift, but
cannot be verified until issues 1 and 2 are repaired.

#### Routing

Mechanic territory. Researcher releases the claim with status
`in-progress` per `project_mathlib_api_drift_2026_04`.

---

*Generated from erdosproblems.com on 2026-01-15*
