# laws-of-large-numbers-oq-02

## Problem Description

How fast does convergence occur in the Law of Large Numbers?

Three progressively sharper quantitative refinements of the Weak Law of Large Numbers
(WLLN) are studied:

1. **Chebyshev rate**: P(|X̄ₙ − μ| ≥ ε) ≤ σ² / (n ε²)  — rate O(1/n).
2. **Central Limit Theorem (CLT)**: √n (X̄ₙ − μ) / σ →ᵈ N(0,1)  — fluctuations scale as 1/√n.
3. **Berry–Esseen bound**: |P(Sₙ ≤ x) − Φ(x)| ≤ Cρ / (σ³ √n)  — explicit error bound for the
   CLT approximation, where `ρ = 𝔼|X − μ|³`.

## Metadata

- **Category**: extension (quantitative refinement of the WLLN)
- **Tractability**: mixed — Chebyshev rate is straightforward from Mathlib; CLT/Berry–Esseen
  are research-level formalizations.
- **Source Proof**: laws-of-large-numbers
- **Selected By**: seeker (date in candidate-pool); scaffold added 2026-05-13 by researcher-5
  after S1 OBSERVE.

## Related Gallery Proofs

- `laws-of-large-numbers` — parent (Weak/Strong LLN).
- `laws-of-large-numbers-oq-01-oq-02` — Marcinkiewicz–Zygmund SLLN rate hierarchy (sibling).
- `laws-of-large-numbers-oq-01-oq-03` — sibling.
- `laws-of-large-numbers-oq-03`, `laws-of-large-numbers-oq-04` — other siblings.

## Current Lean File

`proofs/Proofs/LawsOfLargeNumbersOQ02.lean` — 338 LOC, 0 sorries, **3 axioms**
(`variance_sampleMean`, `standardNormalCDF`, `berryEsseenConstant`). Prior PRs:

- #13382 (2026-04-27): "eliminate `sampleMean_memLp` axiom + Mathlib v4.26 fix" — converted
  one axiom into a theorem.
- #13415 (2026-04-27): "refresh stale axiom count".

## Gallery Status

**No gallery entry exists**: `src/data/proofs/laws-of-large-numbers-oq-02/` is absent. The
Lean file is built but ungalleried. Creating the gallery entry is the enricher's domain
(out of scope for this researcher slug).

## Suggested First Steps

1. Audit Mathlib v4.26.0 for bearers that could discharge any of the three remaining axioms
   (see `s1-observe-variance-sampleMean-bearer-audit.md` — the `variance_sampleMean` axiom
   is derivable; CLT/Berry–Esseen are not).
2. S2 ACT (the obvious next step): replace the `variance_sampleMean` axiom with a theorem
   proved from `IndepFun.variance_sum` + `variance_smul` (~25 LOC, no new imports).
3. Long-term: track upstream Mathlib for a CLT theorem statement once characteristic-
   function infrastructure crystallizes into an applied lemma.
