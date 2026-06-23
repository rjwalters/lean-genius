# Optimal Minimum Modulus Bound (erdos-8-oq-01)

## Problem Summary

The parent problem **erdos-8** ("Monochromatic Covering Systems") is
SOLVED (disproved by Hough 2015). The disproof relies on **Hough's
minimum modulus bound**: every covering system with distinct moduli
has its smallest modulus `≤ 616 000`. In the Lean formalization
(`proofs/Proofs/Erdos8Problem.lean`) this appears as

```lean
axiom hough_minimum_modulus (cs : CoveringSystem) (hd : cs.hasDistinctModuli) :
    cs.minModulus ≤ 616000
```

The open question **erdos-8-oq-01** asks:

> What is the **optimal** minimum modulus bound? I.e., is `616 000` the
> tight constant, or can it be improved?

History of the bound:
- Hough (2015): proved `minModulus ≤ 616 000`.
- Balister, Bollobás, Morris, Sahasrabudhe, Tiba (2022): refined to a
  significantly smaller bound (the exact constant in their paper is
  much smaller; their proof gives `≤ exp(C log log m / log log log m)`
  for the m-th covering moduli, and structural improvements over Hough's
  Fourier-analytic original).
- The **true optimal bound** is unknown.

## Statement (informal)

Find the smallest `K ∈ ℕ` such that:
- For every covering system `cs` with distinct moduli,
  `cs.minModulus ≤ K`;
- There exists a covering system with distinct moduli and
  `cs.minModulus = K`.

A weaker but more tractable question: prove `K ≤ K₀` for some explicit
`K₀ < 616 000`.

## Status in the Lean formalization

Both remaining axioms in `Erdos8Problem.lean` are **deep published
results**:

| Axiom | Source | Effort to discharge |
|---|---|---|
| `hough_minimum_modulus` | Hough 2015 (Annals of Math) | ~10⁴ LOC of analytic number theory (Fourier-analytic L²-mean estimates over residue classes) |
| `density_conjecture_false` | Hough 2015 (same paper, density version) | ~10⁴ LOC, same toolkit |

Neither is a candidate for session-level discharge. They are
"foundational" axioms in the sense that an honest formalization would
require either (a) porting the Hough 2015 paper in full, or (b)
accepting them as published-result assumptions and focusing on
**downstream** structural work.

## Why This Matters

The optimal bound has direct consequences:
- **Algorithmic**: explicit lower bounds on the smallest covering-system
  modulus drive concrete search programs (Cao 2018 verified Hough's
  bound is achievable in particular shape regimes).
- **Structural**: the optimal bound encodes the entire "shape" of
  covering systems — it controls density, entropy, and Fourier-uniformity
  bounds.
- **Mathlib value**: a formalized bound, even a weak one (say `K ≤ 10^9`),
  would be the **only** Mathlib-accessible quantitative result on
  covering systems.

## Classification

```yaml
tier: C
significance: 6
tractability: 2  # session-level: very low (deep axiom); structural sub-questions are higher
status: AXIOMATIZED
parent: erdos-8
deep-axioms-in-parent:
  - hough_minimum_modulus
  - density_conjecture_false
tags:
  - covering-systems
  - number-theory
  - hough-2015
  - balister-bbmst-2022
  - axiom-elimination
  - deep-result-axiom
```

## Existing Infrastructure (`Erdos8Problem.lean`, 352 LOC, 9 thms, 2 axioms, 0 sorries)

| Definition | Purpose |
|---|---|
| `CongruenceClass` | residue + modulus + `modulus ≥ 2` + `residue < modulus` |
| `CoveringSystem` | classes + nonempty + covers ℤ |
| `CoveringSystem.moduli` | the set of moduli, as `Finset ℕ` |
| `CoveringSystem.hasDistinctModuli` | `Nodup` on the moduli list |
| `CoveringSystem.minModulus` | `cs.moduli.min'` |

| Theorem | Status |
|---|---|
| `single_class_not_covering` | proved |
| `covering_distinct_has_ge_two_classes` | proved |
| `covering_distinct_moduli_card_ge_two` | proved |
| `CoveringSystem.minModulus_mem` | proved |
| `bottleneck_counterexample` | proved (was axiom, discharged in PR #7893) |
| `erdos_8_resolution` | proved (was axiom, discharged in PR #7893) |
| `erdos_8_false` | proved |
| `balister_improved_bound` | proved (trivially, same bound as Hough — placeholder) |
| `erdos_8_summary` | proved |

Two remaining axioms (`hough_minimum_modulus`, `density_conjecture_false`)
are **deep, published results** — see the assessment in the linked
session note.

## Reference

- Hough, B. (2015), *Solution of the minimum modulus problem for covering
  systems*, **Annals of Mathematics** 181 (1), 361-382. [arXiv:1307.0874]
- Balister, P., Bollobás, B., Morris, R., Sahasrabudhe, J., Tiba, M.
  (2022), *On the Erdős covering problem*, *Invent. Math.* 228, 377-414.
  [arXiv:2104.13145]
- Cao, J. (2018), Various improvements on small-bound covering systems.
- Erdős, P., Graham, R. (1980), *Old and new problems and results in
  combinatorial number theory*, §6.
