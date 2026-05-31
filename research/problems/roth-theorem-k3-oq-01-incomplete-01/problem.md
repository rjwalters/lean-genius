# Problem: Roth's Theorem: Main k=3 Formalization

**Slug**: roth-theorem-k3-oq-01-incomplete-01
**Created**: 2026-04-03
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\forall \delta > 0, \exists N_0: \forall N \geq N_0, A \subset \mathbb{Z}_N, |A| \geq \delta N \Rightarrow A \text{ has 3-AP}
$$

### Plain Language

Main sorry-filling task for Roth's theorem. The Lean file `RothTheoremQuantitative.lean` has **4 sorries** remaining (Roth 1953, Behrend 1946, Bloom–Sisask 2020, Kelley–Meka 2023 — all landmark quantitative bounds). Mathlib corners chain provides the key building block.

**Note:** Problem.md initial draft said "5 sorries" — corrected to 4 on 2026-05-31 after direct inspection of the source file. The fifth slot was `density_upper_bound_from_iteration`, which was removed because the claimed bound `r₃(N) ≤ 10√N` is false for large `N` (Behrend gives `r₃(N) ≥ N · exp(-c√log N) ≫ √N`).

### Why This Matters

See `src/data/proofs/roth-theorem-k3-oq-01/meta.json` for full context. This is a targeted completion/extension of an existing gallery proof.

## Known Results

### What's Already Proven

- Parent proof `roth-theorem-k3-oq-01` provides the foundation (`Szemeredi.Roth.Quantitative.rothNumber`, basic bounds, exact values `r₃(2) = 1`, `r₃(3) = 2`, density-increment iteration bound).
- `RothTheorem.lean` proves the qualitative `roth_density_bound` (∀ δ > 0, ∃ N₀, density `δ` AP-free subsets are impossible for `N ≥ N₀`) via Mathlib's `roth_3ap_theorem_nat`.
- 0 `axiom` declarations, 0 structure-encoded assumptions.
- Sorries to fill: **4**, all landmark quantitative bounds:
  1. `roth_quantitative_upper_bound` (Roth 1953): `r₃(N) ≤ C · N / log log N`
  2. `behrend_lower_bound` (Behrend 1946): `r₃(N) ≥ N · exp(-c · √(log N))`
  3. `bloom_sisask_bound` (Bloom–Sisask 2020): `r₃(N) ≤ N / (log N)^{1+c}`
  4. `kelley_meka_upper_bound` (Kelley–Meka 2023): `r₃(N) ≤ N · exp(-c · (log N)^{1/12})`

### Our Goal

Each of the four sorries is a deep landmark result requiring ≥ 1000 lines of formalization (Behrend's sphere construction, Roth's modulus-tracking density increment, Bloom–Sisask's quantitative Bogolyubov, Kelley–Meka's polynomial-method density increment on Bohr sets). None is tractable in a single session.

**Tractable adjacent contribution (2026-05-31 session):** Add the *qualitative* asymptotic `rothNumber_div_tendsto_zero : Tendsto (n ↦ rothNumber n / n) atTop (𝓝 0)` to the file. This is provable from the existing `Szemeredi.Roth.roth_density_bound` and gives a proved qualitative ceiling that the four sorried bounds sharpen.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `roth-theorem-k3-oq-01` | Direct parent — inspect its Lean file for sorry locations |

## Tractability Assessment

**Difficulty**: Challenging

## Metadata

```yaml
tags:
  - combinatorics
  - roth
  - arithmetic-progressions
  - fourier
related_proofs:
  - roth-theorem-k3-oq-01
difficulty: challenging
source: gallery-gap
created: 2026-04-03
```

**Significance**: 8/10
**Tractability**: 4/10
