# Current State

**Phase**: ACT
**Path**: full
**Since**: 2026-03-25 (gallery entry shipped)
**Last Updated**: 2026-05-08 (Iteration 5, researcher-11)
**Iteration**: 5

## Current Focus

**1 axiom remains** in `proofs/Proofs/Erdos864Problem.lean` (806 lines, 22
theorems, 8 definitions, 0 sorries on origin/main):

- `erdos_freud_lower_bound` — the Erdős–Freud 1991 lower bound
  `maxAlmostSidon N ≥ (1 + o(1)) · (2/√3) · √N`. Proved on paper via the
  reflected construction `A = B ∪ {N − b : b ∈ B}` for `B ⊆ {1,...,N/3}`
  Sidon. Eliminating this axiom would require importing or developing
  asymptotic analysis machinery sufficient to discharge the `(1 + o(1))`
  factor; the underlying combinatorics (`reflected_construction_bound` at
  line 796) is **already proved** as a non-asymptotic theorem.

## Iteration History

- **Iter 1** (2026-03-25, PR #6838): enrichment + cross-references for
  the gallery entry alongside erdos-770, erdos-892, abel-ruffini.
- **Iter 2** (2026-03-27, PR #7235): identified redundant axiom; first
  pass on axiom elimination. Followed by:
- **Iter 2 cont.** (2026-03-27, PR #7139): axiom elimination across
  erdos-478/382/864 — 6 axioms eliminated total.
- **Iter 3** (2026-03-28, PR #7258, PR #7330): infrastructure +
  Fermat structural theory. Axiom elimination continued.
- **Iter 3 cont.** (2026-03-28, PR #7308): proved
  `sidon_counting_bound` (k(k+1)/2 ≤ 2N − 1) and `edgeCount_le`
  (the tight `n(n-1)/2` bound).
- **Iter 4** (2026-03-28, PR #7277): audit axiomCount fix 3→2
  alongside erdos-913 and erdos-159 lineCount fixes; later
- **Iter 4 cont.** (2026-04-03, PR #8740): True-stub cleanup.
- **Iter 5** (2026-05-08, this PR, researcher-11): state.md sync to
  reflect the actual state of the formalization (was at iter 1 NEW for
  six weeks despite ~10 merged PRs).

## Built Items (current snapshot)

**Definitions** (8): `sumRepCount`, `multiRepSet`, `IsAlmostSidon`,
`IsSidon`, `maxAlmostSidon`, plus three derived sets used in the
reflected construction.

**Theorems** (22), grouped by section:

- **Almost-Sidon ↔ Sidon bridge**: `almost_sidon_exceeds_sidon`,
  `sidon_is_almost_sidon`, `isAlmostSidon_empty`, `isAlmostSidon_subset`.
- **Combinatorial counts**: `pairwise_sum_count`, `sum_in_range`.
- **Sidon-set basics**: `isSidon_empty`, `sumRepCount_subset`,
  `isSidon_subset`, `distinct_sums_bounded`.
- **Sidon counting bounds**: `sidon_counting_bound` (k(k+1)/2 ≤ 2N−1),
  `sidon_card_sq_le` (k² ≤ 4N), `sidon_diff_counting_bound`,
  `sidon_card_sq_le_2N` (k² ≤ 2N + k — sharper than the `4N` form).
- **Sum-of-rep characterization**: `sum_rep_iff_sidon` and helpers.
- **Reflected construction**: `reflected_construction_valid` (the
  reflected B ∪ (N−B) is almost-Sidon for B Sidon), `reflection_injOn`,
  `reflection_disjoint`, `reflection_card`, `reflection_subset_bound`,
  `reflected_construction_bound` (non-asymptotic combinatorial bound).

## Active Approach

The axiom `erdos_freud_lower_bound` is asymptotic; eliminating it
requires either Mathlib's asymptotic-equality framework or a proof
that the combinatorial `reflected_construction_bound` extends
asymptotically. The latter requires developing an explicit Sidon
construction `B ⊆ {1,...,N/3}` of size `(1+o(1))·√(N/3) = (1+o(1))·√N/√3`,
e.g., a Singer-set or Erdős–Turán construction. Singer sets are
in scope for Mathlib (they exist as a research target in Mathlib's
NumberTheory.Singer issue list), but not yet imported here.

## Blockers

None for axiom-side work; one axiom remains and is appropriate as an
asymptotic-analysis limit.

The underlying combinatorial bound (`reflected_construction_bound`) is
already non-asymptotic and proved.

## Next Action

**Iter 6 candidate**: prove `almost_sidon_card_bound`, the dual
**upper bound** for almost-Sidon sets (currently absent — only the
Sidon upper bound `k² ≤ 4N` and `k² ≤ 2N + k` are present).

Statement (rough): for almost-Sidon `A ⊆ {1,...,N}`,
`|A|(|A|+1) ≤ 4N + 2|A| − 4` (equivalently `k² ≤ 4N + k − 4`).

Proof sketch: distinct sums = k(k+1)/2 − collisions; almost-Sidon
caps collisions at `c − 1` for the one repeated value `n`, where
`c ≤ k` (each value `n` has at most `k` representations
`(a, n−a)` with `a ∈ A`). Therefore distinct sums `≥ k(k+1)/2 − (k−1)`,
which combined with `distinct sums ≤ 2N − 1` gives the bound.

This would be the **first proven upper bound for the almost-Sidon
problem** in this gallery entry, complementing the lower-bound axiom.

## Attempt Counts

- Total attempts: 5
- Current approach attempts: 1 (state.md sync, this PR)
- Approaches tried (axiom-side): infrastructure + bridge construction
  (Iter 1–4); state sync (Iter 5).

## References

- `proofs/Proofs/Erdos864Problem.lean` — main file (806 lines, 22
  theorems, 8 defs, 1 axiom, 0 sorries).
- `src/data/proofs/erdos-864/meta.json` — gallery integration.
- Erdős–Freud 1991: "On disjoint sets of differences", *J. Number Theory* 38.
- Erdős 1992 commentary on the Erdős–Freud problem.
