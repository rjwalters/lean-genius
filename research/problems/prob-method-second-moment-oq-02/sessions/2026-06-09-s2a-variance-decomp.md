# 2026-06-09 — S2-A ACT: generic variance decomposition (Docker-clean)

**Researcher**: researcher-7
**Phase**: S2 ACT (was: S2 ACT ready post-S1g 27-day stall)
**Cycle**: PREP → ACT — first Lean code on this slug after seven doc-only PRs
(S1, S1b, S1c, S1d, S1e, S1f, S1g; 2026-05-12 → 2026-05-13)

## What shipped

`proofs/Proofs/ProbMethodSecondMomentOQ02.lean` — 153 lines, 9 theorems,
3 definitions, **0 sorries, 0 axioms, Docker 7744 jobs clean**.

Plus pre-existing Mathlib drift fixes to the parent (`div_le_iff` →
`div_le_iff₀`, `pow_le_pow_left` → `pow_le_pow_left₀`, drop redundant
`ring` after `field_simp`) — needed to make this file's parent import
build at the current Mathlib snapshot `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
checkout of pin `v4.26.0`.

## Headline identity

For ℚ-valued functions `X : ι → α → ℚ` on a Finset `s` (counting-measure
sample space) and an index Finset `t : Finset ι`:

    Var(∑_{i ∈ t} X i) = ∑_{(i,j) ∈ t ×ˢ t} Cov(X i, X j)

(`variance_sum_eq_sum_covariance`). This is the pair-sum form of the
textbook decomposition

    Var(∑) = ∑ Var + ∑_{i ≠ j} Cov,

deferred to a follow-up via `Finset.diag_union_offDiag`.

## Theorem inventory

| # | Name | Statement | Notes |
|---|------|-----------|-------|
| 1 | `variance_eq_covariance_self` | Var(f) = Cov(f, f) | `simp only [sq]` |
| 2 | `covariance_symm` | Cov(f, g) = Cov(g, f) | `ring` per summand |
| 3 | `mean_add` | mean (f + g) = mean f + mean g | linearity of `Finset.sum` |
| 4 | `covariance_add_left` | Cov(f₁+f₂, g) = Cov(f₁, g) + Cov(f₂, g) | bilinearity |
| 5 | `covariance_add_right` | Cov(f, g₁+g₂) = Cov(f, g₁) + Cov(f, g₂) | by symmetry |
| 6 | `variance_add` | Var(f+g) = Var f + Var g + 2·Cov(f, g) | pair case |
| 7 | `covariance_sum_left` | Cov(∑_t X, g) = ∑_t Cov(X i, g) | Finset induction |
| 8 | `covariance_sum_right` | Cov(f, ∑_t Y) = ∑_t Cov(f, Y j) | by symmetry |
| 9 | `variance_sum_eq_sum_covariance` | Var(∑_t X) = ∑_{t ×ˢ t} Cov | **headline**, via `Finset.sum_product` |

Definitions: `mean`, `variance`, `covariance` (all over a Finset `s`,
ℚ-valued, counting-measure).

## Pinned Mathlib bearers (re-verified 2026-06-09)

| Bearer | Path (Mathlib SHA `2df2f01…`) | Used by |
|---|---|---|
| `Finset.sum_add_distrib` | Mathlib.Algebra.BigOperators.Group.Finset.Basic | mean_add, covariance_add_left |
| `Finset.sum_product` | Mathlib.Algebra.BigOperators.Group.Finset.Sigma:81 | variance_sum_eq_sum_covariance |
| `Finset.sum_insert` | Mathlib.Algebra.BigOperators.Group.Finset.Defs | covariance_sum_left induction |
| `Finset.sum_const_zero` | Mathlib.Algebra.BigOperators.Finsupp.Basic | empty case of covariance_sum_left |
| `div_le_iff₀` | Mathlib.Algebra.Order.Field.Basic (was `div_le_iff` pre-snapshot) | parent fix |
| `pow_le_pow_left₀` | Mathlib.Algebra.Order.GroupWithZero.Basic:470 (was `pow_le_pow_left` pre-snapshot) | parent fix |

## Scope discipline

Single Lean file added (`ProbMethodSecondMomentOQ02.lean`); single
import line added to `proofs/Proofs.lean`; single new gallery directory
`src/data/proofs/prob-method-second-moment-oq-02/` with one `meta.json`.
Plus the two-line drift fix to the parent + OQ-01 (3 lines total). No
other files touched.

## Follow-up scope (out of this PR)

- **§A.2 diag/offDiag split**: `variance_sum_eq_diag_plus_offDiag` —
  one Finset.diag_union_offDiag application on the pair-sum form.
  Independent of any new Mathlib infrastructure; ~15 LOC.
- **§A.3 `variance_indicator` collapse**: for f a ∈ {0,1}, simplify
  Var(f) = mean f − (mean f)². Pure algebra (~15 LOC), independent
  of §A.1 pair-sum.
- **§B G(n,p) construction**: defer until S1d's `PMF.ofFintype`
  bearer is re-verified at current pin (S1d's `Fintype.sum_pow_mul_eq_add_pow`
  cite was confirmed by S1g — but at T-27d, worth a fresh check).
- **§C Paley-Zygmund route**: parent's `paley_zygmund_quantitative`
  already provides the discrete-Finset Paley-Zygmund. The OQ-01 file
  exposes the probability form. So §C may be already in place for
  the threshold-function downstream — to be evaluated when §B lands.

## Build verification

`./proofs/scripts/docker-build.sh Proofs.ProbMethodSecondMomentOQ02`
finished in ~3 minutes wall-clock with 7744 successful jobs after
the parent-drift fixes. No warnings. The build cache downloaded
7727 Mathlib oleans; only ~17 oleans rebuilt locally
(`ProbMethodSecondMoment`, `ProbMethodSecondMomentOQ01`, and the
new `ProbMethodSecondMomentOQ02`).

## State delta

- Iteration: 2 → 3
- Phase: S2 ACT ready → **S2-A ACT complete** (S2-B = diag/offDiag
  split, S2-C = §B G(n,p), S2-D = §C Paley-Zygmund evaluation)
- Files added: 1 Lean + 1 meta.json + 1 session note + this state edit
- Files modified: parent (3 lines drift fix) + OQ-01 (1 line drift fix)
  + Proofs.lean (1 import line)
- Total LOC delta: +153 Lean (new file) + 5 drift-fix lines = +158 Lean
