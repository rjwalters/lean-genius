# Knowledge Base: cantor-diagonalization-oq-01-oq-01-oq-02-oq-03

## Problem Understanding

Does the parent's proof of cf(2^ℵ₀) > ℵ₀ (using `Cardinal.lt_cof_power`) generalize to
cf(2^ℵ_α) > ℵ_α for all ordinals α? Can the full generalized continuum function 2^ℵ_α
be analyzed uniformly?

## Key Insights

- **YES, immediate generalization**: `Cardinal.lt_cof_power le_rfl (by norm_num)` works
  verbatim with `aleph α` replacing `aleph 0`. The Mathlib theorem is already stated for
  arbitrary κ: `λ ≤ κ → 1 < μ → λ < cf(μ^κ)`. Setting μ=2, κ=λ=ℵ_α gives the result.

- **Monotonicity via gcongr**: `(2 : Cardinal)^aleph α ≤ (2 : Cardinal)^aleph β` for
  `α ≤ β` follows from `gcongr` + `aleph_le_aleph.mpr h`.

- **Successor bound**: `ℵ_{α+1} = (ℵ_α)⁺ ≤ 2^ℵ_α` via `aleph_succ` +
  `Order.succ_le_of_lt (two_pow_aleph_gt_aleph α)`.

- **König exclusion at every ordinal**: If `cf(ℵ_β) ≤ ℵ_α`, then `2^ℵ_α ≠ ℵ_β`.
  Proof: if equal, then cf(2^ℵ_α) = cf(ℵ_β) ≤ ℵ_α contradicts König.

- **Cantor's theorem**: `Cardinal.lt_two_pow (aleph α)` gives `ℵ_α < 2^ℵ_α` for free.

## Session 2026-04-13 (Session 1) - Formalization

**Mode**: FRESH
**Outcome**: completed

### What I Did
- Created `proofs/Proofs/CantorDiagonalizationOQ01OQ01OQ02OQ03.lean` (117 lines)
- Proved `konig_aleph_general` for all ordinals α (0 sorries, 0 axioms)
- Proved three specific instances (α=0, α=1, α=ω)
- Proved `two_pow_aleph_gt_aleph` (Cantor at all alephs)
- Proved `two_pow_aleph_mono` (monotonicity)
- Proved `aleph_succ_le_two_pow_aleph` (successor bound)
- Proved `two_pow_aleph_ne_aleph_of_cof_le` (König exclusion)
- Proved `generalized_continuum_summary` combining all three main results

### Files Created
- `proofs/Proofs/CantorDiagonalizationOQ01OQ01OQ02OQ03.lean` (117 lines, 0 sorries, 0 axioms)
- `src/data/proofs/cantor-diagonalization-oq-01-oq-01-oq-02-oq-03/meta.json`
- `research/problems/cantor-diagonalization-oq-01-oq-01-oq-02-oq-03/knowledge.md`
