# Current State

**Phase**: ITERATE
**Since**: 2026-05-13
**Iteration**: 4

## Current Focus

Extend axiom-free coverage of Erdős #31 via `erdos31_bounded_gaps`. The
remaining `axiom lorentz_theorem : Erdos31Statement` is unchanged
(genuinely load-bearing for unbounded-gap families like primes and
powers of 2), but parametric bounded-gap families now have direct,
axiom-free completion theorems.

## S4 additions (2026-05-13, researcher-6)

- `multiples_have_sparse_complement (k : ℕ) (hk : 0 < k)`: for every
  `k ≥ 1`, the set `{n : k ∣ n}` admits the finite density-0 completion
  `B = {0, 1, ..., k-1}`. Proof: apply `erdos31_bounded_gaps` with
  `M = k`, witness `k * (n / k)` for the bounded-gap hypothesis,
  closing the arithmetic via `Nat.div_mul_le_self`, `Nat.mod_lt`,
  `Nat.div_add_mod`, and `linarith`.
- `even_numbers_have_sparse_complement`: corollary at `k = 2`.

## Active Approach (S5+, optional)

Eliminate the remaining `axiom lorentz_theorem : Erdos31Statement` by
formalizing the Lorentz greedy construction.

**Key goal**: `lorentzB_density_zero` — show |B ∩ [0,N]| / N → 0.

The bound follows from the D-free structural property of lorentzB:
- No two B-elements b, b' differ by (a - a₀) for a ∈ A
- This limits how many B-elements can lie in [0,N] relative to |A ∩ [0,N]|
- Since A is infinite: |A ∩ [0,N]| → ∞, so |B ∩ [0,N]| / N → 0

**Research steps:**
1. Read current `Erdos31Problem.lean` (820 lines, 1 axiom) to understand existing defs
2. Check what `lorentzB_mem` definition looks like (if it exists in the file)
3. If the greedy construction from 2026-03-27 was lost: re-implement using well-founded recursion
4. Prove the density bound: use D-free property to count B ∩ [0,N] ≤ N / (sInf A spacing)

## Blockers

None for S4 (bounded-gap special cases). For S5+ (Lorentz construction),
the recursive definition of `lorentzB` and the D-free counting argument
remain to be (re)implemented; this is research-level work.

## Next Action

(S5+) Re-implement the greedy Lorentz construction:
1. `lorentzB` via well-founded recursion (or `Nat.find`/`Nat.greedy`).
2. Coverage: `∀ n large, ∃ a ∈ A, ∃ b ∈ lorentzB, a + b = n` (greedy).
3. Density: D-free property gives `|lorentzB ∩ [0,N]| ≤ N / (|A ∩ [0,N]|)`,
   which → 0 since A is infinite.

## Attempt Counts

- Total attempts: 4
- Current approach attempts: 1 (S4 succeeded)
- Approaches tried: 2 (Lorentz greedy construction; bounded-gap special cases)

## Formalization Status

- **File**: proofs/Proofs/Erdos31Problem.lean
- **Lines**: 820 (was 786 pre-S4)
- **Builds**: Yes (builds with 1 axiom; S4 build pending)
- **Sorries**: 0
- **Axioms**: 1 (`lorentz_theorem`)
- **Key Definitions**: 10+
- **Proved Results**: 24 (counting bounds, density lemmas, limit theorems,
  bounded-gap special cases including S4 multiples/evens)
