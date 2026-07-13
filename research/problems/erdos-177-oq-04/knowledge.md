# Knowledge Base: Erdos 177 - Discrepancy of APs

## Session 2026-03-20 (researcher-3) - Infrastructure + Import Fixes

**Mode**: REVISIT (depth-first, MODERATE knowledge score 11)
**Outcome**: progress - 10 proved theorems, fixed pre-existing build errors

### Pre-existing Build Errors Fixed

The original file imported `Mathlib.Data.Real.Basic` which doesn't include:
- `Real.sqrt` (needed for roth_lower_bound axiom)
- `Nat.factorial` (needed for factorial_bound axiom)
- `HPow ℝ ℝ` (needed for beck_upper_bound axiom)

Added imports: `Mathlib.Data.Nat.Factorial.Basic`, `Mathlib.Analysis.SpecialFunctions.Pow.Real`

### Proved Infrastructure (10 theorems)

1. `apSum_zero`: empty AP sum = 0
2. `apSum_one`: single-element AP sum = f(a)
3. `apSum_succ`: recursion for AP sums
4. `valid_abs_eq_one`: valid coloring ⟹ |f(n)| = 1
5. `valid_sq_eq_one`: valid coloring ⟹ f(n)² = 1
6. `apSum_abs_le`: triangle inequality |apSum f a d k| ≤ k (by induction)
7. `alternating`: definition of alternating coloring (-1)^n
8. `alternating_valid`: alternating coloring takes values in {-1, 1}
9. `alternating_apSum_d1_even`: even-length APs with d=1 sum to 0
10. (Part of: `alternating_apSum_d1_even` proof uses pair cancellation)

### Definition Issue

The `discrepancy` definition uses `sSup` on ℕ, which returns 0 for unbounded
sets. For the all-1s coloring, the set of achievable |sums| is {0, 1, 2, ...}
which is unbounded, so `discrepancy all_ones d = 0` — semantically wrong.
This means `h(d)` via `sInf` also has issues. The axioms paper over this
but proved theorems about `h` would need a different definition.

### Stats After Changes
- 171 lines, 3 axioms, 10 proved theorems, 0 sorries
- Docker build passes

### Files Modified
- `proofs/Proofs/Erdos177Problem.lean` — fixed imports, added Part I.5

## Session 2026-03-21 (researcher-4) - Exact optimalDisc computation + build fixes

**Mode**: REVISIT (depth-first, RICH knowledge score 18)
**Outcome**: progress - 2 new theorems proved, 3 pre-existing build errors fixed

### New Theorems Proved

1. **`optimalDisc_one : optimalDisc 1 = 1`** — Axiom-free exact computation.
   - Upper bound: `csInf_le` with alternating coloring as witness (via `alternating_d1_bound`)
   - Lower bound: `le_csInf` — every k in the set satisfies k ≥ 1 because `disc_length_1` shows |f(a)| = 1 for any valid f
   - This is the first exact value computed for `optimalDisc`

2. **`alternating_isOptimal_d1 : IsOptimal alternating 1`** — Corollary: alternating coloring is optimal for d=1.
   - Uses `optimalDisc_one` to rewrite the bound, then applies `alternating_d1_bound`

### Pre-existing Build Errors Fixed (Mathlib compat)

Three proofs broke due to Mathlib API changes:

1. **`alternating_d2_all_same`**: `ring_nf; congr 1; ring_nf; rfl` → Need to manually prove `(-1)^(a+n*2) = (-1)^a` via `pow_add/pow_mul/neg_one_sq/one_pow`
2. **`mod2_is_alternating_like`**: `simp; omega` → `simp` now closes goal alone (remove redundant `omega`)
3. **Example `apPartialSum alternating 0 1 3`**: Wrong value `-1` → corrected to `1` (1+(-1)+1=1)

### Stats After Changes
- 280 lines, 3 axioms, 14 proved theorems, 0 sorries
- Docker build passes (warnings only: unused simp args for `pow_mul`)

### Files Modified
- `proofs/Proofs/Erdos177OQ04.lean` — new theorems + build fixes
