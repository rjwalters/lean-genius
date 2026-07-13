# Knowledge: Erdős 678 - LCM of Consecutive Integer Intervals

## Problem Summary

Erdős Problem #678: Let M(n,k) = lcm{n+1, ..., n+k}. Are there infinitely many m,n,k ≥ 3
with m ≥ n+k such that M(n,k) > M(m,k+1)?

Answer: YES (Stijn Cambie, 2024). The formalization has 7 remaining sorrys (down from 11,
file now compiles).

## Session 2026-04-04 (Session 1) - Fix compilation + prove 4 sorrys

**Mode**: FRESH
**Outcome**: progress

### What I Did
- Fixed compilation: file previously failed to build due to ambiguous `lcm` in
  `(Finset.range k).fold lcm 1 (fun i => n+1+i)`. With `open Finset Nat`, Lean couldn't
  resolve `lcm`. Fixed by using `Nat.lcm` explicitly.
- Proved `intervalLcm_eq_intervalLcm'`: uses `Finset.fold_image` with bijection
  `(fun i => n+1+i) : range k → Icc (n+1) (n+k)`, proved via `ext; simp; omega`
- Proved `intervalLcm_mono_right`: `range k ⊆ range (k+1)` via `range_succ` + `fold_insert`
  → `intervalLcm n (k+1) = Nat.lcm (n+k+1) (intervalLcm n k)` → `Nat.dvd_lcm_right`
- Proved `dvd_intervalLcm`: induction on k, using `fold_insert` + `dvd_lcm_{left,right}`
- Proved `prime_power_divides_intervalLcm`: direct from `dvd_intervalLcm` via bound arithmetic
- Removed wrong expected values: `intervalLcm_96_7 = 1073741700` and `intervalLcm_104_8 = 786145080`
  were WRONG (file never compiled, these were never verified). Actual values:
  - `intervalLcm 96 7 = lcm(97..103) = 8,321,670,749,700` (not 1,073,741,700)
  - `intervalLcm 104 8 = lcm(105..112) ≈ 3,803,928,503,760`
- Fixed `minimalN` def: added `noncomputable` + `Classical.decPred` to fix typeclass error

### Key Findings
- `intervalLcm_chebyshev_upper` (M(n,k) ≤ 4^k) is **FALSE as stated** for n > 0:
  M(96, 7) ≈ 8.3 × 10^12 ≫ 4^7 = 16384. True only for n=0 (i.e., lcm(1..k) ≤ 4^k).
- Key fold manipulation pattern: `range_succ` + `fold_insert not_mem_range_self` converts
  `intervalLcm n (k+1)` to `Nat.lcm (n+k+1) (intervalLcm n k)`.
- `Finset.fold_image` signature: `(image g s).fold op b f = s.fold op b (f ∘ g)` when g injOn s.
  Use `conv_rhs` to apply it to the RHS of an equality.

### Files Modified
- `proofs/Proofs/Erdos678Problem.lean`: fixed compilation, proved 4 sorrys (11→7)

### PR
- https://github.com/rjwalters/lean-genius/pull/9294

### Remaining 7 Sorrys

| Sorry | Why blocked |
|-------|-------------|
| `erdos_678_infinitely_many` | Needs Cambie 2024 proof |
| `cambie_2024` | Needs Cambie 2024 proof |
| `interval_skip_prime_power` | Complex prime power analysis |
| `intervalLcm_growth` | Needs Chebyshev-type theorem |
| `intervalLcm_chebyshev_upper` | FALSE as stated (should be restricted to n=0) |
| `minimalN` existence | Needs k ≥ 7 existence for all large k |
| `erdos_growth_rate` | Needs Erdős result on growth of minimal n |

### Next Steps
1. Fix `intervalLcm_chebyshev_upper` statement to `n = 0` version, then prove via
   `Nat.centralBinom` or prime counting bounds
2. Attempt `interval_skip_prime_power` — prime power gap analysis in intervals
3. `erdos_678_infinitely_many` is OPEN (Cambie 2024 not yet in Mathlib)
