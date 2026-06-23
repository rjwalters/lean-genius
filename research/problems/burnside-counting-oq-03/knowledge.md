# Problem: Burnside Counting: Generalize to Pólya Enumeration

**Problem ID**: burnside-counting-oq-03
**Status**: in-progress (ACT phase)
**Parent**: burnside-counting (existing gallery proof)

## Problem Statement

Generalize the Burnside necklace counting from `BurnsideCounting.lean` to the full
Pólya enumeration theorem for cyclic groups. The key result:

For cyclic rotation of Z_n on Fin n → Fin k (k-colorings of n positions):
  |Fix(r)| = k^gcd(r, n)

  n · (#distinct k-necklaces) = Σ_{r : Fin n} k^gcd(r, n)
                               = Σ_{d | n} φ(n/d) · k^d

## Session 2026-04-04 (Session 1) - Initial Research and Implementation

**Mode**: FRESH
**Outcome**: progress (file built, 4 sorries remain, concrete n=4 computations proved)

### What I Did

1. Surveyed existing `BurnsideCounting.lean` (256 lines, 5 axioms)
2. Identified key Mathlib lemma: `ZMod.addOrderOf_coe` giving `addOrderOf r = n / gcd(n, r.val)`
3. Identified key mathematical insight: orbit of position i under rotation r is {j | j ≡ i mod gcd(r,n)}
4. Created `proofs/Proofs/BurnsideCountingOQ03.lean` (230 lines)
5. Created gallery data: `src/data/proofs/burnside-counting-oq-03/`

### Key Findings

- **Orbit structure**: For rotation r in Z_n, orbit of i = {j | j ≡ i mod gcd(r,n)}
  This follows from: subgroup <r> in Z_n = {0, r, 2r, ...} = gcd(r,n)·Z_{n/gcd(r,n)}
- **Fixed-point formula**: |Fix(r)| = k^gcd(r,n) (bijection fixed-colorings ↔ Fin gcd → Fin k)
- **Mathlib bridge**: `ZMod.addOrderOf_coe` + `ZMod.natCast_zmod_val` proves `addOrderOf r = n/gcd(n,r)`
- **Proved by native_decide**: fixed-point counts for n=4 (16, 2, 4, 2), sum = 24, Pólya sums

### Files Modified

- `proofs/Proofs/BurnsideCountingOQ03.lean` (created, builds with 4 sorries)
- `src/data/proofs/burnside-counting-oq-03/` (created: meta.json, annotations.json, index.ts)
- `src/data/research/problems/burnside-counting-oq-03.json` (updated: status, knowledge)

### What's Proved (✓) vs Remaining Sorries (◐)

✓ `addOrderOf_rotation`: addOrderOf r = n/gcd(n, r.val) — uses ZMod.addOrderOf_coe
✓ `fp_count_rot{0,1,2,3}_4_2`: concrete fixed-point counts 16, 2, 4, 2 — native_decide
✓ `fp_sum_binary4`: Burnside sum = 24 — from the 4 counts above
✓ `polya_sum_Z4_binary`: Σ_{r:Fin4} 2^gcd(r,4) = 24 — native_decide
✓ `polya_divisor_sum_Z4_binary`: Σ_{d|4} φ(4/d)·2^d = 24 — native_decide
✓ `polya_sum_equiv_4_2`: two formulations equal — native_decide
✓ `polya_binary4_necklace_count`: 24/4 = 6 — norm_num

◐ `fixed_factors_through_mod`: orbit = cosets of <r>
◐ `polya_cyclic_fixed_count`: |Fix(r)| = k^gcd(r,n) general case
✓ `polya_sum_identity`: proved via fiber decomposition + bijection (Session 2)
✓ `polya_necklace_formula_statement`: Burnside connection (Session 1)

### Session 2026-04-04 (Session 2) - Proved polya_sum_identity

**Mode**: REVISIT
**Outcome**: progress (1 sorry closed)

#### What I Did
1. Proved `polya_sum_identity`: Σ_{r:Fin n} k^gcd(r,n) = Σ_{d|n} φ(n/d)·k^d
   - Used `Finset.sum_fiberwise_of_maps_to` to decompose by fiber d = gcd(r,n)
   - Proved helper `fiber_card_eq_totient`: |{r:Fin n | gcd(r,n)=d}| = φ(n/d)
   - Bijection r ↦ r.val/d with {s < n/d | Coprime(n/d, s)}, using `Nat.coprime_div_gcd_div_gcd`

#### Key Lean 4.26 API Findings
- `Finset.sum_fiberwise_of_maps_to` has equation REVERSED: `fiber_sum = original_sum`. Need `.symm` or `have ... ; rw [← ...]` to use it for `original_sum = fiber_sum`
- `Nat.mul_lt_mul_left` is an IFF (use `.mpr`), not a direct implication
- `Fin.ext` replaces missing `Fin.val_eq_val.mp`
- `omega` cannot handle variable multiplication (`d * x = r, d * x = r'` when `d` is a variable); use `linarith [congr_arg (d * ·) heq]`
- `Nat.coprime_div_gcd_div_gcd` gives `Coprime (m/gcd m n) (n/gcd m n)` when `0 < gcd m n`

#### Remaining Sorries
- `fixed_factors_through_mod`: orbit = cosets of <r> in ZMod n (hard, ZMod arithmetic)
- `polya_cyclic_fixed_count`: |Fix(r)| = k^gcd(r,n) bijection (depends on above)

### Next Steps

1. **Prove `fixed_factors_through_mod`**: Use Bezout's theorem to show orbit membership
   - Need: `Nat.gcd_dvd_left`, `Nat.dvd_sub'`, Bezout coefficients
   - Approach: show i.val - j.val ∈ <r.val, n> iff gcd(r.val,n) | (i.val - j.val) in ZMod n
2. **Prove `polya_cyclic_fixed_count`**: Construct explicit bijection fixed-colorings ↔ Fin d → Fin k
   - Forward: c ↦ (j ↦ c ⟨j.val, ...⟩) for j : Fin d (orbit representatives {0,...,d-1})
   - Backward: f ↦ (i ↦ f ⟨i.val % d, ...⟩) (assign color by orbit representative)

## Mathematical Background

### Pólya Enumeration for Cyclic Groups

The **Pólya cycle index** for Z_n acting on Fin n is:
  Z(Z_n) = (1/n) Σ_{r=0}^{n-1} x_{gcd(r,n)}^{n/gcd(r,n)}

When evaluated at x_j = k for all j (all variables equal k):
  Z(Z_n; k, k, ..., k) = (1/n) Σ_r k^gcd(r,n)

The **simplified Pólya formula**: #necklaces = (1/n) Σ_{d|n} φ(d) · k^{n/d}
(Here φ(d) = #{r : gcd(r,n) = n/d}... wait, let me recalculate.
Actually: #{r : gcd(r,n)=d} = φ(n/d). So:
  Σ_r k^gcd(r,n) = Σ_{d|n} φ(n/d) · k^d.
Dividing by n: #necklaces = (1/n) Σ_{d|n} φ(n/d) · k^d.)

### Key Mathlib Lemmas

- `ZMod.addOrderOf_coe`: addOrderOf (↑a : ZMod n) = n / n.gcd a
- `ZMod.natCast_zmod_val [NeZero n] (a : ZMod n) : (a.val : ZMod n) = a`
- `IsCyclic.card_orderOf_eq_totient`: #{a : cyclic group | orderOf a = d} = φ(d) for d | n
- `Nat.sum_totient`: Σ_{d|n} φ(d) = n
