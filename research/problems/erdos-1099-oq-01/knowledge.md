# Erdős Problem #1099: Divisor Ratio Sum Boundedness

**Problem**: For α > 1, is liminf h_α(n) bounded, where h_α(n) = Σ((d_{i+1}/dᵢ) - 1)^α?
**Answer**: YES (Vose, 1984)
**Status**: IN-PROGRESS (0 sorries, 1 axiom)

## Current State

- **File**: `proofs/Proofs/Erdos1099Problem.lean` (~622 lines)
- **Sorries**: 0
- **Axioms**: 1 (vose_bounded_sequence — deep Vose 1984 construction)
- All helper lemmas fully proved, file compiles clean

## Session 2026-03-25 (Session 4) - Prove sortedDivisors_two_pow and divisorRatios_two_pow (0 sorries)

**Mode**: REVISIT (RICH knowledge, score 30)
**Outcome**: progress (2S → 0S, eliminated all sorries)

### What I Did
- Proved `list_range_pairwise_lt`: `(List.range n).Pairwise (· < ·)` by induction using `range_succ` + `pairwise_append`
- Proved `sortedDivisors_two_pow`: divisors of 2^k = [1,2,4,...,2^k] via `Perm.eq_of_pairwise` pattern (nodup + sorted + same elements via `Nat.divisors_prime_pow`)
- Proved `geo_ratios_aux`: generalized geometric ratio lemma — for consecutive powers 2^s, 2^(s+1), ..., the ratios are all 2, by induction on k with `push_cast`/`pow_succ`/`mul_div_cancel_left₀`
- Proved `divisorRatios_two_pow`: decompose `range(k+1)` as `0 :: range'(1,k)` to match `geo_ratios_aux` with s=0
- Fixed monadic coercion issues: added `@List.zipWith ℕ ℕ ℚ` and `@List.map ℚ ℝ` to `divisorRatios`/`h_alpha` definitions to prevent Lean 4 from elaborating ℕ→ℚ and ℚ→ℝ casts as monadic list coercions
- Fixed `prime_ratio_mem`: use `unfold divisorRatios; rw [heq]; dsimp only` to handle let binding inlining
- Fixed `prime_h_alpha_unbounded`: unfold `f` before `linarith` via `have hfp : f ↑p = ... := by simp [f, Rat.cast_natCast]`
- Simplified `power_of_two_h_alpha`: removed monadic normalization steps (no longer needed with `@` definitions)

### Key Findings
- Lean 4's elaboration of `List.zipWith (fun a b => (a : ℚ) / b)` with `List ℕ` args can produce monadic coercion (`do let a ← l; pure ↑a`) instead of keeping the cast inside the lambda — fixed by `@List.zipWith ℕ ℕ ℚ` explicit type annotation
- `pow_succ` (not `pow_succ'`) gives `a^(n+1) = a^n * a` and matches in ℚ context
- `dsimp only` is needed to inline `let` bindings left by `unfold` before `rw` can match patterns
- `set f := ...` makes `f` opaque to `linarith`; need `simp [f, ...]` to unfold first

### Files Modified
- `proofs/Proofs/Erdos1099Problem.lean` (~578→622 lines, -2 sorries, +6 theorems)
- `src/data/proofs/erdos-1099/meta.json` (sorries: 2→0)
- `src/data/research/problems/erdos-1099-oq-01.json` (knowledge updated)

## Session 2026-03-25 (Session 2) - Prove h_alpha_ge_one and prime_h_alpha_unbounded

**Mode**: REVISIT (MODERATE knowledge, score 12)
**Outcome**: progress (5A+1S → 4A+0S)

### What I Did
- Proved `zipWith_div_ge_one`: consecutive ratios in sorted positive lists are ≥ 1 (by list induction)
- Proved `divisorRatios_ge_one`: all divisor ratios are ≥ 1 (corollary)
- Completed `h_alpha_ge_one` proof: used nonneg terms + `List.single_le_sum` to show sum ≥ largest term ≥ 1
- Proved `prime_ratio_mem`: for prime p, the ratio p/1 = p appears in divisorRatios (via `Nat.Prime.eq_one_or_self_of_dvd`)
- Converted `prime_h_alpha_unbounded` from axiom to theorem: for any M, find prime p with p-1 > M, then h_α(p) ≥ (p-1)^α ≥ p-1 > M

### Key Findings
- `le_div_iff` + `Nat.cast_le` handles the ratio ≥ 1 proof cleanly
- `Real.rpow_nonneg` requires `0 ≤ base`; for ratios ≥ 1, `base = ratio - 1 ≥ 0` works
- `Real.rpow_le_rpow_left` gives exponent monotonicity: x^1 ≤ x^α when x ≥ 1, α ≥ 1
- `Nat.exists_infinite_primes` + natural ceiling gives prime p > M+1

### Files Modified
- `proofs/Proofs/Erdos1099Problem.lean` (458→542 lines, +5 theorems, -1 axiom, -1 sorry)
- `src/data/proofs/erdos-1099/meta.json` (updated counts)
- `src/data/research/problems/erdos-1099-oq-01.json` (updated knowledge)

### Next Steps
- Prove `power_of_two_h_alpha` via `Nat.divisors_prime_pow` + sorted list of powers of 2
- Prove `sum_divisor_ratios_lower_bound` via AM-GM + telescoping product (Πrᵢ = n)

## Session 2026-03-25 (Session 3) - Prove vose_liminf_bounded, remove false axiom

**Mode**: REVISIT (RICH knowledge, score 19)
**Outcome**: progress (4A+2S → 1A+2S; 2 axioms eliminated, 1 false axiom removed)

### What I Did
- Proved `vose_liminf_bounded` from `vose_bounded_sequence`: trivial derivation using any element of the bounded sequence
- Discovered `sum_divisor_ratios_lower_bound` is **mathematically false**: Σ(d_{i+1}/dᵢ) > τ(n)+log(n) fails for n=2,3,4,6,12,24. Correct bound is Σ ≥ τ-1+log(n) via x ≥ 1+ln(x) for x≥1
- Found that `power_of_two_h_alpha` was already proved on main branch (2 sorries in helper lemmas)
- Identified pre-existing Mathlib API breakage: le_div_iff₀, List.single_le_sum, Real.rpow_le_rpow_left, Finset.mem_sort

### Key Findings
- `vose_liminf_bounded` follows trivially from `vose_bounded_sequence`: pick seq(0), it satisfies h_alpha ≤ bound < bound+ε
- The false axiom `sum_divisor_ratios_lower_bound` was off by 1 in the τ count (τ-1 ratios, not τ)
- Lean 4.26 / current Mathlib renamed several lemmas affecting existing proofs

### Files Modified
- `proofs/Proofs/Erdos1099Problem.lean` — 1 axiom eliminated (vose_liminf → theorem), 1 false axiom removed
- `src/data/proofs/erdos-1099/meta.json` — Updated axiom/sorry counts

### Next Steps
- Fill 2 remaining sorries in sortedDivisors_two_pow and divisorRatios_two_pow
- Fix pre-existing Mathlib API breakage (le_div_iff, List.single_le_sum, rpow_le_rpow_left)
- Consider proving vose_bounded_sequence (deep Vose construction, likely 500+ lines)
