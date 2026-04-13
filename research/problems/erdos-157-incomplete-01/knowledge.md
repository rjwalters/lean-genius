# Knowledge Base: erdos-157-incomplete-01

Insights accumulated during research on this problem.

---

## Problem Understanding

Erdős #157: Prove that no infinite Sidon set can be an asymptotic basis of order 2.

**State**: `sidon_not_basis_2` in `proofs/Proofs/Erdos157Problem.lean`.
- `pilatte_existence`: BLOCKED (requires formalizing Pilatte 2023 probabilistic method, >1000 lines).
- `sidon_counting_contradiction`: PROVED (session 2026-04-03).
- `sidon_not_basis_2`: Still has sorry — needs `SumsetK_A_2_card_bound` helper.

---

## Session 2026-04-03 (Session 2) — Prove sidon_counting_contradiction

**Mode**: FRESH
**Outcome**: progress — proved sidon_counting_contradiction, removed one sorry

### What I Did
- Identified the correct counting argument: for N = 8*M^4 and large M, the Sidon bound
  M*(M+1)/2 ≈ N contradicts the basis requirement of ~2N representable integers.
- Chose N = 8*M^4 to make √(2N) = 4M² and (2N)^(1/4) = 2M exactly.
- Proved `sidon_counting_contradiction` in `Erdos157Problem.lean:358-443`.

### Key Technical Findings (Lean 4 Cast Elaboration)

**Critical bug**: `↑(8 * M^4)` in `have` type signatures causes `HMul ℕ ℕ ℝ` synthesis failure.
- Root cause: When Lean sees `↑(8 * M^4)` in a context expecting ℝ, it tries to elaborate
  `8 * M^4 : ℝ` directly (identity coercion attempt), leading to `HMul ℕ ℕ ℝ`.
- Fix: Use `((8 * M^4 : ℕ) : ℝ)` explicit notation to force inner type as ℕ before cast.
- The goal after `use 8 * M^4` correctly has `↑(8 * M^4)` (substitution, not fresh elaboration).

**hcast lemma**: `((8*M^4:ℕ):ℝ) = 8*(M:ℝ)^4` via `Nat.cast_mul` + `Nat.cast_pow`. Essential for
subsequent cast-arithmetic. Pattern: `Nat.cast_mul m n : ↑(m*n) = ↑m * ↑n`.

**rw [hcast]; ring pattern**: After `rw [hcast]`, all casts are eliminated and `ring` closes.
- `linear_combination 2 * hcast` FAILED: residual had `8*M^4 * 2 - ↑(8*M^4) * 2 = 0`
  (ring saw LHS as ℕ-valued, RHS as ℝ-cast — different atoms despite definitional equality).
- `push_cast` FAILED: contracts `2 * ↑(8*M^4)` to `↑(16*M^4)` instead of distributing.
- `simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]; ring`: would work but rw [hcast] cleaner.

**rpow_mul approach** for (2N)^(1/4) = 2M:
- `← rpow_natCast` converts `^4` (ℕ power) to `^(4:ℝ)` (rpow)
- `← rpow_mul` collapses `(x^4)^(1/4)` to `x^(4*(1/4))`
- `h4 : ((4:ℕ):ℝ) * (1/4:ℝ) = 1 := by norm_num` then `rw [h4, rpow_one]`

**nlinarith for M≤M² and M³≤M⁴**:
- `nlinarith [hM_pos]` fails for `M ≤ M^2` because ℝ has `M > 0 ≠ M ≥ 1`.
- Fix: need `hM1 : (1:ℝ) ≤ (M:ℝ)` from `exact_mod_cast (show 1 ≤ M by omega)`.
- Then: `nlinarith [mul_nonneg hM_pos.le (show (0:ℝ) ≤ M-1 from by linarith)]`.
- For M³≤M⁴: `nlinarith [mul_lt_mul_of_pos_right h2C2 hM2_pos, mul_le_mul_of_nonneg_right hMle hM2_pos.le]`.

### Files Modified
- `proofs/Proofs/Erdos157Problem.lean` (sidon_counting_contradiction proof, lines 358-443)
- `src/data/research/problems/erdos-157-incomplete-01.json` (knowledge updated)

### Next Steps
1. Prove `SumsetK_A_2_card_bound`: `|SumsetK A 2 ∩ [1,2N]| ≤ M*(M+1)/2`
   - Strategy: use IsSidonAlt injectivity, inject sums into `Option(A × A)` or direct bijection
   - Key: each sum has at most 1 representation a+b with a≤b in a Sidon set
2. Connect SumsetK_A_2_card_bound to sidon_not_basis_2 via sidon_counting_contradiction
3. `pilatte_existence`: flag as BLOCKED — skip for now

---

## Session 2026-04-03 (Session 1) — Survey and Strategy

**Mode**: FRESH
**Outcome**: scouted — correct proof strategy identified, no Lean code written

### Key Findings
- `basis_counting_lower` is NOT sufficient: only gives c > 0, not c > 1.
- Correct approach: direct counting via IsSidonAlt distinctness.
  Injection from [N₀, 2N] into pairs in A — bounded by M*(M+1)/2 where M = |A ∩ [1,2N]|.
- `IsSidonAlt` (proved in file): each sum s has at most 1 pair (a,b), a≤b, a+b=s.
- `sidon_counting_bound` provides C with |A ∩ [1,N]| ≤ √N + C*N^(1/4).
- `sidon_iff_sidon_alt`, `powers_of_two_sidon`, `example_is_sidon`: all proved (0 sorries).

---

## Dead Ends

- `basis_counting_lower` as the main tool: gives c>0 only, consistent with Sidon bound c≤1.
- `linear_combination 2 * hcast`: ring sees `((8*M^4:ℕ):ℝ)` and `↑(8*M^4)` as different atoms.
- `push_cast`: contracts numerals with casts instead of distributing.
- `↑(8*M^4)` notation in `have` type signatures: causes `HMul ℕ ℕ ℝ` elaboration error.
