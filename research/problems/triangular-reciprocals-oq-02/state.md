# Research State: triangular-reciprocals-oq-02

## Current State
**Phase**: ACT (scaffold landed; closures pending)
**Path**: full
**Since**: 2026-06-01 (S4 — researcher-1 ACT SCAFFOLD)
**Iteration**: 4
**Prior**: S3 ORIENT→DECIDE (2026-06-01, researcher-1 — approach lock + signatures)
         S2 OBSERVE→ORIENT (2026-06-01, researcher-1 — problem.md + Mathlib scout)

## Current Focus
S4 scaffolds the Lean files with all proofs as `sorry`. Both files Docker-build
clean on Mathlib v4.26.0:

- `proofs/Proofs/TriangularReciprocalsOQ02.lean` (8 sorries: 4 lemmas, main HasSum
  + tsum corollary, 3 special-case sanity checks for k=1,2,3).
- `proofs/Proofs/TriangularReciprocalsOQ02Aristotle.lean` (3 sorries: companion
  forms of Lemmas 1, 3, 4 exposed to Aristotle).

Lemma 2 (`partial_sum_closed_form`) is intentionally NOT exposed to the companion —
the reindex argument is the substantive content of this proof and is kept in the
main file per gallery convention.

The next pass (S5, ACT) will close Lemmas 1 + 4 (mechanical) plus the three
special-case sanity checks; S6 attacks Lemma 3 (tail bound); S7+ attacks Lemma 2
(the reindex) and the main theorem closure.

## Active Approach
**Approach 1 — Direct partial fractions + harmonic telescoping (LOCKED).**
- Lemma 1 (`partial_fraction`): $\tfrac{1}{n(n+k)} = \tfrac{1}{k}(\tfrac{1}{n} - \tfrac{1}{n+k})$
  for $n, k \ge 1$. **Transfer verbatim** from `TriangularReciprocalGeneralized.lean:133`
  (`field_simp; ring` after `Nat.cast_ne_zero` hypotheses).
- Lemma 2 (`partial_sum_closed_form`): $\sum_{n=1}^{N} \tfrac{1}{n(n+k)} =
  \tfrac{1}{k}\bigl(H_k - (H_{N+k} - H_N)\bigr)$.
  Strategy: split via Lemma 1 → two sums; reindex the second by $m = n+k$ using
  `Finset.sum_Ico_add'` (the same lemma `harmonic_eq_sum_Icc` uses).
- Lemma 3 (`tail_to_zero`): $|H_{N+k} - H_N| \le k/(N+1)$; take limit to get $\to 0$.
- Lemma 4 (`summable_one_div_n_mul_n_add_k`): $0 \le 1/(n(n+k)) \le 1/n^2$ for $n \ge 1$,
  comparison with `Real.summable_one_div_nat_pow.mpr (by norm_num : (1:ℝ) < 2)`.
- Main: `HasSum (fun n : ℕ => 1/((n+1:ℝ)*((n+1)+k))) ((harmonic k : ℝ)/k)`.

Approach 2 (digamma) remains parked. May surface as a one-line corollary using
`Real.deriv_Gamma_nat` after the main result is in place.

## Attempt Count
- Total attempts: 0 (S4 ships scaffolds only; no proof bodies yet)
- Current approach attempts: 0 (closures begin in S5)
- Approaches tried: 0
- Approaches considered & parked: 1 (digamma series)

## Blockers
None.

## Next Action

ACT phase (S5) — close the easy lemmas:

1. **Lemma 1 (`partial_fraction`)**: lift from `TriangularReciprocalGeneralized.lean:133`
   (`field_simp; ring` after `Nat.cast_ne_zero` derived hypotheses). Mirror to the
   Aristotle companion.
2. **Lemma 4 (`summable_one_div_n_mul_n_add_k`)**: `Summable.of_nonneg_of_le` (or
   `Summable.comparison`) against `Real.summable_one_div_nat_pow` at p=2. Bound
   `1/((n+1)((n+1)+k)) ≤ 1/((n+1)^2)` since `(n+1)+k ≥ (n+1)`. Mirror to companion.
3. **Special cases k=1,2,3**: `simp only [harmonic_succ, harmonic_zero]; norm_num`
   should close all three in one tactic each (rational arithmetic).
4. Docker-build, commit, push, refresh PR description.

S6 attacks Lemma 3 (the tail bound `H_{N+k} - H_N ≤ k/(N+1)` + squeeze to 0).
S7+ attacks Lemma 2 (the reindex via `Finset.sum_Ico_add'`).
S8+ assembles the main theorem from Lemmas 2 + 3 + 4 + partial_sum_closed_form.

## S4 Scaffold Artifacts (researcher-1, 2026-06-01)

- `proofs/Proofs/TriangularReciprocalsOQ02.lean` — 125 lines, 8 sorries:
  - `partial_fraction` (line 42)
  - `partial_sum_closed_form` (line 58)
  - `tail_to_zero` (line 72)
  - `summable_one_div_n_mul_n_add_k` (line 85)
  - `generalized_triangular_reciprocals` (line 101, main HasSum)
  - `generalized_triangular_reciprocals_tsum` (line 117, tsum corollary — closed via
    `.tsum_eq` once main lands, but currently uses the main as a sorry)
  - `special_case_k1` / `_k2` / `_k3` (lines 121, 125, 129)
- `proofs/Proofs/TriangularReciprocalsOQ02Aristotle.lean` — 45 lines, 3 sorries:
  - `partial_fraction_aristotle` (line 23)
  - `tail_to_zero_aristotle` (line 32)
  - `summable_one_div_n_mul_n_add_k_aristotle` (line 41)
- Docker build: both files compile clean (Mathlib v4.26.0, 7743/7743 jobs).

## Key Decisions from S3 (researcher-1, 2026-06-01)

- **File name**: `Proofs/TriangularReciprocalsOQ02.lean` (slug-matching, Aristotle-friendly).
  Rejected `TriangularReciprocalsHarmonic.lean` — slug match wins for gallery discovery.
- **Namespace**: `TriangularReciprocalsHarmonic` (descriptive; avoids collision with the
  alternating sibling's `AlternatingTriangularReciprocals.Generalized`).
- **Hypothesis convention**: `(k : ℕ) (hk : 0 < k)` — matches sibling
  `TriangularReciprocalGeneralized.lean` (`generalized_alternating_sum k hk`).
- **Index convention**: prove Lemma 2 with `Finset.Icc 1 N` (matches `harmonic_eq_sum_Icc`),
  then convert to `Finset.range` at the `HasSum` boundary using `hasSum_nat_add_iff 1` to
  drop the $n=0$ term (same trick used at `TriangularReciprocalGeneralized.lean:124`).
- **Casting site**: cast `harmonic` to ℝ at the statement level
  (`(harmonic k : ℝ)`), not inside the proof. The Bounds.lean recipe
  `simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]`
  unfolds the rational into the real Icc-sum cleanly.

## Key Mathlib Anchors (S3-verified, Mathlib v4.26.0)

| Symbol | Source | Use |
|--------|--------|-----|
| `harmonic : ℕ → ℚ` | `NumberTheory/Harmonic/Defs.lean:21` | Definition |
| `harmonic_eq_sum_Icc` | `Defs.lean:37` | Switch to 1-indexed Icc view |
| `Finset.sum_Ico_add'` | `Algebra/BigOperators/Intervals.lean` | Reindex shift $n \mapsto n+k$ |
| `Rat.cast_sum`, `cast_inv`, `cast_natCast` | `Bounds.lean:24,31` | ℚ→ℝ unfold |
| `Real.summable_one_div_nat_pow` | `Analysis/PSeries` | $p=2$ comparison |
| `hasSum_nat_add_iff` | `Topology/Algebra/InfiniteSum/NatInt` | Drop $n=0$ term |
| `Real.deriv_Gamma_nat` | `NumberTheory/Harmonic/GammaDeriv.lean` | Optional digamma corollary |
