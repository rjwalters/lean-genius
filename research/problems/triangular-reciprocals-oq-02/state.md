# Research State: triangular-reciprocals-oq-02

## Current State
**Phase**: ACT (S5 mechanical-closure pass shipped)
**Path**: full
**Since**: 2026-06-01 (S5 — researcher-1 ACT close-mechanical-sorries)
**Iteration**: 5
**Prior**: S4 ACT SCAFFOLD (2026-06-01, researcher-1 — both files build clean with sorries)
         S3 ORIENT→DECIDE (2026-06-01, researcher-1 — approach lock + signatures)
         S2 OBSERVE→ORIENT (2026-06-01, researcher-1 — problem.md + Mathlib scout)

## Current Focus
S5 closed 5 of 8 sorries in `TriangularReciprocalsOQ02.lean` and 2 of 3 in the
Aristotle companion. Both files Docker-build clean on Mathlib v4.26.0 with the
remaining sorries explicitly localised to the substantive math (Lemma 2 reindex,
Lemma 3 tail bound, main `HasSum` assembly).

| # | Lemma | File / line | Status (S5) |
|---|-------|-------------|-------------|
| 1 | `partial_fraction`                      | main:~42  | **closed** — `field_simp; ring` lifted verbatim from `TriangularReciprocalGeneralized.lean:133` |
| 2 | `partial_sum_closed_form`               | main:~62  | sorry (S7+) — reindex via `Finset.sum_Ico_add'` |
| 3 | `tail_to_zero`                          | main:~76  | sorry (S6)  — bound `H_{N+k} − H_N ≤ k/(N+1)` |
| 4 | `summable_one_div_n_mul_n_add_k`        | main:~88  | **closed** — `Summable.of_nonneg_of_le` against `1/(n+1)^2`, p-series at p=2 + `summable_nat_add_iff 1` shift |
|   | `generalized_triangular_reciprocals`    | main:~124 | sorry (S7) — combine 2+3+4 to lift partial sums to `HasSum` |
|   | `special_case_k1` / `_k2` / `_k3`       | main:~140+| **closed** — unfold `harmonic_succ` then `push_cast; norm_num` |

Aristotle companion (`TriangularReciprocalsOQ02Aristotle.lean`):
- `partial_fraction_aristotle`              — **closed** (S5)
- `tail_to_zero_aristotle`                  — sorry (S6)
- `summable_one_div_n_mul_n_add_k_aristotle` — **closed** (S5)

## Mathlib v4.26.0 API notes (S5 session)

- `div_le_div_iff` → `div_le_div_iff₀` (rename in v4.26).
- `Nat.cast_nonneg` named arg is `α`, not `R` (regression of an older R-convention).

## Active Approach
**Approach 1 — Direct partial fractions + harmonic telescoping (LOCKED at S3).**
- Lemma 1 (`partial_fraction`): $\tfrac{1}{n(n+k)} = \tfrac{1}{k}(\tfrac{1}{n} - \tfrac{1}{n+k})$
  for $n, k \ge 1$. **Closed S5** via verbatim lift from `TriangularReciprocalGeneralized.lean:133`.
- Lemma 2 (`partial_sum_closed_form`): $\sum_{n=1}^{N} \tfrac{1}{n(n+k)} =
  \tfrac{1}{k}\bigl(H_k - (H_{N+k} - H_N)\bigr)$. Strategy: split via Lemma 1 → two sums;
  reindex the second by $m = n+k$ using `Finset.sum_Ico_add'` (the same lemma `harmonic_eq_sum_Icc` uses).
- Lemma 3 (`tail_to_zero`): $0 \le H_{N+k} - H_N \le k/(N+1)$; take limit to get $\to 0$.
- Lemma 4 (`summable_one_div_n_mul_n_add_k`): **Closed S5**. We dominate
  $1/((n+1)((n+1)+k)) \le 1/(n+1)^2$ since $(n+1)+k \ge (n+1)$, then use
  `summable_one_div_nat_pow.mpr one_lt_two` shifted by `(summable_nat_add_iff 1).mpr` and
  squeeze via `Summable.of_nonneg_of_le`.
- Main: `HasSum (fun n : ℕ => 1/((n+1:ℝ)*((n+1)+k))) ((harmonic k : ℝ)/k)`.

Approach 2 (digamma) remains parked. May surface as a one-line corollary using
`Real.deriv_Gamma_nat` after the main result is in place.

## Attempt Count
- Total attempts: 1 (S5 close-mechanical-sorries pass — succeeded on Docker)
- Current approach attempts: 1
- Approaches tried: 1
- Approaches considered & parked: 1 (digamma series)

## Blockers
None. The remaining three sorries (Lemma 2, Lemma 3, main `HasSum`) are mathematical,
not API-blocked.

## Next Action

**S6** — close `tail_to_zero` (Lemma 3) and its Aristotle mirror.

Strategy: write `harmonic (N+k) - harmonic N` as `∑ i ∈ Finset.Icc (N+1) (N+k), (1:ℝ)/i`
via `harmonic_eq_sum_Icc` and `Finset.sum_Icc_consecutive` (or `Finset.sum_Ioc_consecutive`).
Bound each term by `1/(N+1)`. Squeeze using `tendsto_const_div_atTop_nhds_zero_nat`
applied to the constant bound `k/(N+1)`.

**S7+** — close `partial_sum_closed_form` (Lemma 2). The reindex via `Finset.sum_Ico_add'`
is the substantive step. Then assemble the main `HasSum` from 2+3+4.

## S4 Scaffold Artifacts (researcher-1, 2026-06-01)

- `proofs/Proofs/TriangularReciprocalsOQ02.lean` — 125 lines, 8 sorries (S4 → 3 sorries S5).
- `proofs/Proofs/TriangularReciprocalsOQ02Aristotle.lean` — 45 lines, 3 sorries (S4 → 1 sorry S5).
- Docker build: both files compile clean (Mathlib v4.26.0, 7743/7743 jobs).

## Key Decisions from S3 (researcher-1, 2026-06-01)

- **File name**: `Proofs/TriangularReciprocalsOQ02.lean` (slug-matching, Aristotle-friendly).
- **Namespace**: `TriangularReciprocalsHarmonic` (descriptive; avoids collision with the
  alternating sibling's `AlternatingTriangularReciprocals.Generalized`).
- **Hypothesis convention**: `(k : ℕ) (hk : 0 < k)` — matches sibling
  `TriangularReciprocalGeneralized.lean` (`generalized_alternating_sum k hk`).
- **Index convention**: prove Lemma 2 with `Finset.Icc 1 N` (matches `harmonic_eq_sum_Icc`),
  then convert to `Finset.range` at the `HasSum` boundary using `hasSum_nat_add_iff 1` to
  drop the $n=0$ term (same trick used at `TriangularReciprocalGeneralized.lean:124`).
- **Casting site**: cast `harmonic` to ℝ at the statement level
  (`(harmonic k : ℝ)`), not inside the proof.

## Key Mathlib Anchors (S3-verified, Mathlib v4.26.0)

| Symbol | Source | Use |
|--------|--------|-----|
| `harmonic : ℕ → ℚ` | `NumberTheory/Harmonic/Defs.lean:21` | Definition |
| `harmonic_eq_sum_Icc` | `Defs.lean:37` | Switch to 1-indexed Icc view |
| `Finset.sum_Ico_add'` | `Algebra/BigOperators/Intervals.lean` | Reindex shift $n \mapsto n+k$ |
| `Rat.cast_sum`, `cast_inv`, `cast_natCast` | `Bounds.lean:24,31` | ℚ→ℝ unfold |
| `summable_one_div_nat_pow` | `Analysis/PSeries` | $p=2$ comparison (S5 used) |
| `summable_nat_add_iff` | `Topology/Algebra/InfiniteSum/NatInt` | Drop $n=0$ term (S5 used to shift index by 1) |
| `Summable.of_nonneg_of_le` | `Topology/Instances/ENNReal` | Comparison test (S5 used) |
| `div_le_div_iff₀` | `Algebra/Order/GroupWithZero/Unbundled/Basic.lean:1364` | Cross-multiply for div bounds (was `div_le_div_iff` in v4.10) |
| `hasSum_nat_add_iff` | `Topology/Algebra/InfiniteSum/NatInt` | Drop $n=0$ term in main proof |
| `Real.deriv_Gamma_nat` | `NumberTheory/Harmonic/GammaDeriv.lean` | Optional digamma corollary |
