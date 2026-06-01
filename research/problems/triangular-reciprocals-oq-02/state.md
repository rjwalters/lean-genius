# Research State: triangular-reciprocals-oq-02

## Current State
**Phase**: ACT (S6 tail-limit close shipped — companion fully closed)
**Path**: full
**Since**: 2026-06-01 (S6 — researcher-1 ACT close tail_to_zero + Aristotle mirror)
**Iteration**: 6
**Prior**: S5 ACT mechanical-close (2026-06-01, researcher-1 — 5/8 + 2/3 sorries)
         S4 ACT SCAFFOLD (2026-06-01, researcher-1 — both files build clean with sorries)
         S3 ORIENT→DECIDE (2026-06-01, researcher-1 — approach lock + signatures)
         S2 OBSERVE→ORIENT (2026-06-01, researcher-1 — problem.md + Mathlib scout)

## Current Focus
S6 closed `tail_to_zero` (Lemma 3) and its Aristotle mirror via induction on `k`
plus `tendsto_one_div_add_atTop_nhds_zero_nat ∘ tendsto_add_atTop_nat k`. The
Aristotle companion is now sorry-free; the main file is down to two sorries
(Lemma 2 reindex + main `HasSum` assembly).

| # | Lemma | File / line | Status (S6) |
|---|-------|-------------|-------------|
| 1 | `partial_fraction`                      | main:~42  | **closed (S5)** — `field_simp; ring` lifted verbatim from `TriangularReciprocalGeneralized.lean:133` |
| 2 | `partial_sum_closed_form`               | main:~62  | sorry (S7+) — reindex via `Finset.sum_Ico_add'` |
| 3 | `tail_to_zero`                          | main:~78  | **closed (S6)** — induction on k; succ step uses `tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat k)` and `harmonic_succ` |
| 4 | `summable_one_div_n_mul_n_add_k`        | main:~117 | **closed (S5)** — `Summable.of_nonneg_of_le` against `1/(n+1)^2`, p-series at p=2 + `summable_nat_add_iff 1` shift |
|   | `generalized_triangular_reciprocals`    | main:~153 | sorry (S7) — combine 2+3+4 to lift partial sums to `HasSum` |
|   | `special_case_k1` / `_k2` / `_k3`       | main:~169+| **closed (S5)** — unfold `harmonic_succ` then `push_cast; norm_num` |

Aristotle companion (`TriangularReciprocalsOQ02Aristotle.lean`) — **fully sorry-free**:
- `partial_fraction_aristotle`              — **closed (S5)**
- `tail_to_zero_aristotle`                  — **closed (S6)** (mirror of main S6 proof)
- `summable_one_div_n_mul_n_add_k_aristotle` — **closed (S5)**

## Mathlib v4.26.0 API notes (S5–S6 sessions)

- `div_le_div_iff` → `div_le_div_iff₀` (rename in v4.26).
- `Nat.cast_nonneg` named arg is `α`, not `R` (regression of an older R-convention).
- S6 gotcha: `.comp` dot notation on `tendsto_one_div_add_atTop_nhds_zero_nat`
  triggered `ContinuousSMul ℚ≥0 ?m` typeclass instability. Workaround: bind the
  RHS to a typed `have h_base : Tendsto _ atTop (𝓝 (0 : ℝ))` first, then
  `h_base.comp h_shift`.
- S6 gotcha: `Tendsto.add` of two `(𝓝 0)` limits produces `(𝓝 (0 + 0))`, not
  `(𝓝 0)` — close with `simpa using ih.add h_term` (or `(by simp : (0+0:ℝ)=0) ▸`).

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
- Total attempts: 2 (S5 mechanical pass; S6 tail-limit close — both succeeded on Docker)
- Current approach attempts: 2
- Approaches tried: 1
- Approaches considered & parked: 1 (digamma series)

## Blockers
None. The remaining two sorries (Lemma 2 reindex, main `HasSum`) are mathematical,
not API-blocked.

## Next Action

**S7** — close `partial_sum_closed_form` (Lemma 2).

Strategy: apply `partial_fraction` term-wise to split `∑ n ∈ Icc 1 N, 1/(n(n+k))`
into `(1/k) * (∑ 1/n − ∑ 1/(n+k))`. The first sum is `harmonic N` via
`harmonic_eq_sum_Icc`. For the second, reindex via `Finset.sum_Ico_add'`
(treating `Icc 1 N = Ico 1 (N+1)`): substitution `m = n + k` gives
`∑ m ∈ Icc (1+k) (N+k), 1/m = harmonic (N+k) − harmonic k`
(via `Finset.sum_Ico_consecutive` splitting `Icc 1 (N+k)` at `k`). Combine to
`(1/k) * (H_k - (H_{N+k} - H_N))`.

**S8** — close the main `generalized_triangular_reciprocals` (`HasSum`).

Strategy: use `HasSum.tendsto_sum_nat`-style conversion. Show
`Tendsto (partial sum over Icc 1 N) atTop (𝓝 (H_k / k))` via Lemma 2 + Lemma 3,
then convert to `HasSum (fun n : ℕ => 1/((n+1)((n+1)+k))) (H_k/k)` via
`hasSum_iff_tendsto_nat_of_summable_norm` or the
`(hasSum_nat_add_iff 1)` trick used at `TriangularReciprocalGeneralized.lean:124`.
The summability witness is `summable_one_div_n_mul_n_add_k` (Lemma 4).

## S4–S6 Build Artifacts (researcher-1, 2026-06-01)

- `proofs/Proofs/TriangularReciprocalsOQ02.lean` — 197 lines, 8 sorries (S4) → 3 (S5) → 2 (S6).
- `proofs/Proofs/TriangularReciprocalsOQ02Aristotle.lean` — 78 lines, 3 sorries (S4) → 1 (S5) → 0 (S6).
- Docker build (Mathlib v4.26.0, 7743/7743 jobs):
  * Main file S6: ✓ (only Lemma 2 + main HasSum sorries remain)
  * Companion S6: ✓ (sorry-free)

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
