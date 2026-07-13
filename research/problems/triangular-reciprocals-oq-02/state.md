# Research State: triangular-reciprocals-oq-02

## Current State
**Phase**: COMPLETE + GALLERY-PUBLISHED (S9 STATE-SYNC — gallery meta.json created)
**Path**: full
**Since**: 2026-06-10 (S9 — researcher-6 created src/data/proofs/triangular-reciprocals-oq-02/meta.json)
**Iteration**: 9 (S9 STATE-SYNC)
**Prior**: S8 ACT close main `HasSum` (2026-06-01, researcher-1)
         S7 ACT close partial_sum_closed_form (2026-06-01, researcher-1)
         S6 ACT close tail_to_zero (2026-06-01, researcher-1 — main + Aristotle)
         S5 ACT mechanical-close (2026-06-01, researcher-1 — 5/8 + 2/3 sorries)
         S4 ACT SCAFFOLD (2026-06-01, researcher-1 — both files build clean with sorries)
         S3 ORIENT→DECIDE (2026-06-01, researcher-1 — approach lock + signatures)
         S2 OBSERVE→ORIENT (2026-06-01, researcher-1 — problem.md + Mathlib scout)

## Current Focus
S7 closed `partial_sum_closed_form` (Lemma 2) by applying `partial_fraction`
term-wise, splitting via `Finset.sum_sub_distrib`, and reindexing the
`∑ 1/(n+k)` piece via `Finset.sum_Ico_add'` (c := k). The harmonic differences
are identified through `harmonic_eq_sum_Icc` + `Finset.sum_Ico_consecutive`.

S8 closed `generalized_triangular_reciprocals` (the main `HasSum`) via
`hasSum_iff_tendsto_nat_of_nonneg`, identifying the `range N` partial sum with
the `Icc 1 N` form (again `Finset.sum_Ico_add'`), then applying Lemma 2's
closed form and Lemma 3's tail limit through
`(tendsto_const_nhds.sub tail).const_mul (1/k)`.

Result: **main file is 0 sorries / 0 axioms; companion is 0 sorries / 0 axioms.**

| # | Lemma | File / line | Status (S8) |
|---|-------|-------------|-------------|
| 1 | `partial_fraction`                      | main:~42  | **closed (S5)** — `field_simp; ring` lifted verbatim from `TriangularReciprocalGeneralized.lean:133` |
| 2 | `partial_sum_closed_form`               | main:~62  | **closed (S7)** — `partial_fraction` termwise + `Finset.sum_sub_distrib` + `Finset.sum_Ico_add'` reindex + `Finset.sum_Ico_consecutive` decomp |
| 3 | `tail_to_zero`                          | main:~78  | **closed (S6)** — induction on k; succ step uses `tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat k)` and `harmonic_succ` |
| 4 | `summable_one_div_n_mul_n_add_k`        | main:~117 | **closed (S5)** — `Summable.of_nonneg_of_le` against `1/(n+1)^2`, p-series at p=2 + `summable_nat_add_iff 1` shift |
|   | `generalized_triangular_reciprocals`    | main:~225 | **closed (S8)** — `hasSum_iff_tendsto_nat_of_nonneg` + `range→Icc` reindex + Lemma 2 + Lemma 3 + `const_mul` |
|   | `special_case_k1` / `_k2` / `_k3`       | main:~250+| **closed (S5)** — unfold `harmonic_succ` then `push_cast; norm_num` |

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
- Total attempts: 4 (S5 mechanical; S6 tail-limit; S7 Lemma 2; S8 main `HasSum`)
- Current approach attempts: 4
- Approaches tried: 1
- Approaches considered & parked: 1 (digamma series)

## Blockers
None — problem fully closed.

## Next Action

**Problem complete and gallery-published.** S9 STATE-SYNC (2026-06-10,
researcher-6) created `src/data/proofs/triangular-reciprocals-oq-02/meta.json`
with `status: "verified"`, `badge: "original"`, 0 sorries / 0 axioms, and
6 sections matching the file structure. Counts: main 318 lines / 9 theorems,
companion 97 lines / 3 theorems, Mathlib v4.26.0.

Future work: Consider Mathlib upstream contribution after the deprecation
warnings for `Nat.Ico_succ_right` are addressed (replacement
`Finset.Ico_succ_right_eq_Icc` not yet available in v4.26.0; will land in a
future Mathlib bump). The digamma reformulation (ψ(k+1) + γ)/k via
`Real.deriv_Gamma_nat` is the natural follow-up corollary.

## S9 Build Artifact (researcher-6, 2026-06-10)

- `src/data/proofs/triangular-reciprocals-oq-02/meta.json` — new gallery
  entry, status `verified`, badge `original`, 5 crossReferences (to
  `triangular-reciprocals`, `-oq-03`, `-oq-01`, `harmonic-divergence`,
  `basel-problem`), 8 mathlibDependencies, 5 originalContributions.
- Docker re-verification of `Proofs.TriangularReciprocalsOQ02` +
  `Proofs.TriangularReciprocalsOQ02Aristotle` against current Mathlib v4.26.0
  toolchain (confirms S8 result still holds).

## S4–S8 Build Artifacts (researcher-1, 2026-06-01)

- `proofs/Proofs/TriangularReciprocalsOQ02.lean` — 287 lines, 8 sorries (S4) → 3 (S5) → 2 (S6) → 1 (S7) → 0 (S8).
- `proofs/Proofs/TriangularReciprocalsOQ02Aristotle.lean` — 97 lines, 3 sorries (S4) → 1 (S5) → 0 (S6).
- Docker build (Mathlib v4.26.0, 7743/7743 jobs):
  * Main file S6: ✓ (only Lemma 2 + main HasSum sorries remain)
  * Companion S6: ✓ (sorry-free)
  * Main file S8: ✓ (sorry-free, 0 axioms; deprecation warnings only — see Mathlib API notes)

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
