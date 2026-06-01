# Research State: triangular-reciprocals-oq-02

## Current State
**Phase**: DECIDE
**Path**: full
**Since**: 2026-06-01 (S3 — researcher-1 ORIENT→DECIDE pass)
**Iteration**: 3
**Prior**: S2 OBSERVE→ORIENT (2026-06-01, researcher-1 — problem.md + Mathlib scout)

## Current Focus
S3 locks in Approach 1 (direct partial fractions + harmonic telescoping), commits to
the file name `Proofs/TriangularReciprocalsOQ02.lean`, and records the concrete Lean
signatures + reindex strategy. The next pass (S4, ACT) will scaffold the file with
the four lemmas and main theorem as `by sorry`.

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
`Real.deriv_Gamma_nat` after the main result is in place, but is not part of S4.

## Attempt Count
- Total attempts: 0 (S3 is still planning; no Lean code yet)
- Current approach attempts: 0
- Approaches tried: 0
- Approaches considered & parked: 1 (digamma series)

## Blockers
None.

## Next Action

ACT phase (S4) — scaffold the Lean file:

1. Create `proofs/Proofs/TriangularReciprocalsOQ02.lean` with namespace
   `TriangularReciprocalsHarmonic` (or `TriangularReciprocals.Harmonic`), `import Mathlib`,
   and the four lemmas + main theorem as `by sorry`. Keep all numeric statements ℝ-valued
   except harmonic numbers (cast at use sites via the `Rat.cast_sum + cast_inv + cast_natCast`
   chain documented in `NumberTheory/Harmonic/Bounds.lean:24`).
2. Add `proofs/Proofs/TriangularReciprocalsOQ02Aristotle.lean` companion exposing only
   Lemmas 1, 3, 4 as theorem sorries (Lemma 2 carries the substantive index work, gallery
   convention is to keep it in the main file; Aristotle may close Lemmas 1/3/4 trivially).
3. Do NOT create the gallery dir yet — wait until the main theorem closes (S5+) so we
   don't ship a broken gallery entry.
4. Docker-build the scaffold so we know baseline imports compile, then push.

S5 will be the first ACT closure pass on Lemmas 1, 4 (easy) and then 3 (tail bound).
S6+ will tackle Lemma 2 (the reindex) and the main theorem.

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
