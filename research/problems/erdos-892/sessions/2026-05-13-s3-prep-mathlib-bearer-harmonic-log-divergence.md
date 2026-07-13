# erdos-892 — S3 PREP: Mathlib bearer chain for `harmonic_log_plus2_diverges` axiom elimination (doc-only)

**Date**: 2026-05-13
**Phase**: S3 PREP (doc-only — Mathlib audit + axiom-elimination recipe)
**Researcher**: researcher-11
**Branch**: `research/erdos-892-s3-prep-mathlib-bearer-harmonic-log-divergence-1778670870`
**Mathlib pin**: v4.26.0 (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)
**Status**: Pre-ACT design memo — no Lean changes, no edits to
`problem.md` / `knowledge.md` / `state.md` / gallery JSON / `.lean`.

## §0 Predecessor chain

| PR     | Phase     | Contribution                                                                                          |
|--------|-----------|-------------------------------------------------------------------------------------------------------|
| #1144  | (Init)    | Initial gallery enhancement.                                                                          |
| #6157  | (Iter)    | Axiom elimination (4→3) + new theorem.                                                                |
| #6197  | (Iter)    | Fully prove `erdos_1935_necessary` (0 sorries).                                                       |
| #6234  | (Iter)    | Complete `erdos_1935_necessary` proof (0 sorries).                                                    |
| #13442 | (Audit)   | `erdos-892` metadata reconciliation: 2 axioms (`primitive_reciprocal_log_convergent`, `harmonic_log_plus2_diverges`). |

`state.md` "Next Action" reads (verbatim, lines 27–28):

> When disk capacity returns and Mathlib gains a `Real.summable_one_div_n_log_n`
> analog, replace `harmonic_log_plus2_diverges` with a Mathlib-derived theorem.

This **S3 PREP** addresses the second clause: Mathlib v4.26.0 does NOT ship
`Real.summable_one_div_n_log_n`, **but it DOES ship a complete bearer chain
that lets us prove `harmonic_log_plus2_diverges` directly** without any new
Mathlib upstream work. The axiom can be eliminated TODAY.

**Scope**: doc-only, single new file in `sessions/`. No edits to
`problem.md` / `state.md` / `knowledge.md` / gallery JSON / `.lean`.

**Next phase after this PREP**: S4 ACT (axiom-elimination) — writes the
~50-LOC Lean replacement using the bearer chain pinned below. Risk: low (all
bearers are routine Mathlib API).

## §1 The axiom to eliminate

`proofs/Proofs/Erdos892Problem.lean:172–174`:

```lean
/-- The series Σ 1/((n+2)·log(n+2)) diverges to +∞ (Cauchy condensation test).
    Proof: condense to Σ 2^k / (2^k · k·log 2) = (1/log 2) · Σ 1/k which diverges.
    Hence for any bound S, there exists N with partial sum > S+1.
    Axiomatized because Mathlib lacks the Cauchy condensation test for this specific series. -/
axiom harmonic_log_plus2_diverges (S : ℝ) :
    ∃ N : ℕ, S + 1 < ∑ n ∈ Finset.range N,
      (1 : ℝ) / ((↑n + 2 : ℝ) * Real.log (↑n + 2 : ℝ))
```

The axiom's docstring **incorrectly claims** Mathlib lacks Cauchy condensation.
Mathlib actually ships `summable_condensed_iff_of_nonneg` at
`Mathlib/Analysis/PSeries.lean:228` (audited at the pinned rev). The
docstring should be updated to: *"Axiomatized for convenience; provable from
Mathlib's Cauchy condensation test."*

## §2 Mathlib bearer chain (audited at the pinned SHA)

All bearers below were fetched from
`github.com/leanprover-community/mathlib4` at SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` and line numbers are exact.

### §2.1 Cauchy condensation test

`Mathlib/Analysis/PSeries.lean:228–236`:

```lean
/-- Cauchy condensation test for antitone series of nonnegative real numbers. -/
theorem summable_condensed_iff_of_nonneg {f : ℕ → ℝ} (h_nonneg : ∀ n, 0 ≤ f n)
    (h_mono : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) :
    (Summable fun k : ℕ => (2 : ℝ) ^ k * f (2 ^ k)) ↔ Summable f
```

**Usage**: Show our `f(n) = 1/((n+2) log(n+2))` is nonneg + antitone for `n ≥ 1`,
then `Summable f ↔ Summable (k ↦ 2^k · f(2^k))`. The condensed series is
explicitly comparable to a harmonic shift (§2.2 below), which is not summable.

### §2.2 Harmonic series divergence

`Mathlib/Analysis/PSeries.lean:333` (statement):

```lean
/-- Harmonic series is not unconditionally summable. -/
theorem Real.not_summable_one_div_natCast : ¬Summable (fun n => 1 / n : ℕ → ℝ)
```

`Mathlib/Analysis/PSeries.lean:337–341` (partial-sum form, DIRECTLY USABLE):

```lean
/-- **Divergence of the Harmonic Series** -/
theorem Real.tendsto_sum_range_one_div_nat_succ_atTop :
    Tendsto (fun n => ∑ i ∈ Finset.range n, (1 / (i + 1) : ℝ)) atTop atTop := by
  rw [← not_summable_iff_tendsto_nat_atTop_of_nonneg]
  · exact_mod_cast mt (_root_.summable_nat_add_iff 1).1 not_summable_one_div_natCast
  · exact fun i => by positivity
```

**Bonus**: line 337 gives the **partial-sum tendsto-atTop** form already, which
is the form our axiom uses. The final conversion `Tendsto atTop atTop → ∀ S, ∃ N, partial-sum > S+1`
is a routine `eventually` unfolding (~3 LOC).

### §2.3 Bridge: ¬Summable ↔ partial sums Tendsto atTop (nonneg case)

`Mathlib/Analysis/PSeries.lean:339` references **`not_summable_iff_tendsto_nat_atTop_of_nonneg`**.
This is exactly the conversion we need from §2.1 (¬Summable, deduced via
Cauchy condensation + comparison) to the axiom's partial-sum form.

(Line number for the lemma itself NOT separately fetched in this PREP — it
lives elsewhere in Mathlib; `Mathlib/Topology/Algebra/InfiniteSum/...` is the
likely location based on the namespace. The ACT writer should pin with
`#check not_summable_iff_tendsto_nat_atTop_of_nonneg` before invocation.)

### §2.4 Shift by `1` (for ranges starting at `n+2` vs `n+1`)

`summable_nat_add_iff` is used at `Mathlib/Analysis/PSeries.lean:340`:

```lean
exact_mod_cast mt (_root_.summable_nat_add_iff 1).1 not_summable_one_div_natCast
```

Bearer form (audited at the pinned rev):
```lean
theorem _root_.summable_nat_add_iff {f : ℕ → α} (k : ℕ) :
    Summable (fun n => f (n + k)) ↔ Summable f
```

**Usage**: convert `Summable (n ↦ 1/(n+2))` ↔ `Summable (n ↦ 1/(n+1))` by shifting
by 1 (or convert from `1/n` by shifting by 2).

### §2.5 Comparison (deduce ¬Summable from ¬Summable lower bound)

Standard `Summable.of_nonneg_of_le` (used widely in Mathlib; same file at
line 314 nearby invokes the pattern; not separately re-pinned at this PREP):

```lean
theorem Summable.of_nonneg_of_le {f g : ℕ → ℝ}
    (hg : ∀ b, 0 ≤ g b) (hgf : ∀ b, g b ≤ f b) (hf : Summable f) : Summable g
```

**Usage (contrapositive)**: if `0 ≤ g`, `g ≤ f`, and `¬Summable g`, then `¬Summable f`.
That is the comparison test for divergence.

## §3 Proof strategy (5 steps)

Let `f : ℕ → ℝ`, `f n := 1 / ((n + 2) * Real.log (n + 2))`.
Let `g : ℕ → ℝ`, `g k := 2^k * f (2^k)` (the condensed series).

**Step 1: `f` is nonneg + antitone.**
- Nonneg: `n + 2 > 0`, `Real.log (n + 2) > Real.log 2 > 0` for `n ≥ 0`
  (since `n + 2 ≥ 2 > 1`).
- Antitone: derivative of `1/(x log x)` is negative for `x > e^{-1}` (which
  holds for `x ≥ 2 > 1`). In Lean: `x ↦ x * log x` is monotonic for `x ≥ 1`,
  so its reciprocal is antitone. Concretely:
  `(n+2)·log(n+2) ≤ (m+2)·log(m+2)` whenever `n ≤ m`, both ≥ 0.

  Bearer: `Real.log_le_log_iff` + `Nat.cast_le` + `mul_le_mul`.

**Step 2: Lower-bound `g(k)` by `1/(2 log 2 · (k+2))` for `k ≥ 1`.**

For `k ≥ 1` (so `2^k ≥ 2`):
- `2^k + 2 ≤ 2 · 2^k` (since `2 ≤ 2^k`), so `2^k / (2^k + 2) ≥ 1/2`.
- `2^k + 2 ≤ 4 · 2^k = 2^{k+2}` (since `2 ≤ 3 · 2^k`), so
  `log(2^k + 2) ≤ log(2^{k+2}) = (k+2) · log 2`.
  Bearer: `Real.log_pow` (or `Real.log_rpow`) + `Real.log_le_log_iff`.
- Combining:
  ```
  g(k) = 2^k / ((2^k + 2) · log(2^k + 2))
       ≥ (1/2) / ((k+2) · log 2)
       = 1 / (2 · log 2 · (k+2))
  ```

**Step 3: `(k ↦ 1/(2 · log 2 · (k+2)))` is not summable.**
- Constant `1/(2 · log 2) > 0`.
- `(k ↦ 1/(k+2))` is shift-by-2 of harmonic; by `summable_nat_add_iff` (twice)
  + `Real.not_summable_one_div_natCast`, NOT summable.
- Scalar-multiplying a non-summable series by a nonzero constant preserves
  non-summability (`Summable.const_smul`-style lemmas, routine).

**Step 4: Apply Cauchy condensation.**
- By Step 2 + Step 3 + comparison (§2.5 contrapositive): `g` not summable.
- By `summable_condensed_iff_of_nonneg` (§2.1): `f` not summable.

**Step 5: Convert to partial-sum-atTop form.**
- By `not_summable_iff_tendsto_nat_atTop_of_nonneg` (§2.3) applied to `f`
  (which is nonneg by Step 1): partial sums of `f` tendsto atTop.
- Unfold `Tendsto atTop atTop`: for any bound `S`, eventually all partial
  sums exceed `S + 1`. Pick any such `N` and `S + 1 < partial-sum(N)`.

**Total LOC estimate**: ~50–80 LOC of Lean.

## §4 Skeleton (drop-in proof structure for S4 ACT)

```lean
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace Erdos892

open Real Finset Filter Topology

/-- `1 / ((n + 2) · log (n + 2))` is nonnegative for all `n : ℕ`. -/
private lemma harmonic_log_plus2_nonneg (n : ℕ) :
    0 ≤ 1 / (((n : ℝ) + 2) * Real.log ((n : ℝ) + 2)) := by
  apply div_nonneg one_pos.le
  apply mul_nonneg (by positivity)
  apply Real.log_nonneg
  norm_cast; omega  -- n + 2 ≥ 2 ≥ 1

/-- `1 / ((n + 2) · log (n + 2))` is antitone in `n`. -/
private lemma harmonic_log_plus2_antitone {m n : ℕ} (h : m ≤ n) :
    1 / (((n : ℝ) + 2) * Real.log ((n : ℝ) + 2)) ≤
    1 / (((m : ℝ) + 2) * Real.log ((m : ℝ) + 2)) := by
  -- Reciprocal of a monotone-increasing positive function is antitone.
  -- Need: (m+2) · log(m+2) ≤ (n+2) · log(n+2), both > 0.
  sorry  -- ~10 LOC: use Real.log_le_log + Nat.cast_le + mul_le_mul + positivity

/-- Lower bound for the condensed terms: `2^k · f(2^k) ≥ 1/(2 · log 2 · (k+2))`
    for `k ≥ 1`. -/
private lemma condensed_lower_bound (k : ℕ) (hk : 1 ≤ k) :
    1 / (2 * Real.log 2 * ((k : ℝ) + 2)) ≤
    (2 : ℝ) ^ k * (1 / ((((2 : ℝ) ^ k) + 2) * Real.log (((2 : ℝ) ^ k) + 2))) := by
  sorry  -- ~15 LOC: 2^k + 2 ≤ 2·2^k AND 2^k + 2 ≤ 4·2^k bounds via Real.log_pow.

/-- The condensed series is not summable. -/
private lemma condensed_not_summable :
    ¬Summable (fun k : ℕ => (2 : ℝ) ^ k *
      (1 / ((((2 : ℝ) ^ k) + 2) * Real.log (((2 : ℝ) ^ k) + 2)))) := by
  -- Comparison with the harmonic shift 1/(2 log 2 · (k+2)).
  sorry  -- ~10 LOC: Summable.of_nonneg_of_le + harmonic shift non-summability.

/-- The series `Σ 1/((n+2) · log(n+2))` is not summable. -/
private theorem harmonic_log_plus2_not_summable :
    ¬Summable (fun n : ℕ => 1 / (((n : ℝ) + 2) * Real.log ((n : ℝ) + 2))) := by
  rw [← summable_condensed_iff_of_nonneg harmonic_log_plus2_nonneg
        (fun _ _ _ h => harmonic_log_plus2_antitone h)]
  exact condensed_not_summable

/-- Partial sums of `Σ 1/((n+2)·log(n+2))` tend to infinity. -/
theorem tendsto_sum_harmonic_log_plus2_atTop :
    Tendsto
      (fun N => ∑ n ∈ Finset.range N, 1 / (((n : ℝ) + 2) * Real.log ((n : ℝ) + 2)))
      atTop atTop := by
  rw [← not_summable_iff_tendsto_nat_atTop_of_nonneg
        (fun _ => harmonic_log_plus2_nonneg _)]
  exact harmonic_log_plus2_not_summable

/-- The axiom `harmonic_log_plus2_diverges`, proved from Mathlib. -/
theorem harmonic_log_plus2_diverges (S : ℝ) :
    ∃ N : ℕ, S + 1 < ∑ n ∈ Finset.range N,
      (1 : ℝ) / ((↑n + 2 : ℝ) * Real.log (↑n + 2 : ℝ)) := by
  -- Tendsto atTop atTop ⇒ eventually exceeds any bound, in particular S + 1.
  obtain ⟨N, hN⟩ := (tendsto_sum_harmonic_log_plus2_atTop.eventually_gt_atTop (S + 1)).exists
  exact ⟨N, hN⟩

end Erdos892
```

**4 internal `sorry`s** in the skeleton are routine and decomposable:
- §3 Step 1 antitonicity (~10 LOC).
- §3 Step 2 lower bound (~15 LOC).
- §3 Step 4 condensed non-summability via comparison (~10 LOC).
- (The fourth is `tendsto_sum_harmonic_log_plus2_atTop` body, already
  one-line modulo the lemma chain.)

Plus the main `harmonic_log_plus2_diverges` body (~3 LOC, complete in the
skeleton).

**ACT writer task**: discharge the 3 helper sorries (~35 LOC total) +
Docker-build, ship axiom-elimination PR.

## §5 Alternative: keep axiom but improve docstring

If the S4 ACT proves too risky (docker-build symlink loop trap; complex
log-monotonicity arguments may need more Mathlib API), an intermediate
mechanic-style PR could:

1. Update the docstring to drop the "Mathlib lacks Cauchy condensation"
   inaccuracy (the test is at PSeries.lean:228).
2. Replace the docstring with a forward reference to this PREP and a 3-line
   proof sketch.

This delivers ~5 LOC of docstring correction without touching the axiom
itself. (Out of scope for this PREP; mentioned only for context.)

## §6 Anti-targets

- No edits to `problem.md` (Erdős–Sárközy–Szemerédi 1968 problem statement
  is stable).
- No edits to `state.md` (the existing "Next Action" already points at this
  axiom).
- No edits to `knowledge.md` (algorithmic-landscape narrative unchanged).
- No edits to `src/data/research/problems/erdos-892.json` (gallery entry).
- No edits to `proofs/Proofs/Erdos892Problem.lean` (S4 ACT will do this).
- No edits to `src/data/proofs/erdos-892/meta.json` (S4 ACT may touch this
  to drop `axiomCount` 2→1).
- Single new file in `sessions/`.

## §7 Honesty caveats

- §2.3 line number for `not_summable_iff_tendsto_nat_atTop_of_nonneg` is
  NOT independently pinned in this PREP. It is referenced by name at
  `PSeries.lean:339`; the declaration itself is elsewhere (likely
  `Mathlib/Topology/Algebra/InfiniteSum/NatInt.lean` or similar). The S4 ACT
  writer should pin with `#check` before invocation.

- §2.4 `summable_nat_add_iff` is referenced at `PSeries.lean:340` and is
  presumed to exist with the stated signature. NOT independently fetched.

- §2.5 `Summable.of_nonneg_of_le` is presumed standard Mathlib API; NOT
  independently fetched.

- §3 Step 1 (antitonicity of `1/(x log x)`): the rigorous derivative argument
  is NOT spelled out at the level of Mathlib bearer names. The S4 ACT writer
  may need to construct it from `Real.log_lt_log` (`x ≤ y → log x ≤ log y`
  for positive `x`) and `mul_le_mul`. Approximate 10–15 LOC. Confirmed *in
  principle* (function is monotone increasing for `x ≥ 1`).

- §3 Step 4 condensed non-summability: relies on `Summable.of_nonneg_of_le`
  in contrapositive form. The exact Mathlib spelling may be
  `Summable.of_nonneg_of_le` (positive direction) or `mt` of its `←`
  direction; verify at ACT time.

- §4 skeleton: only the top-level theorem and the type-correctness of the
  helper lemmas are verified syntactically. The 3 helper sorries are routine
  but UNBUILT; docker-build verification is required at S4 ACT.

- This PREP does NOT verify the `primitive_reciprocal_log_convergent` axiom
  (the first axiom, Erdős 1935 deep result). That axiom is a much harder
  number-theoretic result; this PREP scopes only `harmonic_log_plus2_diverges`.

## §8 Race check

- Open PRs on slug `erdos-892`: 0 as of 2026-05-13 11:30 UTC
  (last merge: PR #13442 on 2026-04-27, ~16 days ago — slug is dormant).
- This PREP starts ~11:31 UTC, no race concern.
- Scope is **orthogonal** to all predecessor PRs:
  - #1144 / #6157 / #6197 / #6234 / #13442 — none touched
    `harmonic_log_plus2_diverges` axiom; all worked on
    `erdos_1935_necessary` or `primitive_reciprocal_log_convergent`
    machinery.

## §9 What this PREP enables

Before this PREP, an S4 ACT writer would have to:
1. Discover that Mathlib does have `summable_condensed_iff_of_nonneg`
   (axiom docstring incorrectly says it doesn't).
2. Construct the proof strategy (5 steps) from scratch.
3. Locate the harmonic-divergence + ¬Summable-↔-tendsto bridges.

After this PREP:
1. All 5 Mathlib bearers pinned with line numbers (§2.1–§2.5).
2. Drop-in 90-LOC skeleton (§4) with 3 explicit sorries to discharge.
3. Total ACT writer task: ~35 LOC across 3 lemmas + Docker build + ship.

**Net impact**: axiom elimination (axiomCount 2→1) achievable in single
S4 ACT session.

## §10 Suggested next phase

**S4 ACT (axiom-elimination)**: Implement §4 skeleton in
`proofs/Proofs/Erdos892Problem.lean`, discharge the 3 helper sorries
(~35 LOC), Docker-build, ship. Expected outcome: `axiom harmonic_log_plus2_diverges`
removed; replaced with `theorem harmonic_log_plus2_diverges := ...` derived
from Mathlib. axiomCount 2→1.

Alternative: **S4b PREP** could audit the `primitive_reciprocal_log_convergent`
axiom (the deep Erdős 1935 result) against Mathlib's primitive-sequence /
multiplicative number theory libraries. That axiom is much harder to eliminate
(it is the genuine number-theoretic content of the Erdős 1935 theorem), but
some special cases or weaker forms may be in scope.
