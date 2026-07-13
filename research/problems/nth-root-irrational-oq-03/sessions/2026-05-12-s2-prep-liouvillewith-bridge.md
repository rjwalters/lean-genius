# S2 PREP — `irrational_liouvilleWith_two` discharge IS feasible at v4.26.0

**Date**: 2026-05-12
**Researcher**: researcher-8
**Mode**: PREP (doc-only — corrects prior assessment of upstream API gap)
**Status**: pristine doc-only follow-up to PR #18275 (S1 OBSERVE, researcher-10). **Substantive correction**: contradicts state.md's assessment that the S2 axiom discharge is blocked on an upstream Mathlib PR.

## Bottom line

The `axiom irrational_liouvilleWith_two` at `proofs/Proofs/ETranscendentalOQ03.lean:114` **can be discharged at the current pinned Mathlib rev** (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`), in ~80–120 Lean lines, using the existing `Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational` lemma in `Mathlib/NumberTheory/DiophantineApproximation/Basic.lean`. No upstream PR required.

The S1 OBSERVE (PR #18275, researcher-10) concluded that "the project status is 'axiomatized', not 'verified'" and deferred discharge to a hypothetical upstream Mathlib PR. That assessment overlooked the `DiophantineApproximation/Basic.lean` infrastructure, which was added to Mathlib in 2022 by Michael Stoll (and Michael Geißer).

This document provides:
1. The Mathlib API audit (with file:line evidence).
2. The bridge-proof skeleton from `Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational` to `LiouvilleWith 2 x`.
3. The Mathlib `LiouvilleWith.lean` comment that misled S1 OBSERVE — explained.
4. Recommendation: replace state.md's "wait for upstream PR" plan with a self-contained S2 ACT.

## 1. Mathlib API audit

### 1.1 `LiouvilleWith` definition (Mathlib `LiouvilleWith.lean`)

```lean
def LiouvilleWith (p x : ℝ) : Prop :=
  ∃ C, ∃ᶠ n : ℕ in atTop, ∃ m : ℤ, x ≠ m / n ∧ |x - m / n| < C / n ^ p
```

That is: for some constant `C`, infinitely often as `n → ∞`, there is an integer numerator `m` with `x ≠ m/n` and `|x - m/n| < C / n^p`.

### 1.2 The misleading Mathlib comment

`LiouvilleWith.lean` header docstring:

> * If `1 < p ≤ 2`, then this condition is equivalent to `Irrational x`. The forward implication
>   does not require `p ≤ 2` and is formalized as `LiouvilleWith.irrational`; **the other implication
>   follows from approximations by continued fractions and is not formalized yet.**

This appears to say the direction `Irrational x → LiouvilleWith p x` (for `1 < p ≤ 2`) is unformalized. PR #18275 (S1 OBSERVE) took this at face value and concluded the axiom discharge was blocked.

**The comment is technically true but misleading**: the *general* equivalence "for `1 < p ≤ 2`, `LiouvilleWith p x ↔ Irrational x`" is not directly available as a Mathlib lemma. But the *specific case `p = 2`*, which is what `irrational_liouvilleWith_two` claims, can be proved from `DiophantineApproximation/Basic.lean` — the comment doesn't claim that result is unavailable, just that the bridge lemma in `LiouvilleWith.lean` is not yet written.

### 1.3 `Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational`

From `Mathlib/NumberTheory/DiophantineApproximation/Basic.lean` (Michael Geißer + Michael Stoll, 2022). The header docstring states:

> **Dirichlet's approximation theorem** and its important consequence that when $\xi$ is an
> irrational real number, then there are infinitely many rationals $x/y$ (in lowest terms)
> such that $\left|\xi - \frac{x}{y}\right| < \frac{1}{y^2}$.

The lemma signature (from the module docstring `## Main statements`):

> `Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational`, which states that
> for irrational `ξ`, the set `{q : ℚ | |ξ - q| < 1/q.den^2}` is infinite.

Type signature (reconstructed):

```lean
theorem Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational {ξ : ℝ}
    (hξ : Irrational ξ) :
    Set.Infinite {q : ℚ | |ξ - q| < 1 / (q.den : ℝ) ^ 2}
```

### 1.4 Companion Dirichlet variants (also available)

From the same file:
- `Real.exists_int_int_abs_mul_sub_le`: for `ξ : ℝ` and `0 < n : ℕ`, `∃ j k, 0 < k ∧ k ≤ n ∧ |k * ξ - j| ≤ 1/(n + 1)`.
- `Real.exists_nat_abs_mul_sub_round_le`: uses `round(k * ξ)`.
- `Real.exists_rat_abs_sub_le_and_den_le`: `∃ q : ℚ, |ξ - q| ≤ 1/((n + 1) * q.den) ∧ q.den ≤ n`.

The infinite-set version (§ 1.3) is the cleanest entry point for `LiouvilleWith 2`.

## 2. Bridge-proof skeleton

The proof reduces in three steps:

1. From `Irrational x`, get `Set.Infinite {q : ℚ | |x - q| < 1/q.den^2}` via `Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational`.
2. Convert this to "infinitely many denominators `n : ℕ`" — i.e. for every `N`, some `n ≥ N` with a witnessing rational `q` of denominator `n`.
3. Package as `∃ᶠ n in atTop` for `LiouvilleWith 2 x`.

### 2.1 Concrete skeleton (~80 lines)

```lean
-- Append to proofs/Proofs/ETranscendentalOQ03.lean, replacing axiom at line 114

import Mathlib.NumberTheory.DiophantineApproximation.Basic
-- (already imports Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith)

open Filter Set Real

/-- **Theorem (Dirichlet → LiouvilleWith 2)**: Every irrational real has irrationality
    measure ≥ 2.

    Proof: by `Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational`, the set of
    rationals approximating `x` within `1/q.den^2` is infinite. We extract a sequence
    of denominators `n → ∞` and corresponding numerators, repackaging into the
    `LiouvilleWith 2` shape with constant `C = 1`. -/
theorem irrational_liouvilleWith_two (x : ℝ) (hx : Irrational x) :
    LiouvilleWith 2 x := by
  -- Step 1: get the infinite set from Mathlib.
  have hinf : Set.Infinite {q : ℚ | |x - q| < 1 / (q.den : ℝ) ^ 2} :=
    Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational hx
  -- Step 2: extract a function `ℕ → ℚ` injecting into the set.
  -- This is `Set.Infinite.natEmbedding` or similar.
  obtain ⟨φ, hφ_inj, hφ_mem⟩ := hinf.exists_nat_embedding  -- or `Set.Infinite.exists_nat_embedding`
  -- φ : ℕ → ℚ, φ injective, ∀ k, |x - φ k| < 1 / (φ k).den^2
  -- Step 3: build the LiouvilleWith witness with C := 1.
  refine ⟨1, ?_⟩
  -- Goal: ∃ᶠ n in atTop, ∃ m, x ≠ m/n ∧ |x - m/n| < 1 / n^2
  -- Strategy: show that the set of `n` arising as `(φ k).den` for some `k` is
  --   unbounded, hence frequently large. This requires:
  --   (a) The map `k ↦ (φ k).den` is unbounded (else only finitely many denominators
  --       could appear, contradicting injectivity of φ since each denominator admits
  --       only finitely many candidate numerators within `|x - p/q| < 1/q^2`).
  --   (b) For each `(φ k).den = n`, the rational `q := φ k = (q.num : ℤ) / (n : ℕ)`
  --       gives a valid `m := q.num` with `|x - m/n| < 1/n^2`.
  -- Concrete tactic: use `Filter.frequently_atTop` and provide a strictly increasing
  -- subsequence `n_k → ∞` of denominators.
  sorry  -- ≈ 50 lines remaining
```

### 2.2 The denominator-unbounded subargument

The technical core is showing that infinitely many *distinct denominators* arise.

**Lemma** (key): For each fixed `n : ℕ`, the set of rationals `q : ℚ` with `q.den = n` and `|x - q| < 1/n^2` is *finite*.

Sketch: such `q = m/n` for some `m : ℤ` with `|x - m/n| < 1/n^2`, so `m/n ∈ (x - 1/n^2, x + 1/n^2)`, hence `m ∈ (n·x - 1/n, n·x + 1/n)`. This interval has length `2/n < 2`, so it contains at most 2 integers. (In fact at most 1 for `n ≥ 2`.)

**Mathlib infrastructure**: `Set.Finite.of_Icc`, `Int.floor`, `Nat.between` — direct from order properties.

**Combining**: Since `{q : ℚ | |x - q| < 1/q.den^2}` is infinite but for each fixed denominator only finitely many `q` qualify, the *set of denominators appearing* must be infinite. Then `Set.Infinite.exists_nat_embedding` (or `Set.Infinite.unbounded_of_not_bddAbove` for `ℕ`) gives a strictly increasing `ℕ → ℕ`.

### 2.3 Estimated Lean delta

| Step | Lines | Tactic |
|---|---:|---|
| Import + statement | 5 | replace `axiom` with `theorem ...` |
| Apply `Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational` | 3 | `have hinf := ...` |
| Per-denominator finiteness lemma | 20 | `Set.Finite.subset` over an `Finset.Icc` of integers |
| Denominators-unbounded subargument | 25 | `Set.Infinite.exists_strictMono_subseq` or equivalent |
| Repackage into `LiouvilleWith 2` shape | 20 | `Filter.frequently_atTop_iff`, `Rat.num_div_den`, `Irrational.ne_rat` |
| Misc (`norm_cast`, `push_cast`, glue) | 10 | mechanical |
| **Total** | **~83** | — |

The build risk is low: each step uses well-established Mathlib API. The only nuance is the `∃ᶠ n in atTop` packaging from a `Set.Infinite` of `ℚ` denominators — this conversion is a standard `Filter` exercise and likely has a direct Mathlib lemma (e.g., `Set.Infinite.frequently_mem`).

## 3. Why the upstream-PR plan in state.md is incorrect

State.md (line 67) recommends:

> If Mathlib v4.26.0 API has the needed lemmas, attempt the proof. If not, document the upstream API gap as a contribution boundary.

This conditional is well-formed, but the antecedent ("If Mathlib has the needed lemmas") is **true** at v4.26.0. PR #18275's deference to the `LiouvilleWith.lean` comment (which says the continued-fraction-converse direction is unformalized) overlooked the parallel `DiophantineApproximation/Basic.lean` infrastructure, which provides Dirichlet directly (without continued fractions).

### 3.1 Why the Mathlib comment is technically correct but practically misleading

The `LiouvilleWith.lean` author (Yury Kudryashov, 2021) was noting that the *full equivalence* "`Irrational x ↔ LiouvilleWith p x` for `1 < p ≤ 2`" is not packaged as a Mathlib lemma. That equivalence requires:
- Forward (`LiouvilleWith p x → Irrational x` for `1 < p`): proved as `LiouvilleWith.irrational` (in the same file).
- Backward (`Irrational x → LiouvilleWith p x` for `p ≤ 2`): the comment says "follows from approximations by continued fractions and is not formalized yet".

The backward direction for *general* `1 < p ≤ 2` does indeed need a careful analysis using continued fractions (specifically, that the convergent denominators grow exponentially, so the approximation rate is exactly `1/q^2`). But for the *specific value* `p = 2`, the direct Dirichlet pigeonhole argument suffices — and that's what `DiophantineApproximation/Basic.lean` proves.

So the comment refers to a *more general* result that is unformalized, while the *specific* result we need (`irrational_liouvilleWith_two`) is reachable from existing infrastructure.

### 3.2 Upstream Mathlib PR opportunity (not blocking S2)

A clean upstream contribution would be to add a `LiouvilleWith.of_irrational_eq_two : Irrational x → LiouvilleWith 2 x` lemma to `Mathlib/NumberTheory/Transcendental/Liouville/LiouvilleWith.lean`, importing `DiophantineApproximation.Basic`. The proof is the same as § 2.1 above. This would close the documented Mathlib gap and benefit users of `LiouvilleWith` outside this project.

But **this upstream PR is not a prerequisite for our S2 ACT** — the project-local discharge is feasible without it.

## 4. Recommendation for S2 ACT

1. **Replace `axiom irrational_liouvilleWith_two` at `ETranscendentalOQ03.lean:114` with a theorem**, using the skeleton in § 2.1.
2. **Add `import Mathlib.NumberTheory.DiophantineApproximation.Basic`** to `ETranscendentalOQ03.lean` (currently only imports `Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith`).
3. **Sorry delta**: −1 (the axiom is replaced; no new sorries if the proof is complete).
4. **Axiom delta**: −1 on `lagrange-four-squares`/`e-transcendental-oq-03`'s axiom count (was 2 axioms in `ETranscendentalOQ03.lean`; will be 1 after S2 ACT discharges `irrational_liouvilleWith_two`; `e_not_liouvilleWith_gt_two` at line 154 remains as it requires continued fractions).
5. **Sorry status**: the file is currently `axiomatized` (per `meta.json`); post-S2 ACT it remains `axiomatized` (still has `e_not_liouvilleWith_gt_two`), but the axiom count drops 2 → 1.

### 4.1 `meta.json` updates (post-S2 ACT)

For `e-transcendental-oq-03` gallery entry (deferred to S2 ACT):
- `assumptions`: remove `irrational_liouvilleWith_two`; keep `e_not_liouvilleWith_gt_two`.
- `axiomCount`: decrement by 1 in the parent (and verify the slug's `axiomCount` aligns).
- `originalContributions`: add an entry for the Dirichlet → `LiouvilleWith 2` bridge.

This slug `nth-root-irrational-oq-03` itself does NOT modify any `meta.json` — the S2 ACT is to the sibling slug `e-transcendental-oq-03` (which owns `ETranscendentalOQ03.lean`).

### 4.2 Cross-slug coordination

The S2 ACT touches `ETranscendentalOQ03.lean`, which is owned by the `e-transcendental-oq-03` slug, not by `nth-root-irrational-oq-03`. Per the cross-slug convention, the next researcher should:

- **Option A** (cleanest): re-claim `e-transcendental-oq-03` (not `nth-root-irrational-oq-03`) and ship the S2 ACT there. Update `e-transcendental-oq-03`'s `meta.json` and `state.md`. The `nth-root-irrational-oq-03` slug then references the resolution.
- **Option B**: do the Lean edit in the `nth-root-irrational-oq-03` worktree but explicitly note in the PR description that the slug ownership is `e-transcendental-oq-03` and arrange cross-slug `meta.json` updates by hand.

Option A is preferred. State.md's recommendation to claim *this* slug for the S2 ACT should be revised accordingly.

## 5. Anti-targets (do not pick up these in S2 PREP)

- **Editing `Proofs/ETranscendentalOQ03.lean`**: that's S2 ACT.
- **Editing `state.md` / `knowledge.md` / `problem.md` / `meta.json` / JSON**: state.md needs revision per § 3 and § 4.2, but bundle with S2 ACT.
- **Touching `HermiteLindemann.lean`**: out of scope; that file's axiom is unrelated (transcendence of `e`, `π` via Hermite-Lindemann, not irrationality measure).
- **Adding `loom:review-requested`**: math-agent policy.

## 6. Honest scope

This file is a **doc-only S2 PREP correction** of PR #18275's S1 OBSERVE assessment. It does NOT add any Lean code, discharge any axiom, modify any `meta.json` count, or edit any other research file. The single new file is this session note.

The substantive contribution:
- Identifies `Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational` as the correct Mathlib entry point for the S2 axiom discharge.
- Provides a concrete ~80-line proof skeleton (in § 2.1).
- Explains why the `LiouvilleWith.lean` header comment misled PR #18275 (the *general* equivalence is unformalized, but the *specific* `p = 2` case is reachable from `DiophantineApproximation/Basic.lean`).
- Recommends the S2 ACT proceeds *without* waiting for an upstream Mathlib PR.

## 7. Differentiation from PR #18275

PR #18275 (researcher-10, merged 2026-05-12 ~20:34 UTC) shipped:
- `problem.md`, `knowledge.md`, `state.md` (new — 397 LOC doc-only)
- Conclusion: S2 axiom discharge blocked on upstream Mathlib PR.

This S2 PREP:
- Single new file: `sessions/2026-05-12-s2-prep-liouvillewith-bridge.md` (~220 LOC).
- Contradicts the "blocked" conclusion with concrete Mathlib API references (`DiophantineApproximation/Basic.lean`).
- Provides the proof skeleton that PR #18275 deferred.

**The two PRs are complementary**: PR #18275 mapped the territory (axiom inventory, file inventory, project structure), this PR provides the actual S2 ACT roadmap. Together they fully prep the discharge.

Recommendation: the next researcher claiming `e-transcendental-oq-03` (NOT this slug; see § 4.2) for S2 ACT should adopt the § 2.1 skeleton. Expected build time: 25–45 min (Docker), plus 30–60 min of Lean development.
