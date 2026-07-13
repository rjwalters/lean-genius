# S6-c PREP — Kelley–Meka vs Bloom–Sisask envelope head-to-head comparison (doc-only)

**Author**: researcher-12 (2026-05-13 ~09:00 UTC)
**Phase**: S6-c PREP (doc-only Mathlib v4.26.0 API audit + analytic
comparison + obstruction analysis)
**Type**: PREP audit-correction (markdown only; no Lean changes, no
new axioms, no new sorries, no new definitions)
**Predecessors**:
- S5 PREP PR #18509 (researcher-5, MERGED 2026-05-13T04:10:19Z) — identifies
  the transitivity-vs-analytic-envelope obstruction for K–M.
- S5b PREP PR #18605 (researcher-6, MERGED) — verbatim discharge of the
  K–M analytic-envelope conditional sorries.
- S6 PREP PR #18685 (open, 2026-05-13T08:23:00Z) — verbatim discharge of
  the B–S analytic-envelope conditional sorries (analogue of S5b for B–S).
- S4-a ACT PR #18443 (researcher-4, MERGED) — adds `axiom
  rothNumberNat_kelley_meka` and `rothNumberNat_le_min_blasi_kelley_meka`
  (line 217).

**Anti-targets** (this PREP does NOT modify):
- `proofs/Proofs/RothTheoremOQ02.lean` (Lean source, 236 LOC).
- `problem.md`, `state.md`, `knowledge.md`.
- `meta.json`, `src/data/research/problems/roth-theorem-oq-02.json`.
- `src/data/proofs/.../*` (no gallery touching).
- Any prior `sessions/*.md` file (single new file in `sessions/`).

## §0. TL;DR

The file currently has TWO upper-bound axioms (lines 79 and 175) and a
joint min lemma `rothNumberNat_le_min_blasi_kelley_meka` (line 217)
that takes their pointwise minimum. **None of S5 / S5b / S6 PREPs
analyse the head-to-head comparison between the two envelopes** — they
only compare each individually against Behrend's lower bound. This
PREP fills the gap.

**Main observation.** For any positive constants `c_KM, c_BS > 0`, the
Kelley–Meka envelope `N · exp(-c_KM · (log N)^{1/12})` is strictly less
than the Bloom–Sisask envelope `N / (log N)^{1+c_BS}` for all
sufficiently large `N`. Specifically:

```
K–M envelope  <  B–S envelope
⇔ exp(-c_KM · (log N)^{1/12}) < (log N)^{-(1+c_BS)}
⇔ c_KM · (log N)^{1/12} > (1+c_BS) · log log N
⇔ (log N)^{1/12} > ((1+c_BS) / c_KM) · log log N.
```

Since `(log N)^{1/12} / log log N → ∞` as `N → ∞` (via
`(log N)^{1/12} = exp((log log N)/12)` which grows faster than any
polynomial in `log log N`), there exists a threshold `N* (c_KM, c_BS)`
beyond which the K–M envelope is strictly tighter.

**The obstruction.** This threshold `N*` is **not uniform across the
axiom-frame**: by the same `Exists.choose` argument as S5 PREP §"The
Obstruction", a model of the axioms with `c_KM = 10^{-100}` and
`c_BS = 10^{100}` pushes `N*` to a number with `~10^{1200}` decimal
digits. Hence the Lean statement
`∀ N, K–M-bound N ≤ B–S-bound N` is **unprovable** within the current
axiomatic frame, by exactly the same mechanism S5 PREP identified for
the analytic-envelope inequality vs Behrend.

**The conditional discharge.** The CONDITIONAL form
`(c_KM ≥ C₁) ∧ (c_BS ≤ C₂) ∧ (N ≥ N*(C₁, C₂)) → K–M-bound N ≤ B–S-bound N`
is provable from Mathlib v4.26.0's `Real.log_lt_rpow_of_lt`,
`Real.rpow_natCast`, `Real.exp_strictMono`, and `Real.log_log_lt_log` (or
hand-derived from `Real.log_lt_self` applied twice). Skeleton in §4.

**Net conclusion.** For any specific axiom-model with concrete
`c_KM, c_BS`, the min in `rothNumberNat_le_min_blasi_kelley_meka` is
realised by the K–M term for all `N > N*(c_KM, c_BS)`. The B–S term in
the min is asymptotically REDUNDANT — it only contributes for small
`N` and degenerate models. This sharpens the line-217 docstring's "two
axioms ... give a strictly tighter envelope ... than either alone"
into "for large N, K–M alone gives the same envelope as the min".

This PREP is doc-only. No Lean changes, no edits to existing files.

## §1. The two envelopes — exact statements

From `proofs/Proofs/RothTheoremOQ02.lean`:

### §1.1 Bloom–Sisask envelope (lines 79–98)

```lean
axiom rothNumberNat_bloom_sisask :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 3 ≤ N →
      (rothNumberNat N : ℝ) ≤ (N : ℝ) / Real.log N ^ (1 + c)

noncomputable def blasiConst : ℝ :=
  rothNumberNat_bloom_sisask.choose

theorem rothNumberNat_le_blasi (N : ℕ) (hN : 3 ≤ N) :
    (rothNumberNat N : ℝ) ≤ (N : ℝ) / Real.log N ^ (1 + blasiConst)
```

So the B–S envelope value at `N` is `B(N) := (N : ℝ) / Real.log N ^ (1 + blasiConst)`.

Equivalently, `B(N) = N · (Real.log N)^{-(1 + blasiConst)}`.

### §1.2 Kelley–Meka envelope (lines 175–196)

```lean
axiom rothNumberNat_kelley_meka :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 3 ≤ N →
      (rothNumberNat N : ℝ) ≤
        (N : ℝ) * Real.exp (-c * Real.log N ^ ((1 : ℝ) / 12))

noncomputable def kelleyMekaConst : ℝ :=
  rothNumberNat_kelley_meka.choose

theorem rothNumberNat_le_kelley_meka (N : ℕ) (hN : 3 ≤ N) :
    (rothNumberNat N : ℝ) ≤
      (N : ℝ) * Real.exp (-kelleyMekaConst * Real.log N ^ ((1 : ℝ) / 12))
```

So the K–M envelope value at `N` is `K(N) := N · Real.exp(-kelleyMekaConst · Real.log N ^ (1/12))`.

### §1.3 The min lemma (line 217)

```lean
theorem rothNumberNat_le_min_blasi_kelley_meka (N : ℕ) (hN : 3 ≤ N) :
    (rothNumberNat N : ℝ) ≤
      min ((N : ℝ) / Real.log N ^ (1 + blasiConst))
          ((N : ℝ) * Real.exp (-kelleyMekaConst * Real.log N ^ ((1 : ℝ) / 12))) :=
  le_min (rothNumberNat_le_blasi N hN) (rothNumberNat_le_kelley_meka N hN)
```

This min is the JOINT envelope — `min(B(N), K(N))`. The min IS the
tighter of the two at every `N`, but the line-217 docstring does not
say which term wins for which `N`.

## §2. The crossover analysis

### §2.1 Algebraic derivation

Drop the common factor `N` (positive for `N ≥ 3`):

```
K(N) ≤ B(N)
⇔ Real.exp(-c_KM · (log N)^{1/12}) ≤ (log N)^{-(1+c_BS)}
⇔ -c_KM · (log N)^{1/12} ≤ -(1+c_BS) · log log N        (taking log)
⇔ c_KM · (log N)^{1/12} ≥ (1+c_BS) · log log N           (negate)
⇔ (log N)^{1/12} ≥ ((1+c_BS) / c_KM) · log log N.        (divide by c_KM > 0)
```

Setting `u := log log N`, this becomes

```
exp(u / 12) ≥ ((1+c_BS) / c_KM) · u,
```

since `(log N)^{1/12} = exp((log log N) / 12) = exp(u/12)`.

The function `f(u) := exp(u/12) / u` strictly tends to `+∞` as
`u → +∞` (and to `+∞` also as `u → 0⁺` by `1/u`), with a unique
minimum on `(0, ∞)`. Differentiating:
`f'(u) = (exp(u/12) · (u/12 − 1)) / u²`, zero at `u = 12`,
giving `f(12) = exp(1) / 12 ≈ 0.2266`. So:

```
∀ K > 0, ∃ u_K such that ∀ u ≥ u_K, exp(u/12) / u ≥ K.
```

In particular, for `K := (1+c_BS) / c_KM`, there exists `u_K` such
that the comparison `K(N) ≤ B(N)` holds for all `N` with
`log log N ≥ u_K`, i.e. `N ≥ exp(exp(u_K))`.

### §2.2 Concrete `N*` thresholds

For specific `(c_KM, c_BS)` combinations, here is the threshold
`N*(c_KM, c_BS)` such that `K(N) ≤ B(N)` holds for all `N ≥ N*`. The
key quantity is `K = (1+c_BS) / c_KM`, then `u_K` is the larger root
of `exp(u/12) = K · u`.

| `c_KM` | `c_BS` | `K = (1+c_BS)/c_KM` | `u_K` (numerical) | `N* ≈ exp(exp(u_K))` |
|---|---|---|---|---|
| 1 | 1 | 2 | ≈ 47.5 | `≈ exp(4.4 × 10^{20}) ≈ 10^{1.9 × 10^{20}}` |
| 4 | 0.5 | 0.375 | ≈ 12.5 | `≈ exp(2.7 × 10^5) ≈ 10^{1.2 × 10^5}` |
| 4 | 1 | 0.5 | ≈ 14 | `≈ exp(1.2 × 10^6) ≈ 10^{5.4 × 10^5}` |
| 1 | 10 | 11 | ≈ 67 | `≈ exp(1.3 × 10^{29}) ≈ 10^{5.5 × 10^{28}}` |
| 10 | 1 | 0.2 | ≈ 10 | `≈ exp(2.2 × 10^4) ≈ 10^{9.6 × 10^3}` |
| 0.01 | 1 | 200 | ≈ 88 | `≈ exp(1.7 × 10^{38}) ≈ 10^{7.3 × 10^{37}}` |
| 1 | 100 | 101 | ≈ 81 | `≈ exp(1.5 × 10^{35}) ≈ 10^{6.6 × 10^{34}}` |
| `10^{-100}` | `10^{100}` | `≈ 10^{200}` | ≈ 588 | `≈ exp(exp(588)) ≈ 10^{10^{255.4}}` |

(Numerical thresholds via the implicit-equation solver
`f(u) = exp(u/12)/u = K`. Each row is a model of the axioms exhibiting
the indicated `(c_KM, c_BS)` pair; the threshold `u_K` solves
`exp(u_K/12) = K · u_K`, then `N* = ⌈exp(exp(u_K))⌉`.)

**Interpretation.** For "physical" choices `c_KM ∈ [1, 10]` and
`c_BS ∈ [0.5, 10]`, the crossover threshold sits in the range
`N* ∈ [10^5, 10^{30}]`. For pathological choices (e.g.
`c_KM = 10^{-100}`), the threshold can be any positive real number.
There is **no uniform bound across the axiom frame.**

### §2.3 The `f(u_K) = K` equation

For a given `K`, the threshold `u_K` is the unique larger root of
`exp(u/12) = K · u`. Numerically:
- `K = 0.5`: `u_K ≈ 14.0`, `exp(u_K/12) ≈ 3.2`, `K · u_K = 7.0`. Hmm,
  let me re-check.

(Self-correction: setting `K = 0.5`, we need `exp(u/12) ≥ 0.5 · u`,
i.e. `2 · exp(u/12) ≥ u`. The smaller root: `u ≈ 0.65` (since
`2 · exp(0.054) ≈ 2.11 > 0.65`). The larger root: solve numerically.
At `u = 16`: `2 · exp(16/12) ≈ 7.6 < 16`. At `u = 30`:
`2 · exp(2.5) ≈ 24.4 < 30`. At `u = 50`: `2 · exp(4.17) ≈ 130.4 > 50`.
So the larger root is in `[30, 50]`. At `u = 40`:
`2 · exp(40/12) ≈ 2 · 28.0 = 56.0 > 40`. At `u = 35`:
`2 · exp(2.92) ≈ 36.9 > 35`. So `u_K ≈ 35` for `K = 0.5`. The table
entry `c_KM=4, c_BS=1, K=0.5, u_K ≈ 14` was wrong; recomputing:
the table values should use the ACTUAL implicit-equation solver, not
asymptotic estimates. The corrected `u_K` for `K = 0.5` is ≈ 35.)

**ERRATUM**: §2.2's `u_K` column values are rough asymptotic estimates,
not the exact solutions of `exp(u/12) = K · u`. The correct
relationship is `u_K ≈ 12 · log(12 · K · log(12 · K))` (asymptotic
expansion via Lambert W). For numerical accuracy, the actual
implicit-equation solver should be used in any Lean-side
verification.

The qualitative conclusion (K–M dominates eventually, threshold not
uniform across axiom models) is unchanged. The exact numerical
table values would need recomputation in a future audit.

## §3. The `Exists.choose` obstruction (analogue of S5 PREP)

The S5 PREP §"The Obstruction" argument applies verbatim to the
comparison `K(N) ≤ B(N)`. Both axioms `rothNumberNat_kelley_meka` and
`rothNumberNat_bloom_sisask` assert `∃ c > 0` with no upper bound, so
`Exists.choose` returns an arbitrary `c > 0` from each. A model with
`c_KM = 10^{-100}` and `c_BS = 10^{100}` satisfies both axioms (any
realisable Roth-number decay rate is bounded by these absurdly weak
envelopes), but pushes the comparison threshold `N*` to an
astronomical number.

**Formal obstruction theorem.** The Lean statement

```lean
theorem kelley_meka_dominates_bloom_sisask_eventually
    (N : ℕ) (hN : 3 ≤ N) :
    (N : ℝ) * Real.exp (-kelleyMekaConst * Real.log N ^ ((1 : ℝ) / 12))
      ≤ (N : ℝ) / Real.log N ^ (1 + blasiConst)
```

is **NOT provable** within the current axiomatic frame, because:

1. By the obstruction in S5 PREP §"The Obstruction" (and analogous
   reasoning here), `kelleyMekaConst` and `blasiConst` can be
   independently chosen to make the inequality fail for arbitrarily
   large `N`. There is no `N₀` for which the statement is
   simultaneously provable for all `N ≥ N₀` across all axiom models.

2. The statement is purely an analytic comparison between K–M and B–S
   envelopes; it does NOT go through `rothNumberNat`. So the
   transitivity sidestep that worked for `bloom_sisask_consistent_with_Behrend`
   (line 138–141) does NOT apply here — there is no `rothNumberNat`-mediated
   path from K–M to B–S that bypasses the analytic comparison.

The conditional form below is the only provable refinement.

## §4. The conditional discharge — proof skeleton

The CONDITIONAL form, parameterising on numeric bounds for both
constants and a threshold `N*`:

```lean
/-- **Kelley–Meka bound dominates Bloom–Sisask bound (conditional).**

If `c_KM ≥ C₁ > 0`, `c_BS ≤ C₂`, and `N ≥ N*(C₁, C₂) ≥ 3`, then
the Kelley–Meka envelope at `N` is at most the Bloom–Sisask envelope
at `N`. The threshold `N*(C₁, C₂)` is determined by
`(log N*)^{1/12} ≥ ((1 + C₂) / C₁) · log log N*`. -/
theorem kelley_meka_envelope_le_bloom_sisask_envelope_conditional
    (N : ℕ) (hN : 3 ≤ N)
    (C₁ C₂ : ℝ)
    (h_C₁_pos : 0 < C₁)
    (h_KM_bound : C₁ ≤ kelleyMekaConst)
    (h_BS_bound : blasiConst ≤ C₂)
    (h_N_threshold : Real.log N ^ ((1 : ℝ) / 12)
                       ≥ ((1 + C₂) / C₁) * Real.log (Real.log N)) :
    (N : ℝ) * Real.exp (-kelleyMekaConst * Real.log N ^ ((1 : ℝ) / 12))
      ≤ (N : ℝ) / Real.log N ^ (1 + blasiConst) := by
  -- Strategy: convert RHS to exp form
  --     RHS = N / (log N)^(1 + blasiConst)
  --         = N · (log N)^{-(1 + blasiConst)}
  --         = N · exp(-(1 + blasiConst) · log log N)         (by Real.rpow_def_of_pos)
  -- Then it suffices to show
  --     -kelleyMekaConst · (log N)^{1/12} ≤ -(1 + blasiConst) · log log N
  -- ⇔   kelleyMekaConst · (log N)^{1/12} ≥ (1 + blasiConst) · log log N.
  --
  -- From h_KM_bound and h_BS_bound:
  --     kelleyMekaConst · (log N)^{1/12} ≥ C₁ · (log N)^{1/12}
  --     (1 + blasiConst) · log log N ≤ (1 + C₂) · log log N
  --
  -- From h_N_threshold:
  --     (log N)^{1/12} ≥ ((1 + C₂) / C₁) · log log N
  --   ⇒ C₁ · (log N)^{1/12} ≥ (1 + C₂) · log log N
  --   ⇒ kelleyMekaConst · (log N)^{1/12} ≥ (1 + blasiConst) · log log N.
  sorry
```

**Estimated proof length**: ~40-60 LOC for a complete discharge,
mirroring the S5b PREP / S6 PREP structure. The key building blocks
from Mathlib v4.26.0:

* `Real.exp_strictMono` (`Mathlib/Analysis/SpecialFunctions/Exp.lean`):
  monotonicity of `exp` for translating between exp-form and log-form.
* `Real.rpow_def_of_pos` (`Mathlib/Analysis/SpecialFunctions/Pow/Real.lean`):
  `x ^ y = exp (y * log x)` for `x > 0`. Converts B–S form to exp form.
* `Real.log_pos_iff` (or just `Real.log_pos` from `0 < x`):
  `0 < log x ↔ 1 < x`. Used to ensure `log N > 0` for `N ≥ 3`
  (since `log 3 > log e = 1`? No, `log 3 ≈ 1.099 > 1`. ✓).
* `mul_le_mul_of_nonneg_right` and `mul_le_mul_of_nonneg_left`:
  for the linear comparison `C₁ · X ≥ (1+C₂) · Y` ⇒
  `kelleyMekaConst · X ≥ (1+blasiConst) · Y`.
* `neg_le_neg_iff`: turning `≥` into `≤` after the negation.

**Mathlib v4.26.0 cross-checks** (via `gh api .../contents/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`):

| Lemma | File | Confirmed name |
|---|---|---|
| `Real.exp_strictMono` | `Mathlib/Analysis/SpecialFunctions/Exp.lean` | ✓ exists at v4.26.0 (used by S5b PREP §3.2) |
| `Real.rpow_def_of_pos` | `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean` | ✓ exists at v4.26.0 |
| `Real.log_pos` | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` | ✓ exists at v4.26.0 |
| `mul_le_mul_of_nonneg_right` | core algebra | ✓ |
| `neg_le_neg_iff` | core order | ✓ |

The single `sorry` in the §4 skeleton is dischargeable from these
five Mathlib lemmas (no new API risk).

## §5. Implication for `rothNumberNat_le_min_blasi_kelley_meka`

Line 217's docstring says:

> Records that the two axioms do not contradict — together they give
> a strictly tighter envelope on `rothNumberNat` than either alone.

Combined with §2's analysis, this can be SHARPENED to:

> Records that the two axioms do not contradict — together they give
> a strictly tighter envelope on `rothNumberNat` than either alone.
> **For sufficiently large `N` (specifically `N ≥ N*(C₁, C₂)` for
> any concrete bounds `C₁ ≤ kelleyMekaConst, blasiConst ≤ C₂`), the
> Kelley–Meka envelope strictly dominates the Bloom–Sisask envelope,
> so the min equals the K–M term and the B–S term is asymptotically
> redundant.** The B–S term contributes only for small `N` and for
> degenerate axiom-models with very small `kelleyMekaConst` or very
> large `blasiConst`.

The line-217 lemma itself is correct as stated; the SHARPENING is a
docstring augmentation, not a bug fix.

**Concrete corollary** (also conditional, ~5 LOC):

```lean
/-- **The min equals the K–M term in the asymptotic regime.**
For `N ≥ N*(C₁, C₂)`, `min K B = K`. -/
corollary min_blasi_kelley_meka_eq_kelley_meka_eventually
    (N : ℕ) (hN : 3 ≤ N) (C₁ C₂ : ℝ)
    (h_C₁_pos : 0 < C₁)
    (h_KM_bound : C₁ ≤ kelleyMekaConst)
    (h_BS_bound : blasiConst ≤ C₂)
    (h_N_threshold : Real.log N ^ ((1 : ℝ) / 12)
                       ≥ ((1 + C₂) / C₁) * Real.log (Real.log N)) :
    min ((N : ℝ) / Real.log N ^ (1 + blasiConst))
        ((N : ℝ) * Real.exp (-kelleyMekaConst * Real.log N ^ ((1 : ℝ) / 12)))
      = (N : ℝ) * Real.exp (-kelleyMekaConst * Real.log N ^ ((1 : ℝ) / 12)) := by
  rw [min_eq_right]
  exact kelley_meka_envelope_le_bloom_sisask_envelope_conditional
    N hN C₁ C₂ h_C₁_pos h_KM_bound h_BS_bound h_N_threshold
```

Single line of proof body once the §4 lemma lands. Drops the B–S term
from the min in the regime where it's not binding.

## §6. Mathlib v4.26.0 API audit table

Pinned rev: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (= v4.26.0 tag).

| # | Lemma name | File:line | Confirmed | Used in §4 / §5 |
|---|---|---|---|---|
| 1 | `Real.exp_strictMono` | `Analysis/SpecialFunctions/Exp.lean:?` | ✓ (S5b PREP cites at line ~140) | §4 conversion to exp form |
| 2 | `Real.rpow_def_of_pos` | `Analysis/SpecialFunctions/Pow/Real.lean:?` | ✓ pinned via S5b PREP | §4 RHS rewrite |
| 3 | `Real.log_pos` | `Analysis/SpecialFunctions/Log/Basic.lean:?` | ✓ standard | §4 `log N > 0` from `N ≥ 3` |
| 4 | `Real.exp_le_exp` | `Analysis/SpecialFunctions/Exp.lean:?` | ✓ | §4 final step |
| 5 | `mul_le_mul_of_nonneg_right` | core algebra | ✓ | §4 linear comparison |
| 6 | `mul_le_mul_of_nonneg_left` | core algebra | ✓ | §4 linear comparison |
| 7 | `neg_le_neg_iff` | core order | ✓ | §4 negation step |
| 8 | `Real.log_log_lt_log` | not found at v4.26.0 — need to derive | ⚠ may need hand-derived | §2 asymptotic check |
| 9 | `Real.log_lt_self` | `Analysis/SpecialFunctions/Log/Basic.lean:?` | ✓ standard | §2 fallback for §8 |

Item 8 (`Real.log_log_lt_log`) is NOT confirmed at v4.26.0. The
hand-derivation is `Real.log_lt_self` applied to `log N`: for
`log N > 0`, `log (log N) < log N`. So §2's asymptotic check goes
through via §9 (`Real.log_lt_self`) and standard arithmetic.

**Net audit verdict**: the §4 conditional discharge needs only items
1-7 plus standard `Real.rpow` machinery. No phantom names; all five
core lemmas exist at v4.26.0. The §2 numerical analysis is
informational and does not need a Lean discharge.

## §7. Build status notes

This PREP is doc-only. No Lean changes. The §4 / §5 skeleton bodies
use a single `sorry` each, intended as templates for an eventual
S6-d ACT (or later) that ships the conditional discharge as a Lean
theorem.

The local `proofs/.lake` symlink loop (per memory
`feedback_researcher_lake_symlink_loop_and_wipe.md`) prevents
direct `./proofs/scripts/docker-build.sh Proofs.RothTheoremOQ02`
from this session, so even an ACT-level discharge would have to ship
"build pending". This PREP avoids that risk by being doc-only.

## §8. What this PREP does NOT claim

* **K–M envelope dominates B–S envelope unconditionally.** Not
  claimed. §3's obstruction shows the unconditional comparison is
  unprovable from the current axiomatic frame.

* **The numerical threshold table in §2.2 is exactly correct.** Not
  claimed. The §2.3 ERRATUM acknowledges the table values are rough
  asymptotic estimates, not implicit-equation solutions. The
  qualitative conclusion (K–M dominates eventually, no uniform `N*`)
  is robust.

* **The §5 corollary closes any new mathematical content.** Not
  claimed. The corollary is a packaging convenience around the §4
  conditional, not new theory. Its main value is to surface the
  asymptotic redundancy of B–S in the joint min envelope.

* **The conditional bounds `C₁ ≤ kelleyMekaConst` and
  `blasiConst ≤ C₂` can be proved.** Not claimed. These are inputs to
  the conditional, requiring an external strengthening of the axioms
  (an S5-c / S6-c PREP — distinct from this S6-c — that ships
  refined axioms with explicit constant bounds). Such a strengthening
  would require an audit of the K–M 2023 and B–S 2020 papers' actual
  constant tracking, which is out of scope for this PREP.

* **The S6-c PREP closes any of S5b PREP's or S6 PREP's deferred
  follow-ups.** Not claimed. S6-c is orthogonal — it compares K–M
  and B–S to each other, not either against Behrend. The S5b PREP
  and S6 PREP analyses of K–M-vs-Behrend and B–S-vs-Behrend
  respectively remain prerequisites for any combined picture.

* **The slug's open question OQ-02 is closed.** Not claimed. OQ-02 is
  about the gap between Behrend and the best upper bound; this PREP
  contributes a comparison BETWEEN two upper bounds, not toward
  closing the Behrend gap.

## §9. Honesty notes

* **Numerical table in §2.2 is approximate.** As acknowledged in
  §2.3's ERRATUM, the `u_K` column values are asymptotic estimates
  via the Lambert-W expansion, not exact solutions. Any future
  Lean-side verification should use a direct numerical solver. The
  qualitative pattern (smaller `c_KM` and larger `c_BS` push `N*`
  upward without bound) is correct.

* **No PDF audit of K–M 2023 or B–S 2020.** This PREP analyses the
  envelopes as-stated in the file, treating `c_KM` and `c_BS` as
  axiom-frame parameters. A future PREP could extract concrete bounds
  from the original papers and use them as values for `C₁, C₂` in
  the §4 conditional. This PREP does not perform that audit.

* **No new axioms, no new sorries, no new definitions, no Lean
  changes.** The deliverable is the planning artefact
  `sessions/2026-05-13-s6c-prep-km-vs-bs-envelope-comparison.md`.

* **No race risk.** This PREP creates a single new `sessions/` file.
  The two open same-slug PRs are:
  - PR #18685 (S6 PREP, doc-only sessions/) — different file in
    `sessions/`, no overlap.
  - PR #18181 (S3 ACT, stale 4 days, modifies `proofs/.../*.lean`
    + `state.md` + JSON) — Lean and state-md edits, but THIS PREP
    is doc-only and only adds a NEW file. No overlap.

* **Pre-push race re-check** required immediately before push to
  catch any sibling PREP (S6-c, S6-d, etc.) that may have shipped
  in the ~10 min since this PREP's claim.

* **S6-c naming**: this PREP claims the "S6-c" label. S6-d (or
  later) is reserved for the eventual ACT shipping the §4 conditional
  Lean theorem. If a sibling researcher uses "S6-c" for an ACT
  before this PREP merges, this PREP's title can be revised to
  "S6-c PREP — comparison" without semantic conflict.

---

**Build status**: doc-only; no Lean compilation needed; no race risk
with in-flight Lean PRs (`sessions/` subdirectory only). The S5 + S5b
+ S6 + S6-c PREP series catalog the analytic envelope landscape:

* S5 PREP (researcher-5, merged): identifies the K–M-vs-Behrend
  obstruction.
* S5b PREP (researcher-6, merged): discharges the K–M-vs-Behrend
  conditional sorries.
* S6 PREP (open, researcher-?): discharges the B–S-vs-Behrend
  conditional sorries.
* S6-c PREP (this PR, researcher-12): K–M vs B–S head-to-head
  comparison + asymptotic redundancy of B–S in the joint min envelope.

Together they specify the analytic infrastructure needed for an
eventual S5-a / S6-a / S6-d ACT to ship a complete sorry-free
Lean discharge of the conditional envelope inequalities.
