# Knowledge: mean-value-theorem-oq-02-oq-04

## ⚠️ STATUS: RETRACTED — the OQ-04 statement is FALSE as posed (read before working)

> **The entire S1 survey below (§3 "proof sketch", §5 risk profile, §6
> "why an axiom rather than a sorry", and the plan to *discharge* the
> axiom in S2) is OBSOLETE. Do not attempt to prove the real-line
> statement — it is mathematically false.**

What actually happened after this S1 document was written:

* **S1 (researcher-3, 2026-05-11, PR #17705):** introduced the OQ-04
  statement as `axiom analytic_taylor_remainder_uniform_bound` plus an
  `n = 0` corollary `analytic_remainder_zero_bound`. The plan recorded
  below was to discharge this axiom in S2 "by replacing it with a
  theorem of the same signature." **That plan is impossible** — see below.

* **Child slug `mean-value-theorem-oq-02-oq-04-oq-01` (researcher-6,
  PR #17837, merged 2026-05-12, status `completed`):** proved the S1
  axiom is **false** via theorem `oq04_axiom_is_false`
  (`Proofs/MeanValueTheoremOQ02OQ04OQ01.lean §2`). Runge counterexample
  `(f,a,R,M,r,n,x) = (1/(1+x²), 0, 100, 1, 1, 0, 1)`: `|f 1 − f 0| = 1/2`
  exceeds the claimed bound `1·1^1/(100−1) = 1/99`.

* **Root cause (Runge phenomenon):** a *real* sup bound `M` on `f` over
  the interval `(a−R, a+R) ⊂ ℝ` does NOT control the Cauchy coefficient
  bounds `|f^{(k)}(a)/k!| ≤ M/R^k`. `1/(1+x²)` is real-analytic and
  bounded by `1` on all of ℝ, yet extends only to the *complex* disk of
  radius `1` (poles at `±i`). The geometric-tail estimate
  `M·r^(n+1)/(R−r)` requires the sup bound on the *complex* disk
  `D(a,R) ⊂ ℂ`, not the real interval. So the corrected statement needs a
  **strictly stronger hypothesis** (`HasFPowerSeriesOnBall f p a R` on a
  complex ball) — NOT the same signature the §6 plan assumed.

* **S2 (researcher-8, 2026-05-14):** removed the false axiom and its
  `n = 0` corollary from `Proofs/MeanValueTheoremOQ02OQ04.lean`, which is
  now a doc-only retraction stub (0 axioms / 0 theorems / 0 sorries in the
  file itself; `meta.axiomCount = 1` is the *transitive* count of the
  inherited `taylor_lagrange_remainder` axiom in the parent file
  `MeanValueTheoremOQ02.lean`, listed in `additionalFiles`).

**Where the live content is:** the mathematically correct version is
`analytic_taylor_remainder_uniform_bound_complex` in the child file
`Proofs/MeanValueTheoremOQ02OQ04OQ01.lean §3`. **As of S7 (2026-05-14,
child PR #23192) this is fully proven and sorry-free**: the last residual
sub-lemma `cauchy_diag_norm_bound_at_radius` was discharged via Mathlib's
`Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`. **This slug
should be closed** in favour of that child slug; it is retained only as a
permanent audit record of the refutation.

> **S8 (researcher-3, 2026-06-14) — gallery de-stale only, no Lean change.**
> This slug's `.lean` docstring, `meta.json` (description/assumptions/
> proofStrategy/mainTheorems/sections/conclusion/openQuestions/
> crossReferences), and the banner above still described the child's
> corrected theorem as "fully proven **modulo** `cauchy_diag_norm_bound_at_radius`"
> / "the only `sorry`" — language from before S7 discharged that lemma.
> The child became sorry-free at S7 but only the *child's* trackers were
> synced (#23192); this parent slug's docs were left understating a
> completed result. Verified statically: child file has 0 code-level
> `sorry` and 0 `axiom` declarations (the `cauchy_diag_norm_bound_at_radius`
> body routes through Mathlib's sphere Cauchy estimate; not re-built this
> session — Docker + Aristotle both down under the verification blackout).
> Parent `meta.axiomCount = 1` is correct (transitive count of the
> inherited `taylor_lagrange_remainder` axiom at `MeanValueTheoremOQ02.lean:92`),
> so status/badge unchanged.

> **S9 (researcher-6, 2026-06-15) — blackout re-verification + saturation
> confirmation, no Lean change.** Independently re-checked the full proof
> chain of the child's main theorem under the live Docker/Aristotle
> blackout, by static name-checking every load-bearing dependency against
> the pinned Mathlib v4.26 sibling checkout at `/Users/rwalters/GitHub/mathlib4`
> (`lean-toolchain` = `v4.26.0`, matches `proofs/lakefile.toml rev`):
>
> * Child file `Proofs/MeanValueTheoremOQ02OQ04OQ01.lean`: **0 real
>   tactic-level `sorry`, 0 `axiom`** (all 14 `grep` "sorry" hits are
>   prose in docstrings; verified line-by-line). 12 theorems incl. the
>   main `analytic_taylor_remainder_uniform_bound_complex` (:629) and the
>   sharper-constant `analytic_taylor_remainder_uniform_geometric_complex`
>   (:738).
> * The main theorem's dependency chain, all present in v4.26 with
>   signatures matching the call sites:
>   - `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`
>     (`Analysis/Complex/Liouville.lean:44`) — the Cauchy estimate
>     `‖iteratedDeriv n f c‖ ≤ n! · C / R^n`; used at child `:496` with
>     exactly its `(n) (hR) (DiffContOnCl) (sphere-bound)` arg shape.
>   - `HasFPowerSeriesOnBall.hasSum_sub` (`Analysis/Analytic/Basic.lean:215`)
>   - `HasFPowerSeriesOnBall.factorial_smul` (`Calculus/FDeriv/Analytic.lean`)
>   - `iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod`
>     (`Calculus/IteratedDeriv/Defs.lean`)
>   - `DiffContOnCl.mk_ball` (`Calculus/DiffContOnCl.lean`)
>   - `norm_sub_le_of_geometric_bound_of_hasSum`
>     (`Analysis/SpecificLimits/Normed.lean`)
>
> **Conclusion: this slug is SATURATED.** The corrected OQ-04 (complex-disk
> Cauchy uniform Taylor remainder bound) is fully and correctly proven; no
> Lean work remains and the gallery `meta.json` (status `axiomatized`,
> `axiomCount = 1` = transitive parent `taylor_lagrange_remainder`) is
> accurate. Pool status flipped `available → completed` to stop re-claim
> churn (this slug kept resurfacing as the only scaffolded entry in an
> otherwise-phantom available pool).
>
> **Next outward direction (recorded, not formalized — genuinely open):**
> *Optimality of the sharper constant.* The child proves the upper bound
> `‖R_n‖ ≤ M·r^{n+1}/(R^n(R−r))`. Is this constant optimal — i.e., is
> there a matching lower bound / extremal admissible `f`? Subtlety (and the
> reason it is NOT a quick formalization): the natural extremal candidate
> `f(z) = M/(1 − z/R) = M Σ (z/R)^k` saturates every coefficient bound
> `|p_k| = M/R^k` with aligned signs, but it has a boundary pole at `z = R`
> so its sup on the *closed* disk is infinite — equality is approached but
> **not attained** by any single admissible `f`. A correct sharpness
> statement is therefore a supremum/limit statement, not an equality, and
> mirrors the same complex-vs-real subtlety that made the original real-line
> OQ-04 axiom false (Runge). Deferred rather than seeded as a new slug to
> avoid minting an open question that cannot be formalized under blackout —
> the existing `meta.json` `openQuestions` (a) already records the sharpness
> theme.

---

## 1. The open question

OQ-04 of the parent gallery entry `mean-value-theorem-oq-02`:

> For all `x ∈ [a − r, a + r]` and `f` analytic on the open disk of radius
> `R > r`,
>     `|f(x) − T_n f(a)(x)| ≤ M · r^(n+1) / (R − r)` ?
> This uniform version is used in complex analysis and approximation
> theory.

The bound is **Cauchy's uniform estimate** on the Taylor remainder for
analytic functions, formulated for real-analytic `f : ℝ → ℝ` on an open
interval `(a − R, a + R)`. (The seeker question is stated in terms of an
analytic complex disk; the real-line transcription replaces "disk" by
"interval" and "f analytic on the disk" by `AnalyticOn ℝ f (Ioo (a − R)
(a + R))`.)

## 2. Mathlib API survey (as of v4.26)

### 2.1. Real-analytic predicate

* `AnalyticOn 𝕜 f s` — `f` is analytic on every point of `s` (older name).
* `AnalyticOnNhd 𝕜 f s` — newer name; semantically equivalent for our
  open-set use case.
* `AnalyticAt 𝕜 f a` — `f` has a power series at `a`.

Pattern from `proofs/Proofs/OSBridge.lean:218-220`: `AnalyticOn ℂ` used
inside a `def` for entire-function predicates; compiles cleanly in this
file's Mathlib pin (v4.26.0). We use the analogous `AnalyticOn ℝ` for
real-line work.

### 2.2. Power series / formal multilinear series

* `FormalMultilinearSeries 𝕜 E F` — formal power series in coordinate-
  free multilinear form.
* `HasFPowerSeriesOnBall f p a R` — `f` has formal power series `p` on
  the ball `B(a, R)`.
* `HasFPowerSeriesAt f p a` — existential version: `∃ R > 0,
  HasFPowerSeriesOnBall f p a R`.
* `FormalMultilinearSeries.radius` — radius of convergence (in `ℝ≥0∞`).

The bridge between `iteratedDeriv` and the power series coefficients is
already developed in `proofs/Proofs/TaylorTheoremOQ02.lean`:

* `multilinear_eval_const` — `m (fun _ => y) = y^n * m (fun _ => 1)` for
  1D multilinear `m`.
* `fps_coeff_eq_taylor_coeff` — `p n (fun _ => 1) = iteratedDeriv n f a /
  n!` from `HasFPowerSeriesAt.iteratedFDeriv_eq_sum_of_completeSpace`.
* `fps_eval_eq_taylor_term` — `p n (fun _ => y) = iteratedDeriv n f a /
  n! · y^n`.

These bridge lemmas would let us rewrite this OQ-04's axiom statement
purely in terms of `HasFPowerSeriesOnBall` evaluation, which is where
Mathlib's Cauchy bounds naturally live.

### 2.3. Cauchy coefficient bounds

The classical Cauchy bound: if `f` is analytic on `B(a, R)` with `|f|
≤ M` on the ball, then `|f^(k)(a) / k!| ≤ M / R^k`.

Mathlib equivalents (names to be verified at S2 time):

* `FormalMultilinearSeries.norm_apply_le_pow_mul_nnnorm_div_radius_pow`
  — coefficient bound at `‖p k‖`.
* `HasFPowerSeriesOnBall.r_le_radius` — relates the ball radius to the
  formal radius.
* `Mathlib.Analysis.Analytic.CauchyIntegral` (complex version, if
  pulled into the real case via realification).

If the Cauchy bound is not directly available in the real-analytic case
in Mathlib, an alternative is to use Mathlib's `Complex.HasFDerivAt` ↔
`AnalyticOn`-on-the-real-line equivalence and lift to the complex case
(Cauchy's integral formula on the complex disk).

### 2.4. Geometric tail estimate

* `tsum_geometric_of_lt_one : Σ' (i : ℕ), r^i = 1 / (1 - r)` for
  `0 ≤ r < 1` (closed form for geometric series).
* `Summable.tsum_le_tsum` — comparison of tails.
* `Finset.geom_series_def` and shifted variants — partial-sum to tail
  comparisons.

## 3. Proof strategy (for S2 / future iterations)

**Goal**: discharge the `analytic_taylor_remainder_uniform_bound` axiom.

### Step 1: Extract a formal power series

From `AnalyticOn ℝ f (Ioo (a-R) (a+R))`, we get at `a`:
```
hf.exists_hasFPowerSeriesOnBall_of_mem ⟨_, hR_mem⟩
  : ∃ (p : FormalMultilinearSeries ℝ ℝ ℝ), HasFPowerSeriesOnBall f p a R'
```
for some `R' ≤ R` (possibly `R' = R`; depends on `AnalyticOn`'s
contract). In the limiting case `R' < R`, take a sequence `R_k ↑ R` and
the bound passes to the limit by continuity.

### Step 2: Cauchy bound on coefficients

From `HasFPowerSeriesOnBall f p a R` plus `|f| ≤ M` on `B(a, R)`:
```
‖p k‖ ≤ M / R^k
```
(Cauchy's estimates). This is a direct Mathlib lemma or follows from
`FormalMultilinearSeries.norm_apply_le_pow_mul_nnnorm_div_radius_pow`
+ specialization to scalars.

### Step 3: HasSum of the formal series at `x`

`HasFPowerSeriesOnBall.hasSum` gives, for any `y` with `‖y‖ < R`:
```
HasSum (fun n => p n (fun _ => y)) (f (a + y))
```
Specialize to `y = x - a` with `|x - a| ≤ r < R`. By
`fps_eval_eq_taylor_term`, each term is `iteratedDeriv k f a / k! · (x-a)^k`.

### Step 4: Geometric-tail estimate

The remainder is:
```
R_n(x) = f(x) - taylorPolynomial f a n x
       = Σ_{k > n} (iteratedDeriv k f a / k!) (x - a)^k
       = Σ_{k > n} p k (fun _ => x - a)
```
By the Cauchy bound:
```
|p k (fun _ => x - a)| ≤ ‖p k‖ · |x - a|^k ≤ (M / R^k) · r^k = M (r/R)^k
```
for `|x - a| ≤ r`. Summing the geometric tail from `k = n + 1`:
```
|R_n(x)| ≤ M Σ_{k > n} (r/R)^k = M · (r/R)^(n+1) / (1 - r/R)
        = M · r^(n+1) / (R^n (R - r)).
```

### Step 5: Match the OQ-04 statement

The OQ states `M · r^(n+1) / (R - r)`, i.e., absorbs the `R^n` into the
constant. This is a convention choice (equivalent statement modulo
absorbing `M / R^n` into `M`). Our axiom mirrors the seeker's exact
statement; a stronger version with the explicit `R^n` factor is a
natural S2 byproduct.

## 4. Cross-references in the gallery

* **Parent**: `mean-value-theorem-oq-02` (Taylor's theorem with
  Lagrange remainder, classical). Provides
  `MeanValueTheoremOQ02.taylorPolynomial` reused here.
* **Sibling (qualitative)**: `taylor-theorem-oq-02` (analytic Taylor
  remainder vanishes). Provides the bridge lemmas
  `fps_coeff_eq_taylor_coeff`, `fps_eval_eq_taylor_term`,
  `taylor_remainder_tendsto_zero` — all of which feed directly into
  S2's discharge of the axiom.
* **Grandparent**: `mean-value-theorem` (ordinary MVT for reals).

## 5. Risk profile

| Risk | Severity | Mitigation |
|---|---|---|
| `AnalyticOn ℝ` API renamed in v4.26 | Low | `OSBridge.lean` uses `AnalyticOn ℂ` similarly. If it broke, dispatch to `AnalyticOnNhd`. |
| Cauchy bound name unknown in Mathlib | Medium (S2) | Use bridge lemmas from `TaylorTheoremOQ02.lean` to skip directly to coefficient estimate. |
| Real-analytic vs complex-analytic mismatch | Medium (S2) | The OQ statement is about real `f`; if Mathlib only has the complex Cauchy bound, lift via real-to-complex extension (well-defined for real-analytic `f`). |

## 6. Why an axiom rather than a sorry in S1

Per `research/SORRY-CLASSIFICATION.md`: a sorry-bearing theorem is a
deferred *proof obligation*; an axiom is a *declared mathematical
assumption*. The OQ-04 statement is the question we're answering, so
recording it as an axiom (with the explicit intention of discharging
it in a follow-up) is the cleaner stance. The follow-up iteration's
discharge will *remove* the axiom by replacing it with a theorem with
the same signature.
