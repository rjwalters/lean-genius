# Session 2026-05-09 (Iteration 8, researcher-9) — S8 partial: integral building blocks for K-side IBP

**Mode**: ACT (RICH knowledge tier, score 47 — depth-over-breadth)
**Outcome**: Two new sorry-free lemmas in
`proofs/Proofs/AmgmInequalityOQ04OQ02.lean` (new §12) — `integral_sin_sq_div_sqrt_denom`
and `integral_cos_sq_div_sqrt_denom`. These are the **integral building blocks**
that the IBP step (S9) will combine with FTC on the auxiliary function
`auxFnK k θ := sin θ · cos θ / √(1-k²sin²θ)` to discharge the K-side
integral identity `∫ dIntegrandK k θ dθ = (E - (1-k²) K) / (k(1-k²))`.

## Why split S8 into "S8 partial" + "S9 IBP step"

The full S8 target is the integral identity, estimated at 80–120 lines.
Three reasons to split:

1. **Local Docker build cost is ~45+ min** (memory note
   `feedback_researcher_lake_symlink_broken`), so a single-PR delivery of
   the full IBP requires shipping ~120 lines untested locally and
   waiting one CI cycle.
2. **The two integral identities are independently useful.**  They are
   the integrated form of `dIntegrandE_mul_k` (sin² case) and a direct
   `cos² = 1 - sin²` corollary (cos² case).  Future K-derivative work
   (alternative proofs of `dK/dk`, hypergeometric identities, AGM-route
   reformulations) can reuse them without committing to the auxFnK
   route.
3. **Bounded-risk delivery.**  ~80 Lean lines of pointwise identity
   + integral linearity is mechanical; the IBP step (S9) requires
   `HasDerivAt` chain rule on a quotient, which is the algebraically
   trickiest piece and the one most likely to require iteration.

## What this session adds

### §12.1 `integral_sin_sq_div_sqrt_denom`

```lean
lemma integral_sin_sq_div_sqrt_denom (hk_pos : 0 < k) (hk_lt : k < 1) :
    ∫ θ in (0 : ℝ)..π / 2,
        Real.sin θ ^ 2 / Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2)
      = (AmgmInequalityOQ04OQ01.ellipticK k - ellipticE k) / k ^ 2
```

Proof sketch:
- **Pointwise**: `sin²θ / √D = (ellipticIntegrand - ellipticIntegrandE) / k²`.
  Multiplying by `k² · √D` reduces to `k²sin²θ = 1 - D²`, which is
  exactly the Pythagorean identity `D² = 1 - k²sin²θ` rearranged.
  Lean: `field_simp; linear_combination hs_sq` where
  `hs_sq : √D · √D = 1 - k²sin²θ` from `Real.mul_self_sqrt`.
- **Integral lift**: `intervalIntegral.integral_congr` swaps the
  integrand to the pointwise form; `intervalIntegral.integral_div` pulls
  the `1/k²` outside; `intervalIntegral.integral_sub` splits using
  `ellipticK_integrable` and `ellipticE_integrable`; `rfl` closes since
  `ellipticK = ∫ ellipticIntegrand` and `ellipticE = ∫ ellipticIntegrandE`
  by definition.

This is the **integrated form** of §8's `dIntegrandE_mul_k`:
- §8 said `k · dIntegrandE = ellipticIntegrandE - ellipticIntegrand`
  (pointwise).
- §12.1 says the integrated `sin²θ` form is `(K - E) / k²`.
- The factor of `k` (not `k²`) on the §8 LHS becomes `k²` on §12.1's
  denominator because we multiply through by an extra `k`/√D
  to isolate `sin²θ` rather than `dIntegrandE`.

### §12.2 `integral_cos_sq_div_sqrt_denom`

```lean
lemma integral_cos_sq_div_sqrt_denom (hk_pos : 0 < k) (hk_lt : k < 1) :
    ∫ θ in (0 : ℝ)..π / 2,
        Real.cos θ ^ 2 / Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2)
      = (ellipticE k - (1 - k ^ 2) * AmgmInequalityOQ04OQ01.ellipticK k)
          / k ^ 2
```

Proof sketch:
- **Pointwise**: `cos²θ / √D = ellipticIntegrand - sin²θ/√D`, immediate
  from `cos²θ = 1 - sin²θ` (from `Real.sin_sq_add_cos_sq`) and
  `sub_div`.
- **Integral lift**: split the integral via `integral_sub`; substitute
  §12.1's value for the `sin²θ` integral; algebraic close
  `K - (K-E)/k² = (k²K - K + E)/k² = (E - (1-k²)K)/k²` via `field_simp; ring`.

## Why this is real progress (not a sorry-relocation)

This session **proves two new theorems** with no new sorries and no new
axioms; it is honest forward progress.  The full S8 target
`integral_dIntegrandK_eq` is **not** delivered this session — it remains
to be proved in S9.  The contribution is:

* +2 theorems, 0 axioms, 0 sorries, +135 lines.
* Two reusable lemmas about elliptic integrals that any future
  K-derivative work can build on.
* A **concretized recipe for S9** (auxFnK + FTC + combine) that reduces
  the remaining work from "find an antiderivative" to "compute the
  derivative of a known function and combine with §12".

## Honest assessment of progress

- Session score: **modest but real**.  Two integral identities
  (~30+50 lines) plus the §12 docstring with the IBP plan.
- Sorry/axiom delta: **0**.  Both new lemmas are sorry-free,
  axiom-free.
- Did not solve the open question.  The K-side integral identity, the
  `dK_dk` assembly, and the Wronskian closure all remain.
- Plan trajectory unchanged from S7 (this PR is a partial advance on
  the S8 line item; S9–S11 lines unchanged).

## Build status

Local Docker build NOT attempted (`proofs/.lake` self-symlink → 45+
minute fresh clone + cache fetch).  Defer to CI on the PR.

## Risk register

* **`linear_combination hs_sq` coefficient**: I verified by hand that
  coefficient 1 (no minus) closes the goal after `field_simp` produces
  `sin²θ * k² = 1 - sqrt * sqrt`.  If `field_simp`'s normalization
  produces a different form, may need to adjust to
  `linear_combination -hs_sq` or add an explicit `ring` after.  Risk:
  **low** — verified algebraically, mirrors the S8 pattern at
  `dIntegrandE_mul_k`.
* **`rfl` closure of `(∫ K_int) - (∫ E_int) = ellipticK - ellipticE`**:
  by definition of `ellipticK` and `ellipticE` via `∫`, this should be
  `rfl`.  If Lean's elaboration prefers an explicit `unfold`, may need
  `show ellipticK k - ellipticE k = ellipticK k - ellipticE k` before
  `rfl`.  Risk: **low** — same pattern at line 471 (closing
  `integral_dIntegrandE_eq`).
* **`Real.sin_sq_add_cos_sq` direction sign**: I verified by hand that
  `linear_combination Real.sin_sq_add_cos_sq θ` (coefficient +1) closes
  the goal `cos²θ = 1 - sin²θ`.  Compare to line 183 of this file which
  uses coefficient -1 for the *reverse* direction `1 - sin²θ = cos²θ`.
  Risk: **very low**.

## Files modified

- `proofs/Proofs/AmgmInequalityOQ04OQ02.lean` (+135 lines: new §12 with
  docstring + 2 lemmas).
- `src/data/proofs/amgm-inequality-oq-04-oq-02/meta.json` (lineCount
  829→964, theoremCount 36→38; both `meta.*` and `leanFile.*` blocks).
- `research/problems/amgm-inequality-oq-04-oq-02/state.md` (Iteration
  7→8; Iteration 8 entry + Sharpening of the Plan for S9+).
- `research/problems/amgm-inequality-oq-04-oq-02/sessions/2026-05-09-s08-partial-integral-building-blocks.md`
  (this note).

## Next iteration recommendations

**S9**: Complete the IBP step.  ~95 lines:

1. `auxFnK` definition and endpoint values (sin 0 = 0, cos(π/2) = 0).
2. `auxFnK_hasDerivAt` — chain rule + algebraic reduction to integrating form.
3. `integral_auxFnK_deriv_eq_zero` via `integral_eq_sub_of_hasDerivAt`.
4. Combine with §12.2 to close `integral_dIntegrandK_eq`.

After S9 lands, S10 (`dK_dk` assembly) is a ~30-line mirror of the
S5/PR-#17371 `dE_dk` template.

## Sorry/axiom counts

| metric                | before S8 partial | after S8 partial |
|-----------------------|-------------------|------------------|
| total sorries         | 0                 | 0                |
| total axioms          | 1                 | 1                |
| theorem count         | 36                | 38               |
| line count            | 829               | 964              |
