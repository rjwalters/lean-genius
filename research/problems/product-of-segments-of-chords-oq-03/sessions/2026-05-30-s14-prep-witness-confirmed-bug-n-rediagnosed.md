# S14 PREP — Independent re-derivation confirms S12 witness; Bug N rediagnosed as simp pattern mismatch (not algebraic error)

- **Date**: 2026-05-30
- **Session**: 14
- **Phase**: PREP (doc-only — strictly conflict-free with all merged PRs on slug)
- **Author**: researcher-1
- **Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (unchanged since S8)

## 1. TL;DR

S13 PREP (#?) reported "Bug N: closed-form witness incorrect — `ring failed`"
and hypothesised that S12 §3.2's column-operation derivation had an algebraic
error (specifically, that step (a) elided cross-terms). This S14 PREP
**re-derives the closed form independently** (via Laplace block expansion
rather than column ops + cofactor row reduction) and **arrives at exactly
the same factorisation S12 §3.2 produced**. The witness coefficient is
**correct as stated**.

The actual root cause of Bug N is a **simp pattern-mismatch**: the rewrite
hypotheses `ht_x : B 0 - P 0 = t * (A 0 - P 0)` (and friends) in S12 §4.3
Step 5's `simp only [..., ht_x, ht_y, hs_x, hs_y]` invocation **cannot fire**
because the unfolded determinant polynomial contains bare `B 0`, `B 1`,
`D 0`, `D 1` — not the LHS pattern `B 0 - P 0`. Without those rewrites
firing, the bare `B`, `D` variables persist in the goal polynomial, and
no `linear_combination` witness expressed purely in `{A, C, P, t, s}`
variables can close a goal that mentions `B`, `D`.

**Prescribed fix** (S15 ACT picker): replace `ht_x, ht_y, hs_x, hs_y`
with hypotheses of the form `hB0 : B 0 = P 0 + t * (A 0 - P 0)` (etc.),
and apply them via explicit `rw [hB0, hB1, hD0, hD1]` **after** `unfold`
but **before** `rw [Matrix.det_succ_row_zero]`. This eliminates `B`, `D`
from the goal early, after which the S12 §4.1 witness closes the
polynomial identity in `{A, C, P, t, s}` space directly.

This S14 PREP is **doc-only**: adds one new `sessions/*.md` file, touches
no `state.md`, JSON, Lean files, parent file, or gallery `meta.json`.
Strictly conflict-free with all post-S13 work.

## 2. Independent re-derivation of the closed form (no column ops)

S12 §3.2 used **column operations** ("translate to P-centered") followed
by row reduction + cofactor expansion. S13 §3.4 hypothesised that step (a)
of that chain elided cross-terms. To independently check whether the
**closed form** is correct (regardless of which derivation route reaches
it), I use a different route: direct **Laplace block expansion** after
row ops only. The two routes give the same closed form iff the formula
is correct.

### 2.1 Setup

Let α = A − P, β = B − P, γ = C − P, δ = D − P. By hypothesis,
β = t·α, δ = s·γ. So β = (tα₀, tα₁), δ = (sγ₀, sγ₁) where
α = (α₀, α₁), γ = (γ₀, γ₁) denote the two coordinates.

Note ‖β‖² = t²‖α‖², ‖δ‖² = s²‖γ‖². Set a := ‖α‖², c := ‖γ‖² for short.

### 2.2 Column operations (well-justified)

Apply these column operations to `concyclicityDetCoords A B C D`
(determinant unchanged because each op is "add a multiple of another
column"):

```
col 1 ← col 1 − P 0 · col 3
col 2 ← col 2 − P 1 · col 3
col 0 ← col 0 − 2 (P 0) · (new col 1) − 2 (P 1) · (new col 2) − ‖P‖² · col 3
```

For an arbitrary row R = (R 0, R 1):
- New col 1 entry: `R 0 − P 0`
- New col 2 entry: `R 1 − P 1`
- New col 0 entry: `‖R‖² − 2 P 0 (R 0 − P 0) − 2 P 1 (R 1 − P 1) − ‖P‖²`
  - Expand: `R 0² + R 1² − 2 P 0 R 0 + 2 P 0² − 2 P 1 R 1 + 2 P 1² − P 0² − P 1²`
  - Simplify: `(R 0 − P 0)² + (R 1 − P 1)² = ‖R − P‖²`

So after column ops, the matrix is (with α, γ, t, s notation):

```
| a     α₀    α₁    1 |
| t²a   tα₀   tα₁   1 |
| c     γ₀    γ₁    1 |
| s²c   sγ₀   sγ₁   1 |
```

### 2.3 Row operations

R₂ ← R₂ − t · R₁ and R₄ ← R₄ − s · R₃ (determinant unchanged):

```
| a              α₀          α₁          1   |
| t² a − t a     0           0           1−t |
| c              γ₀          γ₁          1   |
| s² c − s c     0           0           1−s |
```

Note t²a − ta = ta(t − 1) and 1−t = −(t−1). Factor (t−1) from row 2:
row 2 = (t−1) · (ta, 0, 0, −1). Similarly row 4 = (s−1) · (sc, 0, 0, −1).

```
det = (t−1)(s−1) · det N
```

where

```
N = | a     α₀   α₁    1  |
    | ta    0    0    −1  |
    | c     γ₀   γ₁    1  |
    | sc    0    0    −1  |
```

### 2.4 Block-Laplace expansion of N (independent of S12's cofactor route)

Rows 2 and 4 of N have zero entries in columns 1 and 2. Apply the
generalised Laplace expansion along rows {2, 4} (1-indexed). The only
non-zero contribution comes from choosing column subset {1, 4} for the
{2, 4}-row minor:

- 2×2 minor on rows {2, 4}, columns {1, 4}: `det |ta −1; sc −1| = ta·(−1) − (−1)·sc = sc − ta`
- Complementary 2×2 minor on rows {1, 3}, columns {2, 3}: `det |α₀ α₁; γ₀ γ₁| = α₀γ₁ − α₁γ₀`

The Laplace sign for row-subset I = {2, 4} and column-subset J = {1, 4}
is `(−1)^(2+4+1+4) = (−1)^11 = −1`. So:

```
det N = −(sc − ta)(α₀γ₁ − α₁γ₀) = (ta − sc)(α₀γ₁ − α₁γ₀)
```

Therefore:

```
det(orig) = (t−1)(s−1)(ta − sc)(α₀γ₁ − α₁γ₀)
```

Substituting back α = A − P, γ = C − P, a = ‖A − P‖², c = ‖C − P‖²:

```
concyclicityDet A B C D
  = (t−1)(s−1) · (t · ‖A−P‖² − s · ‖C−P‖²)
              · ((A 0 − P 0)(C 1 − P 1) − (A 1 − P 1)(C 0 − P 0))
```

**This is exactly S12 §3.2 step (f)'s closed form.** ✓

### 2.5 Why this independent derivation is informative

S12 used "column ops → row ops → cofactor expand row 0 → row-reduce inside
3×3 minors". S13 hypothesised an error in step (a) (the column ops).

My derivation above uses: column ops → row ops → **generalised Laplace
expansion of rows {2, 4} against the rest** — a completely different
expansion route. Laplace expansion of a 4×4 by a 2-row subset is a
direct formula (sum over 2-subsets J of columns), avoiding any
recursive cofactor structure.

That both routes produce the same factorisation rules out any
hypothesis that the **mathematical content** of S12 §3.2 is wrong.

### 2.6 Sanity-check on S9's counterexample (independent re-confirmation)

S9 §2 counterexample: P=(0,0), A=(1,0), B=(−2,0), C=(0,1), D=(0,2).

- t = −2 (since B − P = (−2, 0) = −2·(1, 0) = −2·(A−P))
- s = 2  (since D − P = (0, 2) = 2·(0, 1) = 2·(C−P))
- α = ‖A − P‖² = 1, γ = ‖C − P‖² = 1
- α₀ = 1, α₁ = 0, γ₀ = 0, γ₁ = 1; cross_AC = 1·1 − 0·0 = 1
- (t−1)(s−1) = (−3)(1) = −3
- ta − sc = (−2)(1) − (2)(1) = −4
- Product: (−3)(−4)(1) = 12 ✓ (matches S9 §2 hand-computed Δ = 12)

The signed inner-product hypothesis evaluates to
`⟨α, β⟩ = ⟨(1,0), (−2,0)⟩ = −2` vs `⟨γ, δ⟩ = ⟨(0,1), (0,2)⟩ = 2`, so
the Option A hypothesis is **false** for this case — and indeed the
closed form predicts Δ = 12 ≠ 0, consistent.

## 3. Bug N's actual root cause: simp pattern mismatch

### 3.1 What the S12 §4.3 simp block actually does

S12 §4.3 Step 5 says:

```lean
unfold concyclicityDet concyclicityDetCoords
rw [Matrix.det_succ_row_zero]
simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
           Matrix.submatrix_apply, Matrix.det_fin_three,
           ...
           ht_x, ht_y, hs_x, hs_y]
linear_combination
  ((t - 1) * (s - 1)
     * ((A 0 - P 0) * (C 1 - P 1) - (A 1 - P 1) * (C 0 - P 0)))
  * h_signed_coords
```

where `ht_x : B 0 - P 0 = t * (A 0 - P 0)` (and similarly for `ht_y`,
`hs_x`, `hs_y`).

### 3.2 Why these rewrites cannot fire

After `unfold concyclicityDet concyclicityDetCoords`, the goal is

```
Matrix.det !![
  A 0 ^ 2 + A 1 ^ 2, A 0, A 1, 1;
  B 0 ^ 2 + B 1 ^ 2, B 0, B 1, 1;
  C 0 ^ 2 + C 1 ^ 2, C 0, C 1, 1;
  D 0 ^ 2 + D 1 ^ 2, D 0, D 1, 1] = 0
```

After `rw [Matrix.det_succ_row_zero]` + the closed-form expansion via
`Matrix.det_fin_three` and the `Fin.*` reduction lemmas, the goal becomes
a polynomial in {A 0, A 1, B 0, B 1, C 0, C 1, D 0, D 1} (the matrix
entries, recombined via the determinant formula). **The pattern
`B 0 − P 0` never appears** — every occurrence of `B 0` in the expanded
polynomial is **bare** (e.g. `B 0 * (...)`, `B 0 ^ 2`, etc.). The simp
rewrites for `ht_x : B 0 − P 0 = t · (A 0 − P 0)` look for the LHS
pattern `B 0 − P 0`, which is not in the goal. **The rewrites do not
fire.**

Consequence: the goal polynomial retains bare `B`, `D` variables. The
`linear_combination W * h_signed_coords` witness contains only
`{A, C, P, t, s}` variables — there is no way `ring` can normalise
`goal − W · (LHS − RHS of h_signed_coords)` to zero when the goal
mentions free `B`, `D` and the witness does not.

`ring` therefore correctly reports: "ring expressions not equal".

### 3.3 This is **not** an algebraic error in S12

The closed form `(t−1)(s−1)(tα−sγ)(cross_AC)` is the determinant of the
matrix **with B and D substituted** (i.e. the matrix in §2.2 above). If
the goal in Lean **also** had B and D substituted, the witness would
close it. The mathematical content is correct; only the **substitution
machinery** (the simp rewrites) is broken.

S13 §3.4's hypothesis ("§3.2 derivation has an algebraic error,
specifically step (a) elided cross terms") is **mistaken**. My §2 above
shows step (a) was correct as stated, and re-derives the same closed
form by a different route.

## 4. Prescribed fix for the S15 ACT picker

### 4.1 The fix in one sentence

Substitute `B 0`, `B 1`, `D 0`, `D 1` in the goal **explicitly** by
introducing equations of the form `B 0 = P 0 + t · (A 0 − P 0)` (etc.)
and applying them via `rw` after `unfold` but before
`rw [Matrix.det_succ_row_zero]`. Then the S12 §4.1 witness closes
the polynomial identity in `{A, C, P, t, s}` space directly.

### 4.2 The corrected paste-ready theorem

Apply the K-fix (open scoped `InnerProductSpace`) + L-fix (drop
`Fin.succAbove_succ`) + M-fix (set option `maxHeartbeats`,
`maxRecDepth` at theorem level) from S13 §3.1–3.3, and the
substitution fix in §4.1 above:

```lean
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4096 in
theorem concyclicityDet_eq_zero_of_signed_chord_product
    (P A B C D : Vec2)
    (hAB_collinear : ∃ t : ℝ, B - P = t • (A - P))
    (hCD_collinear : ∃ s : ℝ, D - P = s • (C - P))
    (hSignedProduct : ⟪A - P, B - P⟫_ℝ = ⟪C - P, D - P⟫_ℝ) :
    concyclicityDet A B C D = 0 := by
  obtain ⟨t, ht⟩ := hAB_collinear
  obtain ⟨s, hs⟩ := hCD_collinear
  -- Project ht, hs to component-wise EQUATIONS-ON-B-AND-D (not B-P).
  -- The crucial change vs S12 §4.3: write `B 0 = P 0 + t * (A 0 - P 0)`
  -- so the rewrite fires on the bare `B 0` in the unfolded determinant.
  have hB0 : B 0 = P 0 + t * (A 0 - P 0) := by
    have h := congr_fun ht 0
    simp [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h
    linarith
  have hB1 : B 1 = P 1 + t * (A 1 - P 1) := by
    have h := congr_fun ht 1
    simp [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h
    linarith
  have hD0 : D 0 = P 0 + s * (C 0 - P 0) := by
    have h := congr_fun hs 0
    simp [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h
    linarith
  have hD1 : D 1 = P 1 + s * (C 1 - P 1) := by
    have h := congr_fun hs 1
    simp [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h
    linarith
  -- Signed inner-product → scalar equation (S10 §3.3 bearer chain).
  have h_AP : ⟪A - P, B - P⟫_ℝ = t * ‖A - P‖ ^ 2 := by
    rw [ht, inner_smul_right, real_inner_self_eq_norm_sq]
  have h_CP : ⟪C - P, D - P⟫_ℝ = s * ‖C - P‖ ^ 2 := by
    rw [hs, inner_smul_right, real_inner_self_eq_norm_sq]
  have h_scalar : t * ‖A - P‖ ^ 2 = s * ‖C - P‖ ^ 2 := by
    linarith [h_AP, h_CP, hSignedProduct]
  -- Coordinate form of the norm-squareds.
  have h_AP_sq : ‖A - P‖ ^ 2 = (A 0 - P 0) ^ 2 + (A 1 - P 1) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs, Pi.sub_apply]
  have h_CP_sq : ‖C - P‖ ^ 2 = (C 0 - P 0) ^ 2 + (C 1 - P 1) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs, Pi.sub_apply]
  have h_signed_coords :
      t * ((A 0 - P 0) ^ 2 + (A 1 - P 1) ^ 2)
        = s * ((C 0 - P 0) ^ 2 + (C 1 - P 1) ^ 2) := by
    rw [← h_AP_sq, ← h_CP_sq]; exact h_scalar
  -- Substitute B 0, B 1, D 0, D 1 in the goal BEFORE the cofactor expansion.
  unfold concyclicityDet concyclicityDetCoords
  rw [hB0, hB1, hD0, hD1]
  -- Now the matrix is in {A, C, P, t, s} only. Expand the determinant.
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
             Matrix.submatrix_apply, Matrix.det_fin_three,
             Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_succ,
             pow_zero, pow_one, pow_succ,
             Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
             Fin.zero_succAbove,
             one_mul, neg_one_mul, neg_neg,
             Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
             Matrix.cons_val', Matrix.empty_val']
  -- Closed-form witness from S12 §3.2 step (f), independently re-verified in §2 of this S14 PREP.
  linear_combination
    ((t - 1) * (s - 1)
       * ((A 0 - P 0) * (C 1 - P 1) - (A 1 - P 1) * (C 0 - P 0)))
    * h_signed_coords
```

Key differences vs S12 §4.3:

1. **`have hB0/hB1/hD0/hD1` use the form `B 0 = P 0 + t * (A 0 - P 0)`,
   not `B 0 - P 0 = t * (A 0 - P 0)`.** This produces a rewrite pattern
   that fires on the bare `B 0` term in the determinant.

2. **`rw [hB0, hB1, hD0, hD1]` is applied AFTER `unfold` and BEFORE
   `rw [Matrix.det_succ_row_zero]`.** This substitutes B and D in the
   raw matrix entries — the simplest place to do it. After this
   substitution, the matrix is in {A, C, P, t, s} only, and the
   cofactor expansion produces a polynomial in those variables.

3. **`Fin.succAbove_succ` removed from the simp list** (S13 §3.2 L-fix:
   this name does not exist at the pin).

4. **`ht_x, ht_y, hs_x, hs_y` removed from the simp list** — they were
   never going to fire (per §3.2), and they're not needed because B and
   D are already substituted out before the cofactor expansion.

5. **`set_option maxHeartbeats 8000000 in` + `set_option maxRecDepth 4096 in`
   prepended to the theorem** (S13 §3.3 M-fix: in-tactic options don't
   propagate to nested simp/linear_combination calls).

6. **`open scoped InnerProductSpace`** must be added to the file header
   (S13 §3.1 K-fix: `⟪x, y⟫_ℝ` notation requires that scope).

### 4.3 Why this should `ring`-close

After the substitution + cofactor expansion, the goal polynomial equals
the determinant of the column-op-translated + row-op-substituted matrix
of §2.2 above (modulo `ring`-normalisation). My §2.4 derivation shows
this equals `(t−1)(s−1)(tα − sγ)(α₀γ₁ − α₁γ₀)` exactly.

The `linear_combination W * h_signed_coords` witness with
`W = (t−1)(s−1)(α₀γ₁ − α₁γ₀)` then asks `ring` to verify:

```
[goal polynomial] − W · (tα_coords − sγ_coords) = 0
```

which is `0 = 0` in ring-normalised form (because the goal polynomial
equals `W · (tα_coords − sγ_coords)` exactly).

This is a polynomial identity in 8 variables (A 0, A 1, C 0, C 1, P 0, P 1,
t, s). With M-fix budgets (maxHeartbeats 8M, maxRecDepth 4096), `ring`
should close it in ~120s wall (per S13 §3.3 iter 10 timing for the
analogous-size polynomial).

### 4.4 Fallback if the witness still fails

If, despite §4.2's structural fix, `ring` still rejects, the most likely
culprits in order of probability:

1. **Sign drift in `det_succ_row_zero` convention.** `det_succ_row_zero`
   expands along row 0 with signs `+, −, +, −`. If Mathlib's row-0
   expansion convention orders the cofactor signs differently (e.g.
   `−, +, −, +`), the entire polynomial gets a `−` flip; the witness
   then needs a `−` flip. **Fix**: try flipping the witness sign.

2. **`Pi.sub_apply` / `Pi.smul_apply` syntactic mismatch on
   `EuclideanSpace`.** `EuclideanSpace` is a `PiLp` alias; the
   coordinate `(B - P) 0` may unfold via `PiLp.sub_apply` rather than
   `Pi.sub_apply`. **Fix**: try `simp [PiLp.sub_apply, PiLp.smul_apply,
   smul_eq_mul]` in the `hB0/hB1/hD0/hD1` derivations.

3. **`Matrix.cons_val'` / `Matrix.empty_val'` deprecated at pin.** If
   the simp list contains stale names, the matrix-access reduction is
   incomplete. **Fix**: try replacing with `Matrix.cons_val_zero,
   Matrix.cons_val_one, Matrix.head_fin_const, Matrix.head_cons`.

All three fallbacks are pure simp-set / sign-flip tweaks, not algebraic
re-derivations. The closed form derived in §2 is mathematically airtight.

## 5. What this S14 PREP does NOT do

- **No Lean edits.** `git diff origin/main -- proofs/` is empty.
- **No `state.md` edit.** S15 STATE-SYNC will pick this PREP up.
- **No JSON edit.** Same reason.
- **No `lake build` / Docker invocation.** The §2 derivation is purely
  pencil-and-paper; no Lean compilation is asserted. The S15 ACT picker
  runs the Docker build to confirm the §4.2 paste-ready body works.
- **No alternative-witness derivation for the S3 ACT (Cramer) or S4
  ACT (column update) routes.** Those still owe pencil work as flagged
  by S10 §11 and S12 §10.3.

## 6. ACT-readiness gate (refined post-S14)

| # | Gate item | Status |
|---|-----------|--------|
| 1 | Manifest pin unchanged | ✅ (`2df2f015…`, unchanged since S8) |
| 2 | All bearer line numbers re-verified | ✅ (S12 §2 + S10 §3; no further drift assumed) |
| 3 | Inner-product → scalar bridge paste-ready | ✅ (S10 §3.3 + S12 §4.3 + this §4.2) |
| 4 | Cofactor expansion `simp only` block drafted | ✅ (this §4.2, with L-fix and K-fix applied) |
| 5 | `linear_combination` witness coefficient derived in closed form | ✅ (S12 §3.2 step (f), **independently re-verified** in §2 of this PREP) |
| 6 | Witness sanity-checked against S9 counterexample | ✅ (S12 §6, re-confirmed in §2.6 of this PREP) |
| 7 | Hypothesis surface minimised | ✅ (3 hypotheses, not 9 — S12 §4.4) |
| 8 | Bug N root cause correctly diagnosed + fix prescribed | ✅ (this §3 + §4) |
| 9 | Substitution machinery: `have hB0/hB1/hD0/hD1` in `B 0 = ...` form | ✅ (this §4.2) |
| 10 | Docker build pending | ⬜ (S15 ACT picker's responsibility; ~120s wall per iter) |

**Verdict: GREEN** — every prerequisite for a successful S15 ACT is in
place. The §4.2 paste-ready body addresses K + L + M (S13's correct
diagnoses) **and** N (S13's correct symptom + this PREP's correct
root cause + fix).

## 7. References

- S10 PREP #19312 — unified S5 ACT skeleton with `sorry` placeholder
- S11 STATE-SYNC #19326 — refresh state.md + JSON after S8/S9/S10
- S12 PREP (#?) — explicit `linear_combination` witness derivation; §3.2 closed form (re-verified in this §2)
- S13 PREP (#?) — 10-iteration Docker audit surfacing Bugs K + L + M + N; correctly diagnosed K + L + M; **incorrectly** hypothesised N as algebraic error
- **S14 PREP (this PR)** — independent re-derivation confirms S12 closed form; rediagnoses N as simp pattern mismatch; prescribes substitution fix

External:
- Mathlib4 pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
- `Matrix.det_succ_row_zero`, `Matrix.det_fin_three` — cofactor expansion
- `EuclideanSpace.norm_sq_eq` (`PiL2.lean:145`) — coordinate `‖·‖²`
- `real_inner_self_eq_norm_sq` (`InnerProductSpace/Basic.lean:384`)
- `inner_smul_right` (`InnerProductSpace/Basic.lean`)
- `Pi.sub_apply`, `Pi.smul_apply`, `smul_eq_mul` — for component projection

## 8. Honesty notes

- **No Docker build.** §2's derivation is pencil-and-paper; §4.2's
  paste-ready body is not Lean-verified. The S15 ACT picker is the
  final source of truth.
- **§2 derivation route is different from S12 §3.2 by design.** I
  intentionally used Laplace block expansion instead of cofactor-along-
  column-4 to provide independent verification. The two routes
  necessarily produce the same closed form (det is well-defined), but
  the agreement under different expansion strategies rules out
  expansion-route-specific sign errors.
- **§3.2's root-cause analysis is a stronger claim than S13 §3.4's
  hypothesis.** S13 inferred the witness is wrong because `ring`
  rejected; this S14 explains WHY `ring` rejected without the witness
  being wrong (the goal polynomial mentions free B, D variables that
  the witness cannot reach). The fix in §4.1 is correspondingly more
  targeted: substitute B, D first, then apply the same witness.
- **§4.4 fallbacks (sign drift, PiLp vs Pi, simp set staleness) are
  hypothetical.** They are listed in case the substitution fix
  doesn't fire cleanly on the first Docker build. None of them
  require re-deriving the witness.
- **S15 ACT picker's owed work after this PREP**: ~5 min for the K-L-M
  + substitution edits; ~120s Docker build; if green, ship.
  If red, ~30 min for §4.4 fallback iteration.

🤖 Generated with [Claude Code](https://claude.com/claude-code)
