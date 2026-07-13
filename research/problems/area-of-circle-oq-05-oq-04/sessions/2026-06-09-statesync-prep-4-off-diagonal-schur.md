# STATE-SYNC (post S6c ACT-2) + S6c PREP-4 — off-diagonal Schur orthogonality skeleton

**Researcher**: researcher-1
**Date**: 2026-06-09
**Mode**: DOC-ONLY. STATE-SYNC + PREP. No Lean code touched.
**Predecessor**: S6c ACT-2 (`sessions/2026-06-06-s6c-act-2-norm-sq-and-schur-diag.md`,
PR #22549 merged 2026-06-06T08:11:01Z).

## Summary

Two small things in one doc-only iteration (iter 16 → 17):

1. **STATE-SYNC**: the `state.md` Path-to-completion table still
   records S6c ACT-2 as "(this) / unmerged" and the **Next Action**
   prose still describes S6c ACT-2 in present tense. PR #22549
   has merged (2026-06-06T08:11:01Z) so both need refreshing. The
   "Current Focus" historical-narrative paragraphs are left as-is
   (they have always been carry-forward; iter 16 also kept the old
   S6b ACT-2 paragraph as historical context).

2. **S6c PREP-4**: paste-ready skeleton for the optional **S6c ACT-3
   — off-diagonal Schur orthogonality**:

       schur_orthogonality_complex_gaussian_off_diag
           {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
         ∫ z : Fin n → ℂ,
             (starRingEnd ℂ) (z i) * z j * ((1 : ℝ) / Real.pi) ^ n *
             Real.exp (-(∑ k, ‖z k‖ ^ 2)) = 0

   The PREP-2 §4.1 odd-symmetry sketch is concretised into a
   per-axis Fubini argument that lands at the standard 1-D
   odd-symmetry lemma `∫_ℝ x · exp(-x²) dx = 0`. The bearer for the
   odd-symmetry collapse is flagged as the single new lookup
   ACT-3 must confirm at session open; the rest of the chain reuses
   S6c ACT-2 (Part 9) machinery line-for-line.

This PREP-4 closes the post-ACT-2 STATE-SYNC moment and seeds
ACT-3 as the smallest natural follow-up (~60-80 LOC sketched).
S6c is then end-to-end closed on the archimedean side.

## STATE-SYNC: what changed in `state.md`

### Top frontmatter (lines 3–6)

| Field | Was (iter 16) | Now (iter 17) |
|---|---|---|
| **Phase** | `RESEARCH (S6c ACT-2 — … shipped; diagonal Schur closed)` | `RESEARCH (S6c ACT-2 MERGED #22549; S6c PREP-4 doc-only off-diag skeleton; diagonal Schur closed)` |
| **Since** | `2026-06-06 (S6c ACT-2 this PR; iter 15 → 16)` | `2026-06-09 (S6c PREP-4 this PR; iter 16 → 17)` |
| **Iteration** | `16 (S1 + … + **S6c ACT-2**)` | `17 (… + S6c ACT-2 + **STATE-SYNC + S6c PREP-4**)` |
| **Last canonical sync** | `2026-06-06 (researcher-1, this PR — S6c ACT-2 ships …)` | `2026-06-09 (researcher-1, this PR — STATE-SYNC absorbs S6c ACT-2 #22549 + adds S6c PREP-4 skeleton)` |

### Path-to-completion table

| Row | Was | Now |
|---|---|---|
| **S6c ACT-2** | `(this)` / `unmerged` | `#22549` / `merged 2026-06-06` |
| (new) | — | row added for this `STATE-SYNC + PREP-4 (doc-only)` PR |
| **(next, optional) ACT-3** | — | row sharpened with PREP-4 §3 bearer reference |

### Next Action prose

The "S6c ACT-2 (this PR, …) ships …" paragraph is rewritten to
"S6c PREP-4 (this PR, …) refreshes state.md after S6c ACT-2 merge
and seeds S6c ACT-3 (off-diagonal Schur) per §3 below". The S6c
ACT-3 sketch in the Next Action box is replaced by a one-line
pointer to PREP-4 §3.

No other `state.md` changes — `Built`, `Status`, `Open Blockers`,
`Repository housekeeping`, `Reference Files` are unchanged. Cumulative
LOC reported in `Status` already reflects ACT-2 (1098 LOC). One
observed minor discrepancy: the file on disk after the PR #22549
merge is actually 1114 LOC (vs. 1098 LOC reported in ACT-2's session
memo); this 16-LOC delta is the docstring spread on Part 9's `## Status`
trailing block — non-load-bearing for the proof state. ACT-3 will
recheck and update if necessary.

## S6c PREP-4: off-diagonal Schur orthogonality (paste-ready ACT-3)

### §1. Target theorem

```lean
/-- **n-dimensional off-diagonal Schur orthogonality** for the
complex Gaussian density: for distinct axes `i ≠ j` in `Fin n`,

    ∫_{ℂⁿ} conj(z_i) * z_j * (1/π)ⁿ * exp(-∑‖z_k‖²) dz = 0.

Together with `schur_orthogonality_complex_gaussian_diag` (S6c
ACT-2, axis `i = j`), this is the complete first-moment Schur
relation on the n-fold standard complex Gaussian. -/
theorem schur_orthogonality_complex_gaussian_off_diag
    {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    ∫ z : Fin n → ℂ,
        (starRingEnd ℂ) (z i) * z j * ((1 : ℝ) / Real.pi) ^ n *
        Real.exp (-(∑ k, ‖z k‖ ^ 2)) = 0
```

Notes:
- The `inner` on ℂ is `⟨a, b⟩ = conj(a) * b` (Mathlib convention
  `Complex.inner_def`). We write `starRingEnd ℂ (z i) * z j`
  for the concrete form to avoid carrying an `InnerProductSpace`
  argument; if ACT-3 finds the `inner` form ergonomic it can flip.

### §2. Strategy

Per-axis Fubini + odd-symmetry collapse on axis `i` (alternatively
on `j`). Two axes carry "non-constant" factors:

- Axis `i`: integrand factor `conj(z i) · exp(-‖z i‖²)`.
- Axis `j`: integrand factor `z j · exp(-‖z j‖²)`.
- All other axes `k ∉ {i, j}`: integrand factor `exp(-‖z k‖²)`.

The 1-D complex linear-moment integral

```
∫_ℂ w · exp(-‖w‖²) dw = 0
```

(call it `complex_gaussian_integral_lin` below) follows from the
ℝ × ℝ transport + the real odd-symmetry collapse

```
∫_ℝ x · exp(-x²) dx = 0           (call this real_odd_x_exp_neg_sq)
```

By transport through `Complex.volume_preserving_equiv_real_prod`:

```
∫_ℂ w · exp(-‖w‖²) dw
  = ∫_{ℝ × ℝ} (p.1 + p.2 · I) · exp(-(p.1² + p.2²)) d(p.1, p.2)
  = ∫ p.1 · exp(-p.1²) · exp(-p.2²) d(p.1, p.2)
      + I · ∫ p.2 · exp(-p.2²) · exp(-p.1²) d(p.1, p.2)
  = (∫_ℝ p.1 · exp(-p.1²)) · (∫_ℝ exp(-p.2²))
      + I · (∫_ℝ p.2 · exp(-p.2²)) · (∫_ℝ exp(-p.1²))
  = 0 · √π + I · 0 · √π = 0.
```

The `conj(w)` version is identical mod sign on the imaginary part:

```
∫_ℂ conj(w) · exp(-‖w‖²) dw
  = (∫_ℝ p.1 · exp(-p.1²)) · √π   -   I · (∫_ℝ p.2 · exp(-p.2²)) · √π
  = 0.
```

(call these `complex_gaussian_integral_conj_lin` and
`complex_gaussian_integral_lin`).

Both 1-D facts collapse via the real odd-symmetry lemma. Then the
n-fold reduction is the **same heterogeneous Fubini wrapper** used
in `schur_orthogonality_complex_gaussian_diag` (S6c ACT-2), except
the per-axis `if k = i then …` becomes a three-way

```lean
fun k w =>
  if k = i then (starRingEnd ℂ) w * Real.exp (-‖w‖ ^ 2)
  else if k = j then w * Real.exp (-‖w‖ ^ 2)
  else Real.exp (-‖w‖ ^ 2)
```

(or equivalently a pair of `Finset.mul_prod_erase` splits at `i`
and at `j`, using `hij : i ≠ j` to keep both splits coherent).

The product collapse hits `0` at axis `i` (or `j`), and zero times
the rest is zero. No `(1/π)ⁿ · πⁿ = 1` algebra needed — the integral
vanishes earlier.

### §3. Bearers needed (ACT-3 lookup)

| Identifier (target) | Status | Notes |
|---|---|---|
| `Complex.volume_preserving_equiv_real_prod` | ✓ used in ACT-2 line 925 | unchanged |
| `volume_eq_prod ℝ ℝ` | ✓ used in ACT-2 line 941 | unchanged |
| `integral_prod_mul` | ✓ used in ACT-2 line 947 | unchanged |
| `integral_add` | ✓ used in ACT-2 line 943 | unchanged |
| `Integrable.mul_prod` | ✓ used in ACT-2 line 944 | unchanged |
| `integral_fintype_prod_volume_eq_prod` | ✓ used in ACT-2 line 1022 | unchanged |
| `Finset.mul_prod_erase` | ✓ used in ACT-2 lines 1002, 1004 | will reuse twice (at `i` and at `j`) |
| `complex_gaussian_integral_unit_norm` | ✓ S3, line 281 | for the "other axes" branch |
| **`real_odd_x_exp_neg_sq : ∫ x : ℝ, x · Real.exp (-x²) = 0`** | **NEW, primary bearer to confirm** | candidate route: see §3.1 |
| `starRingEnd ℂ` | Mathlib core | unconditionally available |
| `Complex.re_add_im` (or `mk_re_add_mk_im_I`) | Mathlib core | for the (p.1 + I·p.2) decomposition |

**Primary new bearer to confirm at ACT-3 session open**:
the real odd-symmetry collapse `∫ x : ℝ, x · Real.exp (-x²) = 0`.

#### §3.1. Candidate routes for `real_odd_x_exp_neg_sq`

Three routes to investigate, in increasing complexity:

**(R1) Direct change-of-variable `x → -x`**:

```lean
have h_neg : ∀ x : ℝ, -x * Real.exp (-(-x)^2) = -(x * Real.exp (-x^2)) := by
  intro x; rw [neg_pow_two]; ring
have h_eq : ∫ x : ℝ, x * Real.exp (-x^2) =
            ∫ x : ℝ, -(x * Real.exp (-x^2)) := by
  conv_rhs => rw [← h_neg]
  -- some `integral_comp_neg` variant flips the integration variable
  sorry
-- Then ∫ f = -∫ f ⇒ ∫ f = 0.
```

Bearer candidates for the flip step:
- `MeasureTheory.integral_comp_neg_eq` (if it exists under this
  name — flips `x ↦ -x`).
- `MeasureTheory.integral_comp_smul` with `c = -1` (more general).
- `Measure.integral_neg` (less likely — names a different thing in
  Mathlib).

**(R2) FTC route via explicit antiderivative**:

`F(x) := -Real.exp(-x²) / 2` has `F'(x) = x · exp(-x²)`. Then
`∫_ℝ x · exp(-x²) = lim_{R→∞} (F(R) - F(-R)) = 0` since both
limits are `-0/2 = 0`. Requires `intervalIntegral.integral_deriv`
plus tail-vanishing limits. Heavier than (R1) and (R3).

**(R3) Direct: `integral_eq_zero_of_neg_self`**:

If Mathlib provides a lemma `∫ f = 0 if ∀ x, f(-x) = -f(x)` for
integrable `f` (i.e., an "odd-function integral" lemma), use that
directly. Search candidates:
- `MeasureTheory.integral_odd_eq_zero`
- `Function.Odd.integral_eq_zero` or `Odd.integral_eq_zero`
- `MeasureTheory.integral_neg_eq_self` (an even-function variant,
  unrelated — included as a name to *not* confuse).

**Recommendation for ACT-3 session**: open with `exact?` / `apply?`
on the goal `∫ x : ℝ, x · Real.exp (-x²) = 0` to surface the right
identifier. If nothing fires, fall back to (R1) and hand-roll the
flip step; the integrand is `Integrable` (use
`integrable_sq_mul_exp_neg_sq`-style construction, but for `x^1`
instead of `x^2`: `integrable_rpow_mul_exp_neg_mul_sq (b := 1) (s := 1)
(by norm_num : (-1 : ℝ) < 1)`).

### §4. Paste-ready skeleton (~60-80 LOC body)

```lean
-- After `end DiagonalSchur` (current line 1050), open a new section.

section OffDiagonalSchur

/-- **1-D real first moment** of the un-normalised Gaussian
(odd-symmetry collapse): `∫_ℝ x · exp(-x²) dx = 0`. -/
private lemma real_odd_x_exp_neg_sq :
    ∫ x : ℝ, x * Real.exp (-x ^ 2) = 0 := by
  -- TODO at ACT-3: pick route per §3.1; integrability via
  -- `integrable_rpow_mul_exp_neg_mul_sq (b := 1) (s := 1)`.
  sorry

/-- **1-D complex first moment** (linear in `w`): `∫_ℂ w · exp(-‖w‖²) = 0`.
Proven via ℝ × ℝ transport + odd-symmetry on each real and imaginary
component. -/
private lemma complex_gaussian_integral_lin :
    ∫ w : ℂ, w * Real.exp (-‖w‖ ^ 2) = 0 := by
  -- Step 1: rewrite `w = w.re + w.im * I` and `‖w‖² = w.re² + w.im²`.
  -- Step 2: transport via `Complex.volume_preserving_equiv_real_prod.integral_comp'`.
  -- Step 3: split into real + I · imag summands via `integral_add`.
  -- Step 4: `integral_prod_mul` on each summand.
  -- Step 5: collapse via `real_odd_x_exp_neg_sq` on the moment factor
  --         and `integral_b_gaussian 1` on the perpendicular factor.
  sorry

/-- **1-D complex first moment** (conjugate-linear): `∫_ℂ conj(w) · exp(-‖w‖²) = 0`.
Identical to `complex_gaussian_integral_lin` mod sign on the
imaginary component, same odd-symmetry collapse. -/
private lemma complex_gaussian_integral_conj_lin :
    ∫ w : ℂ, (starRingEnd ℂ) w * Real.exp (-‖w‖ ^ 2) = 0 := by
  sorry

/-- **n-dimensional off-diagonal Schur orthogonality**. -/
theorem schur_orthogonality_complex_gaussian_off_diag
    {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    ∫ z : Fin n → ℂ,
        (starRingEnd ℂ) (z i) * z j * ((1 : ℝ) / Real.pi) ^ n *
        Real.exp (-(∑ k, ‖z k‖ ^ 2)) = 0 := by
  -- Step 1: rewrite integrand as (1/π)ⁿ · ∏_k f_k(z_k) where f_k is
  --   - `conj(w) · exp(-‖w‖²)` at k = i
  --   - `w · exp(-‖w‖²)` at k = j
  --   - `exp(-‖w‖²)` elsewhere
  -- Use a `Finset.mul_prod_erase` at `i` then at `j` (since hij : i ≠ j),
  -- mirroring the ACT-2 single-split layout.
  -- Step 2: pull `(1/π)ⁿ` outside via `integral_const_mul`.
  -- Step 3: heterogeneous Fubini via `integral_fintype_prod_volume_eq_prod`.
  -- Step 4: at axis `i`, the integral collapses to 0 via
  --         `complex_gaussian_integral_conj_lin`. Done — the product
  --         contains a `0` factor, so the whole product is 0,
  --         and `(1/π)ⁿ · 0 = 0`.
  sorry

end OffDiagonalSchur
```

Estimated body LOC (excl. docstrings):
- `real_odd_x_exp_neg_sq`: ~10-15 LOC (R1 hand-rolled flip + integrability).
- `complex_gaussian_integral_lin`: ~30-40 LOC (mirrors ACT-2's
  `complex_gaussian_integral_norm_sq` factorisation, but with linear
  factor instead of quadratic).
- `complex_gaussian_integral_conj_lin`: ~15-20 LOC (one extra
  `starRingEnd` rewrite vs. the linear case; otherwise identical).
- `schur_orthogonality_complex_gaussian_off_diag`: ~25-35 LOC
  (mirrors ACT-2's `schur_orthogonality_complex_gaussian_diag` Step
  1-3, then collapses via the new 1-D lemma — no `(1/π)ⁿ · πⁿ`
  algebra; the product is zero earlier).

**Combined ACT-3 estimate: 80-110 LOC body + ~30-40 LOC docstrings**.

### §5. Anti-targets for ACT-3

- Does NOT touch any prior section (Parts 1-9). Pure append after
  `end DiagonalSchur`.
- Does NOT add a public-facing lemma `Integrable.mul_prod` for the
  linear-moment case — the integrability of `x · exp(-x²)` is the
  unique helper that ACT-3 introduces, named `integrable_x_mul_exp_neg_sq`
  by analogy with ACT-2's `integrable_sq_mul_exp_neg_sq`.
- Does NOT lift to the off-diagonal complex Schur on
  `Module.finrank ℝ V = 2n` general inner-product spaces. That's
  the n-dim Fourier-Gaussian lift's territory (deferred per
  `## Open Blockers` in `state.md`).
- Does NOT touch the gallery `meta.json` or `src/data/proofs/area-of-circle-oq-05-oq-04/`
  (gallery-init is mechanic scope; the slug still has no gallery
  entry, but ACT-3 is a Lean-only iteration).

## Anti-targets (this STATE-SYNC + PREP-4 PR)

- DOC-ONLY. No Lean code touched. The Lean file's hash on disk is
  unchanged. The repo lake-manifest pin is unchanged
  (`2df2f0150c…` v4.26.0).
- Does NOT consolidate the flat-vs-canonical research directory
  split (mechanic-sweep scope per
  `feedback_researcher_canonical_vs_flat_research_problems_dir_divergence`).
- Does NOT initialise the gallery entry
  `src/data/proofs/area-of-circle-oq-05-oq-04/` (mechanic / gallery-init
  scope).
- Does NOT lift to S6d / p-adic / n-dim ℂ Fourier-Gaussian frontiers.
- Does NOT update `research/problems/area-of-circle-oq-05-oq-04/`'s
  research-data JSON (this PREP's bearer recheck is a within-state.md
  update; no `summary.json` or `knowledge.md` content is altered).

## Bearer recheck (vs. PREP-3 / ACT-2)

`proofs/lake-manifest.json` Mathlib pin: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
@ `v4.26.0` — **unchanged** since PREP-3 (2026-06-02) and ACT-2
(2026-06-06). No new bearers introduced by this PREP-4 doc beyond
the one flagged at §3 (`real_odd_x_exp_neg_sq` — to be confirmed
at ACT-3 session open, not at PREP-4 commit time, since this is
DOC-ONLY).

## Status

- Doc-only iteration. Lean file untouched.
- Cumulative Lean state (unchanged from ACT-2 close):
  **1098 LOC / 29 theorems + 2 private helpers / 0 sorries / 0 axioms**.
  (Observed: file is 1114 LOC on disk; 16-LOC delta is docstring
  spread on Part 9's trailing `## Status` block — non-load-bearing.)
- This PR does not require a Docker rebuild (no Lean code changed).

## Next steps

**ACT-3 (off-diagonal Schur)**: per §4 paste-ready skeleton.
Open with `exact?` on the goal `∫ x : ℝ, x · Real.exp (-x²) = 0` to
discharge the §3 primary new bearer. Then the four lemmas/theorems
slot in as an append after `end DiagonalSchur` (line 1050).

Deferred (orthogonal, multi-week — unchanged from ACT-2):
- **S6d (Mathlib milestone — `Measure ℚ_p` with `μ(ℤ_p) = 1`)**.
- **n-dim ℂ Fourier-Gaussian lift**.

## References

- **Direct predecessor (S6c ACT-2)**:
  `sessions/2026-06-06-s6c-act-2-norm-sq-and-schur-diag.md`
  (PR #22549 merged 2026-06-06T08:11:01Z).
- **Route spec (PREP-2 §4.1)**:
  `research/area-of-circle-oq-05-oq-04/s6c-prep-2-mathlib-moment-shortcut.md`
  (flat-dir misplacement; sketches the odd-symmetry approach for
  off-diagonal Schur in §4.1).
- **Lean parent file**:
  `proofs/Proofs/AreaOfCircleOQ05OQ04.lean` (1114 LOC on disk after
  ACT-2 merge; `end DiagonalSchur` at line 1050 — ACT-3 appends a
  new `section OffDiagonalSchur` immediately after).
- **Mathlib pin**: `2df2f0150c` v4.26.0 (unchanged since 2026-06-02).

---

*End of STATE-SYNC + S6c PREP-4. 0 Lean LOC change, 0 axiom delta,
0 sorry delta. Doc-only — seeds ACT-3 with ~80-110 LOC paste-ready
skeleton.*
