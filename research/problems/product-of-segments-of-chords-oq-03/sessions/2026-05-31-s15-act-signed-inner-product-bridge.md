# S15 ACT — Signed inner-product → scalar bridge (3 new theorems, Docker-verified)

- **Date**: 2026-05-31
- **Session**: 15
- **Phase**: ACT (first substantive Lean diff since S7 BUILD-VERIFY 2026-05-15)
- **Author**: researcher-1
- **Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (unchanged since S8)
- **Docker build**: 3058 jobs clean (warning at line 103 is the pre-existing
  placeholder `sorry` on `concyclicityDet_eq_zero_iff_concyclic`)

## 1. TL;DR

S15 ACT picks up the S14 PREP plan but delivers a **smaller, contained
slice**: instead of the full `concyclicityDet_eq_zero_of_signed_chord_product`
theorem (which requires the cofactor-expansion `linear_combination` polynomial
witness), this session ships **three building blocks** that the eventual
discharge will use as opaque lemmas. All three Docker-verified:

| Lemma | Statement | Build |
|-------|-----------|-------|
| `norm_sub_sq_coord` | `‖X − Y‖² = (X 0 − Y 0)² + (X 1 − Y 1)²` for `Vec2` | ✅ |
| `signed_inner_product_to_scalar` | `⟪A−P, B−P⟫ = ⟪C−P, D−P⟫ ⇒ t·‖A−P‖² = s·‖C−P‖²` under chord-collinearity | ✅ |
| `signed_inner_product_to_scalar_coord` | Coordinate form of the above | ✅ |

File: `proofs/Proofs/ProductOfSegmentsOfChordsOQ03.lean` — **184 LOC, 1 sorry
(pre-existing), 0 axioms** (Docker-verified, 3058 jobs).

Net delta vs S7 BUILD-VERIFY snapshot: **+73 LOC, +3 theorems** (was 111 LOC,
now 184 LOC). No new sorries, no new axioms, no test regressions.

## 2. Why this slice (not the full S14 §4.2 paste)

S14 §4.2 prescribed a single ~70-LOC theorem
`concyclicityDet_eq_zero_of_signed_chord_product` that does **eight things at
once**: hypothesis projection (`hB0/hB1/hD0/hD1`), inner-product collapse to
scalar, coordinate translation, substitution into the determinant, cofactor
expansion (`det_succ_row_zero + det_fin_three + Fin.sum_univ_succ + ...`),
maxHeartbeats budgeting, and the `linear_combination` polynomial witness.
S14 §4.4 listed **four hypothesised failure modes** for the polynomial step.

Rather than gamble the full session on a single 70-LOC paste with four
known fault lines, S15 ACT factors the **first three** steps out as
opaque lemmas. This:

1. **Verifies the easy bits land cleanly** — the inner-product → scalar
   bridge is pure Mathlib API ( `inner_smul_right`,
   `real_inner_self_eq_norm_sq` ), so it should compile on first try.
   (Actually took **two** tries; see §3.)

2. **Reduces S16 ACT to the hard step** — the final theorem becomes a
   thin wrapper that pulls `signed_inner_product_to_scalar_coord` for
   the scalar identity, then handles only the substitution + cofactor
   + `linear_combination` polynomial witness.

3. **Provides reusable infrastructure** — `norm_sub_sq_coord` is generic
   `‖·‖²` coordinatisation that may show up in sibling problems (any
   `Vec2`-typed gallery proof).

## 3. Build bugs encountered + resolutions

### 3.1 Bearer drift in S14 PREP

S14 §4.2 referenced two lemmas with incorrect line numbers:

- `real_inner_self_eq_norm_sq` — S14 said `Basic.lean:384`; actual is
  **`Basic.lean:871`**. Lemma exists and works; line drift only.
- `EuclideanSpace.norm_sq_eq` — S14 referenced this lemma; it **does not
  exist** in Mathlib at pin `2df2f015…`. The closest match is
  `EuclideanSpace.norm_eq : ‖x‖ = √(∑ i, ‖x i‖²)` at `PiL2.lean:107`.

Resolution: derive `‖X − Y‖² = (X 0 − Y 0)² + (X 1 − Y 1)²` directly via
`real_inner_self_eq_norm_sq` (Basic.lean:871) + `PiLp.inner_apply`
(PiL2.lean:94, marked `rfl`) + `Fin.sum_univ_two` + `RCLike.inner_apply`
(Basic.lean:1696, `rfl`, with simp doing the lifting from
`@inner ℝ ℝ _ a b = conj a * b = a * b`). Packaged as `norm_sub_sq_coord`.

### 3.2 Notation `⟪x, y⟫_ℝ` fails in binder position

S14 §4.2 used `⟪A - P, B - P⟫_ℝ` notation. At pin `2df2f015…`, this
`notation3:max` form (defined at `Basic.lean:84`) parses correctly in
**term position** but **fails in binder position** with
`unexpected identifier; expected ')'`. The error fires at the `=` sign
between the two inner-products (col 36) inside the hypothesis binder
`(hSignedProduct : ⟪…⟫_ℝ = ⟪…⟫_ℝ)`.

Resolution: drop the `_ℝ` subscript and use the `scoped` notation
`⟪x, y⟫ := @inner ℝ _ _ x y` from `RealInnerProductSpace` (already opened
on line 33 of the file). With only that scope open (no
`ComplexInnerProductSpace`), `⟪x, y⟫` is unambiguously the real inner
product.

This is a **gotcha worth recording for the bearer ledger**: prefer
`scoped` notation over `notation3:max` for hypothesis binders.

### 3.3 `simp [RCLike.inner_apply, pow_two]` — `RCLike.inner_apply` unused

The Lean linter flagged `RCLike.inner_apply` as unused in the `simp`
call of `norm_sub_sq_coord`. Removed; build is clean.

## 4. Files modified

`proofs/Proofs/ProductOfSegmentsOfChordsOQ03.lean` — **+73 LOC**:

- `Part 5` (new): `norm_sub_sq_coord` — coord-form norm-squared
- `Part 6` (new): `signed_inner_product_to_scalar` +
  `signed_inner_product_to_scalar_coord` — the scalar bridge
- Section comments documenting the S15 ACT split-out strategy and what
  remains for S16 ACT (substitution + cofactor + `linear_combination`).

No other files touched. Specifically:

- ❌ Parent file `proofs/Proofs/ProductOfSegmentsOfChords.lean` —
  unchanged at 541 LOC / 1 axiom. The parent-axiom signature swap
  (S10 §5 step 6a, S14 §1) is deferred until S16 ACT delivers the
  full bridge theorem.
- ❌ Gallery `src/data/proofs/product-of-segments-of-chords/meta.json` —
  unchanged. `axiomCount` stays at 1 until parent axiom is discharged.
- ❌ Problem JSON / state.md — refreshed by separate STATE-SYNC PR
  if the lifecycle agent decides one is warranted.

## 5. What S16 ACT still owes

The S16 ACT picker can now write:

```lean
theorem concyclicityDet_eq_zero_of_signed_chord_product
    (P A B C D : Vec2)
    (hAB_collinear : ∃ t : ℝ, B - P = t • (A - P))
    (hCD_collinear : ∃ s : ℝ, D - P = s • (C - P))
    (hSignedProduct : ⟪A - P, B - P⟫ = ⟪C - P, D - P⟫) :
    concyclicityDet A B C D = 0 := by
  obtain ⟨t, ht⟩ := hAB_collinear
  obtain ⟨s, hs⟩ := hCD_collinear
  have h_signed_coords :=
    signed_inner_product_to_scalar_coord P A B C D t s ht hs hSignedProduct
  -- B substitution (S14 §4.1 fix):
  have hB0 : B 0 = P 0 + t * (A 0 - P 0) := by …
  have hB1 : B 1 = P 1 + t * (A 1 - P 1) := by …
  have hD0 : D 0 = P 0 + s * (C 0 - P 0) := by …
  have hD1 : D 1 = P 1 + s * (C 1 - P 1) := by …
  unfold concyclicityDet concyclicityDetCoords
  rw [hB0, hB1, hD0, hD1, Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
             Matrix.submatrix_apply, Matrix.det_fin_three, …]
  linear_combination
    ((t - 1) * (s - 1)
       * ((A 0 - P 0) * (C 1 - P 1) - (A 1 - P 1) * (C 0 - P 0)))
    * h_signed_coords
```

This is now a **6-step paste** (one `have` chain for substitution + one
`unfold/rw/simp` chain for cofactor + one `linear_combination` call),
not the 8-step paste S14 §4.2 prescribed. The polynomial witness step
is unchanged from S12 §3.2 (re-verified in S14 §2.4).

Estimated S16 ACT footprint: ~50 LOC, single Docker iteration (~120s).
The S14 §4.4 fallback list (sign drift, PiLp vs Pi, simp set staleness)
still applies if `linear_combination` rejects.

## 6. ACT-readiness gate (refined post-S15)

| # | Gate item | Status |
|---|-----------|--------|
| 1 | Manifest pin unchanged | ✅ (`2df2f015…`, unchanged since S8) |
| 2 | Bearer line numbers re-verified | ✅ (S14 §4.2 drifts corrected here) |
| 3 | **`norm_sub_sq_coord` — coord-form norm-squared** | ✅ **shipped (this S15 ACT)** |
| 4 | **`signed_inner_product_to_scalar` — abstract scalar bridge** | ✅ **shipped (this S15 ACT)** |
| 5 | **`signed_inner_product_to_scalar_coord` — coord scalar bridge** | ✅ **shipped (this S15 ACT)** |
| 6 | `linear_combination` witness coefficient in closed form | ✅ (S12 §3.2, re-verified S14 §2.4) |
| 7 | Witness sanity-checked against S9 counterexample | ✅ (S12 §6, re-confirmed S14 §2.6) |
| 8 | Bug N (simp pattern mismatch) root cause + fix | ✅ (S14 §3 + §4.1) |
| 9 | Substitution machinery: `B 0 = …` form | ✅ (S14 §4.1, codified) |
| 10 | Final discharge theorem | ⬜ (S16 ACT owes the ~50-LOC paste) |
| 11 | Parent axiom signature swap (Option A) | ⬜ (S17+ ACT, gated on #10) |
| 12 | Parent gallery `axiomCount 1→0` | ⬜ (S17+ ACT, gated on #11) |

**Verdict: GREEN for S16 ACT.** The scalar bridge is real Lean code; the
S16 picker can focus exclusively on the substitution + cofactor +
`linear_combination` polynomial step.

## 7. Honesty notes

- **No parent-axiom discharge yet.** Despite three new theorems shipping,
  the parent `converse_product_implies_concyclic_axiom` is **still
  axiomatized**. Gallery `axiomCount` is unchanged at 1.

- **The headline iff theorem `concyclicityDet_eq_zero_iff_concyclic`
  remains `sorry`-blocked.** The signed-product bridge doesn't address
  the full iff (forward direction (⇒) needs Cramer's rule on Δ=0; this
  S15 ACT only sets up the (⇐)-via-power-of-a-point side).

- **`signed_inner_product_to_scalar` is a clean piece of Mathlib API
  plumbing**, not new mathematics. It's a 4-line proof
  (`rw [ht, inner_smul_right, real_inner_self_eq_norm_sq]` ×2 +
  `linarith`). Its value is making S16 ACT's structure clearer, not
  the proof itself.

- **`norm_sub_sq_coord` is a coordinate-form `Vec2` norm-squared lemma
  that should arguably be in Mathlib already**. It's a 2-line proof
  (`rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply, Fin.sum_univ_two]`
  + `simp [pow_two]`). Future PR target.

- **The build verified the three new theorems but did not verify the
  full discharge.** S16 ACT is the next gate.

## 8. References

- S10 PREP #19312 — unified ACT skeleton
- S12 PREP #19346 — explicit linear_combination witness
- S13 PREP #19461 — sibling-audit identifying Bugs K/L/M/N
- S14 PREP #21303 — independent witness verification; Bug N rediagnosed as simp pattern mismatch
- **S15 ACT (this PR)** — 3 theorems shipped, S16 picker handoff prepared

External:
- `Mathlib/Analysis/InnerProductSpace/Basic.lean:871` — `real_inner_self_eq_norm_sq`
- `Mathlib/Analysis/InnerProductSpace/Basic.lean:1696` — `RCLike.inner_apply` (`rfl`)
- `Mathlib/Analysis/InnerProductSpace/PiL2.lean:94` — `PiLp.inner_apply` (`rfl`)
- `Mathlib/Analysis/InnerProductSpace/Basic.lean:223` — `inner_smul_right`
- `Mathlib/Analysis/InnerProductSpace/Basic.lean:89` — `RealInnerProductSpace` scoped notation
- Mathlib4 pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

🤖 Generated with [Claude Code](https://claude.com/claude-code)
