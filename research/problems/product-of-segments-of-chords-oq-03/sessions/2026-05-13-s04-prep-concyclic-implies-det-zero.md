# S4 PREP — `concyclic → Δ = 0` direction (doc-only)

**Date**: 2026-05-13
**Researcher**: researcher-12
**Phase**: PREP (orientation for the *(⇐) direction* of
`concyclicityDet_eq_zero_iff_concyclic` in
`proofs/Proofs/ProductOfSegmentsOfChordsOQ03.lean`, downstream of
S2 SCAFFOLD #18380 (merged) and orthogonal to S3 PREP #18466
(in-flight, Cramer (⇒) direction)).
**Type**: Doc-only design memo. No edits to Lean files, `state.md`,
`problem.md`, `knowledge.md`, the in-flight PR #18466 `sessions/`
note, gallery `meta.json`, or research JSON.

## 0. Why this PREP

`state.md` § "Subsequent Plan" table:

| Session | Goal | Lines | Sorries |
|---------|------|-------|---------|
| S3 | (⇐) `Δ = 0 ∧ non-collinear → ∃ O r, ...` via Cramer. | ~80 | -0 +0 (close 1, open 1) |
| **S4** | **(⇒) `concyclic → Δ = 0` via row reduction.** | **~30** | **-1** |
| S5 | Bridge: `chord_product_equal → Δ = 0`. | ~50 | -1 |

S3 PREP #18466 (researcher-9, opened 2026-05-13 02:19 UTC) designs
the harder direction (Cramer's rule constructing center+radius from
the determinant condition). **This PREP designs the easier S4
direction**: from "there exists a circle through P₁..P₄" to
"`concyclicityDet P₁ P₂ P₃ P₄ = 0`".

The S4 direction is ~30 LOC by `state.md`'s estimate and is
mathematically routine: the determinant has a linear-dependent
column whenever the implicit circle equation
`x² + y² + Dx + Ey + F = 0` is satisfied by all four points.

This PREP is orthogonal to S3 PREP #18466:
- PR #18466 sessions/ doc: `2026-05-13-s3-prep-cramer-design.md`
- This PREP sessions/ doc: `2026-05-13-s04-prep-concyclic-implies-det-zero.md`
- Different theorem, different proof technique, no Lean overlap.

## 1. Goal of the eventual S4 ACT

After S3 ACT lands (closing the main `sorry` and opening a new sorry
on the (⇐) `concyclic → Δ = 0` half — per S3 PREP § "Status"), S4
ACT discharges that new sorry. Two structural choices for the S4
ACT:

### 1.1 Choice A — `iff` packaging (recommended)

Discharge S3's "(⇐) sorry" as part of the original `iff` theorem.
S3 ACT will leave the `sorry` only on this direction; S4 closes it
inline.

### 1.2 Choice B — separate auxiliary theorem

Add a standalone lemma:

```lean
theorem concyclicityDet_eq_zero_of_concyclic
    (P₁ P₂ P₃ P₄ : Vec2)
    (h : ∃ (O : Vec2) (r : ℝ), 0 < r ∧
      ‖P₁ - O‖ = r ∧ ‖P₂ - O‖ = r ∧
      ‖P₃ - O‖ = r ∧ ‖P₄ - O‖ = r) :
    concyclicityDet P₁ P₂ P₃ P₄ = 0
```

Then S3's `iff` proof invokes this lemma in the (⇐) direction.

**Recommendation**: Choice A unless S3 ACT explicitly factors S4 out
into a helper.

## 2. The algebraic identity

If P₁..P₄ lie on a common circle with center `O = (O₁, O₂)` and
radius `r`, then for each i,

```
‖Pᵢ - O‖² = r²
⇔ (Pᵢ₁ - O₁)² + (Pᵢ₂ - O₂)² = r²
⇔ Pᵢ₁² + Pᵢ₂² - 2·O₁·Pᵢ₁ - 2·O₂·Pᵢ₂ + (O₁² + O₂² - r²) = 0.
```

Set `D := -2·O₁`, `E := -2·O₂`, `F := O₁² + O₂² - r²`. Then for all
four points:

```
Pᵢ₁² + Pᵢ₂² + D·Pᵢ₁ + E·Pᵢ₂ + F = 0   ……(★)
```

In matrix form, this says **column 0 of `concyclicityDetCoords`'s
underlying matrix is the linear combination
`-D · col 1 - E · col 2 - F · col 3`**. Determinants of matrices
with linearly-dependent columns are zero.

## 3. Two implementation paths in Lean

### 3.1 Path A — column operations (clean, ~25 LOC)

Use `Matrix.det_updateCol_add_smul_self` to absorb columns 1, 2, 3
into column 0 with multipliers `D`, `E`, `F`. After three
operations, column 0 becomes the all-zero column (by (★)). Then
`Matrix.det_eq_zero_of_column_eq_zero` finishes.

Sketch:

```lean
theorem concyclicityDet_eq_zero_of_concyclic
    (P₁ P₂ P₃ P₄ : Vec2)
    (h : ∃ (O : Vec2) (r : ℝ), 0 < r ∧
      ‖P₁ - O‖ = r ∧ ‖P₂ - O‖ = r ∧
      ‖P₃ - O‖ = r ∧ ‖P₄ - O‖ = r) :
    concyclicityDet P₁ P₂ P₃ P₄ = 0 := by
  obtain ⟨O, r, hr, h₁, h₂, h₃, h₄⟩ := h
  set D := -2 * O 0
  set E := -2 * O 1
  set F := (O 0)^2 + (O 1)^2 - r^2
  -- Auxiliary equality (★) for each Pᵢ:
  have hPi : ∀ i ∈ ({P₁, P₂, P₃, P₄} : Set Vec2),
      (i 0)^2 + (i 1)^2 + D * i 0 + E * i 1 + F = 0 := by
    intro i hi
    -- Unfold ‖Pᵢ - O‖ = r, expand the norm via EuclideanSpace.norm_eq + Fin.sum_univ_two,
    -- substitute hri : ‖Pᵢ - O‖ = r, then ring.
    sorry
  -- Now perform column reduction on the 4×4 matrix and finish.
  unfold concyclicityDet concyclicityDetCoords
  -- Apply det_updateCol_add_smul_self ×3, then det_eq_zero_of_column_eq_zero.
  sorry
```

LOC budget: ~25 LOC body + ~10 LOC for the (★) helper.

### 3.2 Path B — direct expansion (brute force, ~15 LOC)

Match the style of S2's numerical examples (lines 74–85): unfold
`concyclicityDetCoords`, apply `simp [Matrix.det_fin_four]`, then
substitute `‖Pᵢ - O‖² = r²` four times and finish with `ring`.

Sketch:

```lean
theorem concyclicityDet_eq_zero_of_concyclic
    (P₁ P₂ P₃ P₄ : Vec2)
    (h : ∃ (O : Vec2) (r : ℝ), 0 < r ∧
      ‖P₁ - O‖ = r ∧ ‖P₂ - O‖ = r ∧
      ‖P₃ - O‖ = r ∧ ‖P₄ - O‖ = r) :
    concyclicityDet P₁ P₂ P₃ P₄ = 0 := by
  obtain ⟨O, r, hr, h₁, h₂, h₃, h₄⟩ := h
  -- Convert each ‖Pᵢ - O‖ = r into the squared form:
  -- (Pᵢ₁ - O₁)² + (Pᵢ₂ - O₂)² = r²
  have hPi : ∀ Pi ∈ [P₁, P₂, P₃, P₄], (Pi 0 - O 0)^2 + (Pi 1 - O 1)^2 = r^2 := by
    intro Pi hPi_mem
    rcases hPi_mem with rfl | rfl | rfl | rfl | _ <;>
      · rw [show (_ : ℝ) = ‖_‖ from (EuclideanSpace.norm_eq _).symm,
            Fin.sum_univ_two, h₁]  -- placeholder; adapt per hypothesis
        ring
  -- Direct expansion:
  unfold concyclicityDet concyclicityDetCoords
  simp [Matrix.det_fin_four]
  -- Use hPi (specialised four times) to substitute Pᵢ₁² + Pᵢ₂² = expanded form
  nlinarith [hPi P₁ (by simp), hPi P₂ (by simp), hPi P₃ (by simp), hPi P₄ (by simp)]
```

LOC budget: ~15-20 LOC body.

### 3.3 Recommendation

**Path B (direct expansion)** is the natural style for this file —
matches S2's `Matrix.det_fin_four + ring` discipline. Path A is
"more elegant" but the `det_updateCol_add_smul_self` chain takes 3
applications + careful tracking of column indices via `Fin 4`,
which can balloon LOC.

If `nlinarith` fails on the final step (likely if the 4×4
determinant expansion is high-degree), fall back to Path A or to a
custom `ring`-discharge with explicit `Pᵢ₁² + Pᵢ₂²` substitutions
before `ring`.

## 4. Mathlib API audit (verified live)

In `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`:

| Line | Symbol                                       | Use                                    |
|------|----------------------------------------------|----------------------------------------|
| 361  | `theorem Matrix.det_eq_zero_of_column_eq_zero` | **Path A finisher**                  |
| 477  | `theorem Matrix.det_updateCol_add_smul_self`   | **Path A column operations (×3)**   |
| 467  | `theorem Matrix.det_updateCol_add_self`        | unit-multiplier variant (orientation) |

For Path B, the existing S2 file already uses:

- `Matrix.det_fin_four` (expands a 4×4 determinant to a 24-term polynomial sum).
- `EuclideanSpace.norm_eq` (norm = sqrt of sum-of-squares).
- `Fin.sum_univ_two` (sum over `Fin 2 = {0, 1}`).
- `Real.sq_sqrt`, `Real.sqrt_sq` (norm² ↔ sum-of-squares bridge).

All standard. No new imports needed beyond S2's.

## 5. Risk register

| Risk                                                              | Severity | Mitigation                                  |
|-------------------------------------------------------------------|----------|---------------------------------------------|
| `nlinarith` times out on the 24-term `det_fin_four` polynomial     | Med      | Fall back to Path A; or pre-substitute (★) and call `ring` |
| `EuclideanSpace.norm_eq` returns `Real.sqrt (∑ i, ...^2)`; need to square both sides of `‖_‖ = r` | Med | `Real.sqrt_eq_iff_sq_eq` + `hr_pos` → `sq_abs` |
| `det_updateCol_add_smul_self` requires `i ≠ j` proof; `Fin 4` index arithmetic | Low | `decide` discharges `(0 : Fin 4) ≠ (1 : Fin 4)` etc. |
| `Vec2 = EuclideanSpace ℝ (Fin 2)` coercion: `P 0` and `P 1` access | Low | Already in S2's file, just use the established style |
| S3 ACT may absorb S4 into the iff proof inline (Choice A); S4 ACT then has nothing to do | Low | Coordinate with S3 ACT author; ship S4 as Choice B helper if S3 leaves the (⇐) sorry standalone |
| `Matrix.det_fin_four` may produce a slightly different ordering of monomials than expected; `ring` may need explicit rewrite first | Low | `simp only` before `ring`, or `linear_combination` with explicit coefficients |
| Hypothesis `hr` (0 < r) needed to square both sides without sign issue | Low | Use `Real.sqrt_eq_iff_sq_eq` or `Real.sqrt_eq_iff_mul_self_eq` |

## 6. Acceptance criteria (binary)

The S4 ACT PR (or the S3 ACT PR that absorbs S4 inline) must:

- [ ] Either discharge the (⇐) half of `concyclicityDet_eq_zero_iff_concyclic`
      inline, **or** add a `theorem concyclicityDet_eq_zero_of_concyclic`
      helper.
- [ ] Use 0 new `sorry`, 0 `axiom`, ≤ 35 LOC body (whichever path).
- [ ] Build successfully via
      `./proofs/scripts/docker-build.sh Proofs.ProductOfSegmentsOfChordsOQ03`.
- [ ] Reuse S2's `Matrix.det_fin_four + ring` discipline if Path B;
      otherwise cite `det_updateCol_add_smul_self` if Path A.
- [ ] Update `state.md` "Subsequent Plan" table: S4 row sorries `-1`
      column reflects the close.
- [ ] Update `src/data/research/problems/product-of-segments-of-chords-oq-03.json`
      `nextSteps` to S5.
- [ ] Confirm 0 sorries on the slug Lean file after this merge.

The ACT PR **must NOT**:

- Touch `problem.md`, `knowledge.md`, the S2 SCAFFOLD's Lean file
  (`ProductOfSegmentsOfChordsOQ03.lean`) for definitions/structure —
  only the proof body of the relevant theorem.
- Attempt S5 (chord_product_equal → Δ = 0) — that's a separate
  bridge through `power-of-a-point` and is a different session.
- Add new top-level Mathlib imports beyond what S2 / S3 already
  pull (`Matrix.det_fin_four`, `EuclideanSpace.norm_eq`,
  `det_updateCol_add_smul_self` are all in `Mathlib`).
- Add an `axiom` declaration. The (⇐) direction is fully
  constructive.

## 7. Race awareness / orthogonality

At PREP push time (≥ 2026-05-13 02:25 UTC, ~5 min after the draft
opened):

| PR     | State                | File overlap with this PREP                          | Conclusion              |
|--------|----------------------|------------------------------------------------------|-------------------------|
| #18380 | MERGED 02:11 UTC     | none (different theorem; S2 SCAFFOLD already on main)| Orthogonal              |
| #18466 | Open (~6 min ago)    | none (different sessions/ note, different (⇐)/(⇒) direction) | Orthogonal              |

This PREP creates exactly one new file:
`research/problems/product-of-segments-of-chords-oq-03/sessions/2026-05-13-s04-prep-concyclic-implies-det-zero.md`.

PR #18466 adds `sessions/2026-05-13-s3-prep-cramer-design.md` and
focuses on the **(⇒)** direction (`det = 0 ∧ non-collinear → ∃ O r`)
via Cramer's rule + center+radius construction. This PREP focuses
on the **(⇐)** direction (`∃ O r → det = 0`) via column reduction.
Zero overlap on the Lean theorem body, zero overlap on session/ docs.

No `gh pr list --search` rows for "S4" or "concyclic" or
"row reduction" on this slug at PREP draft time.

## 8. Honest scope

This PREP **does**:

- Lock the algebraic identity (★) and two implementation paths.
- Cite the 3 load-bearing Mathlib lemmas live at master
  `2df2f015...`.
- Provide a Lean skeleton with explicit risk fallbacks.
- Estimate ~15-30 LOC for the S4 ACT body.
- Anticipate the S3 / S4 inline-vs-standalone packaging question.

This PREP **does not**:

- Discharge the S2 sorry. That's S3 ACT (and inline S4 if
  packaged together) or S4 ACT (standalone).
- Address S5 (chord_product_equal → Δ = 0) — that bridge uses
  the power-of-a-point theorem and is a separate session.
- Address the parent `converse_product_implies_concyclic_axiom`
  (state.md S6) — that's the final replacement step.

## 9. References

- Mathlib. `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean` —
  `det_updateCol_add_smul_self` (line 477),
  `det_eq_zero_of_column_eq_zero` (line 361).
- Parent file. `Proofs/ProductOfSegmentsOfChords.lean` —
  carries the `converse_product_implies_concyclic_axiom` that this
  slug's chain ultimately replaces.
- Slug Lean file. `Proofs/ProductOfSegmentsOfChordsOQ03.lean` —
  S2 SCAFFOLD with `concyclicityDetCoords` definition (line 54) and
  the iff theorem stub (line 98).
- Sister PREP. `2026-05-13-s3-prep-cramer-design.md` (PR #18466,
  researcher-9) — designs the (⇒) Cramer direction.

## 10. Files this PREP adds / does not edit

**Adds** (exactly one file):

- `research/problems/product-of-segments-of-chords-oq-03/sessions/2026-05-13-s04-prep-concyclic-implies-det-zero.md`
  (this file).

**Does not edit**:

- `proofs/Proofs/ProductOfSegmentsOfChordsOQ03.lean`.
- `proofs/Proofs/ProductOfSegmentsOfChords.lean` (parent).
- `proofs/Proofs.lean`.
- `research/problems/product-of-segments-of-chords-oq-03/problem.md`.
- `research/problems/product-of-segments-of-chords-oq-03/knowledge.md`.
- `research/problems/product-of-segments-of-chords-oq-03/state.md`.
- `research/problems/product-of-segments-of-chords-oq-03/bracketing-decomposition-draft.md`.
- The in-flight `sessions/2026-05-13-s3-prep-cramer-design.md` PREP.
- `src/data/research/problems/product-of-segments-of-chords-oq-03.json`.
- `src/data/proofs/product-of-segments-of-chords/meta.json`.

**Build status**: doc-only; no `lake build` invocation needed.
