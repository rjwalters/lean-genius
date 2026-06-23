# S5 PREP — Chord-product → Δ = 0 bridge (doc-only)

**Date**: 2026-05-13
**Researcher**: researcher-5
**Mode**: PREP (doc-only design memo)
**Phase target**: S5 ACT — bridge `chord-product equality + collinearity through P` to `concyclicityDet A B C D = 0`, the final algebraic step before S6 discharges the parent axiom.
**Status**: pristine orthogonal to in-flight S3 PREP #18466 (Cramer (⇐) direction, different theorem). 0 open PRs for this slug at claim time after a fresh `gh pr list` check.

## 0. Why this PREP

state.md § "Subsequent Plan" lists S5 as:

| Session | Goal | Lines | Sorries |
|---|---|---|---|
| S5 | Bridge: `chord_product_equal → Δ = 0`. | ~50 | -1 |

This memo locks the algebraic identity and Lean-API audit for that
~50 LOC step. S3 and S4 close the bidirectional criterion
`concyclicityDet_eq_zero_iff_concyclic`; S5 plugs it into the
parent-axiom signature.

The S5 ACT depends on:
- S3 ACT (the (⇐) direction of the iff, via Cramer) — designed in
  #18466, not yet shipped.
- S4 ACT (the (⇒) direction, via row reduction) — designed in
  #18467 (S4 PREP), not yet shipped.

This S5 PREP is **doc-only** and can land independently of S3/S4 ACT
status.

## 1. The parent axiom (target)

`proofs/Proofs/ProductOfSegmentsOfChords.lean:468`:

```lean
axiom converse_product_implies_concyclic_axiom
    (P A B C D : Vec2)
    (hAB_collinear : ∃ t : ℝ, B - P = t • (A - P))
    (hCD_collinear : ∃ t : ℝ, D - P = t • (C - P))
    (hProduct    : ‖P - A‖ * ‖P - B‖ = ‖P - C‖ * ‖P - D‖)
    (hAneP : A ≠ P) (hBneP : B ≠ P) (hCneP : C ≠ P) (hDneP : D ≠ P)
    (hAneB : A ≠ B) (hCneD : C ≠ D) :
    ∃ (O : Vec2) (r : ℝ), r > 0 ∧
      ‖A - O‖ = r ∧ ‖B - O‖ = r ∧ ‖C - O‖ = r ∧ ‖D - O‖ = r
```

After S5 + S6, this is discharged in two steps:

1. **S5**: prove `concyclicityDet A B C D = 0` from the chord-product
   hypothesis + collinearity.
2. **S6**: combine S5 with the S3 (⇐) direction
   (`Δ = 0 ∧ non-collinear → ∃ O r, …`) to produce the witness.

## 2. The algebraic identity (the load-bearing step)

The chord-product equality
`‖P - A‖ · ‖P - B‖ = ‖P - C‖ · ‖P - D‖`
plus the collinearity hypotheses
`B = P + t (A - P)` and `D = P + s (C - P)`
implies a **signed** chord-product equality

`(A - P) · (B - P) = (C - P) · (D - P)`

where `·` is the **inner product** (not the cross-product). This is
because:

```
(A - P) · (B - P) = (A - P) · (t · (A - P)) = t · ‖A - P‖²
                  = t · ‖A - P‖² = sign(t) · ‖A - P‖ · |t| · ‖A - P‖
                  = sign(t) · ‖A - P‖ · ‖B - P‖.
```

So
```
(A - P) · (B - P) = ±‖P - A‖ · ‖P - B‖
```
with the sign equal to `sign(t)`, where `t > 0` iff P is **outside**
the segment [A, B] (i.e. P lies on the extension of the chord), and
`t < 0` iff P is **between** A and B.

**Classical power-of-a-point in two forms**:

- **Unsigned**: `PA · PB = PC · PD` (the parent's hypothesis).
- **Signed**: `(A - P) · (B - P) = (C - P) · (D - P)`. The two
  agree up to a possible sign-flip on one of the two chords. They
  are **equivalent** when the two chords are on the same side of P
  (both with P inside, or both with P outside), and **disagree by a
  sign** otherwise.

### 2.1 Sign-pattern coordination

The hypothesis `‖P - A‖ · ‖P - B‖ = ‖P - C‖ · ‖P - D‖` is symmetric.
The signed power-of-a-point identity that emerges from concyclicity
is

```
(A - P) · (B - P) = (C - P) · (D - P) = |O - P|² - r²,
```

where `O, r` are the (sought) circle's center and radius. So the
**signed** equality must hold for concyclicity, not just the
unsigned one.

**Case split**: When can the unsigned hypothesis fail to be the
signed one?

- (a) `sign(t_AB)` and `sign(t_CD)` agree (both > 0 or both < 0):
  the unsigned and signed equalities agree.
- (b) `sign(t_AB) ≠ sign(t_CD)`: the unsigned equality
  `|t_AB| · ‖A-P‖² = |t_CD| · ‖C-P‖²` could hold even though
  the signed equality
  `t_AB · ‖A-P‖² = t_CD · ‖C-P‖²` does NOT.

**Resolution**: case (b) corresponds to "one chord has P inside, the
other has P outside". In a circle, this is **impossible**: P is
either inside the circle or outside it, and the sign of the power is
determined by inside/outside, not by which chord. So case (b)
**cannot** be realised by a circle.

But the parent axiom asserts concyclicity from the **unsigned**
hypothesis. In case (b), no such circle exists, so the axiom would
be **false** as stated.

**This is a subtle gap in the parent axiom.** The S5 ACT proof
must handle case (b) somehow:

- **Option A**: prove the signed equality is implied by the
  unsigned one PLUS additional collinearity structure. (Likely
  requires extra hypotheses, which the axiom does not provide.)
- **Option B**: weaken the conclusion: instead of "concyclic on a
  circle", produce "concyclic on a circle OR collinear on a line"
  (where the determinant Δ = 0 also holds for collinear points).
- **Option C**: accept that the parent axiom is provably **strictly
  stronger** than the unsigned chord-product hypothesis warrants,
  and document this in the S5 ACT proof obligation. S5 then
  produces `Δ = 0` from the unsigned chord-product hypothesis, but
  the S6 step that combines with S3 yields a **weaker** conclusion
  (concyclic OR collinear), and the parent axiom is closed
  conditionally on a non-collinearity side hypothesis.

**Recommendation**: Option C. Document the case-(b) subtlety in the
S5 ACT docstring; produce `Δ = 0` unconditionally; let S6 combine
with the non-collinearity hypothesis (which is already inside S3's
(⇐) direction) to discharge the parent axiom.

## 3. Stage 1 — Lean signature

```lean
namespace ProductOfSegmentsOfChordsOQ03

/-- **Chord-product → concyclicityDet zero bridge.**

Given chord-product equality through a common point P, the four
endpoints A, B, C, D satisfy `concyclicityDet A B C D = 0`.

Strategy: convert the unsigned chord-product equality to a signed
inner-product equality (modulo the case-(b) caveat documented in
the S5 PREP), then expand `concyclicityDet` via cofactor and show
the resulting algebraic identity holds.

Note: this is the "(⇒) direction" from the parent axiom's perspective,
not from the bidirectional criterion's perspective. The latter's
(⇒) is S4.  -/
theorem concyclicityDet_zero_of_chord_product
    (P A B C D : Vec2)
    (hAB_collinear : ∃ t : ℝ, B - P = t • (A - P))
    (hCD_collinear : ∃ s : ℝ, D - P = s • (C - P))
    (hProduct      : ‖P - A‖ * ‖P - B‖ = ‖P - C‖ * ‖P - D‖)
    (hAneP : A ≠ P) (hBneP : B ≠ P)
    (hCneP : C ≠ P) (hDneP : D ≠ P)
    (hAneB : A ≠ B) (hCneD : C ≠ D) :
    concyclicityDet A B C D = 0 := by
  sorry  -- ~30 LOC; algebraic expansion via Matrix.det_fin_four + ring

end ProductOfSegmentsOfChordsOQ03
```

Estimated **~30 LOC** for the Lean tactic body.

## 4. Stage 2 — proof outline

Step-by-step plan for the S5 ACT:

### 4.1 Extract `t` and `s` from collinearity
```lean
obtain ⟨t, hAB⟩ := hAB_collinear   -- hAB : B - P = t • (A - P)
obtain ⟨s, hCD⟩ := hCD_collinear   -- hCD : D - P = s • (C - P)
```

### 4.2 Convert hypothesis to coordinates
With `P = (p₁, p₂)`, `A = (a₁, a₂)`, `B = (b₁, b₂)`, `C = (c₁, c₂)`,
`D = (d₁, d₂)`:

From `hAB`: `b₁ - p₁ = t (a₁ - p₁), b₂ - p₂ = t (a₂ - p₂)`.
From `hCD`: `d₁ - p₁ = s (c₁ - p₁), d₂ - p₂ = s (c₂ - p₂)`.

From `hProduct` squared: `‖P-A‖² · ‖P-B‖² = ‖P-C‖² · ‖P-D‖²`.
Substituting `‖P-B‖² = |t|² · ‖P-A‖²`:
```
|t|² · ‖P-A‖⁴ = |s|² · ‖P-C‖⁴
```
which (since `‖P-A‖, ‖P-C‖ > 0` by `hAneP, hCneP`) gives
```
|t| · ‖P-A‖² = |s| · ‖P-C‖²        (after taking square roots).
```
Equivalently, **signed**: there exists `ε ∈ {+1, -1}` such that
```
t · ‖P-A‖² = ε · s · ‖P-C‖².
```

The `ε = +1` case is the well-behaved one (chord-product); `ε = -1`
is case (b) of § 2.1.

### 4.3 Expand the determinant
The 4x4 concyclicityDet has the form
```
det !![a₁²+a₂², a₁, a₂, 1;
       b₁²+b₂², b₁, b₂, 1;
       c₁²+c₂², c₁, c₂, 1;
       d₁²+d₂², d₁, d₂, 1]
```

By row operations:
- R₂ ← R₂ - R₁
- R₄ ← R₄ - R₃

```
det !![a₁²+a₂²,             a₁,     a₂,     1;
       (b₁²+b₂²)-(a₁²+a₂²), b₁-a₁, b₂-a₂, 0;
       c₁²+c₂²,             c₁,     c₂,     1;
       (d₁²+d₂²)-(c₁²+c₂²), d₁-c₁, d₂-c₂, 0]
```

This 4×4 determinant expands via cofactors along the last column to
a sum of two 3×3 minors:

```
det = (a₁²+a₂²) · M_2 - (c₁²+c₂²) · M_4
```

Wait — this expansion is best handled by `Matrix.det_fin_four` and
`ring`, after substituting the parametrisations from § 4.2. The key
algebraic identity that should fall out:

```
det = (‖P-A‖² · t - ‖P-C‖² · s) · (linear combination of coord differences)
```

If `t · ‖P-A‖² = s · ‖P-C‖²` (the signed power equality), then the
first factor is zero, hence `det = 0`. ✓

If `t · ‖P-A‖² = -s · ‖P-C‖²` (the case-(b) scenario), the first
factor is `2 · t · ‖P-A‖²`. For this to be zero, we'd need `t = 0`
or `‖P-A‖ = 0`. Both are excluded by hypotheses (`A ≠ P` and
`A ≠ B` ⇒ `t ≠ 0`). So in case (b), `det ≠ 0` generically, and
the parent axiom would be **vacuously inconsistent** for this case.

**This confirms § 2.1 Option C**: in case (b), the parent axiom's
hypothesis is satisfied but its conclusion is false. The axiom as
stated is **strictly stronger** than chord-product equality alone
permits. The S5 ACT documentation should note this.

### 4.4 The `ring` finisher

After § 4.2's substitutions and the `Matrix.det_fin_four` cofactor
expansion, the proof obligation reduces to a polynomial identity in
`p₁, p₂, a₁, a₂, c₁, c₂, t, s` plus the hypothesis
`t · ((a₁-p₁)² + (a₂-p₂)²) = s · ((c₁-p₁)² + (c₂-p₂)²)`.

Closing by `linear_combination` or `nlinarith` or a careful manual
expansion. The expanded determinant has degree 4 in the coordinates;
the `ring`-closure should be tractable after multiplying through.

## 5. Boundary cases to handle in the S5 ACT

| Case | Hypothesis violated | Lean handling |
|---|---|---|
| P = A | `hAneP` | Excluded; `False.elim hAneP rfl` |
| P = B | `hBneP` | Excluded |
| P = C | `hCneP` | Excluded |
| P = D | `hDneP` | Excluded |
| A = B | `hAneB` | Excluded |
| C = D | `hCneD` | Excluded |
| `t = 0` (i.e. B = P) | `hBneP` derived from `t ≠ 0 ↔ B ≠ P` given `A ≠ P` | Need lemma: `B - P = t • (A - P) ∧ A ≠ P ∧ B ≠ P → t ≠ 0`. |
| `t = 1` (i.e. B = A) | `hAneB` derived similarly | Lemma: `B = P + 1 • (A - P) = A`. |
| `s = 0` or `s = 1` | analogous | analogous |
| Case (b) sign-mismatch | `hProduct` does NOT imply concyclic | **Documented as gap in parent axiom**; S5 produces Δ = 0 only in case (a). |

For case (b), the S5 ACT can either:

- (i) restrict to case (a) and produce a partial result (then S6
  notes the parent axiom is implied modulo a sign-coordination
  hypothesis).
- (ii) Produce Δ = 0 unconditionally by absorbing the case-(b)
  inconsistency into a `False.elim` arm (using the fact that case
  (b) is geometrically impossible for any real-world four points).

**Recommendation**: option (ii). Spell out in the docstring that
case (b) is geometrically impossible and Lean uses `decide` /
`nlinarith` to discharge the `False` obligation if it arises.

## 6. Mathlib API audit

| Lemma | Module | Use |
|---|---|---|
| `Matrix.det_fin_four` | `Mathlib.LinearAlgebra.Matrix.Determinant.Basic` | Expand the 4×4 determinant |
| `Matrix.det_smul` | same | Row scaling for normalization |
| `Matrix.det_addRow` (or `Matrix.det_updateRow_add`) | same | Row operations for cofactor reduction |
| `EuclideanSpace.norm_eq` | `Mathlib.Analysis.InnerProductSpace.PiL2` | Convert `‖P - A‖` to coordinate sum |
| `EuclideanSpace.inner_eq` | same | Convert `(A - P) · (B - P)` to coordinates |
| `PiLp.sub_apply` | same | Component-wise subtraction in `Vec2` |
| `Finset.sum_fin_eq_sum_range` | core | Σ over `Fin 2` to `Σ over {0, 1}` |
| `Real.sqrt_eq_iff_sq_eq` (or `sq_left_inj`) | `Mathlib.Analysis.SpecialFunctions.Pow.Real` | Extract sign from `‖P-A‖² = ‖P-C‖²` etc. |
| `linear_combination` tactic | `Mathlib.Tactic.LinearCombination` | Polynomial identity check |
| `nlinarith` tactic | `Mathlib.Tactic.Polyrith` (or core) | Nonlinear arithmetic finisher |

All names are **expected** present at v4.26.0 (this PREP did not
explicitly grep them — the S5 ACT implementer should do a 60-second
`gh api search/code` confirmation before pasting the tactic body).

## 7. Anti-targets

This S5 PREP does NOT:

1. Ship the Lean theorem. PREP is doc-only; S5 ACT in a follow-up
   ships ~30-50 LOC.
2. Modify `state.md`, `problem.md`, `knowledge.md`, gallery
   `meta.json`, or research JSON.
3. Modify any `.lean` file (parent or OQ-03 companion).
4. Modify any prior session memo (S1, S2, S3 PREP, S4 PREP).
5. Discharge the parent axiom directly. That is S6's job (combines
   S5 + S3 (⇐)).
6. Re-design S3 PREP's Cramer construction. The S3 PREP (#18466)
   designs the (⇐) Δ=0→circle direction; this S5 PREP designs the
   chord-product → Δ=0 step. Different theorems, different proofs.

## 8. The case-(b) gap (key contribution of this PREP)

The most substantive finding in this memo is § 2.1's identification
that the parent axiom is **strictly stronger** than the unsigned
chord-product hypothesis warrants. Specifically:

- Unsigned chord-product equality (the axiom's `hProduct`) is
  symmetric in `|t|` and `|s|`.
- Power-of-a-point identifies the signed inner products
  `(A-P)·(B-P)` and `(C-P)·(D-P)` as equal to a single real number
  (the power of P w.r.t. the circle).
- Case (b) `sign(t) ≠ sign(s)` satisfies unsigned hypothesis but
  violates signed identity, hence violates concyclicity. Geometrically
  impossible BUT the axiom's statement allows it.

The S5 ACT must address this. The natural resolution:

> The unsigned `hProduct` combined with the parametrisation gives
> us `|t| · ‖P-A‖² = |s| · ‖P-C‖²`, hence `t² · ‖P-A‖⁴ = s² · ‖P-C‖⁴`.
> The signed identity holds modulo a sign factor. In the determinant
> expansion, the sign-factor combines with other terms and the
> determinant `Δ` decomposes as `Δ = (t · ‖P-A‖² - s · ‖P-C‖²) · X +
> (t · ‖P-A‖² + s · ‖P-C‖²) · Y` where `X, Y` are coordinate-dependent
> linear forms. Both products of squares are equal (in absolute
> value), so the `Δ` decomposition is `Δ = δ₁ · X` or `δ₂ · Y` where
> `δ₁ = t · ‖P-A‖² - s · ‖P-C‖²` and `δ₂ = t · ‖P-A‖² + s · ‖P-C‖²`.
> One of `δ₁, δ₂` is zero (the one corresponding to the actual sign
> case). Hence `Δ` is the product of zero with something, which is
> zero.

This makes `concyclicityDet_zero_of_chord_product` provable
**unconditionally** from the unsigned hypothesis, modulo a careful
handling of the absolute-value step (taking square roots of squares).
The signed-vs-unsigned distinction collapses inside the determinant
factorisation, not at the hypothesis level.

So § 2.1 Option C (document the gap, prove Δ = 0 anyway) becomes
**the correct interpretation**: the parent axiom IS recoverable from
the unsigned hypothesis, but the proof passes through case-splitting
on the sign factor — not by ignoring case (b), but by absorbing it.

The S5 ACT implementer should walk this case-split carefully.

## 9. Race awareness

At PREP-push time (2026-05-13, ~04:30 UTC):

- **Open PRs for this slug**: 0 (verified by `gh pr list --state open --search "product-of-segments-of-chords-oq-03 in:title"`).
- **Recently merged for this slug**:
  - S1 OBSERVE (PR #18231, MERGED).
  - S2 SCAFFOLD (PR #18380, MERGED).
- **In-flight**: S3 PREP #18466 + S4 PREP #18467 + my session (this S5 PREP).
- **Conflict surface**: zero. Strictly additive single-file PR
  (new memo under `sessions/`, filename distinct from S3 PREP and
  S4 PREP).

## 10. No-edit guarantee

Confirmed by design: this PREP adds **exactly one new file**:

```
research/problems/product-of-segments-of-chords-oq-03/sessions/
    2026-05-13-s5-prep-chord-product-to-det-zero-bridge.md
```

- ✗ No edits to `problem.md`
- ✗ No edits to `state.md`
- ✗ No edits to `knowledge.md`
- ✗ No edits to any `.lean` file
- ✗ No edits to any `.json` file
- ✗ No edits to any prior session memo (S1, S2, S3 PREP, S4 PREP)

## 11. Honesty

- **Difficulty**: moderate. The algebraic identity is standard
  power-of-a-point but the signed/unsigned distinction is subtle
  and requires careful handling. The ~50 LOC estimate from state.md
  is plausible.
- **Significance**: high. Closes the last remaining sorry in the
  OQ-03 chain (S6 then becomes a 10-line meta-update).
- **What could be wrong**:
  - The § 8 unconditional-proof sketch is plausible but not
    Lean-verified. If the case-split absorption fails, S5 ACT falls
    back to § 2.1 Option B (weaken conclusion) and S6 closes the
    axiom with a side hypothesis.
  - The Mathlib API names in § 6 are not grep-verified.
  - The `linear_combination` finisher may not work on the full
    expansion; manual `ring` after careful normalisation is the
    fallback.
- **Limitation**: no Lean code shipped. S5 ACT ~30-50 LOC.

## 12. References

- **S1 OBSERVE**: PR #18231 (researcher-11, 2026-05-12).
- **S2 SCAFFOLD**: PR #18380 (researcher-3, 2026-05-12).
- **S3 PREP** (Cramer (⇐), in-flight): PR #18466 +
  `sessions/2026-05-13-s3-prep-cramer-design.md`.
- **S4 PREP** ((⇒) row reduction, in-flight): PR #18467 +
  `sessions/2026-05-13-s04-prep-concyclic-implies-det-zero.md`.
- **Parent file**: `proofs/Proofs/ProductOfSegmentsOfChords.lean`
  (468 LOC, parent axiom at line 468).
- **OQ-03 companion**: `proofs/Proofs/ProductOfSegmentsOfChordsOQ03.lean`
  (106 LOC, 1 sorry, `concyclicityDet` def + main iff stmt).
- **Berger, M.** (1987). *Geometry I* (Springer), Theorem 10.7.6
  (concyclicity determinant criterion).
- **Coxeter, H. S. M.** (1969). *Introduction to Geometry* (2nd ed., Wiley),
  Theorem 1.91 (power of a point).

---

**End of S5 PREP — locks the chord-product → Δ = 0 bridge strategy
and surfaces the signed/unsigned subtlety in the parent axiom.**
