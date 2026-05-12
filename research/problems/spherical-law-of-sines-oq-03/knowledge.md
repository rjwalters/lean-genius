# Knowledge: Four-Parts Formula for Spherical Triangles

**Slug**: spherical-law-of-sines-oq-03
**Phase**: OBSERVE
**Last updated**: 2026-05-12

## Mathlib v4.26.0 API Inventory (Pinned Toolchain)

### Trigonometry (canonical paths)

* `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic`
  - `Real.sin`, `Real.cos`, `Real.tan` — standard real trig.
  - `Real.cos_pi_div_two = 0`, `Real.sin_pi_div_two = 1`.
  - **No `Real.cot`** at v4.26.0; agents encode `cot x := cos x / sin x`
    or `cot x := (Real.tan x)⁻¹` as a local convention.
* `Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse`
  - `Real.arccos : ℝ → ℝ`, image `[0, π]`.
  - `Real.sin_arccos : Real.sin (Real.arccos x) = Real.sqrt (1 - x^2)`
    (unconditional — applies to all $x$, treats out-of-range as $0$).
  - `Real.cos_arccos : -1 ≤ x → x ≤ 1 → Real.cos (Real.arccos x) = x`.
  - `Real.arccos_nonneg : 0 ≤ Real.arccos x`.
  - `Real.arccos_le_pi : Real.arccos x ≤ π`.
* `Real.sin_nonneg_of_nonneg_of_le_pi : 0 ≤ x → x ≤ π → 0 ≤ Real.sin x`
  — the linchpin for extracting `sin(arcLen u v) ≥ 0` from
  `sin_sq_arcLen` (parent line 220).

### Linear algebra / cross product

* `Mathlib.LinearAlgebra.CrossProduct` — `Matrix.crossProduct`, used by
  parent via `(_×₃_) : (Fin 3 → ℝ) → (Fin 3 → ℝ) → (Fin 3 → ℝ)` notation.
* `Fin.sum_univ_three : (∑ i : Fin 3, f i) = f 0 + f 1 + f 2`.
* `linear_combination [hyps] := ring` — closes algebraic equalities
  given polynomial hypotheses. Used heavily by the parent.

### Standard tactics

* `field_simp`, `ring`, `nlinarith`, `polyrith` — sufficient for all
  polynomial / rational identities involving `sin, cos` once
  substitutions are made symbolically.

## Parent `spherical-law-of-sines` Infrastructure

(File: `proofs/Proofs/SphericalLawOfSines.lean`, 323 lines.)

| Item | Type | Notes |
|---|---|---|
| `dot a b` | `(Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ` | `∑ i, a i * b i` |
| `normSq a` | `(Fin 3 → ℝ) → ℝ` | `dot a a` |
| `IsUnit3 w` | `Prop` | `normSq w = 1`; used as unit-vector hypothesis |
| `arcLen u w` | `ℝ` | `Real.arccos (dot u w)` |
| `tripleProduct a b c` | `ℝ` | `dot a (b ×₃ c)` |
| `projPerp u w` | `(Fin 3 → ℝ) → ℝ` | `u - (dot u w) • w` |
| `dihedralAngle A B C` | `ℝ` | `arccos(dot(projPerp B A)(projPerp C A) / (\|projPerp B A\| \|projPerp C A\|))`, defaults to $0$ if either projection has zero norm |
| `lagrange_identity` | thm | $\lvert u\times v\rvert^2 = \lvert u\rvert^2\lvert v\rvert^2 - (u\cdot v)^2$ |
| `projPerp_dot_zero` | thm | $\mathrm{proj}_\perp(u,w)\cdot w = 0$ for unit $w$ |
| `normSq_projPerp_unit` | thm | $\lvert\mathrm{proj}_\perp(u,w)\rvert^2 = \sin^2(\mathrm{arcLen}(u,w))$ for unit $u, w$ |
| `projPerp_cross_eq` | thm | **Key**: $\mathrm{proj}_\perp(B,A)\times\mathrm{proj}_\perp(C,A) = \det[A,B,C]\cdot A$ for unit $A$ |
| `normSq_projPerp_cross` | thm | $\lvert\cdot\rvert^2 = \det[A,B,C]^2$ |
| `sin_sq_dihedralAngle` | thm | $\sin^2\alpha = \det^2 / (\sin^2 b\,\sin^2 c)$, for non-degenerate triangle |
| `sin_sq_arcLen` | thm | $\sin^2(\mathrm{arcLen}\,u\,w) = \lvert\mathrm{proj}_\perp(w,u)\rvert^2$ for unit $u, w$ |
| `spherical_law_of_sines_sq` | thm | two-ratio squared form |
| `spherical_law_of_sines_all_sq` | thm | all three ratios equal |

**Critical missing helper**: the parent does NOT export a linear (not
squared) `sin(arcLen u w) = ...` lemma. We'll need:

```lean
private lemma sin_arcLen_nonneg (u w : Fin 3 → ℝ) :
    0 ≤ Real.sin (arcLen u w) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (Real.arccos_nonneg _) (Real.arccos_le_pi _)

private lemma sin_arcLen_eq_sqrt (u w : Fin 3 → ℝ) (hu : IsUnit3 u)
    (hw : IsUnit3 w) :
    Real.sin (arcLen u w) = Real.sqrt (normSq (projPerp w u)) := by
  have h1 := sin_sq_arcLen u w hu hw  -- sin² = normSq
  have h2 : 0 ≤ Real.sin (arcLen u w) := sin_arcLen_nonneg u w
  have h3 : 0 ≤ normSq (projPerp w u) := normSq_nonneg _
  have := Real.sqrt_eq_iff_sq_eq h2 h3
  -- algebraic massage
  sorry  -- ~5-10 LOC, finalised in S2
```

(Both of these are short proofs once Mathlib lemma names are confirmed.
The latter may instead be stated as `sin(arcLen u w)² = normSq (projPerp w u)`
plus the sign — using `Real.sqrt_sq` if direction-of-equality matches.)

## Sibling `spherical-law-of-cosines` Infrastructure

(File: `proofs/Proofs/SphericalLawOfCosines.lean`, expected to provide:)

```lean
theorem spherical_law_of_cosines
    (A B C : Fin 3 → ℝ) (hA : IsUnit3 A) (hB : IsUnit3 B) (hC : IsUnit3 C) :
    Real.cos (arcLen B C)
    = Real.cos (arcLen A C) * Real.cos (arcLen A B)
      + Real.sin (arcLen A C) * Real.sin (arcLen A B)
        * Real.cos (dihedralAngle A B C)
```

S2 ORIENT must confirm:
* Exact name and namespace of the lemma.
* Whether the sibling uses the same `Fin 3 → ℝ` framework or
  `EuclideanSpace (Fin 3) ℝ` (which would force a translation).
* Whether non-degeneracy hypotheses are needed (probably yes for the
  dihedral-angle slot).

If the namespace bridge is awkward, Route B (independent cross-product
derivation, ~150-200 LOC) is the fallback.

## Classical References

* **Smart, *Textbook on Spherical Astronomy*, 6th ed. (1977)**, §3.7
  ("Four-parts formula"). Equation (3.31) is the same as our boxed form,
  presented as: $\cot a \sin b = \cos b \cos C + \cot A \sin C$.
* **Todhunter, *Spherical Trigonometry*, 5th ed. (1886)**, §62
  ("Cotangent formulae"). Equation (1) on p. 32 with the explicit
  multi-step derivation we follow above.
* **Wikipedia, *Spherical trigonometry*, §"Cotangent four-part
  formulae"**. Lists six cyclic variants and Napier's-circle
  visualisation.
* **Bowditch, *The American Practical Navigator*, 2002 ed.**, §22.6
  ("Computing intercepts"). The cotangent rule is the workhorse for
  converting between local equatorial and horizontal coordinates of
  celestial bodies.

## Proof Strategy: Route A Step-by-Step

**Goal (algebraic form, no cotangents)**:
$$
\sin\alpha \cos a \sin b
\;=\; \sin a \sin\alpha \cos b \cos\gamma
\;+\; \sin a \cos\alpha \sin\gamma
$$

**Step 1**: Apply spherical law of cosines for side $a$ (parent sibling
gives this with vertex $A$ as the dihedral-angle slot):
$$
\cos a = \cos b \cos c + \sin b \sin c \cos\alpha \qquad (\textsf{LC}_a)
$$

**Step 2**: Apply spherical law of cosines for side $c$ (relabel vertex
$C$ to the dihedral slot):
$$
\cos c = \cos a \cos b + \sin a \sin b \cos\gamma \qquad (\textsf{LC}_c)
$$

**Step 3**: Substitute $(\textsf{LC}_c)$ into $(\textsf{LC}_a)$ and
simplify with $1 - \cos^2 b = \sin^2 b$:
$$
\cos a \sin^2 b = \sin a \sin b \cos b \cos\gamma + \sin b \sin c \cos\alpha
$$
Divide by $\sin b$ (uses non-degeneracy $\sin b \ne 0$, equivalent to
`normSq (projPerp C A) ≠ 0`):
$$
\cos a \sin b = \sin a \cos b \cos\gamma + \sin c \cos\alpha \qquad (\star)
$$

**Step 4**: Apply law of sines ($\sin c \cdot \sin\alpha = \sin a \cdot \sin\gamma$
from parent's two-ratio form combined with non-negativity of $\sin$ on
$[0,\pi]$). Multiply $(\star)$ by $\sin\alpha$:
$$
\sin\alpha \cos a \sin b
= \sin\alpha \sin a \cos b \cos\gamma + \sin\alpha \sin c \cos\alpha
= \sin a \sin\alpha \cos b \cos\gamma + \sin a \sin\gamma \cos\alpha
$$
which is the boxed identity.

## Risk Register

| Risk | Mitigation |
|---|---|
| Sibling `spherical-law-of-cosines` uses different unit-vector convention (e.g. `EuclideanSpace` instead of `Fin 3 → ℝ`) | S2 ORIENT reads the sibling header; if mismatched, switch to Route B |
| `Real.cot` ambiguity in Lean | Use polynomial form (no cot); state corollary with `cot ≡ cos/sin` only as documentation |
| Law-of-sines bridge (squared → linear) needs sign argument | Helper lemma `sin_arcLen_nonneg` via `Real.sin_nonneg_of_nonneg_of_le_pi` + `Real.arccos_le_pi` |
| Non-degeneracy hypotheses become verbose | Bundle into a `SphericalTriangle` structure or use `[h]` tactic hypotheses; defer until S3 ACT |
| S2 ORIENT discovers an off-by-one in the formula statement | Stage S2 as scaffold with sorry-stub; S1's purpose is to flag this risk, not eliminate it |

## Module Path Verification (Deferred)

Worktree `.lake` symlink trap (`feedback_researcher_lake_symlink_broken.md`)
blocks direct Lean LSP-based path search during S1. S2 ORIENT must:
1. Open `proofs/Proofs/SphericalLawOfCosines.lean` and grep its header
   for the standard-law-of-cosines theorem name + signature.
2. Resolve imports: probably both `import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic`
   and `import Proofs.SphericalLawOfSines` for the framework lemmas.
3. Run a `docker-build.sh Proofs.SphericalLawOfSinesOQ03` to confirm
   the import graph (Mathlib cache warm-up estimated ~10-15 min in
   isolation, ~45 min if Mathlib is cold).
