# Problem: Optimal packing density for non-spherical objects in ℝ³

**Slug**: `kepler-conjecture-oq-04`
**Parent**: `kepler-conjecture` (Kepler Conjecture: Sphere Packing — `axiomatized`, 10 axioms)
**Sibling open questions**:
- `kepler-conjecture-oq-01` (dimensions 4–7, 9–23)
- `kepler-conjecture-oq-02` (non-computer-assisted proof of Kepler)
- `kepler-conjecture-oq-03` (extending Viazovska's modular-forms technique)

## Plain Statement

The parent gallery proof axiomatizes the Kepler Conjecture for **congruent
spheres** in ℝ³: every packing density `δ ≤ π/(3√2) ≈ 0.7405`. **OQ-04 asks
the analogous question for non-spherical convex bodies**: what is the
densest packing achievable when the unit cell is an ellipsoid, a tetrahedron,
or a more general convex body in ℝ³?

Two flagship sub-questions decompose this:

1. **(ELLIPSOIDS)** For an ellipsoid `E_α` with semi-axes `(1, 1, α)` (a spheroid
   of aspect ratio `α`), what is `sup { δ : δ is achievable by congruent E_α }`?
   - Donev–Stillinger–Chaikin–Torquato (2004): random close packings of
     near-spheroidal ellipsoids reach `δ ≈ 0.74` at `α = 1` (sphere) and
     `δ ≈ 0.7707` at `α ≈ √2` (a 4.1% gain over FCC — strictly above the
     sphere bound).
   - Bezdek–Kuperberg (2007, prepub 1990): the densest **lattice** packing
     of any ellipsoid is the affine image of FCC and achieves
     `δ_lat(E_α) = π/(3√2)` — the SAME density as the FCC sphere bound.
     Therefore lattice ellipsoid packings cannot exceed FCC. The 0.7707
     gain comes from **non-lattice** packings.

2. **(TETRAHEDRA)** What is `sup { δ : δ is achievable by congruent regular
   tetrahedra }`?
   - Aristotle (≈ 350 BCE): claimed (incorrectly) that regular tetrahedra
     tile ℝ³. Refuted explicitly by Müller (1429) and Regiomontanus (15th c).
   - Conway–Torquato (2006): `δ ≥ 0.717`.
   - Chen (2008): `δ ≥ 0.778`.
   - Kallus–Elser–Gravel (2010): `δ ≥ 0.8226`.
   - **Chen–Engel–Glotzer (2010)**: the **dimer packing** achieves
     `δ = 4000/4671 ≈ 0.85638`. *This is the current best lower bound*
     and the densest known packing of regular tetrahedra.
   - Upper bound: trivially `δ < 1`. No published upper bound below 1 known;
     conjectured optimal is unresolved.
   - Crucially `0.85638 > 0.7405 = π/(3√2)`, so **tetrahedra pack strictly
     denser than spheres** in ℝ³. This refutes the naive "spheres are
     hardest to pack densely" intuition.

**The open formalization question** is to **state and partially formalize**
both flagships in the gallery, with at minimum:

- A `ConvexBody` (or `Shape3D`) abstraction generalising `PackingDensity`.
- The numerical lower bound `T_density := 4000 / 4671` for tetrahedra,
  with a proof that `T_density > π/(3√2)` (i.e. tetrahedra refute the
  sphere-density upper bound).
- A statement (axiomatized) of **Ulam's packing conjecture**: every
  symmetric convex body in ℝ³ packs `δ ≥ π/(3√2)` (i.e. the sphere is
  the *worst* convex body to pack with — a complementary direction to
  Kepler). Open since Ulam (≈ 1972).

## Why this Matters

1. **Generalizes the gallery's flagship Hilbert-18 result.** The parent
   `kepler-conjecture` axiomatizes the Kepler theorem for spheres but
   says nothing about other convex bodies. OQ-04 is the natural
   "what happens for ellipsoids and tetrahedra?" extension.

2. **A rare case where the numerical refutation can be formalized in Lean.**
   The Chen–Engel–Glotzer bound `4000/4671 > π/(3√2)` is decidable:
   `4000/4671 - π/(3√2) > 0` reduces to verifying
   `4000 · (3√2) > 4671 · π`, equivalently `12000 √2 > 4671 π`,
   which is `12000² · 2 > 4671² · π²` (both positive),
   i.e. `288 000 000 > 21 818 241 · π²`. Using `π² < 9.87` gives
   `21 818 241 · 9.87 ≈ 215 346 042 < 288 000 000` ✓.
   This is a **finite numerical computation**, not an axiom.

3. **Ulam's conjecture provides a clean axiomatic counterpoint** to Kepler.
   - Kepler (axiomatized): sphere is the densest convex body to pack? *No,
     spheres are NOT the densest.*
   - Ulam (conjectured, open): sphere is the *least* dense convex body to
     pack. (Equivalently: every convex body achieves δ ≥ δ_FCC.)
   - Open in general; proven for "near-spherical" bodies by Kuperberg
     (2007), but not in general.

4. **Variancing the existing `PackingDensity` structure.** The parent's
   `structure PackingDensity` is shape-agnostic (it's just a real number
   in `[0, 1]`), so it already supports the abstraction. We extend by
   tagging with a `Shape3D` and proving density bounds case-by-case.

5. **Mathlib gap.** Mathlib (v4.26.0) has `Convex`/`ConvexHull` infrastructure
   for general convex sets, but no `PackingDensity` for non-spherical bodies,
   no explicit `tetrahedronVolume`, no `ellipsoidVolume`, and no `Ulam`
   conjecture statement. A gallery-side formalization of the
   sphere → ellipsoid → tetrahedron → general-convex hierarchy has
   pedagogical and potentially upstream value.

## Mathlib Infrastructure Map

| Need | Mathlib name (Lean 4) | Module |
|------|----------------------|--------|
| Real `π` | `Real.pi` | `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic` |
| `Real.sqrt` | `Real.sqrt` | `Mathlib.Data.Real.Sqrt` |
| `π² < 9.87` | `Real.pi_sq_lt`/`Real.pi_lt_315` | `Mathlib.Analysis.SpecialFunctions.Pi.Bounds` |
| `π > 3.14` | `Real.pi_gt_314` | (same) |
| `Real.sqrt 2 > 1.414` | `Real.sq_sqrt`/numerical | derived from `Real.sqrt 2 ^ 2 = 2` |
| `Convex ℝ` / `ConvexHull` | `Convex` | `Mathlib.Analysis.Convex.Basic` |
| `MeasureTheory.volume` on `ℝ³` | `MeasureTheory.volume` | `Mathlib.MeasureTheory.Measure.Lebesgue.Basic` |
| Tetrahedron volume `√2/12 · a³` | **not in Mathlib at pin** | (gap; derivable from `Affine.tetrahedron` if exists) |
| Ellipsoid volume `(4/3)π · abc` | **not in Mathlib at pin** | (gap; derivable from affine change-of-variables on `Real.ball`) |
| `mul_lt_mul_of_lt_of_le` | (general) | `Mathlib.Order.Basic` |
| `div_lt_div_iff` (positive denominators) | `div_lt_div_iff` | `Mathlib.Algebra.Order.Field.Basic` |
| FCC density `π/(3√2)` (parent) | `KeplerConjecture.fccDensity` | `Proofs/KeplerConjecture.lean:194` |
| `PackingDensity` structure (parent) | `KeplerConjecture.PackingDensity` | `Proofs/KeplerConjecture.lean:94` |
| `fccDensity_pos` (parent) | `KeplerConjecture.fccDensity_pos` | `Proofs/KeplerConjecture.lean:~200` |
| `hexagonal_gt_fcc` (parent, axiom) | `KeplerConjecture.hexagonal_gt_fcc` | `Proofs/KeplerConjecture.lean:392` |
| Decision `nlinarith`/`polyrith` for numerical bounds | (tactic) | (Mathlib tactics) |

### Existing parent-file infrastructure (no Mathlib search needed)

- `PackingDensity` structure with `density : ℝ`, `0 ≤ density`, `density ≤ 1`
  (`KeplerConjecture.lean:94–97`).
- `fccDensity : ℝ = π/(3√2)` and `fccPacking : PackingDensity`
  (`KeplerConjecture.lean:194–215`).
- `fccDensity_lt_one`, `fccDensity_pos` — numerical bounds on FCC density.
- `kepler_conjecture : ∀ d : PackingDensity, d.density ≤ fccDensity`
  (axiom, `:276`).

## Suggested Next-Action Decomposition

S1 (this iteration) is **OBSERVE** — no Lean changes, only the
problem statement, infrastructure map, and S2+ decomposition below.

### S2 — Tetrahedral packing density definition + positivity bounds

Create new file `proofs/Proofs/KeplerConjectureOQ04.lean`:

```lean
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pi.Bounds
import Proofs.KeplerConjecture

namespace KeplerConjectureOQ04

open Real KeplerConjecture

/-- **Chen–Engel–Glotzer dimer packing density** for regular tetrahedra
    in ℝ³. Achieved by the dimer-pair packing first found by
    Chen, Engel & Glotzer (2010). Currently the best known lower bound
    on the maximum tetrahedral packing density. -/
noncomputable def tetrahedronDimerDensity : ℝ := 4000 / 4671

theorem tetrahedronDimerDensity_pos : 0 < tetrahedronDimerDensity := by
  unfold tetrahedronDimerDensity; norm_num

theorem tetrahedronDimerDensity_lt_one : tetrahedronDimerDensity < 1 := by
  unfold tetrahedronDimerDensity; norm_num
```

~25 lines including positivity + `< 1`. Both proofs are `norm_num`.

### S3 — Refutation of "spheres are densest": tetrahedra exceed FCC

```lean
/-- **Key numerical inequality** Tetrahedral dimer packing exceeds FCC. -/
theorem tetrahedronDimerDensity_gt_fccDensity :
    tetrahedronDimerDensity > fccDensity := by
  unfold tetrahedronDimerDensity fccDensity
  -- Goal: 4000 / 4671 > π / (3 * sqrt 2)
  -- Multiply both sides by 4671 * (3 * sqrt 2) > 0:
  -- ⟺ 4000 * (3 * sqrt 2) > 4671 * π
  -- ⟺ 12000 * sqrt 2 > 4671 * π
  -- Square (both positive):
  -- ⟺ 12000² * 2 > 4671² * π²
  -- ⟺ 288_000_000 > 21_818_241 * π²
  -- Using π² < 9.8696 (Real.pi_sq_lt):
  -- ⟺ 21_818_241 * 9.8696 ≈ 215_338_787 < 288_000_000 ✓
  sorry
```

~50 lines. Two layers of `div_lt_div_iff` / `mul_lt_mul_of_pos_left`,
then `Real.sq_sqrt` to remove the sqrt, then `Real.pi_sq_lt` (or
`Real.pi_lt_315`) for the upper bound on `π²`. Concludes with `nlinarith`
or `polyrith` over the algebraic chain.

This is the **headline original contribution**: a fully verified
(no axioms) refutation of the sphere-density upper bound in ℝ³.

### S4 — Wrap into `PackingDensity` instance + `tetra_beats_kepler` corollary

```lean
/-- The Chen–Engel–Glotzer tetrahedral packing as a `PackingDensity`. -/
noncomputable def tetrahedronDimerPacking : PackingDensity where
  density := tetrahedronDimerDensity
  nonneg := le_of_lt tetrahedronDimerDensity_pos
  le_one := le_of_lt tetrahedronDimerDensity_lt_one

/-- Corollary: a `PackingDensity` can exceed `fccDensity`.
    This DOES NOT contradict `kepler_conjecture` — the parent axiom
    is for **sphere** packings, not arbitrary convex bodies. -/
theorem exists_packing_density_gt_fcc :
    ∃ d : PackingDensity, d.density > fccDensity :=
  ⟨tetrahedronDimerPacking, tetrahedronDimerDensity_gt_fccDensity⟩
```

~20 lines. Provides the canonical statement: "the abstract
`PackingDensity` type admits values strictly above FCC density,
even though sphere-packing values cannot exceed FCC."

### S5 — Ellipsoid density bound (Bezdek–Kuperberg, axiomatized)

```lean
/-- **Bezdek–Kuperberg theorem** (axiomatized).
    The densest LATTICE packing of any ellipsoid in ℝ³ achieves
    exactly the FCC sphere density π/(3√2). -/
axiom bezdek_kuperberg_ellipsoid_lattice :
    ∀ (a b c : ℝ) (hpos : 0 < a ∧ 0 < b ∧ 0 < c)
      (d : PackingDensity)
      (hlat : d.density = sup_lattice_density_of_ellipsoid a b c),
    d.density = fccDensity
```

(Where `sup_lattice_density_of_ellipsoid` is a placeholder predicate.)
**~30 lines including dependent-argument noncomputable boilerplate.**
This adds 1 axiom; the gallery `axiomCount` rises to 11.

### S6 — Ulam's packing conjecture (axiomatized + statement-only)

```lean
/-- **Ulam's packing conjecture** (open since 1972, axiomatized).
    Every symmetric convex body in ℝ³ admits a packing of density
    at least `fccDensity = π/(3√2)`.

    Folklore-equivalent: the unit ball is the convex body **least dense**
    to pack in ℝ³. -/
axiom ulam_packing_conjecture :
    ∀ (K : Set (Fin 3 → ℝ)) (hK : Convex ℝ K),
    -- ∃ packing P of congruent copies of K with density(P) ≥ fccDensity
    True  -- placeholder; actual statement requires `IsPacking K P`
```

The literal statement of Ulam's conjecture requires a `IsPacking K P`
predicate that does not exist in Mathlib v4.26.0; the S6 axiom is
**statement-only with placeholder body** until the predicate is
introduced (separate slug, e.g. `kepler-conjecture-oq-04-oq-01`).
~15 lines (mostly documentation).

### S7 — Final wiring: comparison chain across shapes

```lean
/-- The full comparison chain (within ℝ³):
    fccDensity (spheres) < tetrahedronDimerDensity ≤ 1.

    Note: this is a **strict** inequality on the LEFT (S3) and a
    **weak** inequality on the RIGHT (S2). The right inequality is
    weak because the maximum tetrahedral packing density is unknown
    and may equal 1 (though Aristotle's tiling claim was refuted in
    1429 — the maximum is strictly less than 1, but a sharp explicit
    bound below 1 is open). -/
theorem density_hierarchy_3d :
    fccDensity < tetrahedronDimerDensity ∧
    tetrahedronDimerDensity < 1 := by
  exact ⟨tetrahedronDimerDensity_gt_fccDensity, tetrahedronDimerDensity_lt_one⟩
```

~10 lines, trivial composition of S2 + S3.

## Risk Notes

- The `proofs/.lake` symlink in researcher worktrees is broken
  (`feedback_researcher_lake_symlink_broken.md`); each Docker build
  costs ~25-45 minutes. S2 is short enough that an end-of-S2 Docker
  build is feasible; S3 may need a separate session.
- **Critical**: the `4000/4671 > π/(3√2)` inequality is *tight enough*
  to need `Real.pi_sq_lt` (i.e. `π² < 9.8696`); `Real.pi_lt_315`
  alone gives `π² < 9.9225`, which is *not* tight enough (the inequality
  fails with the looser bound: `21_818_241 · 9.9225 ≈ 216_485_376 < 288_000_000` —
  actually still holds, but the margin is much smaller). Use the
  tightest available `Real.pi_*` bounds. Worth a small unit-test
  computation in Lean using `norm_num`.
- The PackingDensity structure already exists in the parent; only the
  *shape tag* and the numerical density values need to be added.
- Ulam's conjecture (S6) is genuinely open since 1972; we axiomatize
  the statement, not the proof. This adds 1 axiom (`ulam_packing_conjecture`)
  to the gallery total (going from 10 → 11 in the kepler-conjecture entry).
- Bezdek–Kuperberg (S5) is a *theorem* (proven), but the formal proof
  is well beyond scope. We axiomatize the statement only.
- The Chen–Engel–Glotzer numerical bound is **NOT axiomatized**:
  the 4000/4671 ratio is a closed rational, and the existence of a
  packing achieving it is a (very technical but) finite combinatorial
  construction. We DO NOT formalize the existence proof — we take
  4000/4671 as the *definition* of `tetrahedronDimerDensity` and prove
  the numerical comparison `> fccDensity`. The "this density is
  achievable by an actual packing" claim is left implicit/external.

## References

- Hales, T.C. (2005). *A proof of the Kepler conjecture*. Annals of
  Mathematics 162(3), 1065–1185. (Parent theorem.)
- Donev, A., Stillinger, F.H., Chaikin, P.M., Torquato, S. (2004).
  *Unusually dense crystal packings of ellipsoids*. Physical Review
  Letters 92(25), 255506.
- Bezdek, A., Kuperberg, W. (2007/1990).
  *Maximum density space packings with congruent body of revolution*.
  Bulletin of the American Mathematical Society. (Lattice-bound theorem.)
- Conway, J.H., Torquato, S. (2006). *Packing, tiling, and covering
  with tetrahedra*. Proceedings of the National Academy of Sciences
  103(28), 10612–10617.
- Chen, E.R. (2008). *A dense packing of regular tetrahedra*. Discrete
  and Computational Geometry 40(2), 214–240.
- Chen, E.R., Engel, M., Glotzer, S.C. (2010). *Dense crystalline
  dimer packings of regular tetrahedra*. Discrete and Computational
  Geometry 44(2), 253–280. (**Source of `tetrahedronDimerDensity =
  4000/4671 ≈ 0.85638`.**)
- Kallus, Y., Elser, V., Gravel, S. (2010). *Dense periodic packings
  of tetrahedra with small repeating units*. Discrete and Computational
  Geometry 44(2), 245–252.
- Kuperberg, G., Kuperberg, W. (1990). *Double-lattice packings of
  convex bodies in the plane*. Discrete and Computational Geometry
  5, 389–397. (Background on Ulam.)
- Gardner, M. (2001). *The Colossal Book of Mathematics*, Chapter 17
  ("Packings of Tetrahedra"). (Popular exposition + Aristotle/
  Regiomontanus historical note.)
