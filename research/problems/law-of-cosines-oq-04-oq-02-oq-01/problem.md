# Problem: Deriving the angle-bisector identity `m·b = n·c` from Mathlib's Euclidean-geometry API

**Slug**: `law-of-cosines-oq-04-oq-02-oq-01`
**Parent**: `law-of-cosines-oq-04-oq-02` (Angle Bisector Length Formula from Stewart's Theorem)
**Tier**: B (Significance 6 / Tractability 5)
**Phase**: OBSERVE (S1)

## Statement

### Plain Language

The parent gallery file `LawOfCosinesOQ04OQ02.lean` proves the angle-bisector length
formula `t²·(b+c)² = bc·((b+c)² − a²)` from Stewart's theorem, but it takes the
**angle-bisector identity**

> `m · b = n · c`   (where `m = BD`, `n = DC`, `b = CA`, `c = AB`)

as an **algebraic hypothesis** (parameter `hbis` in `angle_bisector_squared`,
`angle_bisector_ratio`, `angle_bisector_length`). In other words, the gallery proof is
parametric in this identity rather than deriving it from the actual geometric premise
"`AD` is the bisector of `∠BAC` and `D ∈ segment(B,C)`".

**OQ-04-OQ-02-OQ-01 asks**: Can the identity `m·b = n·c` be **derived from Mathlib's
metric / Euclidean-geometry API**, given only the geometric hypotheses

* `D` is strictly between `B` and `C` on segment `BC`, and
* the undirected angles `∠BAD` and `∠DAC` are equal (the angle-bisector condition),

so that the chained statement `angle_bisector_length` becomes parametric only in
**geometric** premises and not in an injected algebraic identity?

### Formal Statement

The target lemma (in some downstream `LawOfCosinesOQ04OQ02OQ01.lean`) should have a
signature like:

```lean
open EuclideanGeometry

theorem angle_bisector_ratio_from_geometry
    {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P]
    (A B C D : P)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hD   : Sbtw ℝ B D C)              -- D is strictly between B and C
    (hbis : ∠ B A D = ∠ D A C) :       -- AD bisects ∠BAC
    dist B D * dist A C = dist D C * dist A B
```

where `Sbtw ℝ B D C` is `Mathlib.Analysis.Convex.Between.Sbtw` and `∠` is
`EuclideanGeometry.angle`. The conclusion `dist B D * dist A C = dist D C * dist A B`
is exactly `m · b = n · c` with the convention
`a = dist B C, b = dist A C, c = dist A B, m = dist B D, n = dist D C`.

Plugging this into the parent file's `angle_bisector_length` produces a fully geometric
formulation of the angle-bisector-length identity.

### Why It Matters

* **Geometric grounding of an algebraic gallery proof.** The parent OQ-04-OQ-02 file is
  algebraically beautiful (every step a `linear_combination` witness) but operates on
  an *abstract* relation `m·b = n·c`. Bridging it to Mathlib's actual `dist`/`angle`
  API makes the formalization match the textbook geometric statement.

* **Reusable Mathlib pattern.** The angle-bisector theorem is a fundamental result in
  triangle geometry that — at the time of this writing — has **no direct counterpart in
  Mathlib**. A successful derivation produces a Mathlib-contribution candidate
  (e.g. under `Mathlib.Geometry.Euclidean.AngleBisector`) and a reusable template for
  other "bisector / cevian" identities (Ceva, Menelaus, Stewart restricted to
  geometric setups).

* **Pattern transferability.** The exact same template (`Sbtw` + angle equality ⇒
  side-length ratio) governs cevian / median / altitude-foot identities that recur
  across multiple gallery entries (`CevasTheorem*`, `LawOfCosinesOQ04*`,
  `LawOfCosines*OQ01*`). Producing the first such derivation establishes the API
  template for the rest.

* **Decoupling proof architecture.** Today the gallery contains *two distinct*
  triangle-geometry idioms: the algebraic `(a b c t m n : ℝ)`-parametric style
  (Stewart, Ceva-OQ02, Law-of-Cosines-OQ04) and the affine-Euclidean
  `(A B C D : P)`-parametric style (none in the gallery; only fragments in Mathlib
  upstream). OQ-04-OQ-02-OQ-01 is the natural bridge.

## Classification

* **Domain**: Euclidean geometry / inner-product affine spaces
* **Tags**: geometry, triangle-geometry, angle-bisector, stewarts-theorem, cevian,
  law-of-cosines, mathlib-integration, open-question
* **Type**: API-bridging open question (not a new mathematical result)

## Approach Menu

S1 surveys three approach paths. See `knowledge.md` §3 for full details.

| Path | Strategy | Status |
|------|----------|--------|
| A    | Law of sines in sub-triangles ABD, ACD; collinearity ⇒ `sin∠ADB = sin∠ADC`. | **Target.** Cleanest mathematically; requires a triangle-form law of sines that does **not** currently sit packaged in Mathlib. |
| B    | Parametrize `D = A + t (u + v)` where `u = (B−A)/|B−A|`, `v = (C−A)/|C−A|` (the bisector direction); solve `D ∈ aff(B,C)` for `t`; compute `BD` and `DC` explicitly. | **Backup.** Requires expanding norms; doable but heavy. |
| C    | Construct parallel line through `C` to `AB`, meeting line `AD` at `E`; show triangles `ABD, ECD` similar, then `AC = CE` from isoceles ⇒ ratio. | **Eliminated for S2 starter.** Mathlib lacks packaged parallel-similar-triangle infrastructure; would require building substantial scaffolding first. |

Path A is the S2 target. The atomic dependency it surfaces is a **triangle law of
sines lemma**, which itself can either (i) be derived locally from
`norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_norm_mul_cos_angle` (Mathlib
Triangle.lean's law of cosines) plus Pythagorean identity, or (ii) be invoked from
`EuclideanGeometry.Sphere.dist_div_sin_oangle_eq_two_mul_radius` after placing the
triangle on its circumcircle (which is heavier — requires `Module.Oriented ℝ V (Fin 2)`).

## Related Proofs

| Slug | Relationship |
|------|--------------|
| `law-of-cosines-oq-04-oq-02` | **Parent.** Currently parametric in `hbis : m*b = n*c`. Replacing this with a derived geometric premise is the entire scope of this OQ. |
| `law-of-cosines-oq-04`       | **Grandparent.** Provides Stewart's theorem; orthogonal to the bisector identity. |
| `law-of-cosines`             | **Root.** Provides the law of cosines in algebraic form. |
| `cevas-theorem-oq-02-oq-01-oq-03` | **Sibling pattern.** Same algebraic-parametric idiom (`α_D, β_D` weights); angle-bisector instance noted in its docstring (line 33). The geometric derivation here would generalize. |
| `cevas-theorem-oq-01`        | **Sibling.** Ceva's theorem in algebraic form; same parametric-vs-geometric tension. |

## Goal

Replace the algebraic hypothesis `hbis : m * b = n * c` in
`AngleBisectorLength.angle_bisector_length` with a geometric premise derived from
`Sbtw ℝ B D C ∧ ∠ B A D = ∠ D A C`, in a new file
`Proofs/LawOfCosinesOQ04OQ02OQ01.lean`. Target: zero axioms, zero sorries; ~250-400
lines.

## Acceptance Criteria

1. The file `Proofs/LawOfCosinesOQ04OQ02OQ01.lean` builds with `lake` against current
   Mathlib (verified via `proofs/scripts/docker-build.sh`).
2. The headline theorem `angle_bisector_ratio_from_geometry` (or equivalent) has
   signature taking only `Sbtw` + angle equality + non-degeneracy as hypotheses.
3. A specialization `angle_bisector_length_geometric` invokes the parent
   `AngleBisectorLength.angle_bisector_length` with the derived identity, producing a
   fully-geometric `t²·(b+c)² = bc·((b+c)² − a²)` statement.
4. Zero sorries and zero `axiom` declarations in the new file.
5. Gallery entry `src/data/proofs/law-of-cosines-oq-04-oq-02-oq-01/` updated with
   `meta.json`, `index.ts`, optional `annotations.json`.
