# Knowledge Base: spherical-law-of-sines-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

OQ-02 of the `spherical-law-of-sines` gallery entry asks for the **dual spherical
law of cosines** (the `problem.md` canonical statement; the auto-generated JSON
title "Squared Ratio Formalization" had drifted to describe the parent file and
is superseded by the dual-law goal):

    cos C = - cos A · cos B + sin A · sin B · cos c

i.e. an *angle* expressed in terms of the other two angles and the opposite
*side* — dual to the standard law of cosines `cos c = cos a cos b + sin a sin b
cos C`.

In the parent's `Fin 3 → ℝ` cross-product framework, with unit-vector vertices
`A, B, C`, sides `a = arcLen B C`, `b = arcLen A C`, `c = arcLen A B`, and
dihedral angles `α = dihedralAngle A B C`, `β = dihedralAngle B A C`,
`γ = dihedralAngle C A B`, the target (angle `γ`, opposite side `c`) is

    cos γ = - cos α · cos β + sin α · sin β · cos c.

---

## Insights

### Direct algebraic proof (no polar triangle)

The textbook proof applies the standard law of cosines to the polar (dual)
triangle. That requires constructing the polar triangle and proving its
side/angle duality (~150–300 lines). **Avoided entirely** by reusing the two
*unconditional* product identities already proved in the sibling OQ-03 file
(`cos_dihedralAngle_mul`, `sin_dihedralAngle_mul`) plus the local law of cosines
(`spherical_law_of_cosines_local`).

Writing `p = ⟨A,B⟩ = cos c`, `q = ⟨A,C⟩ = cos b`, `r = ⟨B,C⟩ = cos a`:

* `⟨projPerp B A, projPerp C A⟩ = r − pq`   (= cos α · sin c · sin b)
* `⟨projPerp A B, projPerp C B⟩ = q − pr`   (= cos β · sin c · sin a)
* `⟨projPerp A C, projPerp B C⟩ = p − qr`   (= cos γ · sin b · sin a)
* `sin² c = 1 − p²`
* `det[A,B,C]² = 1 − p² − q² − r² + 2pqr`     (Gram determinant of unit vectors)

Multiplying the target by the non-zero factor `sin a · sin b · sin² c` and
substituting reduces it to the **cleared polynomial identity**

    (p − qr)(1 − p²) = −(r − pq)(q − pr) + det² · p,            (K)

which is closed by `ring` once `det²` is expanded (both sides equal
`p − p³ − qr + p²qr`). Cancelling the non-zero factor (proper triangle:
`sin a, sin b, sin c ≠ 0`) gives the honest `cos γ = …`. The two `sin`-form
factors multiply as `|det|·|det| = det²` (`Real.mul_self_sqrt`), so no square
roots survive.

### Reusable Gram identity

`tripleProduct_sq_eq` proves `det[A,B,C]² = det(Gram matrix)` (Cauchy–Binet) as a
pure `ring` identity with no unit hypotheses — reusable beyond this problem.

### Sibling angle laws for free

The dual laws for the other two angles (`α`, `β`) follow from the main statement
by relabelling the vertices `(A,B,C) ↦ (B,C,A)` / `(A,C,B)`, using
`dihedralAngle_comm_last` to normalise the angle argument order. No new algebra.

---

## Dead Ends

* Polar-triangle route — correct but needs substantial new infrastructure
  (polar vertices, side = π − angle duality). Not pursued; the projection-product
  route is shorter and reuses existing OQ-03 lemmas.

---

## Verification status

**VERIFIED** as of 2026-06-27. All 6 theorems type-check cleanly under the pinned
Mathlib (Lean v4.26.0). The Docker build host still has corrupted containerd
metadata (`write …/meta.db: input/output error`), so verification was done with
the host toolchain directly: `cd proofs && ./bin/lake env lean
Proofs/SphericalLawOfSinesOQ02.lean` exits 0 with no diagnostics.

`#print axioms` on every theorem
(`dual_spherical_law_of_cosines`, `dual_spherical_law_of_cosines_A`,
`dual_spherical_law_of_cosines_B`, `dual_law_of_cosines_polynomial`,
`tripleProduct_sq_eq`, `tripleProduct_sq_unit`) reports only
`[propext, Classical.choice, Quot.sound]` — the foundational axioms that do not
count as assumptions. The file is **axiom-free with 0 sorries**.
