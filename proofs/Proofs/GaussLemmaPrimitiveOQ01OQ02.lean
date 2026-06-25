/-
Gauss's Lemma in action: the monic cubic `X^3 - X - 1` is irreducible over ℚ,
proved entirely on the integer / finite-field side.

Source: open question 2 of the gauss-lemma-primitive family
Status: VERIFIED (0 axioms, 0 sorries)

The parent entry `gauss-lemma-primitive-oq-01` packaged Gauss's Lemma as a *bridge*:
for a monic integer polynomial, irreducibility over ℚ coincides with irreducibility
over ℤ (Mathlib's `IsPrimitive.Int.irreducible_iff_irreducible_map_cast` specialized to
monic polynomials, where primitivity is automatic).  The parent only exhibited a
*negative* witness (`2X`, showing primitivity cannot be dropped).  This entry supplies
the missing *positive* worked example: it pushes a genuine irreducibility question across
the bridge and dispatches it cheaply on the integer side.

The route is the standard "reduce mod a prime" obstruction:

  * `X^3 - X - 1` is monic, hence primitive;
  * its reduction mod 2 is `X^3 + X + 1 ∈ (ℤ/2)[X]`, which has no root in `ℤ/2`
    (it evaluates to 1 at both 0 and 1) and therefore — being a cubic over a field —
    is irreducible;
  * a monic polynomial whose reduction modulo a prime is irreducible is itself
    irreducible over ℤ (`Monic.irreducible_of_irreducible_map`);
  * Gauss's Lemma lifts integer irreducibility to irreducibility over ℚ.

We also package the general reusable step as
`irreducible_rat_of_irreducible_map_zmod`: a monic integer polynomial whose mod-`p`
reduction is irreducible is irreducible over ℚ.  No step ever touches a rational
denominator.

We prove:
1. `gauss_lemma_int_monic`                 — the monic Gauss bridge (parent's packaging)
2. `irreducible_rat_of_irreducible_map_zmod` — the reusable mod-`p` ⟹ over-ℚ bridge
3. `f_monic`                                — `X^3 - X - 1` is monic
4. `f_map_zmod_two`                         — its mod-2 reduction is `X^3 - X - 1` over ℤ/2
5. `f_no_root_zmod_two`                     — the reduction has no root in ℤ/2
6. `f_irreducible_zmod_two`                 — hence the reduction is irreducible
7. `f_irreducible_int`                      — `X^3 - X - 1` is irreducible over ℤ
8. `cubic_irreducible_over_rat`             — `X^3 - X - 1` is irreducible over ℚ (headline)
-/

import Mathlib

open Polynomial

namespace GaussLemmaPrimitiveOQ01OQ02

/-- **Monic Gauss bridge** (parent `gauss-lemma-primitive-oq-01`'s packaging).
For a monic integer polynomial, irreducibility over ℤ is equivalent to irreducibility
of its image in ℚ[X].  Monicity makes the polynomial primitive, so this is Mathlib's
`IsPrimitive.Int.irreducible_iff_irreducible_map_cast` with no side condition. -/
theorem gauss_lemma_int_monic {p : ℤ[X]} (hp : p.Monic) :
    Irreducible p ↔ Irreducible (p.map (Int.castRingHom ℚ)) :=
  IsPrimitive.Int.irreducible_iff_irreducible_map_cast hp.isPrimitive

/-- **Reusable mod-`p` bridge.**  A monic integer polynomial whose reduction modulo a
prime `p` is irreducible over the field `ℤ/p` is irreducible over ℚ.  This composes
`Monic.irreducible_of_irreducible_map` (mod-`p` irreducible ⟹ irreducible over ℤ) with
the monic Gauss bridge (irreducible over ℤ ⟹ irreducible over ℚ). -/
theorem irreducible_rat_of_irreducible_map_zmod {g : ℤ[X]} (hg : g.Monic)
    (p : ℕ) [Fact (Nat.Prime p)]
    (h : Irreducible (g.map (Int.castRingHom (ZMod p)))) :
    Irreducible (g.map (Int.castRingHom ℚ)) :=
  (gauss_lemma_int_monic hg).mp
    (Polynomial.Monic.irreducible_of_irreducible_map (Int.castRingHom (ZMod p)) g hg h)

/-- The monic cubic `X^3 - X - 1 ∈ ℤ[X]`. -/
noncomputable def f : ℤ[X] := X ^ 3 - X - 1

/-- `X^3 - X - 1` is monic. -/
theorem f_monic : f.Monic := by
  unfold f
  monicity!

/-- The reduction of `X^3 - X - 1` modulo 2 is `X^3 - X - 1` in `(ℤ/2)[X]`. -/
theorem f_map_zmod_two :
    f.map (Int.castRingHom (ZMod 2)) = (X ^ 3 - X - 1 : (ZMod 2)[X]) := by
  simp [f, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_one, Polynomial.map_X]

/-- The mod-2 reduction has no root in `ℤ/2`: it evaluates to `1` at both `0` and `1`. -/
theorem f_no_root_zmod_two :
    ∀ x : ZMod 2, ¬ (f.map (Int.castRingHom (ZMod 2))).IsRoot x := by
  rw [f_map_zmod_two]
  intro x
  simp only [IsRoot.def, eval_sub, eval_pow, eval_X, eval_one]
  revert x
  decide

/-- The mod-2 reduction is irreducible: a cubic over a field with no root is irreducible. -/
theorem f_irreducible_zmod_two :
    Irreducible (f.map (Int.castRingHom (ZMod 2))) := by
  have hdeg : (f.map (Int.castRingHom (ZMod 2))).natDegree = 3 := by
    rw [f_monic.natDegree_map]
    unfold f
    compute_degree!
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [hdeg]; decide
  · exact f_no_root_zmod_two

/-- `X^3 - X - 1` is irreducible over ℤ (its mod-2 reduction is irreducible and it is monic). -/
theorem f_irreducible_int : Irreducible f :=
  Polynomial.Monic.irreducible_of_irreducible_map (Int.castRingHom (ZMod 2)) f f_monic
    f_irreducible_zmod_two

/-- **Headline.**  The monic cubic `X^3 - X - 1` is irreducible over ℚ.  The proof never
factors over ℚ directly: it reduces mod 2 (no root ⟹ irreducible cubic), lifts to ℤ
(`Monic.irreducible_of_irreducible_map`), then to ℚ (Gauss's Lemma). -/
theorem cubic_irreducible_over_rat : Irreducible (X ^ 3 - X - 1 : ℚ[X]) := by
  have h : Irreducible (f.map (Int.castRingHom ℚ)) :=
    irreducible_rat_of_irreducible_map_zmod f_monic 2 f_irreducible_zmod_two
  have hmap : f.map (Int.castRingHom ℚ) = (X ^ 3 - X - 1 : ℚ[X]) := by
    simp [f, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_one, Polynomial.map_X]
  rwa [hmap] at h

end GaussLemmaPrimitiveOQ01OQ02
