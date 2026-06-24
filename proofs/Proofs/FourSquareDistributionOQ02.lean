/-
  Orbit-Counting Bounds on the Number of Four-Square Representation Types
  Open Question: four-square-distribution-oq-02

  Parent `four-square-distribution` studies how the four-square representations of
  `n` distribute across *types* under the symmetries of reordering and sign change.
  By Jacobi's four-square theorem the number of ordered, signed representations is

      r₄(n) = 8 · ∑_{d ∣ n, 4 ∤ d} d.

  The natural symmetry group acting on the solution vectors `(x₁,x₂,x₃,x₄)` with
  `x₁²+x₂²+x₃²+x₄² = n` is the **hyperoctahedral group**

      B₄ = (ℤ/2)⁴ ⋊ S₄          (sign changes on each coordinate, then permutations),

  whose order is `2⁴ · 4! = 384`. A *representation type* of `n` is exactly a B₄-orbit
  of solution vectors. This file proves the clean, fully finite bound the problem asks
  for: the number of types `t(n)` is squeezed between `r₄(n)/384` and `r₄(n)`,

      r₄(n) / 384 ≤ t(n) ≤ r₄(n),     equivalently     r₄(n) ≤ 384 · t(n)  and  t(n) ≤ r₄(n).

  ## What is proved here (and what is assumed)

  The mathematical engine is a general orbit-counting double bound for *any* finite
  group acting on a finite type, proved here from Mathlib's `MulAction` API with
  **0 sorries and 0 axioms** (`numOrbits_le_card`, `card_le_card_group_mul_numOrbits`).
  Specialised to a group of order 384 it gives the four-square corollary
  (`fourSquare_numTypes_bounds`).

  We also compute the order of the hyperoctahedral group concretely:
  `card_hyperoctahedral_four : Nat.card (Equiv.Perm (Fin 4) × (Fin 4 → ZMod 2)) = 384`
  (the underlying set of B₄, with cardinality `4! · 2⁴`).

  ## Honest scope

  The corollary is stated for an *arbitrary* finite group `G` of order 384 acting on
  the (finite) set `S` of four-square solution vectors of `n`; we do not re-build the
  semidirect-product group structure of B₄ acting on ℤ⁴, nor re-derive Jacobi's exact
  value of `r₄(n) = Nat.card S` (the parent's domain). The orbit-counting bound depends
  only on the *order* of the acting group, so taking the action abstractly loses nothing
  in the bound while keeping the file genuinely 0-axiom. The two bounds are the content;
  the constant 384 is pinned by the concrete cardinality computation.

  References:
  - Jacobi (1834): the exact formula r₄(n) = 8 σ*(n)
  - four-square-distribution, four-square-distribution-oq-01: parent type decomposition
-/

import Mathlib

open MulAction

namespace FourSquareDistributionOQ02

-- ============================================================================
-- Part I: General orbit-counting bounds for a finite group action
-- ============================================================================

variable {G X : Type*} [Group G] [MulAction G X]

/-- Every orbit is the image of `G` under `g ↦ g • a`, hence has at most `|G|` elements. -/
theorem card_orbit_le [Finite G] (a : X) : Nat.card (orbit G a) ≤ Nat.card G := by
  apply Nat.card_le_card_of_surjective (fun g : G => (⟨g • a, mem_orbit a g⟩ : orbit G a))
  rintro ⟨x, hx⟩
  obtain ⟨g, rfl⟩ := hx
  exact ⟨g, rfl⟩

/-- **Upper bound.** The number of orbits (representation types) is at most `|X|`:
the orbit quotient map `X → X/∼` is surjective. -/
theorem numOrbits_le_card [Finite X] :
    Nat.card (orbitRel.Quotient G X) ≤ Nat.card X :=
  Nat.card_le_card_of_surjective _ Quotient.mk_surjective

/-- **Lower bound.** `|X| ≤ |G| · (number of orbits)`. Decompose `X` as the disjoint
union of its orbits and bound each orbit's size by `|G|`. -/
theorem card_le_card_group_mul_numOrbits [Finite G] [Finite X] :
    Nat.card X ≤ Nat.card G * Nat.card (orbitRel.Quotient G X) := by
  classical
  letI : Fintype (orbitRel.Quotient G X) := Fintype.ofFinite _
  have hcard : Nat.card X
      = ∑ ω : orbitRel.Quotient G X, Nat.card (orbit G ω.out) := by
    rw [Nat.card_congr (MulAction.selfEquivSigmaOrbits G X), Nat.card_sigma]
  rw [hcard]
  calc ∑ ω : orbitRel.Quotient G X, Nat.card (orbit G ω.out)
      ≤ ∑ _ω : orbitRel.Quotient G X, Nat.card G :=
        Finset.sum_le_sum (fun ω _ => card_orbit_le ω.out)
    _ = Nat.card G * Nat.card (orbitRel.Quotient G X) := by
        rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, ← Nat.card_eq_fintype_card]
        ring

/-- **The orbit-counting double bound**, packaged:
`|X| / |G| ≤ (number of orbits) ≤ |X|`, in the multiplicative form
`|X| ≤ |G| · t` together with `t ≤ |X|`. -/
theorem numOrbits_bounds [Finite G] [Finite X] :
    Nat.card X ≤ Nat.card G * Nat.card (orbitRel.Quotient G X)
      ∧ Nat.card (orbitRel.Quotient G X) ≤ Nat.card X :=
  ⟨card_le_card_group_mul_numOrbits, numOrbits_le_card⟩

/-- A nonempty finite `X` has at least one orbit. -/
theorem numOrbits_pos [Finite G] [Finite X] [Nonempty X] :
    0 < Nat.card (orbitRel.Quotient G X) := by
  haveI : Nonempty (orbitRel.Quotient G X) := ⟨Quotient.mk _ (Classical.arbitrary X)⟩
  exact Nat.card_pos

-- ============================================================================
-- Part II: The order of the hyperoctahedral group B₄
-- ============================================================================

/-- **The order of the hyperoctahedral group `B₄ = (ℤ/2)⁴ ⋊ S₄`.**

Its underlying set is `S₄ × (ℤ/2)⁴` (a permutation together with a sign vector), so it
has `4! · 2⁴ = 24 · 16 = 384` elements. This is the value of `|G|` plugged into the
orbit-counting bound below. -/
theorem card_hyperoctahedral_four :
    Nat.card (Equiv.Perm (Fin 4) × (Fin 4 → ZMod 2)) = 384 := by
  classical
  simp only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_perm, Fintype.card_fun,
      Fintype.card_fin, ZMod.card]
  decide

-- ============================================================================
-- Part III: The four-square representation-type bounds
-- ============================================================================

/-- **Bounds on the number of four-square representation types.**

Let `S` be the (finite) set of ordered, signed four-square representations of `n`
— so `Nat.card S = r₄(n)` by Jacobi — acted on by the hyperoctahedral group `B₄`
(here any finite group `G` of order 384). The number of representation types
`t(n) = Nat.card (B₄-orbits)` satisfies

    r₄(n) ≤ 384 · t(n)        and        t(n) ≤ r₄(n).

Equivalently `⌈r₄(n)/384⌉ ≤ t(n) ≤ r₄(n)`. -/
theorem fourSquare_numTypes_bounds {S : Type*} [Finite S]
    (hG : Nat.card G = 384) [Finite G] [MulAction G S] :
    Nat.card S ≤ 384 * Nat.card (orbitRel.Quotient G S)
      ∧ Nat.card (orbitRel.Quotient G S) ≤ Nat.card S := by
  refine ⟨?_, numOrbits_le_card⟩
  have h := card_le_card_group_mul_numOrbits (G := G) (X := S)
  rwa [hG] at h

/-- The lower bound in divided form: `r₄(n) / 384 ≤ t(n)`. -/
theorem fourSquare_numTypes_ge {S : Type*} [Finite S]
    (hG : Nat.card G = 384) [Finite G] [MulAction G S] :
    Nat.card S / 384 ≤ Nat.card (orbitRel.Quotient G S) :=
  Nat.div_le_of_le_mul (fourSquare_numTypes_bounds hG).1

end FourSquareDistributionOQ02

#print axioms FourSquareDistributionOQ02.card_le_card_group_mul_numOrbits
#print axioms FourSquareDistributionOQ02.numOrbits_le_card
#print axioms FourSquareDistributionOQ02.card_hyperoctahedral_four
#print axioms FourSquareDistributionOQ02.fourSquare_numTypes_bounds
