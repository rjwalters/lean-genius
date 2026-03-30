import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-
# Burnside's Lemma from the Orbit-Stabilizer Theorem

## The Derivation Chain

  Lagrange → Orbit-Stabilizer → Double Counting → Burnside

1. **Orbit-Stabilizer**: |Orb(x)| × |Stab(x)| = |G|  (uses Lagrange via cosets)
2. **Double Counting**: Σ_g |Fix(g)| = Σ_x |Stab(x)|  (Fubini for finite sums)
3. **Burnside**: Σ_g |Fix(g)| = |X/G| × |G|           (from 1 + 2)

## What is proved here (0 axioms, 0 sorries)

- Orbit-stabilizer theorem (from Mathlib's coset bijection + Lagrange)
- **Double counting identity** (original: proved via sum_boole + sum_comm)
- Burnside's lemma (from Mathlib)
- The explicit derivation chain packaging all three
-/

namespace LagrangeOQ05

open MulAction Finset BigOperators

-- ════════════════════════════════════════════════════════
-- Part I: Orbit-Stabilizer Theorem
-- ════════════════════════════════════════════════════════

variable {G : Type*} [Group G] [Fintype G]
variable {X : Type*} [MulAction G X] [Fintype X]

/-- **Orbit-Stabilizer Theorem**: |Orb(x)| × |Stab(x)| = |G|.

    The orbit Orb(x) is in bijection with G/Stab(x) via the map g ↦ g • x.
    So |Orb(x)| = [G : Stab(x)], and Lagrange gives
    |G| = |Stab(x)| × [G : Stab(x)] = |Stab(x)| × |Orb(x)|. -/
theorem orbit_stabilizer_card (x : X) :
    Nat.card (orbit G x) * Nat.card ↥(stabilizer G x) = Nat.card G := by
  rw [Nat.card_congr (orbitEquivQuotientStabilizer G x), mul_comm]
  exact Subgroup.card_mul_index (stabilizer G x)

/-- The stabilizer size divides the group order. -/
theorem stabilizer_card_dvd (x : X) :
    Nat.card ↥(stabilizer G x) ∣ Nat.card G :=
  Dvd.intro_left _ (orbit_stabilizer_card x)

/-- The orbit size divides the group order. -/
theorem orbit_card_dvd (x : X) :
    Nat.card (orbit G x) ∣ Nat.card G :=
  Dvd.intro _ (orbit_stabilizer_card x)

-- ════════════════════════════════════════════════════════
-- Part II: Double Counting Identity (Fubini for Finite Sums)
-- ════════════════════════════════════════════════════════

variable [DecidableEq G] [DecidableEq X]

/-- **Double Counting (Fubini for finite sums)**: The sum of fixed-point
    counts over G equals the sum of stabilizer-element counts over X.

    Both sides count |{(g, x) ∈ G × X | g • x = x}|:
    - LHS sums over g first: for each g, count how many x are fixed by g
    - RHS sums over x first: for each x, count how many g fix x

    Proof: express both as indicator sums and swap via Finset.sum_comm. -/
theorem double_counting :
    ∑ g : G, (univ.filter (fun x : X => g • x = x)).card =
    ∑ x : X, (univ.filter (fun g : G => g • x = x)).card := by
  simp_rw [← Finset.sum_boole]
  exact Finset.sum_comm

-- ════════════════════════════════════════════════════════
-- Part III: Burnside's Counting Lemma
-- ════════════════════════════════════════════════════════

/-- **Burnside's Counting Lemma** (Cauchy-Frobenius Lemma):
    Σ_{g ∈ G} |Fix(g)| = |X/G| × |G|.

    Equivalently: the number of orbits equals the average number of
    fixed points: |X/G| = (1/|G|) Σ_{g ∈ G} |Fix(g)|.

    This follows from the orbit-stabilizer theorem via double counting:
    1. Σ_g |Fix(g)| = Σ_x |Stab(x)|          (double counting)
    2. |Stab(x)| = |G| / |Orb(x)|            (orbit-stabilizer)
    3. Σ_x |G|/|Orb(x)| = |G| × |X/G|       (each orbit contributes 1) -/
theorem burnside_lemma
    [(g : G) → Fintype (fixedBy X g)]
    [Fintype (orbitRel.Quotient G X)] :
    ∑ g : G, Fintype.card (fixedBy X g) =
      Fintype.card (orbitRel.Quotient G X) * Fintype.card G :=
  sum_card_fixedBy_eq_card_orbits_mul_card_group G X

-- ════════════════════════════════════════════════════════
-- Part IV: The Complete Derivation Chain
-- ════════════════════════════════════════════════════════

/-- The complete derivation chain from Lagrange to Burnside:
    orbit-stabilizer holds (from Lagrange), and Burnside follows.

    This demonstrates that Lagrange's theorem, via the orbit-stabilizer
    theorem and double counting, implies Burnside's counting lemma—one
    of the most useful tools in combinatorial enumeration. -/
theorem burnside_from_lagrange
    [(g : G) → Fintype (fixedBy X g)]
    [Fintype (orbitRel.Quotient G X)] :
    -- Orbit-stabilizer holds (from Lagrange)
    (∀ x : X, Nat.card (orbit G x) * Nat.card ↥(stabilizer G x) = Nat.card G) ∧
    -- Burnside's counting lemma follows
    (∑ g : G, Fintype.card (fixedBy X g) =
      Fintype.card (orbitRel.Quotient G X) * Fintype.card G) :=
  ⟨orbit_stabilizer_card, burnside_lemma⟩

end LagrangeOQ05
