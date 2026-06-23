/-
# Orbit Enumeration of Sylow p-Subgroups

OQ-02 follow-up to sylow-theorem (sylow-theorem).

This file formalizes the **orbit-based enumeration** of all Sylow p-subgroups of a
finite group G via the conjugation action. The key insight:

  All Sylow p-subgroups form a single conjugation orbit {g·P | g ∈ G},
  so their count equals [G : N_G(P)] — the index of the normalizer.

## Main Results

- `sylow_orbit_is_all` : orbit G P = ⊤ (every Sylow p-subgroup is conjugate to P)
- `exists_conj_eq` : ∀ Q : Sylow p G, ∃ g : G, g • P = Q
- `stabilizer_eq_normalizer` : stabilizer G P = N_G(P)
- `sylow_count_eq_normalizer_index` : |Sylow p G| = [G : N_G(P)]
- `sylowEquivQuotientNormalizer` : Sylow p G ≃ G / N_G(P)
- `sylow_orbit_stabilizer_formula` : |G| = |Sylow p G| × |N_G(P)|
- `sylow_unique_iff_normal` : |Sylow p G| = 1 ↔ P ◁ G
- `sylow_count_dvd_index` : |Sylow p G| ∣ [G : P]

## Key Mathematical Chain

  Sylow p G                  (all Sylow p-subgroups)
    ≃  orbit G P             (orbit of P under G-conjugation = everything, by orbit_eq_top)
    ≃  G / stabilizer G P    (orbit-stabilizer theorem)
    =  G / N_G(P)            (since stabilizer G P = N_G(P))

  Taking cardinalities: n_p = [G : N_G(P)]
  Combined with |N_G(P)| · [G : N_G(P)] = |G|: gives n_p · |N_G(P)| = |G|

## Tags
group-theory, sylow, orbit-stabilizer, enumeration, normalizer
-/

import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic

open MulAction

namespace SylowOrbitEnum

variable {G : Type*} [Group G] [Fintype G] {p : ℕ} [hp : Fact p.Prime]

/-!
## Part I: The Conjugation Orbit Covers All Sylow Subgroups

G acts on Sylow p G by conjugation: (g, P) ↦ gPg⁻¹.
The Sylow conjugacy theorem says this single orbit covers all of Sylow p G.
-/

/-- The conjugation orbit of any Sylow p-subgroup P equals the entire type Sylow p G.
    This is the set-level statement of the Sylow conjugacy theorem:
    every Sylow p-subgroup is conjugate to P. -/
@[simp]
theorem sylow_orbit_is_all [Finite (Sylow p G)] (P : Sylow p G) :
    orbit G P = ⊤ :=
  Sylow.orbit_eq_top P

/-- Every Sylow p-subgroup Q is conjugate to P: there exists g ∈ G with g • P = Q.
    This is the direct corollary of the orbit covering all of Sylow p G. -/
theorem exists_conj_eq (P Q : Sylow p G) : ∃ g : G, g • P = Q :=
  Sylow.exists_smul_eq G P Q

/-- Conjugation by any g gives an isomorphism P ≅ g • P as groups. -/
noncomputable def conj_iso (P : Sylow p G) (g : G) : P ≃* (g • P : Sylow p G) :=
  Sylow.equivSMul P g

/-!
## Part II: Orbit-Stabilizer Decomposition

The stabilizer of P under conjugation is the normalizer N_G(P) = {g ∈ G | gPg⁻¹ = P}.
This connects the orbit construction to classical normalizer theory.
-/

/-- The stabilizer of P under G-conjugation is exactly the normalizer N_G(P).
    Proof: g stabilizes P iff gPg⁻¹ = P iff g ∈ N_G(P). -/
theorem stabilizer_eq_normalizer (P : Sylow p G) :
    stabilizer G P = P.normalizer :=
  Sylow.stabilizer_eq_normalizer P

/-!
## Part III: Counting Sylow p-Subgroups

Combining the orbit = ⊤ fact with orbit-stabilizer gives the count formula:
  |Sylow p G| = [G : N_G(P)]
-/

/-- **Main counting theorem**: The number of Sylow p-subgroups equals the index
    of the normalizer of any fixed Sylow p-subgroup P.

    Proof route:
    1. orbit G P = Sylow p G      (by Sylow conjugacy)
    2. |orbit G P| = [G : stab G P]  (orbit-stabilizer theorem)
    3. stab G P = N_G(P)          (by stabilizer_eq_normalizer)
    4. Therefore |Sylow p G| = [G : N_G(P)] -/
theorem sylow_count_eq_normalizer_index [Finite (Sylow p G)] (P : Sylow p G) :
    Nat.card (Sylow p G) = P.normalizer.index :=
  Sylow.card_eq_index_normalizer P

/-- **Bijective enumeration**: There is an explicit bijection between the set of
    Sylow p-subgroups and the cosets of the normalizer G / N_G(P).
    This provides the concrete orbit enumeration algorithm:
    list all cosets gN_G(P) and map each to g • P. -/
noncomputable def sylowEquivQuotientNormalizer [Finite (Sylow p G)] (P : Sylow p G) :
    Sylow p G ≃ G ⧸ P.normalizer :=
  Sylow.equivQuotientNormalizer P

/-- The number of Sylow p-subgroups divides the index of P in G. -/
theorem sylow_count_dvd_index [Finite (Sylow p G)] (P : Sylow p G) :
    Nat.card (Sylow p G) ∣ P.index :=
  Sylow.card_dvd_index P

/-!
## Part IV: The Orbit-Stabilizer Product Formula

The orbit-stabilizer theorem, specialized to Sylow subgroups:
  |G| = |Sylow p G| × |N_G(P)|
-/

/-- **Orbit-stabilizer formula**: The group order equals the product of the
    Sylow p-subgroup count and the normalizer order.

    This is the group-theoretic version of the orbit-stabilizer theorem:
      |G| = |orbit G P| × |stabilizer G P| = n_p × |N_G(P)| -/
theorem sylow_orbit_stabilizer_formula [Finite (Sylow p G)] (P : Sylow p G) :
    Nat.card G = Nat.card (Sylow p G) * Nat.card P.normalizer := by
  rw [sylow_count_eq_normalizer_index P, mul_comm]
  exact P.normalizer.card_mul_index.symm

/-!
## Part V: Normality Criterion

A single Sylow p-subgroup is the special case where the orbit has exactly one element,
which happens precisely when P is normal in G.
-/

/-- **Normality criterion**: There is exactly one Sylow p-subgroup if and only if
    that subgroup is normal in G.

    Proof:
    n_p = 1   iff  [G : N_G(P)] = 1      (by counting theorem)
          iff  N_G(P) = G               (index 1 iff subgroup is whole group)
          iff  P ◁ G                    (normalizer = G iff normal) -/
theorem sylow_unique_iff_normal [Finite (Sylow p G)] (P : Sylow p G) :
    Nat.card (Sylow p G) = 1 ↔ (P : Subgroup G).Normal := by
  rw [sylow_count_eq_normalizer_index P, Subgroup.index_eq_one]
  exact Subgroup.normalizer_eq_top_iff

/-- If P is normal in G, it is the unique Sylow p-subgroup. -/
theorem sylow_unique_of_normal [Finite (Sylow p G)] (P : Sylow p G)
    (hN : (P : Subgroup G).Normal) : ∀ Q : Sylow p G, Q = P := by
  have h1 : Nat.card (Sylow p G) = 1 := (sylow_unique_iff_normal P).mpr hN
  have := Nat.card_eq_one.mp h1
  intro Q
  exact Unique.uniq (α := Sylow p G) ⟨⟩ Q

/-- A normal Sylow p-subgroup is fixed under every conjugation. -/
theorem smul_eq_of_normal (P : Sylow p G) (g : G) [h : P.Normal] :
    g • P = P :=
  Sylow.smul_eq_of_normal

/-!
## Part VI: The Count Congruence

Combining the orbit-stabilizer formula with Sylow's third theorem:
  n_p ≡ 1 (mod p)
-/

/-- The number of Sylow p-subgroups satisfies n_p ≡ 1 (mod p). -/
theorem sylow_count_congr_one [Finite (Sylow p G)] :
    Nat.card (Sylow p G) ≡ 1 [MOD p] :=
  card_sylow_modEq_one p G

/-!
## Summary Table

| Result | Mathlib backing |
|--------|----------------|
| orbit = all of Sylow p G | `Sylow.orbit_eq_top` |
| stabilizer = N_G(P) | `Sylow.stabilizer_eq_normalizer` |
| |Sylow p G| = [G : N_G(P)] | `Sylow.card_eq_index_normalizer` |
| Sylow p G ≃ G / N_G(P) | `Sylow.equivQuotientNormalizer` |
| |G| = n_p × |N_G(P)| | orbit-stabilizer + above |
| n_p = 1 ↔ P ◁ G | index_eq_one + normalizer_eq_top_iff |
| n_p ≡ 1 (mod p) | `card_sylow_modEq_one` |

Axiom count: 0, Sorry count: 0
-/

#check @sylow_orbit_is_all
#check @exists_conj_eq
#check @stabilizer_eq_normalizer
#check @sylow_count_eq_normalizer_index
#check @sylowEquivQuotientNormalizer
#check @sylow_orbit_stabilizer_formula
#check @sylow_unique_iff_normal
#check @sylow_unique_of_normal
#check @sylow_count_congr_one

end SylowOrbitEnum
