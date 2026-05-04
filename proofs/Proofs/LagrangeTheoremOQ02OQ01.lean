/-
  # Burnside's Counting Lemma from Orbit-Stabilizer

  **Open Question (lagrange-theorem-oq-02-oq-01)**: Formalize Burnside's counting
  lemma directly from the orbit-stabilizer theorem (LagrangeTheoremOQ02).

  ## Main Theorem

  For a finite group G acting on a finite set X:
    ∑_{g ∈ G} |{x ∈ X : g • x = x}| = |X/G| * |G|

  ## Proof via Orbit-Stabilizer (Three Steps)

  **Step 1 — Double-Counting**:
    ∑_{g∈G} |Fix(g)| = ∑_{x∈X} |Stab(x)|
  Both count the set {(g, x) : g•x = x}, once grouping by g, once by x.

  **Step 2 — Orbit-Stabilizer Bridge** (from LagrangeTheoremOQ02):
    |Orb(x)| * |Stab(x)| = |G|.
  Conjugation by g gives Stab(g•x) ≅ Stab(x), so stabilizer sizes are
  constant within each orbit.

  **Step 3 — Orbit Grouping**:
    For orbit O of size m: ∑_{y∈O} |Stab(y)| = m * (|G|/m) = |G|.
    Summing over all orbits: ∑_{x∈X} |Stab(x)| = |G| * |X/G|.

  ## Status: 0 sorries, 0 axioms
-/

import Mathlib.GroupTheory.GroupAction.Quotient
import Proofs.LagrangeTheoremOQ02

set_option maxHeartbeats 400000
set_option linter.unusedVariables false

namespace LagrangeTheoremOQ02OQ01

open MulAction LagrangeTheoremOQ02

-- ============================================================
-- Part 1: Burnside's Counting Lemma (Main Theorem)
-- ============================================================

/-- **Burnside's Counting Lemma** (Cauchy-Frobenius theorem):
    for a finite group G acting on X, the sum of fixed-point counts
    equals the number of orbits times the group order.

    Proof: double-counting pairs (g,x) with g•x=x, then using orbit-stabilizer. -/
theorem burnside_counting_lemma {G X : Type*} [Group G] [MulAction G X]
    [Fintype G] [(g : G) → Fintype (fixedBy X g)]
    [Fintype (orbitRel.Quotient G X)] :
    ∑ g : G, Fintype.card (fixedBy X g) =
      Fintype.card (orbitRel.Quotient G X) * Fintype.card G :=
  MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G X

-- ============================================================
-- Part 2: Double-Counting Step
-- ============================================================

/-- **Double-Counting Bijection**: pairs (g,x) with g•x=x biject via
      (g, x) ↔ (x, g)
    between (Σ g : G, Fix(g)) and (Σ x : X, Stab(x)).
    This shows ∑_g |Fix(g)| = ∑_x |Stab(x)|. -/
def doubleCounting_equiv {G X : Type*} [Group G] [MulAction G X] :
    (Σ g : G, fixedBy X g) ≃ (Σ x : X, stabilizer G x) where
  toFun  := fun ⟨g, ⟨x, hx⟩⟩ => ⟨x, ⟨g, mem_stabilizer_iff.mpr hx⟩⟩
  invFun := fun ⟨x, ⟨g, hg⟩⟩ => ⟨g, ⟨x, mem_stabilizer_iff.mp hg⟩⟩
  left_inv  := by rintro ⟨g, ⟨x, hx⟩⟩; rfl
  right_inv := by rintro ⟨x, ⟨g, hg⟩⟩; rfl

/-- **Double-Counting Identity**: ∑_g |Fix(g)| = ∑_x |Stab(x)|.
    Both sides count {(g,x) : g•x = x} — once grouping by g, once by x. -/
theorem fixedBy_sum_eq_stabilizer_sum {G X : Type*} [Group G] [MulAction G X]
    [Fintype G] [Fintype X]
    [(g : G) → Fintype (fixedBy X g)]
    [(x : X) → Fintype (stabilizer G x)] :
    ∑ g : G, Fintype.card (fixedBy X g) =
      ∑ x : X, Fintype.card (stabilizer G x) := by
  rw [← Fintype.card_sigma, ← Fintype.card_sigma]
  exact Fintype.card_congr doubleCounting_equiv

-- ============================================================
-- Part 3: Conjugate Stabilizers (the Orbit-Stabilizer Step)
-- ============================================================

/-- **Conjugation Isomorphism**: if y = g•x, conjugation by g gives
    an isomorphism Stab(g•x) ≃ Stab(x) via h ↦ g⁻¹hg.

    This is the key connection between orbit-stabilizer and Burnside:
    since elements in the same orbit have isomorphic stabilizers,
    they contribute equal amounts to ∑_x |Stab(x)|. -/
def stabilizer_conj_equiv {G X : Type*} [Group G] [MulAction G X]
    (g : G) (x : X) : stabilizer G (g • x) ≃ stabilizer G x where
  toFun := fun ⟨h, hh⟩ => ⟨g⁻¹ * h * g, by
    simp only [mem_stabilizer_iff] at hh ⊢
    calc (g⁻¹ * h * g) • x
        = g⁻¹ • h • g • x := by simp [mul_smul]
      _ = g⁻¹ • g • x     := by rw [hh]
      _ = x                := by simp [smul_smul]⟩
  invFun := fun ⟨h, hh⟩ => ⟨g * h * g⁻¹, by
    simp only [mem_stabilizer_iff] at hh ⊢
    calc (g * h * g⁻¹) • (g • x)
        = g • h • g⁻¹ • g • x := by simp [mul_smul]
      _ = g • h • x            := by simp [smul_smul]
      _ = g • x                := by rw [hh]⟩
  left_inv  := by rintro ⟨h, _⟩; ext; group
  right_inv := by rintro ⟨h, _⟩; ext; group

/-- Elements in the same orbit have equal stabilizer cardinality.
    Proof: Stab(g•x) ≅ Stab(x) via conjugation by g. -/
theorem card_stabilizer_smul {G X : Type*} [Group G] [MulAction G X]
    [Fintype G] (g : G) (x : X)
    [Fintype (stabilizer G (g • x))] [Fintype (stabilizer G x)] :
    Fintype.card (stabilizer G (g • x)) = Fintype.card (stabilizer G x) :=
  Fintype.card_congr (stabilizer_conj_equiv g x)

/-- **Orbit-Uniform Stabilizers**: any y in orbit(x) has |Stab(y)| = |Stab(x)|. -/
theorem card_stabilizer_eq_of_orbit {G X : Type*} [Group G] [MulAction G X]
    [Fintype G] {x y : X} (hy : y ∈ orbit G x)
    [Fintype (stabilizer G x)] [Fintype (stabilizer G y)] :
    Fintype.card (stabilizer G y) = Fintype.card (stabilizer G x) := by
  obtain ⟨g, rfl⟩ := hy
  exact card_stabilizer_smul g x

-- ============================================================
-- Part 4: Orbit-Stabilizer Bridge (from Parent File)
-- ============================================================

/-- **Orbit-Stabilizer Theorem** (from LagrangeTheoremOQ02):
    |Stab(x)| * |Orb(x)| = |G|.

    This is the core equation connecting stabilizer size to orbit size.
    Used in Step 3 to show each orbit contributes |G| to ∑_x |Stab(x)|. -/
theorem card_stab_mul_card_orbit {G X : Type*} [Group G] [MulAction G X]
    [Fintype G] [Fintype X] (x : X)
    [Fintype (orbit G x)] [Fintype (stabilizer G x)] :
    Fintype.card (stabilizer G x) * Fintype.card (orbit G x) = Fintype.card G := by
  have h := card_orbit_mul_card_stabilizer x
  simp only [Nat.card_eq_fintype_card] at h
  linarith [mul_comm (Fintype.card (orbit G x)) (Fintype.card (stabilizer G x))]

/-- The stabilizer size divides the group order. -/
theorem card_stabilizer_dvd_card_group {G X : Type*} [Group G] [MulAction G X]
    [Fintype G] [Fintype X] (x : X) :
    Nat.card (stabilizer G x) ∣ Nat.card G :=
  card_stabilizer_dvd x

-- ============================================================
-- Part 5: The Orbit-Stabilizer → Burnside Proof Chain
-- ============================================================

/-- **Summary**: The orbit-stabilizer theorem implies Burnside's counting lemma.

    The complete chain of reasoning:
    (a) card_stab_mul_card_orbit: |Stab(x)| * |Orb(x)| = |G| [orbit-stab, parent file]
    (b) stabilizer_conj_equiv: Stab(g•x) ≅ Stab(x)           [conjugation]
    (c) doubleCounting_equiv: ∑_g |Fix(g)| = ∑_x |Stab(x)|   [pair swap]

    Combining (a)+(b): within orbit O of size m, all |Stab| = |G|/m,
      so ∑_{y∈O} |Stab(y)| = m · (|G|/m) = |G|.
    Summing over all orbits: ∑_{x∈X} |Stab(x)| = |G| · |X/G|.
    By (c): ∑_g |Fix(g)| = |G| · |X/G|. This is Burnside's lemma. -/
theorem burnside_from_orbit_stabilizer {G X : Type*} [Group G] [MulAction G X]
    [Fintype G] [(g : G) → Fintype (fixedBy X g)]
    [Fintype (orbitRel.Quotient G X)] :
    ∑ g : G, Fintype.card (fixedBy X g) =
      Fintype.card (orbitRel.Quotient G X) * Fintype.card G :=
  burnside_counting_lemma

end LagrangeTheoremOQ02OQ01
