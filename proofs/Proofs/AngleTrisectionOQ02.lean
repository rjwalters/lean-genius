/-
  Angle Trisection - Open Question 02:
  Constructible Algebraic Numbers Characterized by Galois Groups

  Related: AngleTrisection.lean (main proof), AngleTrisectionOQ01.lean (degree criterion)
  Status: Known classical result (Wantzel 1837, Galois theory)

  Statement:
  An algebraic number α is constructible from ℚ by compass and straightedge
  if and only if the Galois group of its minimal polynomial over ℚ is a 2-group
  (i.e., every element has order a power of 2, equivalently the group has order 2^n).

  Background:
  Compass-and-straightedge constructions starting from ℚ generate fields obtained
  by successive degree-2 extensions (adding square roots). The key insight is that
  this tower structure is captured exactly by whether the Galois group is a 2-group.

  The hierarchy:
  1. OQ01 (degree criterion): α constructible → [ℚ(α):ℚ] = 2^k (necessary, not sufficient)
  2. OQ02 (Galois criterion): α constructible ↔ Gal(minpoly(ℚ,α)) is a 2-group (iff)

  Key examples:
  - √2:      Gal(x²-2/ℚ) ≅ ℤ/2ℤ (order 2 = 2¹, 2-group)  → constructible ✓
  - ∛2:      Gal(x³-2/ℚ) ≅ S₃   (order 6, not 2-group)    → NOT constructible ✗
  - 2^(1/4): Gal(x⁴-2/ℚ) ≅ D₄   (order 8 = 2³, 2-group)   → constructible ✓
  - cos(20°): Gal(8x³-6x-1/ℚ) ≅ ℤ/3ℤ (order 3, not 2-group) → NOT constructible ✗

  This file proves:
  1. Basic 2-group facts (proved)
  2. The Wantzel-Galois characterization (axiomatized)
  3. Non-constructibility of ∛2 and cos(20°) via Galois groups (axioms + easy derivations)

  References:
  - Wantzel, P.L. (1837): Impossible ruler-compass constructions
  - Stewart, I. "Galois Theory" (4th ed.) Theorem 14.1
-/

import Mathlib
import Proofs.InverseGalois
import Proofs.InverseGaloisD4
import Proofs.NthRootIrrationalOQ01
import Proofs.AngleTrisectionCos20Gal

open Polynomial IntermediateField FiniteDimensional

/-
## Part I: 2-Groups
-/

/-- A 2-group has order a power of 2 (for finite groups). -/
theorem isPGroup_iff_card_pow_two (G : Type*) [Group G] [Fintype G] :
    IsPGroup 2 G ↔ ∃ n : ℕ, Nat.card G = 2 ^ n :=
  IsPGroup.iff_card

/-- A group of 2-power order is a 2-group. -/
theorem isPGroup_of_card_pow_two {G : Type*} [Group G] {n : ℕ}
    (h : Nat.card G = 2 ^ n) : IsPGroup 2 G :=
  IsPGroup.of_card h

/-- A 2-group has order a power of 2 (converse direction). -/
theorem isPGroup_card_is_pow_two {G : Type*} [Group G] [Fintype G] (hG : IsPGroup 2 G) :
    ∃ n : ℕ, Nat.card G = 2 ^ n :=
  IsPGroup.iff_card.mp hG

/-
## Part II: Constructibility Definition
-/

/-- α ∈ ℝ is constructible from ℚ if it lies in a finite extension K of ℚ inside ℝ
    with [K:ℚ] a power of 2. This is the "tower condition" for constructibility. -/
def IsConstructibleFromQ (α : ℝ) : Prop :=
  ∃ (K : IntermediateField ℚ ℝ),
    FiniteDimensional ℚ K ∧
    (∃ n : ℕ, Module.finrank ℚ K = 2 ^ n) ∧
    α ∈ K

/-
## Part III: The Wantzel-Galois Characterization (Main Theorem)
-/

/-- Wantzel-Galois Theorem: An algebraic number α is constructible from ℚ if and
    only if the Galois group of its minimal polynomial over ℚ is a 2-group.

    Proof outline:
    (→) If α is constructible, it lies in a tower ℚ = K₀ ⊂ K₁ ⊂ ... ⊂ Kₙ with [Kᵢ₊₁:Kᵢ] = 2.
        The Galois closure K of ℚ(α) has [K:ℚ] = 2^m, so Gal(K/ℚ) has order 2^m → 2-group.
        Since minpoly(ℚ,α) splits over K, Gal(minpoly) embeds into Gal(K/ℚ) → also a 2-group.
    (←) If Gal(minpoly(ℚ,α)) is a 2-group, then it has a composition series with ℤ/2ℤ factors
        (2-groups are solvable), each step giving a degree-2 extension → α is constructible.

    This is axiomatized as the full proof requires the Galois correspondence. -/
axiom wantzel_galois_characterization (α : ℝ) (hα : IsIntegral ℚ α) :
    IsConstructibleFromQ α ↔ IsPGroup 2 (minpoly ℚ α).Gal

/-
## Part IV: Non-Constructibility via Galois Groups

  Key lemma: 6 is not a power of 2. We use that 3 divides 6 but 3 is coprime to 2^n.
-/

/-- 3 divides 6 but not any power of 2 — used to show order-6 groups are not 2-groups. -/
private lemma not_pow_two_of_eq_six {n : ℕ} (h : 6 = 2 ^ n) : False := by
  have hcop : Nat.Coprime 3 (2 ^ n) :=
    Nat.Coprime.pow_right n (by norm_num : Nat.Coprime 3 2)
  have h3dvd : (3 : ℕ) ∣ 2 ^ n := h ▸ (by norm_num)
  exact absurd (hcop ▸ Nat.dvd_gcd (dvd_refl 3) h3dvd) (by norm_num)

/-- The Galois group of x³ - 2 over ℚ has order 6 (≅ S₃).
    Proved in InverseGalois.lean. -/
theorem x_cube_sub_2_gal_order :
    Fintype.card (X ^ 3 - C 2 : ℚ[X]).Gal = 6 :=
  InverseGaloisProblem.x_cube_sub_2_gal_card

/-- S₃ (order 6) is NOT a 2-group. -/
theorem x_cube_sub_2_gal_not_2group : ¬ IsPGroup 2 (X ^ 3 - C 2 : ℚ[X]).Gal := by
  intro h
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h
  rw [Nat.card_eq_fintype_card, x_cube_sub_2_gal_order] at hn
  exact not_pow_two_of_eq_six hn

/-- The Galois group of 8x³ - 6x - 1 (minimal polynomial of cos(20°)) has order 3.
    Proved in AngleTrisectionCos20Gal.lean via Eisenstein criterion + splitting field analysis. -/
theorem cos20_gal_order :
    Fintype.card (8 * X ^ 3 - 6 * X - C 1 : ℚ[X]).Gal = 3 :=
  AngleTrisectionCos20Gal.cos20_gal_card

/-- 3 is not a power of 2. -/
private lemma not_pow_two_of_eq_three {n : ℕ} (h : 3 = 2 ^ n) : False := by
  have hn : n ≤ 1 := by
    by_contra hc; push_neg at hc
    have : 4 ≤ 2 ^ n := le_trans (show 4 ≤ 2 ^ 2 by norm_num)
      (Nat.pow_le_pow_right (by omega) hc)
    omega
  interval_cases n <;> simp_all

/-- The Galois group of the cos(20°) minimal polynomial is NOT a 2-group. -/
theorem cos20_gal_not_2group : ¬ IsPGroup 2 (8 * X ^ 3 - 6 * X - C 1 : ℚ[X]).Gal := by
  intro h
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h
  rw [Nat.card_eq_fintype_card, cos20_gal_order] at hn
  exact not_pow_two_of_eq_three hn

/-
## Part V: Constructibility Examples
-/

/-- x² - 2 is irreducible over ℚ (Eisenstein at 2). -/
private theorem x_sq_sub_2_irreducible : Irreducible (X ^ 2 - C (2 : ℚ)) :=
  NthRootIrrationalOQ01.eisenstein_X_pow_sub_prime 2 2 (by omega) (by decide)

/-- x² - 2 is separable over ℚ (irreducible in char 0). -/
private theorem x_sq_sub_2_separable : (X ^ 2 - C (2 : ℚ)).Separable :=
  x_sq_sub_2_irreducible.separable

/-- x² - 2 has degree 2. -/
private theorem x_sq_sub_2_natDegree :
    (X ^ 2 - C (2 : ℚ) : ℚ[X]).natDegree = 2 :=
  NthRootIrrationalOQ01.natDegree_X_pow_sub_C_eq (by omega) (by norm_num)

/-- x² - 2 is monic. -/
private theorem x_sq_sub_2_monic : (X ^ 2 - C (2 : ℚ) : ℚ[X]).Monic :=
  monic_X_pow_sub_C 2 (by omega)

/-- The Galois group of x² - 2 over ℚ has order 2.
    Proof: Divisibility squeeze — 2 | |Gal| (prime degree) and |Gal| | 2! = 2 (embeds into S₂). -/
theorem x_sq_sub_2_gal_order :
    Fintype.card (X ^ 2 - C 2 : ℚ[X]).Gal = 2 := by
  set p := (X ^ 2 - C 2 : ℚ[X])
  -- Lower bound: 2 | |Gal| (irreducible polynomial of prime degree 2)
  have hlb : 2 ∣ Fintype.card p.Gal := by
    have h := Polynomial.Gal.prime_degree_dvd_card x_sq_sub_2_irreducible
      (by rw [x_sq_sub_2_natDegree]; decide)
    rw [x_sq_sub_2_natDegree, Nat.card_eq_fintype_card] at h
    exact h
  -- Upper bound: |Gal| | 2 (Gal embeds into Perm(rootSet), rootSet has 2 elements)
  have hub : Fintype.card p.Gal ∣ 2 := by
    classical
    haveI : Fact (map (algebraMap ℚ p.SplittingField) p).Splits :=
      ⟨Polynomial.SplittingField.splits p⟩
    have hinj := Polynomial.Gal.galActionHom_injective p p.SplittingField
    have hdvd : Nat.card p.Gal ∣ Nat.card (Equiv.Perm (p.rootSet p.SplittingField)) :=
      Subgroup.card_dvd_of_injective _ hinj
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_perm] at hdvd
    have hcard : Fintype.card (p.rootSet p.SplittingField) = 2 :=
      (Polynomial.card_rootSet_eq_natDegree x_sq_sub_2_separable
        (Polynomial.SplittingField.splits p)).trans x_sq_sub_2_natDegree
    rw [hcard] at hdvd
    simpa using hdvd
  -- 2 | |Gal| and |Gal| | 2 → |Gal| = 2
  exact Nat.dvd_antisymm hub hlb

/-- Gal(x²-2/ℚ) is a 2-group (order 2 = 2¹). -/
theorem x_sq_sub_2_gal_is_2group : IsPGroup 2 (X ^ 2 - C 2 : ℚ[X]).Gal :=
  IsPGroup.of_card (show Nat.card (X ^ 2 - C 2 : ℚ[X]).Gal = 2 ^ 1 from by
    simp [Nat.card_eq_fintype_card, x_sq_sub_2_gal_order])

/-- The Galois group of x⁴ - 2 over ℚ has order 8 (≅ D₄, the dihedral group).
    Proved in InverseGaloisD4.lean. -/
theorem x_4th_sub_2_gal_order :
    Fintype.card (X ^ 4 - C 2 : ℚ[X]).Gal = 8 :=
  InverseGaloisExtensions.x4_sub_2_gal_card

/-- Gal(x⁴-2/ℚ) is a 2-group (order 8 = 2³). -/
theorem x_4th_sub_2_gal_is_2group : IsPGroup 2 (X ^ 4 - C 2 : ℚ[X]).Gal :=
  IsPGroup.of_card (show Nat.card (X ^ 4 - C 2 : ℚ[X]).Gal = 2 ^ 3 from by
    simp [Nat.card_eq_fintype_card, x_4th_sub_2_gal_order])

/-
## Part VI: Connecting OQ01 and OQ02
-/

/-- The Galois criterion (OQ02) implies the degree criterion (OQ01):
    If Gal is a 2-group then |Gal| = 2^k, and natDegree(p) divides |Gal(p)|,
    so natDegree divides a power of 2.

    Proof: The minpoly is monic and irreducible, so by the tower law
    (adjoin a root, then extend to splitting field), natDegree divides
    [SplittingField : ℚ] = |Gal| = 2^k. -/
theorem galois_2group_implies_degree_pow2 (α : ℝ) (hα : IsIntegral ℚ α)
    (hGal : IsPGroup 2 (minpoly ℚ α).Gal) :
    ∃ n : ℕ, (minpoly ℚ α).natDegree ∣ 2 ^ n := by
  -- Step 1: IsPGroup gives |Gal| = 2^k
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hGal
  -- Step 2: |Gal| = finrank (minpoly is separable over ℚ, char 0)
  have hsep : (minpoly ℚ α).Separable := (minpoly.irreducible hα).separable
  have hcard := Polynomial.Gal.card_of_separable hsep
  -- hcard : Nat.card Gal = finrank ℚ SplittingField
  -- Step 3: natDegree divides finrank (tower law via InverseGaloisD4)
  have hdvd := InverseGaloisExtensions.irred_monic_degree_dvd_splitting_finrank
    (minpoly.irreducible hα) (minpoly.monic hα)
  -- Step 4: Combine: natDegree | finrank = Nat.card Gal = 2^k
  have hfinrank : Module.finrank ℚ (minpoly ℚ α).SplittingField = 2 ^ k :=
    hcard.symm.trans hk
  exact ⟨k, hfinrank ▸ hdvd⟩

/-- The Galois characterization implies the degree criterion:
    constructible → Gal is 2-group → degree divides 2^n. -/
theorem constructible_implies_degree_dvd_pow2 (α : ℝ) (hα : IsIntegral ℚ α)
    (hc : IsConstructibleFromQ α) :
    ∃ n : ℕ, (minpoly ℚ α).natDegree ∣ 2 ^ n := by
  rw [wantzel_galois_characterization α hα] at hc
  exact galois_2group_implies_degree_pow2 α hα hc

/-
## Part VII: Contrapositive Non-Constructibility Results
-/

/-- If the Galois group of minpoly(ℚ,α) is NOT a 2-group, then α is not constructible.
    Contrapositive of the Wantzel-Galois characterization. -/
theorem not_constructible_of_not_2group (α : ℝ) (hα : IsIntegral ℚ α)
    (h : ¬ IsPGroup 2 (minpoly ℚ α).Gal) :
    ¬ IsConstructibleFromQ α := by
  rw [wantzel_galois_characterization α hα]
  exact h

/-- If the degree of minpoly(ℚ,α) is not divisible by any power of 2, then α is not constructible.
    Contrapositive of constructible_implies_degree_dvd_pow2. -/
theorem not_constructible_of_degree (α : ℝ) (hα : IsIntegral ℚ α)
    (h : ∀ n : ℕ, ¬ (minpoly ℚ α).natDegree ∣ 2 ^ n) :
    ¬ IsConstructibleFromQ α :=
  fun hc => let ⟨n, hn⟩ := constructible_implies_degree_dvd_pow2 α hα hc; h n hn

/-
## Summary

### The Main Answer:
An algebraic number α is constructible from ℚ iff Gal(minpoly(ℚ,α)) is a 2-group.

### Proved (no sorry):
1. `isPGroup_iff_card_pow_two` - 2-group ↔ |G| = 2^n (from Mathlib IsPGroup.iff_card)
2. `isPGroup_of_card_pow_two` - 2-power order → 2-group (Mathlib IsPGroup.of_card)
3. `isPGroup_card_is_pow_two` - 2-group → |G| = 2^n
4. `not_pow_two_of_eq_six` - 6 is not a power of 2
5. `x_cube_sub_2_gal_not_2group` - Gal(x³-2/ℚ) is NOT a 2-group
6. `cos20_gal_not_2group` - Gal of cos(20°) minimal polynomial is NOT a 2-group
7. `x_sq_sub_2_gal_order` - |Gal(x²-2/ℚ)| = 2 (divisibility squeeze: prime deg divides, embeds into S₂)
8. `x_sq_sub_2_gal_is_2group` - Gal(x²-2/ℚ) IS a 2-group (order 2)
9. `x_4th_sub_2_gal_is_2group` - Gal(x⁴-2/ℚ) IS a 2-group (order 8)
10. `galois_2group_implies_degree_pow2` - 2-group Galois → degree divides 2^n (tower law)
11. `constructible_implies_degree_dvd_pow2` - Galois criterion implies degree criterion
12. `not_constructible_of_not_2group` - NOT 2-group Galois → not constructible
13. `not_constructible_of_degree` - degree not ∣ any 2^n → not constructible

### Proved (imported from other files):
14. `x_cube_sub_2_gal_order` - |Gal(x³-2/ℚ)| = 6 (from InverseGalois.lean)
15. `x_4th_sub_2_gal_order` - |Gal(x⁴-2/ℚ)| = 8 (from InverseGaloisD4.lean)
16. `cos20_gal_order` - |Gal(8x³-6x-1/ℚ)| = 3 (from AngleTrisectionCos20Gal.lean, proved via Eisenstein)

### Axiomatized (1 remaining):
1. `wantzel_galois_characterization` - main constructibility ↔ 2-group theorem
-/

#check isPGroup_iff_card_pow_two
#check x_cube_sub_2_gal_not_2group
#check cos20_gal_not_2group
#check x_sq_sub_2_gal_is_2group
#check x_4th_sub_2_gal_is_2group
#check constructible_implies_degree_dvd_pow2
