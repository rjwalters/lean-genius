/-
Chinese Remainder Theorem — Weakening Coprimality (OQ-04-OQ-03)

**Question**: Can the pairwise coprimality condition in the list CRT (OQ-04) be weakened?

**Answer**: YES. The necessary and sufficient condition for solvability is *pairwise
GCD compatibility*: for each pair of congruences x ≡ aᵢ (mod mᵢ) and x ≡ aⱼ (mod mⱼ),
the system has a solution if and only if gcd(mᵢ, mⱼ) ∣ (aᵢ - aⱼ) for all pairs i, j.

This strictly generalizes OQ-04's coprime requirement:
- If all moduli are pairwise coprime, gcd = unit divides everything automatically.
- But many non-coprime systems are also solvable (gcd divides the difference).
- And some non-coprime systems are NOT solvable (gcd does not divide the difference).

**Generalized Uniqueness**: When a solution exists, it is unique modulo lcm(m₁,...,mₖ).
For coprime moduli, lcm = product, recovering OQ-04's uniqueness.

This file references the complete proofs in:
- `ChineseRemainderNonCoprimeList.lean` (ed_crt_list_iff, ed_crt_list_unique)
-/

import Proofs.ChineseRemainderNonCoprimeList

namespace CRTWeakenedCoprimality

open ChineseRemainderNonCoprimeList

variable {R : Type*} [EuclideanDomain R] [DecidableEq R]

/-!
## Main Theorem

The pairwise GCD compatibility condition is both necessary and sufficient.
-/

/-- **OQ-04-OQ-03 Main Theorem**: Non-coprime CRT for lists (iff).

    A system of congruences mᵢ ∣ (x - aᵢ) over a Euclidean domain
    is solvable iff gcd(mᵢ, mⱼ) ∣ (aᵢ - aⱼ) for all pairs i, j.

    This weakens OQ-04's coprimality to compatibility. -/
theorem non_coprime_crt_list_iff {sys : System R} :
    (∃ x : R, Satisfies x sys) ↔ Compatible sys :=
  ed_crt_list_iff

/-- **Uniqueness**: Any two solutions agree modulo lcm of all moduli. -/
theorem non_coprime_crt_list_unique {sys : System R} {x y : R}
    (hx : Satisfies x sys) (hy : Satisfies y sys) :
    listLcm (moduli sys) ∣ (x - y) :=
  ed_crt_list_unique hx hy

/-!
## Connection to OQ-04: Coprimality Suffices
-/

/-- **Coprimality ⟹ Compatibility**: Coprime moduli satisfy the GCD condition automatically,
    so OQ-04's coprime CRT is a special case of OQ-04-OQ-03's non-coprime CRT. -/
theorem crt_list_from_coprime {sys : System R}
    (hpc : ∀ p q, p ∈ sys → q ∈ sys → p ≠ q →
      IsUnit (EuclideanDomain.gcd p.2 q.2)) :
    ∃ x : R, Satisfies x sys :=
  non_coprime_crt_list_iff.mpr
    (ChineseRemainderNonCoprimeList.coprime_implies_compatible hpc)

/-!
## Concrete Examples in ℤ
-/

/-- The system x ≡ 2 (mod 6), x ≡ 4 (mod 10) is **compatible**:
    gcd(6, 10) = 2 divides 4 - 2 = 2. Solution: x = 14. -/
example : ∃ x : ℤ, (6 : ℤ) ∣ (x - 2) ∧ (10 : ℤ) ∣ (x - 4) :=
  ⟨14, ⟨2, by norm_num⟩, ⟨1, by norm_num⟩⟩

/-- The system x ≡ 1 (mod 6), x ≡ 4 (mod 10) is **unsolvable**:
    gcd(6, 10) = 2 does NOT divide 4 - 1 = 3 (odd). -/
example : ¬ ∃ x : ℤ, (6 : ℤ) ∣ (x - 1) ∧ (10 : ℤ) ∣ (x - 4) := by
  rintro ⟨x, ⟨a, ha⟩, ⟨b, hb⟩⟩
  -- x = 1 + 6a and x = 4 + 10b, so 1 + 6a = 4 + 10b
  -- 6a - 10b = 3, i.e. 2(3a - 5b) = 3: impossible (even ≠ odd)
  omega

/-!
## Summary

OQ-04-OQ-03 is **resolved** (0 axioms, 0 sorries):

The pairwise coprimality condition CAN be weakened to pairwise GCD compatibility:
- `non_coprime_crt_list_iff`: solvable ↔ compatible (complete iff)
- `non_coprime_crt_list_unique`: solution is unique mod lcm of moduli
- `crt_list_from_coprime`: coprime case is a special case (OQ-04 ⊆ OQ-04-OQ-03)

The full proof is in `ChineseRemainderNonCoprimeList.lean` (0 axioms, 0 sorries).
-/

#check @non_coprime_crt_list_iff
#check @non_coprime_crt_list_unique
#check @crt_list_from_coprime

end CRTWeakenedCoprimality
