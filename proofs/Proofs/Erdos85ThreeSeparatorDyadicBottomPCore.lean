import Proofs.Erdos85ThreeSeparatorDyadicBottomResidue
import Proofs.Erdos85ThreeSeparatorBottomPCoreProfiles

/-!
# Dyadic selection of the bottom P-core profile

For a bottom slice, `q` is either `3a+4` or `3a+5`.  The residue of the
actual binary parameter `q=2^k` selects exactly one alternative: even
exponents give the unit P-core budget and odd exponents give the zero
budget.  This removes the auxiliary quotient `r` from downstream use.
-/

namespace Erdos85

/-- Named form of the six-way singleton P-core profile. -/
def PcoreSixOneHot (d0 d1 d2 g0 g1 g2 : ℕ) : Prop :=
  (d0 = 1 ∧ d1 = 0 ∧ d2 = 0 ∧ g0 = 0 ∧ g1 = 0 ∧ g2 = 0) ∨
  (d0 = 0 ∧ d1 = 1 ∧ d2 = 0 ∧ g0 = 0 ∧ g1 = 0 ∧ g2 = 0) ∨
  (d0 = 0 ∧ d1 = 0 ∧ d2 = 1 ∧ g0 = 0 ∧ g1 = 0 ∧ g2 = 0) ∨
  (d0 = 0 ∧ d1 = 0 ∧ d2 = 0 ∧ g0 = 1 ∧ g1 = 0 ∧ g2 = 0) ∨
  (d0 = 0 ∧ d1 = 0 ∧ d2 = 0 ∧ g0 = 0 ∧ g1 = 1 ∧ g2 = 0) ∨
  (d0 = 0 ∧ d1 = 0 ∧ d2 = 0 ∧ g0 = 0 ∧ g1 = 0 ∧ g2 = 1)

/-- Even exponent parity selects `q=3a+4` from the two bottom equations. -/
theorem dyadic_bottom_even_selects_three_a_add_four
    (q a k : ℕ) (hq : q = 2 ^ k) (hk : Even k)
    (hbottom : q = 3 * a + 4 ∨ q = 3 * a + 5) :
    q = 3 * a + 4 := by
  obtain ⟨r, hr⟩ := twoPow_exists_three_mul_add_one_of_even k hk
  rcases hbottom with hfour | hfive
  · exact hfour
  · exfalso
    omega

/-- Odd exponent parity selects `q=3a+5` from the two bottom equations. -/
theorem dyadic_bottom_odd_selects_three_a_add_five
    (q a k : ℕ) (hq : q = 2 ^ k) (hk : Odd k)
    (hbottom : q = 3 * a + 4 ∨ q = 3 * a + 5) :
    q = 3 * a + 5 := by
  obtain ⟨r, hr⟩ := twoPow_exists_three_mul_add_two_of_odd k hk
  rcases hbottom with hfour | hfive
  · exfalso
    omega
  · exact hfive

/-- Even dyadic exponents force the exact one-hot P-core profile. -/
theorem dyadic_bottom_even_Pcore_oneHot
    (q a b k m0 m1 m2 d0 d1 d2 g0 g1 g2 : ℕ)
    (hq : q = 2 ^ k)
    (hk : Even k)
    (hbottom : q = 3 * a + 4 ∨ q = 3 * a + 5)
    (hab : a + b = q - 1)
    (hmass : m0 + m1 + m2 = 2 * q - 4)
    (h0 : d0 + g0 + b = m0 + 2)
    (h1 : d1 + g1 + b = m1 + 2)
    (h2 : d2 + g2 + b = m2 + 2) :
    PcoreSixOneHot d0 d1 d2 g0 g1 g2 := by
  have hsel := dyadic_bottom_even_selects_three_a_add_four
    q a k hq hk hbottom
  have h := bottomPCore_threeOne_exactly_one
    q a b (a + 1) m0 m1 m2 d0 d1 d2 g0 g1 g2
    (by omega) (by omega) (by omega) hab hmass h0 h1 h2
  simpa [PcoreSixOneHot] using h

/-- Odd dyadic exponents force the completely empty P-core profile. -/
theorem dyadic_bottom_odd_Pcore_all_zero
    (q a b k m0 m1 m2 d0 d1 d2 g0 g1 g2 : ℕ)
    (hq : q = 2 ^ k)
    (hk : Odd k)
    (hbottom : q = 3 * a + 4 ∨ q = 3 * a + 5)
    (hab : a + b = q - 1)
    (hmass : m0 + m1 + m2 = 2 * q - 4)
    (h0 : d0 + g0 + b = m0 + 2)
    (h1 : d1 + g1 + b = m1 + 2)
    (h2 : d2 + g2 + b = m2 + 2) :
    d0 = 0 ∧ d1 = 0 ∧ d2 = 0 ∧ g0 = 0 ∧ g1 = 0 ∧ g2 = 0 := by
  have hsel := dyadic_bottom_odd_selects_three_a_add_five
    q a k hq hk hbottom
  exact bottomPCore_threeTwo_all_zero
    q a b (a + 1) m0 m1 m2 d0 d1 d2 g0 g1 g2
    (by omega) (by omega) (by omega) hab hmass h0 h1 h2

end Erdos85

#print axioms Erdos85.dyadic_bottom_even_selects_three_a_add_four
#print axioms Erdos85.dyadic_bottom_odd_selects_three_a_add_five
#print axioms Erdos85.dyadic_bottom_even_Pcore_oneHot
#print axioms Erdos85.dyadic_bottom_odd_Pcore_all_zero
