import Proofs.Erdos85ThreeSeparatorDyadicBottomPCore

/-!
# Odd bottom-slice P-fiber saturation

For odd binary exponent, the bottom B51 P-core budget vanishes.  Since the
P-centered X-fiber deficit satisfies `f_w+g_w=a`, the vanishing of every
intersection degree `g_w` forces all three deficits to equal the full fiber
size `a`.  Thus all `3a` P-fiber points use their complementary separator
attachment.
-/

namespace Erdos85

/-- Odd dyadic parity forces all three P-fiber attachment deficits to
saturate, while retaining the full zero P-core conclusion. -/
theorem dyadic_odd_bottom_Pfiber_saturation
    (q a b k m0 m1 m2 d0 d1 d2 g0 g1 g2 f0 f1 f2 : ℕ)
    (hq : q = 2 ^ k)
    (hk : Odd k)
    (hbottom : q = 3 * a + 4 ∨ q = 3 * a + 5)
    (hab : a + b = q - 1)
    (hmass : m0 + m1 + m2 = 2 * q - 4)
    (h0 : d0 + g0 + b = m0 + 2)
    (h1 : d1 + g1 + b = m1 + 2)
    (h2 : d2 + g2 + b = m2 + 2)
    (hf0 : f0 + g0 = a)
    (hf1 : f1 + g1 = a)
    (hf2 : f2 + g2 = a) :
    d0 = 0 ∧ d1 = 0 ∧ d2 = 0 ∧
      g0 = 0 ∧ g1 = 0 ∧ g2 = 0 ∧
      f0 = a ∧ f1 = a ∧ f2 = a ∧ f0 + f1 + f2 = 3 * a := by
  have hzero := dyadic_bottom_odd_Pcore_all_zero
    q a b k m0 m1 m2 d0 d1 d2 g0 g1 g2
    hq hk hbottom hab hmass h0 h1 h2
  omega

/-- Subtraction-free B50′ confirms that a saturated deficit in an
`n=a+2` wing is equivalent to zero internal-K defect degree. -/
theorem oddBottom_saturated_Pfiber_reciprocity
    (a n d f : ℕ)
    (hn : n = a + 2)
    (hreciprocity : f + 2 = d + n) :
    (f = a ↔ d = 0) := by
  omega

end Erdos85

#print axioms Erdos85.dyadic_odd_bottom_Pfiber_saturation
#print axioms Erdos85.oddBottom_saturated_Pfiber_reciprocity
