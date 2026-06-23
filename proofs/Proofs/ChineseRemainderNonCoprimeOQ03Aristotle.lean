/-
  Aristotle targets for CRT Non-Coprime OQ-03
  Helper lemmas for proving the GCD-LCM distributive law:
    gcd(lcm(a,b), c) | lcm(gcd(a,c), gcd(b,c))
  in a general EuclideanDomain.

  See ChineseRemainderNonCoprimeOQ03.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture
  - Known results likely provable from Mathlib
  - Clean theorem statements with no definition sorries
  - No axioms

  Proof strategy for the main sorry (gcd_lcm_dvd_lcm_gcd):
  Let d = gcd(lcm(a,b), c), M = lcm(gcd(a,c), gcd(b,c)).
  Easy direction (proved): M | d.
  Hard direction (sorry): d | M.
  Key reduction: M | lcm(a,b) and M | c, so define V = lcm(a,b)/M, W = c/M.
  Then d = M * gcd(V,W) (by gcd_mul_left). The hard direction reduces to
  showing gcd(V,W) is a unit, i.e., IsCoprime V W. This follows from
  min(max(x,y), z) = max(min(x,z), min(y,z)) at each prime valuation,
  but requires UniqueFactorizationMonoid machinery to formalize.
-/
import Mathlib

set_option linter.unusedSectionVars false

namespace CRTOQ03Helpers

variable {R : Type*} [EuclideanDomain R] [DecidableEq R]

/-
## Part 1: Coprimality from GCD factorization

Key helper: if g = gcd(a,b) ≠ 0 and a = g*α, b = g*β, then IsCoprime α β.
This follows from Bézout's identity and cancellation.
-/

/-- If g ≠ 0 and g * x = g * y then x = y. (Cancellation in integral domain.) -/
theorem mul_left_cancel_of_ne_zero {g x y : R} (hg : g ≠ 0)
    (h : g * x = g * y) : x = y :=
  mul_left_cancel₀ hg h

/-- Bézout factoring: gcd(a,b) = a * gcdA + b * gcdB implies
    if a = g*α and b = g*β and gcd(a,b) = g and g ≠ 0, then
    α * gcdA(a,b) + β * gcdB(a,b) = 1. -/
theorem bezout_coprime_factors {a b g α β : R} (hg : g ≠ 0)
    (hα : a = g * α) (hβ : b = g * β)
    (hgcd : EuclideanDomain.gcd a b = g) :
    α * EuclideanDomain.gcdA a b + β * EuclideanDomain.gcdB a b = 1 := by
  have hbez := EuclideanDomain.gcd_eq_gcd_ab a b
  -- Factor out g from the Bézout identity
  have h1 : a * EuclideanDomain.gcdA a b = g * (α * EuclideanDomain.gcdA a b) := by
    rw [hα]; ring
  have h2 : b * EuclideanDomain.gcdB a b = g * (β * EuclideanDomain.gcdB a b) := by
    rw [hβ]; ring
  apply mul_left_cancel₀ hg
  rw [mul_one]
  -- Goal: g * (α * gcdA a b + β * gcdB a b) = g
  symm
  calc g = EuclideanDomain.gcd a b := hgcd.symm
    _ = a * EuclideanDomain.gcdA a b + b * EuclideanDomain.gcdB a b := hbez
    _ = g * (α * EuclideanDomain.gcdA a b) + g * (β * EuclideanDomain.gcdB a b) := by
        rw [h1, h2]
    _ = g * (α * EuclideanDomain.gcdA a b + β * EuclideanDomain.gcdB a b) := by ring

/-- If g | a and g | b and gcd(a,b) = g and g ≠ 0, then the
    quotients a/g and b/g are coprime. -/
theorem isCoprime_of_gcd_factoring {a b g α β : R} (hg : g ≠ 0)
    (hα : a = g * α) (hβ : b = g * β)
    (hgcd : EuclideanDomain.gcd a b = g) :
    IsCoprime α β :=
  ⟨EuclideanDomain.gcdA a b, EuclideanDomain.gcdB a b, by
    convert bezout_coprime_factors hg hα hβ hgcd using 1; ring⟩

/-
## Part 2: Cancellation and divisibility in EuclideanDomain
-/

/-- In an integral domain, a * b | a * c with a ≠ 0 implies b | c. -/
theorem dvd_of_mul_dvd_mul_left_ne_zero {a b c : R} (ha : a ≠ 0)
    (h : a * b ∣ a * c) : b ∣ c :=
  (mul_dvd_mul_iff_left ha).mp h

/-- If d ≠ 0 and d * x | d * y * z, then x | y * z. -/
theorem dvd_of_mul_dvd_mul_left_assoc {d x y z : R} (hd : d ≠ 0)
    (h : d * x ∣ d * (y * z)) : x ∣ y * z :=
  dvd_of_mul_dvd_mul_left_ne_zero hd h

/-
## Part 3: Coprimality inheritance

Key pattern used repeatedly in the GCD-LCM distributive law proof:
if gcd(x,y) = d and x = d*x' and y = d*y', then IsCoprime x' y'.
-/

/-- If d divides both x and y with x = d*x', y = d*y', gcd(x,y) = d,
    and d ≠ 0, then x' and y' are coprime.
    (Same as isCoprime_of_gcd_factoring but stated more generally.) -/
theorem isCoprime_quotients_of_gcd {x y d x' y' : R} (hd : d ≠ 0)
    (hx : x = d * x') (hy : y = d * y')
    (hgcd : EuclideanDomain.gcd x y = d) :
    IsCoprime x' y' :=
  isCoprime_of_gcd_factoring hd hx hy hgcd

/-
## Part 4: IsCoprime inheritance through gcd

If IsCoprime α β, then gcd(c,α) and gcd(c,β) are coprime.
This is because any common divisor of gcd(c,α) and gcd(c,β)
divides both α and β, hence is a unit.
-/

/-- If IsCoprime α β, then gcd(c,α) and gcd(c,β) are coprime. -/
theorem isCoprime_gcd_of_isCoprime {α β c : R}
    (hcop : IsCoprime α β) :
    IsCoprime (EuclideanDomain.gcd c α) (EuclideanDomain.gcd c β) := by
  obtain ⟨u, v, huv⟩ := hcop
  obtain ⟨α', hα'⟩ := EuclideanDomain.gcd_dvd_right c α
  obtain ⟨β', hβ'⟩ := EuclideanDomain.gcd_dvd_right c β
  refine ⟨α' * u, β' * v, ?_⟩
  have h1 : α = EuclideanDomain.gcd c α * α' := hα'
  have h2 : β = EuclideanDomain.gcd c β * β' := hβ'
  have h3 : u * α + v * β = 1 := huv
  calc (α' * u) * EuclideanDomain.gcd c α + (β' * v) * EuclideanDomain.gcd c β
      = u * (EuclideanDomain.gcd c α * α') + v * (EuclideanDomain.gcd c β * β') := by ring
    _ = u * α + v * β := by rw [← h1, ← h2]
    _ = 1 := h3

/-
## Part 5: IsCoprime.mul_dvd applications
-/

/-- If x | lcm(p,q) and y | lcm(p,q) and IsCoprime x y, then x*y | lcm(p,q). -/
theorem coprime_mul_dvd_lcm {x y p q : R}
    (hcop : IsCoprime x y)
    (hx : x ∣ EuclideanDomain.lcm p q)
    (hy : y ∣ EuclideanDomain.lcm p q) :
    x * y ∣ EuclideanDomain.lcm p q :=
  hcop.mul_dvd hx hy

/-- Product of coprime divisors: if a | p and b | q and IsCoprime a b,
    then a*b | lcm(p,q). -/
theorem coprime_dvd_factors_dvd_lcm {a b p q : R}
    (hcop : IsCoprime a b)
    (ha : a ∣ p)
    (hb : b ∣ q) :
    a * b ∣ EuclideanDomain.lcm p q :=
  hcop.mul_dvd (dvd_trans ha (EuclideanDomain.dvd_lcm_left p q))
    (dvd_trans hb (EuclideanDomain.dvd_lcm_right p q))

/-
## Part 6: Key divisibility chains for the distributive law

gcd(c, α) | gcd(a, c) when a = g * α (since gcd(c,α) | α | g*α = a and gcd(c,α) | c).
-/

/-- If a = g * α then gcd(c, α) | gcd(a, c). -/
theorem gcd_factor_dvd_gcd {a c g α : R}
    (hα : a = g * α) :
    EuclideanDomain.gcd c α ∣ EuclideanDomain.gcd a c := by
  apply EuclideanDomain.dvd_gcd
  · calc EuclideanDomain.gcd c α ∣ α := EuclideanDomain.gcd_dvd_right c α
      _ ∣ g * α := dvd_mul_left α g
      _ = a := hα.symm
  · exact EuclideanDomain.gcd_dvd_left c α

/-- Dual: if a = g * α then gcd(c, g) | gcd(a, c). -/
theorem gcd_common_factor_dvd_gcd {a c g α : R}
    (hα : a = g * α) :
    EuclideanDomain.gcd c g ∣ EuclideanDomain.gcd a c := by
  apply EuclideanDomain.dvd_gcd
  · calc EuclideanDomain.gcd c g ∣ g := EuclideanDomain.gcd_dvd_right c g
      _ ∣ g * α := dvd_mul_right g α
      _ = a := hα.symm
  · exact EuclideanDomain.gcd_dvd_left c g

/-
## Part 7: Partial result for the distributive law

Using gcd_mul_dvd_mul_gcd and coprime factoring, we can show:
gcd(c, α)*gcd(c, β) | lcm(gcd(a,c), gcd(b,c))
when a = g*α, b = g*β, IsCoprime α β.

This is a KEY partial result: it handles the "coprime part" of the
distributive law. The remaining difficulty is handling the shared
factor g, which requires UniqueFactorizationMonoid machinery.
-/

/-- Coprime part of the distributive law: if a = g*α, b = g*β with
    IsCoprime α β, then gcd(c,α)*gcd(c,β) | lcm(gcd(a,c), gcd(b,c)). -/
theorem coprime_gcd_dvd_lcm_gcd {a b c g α β : R}
    (hα : a = g * α) (hβ : b = g * β) (hcop : IsCoprime α β) :
    EuclideanDomain.gcd c α * EuclideanDomain.gcd c β ∣
    EuclideanDomain.lcm (EuclideanDomain.gcd a c) (EuclideanDomain.gcd b c) := by
  apply coprime_dvd_factors_dvd_lcm
  · exact isCoprime_gcd_of_isCoprime hcop
  · exact gcd_factor_dvd_gcd hα
  · exact gcd_factor_dvd_gcd hβ

/-
## Part 8: Key result bridging product to lcm

The main file proves: gcd(lcm(a,b), c) | gcd(a,c) * gcd(b,c) (via Bézout).
The easy direction gives: lcm(gcd(a,c), gcd(b,c)) | gcd(lcm(a,b), c).
Combined with gcd(p,q) * lcm(p,q) = p * q, the remaining gap is:
  gcd(lcm(a,b), c) | lcm(gcd(a,c), gcd(b,c))
which requires showing that the quotient gcd(lcm(a,b),c) / lcm(gcd(a,c),gcd(b,c))
is a unit. This is equivalent to the divisibility lattice being distributive.
-/

/-- If M | d and G | d and d | G * M and G ≠ 0, then d/G | M. -/
theorem dvd_div_of_dvd_mul {d G M : R} (hG_ne : G ≠ 0)
    (hGd : G ∣ d) (hdGM : d ∣ G * M) :
    ∃ d₁ : R, d = G * d₁ ∧ d₁ ∣ M := by
  obtain ⟨d₁, hd₁⟩ := hGd
  refine ⟨d₁, hd₁, ?_⟩
  rw [hd₁] at hdGM
  exact (mul_dvd_mul_iff_left hG_ne).mp hdGM

/-- gcd(gcd(a,c), gcd(b,c)) divides gcd(lcm(a,b), c). This follows from
    gcd(gcd(a,c), gcd(b,c)) dividing both lcm(a,b) (via a and b) and c. -/
theorem gcd_gcd_dvd_gcd_lcm (a b c : R) :
    EuclideanDomain.gcd (EuclideanDomain.gcd a c) (EuclideanDomain.gcd b c) ∣
    EuclideanDomain.gcd (EuclideanDomain.lcm a b) c := by
  apply EuclideanDomain.dvd_gcd
  · -- gcd(gcd(a,c), gcd(b,c)) | lcm(a,b)
    -- It divides a (via gcd(a,c) | a) and b (via gcd(b,c) | b)
    -- So it divides lcm(a,b) since both a | lcm and b | lcm
    exact dvd_trans
      (dvd_trans (EuclideanDomain.gcd_dvd_left _ _) (EuclideanDomain.gcd_dvd_left a c))
      (EuclideanDomain.dvd_lcm_left a b)
  · -- gcd(gcd(a,c), gcd(b,c)) | c (via gcd(a,c) | c)
    exact dvd_trans (EuclideanDomain.gcd_dvd_left _ _) (EuclideanDomain.gcd_dvd_right a c)

end CRTOQ03Helpers
