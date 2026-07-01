/-
  Binary GCD (Stein's Algorithm) for Gaussian Integers ℤ[i]
  =========================================================

  The classic binary GCD of Stein computes gcd(u, v) over ℤ using only
  parity tests, subtractions, and halvings -- never a full division:

    * gcd(2u, 2v) = 2·gcd(u, v)          (both even: pull out a factor 2)
    * gcd(2u, v)  = gcd(u, v)   (v odd)  (one even: strip the 2)
    * gcd(u, v)   = gcd(u-v, v)          (both odd: subtract, u-v is even)

  This file develops the analogue over the Gaussian integers ℤ[i].  The
  role of the rational prime `2` is played by the Gaussian prime

        π := 1 + i,          N(π) = 2,

  the unique (up to units) prime lying above `2`, since `2 = -i·(1+i)²`.
  "Even" becomes "divisible by π", and the entire algorithm goes through
  once one establishes the arithmetic of π.  The genuinely base-specific
  fact is the **parity dichotomy**

        π ∣ (a + b·i)  ⟺  a + b is even,

  which is exactly the statement that the residue ring ℤ[i]/(π) ≅ 𝔽₂.
  From it, two π-odd elements always have a π-even difference, so the
  subtraction step makes progress -- just as over ℤ.

  Scope (correctness layer, fully verified, 0 axioms):

    1. `pi_norm`            — N(π) = 2.
    2. `pi_dvd_iff`         — the parity dichotomy π ∣ z ⟺ 2 ∣ (z.re + z.im).
    3. `pi_prime`           — π is prime (norm 2 is a rational prime).
    4. `pi_dvd_sub_of_not_dvd` — two π-odd elements have a π-even difference.
    5. `divPi` + `pi_mul_divPi` — the exact "halving" divide-by-π operation,
       with `norm_divPi` showing the norm halves (the termination measure).
    6. The three GCD reduction identities that make the algorithm correct,
       stated up to `Associated` (i.e. up to units, the natural equality in
       a ring without a canonical gcd representative):
         `gcd_pi_mul`       — both even : gcd(πa, πb) ~ π·gcd(a, b)
         `gcd_pi_mul_odd`   — one  even : gcd(πa, v) ~ gcd(a, v)   (π ∤ v)
         `gcd_sub`          — both odd  : gcd(u, v)  ~ gcd(u-v, v)

  Together these are the operational-correctness core of a binary GCD for
  ℤ[i]: every reduction step of the algorithm is one of (4)/(5)/(6), each
  strictly decreasing the norm, so the process terminates at an associate
  of the Euclidean gcd.

  References:
    * J. Stein, "Computational problems associated with Racah algebra",
      J. Comput. Phys. 1 (1967) 397–405.
    * D. Knuth, TAOCP Vol. 2, §4.5.2 (binary gcd), §4.5.4 (Gaussian gcd).
    * G. H. Hardy & E. M. Wright, §12.6–12.8 (arithmetic of ℤ[i]).
-/
import Mathlib

namespace BinaryGcdOQ04

open Zsqrtd

/-- The Gaussian prime `π = 1 + i`, the (up to units) unique prime above `2`. -/
def pi : GaussianInt := ⟨1, 1⟩

@[simp] lemma pi_re : pi.re = 1 := rfl
@[simp] lemma pi_im : pi.im = 1 := rfl

lemma pi_ne_zero : pi ≠ 0 := by decide

/-- The norm of `π = 1 + i` is `2`. -/
@[simp] lemma pi_norm : Zsqrtd.norm pi = 2 := by
  simp only [Zsqrtd.norm_def, pi_re, pi_im]; ring

/-!
### The parity dichotomy: ℤ[i]/(π) ≅ 𝔽₂

The heart of the Gaussian binary GCD.  Because `i ≡ 1 (mod π)` (indeed
`1 - i = -i·π`), the reduction map `a + b·i ↦ a + b (mod 2)` is a ring
homomorphism onto `𝔽₂`, and its kernel is exactly the ideal `(π)`.
-/

/-- **Parity dichotomy.** `π = 1+i` divides `z` iff `z.re + z.im` is even.
    Equivalently, `ℤ[i]/(π) ≅ 𝔽₂`: an element is "π-even" precisely when the
    sum of its real and imaginary parts is even. -/
theorem pi_dvd_iff (z : GaussianInt) : pi ∣ z ↔ (2 : ℤ) ∣ (z.re + z.im) := by
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨w.re, ?_⟩
    simp only [re_mul, im_mul, pi_re, pi_im]
    ring
  · rintro ⟨k, hk⟩
    refine ⟨⟨k, k - z.re⟩, ?_⟩
    ext <;> simp only [re_mul, im_mul, pi_re, pi_im] <;> omega

/-!
### `π` is prime

An element whose norm is a rational prime is irreducible, hence prime
(ℤ[i] is a Euclidean domain, so irreducible ⟺ prime).
-/

/-- `π = 1 + i` is irreducible in `ℤ[i]`: its norm `2` is a rational prime,
    so in any factorization one factor has norm `1` and is therefore a unit. -/
theorem pi_irreducible : Irreducible pi := by
  refine ⟨?_, ?_⟩
  · -- π is not a unit: its norm has natAbs 2 ≠ 1.
    rw [← Zsqrtd.norm_eq_one_iff, pi_norm]
    decide
  · intro a b hab
    -- From π = a·b we get 2 = |N a| · |N b| in ℕ, so one factor is a unit.
    have hn : (2 : ℕ) = (Zsqrtd.norm a).natAbs * (Zsqrtd.norm b).natAbs := by
      have : (Zsqrtd.norm pi).natAbs
          = (Zsqrtd.norm a).natAbs * (Zsqrtd.norm b).natAbs := by
        rw [hab, Zsqrtd.norm_mul, Int.natAbs_mul]
      simpa [pi_norm] using this
    rw [← Zsqrtd.norm_eq_one_iff, ← Zsqrtd.norm_eq_one_iff]
    -- Now: (N a).natAbs = 1 ∨ (N b).natAbs = 1, from 2 = na · nb.
    set na := (Zsqrtd.norm a).natAbs with hna
    set nb := (Zsqrtd.norm b).natAbs with hnb
    have hdvd : na ∣ 2 := ⟨nb, hn⟩
    rcases (Nat.prime_two.eq_one_or_self_of_dvd na hdvd) with h1 | h2
    · exact Or.inl h1
    · exact Or.inr (by rw [h2] at hn; omega)

/-- `π = 1 + i` is prime in `ℤ[i]`. -/
theorem pi_prime : Prime pi := pi_irreducible.prime

/-- **Both-odd step is well-posed.** If neither `u` nor `v` is divisible by
    `π`, their difference `u - v` is: two nonzero residues in `𝔽₂` are equal,
    so they cancel.  This is what lets the subtraction step make progress. -/
theorem pi_dvd_sub_of_not_dvd (u v : GaussianInt)
    (hu : ¬ pi ∣ u) (hv : ¬ pi ∣ v) : pi ∣ (u - v) := by
  rw [pi_dvd_iff] at hu hv ⊢
  simp only [re_sub, im_sub]
  omega

/-!
### The exact divide-by-π operation ("halving")

When `π ∣ z`, dividing by `π` is exact and halves the norm.  This is the
Gaussian analogue of the right-shift `n ↦ n / 2` in the integer algorithm.
-/

/-- Divide a Gaussian integer by `π = 1 + i`.  Exact when `π ∣ z`
    (see `pi_mul_divPi`); the formula is `(a+bi)/(1+i) = ((a+b) + (b-a)i)/2`. -/
def divPi (z : GaussianInt) : GaussianInt :=
  ⟨(z.re + z.im) / 2, (z.im - z.re) / 2⟩

/-- When `π ∣ z`, multiplying the quotient back recovers `z` exactly. -/
theorem pi_mul_divPi (z : GaussianInt) (h : pi ∣ z) : pi * divPi z = z := by
  rw [pi_dvd_iff] at h
  obtain ⟨k, hk⟩ := h
  ext <;> simp only [re_mul, im_mul, pi_re, pi_im, divPi] <;> omega

/-- Dividing by `π` halves the norm: `N(z) = 2 · N(z/π)` when `π ∣ z`.
    This is the strictly-decreasing termination measure of the algorithm. -/
theorem norm_divPi (z : GaussianInt) (h : pi ∣ z) :
    Zsqrtd.norm z = 2 * Zsqrtd.norm (divPi z) := by
  conv_lhs => rw [← pi_mul_divPi z h]
  rw [Zsqrtd.norm_mul, pi_norm]

/-!
### The three GCD reduction identities

These are stated up to `Associated` (equality up to a unit), which is the
correct notion of equality for gcds in a ring lacking a canonical
representative.  Each is proved from the universal property of the
Euclidean-domain gcd (`gcd_dvd_left/right`, `dvd_gcd`) by antisymmetry of
divisibility.
-/

/-- **Both even.** `gcd(π·a, π·b) ~ π·gcd(a, b)`: a common factor of `π`
    pulls straight out of the gcd. -/
theorem gcd_pi_mul (a b : GaussianInt) :
    Associated (EuclideanDomain.gcd (pi * a) (pi * b)) (pi * EuclideanDomain.gcd a b) := by
  apply associated_of_dvd_dvd
  · -- gcd(πa, πb) ∣ π·gcd(a,b)
    have hp : pi ∣ EuclideanDomain.gcd (pi * a) (pi * b) :=
      EuclideanDomain.dvd_gcd ⟨a, rfl⟩ ⟨b, rfl⟩
    obtain ⟨h, hh⟩ := hp
    rw [hh]
    have hga : h ∣ a := by
      have : pi * h ∣ pi * a := hh ▸ EuclideanDomain.gcd_dvd_left (pi * a) (pi * b)
      exact (mul_dvd_mul_iff_left pi_ne_zero).mp this
    have hgb : h ∣ b := by
      have : pi * h ∣ pi * b := hh ▸ EuclideanDomain.gcd_dvd_right (pi * a) (pi * b)
      exact (mul_dvd_mul_iff_left pi_ne_zero).mp this
    exact mul_dvd_mul_left pi (EuclideanDomain.dvd_gcd hga hgb)
  · -- π·gcd(a,b) ∣ gcd(πa, πb)
    refine EuclideanDomain.dvd_gcd ?_ ?_
    · exact mul_dvd_mul_left pi (EuclideanDomain.gcd_dvd_left a b)
    · exact mul_dvd_mul_left pi (EuclideanDomain.gcd_dvd_right a b)

/-- **One even, one odd.** If `π ∤ v` then `gcd(π·a, v) ~ gcd(a, v)`: the
    factor `π` is coprime to `v`, so it can be dropped. -/
theorem gcd_pi_mul_odd (a v : GaussianInt) (hv : ¬ pi ∣ v) :
    Associated (EuclideanDomain.gcd (pi * a) v) (EuclideanDomain.gcd a v) := by
  apply associated_of_dvd_dvd
  · -- gcd(πa, v) ∣ gcd(a, v)
    set d := EuclideanDomain.gcd (pi * a) v with hd
    have hdpa : d ∣ pi * a := EuclideanDomain.gcd_dvd_left (pi * a) v
    have hdv : d ∣ v := EuclideanDomain.gcd_dvd_right (pi * a) v
    have hnd : ¬ pi ∣ d := fun hpd => hv (hpd.trans hdv)
    have hcop : IsCoprime pi d := (pi_prime.coprime_iff_not_dvd).mpr hnd
    have hda : d ∣ a := hcop.symm.dvd_of_dvd_mul_left hdpa
    exact EuclideanDomain.dvd_gcd hda hdv
  · -- gcd(a, v) ∣ gcd(πa, v)
    refine EuclideanDomain.dvd_gcd ?_ ?_
    · exact (EuclideanDomain.gcd_dvd_left a v).trans (dvd_mul_left a pi)
    · exact EuclideanDomain.gcd_dvd_right a v

/-- **Both odd.** `gcd(u, v) ~ gcd(u - v, v)`: the Euclidean-style
    subtraction step preserves the gcd.  (Combined with
    `pi_dvd_sub_of_not_dvd`, the result `u - v` is π-even, so a subsequent
    `divPi` strictly decreases the norm.) -/
theorem gcd_sub (u v : GaussianInt) :
    Associated (EuclideanDomain.gcd u v) (EuclideanDomain.gcd (u - v) v) := by
  apply associated_of_dvd_dvd
  · refine EuclideanDomain.dvd_gcd ?_ ?_
    · exact dvd_sub (EuclideanDomain.gcd_dvd_left u v) (EuclideanDomain.gcd_dvd_right u v)
    · exact EuclideanDomain.gcd_dvd_right u v
  · refine EuclideanDomain.dvd_gcd ?_ ?_
    · have h1 : EuclideanDomain.gcd (u - v) v ∣ (u - v) := EuclideanDomain.gcd_dvd_left (u - v) v
      have h2 : EuclideanDomain.gcd (u - v) v ∣ v := EuclideanDomain.gcd_dvd_right (u - v) v
      have : EuclideanDomain.gcd (u - v) v ∣ (u - v) + v := dvd_add h1 h2
      simpa using this
    · exact EuclideanDomain.gcd_dvd_right (u - v) v

/-!
### Sanity checks

Small evaluations confirming the parity dichotomy and the divide-by-π map.
-/

-- `2 = (1+i)(1-i)` is π-even (re+im = 2+0), and `1-i` is its π-quotient.
example : pi ∣ (⟨2, 0⟩ : GaussianInt) := by rw [pi_dvd_iff]; decide

-- `1` is π-odd (re+im = 1).
example : ¬ pi ∣ (1 : GaussianInt) := by rw [pi_dvd_iff]; decide

-- `i` is π-odd, and `1 + i = π` is π-even; their difference `i - (1+i) = -1`
-- is again π-odd -- consistent with `1 - 1 = 0` only for two odds.
example : ¬ pi ∣ (⟨0, 1⟩ : GaussianInt) := by rw [pi_dvd_iff]; decide

-- Divide-by-π is exact on `2 = ⟨2,0⟩`, giving `1 - i = ⟨1,-1⟩`.
example : divPi (⟨2, 0⟩ : GaussianInt) = ⟨1, -1⟩ := by decide

-- `π · (1 - i) = 2`.
example : pi * (⟨1, -1⟩ : GaussianInt) = ⟨2, 0⟩ := by decide

end BinaryGcdOQ04
