/-
  # `ℤ[√d]` is a PID and a UFD for `d ∈ {-1, -2}` — and prime-norm irreducibility

  Open question (`bezout-identity-oq-02-oq-01-oq-02-oq-02-oq-03-oq-03`, the
  Euclidean-`ℤ[√d]`-family entry):

    > `ℤ[√d]` is a PID/UFD for `d ∈ {-1, -2}` from the uniform norm bound.

  The parent file `NormEuclideanZsqrtdFamilyOQ03` packaged a *uniform*
  nearest-lattice-point division making `ℤ[√d]` a **Euclidean domain** for every
  `-2 ≤ d < 0` (`euclideanDomain`), specialising to the Gaussian integers
  `ℤ[√-1]` and to `ℤ[√-2]`.  This file harvests the two standard structural
  consequences and adds one piece of genuine arithmetic.

  ## What we prove

  * `isPrincipalIdealRing` / `uniqueFactorizationMonoid` — for every
    `-2 ≤ d < 0`, the ring `ℤ[√d]` is a **principal ideal ring** and a
    **unique factorization monoid**, obtained from the parent's Euclidean
    structure via Mathlib's `EuclideanDomain.to_principal_ideal_domain` and
    `PrincipalIdealRing.to_uniqueFactorizationMonoid`.
  * Concrete corollaries for the two classical rings:
    `gaussianInt_isPrincipalIdealRing`, `gaussianInt_uniqueFactorizationMonoid`
    (`d = -1`) and `negTwo_isPrincipalIdealRing`,
    `negTwo_uniqueFactorizationMonoid` (`d = -2`).
  * `irreducible_of_prime_norm` — for **any** `d`, an element whose norm has
    prime natural absolute value is irreducible.  This is the genuinely
    arithmetic input (multiplicativity of the norm + `norm.natAbs = 1 ↔ unit`,
    both unconditional in `d`), valid well beyond the Euclidean range.
  * `prime_of_prime_norm` — combining the two, for `-2 ≤ d < 0` a prime-norm
    element is actually **prime** (irreducible ⟺ prime in the UFD).

  The PID/UFD step is pure Mathlib plumbing on top of the parent's Euclidean
  structure; the mathematical substance new to this file is the prime-norm
  irreducibility criterion and its UFD upgrade to primality.

  Status: PROVED — 0 sorries, 0 axioms, no `native_decide`.
  Tags: number-theory, quadratic-integers, euclidean-domain, pid, ufd
-/
import Proofs.NormEuclideanZsqrtdFamilyOQ03

open Zsqrtd

namespace NormEuclideanZsqrtdFamilyPIDUFD

variable {d : ℤ}

/-! ### Principal ideal ring and unique factorization, uniformly for `-2 ≤ d < 0` -/

/-- **`ℤ[√d]` is a principal ideal ring for every `-2 ≤ d < 0`.** Immediate from
the parent's Euclidean structure via `EuclideanDomain.to_principal_ideal_domain`. -/
theorem isPrincipalIdealRing (hd : d < 0) (hd2 : -2 ≤ d) :
    IsPrincipalIdealRing (ℤ√d) :=
  letI := NormEuclideanZsqrtdFamily.euclideanDomain d hd hd2
  inferInstance

/-- **`ℤ[√d]` is a unique factorization monoid for every `-2 ≤ d < 0`.** A PID is
a UFD: `PrincipalIdealRing.to_uniqueFactorizationMonoid`. -/
theorem uniqueFactorizationMonoid (hd : d < 0) (hd2 : -2 ≤ d) :
    letI := NormEuclideanZsqrtdFamily.euclideanDomain d hd hd2
    UniqueFactorizationMonoid (ℤ√d) :=
  letI := NormEuclideanZsqrtdFamily.euclideanDomain d hd hd2
  inferInstance

/-! ### The two classical rings -/

/-- The Gaussian integers `ℤ[i] = ℤ[√-1]` form a principal ideal ring. -/
theorem gaussianInt_isPrincipalIdealRing : IsPrincipalIdealRing (ℤ√(-1)) :=
  isPrincipalIdealRing (by norm_num) (by norm_num)

/-- The Gaussian integers `ℤ[i] = ℤ[√-1]` form a unique factorization monoid. -/
theorem gaussianInt_uniqueFactorizationMonoid :
    letI := NormEuclideanZsqrtdFamily.euclideanDomainNegOne
    UniqueFactorizationMonoid (ℤ√(-1)) :=
  letI := NormEuclideanZsqrtdFamily.euclideanDomainNegOne
  inferInstance

/-- `ℤ[√-2]` is a principal ideal ring. -/
theorem negTwo_isPrincipalIdealRing : IsPrincipalIdealRing (ℤ√(-2)) :=
  isPrincipalIdealRing (by norm_num) (by norm_num)

/-- `ℤ[√-2]` is a unique factorization monoid. -/
theorem negTwo_uniqueFactorizationMonoid :
    letI := NormEuclideanZsqrtdFamily.euclideanDomainNegTwo
    UniqueFactorizationMonoid (ℤ√(-2)) :=
  letI := NormEuclideanZsqrtdFamily.euclideanDomainNegTwo
  inferInstance

/-! ### Prime norm ⟹ irreducible (and prime in the UFD) -/

/-- **Prime-norm elements are irreducible.** For *any* `d`, if the natural
absolute value of `N(z)` is a prime number, then `z` is irreducible in `ℤ[√d]`.

The norm is multiplicative, so a factorisation `z = a * b` splits the prime
`|N(z)| = |N(a)| · |N(b)|`, forcing one factor to have norm of absolute value `1`,
i.e. to be a unit (`Zsqrtd.norm_eq_one_iff`, which is unconditional in `d`). This
uses no hypothesis on `d` at all — in particular it holds far outside the
Euclidean range `-2 ≤ d < 0`. -/
theorem irreducible_of_prime_norm {z : ℤ√d}
    (hz : Prime z.norm.natAbs) : Irreducible z := by
  refine ⟨?_, ?_⟩
  · -- `z` is not a unit, else `|N(z)| = 1`, contradicting primality.
    intro hu
    exact hz.ne_one (norm_eq_one_iff.mpr hu)
  · -- A factorisation splits the prime norm.
    intro a b hab
    have hmn : z.norm.natAbs = a.norm.natAbs * b.norm.natAbs := by
      rw [hab, norm_mul, Int.natAbs_mul]
    rcases hz.irreducible.isUnit_or_isUnit hmn with h | h
    · exact Or.inl (norm_eq_one_iff.mp (Nat.isUnit_iff.mp h))
    · exact Or.inr (norm_eq_one_iff.mp (Nat.isUnit_iff.mp h))

/-- **Prime-norm elements are prime** in `ℤ[√d]` for `-2 ≤ d < 0`. In the UFD,
irreducible and prime coincide, so the criterion above upgrades to primality. -/
theorem prime_of_prime_norm (hd : d < 0) (hd2 : -2 ≤ d) {z : ℤ√d}
    (hz : Prime z.norm.natAbs) : Prime z := by
  letI := NormEuclideanZsqrtdFamily.euclideanDomain d hd hd2
  exact UniqueFactorizationMonoid.irreducible_iff_prime.mp (irreducible_of_prime_norm hz)

end NormEuclideanZsqrtdFamilyPIDUFD
