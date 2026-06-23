import Mathlib

/-
# Euclid's Lemma Generalized: Bézout Domains and PIDs (OQ-02-OQ-02)

## The Open Question (bezout-identity-oq-02-oq-02)

Can `euclids_lemma_int` be generalized to arbitrary Bézout domains or PIDs
using Mathlib's `IsBezout` typeclass, giving a single proof covering ℤ, k[x],
and other rings?

## Answer: Yes — and the generalization is immediate!

The key insight: `IsCoprime a b` in ANY commutative ring is already the
abstract Bézout condition — it means ∃ u v, u*a + v*b = 1.
The proof of Euclid's lemma uses ONLY ring axioms, so it works universally.

## The Proof Hierarchy

1. **CommRing level** (most general): IsCoprime → Euclid's lemma by ring identity
2. **IsBezout level**: IsRelPrime a b (every common divisor is a unit) →
   IsCoprime a b → Euclid's lemma (via Submodule.IsPrincipal)
3. **EuclideanDomain level**: algorithmic coprimality → Euclid's lemma
4. **Irreducible elements**: in DecompositionMonoid, irreducible ↔ prime
5. **Instances**: ℤ, ℚ[X], ℤ[i] all satisfy the required typeclasses

## Key Mathlib API Discovered

- `IsRelPrime a b = ∀ c, c ∣ a → c ∣ b → IsUnit c` (every common divisor is a unit)
- `IsBezout.span_pair_isPrincipal : Submodule.IsPrincipal (Ideal.span {x, y})`
- `IsRelPrime.isCoprime : [Submodule.IsPrincipal (Ideal.span {x,y})] → IsRelPrime x y → IsCoprime x y`
- `EuclideanDomain.isCoprime_of_dvd : (∀ z, z ∣ x → z ∣ y → IsUnit z) → IsCoprime x y`
- `irreducible_iff_prime : [CancelCommMonoidWithZero M] [DecompositionMonoid M] → Irreducible a ↔ Prime a`

## Proof Status
- [x] Part I: Euclid's lemma for ANY CommRing via IsCoprime (0 sorries)
- [x] Part II: IsRelPrime → IsCoprime in IsBezout rings (0 sorries)
- [x] Part III: EuclideanDomain version (0 sorries)
- [x] Part IV: Irreducible = Prime in DecompositionMonoids (0 sorries)
- [x] Part V: Concrete instances — ℤ, ℚ[X], ℤ[i] (0 sorries)
- [x] Part VI: The uniform proof principle (0 sorries)
-/

namespace BezoutEuclidGeneral

/-!
## Part I: Euclid's Lemma in Any Commutative Ring

The proof is purely algebraic: ring axioms + the definition of IsCoprime.
This subsumes euclids_lemma_int from BezoutIdentityOQ02.lean.
-/

/-- **Euclid's Lemma for any CommRing** (via IsCoprime):
    If `IsCoprime a b` and `a ∣ b * c`, then `a ∣ c`.

    This is the most general form: it works in ℤ, ℚ[X], ℤ[i], and any commutative ring.

    **Proof**: Exactly the same as for ℤ — ring axioms suffice.
    From IsCoprime: get u, v with u*a + v*b = 1.
    From divisibility: get k with b*c = a*k.
    **Witness**: u*c + v*k, since c = (u*a + v*b)*c = a*(u*c) + (b*c)*v = a*(u*c + v*k).
    Verified by `linear_combination v * hk - c * huv`. -/
theorem euclids_lemma_ring {R : Type*} [CommRing R] {a b c : R}
    (hcop : IsCoprime a b) (hdvd : a ∣ b * c) : a ∣ c := by
  obtain ⟨u, v, huv⟩ := hcop   -- huv : u * a + v * b = 1
  obtain ⟨k, hk⟩ := hdvd        -- hk  : b * c = a * k
  -- Witness: u * c + v * k
  exact ⟨u * c + v * k, by linear_combination v * hk - c * huv⟩

/-- **Euclid's Lemma (right multiplication form)**:
    If IsCoprime a b and a ∣ c * b, then a ∣ c. -/
theorem euclids_lemma_ring' {R : Type*} [CommRing R] {a b c : R}
    (hcop : IsCoprime a b) (hdvd : a ∣ c * b) : a ∣ c := by
  rw [mul_comm] at hdvd
  exact euclids_lemma_ring hcop hdvd

/-!
## Part II: IsBezout Connection

In Lean's Mathlib, the typeclass hierarchy is:

```
EuclideanDomain → PrincipalIdealRing → IsBezout → Ring
```

`IsBezout R` means: for any x, y : R, the ideal Ideal.span {x, y} is principal.
This is precisely the algebraic Bézout property.

Key API:
- `IsRelPrime a b` (from Monoid): `∀ c, c ∣ a → c ∣ b → IsUnit c`
- `IsBezout.span_pair_isPrincipal a b`: installs `Submodule.IsPrincipal (Ideal.span {a, b})`
- `IsRelPrime.isCoprime`: `[Submodule.IsPrincipal ...]` → `IsRelPrime a b → IsCoprime a b`
-/

/-- **IsRelPrime to IsCoprime in IsBezout rings**:
    In an IsBezout CommRing, if every common divisor of a and b is a unit
    (IsRelPrime a b), then a and b satisfy the Bézout condition (IsCoprime a b).

    This is the direction: arithmetic coprimality → algebraic Bézout coefficients. -/
theorem isBezout_relPrime_to_isCoprime {R : Type*} [CommRing R] [IsBezout R]
    {a b : R} (h : IsRelPrime a b) : IsCoprime a b := by
  -- IsBezout.span_pair_isPrincipal provides the principal ideal instance
  haveI := IsBezout.span_pair_isPrincipal a b
  exact h.isCoprime

/-- **IsCoprime to IsRelPrime** (in any CommRing):
    If IsCoprime a b, then every common divisor of a and b is a unit.
    This direction works in any commutative ring. -/
theorem isCoprime_to_relPrime {R : Type*} [CommRing R]
    {a b : R} (hcop : IsCoprime a b) : IsRelPrime a b := by
  intro d hda hdb
  -- d | a and d | b → d | u*a + v*b = 1 → d is a unit
  obtain ⟨u, v, huv⟩ := hcop
  have h1 : d ∣ u * a + v * b :=
    dvd_add (dvd_mul_of_dvd_right hda u) (dvd_mul_of_dvd_right hdb v)
  rw [huv] at h1
  exact isUnit_of_dvd_one h1

/-- **IsBezout characterization**: In an IsBezout CommRing,
    IsCoprime a b ↔ IsRelPrime a b (every common divisor is a unit). -/
theorem isBezout_coprime_iff {R : Type*} [CommRing R] [IsBezout R]
    {a b : R} : IsCoprime a b ↔ IsRelPrime a b :=
  ⟨isCoprime_to_relPrime, isBezout_relPrime_to_isCoprime⟩

/-- **Euclid's Lemma for IsBezout rings** (via IsRelPrime):
    If every common divisor of a and b is a unit, and a | b * c, then a | c. -/
theorem euclids_lemma_isbezout {R : Type*} [CommRing R] [IsBezout R]
    {a b c : R} (h : IsRelPrime a b) (hdvd : a ∣ b * c) : a ∣ c :=
  euclids_lemma_ring (isBezout_relPrime_to_isCoprime h) hdvd

/-!
## Part III: EuclideanDomain Version

Every EuclideanDomain is an IsBezout ring (via PrincipalIdealRing).
`EuclideanDomain.isCoprime_of_dvd` provides the explicit connection.
-/

/-- **Euclid's Lemma for EuclideanDomains**:
    If every common divisor of a and b is a unit, and a | b * c, then a | c.
    EuclideanDomain implies IsBezout, so `isBezout_relPrime_to_isCoprime` applies. -/
theorem euclids_lemma_euclidean {α : Type*} [EuclideanDomain α]
    {a b c : α} (h : IsRelPrime a b) (hdvd : a ∣ b * c) : a ∣ c :=
  euclids_lemma_isbezout h hdvd

/-!
## Part IV: Irreducible = Prime in DecompositionMonoids

In a `DecompositionMonoid` (which includes UFDs, PIDs, and EuclideanDomains),
every irreducible element is prime. This gives the abstract prime version of Euclid's lemma.
-/

/-- **Irreducible ↔ Prime in DecompositionMonoids**:
    In a `CancelCommMonoidWithZero` that is also a `DecompositionMonoid`
    (which ℤ, k[X], ℤ[i] all are), irreducible and prime coincide. -/
theorem irred_iff_prime_decomp {M : Type*} [CancelCommMonoidWithZero M]
    [DecompositionMonoid M] {p : M} : Irreducible p ↔ Prime p :=
  irreducible_iff_prime

/-- **Abstract Euclid's Lemma for Irreducibles** (in CancelCommMonoidWithZero + DecompositionMonoid):
    If p is irreducible and p | a * b, then p | a or p | b. -/
theorem euclids_lemma_irreducible {M : Type*} [CancelCommMonoidWithZero M]
    [DecompositionMonoid M] {p a b : M}
    (hirr : Irreducible p) (hdvd : p ∣ a * b) : p ∣ a ∨ p ∣ b :=
  (irreducible_iff_prime.mp hirr).dvd_or_dvd hdvd

/-!
## Part V: Concrete Instances

ℤ, ℚ[X], and ℤ[i] (Gaussian integers) all satisfy the required typeclasses.
-/

section Integers

/-- **Euclid's Lemma for ℤ** (via abstract CommRing version):
    euclids_lemma_int from BezoutIdentityOQ02 is a special case. -/
theorem euclids_lemma_int (a b c : ℤ)
    (hcop : IsCoprime a b) (hdvd : a ∣ b * c) : a ∣ c :=
  euclids_lemma_ring hcop hdvd

/-- ℤ has the IsBezout property (ideals generated by two elements are principal). -/
example : IsBezout ℤ := inferInstance

/-- ℤ is a DecompositionMonoid (irreducible ↔ prime). -/
example : DecompositionMonoid ℤ := inferInstance

/-- Irreducible = Prime in ℤ. -/
example : Irreducible (2 : ℤ) ↔ Prime (2 : ℤ) := irreducible_iff_prime

end Integers

section Polynomials

variable {k : Type*} [Field k]

/-- **Euclid's Lemma for k[X]** (polynomial ring over a field):
    If IsCoprime f g and f | g * h in k[X], then f | h.
    k[X] is a Euclidean domain (hence IsBezout), so this works. -/
theorem euclids_lemma_poly (f g h : Polynomial k)
    (hcop : IsCoprime f g) (hdvd : f ∣ g * h) : f ∣ h :=
  euclids_lemma_ring hcop hdvd

/-- Polynomial rings over fields are IsBezout (Euclidean → IsBezout). -/
noncomputable example : IsBezout (Polynomial k) := inferInstance

/-- Polynomial rings over fields are DecompositionMonoids. -/
noncomputable example : DecompositionMonoid (Polynomial k) := inferInstance

end Polynomials

section GaussianIntegers

/-- **Euclid's Lemma for ℤ[i]** (Gaussian integers):
    ℤ[i] is a Euclidean domain (Gaussian integer norm), hence IsBezout. -/
theorem euclids_lemma_gaussian (α β γ : GaussianInt)
    (hcop : IsCoprime α β) (hdvd : α ∣ β * γ) : α ∣ γ :=
  euclids_lemma_ring hcop hdvd

/-- ℤ[i] is a DecompositionMonoid (irreducible = prime in Gaussian integers). -/
example : DecompositionMonoid GaussianInt := inferInstance

end GaussianIntegers

/-!
## Part VI: The Uniform Proof Principle

The key theorem: Euclid's lemma holds in ANY commutative ring where
IsCoprime is available. No special structure (Bézout, GCD, etc.) needed.

For specific rings, the question becomes: "how do we establish IsCoprime?"

| Ring | How to get IsCoprime | Method |
|------|---------------------|--------|
| ℤ | `Nat.Coprime.isCoprime` / gcdA, gcdB | Bézout algorithm |
| k[X] | Euclidean algorithm on polynomials | EuclideanDomain |
| ℤ[i] | Gaussian integer Euclidean algorithm | EuclideanDomain |
| IsBezout R | `isBezout_relPrime_to_isCoprime` | Principal ideal |
| EuclideanDomain | `EuclideanDomain.isCoprime_of_dvd` | Direct |

All proofs reduce to the SAME one-line proof: `euclids_lemma_ring hcop hdvd`
-/

/-- **Uniform Euclid's Lemma**: The master theorem.
    Every instance is a special case of this. -/
theorem euclids_lemma_uniform {R : Type*} [CommRing R] {a b c : R}
    (hcop : IsCoprime a b) (hdvd : a ∣ b * c) : a ∣ c :=
  euclids_lemma_ring hcop hdvd

/-- **Transparent term-mode proof**: Makes the ring identity explicit.
    Shows: no axioms beyond ring theory are used. -/
theorem euclids_lemma_explicit {R : Type*} [CommRing R] {a b c : R}
    (u v : R) (huv : u * a + v * b = 1)
    (k : R) (hk : b * c = a * k) : a ∣ c :=
  ⟨u * c + v * k, by linear_combination v * hk - c * huv⟩

/-!
## Verification: Instances and Type Class Hierarchy
-/

-- The full hierarchy for ℤ
example : EuclideanDomain ℤ := inferInstance
example : IsBezout ℤ := inferInstance
example : IsCoprime (3 : ℤ) 7 := ⟨5, -2, by norm_num⟩

-- The full hierarchy for Polynomial ℚ
noncomputable example : EuclideanDomain (Polynomial ℚ) := inferInstance
noncomputable example : IsBezout (Polynomial ℚ) := inferInstance

-- The full hierarchy for Gaussian integers
example : EuclideanDomain GaussianInt := inferInstance
example : IsBezout GaussianInt := inferInstance

-- The IsRelPrime ↔ IsCoprime equivalence in IsBezout rings
example : IsRelPrime (3 : ℤ) 7 := by
  intro d hd3 hd7
  have hdvd1 : d ∣ (3 : ℤ) * 5 + 7 * (-2) := dvd_add (hd3.mul_right 5) (hd7.mul_right (-2))
  norm_num at hdvd1
  exact isUnit_of_dvd_one hdvd1

#check @euclids_lemma_ring
#check @euclids_lemma_isbezout
#check @euclids_lemma_euclidean
#check @euclids_lemma_irreducible
#check @isBezout_coprime_iff

end BezoutEuclidGeneral
