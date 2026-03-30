import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.UniqueFactorizationDomain
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Tactic

/-
# FTA Generalization to Euclidean Domains

## Open Question (bezout-identity-oq-02-oq-01-oq-02)

"Can the approach generalize to Euclidean domains or PIDs using Mathlib's
UniqueFactorizationDomain typeclass?"

## Answer: Yes — via Mathlib's Instance Chain

Mathlib provides the complete chain:
  EuclideanDomain → IsPrincipalIdealRing → UniqueFactorizationMonoid

This means unique factorization holds automatically in any Euclidean domain,
without reproving anything. The FTA for ℤ is a special case since ℤ is
a Euclidean domain.

## Key Mathlib Instances
1. `EuclideanDomain.to_principal_ideal_domain` : ED → PID
2. `IsPrincipalIdealRing` → `IsBezout` (via IsBezout.of_isPrincipalIdealRing)
3. PID → UFD (via the structure theorem for PIDs)

## Status
- [x] Complete — 0 sorries, 0 axioms
-/

namespace FTAEuclidean

/-! ## The Instance Chain -/

/-- Every Euclidean domain is a PID. This is a Mathlib instance. -/
theorem euclidean_is_pid (R : Type*) [EuclideanDomain R] :
    IsPrincipalIdealRing R := inferInstance

/-- Every PID satisfies the Bezout property. This is a Mathlib instance. -/
theorem pid_is_bezout (R : Type*) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] :
    IsBezout R := inferInstance

-- ============================================================

/-! ## Unique Factorization in Euclidean Domains -/

/-- **FTA for Euclidean domains**: Every Euclidean domain is a UFD.

    The proof chain in Mathlib:
    1. EuclideanDomain → IsPrincipalIdealRing (ideal generation via Euclidean algorithm)
    2. IsPrincipalIdealRing → Noetherian (ascending chain condition)
    3. IsPrincipalIdealRing → irreducibles are prime (key step for uniqueness)
    4. WfDvd + irreducibles_prime → UniqueFactorizationMonoid -/
theorem euclidean_is_ufd (R : Type*) [EuclideanDomain R] [GCDMonoid R] :
    UniqueFactorizationMonoid R := inferInstance

-- Concrete Examples

/-- ℤ is a UFD (special case of the above). -/
example : UniqueFactorizationMonoid ℤ := inferInstance

-- The Gaussian integers ℤ[i] also form a Euclidean domain, hence a UFD.
-- (via GaussianInt.instEuclideanDomain in Mathlib.NumberTheory.Zsqrtd.GaussianInt)

section UFDProperties

variable {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]

/-- In a UFD, every irreducible element is prime. -/
theorem irreducible_is_prime_in_ufd {p : R} (hp : Irreducible p) : Prime p :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mp hp

/-- In a UFD, every nonzero non-unit factors into irreducibles. -/
theorem exists_prime_factorization {a : R} (ha : a ≠ 0) :
    ∃ f : Multiset R, (∀ p ∈ f, Irreducible p) ∧ Associated f.prod a :=
  ⟨UniqueFactorizationMonoid.factors a,
   fun p hp => UniqueFactorizationMonoid.irreducible_of_factor p hp,
   UniqueFactorizationMonoid.factors_prod ha⟩

end UFDProperties

end FTAEuclidean

-- ============================================================
-- Export
-- ============================================================

#check @FTAEuclidean.euclidean_is_ufd
#check @FTAEuclidean.irreducible_is_prime_in_ufd
#check @FTAEuclidean.exists_prime_factorization
