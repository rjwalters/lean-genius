import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic

/-
# Bézout Identity OQ03-OQ04-OQ01:
# Generalizing crtDirect to Arbitrary Commutative Rings

## Open Question (bezout-identity-oq-03-oq-04-oq-01)

"Can crtDirect be generalized to arbitrary commutative rings (beyond ℤ)
where Bézout's identity holds? Lean's type class system should support
this via `IsBezout` or `GCDMonoid`."

## Answer

YES. The direct Bézout CRT generalizes immediately to any commutative ring.
No `IsBezout` typeclass is needed — only `IsCoprime m n` (∃ s t, s·m + t·n = 1).

The key insight: the proof is purely algebraic (ring identities), so it
works over any CommRing. The integer-specific parts (`linarith`, `Int.gcd`)
are replaced by `linear_combination` and `IsCoprime.mul_dvd`.

## Builds On
- BezoutIdentityOQ03OQ04.lean: the ℤ version of crtDirect
-/

namespace BezoutIdentityOQ03OQ04OQ01

/-! ## Part 1: Generalized CRT Construction -/

/-- The direct Bézout CRT formula, generalized to any commutative ring.
    Given Bézout coefficients s, t with s·m + t·n = 1,
    the element b·s·m + a·t·n simultaneously satisfies:
    - x ≡ a (mod m)  [since x - a is divisible by m]
    - x ≡ b (mod n)  [since x - b is divisible by n] -/
def crtRing {R : Type*} [CommRing R] (a b s t m n : R) : R :=
  b * s * m + a * t * n

/-! ## Part 2: Correctness Theorems -/

/-- crtRing satisfies the first congruence: x ≡ a (mod m).
    Proof: x - a = b·s·m + a·t·n - a = b·s·m + a·(t·n - 1) = m·(b·s - a·s)
    using t·n = 1 - s·m from the Bézout condition. -/
theorem crtRing_mod_m {R : Type*} [CommRing R] (a b s t m n : R)
    (hbez : s * m + t * n = 1) :
    m ∣ (crtRing a b s t m n - a) :=
  ⟨b * s - a * s, by unfold crtRing; linear_combination a * hbez⟩

/-- crtRing satisfies the second congruence: x ≡ b (mod n).
    Proof: x - b = b·s·m + a·t·n - b = b·(s·m - 1) + a·t·n = n·(a·t - b·t)
    using s·m = 1 - t·n from the Bézout condition. -/
theorem crtRing_mod_n {R : Type*} [CommRing R] (a b s t m n : R)
    (hbez : s * m + t * n = 1) :
    n ∣ (crtRing a b s t m n - b) :=
  ⟨a * t - b * t, by unfold crtRing; linear_combination b * hbez⟩

/-! ## Part 3: Uniqueness -/

/-- CRT uniqueness: if x ≡ y (mod m) and x ≡ y (mod n) with m, n coprime,
    then m·n ∣ (x - y).

    Proof: IsCoprime.mul_dvd from Mathlib.RingTheory.Coprime.Basic. -/
theorem crtRing_unique {R : Type*} [CommRing R] (x y m n : R)
    (hm : m ∣ (x - y)) (hn : n ∣ (x - y))
    (hcop : IsCoprime m n) : m * n ∣ (x - y) :=
  hcop.mul_dvd hm hn

/-! ## Part 4: Existence via IsCoprime -/

/-- Given coprime m, n : R, the CRT system (a, m), (b, n) always has a solution.
    We extract Bézout coefficients from IsCoprime and apply crtRing. -/
theorem crtRing_exists {R : Type*} [CommRing R] (a b m n : R)
    (hcop : IsCoprime m n) :
    ∃ x : R, m ∣ (x - a) ∧ n ∣ (x - b) := by
  obtain ⟨s, t, hst⟩ := hcop
  -- hst : s * m + t * n = 1
  -- Note: IsCoprime m n means ∃ s t, s * m + t * n = 1
  exact ⟨crtRing a b s t m n,
         crtRing_mod_m a b s t m n hst,
         crtRing_mod_n a b s t m n hst⟩

/-! ## Part 5: Connection to IsBezout -/

/-- In an IsBezout ring, every coprime pair has an explicit GCD = 1,
    so the CRT applies. IsBezout ensures every finitely-generated ideal
    is principal, which implies IsCoprime for any pair with gcd = 1. -/
theorem crtRing_bezout {R : Type*} [CommRing R] [IsBezout R] (a b m n : R)
    (hcop : IsCoprime m n) :
    ∃ x : R, m ∣ (x - a) ∧ n ∣ (x - b) :=
  crtRing_exists a b m n hcop

/-! ## Part 6: Recovering the ℤ Case -/

/-- The integer CRT recovers as a special case with IsCoprime = coprimality. -/
theorem crtInt_from_ring (a b s t m n : ℤ) (hbez : s * m + t * n = 1) :
    m ∣ (crtRing a b s t m n - a) ∧ n ∣ (crtRing a b s t m n - b) :=
  ⟨crtRing_mod_m a b s t m n hbez, crtRing_mod_n a b s t m n hbez⟩

/-! ## Summary -/

/-
## The Answer to OQ-03-OQ-04-OQ-01

**YES**, crtDirect generalizes to arbitrary commutative rings.

The key facts:
1. `crtRing` = `b·s·m + a·t·n` works over any `CommRing`.
2. Correctness proofs use `linear_combination` (ring arithmetic) instead
   of `linarith` (integer arithmetic). The proof is purely algebraic.
3. Uniqueness uses `IsCoprime.mul_dvd` instead of `Int.Coprime.mul_dvd_of_dvd_of_dvd`.
4. `IsBezout` ensures the Bézout identity holds in the ring, but the
   core CRT formula only requires the existence of Bézout coefficients
   (i.e., `IsCoprime`), not the full `IsBezout` structure.

Examples of rings where this applies:
- ℤ (integers): the original case
- k[X] (polynomial ring over a field): crtRing solves Lagrange interpolation
- ℤ[i] (Gaussian integers): Gaussian primes + Bézout → CRT
- Any field: trivially, since all non-zero elements are coprime
- Any PID: PIDs are IsBezout
-/

#check @crtRing
#check @crtRing_mod_m
#check @crtRing_mod_n
#check @crtRing_unique
#check @crtRing_exists

end BezoutIdentityOQ03OQ04OQ01
