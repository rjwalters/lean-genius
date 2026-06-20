import Mathlib

/-
# Infinitude of Primes OQ-05: Goldbach's Proof via Fermat Numbers

## Research Problem: infinitude-primes-oq-05

Goldbach's proof (from a 1730 letter to Euler) that there are infinitely many primes,
*without* Euclid's N! + 1 construction. The Fermat numbers

  Fₙ = 2^(2ⁿ) + 1   (F₀ = 3, F₁ = 5, F₂ = 17, F₃ = 257, …)

are **pairwise coprime**: any two distinct Fermat numbers share no common factor.
Hence each Fₙ contributes a prime factor that no other Fₘ can share, so the assignment
n ↦ (smallest prime factor of Fₙ) is an injection from ℕ into the set of primes.
An injection from an infinite set forces the codomain to be infinite.

## Mathematical Content

The crux is `Nat.coprime_fermatNumber_fermatNumber` (distinct Fermat numbers are
coprime), which Mathlib proves from the telescoping identity
F₀·F₁·⋯·Fₙ₋₁ = Fₙ − 2. Goldbach's elegant point is that pairwise coprimality is by
itself enough to manufacture infinitely many primes — the primes need not be exhibited,
only counted.

This file packages that lemma into the statement that the set of primes is infinite, via:
- `fermatPrimeFactor n := (Fₙ).minFac`, a prime (since Fₙ > 1);
- injectivity of `n ↦ fermatPrimeFactor n` (a shared minFac would divide both Fₘ and Fₙ,
  hence divide their gcd = 1, contradicting primality);
- `Set.infinite_of_injective_forall_mem` to conclude `{p | p.Prime}.Infinite`.

## References
- Christian Goldbach (1730): letter to Leonhard Euler
- Aigner & Ziegler, *Proofs from THE BOOK*: "Six proofs of the infinity of primes" (Third proof)
- Mathlib: `Nat.coprime_fermatNumber_fermatNumber`, `Nat.two_lt_fermatNumber`
-/

open Nat

namespace InfinitudePrimesOQ05

/-- The prime factor extracted from the n-th Fermat number Fₙ = 2^(2ⁿ) + 1:
    its smallest prime factor. -/
def fermatPrimeFactor (n : ℕ) : ℕ := (fermatNumber n).minFac

/-! ## Part I: Each Fermat number yields a prime -/

/-- Every Fermat number exceeds 1 (indeed Fₙ > 2), so it is not the unit. -/
theorem fermatNumber_ne_one (n : ℕ) : fermatNumber n ≠ 1 :=
  Nat.ne_of_gt (lt_trans one_lt_two (two_lt_fermatNumber n))

/-- The extracted factor is genuinely prime. -/
theorem fermatPrimeFactor_prime (n : ℕ) : (fermatPrimeFactor n).Prime :=
  Nat.minFac_prime (fermatNumber_ne_one n)

/-- The extracted factor divides its Fermat number. -/
theorem fermatPrimeFactor_dvd (n : ℕ) : fermatPrimeFactor n ∣ fermatNumber n :=
  Nat.minFac_dvd _

/-! ## Part II: Distinct Fermat numbers give distinct primes -/

/-- The map n ↦ (smallest prime factor of Fₙ) is injective.

    If `fermatPrimeFactor m = fermatPrimeFactor n` with `m ≠ n`, that common value `p`
    divides both `Fₘ` and `Fₙ`; but `Fₘ` and `Fₙ` are coprime, so `p = 1` — impossible
    since `p` is prime. -/
theorem fermatPrimeFactor_injective : Function.Injective fermatPrimeFactor := by
  intro m n hmn
  by_contra hne
  have hp := fermatPrimeFactor_prime m
  have hdm : fermatPrimeFactor m ∣ fermatNumber m := fermatPrimeFactor_dvd m
  have hdn : fermatPrimeFactor m ∣ fermatNumber n := hmn ▸ fermatPrimeFactor_dvd n
  have hcop : Nat.Coprime (fermatNumber m) (fermatNumber n) :=
    Nat.coprime_fermatNumber_fermatNumber hne
  have h1 : fermatPrimeFactor m = 1 := Nat.eq_one_of_dvd_coprimes hcop hdm hdn
  exact hp.ne_one h1

/-! ## Part III: Infinitely many primes (Goldbach) -/

/-- **Goldbach's theorem**: there are infinitely many primes, proved via the pairwise
    coprimality of the Fermat numbers (no Euclid construction). -/
theorem infinite_setOf_prime : {p : ℕ | p.Prime}.Infinite :=
  Set.infinite_of_injective_forall_mem
    fermatPrimeFactor_injective fermatPrimeFactor_prime

/-- The Fermat-number proof in fully self-contained form: an injection from ℕ into the
    primes, exhibiting infinitely many of them. -/
theorem exists_injection_nat_to_primes :
    ∃ f : ℕ → ℕ, Function.Injective f ∧ ∀ n, (f n).Prime :=
  ⟨fermatPrimeFactor, fermatPrimeFactor_injective, fermatPrimeFactor_prime⟩

/-! ## Part IV: Verified small cases -/

-- F₀ = 3 is prime, so its smallest prime factor is 3
example : fermatPrimeFactor 0 = 3 := by
  rw [fermatPrimeFactor, fermatNumber_zero]; exact Nat.Prime.minFac_eq (by norm_num)

-- F₁ = 5 is prime, so its smallest prime factor is 5
example : fermatPrimeFactor 1 = 5 := by
  rw [fermatPrimeFactor, fermatNumber_one]; exact Nat.Prime.minFac_eq (by norm_num)

-- F₂ = 17 is prime, so its smallest prime factor is 17
example : fermatPrimeFactor 2 = 17 := by
  rw [fermatPrimeFactor, fermatNumber_two]; exact Nat.Prime.minFac_eq (by norm_num)

-- The extracted primes are pairwise distinct (direct from injectivity)
example : fermatPrimeFactor 0 ≠ fermatPrimeFactor 1 :=
  fermatPrimeFactor_injective.ne (by decide)
example : fermatPrimeFactor 1 ≠ fermatPrimeFactor 2 :=
  fermatPrimeFactor_injective.ne (by decide)

/-! ## Part V: Summary -/

/-- **Infinitude of Primes OQ-05 Summary** (Goldbach via Fermat numbers):
    (1) each `fermatPrimeFactor n` is prime;
    (2) the map is injective;
    (3) therefore the set of primes is infinite. -/
theorem infinitude_primes_oq05_summary :
    (∀ n, (fermatPrimeFactor n).Prime) ∧
    Function.Injective fermatPrimeFactor ∧
    {p : ℕ | p.Prime}.Infinite :=
  ⟨fermatPrimeFactor_prime, fermatPrimeFactor_injective, infinite_setOf_prime⟩

end InfinitudePrimesOQ05
