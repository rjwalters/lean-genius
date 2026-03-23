import Mathlib.Tactic

/-
# √p is Irrational for Prime p (From Axioms)

## What This Proves
We prove that √p is irrational for any prime p, generalizing the √2 proof
in `Sqrt2IrrationalFromAxioms.lean` to all primes.

## Approach
- **Foundation**: Only `ring`, `omega`, `linarith`, `nlinarith` for arithmetic.
  Everything else—definitions, lemmas, proof structure—is built manually.
- **Key Insight**: The √2 proof works because 2 is prime. The "even/odd" trick
  is really the special case of Euclid's lemma for p=2. Once you see this,
  the generalization is immediate.
- **Euclid's Criterion**: We define primality as "p > 1 and p | ab → p | a ∨ p | b".
  This is the exact property needed for the proof. It's equivalent to the
  classical definition (p > 1, only divisors are 1 and p), but that equivalence
  requires Bezout's identity—beyond the scope of this pedagogical proof.

## Status
- [x] Complete proof
- [ ] Uses Mathlib for main result
- [x] Proves extensions/corollaries
- [x] Pedagogical example
- [ ] Incomplete (has sorries)

## Mathlib Dependencies
- `ring` / `omega` / `linarith` / `nlinarith` for arithmetic
- `Nat.mul_mod` for verifying specific primes
- `Nat.Prime` (bridge theorem only—main proof is self-contained)

## Educational Value
This file demonstrates the key generalization step from √2 to √p:

1. **Why parity works for √2**: Being "even" = divisible by 2, and the
   key lemma "n² even → n even" is really "2 | n² → 2 | n"—a special
   case of Euclid's lemma.
2. **The right definition of prime**: For this proof, what matters is the
   *multiplicative* property (Euclid's criterion), not the *divisor* property.
3. **The proof structure is identical**: Replace "even" with "divisible by p"
   and the √2 proof generalizes perfectly.

Compare with `Sqrt2IrrationalFromAxioms.lean` which handles only p = 2.
-/

namespace SqrtPrimeFromAxioms

-- ============================================================
-- PART 1: Divisibility (Built from Scratch)
-- ============================================================

/-- p divides n if n = p * k for some k -/
def Divides (p n : Nat) : Prop := ∃ k : Nat, n = p * k

/-- Notation for our custom divisibility -/
scoped notation:50 a " ∣₀ " b => Divides a b

/-- Every number divides 0 -/
theorem divides_zero (p : Nat) : p ∣₀ 0 := ⟨0, by ring⟩

/-- Every number divides itself -/
theorem divides_self (p : Nat) : p ∣₀ p := ⟨1, by ring⟩

/-- p divides p * a -/
theorem divides_mul (p a : Nat) : p ∣₀ (p * a) := ⟨a, rfl⟩

/-- Divisibility is transitive through multiplication -/
theorem divides_of_divides_mul_left {p a b : Nat} (h : p ∣₀ a) : p ∣₀ (a * b) := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k * b, by rw [hk]; ring⟩

/-- Small numbers less than p are not divisible by p (unless zero) -/
theorem not_divides_of_lt {p n : Nat} (_hp : p > 1) (hn : 0 < n) (hlt : n < p) :
    ¬(p ∣₀ n) := by
  intro ⟨k, hk⟩
  -- k = 0 gives n = 0 (contradicts hn); k ≥ 1 gives n ≥ p (contradicts hlt)
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · omega
  · nlinarith

-- ============================================================
-- PART 2: Primality (Built from Scratch)
-- ============================================================

/-- A number p is prime (Euclid's criterion) if p > 1 and whenever
    p divides a product, it divides one of the factors.

    This is the "right" definition for irrationality proofs. It's
    equivalent to the classical definition (only divisors are 1 and p)
    via Bezout's identity, but we don't need that equivalence here.

    Historical note: Euclid proved this property in Elements Book VII,
    Proposition 30 (circa 300 BCE). It's sometimes called "Euclid's lemma". -/
def EuclidPrime (p : Nat) : Prop :=
  p > 1 ∧ ∀ a b : Nat, (p ∣₀ (a * b)) → (p ∣₀ a) ∨ (p ∣₀ b)

-- ============================================================
-- PART 3: Verifying Small Primes
-- ============================================================

/-- 2 satisfies Euclid's criterion.

    This connects back to the √2 proof: the "even/odd" case analysis
    is exactly the verification that 2 is an Euclid prime. If n is
    odd (not divisible by 2), then n² is odd. Contrapositively,
    2 | n² → 2 | n. -/
theorem two_euclidPrime : EuclidPrime 2 := by
  refine ⟨by omega, fun a b ⟨k, hk⟩ => ?_⟩
  -- Case split: is a even or odd?
  by_cases ha : a % 2 = 0
  · -- a is even → 2 | a
    left; exact ⟨a / 2, by omega⟩
  · -- a is odd → 2 | b
    right
    suffices b % 2 = 0 by exact ⟨b / 2, by omega⟩
    -- a*b = 2k and a is odd. Use modular arithmetic:
    -- (a*b) % 2 = (a%2 * b%2) % 2 = (1 * b%2) % 2 = b%2
    have ha1 : a % 2 = 1 := by omega
    have hab_mod : (a * b) % 2 = 0 := by omega
    rw [Nat.mul_mod, ha1] at hab_mod
    simpa using hab_mod

/-- 3 satisfies Euclid's criterion.

    Verification: if 3 ∤ a, then a ≡ 1 or 2 (mod 3).
    Products of nonzero residues mod 3: 1·1=1, 1·2=2, 2·1=2, 2·2=4≡1.
    None are 0 mod 3, so 3 | ab → 3 | a ∨ 3 | b. -/
theorem three_euclidPrime : EuclidPrime 3 := by
  refine ⟨by omega, fun a b ⟨k, hk⟩ => ?_⟩
  by_cases ha : a % 3 = 0
  · left; exact ⟨a / 3, by omega⟩
  · right
    suffices b % 3 = 0 by exact ⟨b / 3, by omega⟩
    have hab_mod : (a * b) % 3 = 0 := by omega
    rw [Nat.mul_mod] at hab_mod
    -- a % 3 ∈ {1, 2}, case split
    have : a % 3 = 1 ∨ a % 3 = 2 := by omega
    rcases this with h1 | h2 <;> simp_all <;> omega

/-- 5 satisfies Euclid's criterion. -/
theorem five_euclidPrime : EuclidPrime 5 := by
  refine ⟨by omega, fun a b ⟨k, hk⟩ => ?_⟩
  by_cases ha : a % 5 = 0
  · left; exact ⟨a / 5, by omega⟩
  · right
    suffices b % 5 = 0 by exact ⟨b / 5, by omega⟩
    have hab_mod : (a * b) % 5 = 0 := by omega
    rw [Nat.mul_mod] at hab_mod
    have : a % 5 = 1 ∨ a % 5 = 2 ∨ a % 5 = 3 ∨ a % 5 = 4 := by omega
    rcases this with h | h | h | h <;> simp_all <;> omega

-- ============================================================
-- PART 4: Bridge to Mathlib (Optional)
-- ============================================================

/-- Every Mathlib prime is an Euclid prime.
    This bridges our from-axioms development with Mathlib's library,
    letting users apply our theorem to any Mathlib-certified prime.

    The reverse direction (every Euclid prime satisfies the classical
    definition) requires Bezout's identity—a worthy exercise we leave
    for another proof. -/
theorem natPrime_is_euclidPrime {p : Nat} (hp : Nat.Prime p) : EuclidPrime p := by
  refine ⟨hp.one_lt, fun a b hab => ?_⟩
  obtain ⟨k, hk⟩ := hab
  have hdvd : p ∣ a * b := ⟨k, hk⟩
  -- Mathlib's Nat.Prime.dvd_mul gives us p ∣ a ∨ p ∣ b
  rcases hp.dvd_mul.mp hdvd with ha | hb
  · left; exact ha
  · right; exact hb

-- ============================================================
-- PART 5: Key Lemma
-- ============================================================

/-- **KEY LEMMA**: If p is prime and p divides n², then p divides n.

    This generalizes the √2 proof's "n² even → n even" to all primes.
    The proof is almost trivial given our definition of EuclidPrime:
    n² = n * n, so p | n * n → p | n ∨ p | n → p | n.

    This is the entire reason the √2 proof works—it secretly uses
    the fact that 2 is prime. -/
theorem dvd_of_prime_dvd_sq {p n : Nat} (hp : EuclidPrime p) (h : p ∣₀ (n * n)) :
    p ∣₀ n := by
  rcases hp.2 n n h with h | h <;> exact h

-- ============================================================
-- PART 6: Coprimality (Generalized)
-- ============================================================

/-- Two numbers are coprime with respect to prime p if p doesn't
    divide both of them.

    This generalizes the √2 proof's "not both even" to "not both
    divisible by p". In full generality, coprimality means gcd = 1,
    but for our proof we only need this weaker p-specific version. -/
def CoprimeMod (p a b : Nat) : Prop := ¬((p ∣₀ a) ∧ (p ∣₀ b))

-- ============================================================
-- PART 7: The Main Theorem
-- ============================================================

/-- Helper: a² = p * b² implies p | a -/
theorem a_dvd_of_sq_eq_prime_sq {p : Nat} (a b : Nat) (hp : EuclidPrime p)
    (h : a * a = p * (b * b)) : p ∣₀ a := by
  have h_dvd : p ∣₀ (a * a) := ⟨b * b, h⟩
  exact dvd_of_prime_dvd_sq hp h_dvd

/-- Helper: if a = pk and a² = p*b², then b² = p*k²

    Arithmetic: (pk)² = p*b² ⟹ p²k² = p*b² ⟹ pk² = b² -/
theorem b_sq_eq_prime_k_sq {p : Nat} (a b k : Nat) (hp : EuclidPrime p)
    (ha : a = p * k) (h : a * a = p * (b * b)) : b * b = p * (k * k) := by
  have hp_gt := hp.1  -- p > 1
  have hp_pos : 0 < p := by omega
  -- Substitute a = pk: (pk)² = p * b²
  have h1 : p * k * (p * k) = p * (b * b) := by rw [← ha]; exact h
  -- Rearrange to p * (p * k²) = p * b²
  have h2 : p * (p * (k * k)) = p * (b * b) := by
    have : p * k * (p * k) = p * (p * (k * k)) := by ring
    linarith
  -- Cancel p from both sides using division
  have : p * (k * k) = b * b :=
    calc p * (k * k)
        = p * (p * (k * k)) / p := (Nat.mul_div_cancel_left _ hp_pos).symm
      _ = p * (b * b) / p := congr_arg (· / p) h2
      _ = b * b := Nat.mul_div_cancel_left _ hp_pos
  omega

/-- **MAIN THEOREM**: For any prime p, there are no natural numbers a, b
    with b > 0 such that a² = p * b² and a, b are coprime mod p.

    Equivalently: √p cannot be expressed as a ratio a/b of natural numbers
    in lowest terms. That is, √p is irrational.

    The proof is structurally identical to the √2 case:
    1. From a² = p*b², deduce p | a   (using Euclid's lemma)
    2. Write a = pk, substitute back
    3. Get b² = p*k², deduce p | b     (using Euclid's lemma again)
    4. Both a and b divisible by p → contradiction with coprimality -/
theorem sqrt_prime_irrational (p a b : Nat) (hp : EuclidPrime p)
    (hb : b > 0) (h_sq : a * a = p * (b * b)) : ¬CoprimeMod p a b := by
  intro h_coprime
  -- Step 1: Show p | a (because p | a²)
  have h_a_dvd : p ∣₀ a := a_dvd_of_sq_eq_prime_sq a b hp h_sq
  -- Step 2: Write a = pk for some k
  obtain ⟨k, hk⟩ := h_a_dvd
  -- Step 3: Show b² = p * k² (arithmetic cancellation)
  have h_b_sq : b * b = p * (k * k) := b_sq_eq_prime_k_sq a b k hp hk h_sq
  -- Step 4: Show p | b² → p | b (Euclid's lemma again)
  have h_b_sq_dvd : p ∣₀ (b * b) := ⟨k * k, h_b_sq⟩
  have h_b_dvd : p ∣₀ b := dvd_of_prime_dvd_sq hp h_b_sq_dvd
  -- Step 5: Both a and b divisible by p—contradiction!
  exact h_coprime ⟨⟨k, hk⟩, h_b_dvd⟩

-- ============================================================
-- PART 8: Alternative Formulation
-- ============================================================

/-- For any a, b with a² = p*b², either b = 0 or both a and b are
    divisible by p. (Contrapositive of the main theorem.) -/
theorem sqrt_prime_no_rational_form (p a b : Nat) (hp : EuclidPrime p)
    (h : a * a = p * (b * b)) : b = 0 ∨ ((p ∣₀ a) ∧ (p ∣₀ b)) := by
  match b with
  | 0 => left; rfl
  | b + 1 =>
    right
    have h_a_dvd : p ∣₀ a := a_dvd_of_sq_eq_prime_sq a (b + 1) hp h
    obtain ⟨k, hk⟩ := h_a_dvd
    have h_b_sq : (b + 1) * (b + 1) = p * (k * k) :=
      b_sq_eq_prime_k_sq a (b + 1) k hp hk h
    have h_b_sq_dvd : p ∣₀ ((b + 1) * (b + 1)) := ⟨k * k, h_b_sq⟩
    have h_b_dvd : p ∣₀ (b + 1) := dvd_of_prime_dvd_sq hp h_b_sq_dvd
    exact ⟨⟨k, hk⟩, h_b_dvd⟩

-- ============================================================
-- PART 9: Concrete Instances
-- ============================================================

/-- √2 is irrational (recovered as special case) -/
theorem sqrt_2_irrational (a b : Nat) (hb : b > 0)
    (h : a * a = 2 * (b * b)) : ¬CoprimeMod 2 a b :=
  sqrt_prime_irrational 2 a b two_euclidPrime hb h

/-- √3 is irrational -/
theorem sqrt_3_irrational (a b : Nat) (hb : b > 0)
    (h : a * a = 3 * (b * b)) : ¬CoprimeMod 3 a b :=
  sqrt_prime_irrational 3 a b three_euclidPrime hb h

/-- √5 is irrational -/
theorem sqrt_5_irrational (a b : Nat) (hb : b > 0)
    (h : a * a = 5 * (b * b)) : ¬CoprimeMod 5 a b :=
  sqrt_prime_irrational 5 a b five_euclidPrime hb h

/-- √p is irrational for any Mathlib-certified prime p -/
theorem sqrt_natPrime_irrational {p : Nat} (hp : Nat.Prime p) (a b : Nat)
    (hb : b > 0) (h : a * a = p * (b * b)) : ¬CoprimeMod p a b :=
  sqrt_prime_irrational p a b (natPrime_is_euclidPrime hp) hb h

-- ============================================================
-- PART 10: Educational Notes
-- ============================================================

/-
## Why This Proof Works

The key insight is that the √2 proof's "even/odd" trick is secretly
using the fact that 2 is **prime**. Here's the correspondence:

| √2 proof concept     | General √p concept           |
|-----------------------|-------------------------------|
| n is even             | p divides n                   |
| n is odd              | p does not divide n           |
| n² even → n even      | p | n² → p | n (Euclid)      |
| coprime = not both even | coprime = not both div by p |

Once you see this, the proof generalizes immediately.

## What We Built Ourselves

1. **Divisibility** - When does p divide n?
2. **Euclid's criterion for primality** - The multiplicative property
3. **Verification** - 2, 3, 5 are Euclid primes (by modular arithmetic)
4. **Key lemma** - p prime ∧ p | n² → p | n
5. **Main theorem** - No coprime a/b with a² = p*b²
6. **Bridge to Mathlib** - Every Nat.Prime is an Euclid prime

## The Two Definitions of Prime

Our `EuclidPrime p` says: p > 1 and p | ab → p | a ∨ p | b.
The classical definition says: p > 1 and the only divisors of p are 1 and p.

These are equivalent for natural numbers, but proving it requires
**Bezout's identity**: for any a, b with gcd(a,b) = 1, there exist
integers s, t such that sa + tb = 1. From this, if p | ab and p ∤ a,
then gcd(p,a) = 1 (since p is classically prime), so sp + ta = 1,
and sp·b + ta·b = b, hence p | b.

Building Bezout from scratch would add ~200 lines. Instead, we use
the Euclid definition directly and bridge to Mathlib's `Nat.Prime`
for users who need the classical definition.

## Connection to the √2 Proof

In `Sqrt2IrrationalFromAxioms.lean`, the crucial step is:

  theorem even_of_sq_even : Even (n * n) → Even n

This is exactly our `dvd_of_prime_dvd_sq` for p = 2. The parent proof
builds Even/Odd infrastructure to prove this; we use Euclid's criterion
instead. Both approaches reveal the same mathematical truth: the proof
works because the number under the radical is prime.

## What About Non-Prime Numbers?

√6 is also irrational, but our theorem doesn't directly cover it
(6 is not prime). The standard proof uses unique factorization:
6 = 2 × 3, and if a² = 6b² then 2 | a and 3 | a, so 6 | a.
This requires a different approach—see `Sqrt2Irrational.lean` which
uses Mathlib's `irrational_sqrt_natCast_iff` for the general case.
-/

end SqrtPrimeFromAxioms
