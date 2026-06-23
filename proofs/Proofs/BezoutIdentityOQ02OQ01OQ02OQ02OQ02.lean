/-
# Fermat's Two-Square Theorem via Gaussian Integers

**Open Question (bezout-identity-oq-02-oq-01-oq-02-oq-02-oq-02)**:
Fermat's two-square theorem follows directly from the Gaussian integer framework:
a prime p is a sum of two squares iff p = 2 or p ≡ 1 (mod 4).

## Mathematical Content

**Main Theorem**: For a prime p,
  `(∃ a b : ℕ, a² + b² = p) ↔ p = 2 ∨ p % 4 = 1`

## Proof Strategy

**Forward** (sum of squares → mod-4 condition):
  Squares in ZMod 4 are only 0 or 1 (decidable by cases). So a² + b² ≡ 0, 1, or 2
  (mod 4), never 3. If p ≡ 3 (mod 4), contradiction.

**Backward** (mod-4 condition → sum of squares):
  - p = 2: 1² + 1² = 2.
  - p ≡ 1 (mod 4): Mathlib's `Nat.Prime.sq_add_sq` (which relies on the Gaussian
    integer factorization over ℤ[i]).

## Gaussian Integer Connection

From BezoutIdentityOQ02OQ01OQ02OQ02: a rational prime p ≡ 3 (mod 4) is **inert**
(prime) in ℤ[i]. The same ZMod 4 obstruction that blocks sum-of-squares also
explains why inert primes cannot split: p stays irreducible in ℤ[i] exactly
because its norm p² cannot factor as norm(z) = z.re² + z.im² = p.

## Status: 0 sorries, 0 axioms
-/

import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.NumberTheory.SumTwoSquares
import Proofs.BezoutIdentityOQ02OQ01OQ02OQ02

set_option maxHeartbeats 400000

namespace BezoutIdentityOQ02OQ01OQ02OQ02OQ02

open GaussianInt GaussianIntEuclidean

/-! ## Part 1: Mod-4 Obstruction -/

/-- In ZMod 4, the square of any element is 0 or 1. Proved by exhaustive case check. -/
lemma sq_mod4_cases (x : ZMod 4) : x ^ 2 = 0 ∨ x ^ 2 = 1 := by
  fin_cases x <;> decide

/-- The sum of two squares in ZMod 4 is never 3.
    Proved by exhaustive check over all 16 pairs in ZMod 4. -/
lemma sum_sq_ne_three (a b : ZMod 4) : a ^ 2 + b ^ 2 ≠ 3 := by
  fin_cases a <;> fin_cases b <;> decide

/-- If p ≡ 3 (mod 4), then p is not expressible as a sum of two natural number squares.
    Proof: cast a² + b² = p to ZMod 4; squares are 0 or 1 mod 4, so sum ≤ 2, not 3. -/
theorem not_sum_sq_of_mod4_eq_three {p : ℕ} (hp : p.Prime) (hmod : p % 4 = 3) :
    ¬ ∃ a b : ℕ, a ^ 2 + b ^ 2 = p := by
  intro ⟨a, b, hab⟩
  -- Cast the equality to ZMod 4
  have key : (a : ZMod 4) ^ 2 + (b : ZMod 4) ^ 2 = (p : ZMod 4) := by
    have h := congr_arg (Nat.cast : ℕ → ZMod 4) hab
    push_cast at h
    exact h
  -- (p : ZMod 4) = 3 since p % 4 = 3
  have hp4 : (p : ZMod 4) = 3 := by
    rw [show (3 : ZMod 4) = ((3 : ℕ) : ZMod 4) from by norm_num,
        ZMod.natCast_eq_natCast_iff]
    unfold Nat.ModEq
    omega
  rw [hp4] at key
  exact sum_sq_ne_three _ _ key

/-! ## Part 2: The Main Theorem -/

/-- **Fermat's Two-Square Theorem**: A prime p is a sum of two squares of natural
    numbers if and only if p = 2 or p ≡ 1 (mod 4).

    - Forward: squares are 0 or 1 mod 4, so sum ≤ 2 mod 4, never 3.
    - Backward: p = 2 gives 1² + 1²; p ≡ 1 (mod 4) uses `Nat.Prime.sq_add_sq`. -/
theorem fermat_two_square {p : ℕ} (hp : p.Prime) :
    (∃ a b : ℕ, a ^ 2 + b ^ 2 = p) ↔ p = 2 ∨ p % 4 = 1 := by
  constructor
  · -- Forward: if p = a² + b², show p = 2 or p ≡ 1 (mod 4)
    intro h
    by_contra hc
    push_neg at hc
    obtain ⟨h2, h1⟩ := hc
    -- p is prime and ≠ 2, so p is odd (p % 2 = 1)
    have hmod2 : p % 2 ≠ 0 := by
      intro hev
      have hdvd : 2 ∣ p := Nat.dvd_of_mod_eq_zero hev
      have := hp.eq_one_or_self_of_dvd 2 hdvd
      omega
    -- p % 4 ∈ {1, 3} (odd), and ≠ 1, so p % 4 = 3
    have hmod : p % 4 = 3 := by omega
    exact not_sum_sq_of_mod4_eq_three hp hmod h
  · -- Backward: p = 2 gives 1² + 1²; p ≡ 1 (mod 4) uses Mathlib
    intro h
    haveI : Fact p.Prime := ⟨hp⟩
    rcases h with rfl | h1
    · exact ⟨1, 1, by norm_num⟩
    · exact Nat.Prime.sq_add_sq (by omega : p % 4 ≠ 3)

/-- Integer form: a prime p is a sum of two integer squares iff p = 2 or p ≡ 1 (mod 4). -/
theorem fermat_two_square_int {p : ℕ} (hp : p.Prime) :
    (∃ a b : ℤ, a ^ 2 + b ^ 2 = (p : ℤ)) ↔ p = 2 ∨ p % 4 = 1 := by
  rw [← fermat_two_square hp]
  constructor
  · rintro ⟨a, b, hab⟩
    -- Reduce to ℕ: use absolute values
    refine ⟨a.natAbs, b.natAbs, ?_⟩
    have ha2 : (a.natAbs : ℤ) ^ 2 = a ^ 2 := by rw [Int.natAbs_sq]
    have hb2 : (b.natAbs : ℤ) ^ 2 = b ^ 2 := by rw [Int.natAbs_sq]
    exact_mod_cast (show ((a.natAbs : ℤ) ^ 2 + (b.natAbs : ℤ) ^ 2 = p) by linarith)
  · rintro ⟨a, b, hab⟩
    exact ⟨↑a, ↑b, by exact_mod_cast hab⟩

/-! ## Part 3: Concrete Examples -/

-- 2 = 1² + 1²
example : ∃ a b : ℕ, a ^ 2 + b ^ 2 = 2 := ⟨1, 1, by norm_num⟩

-- 5 = 1² + 2² (5 ≡ 1 mod 4)
example : ∃ a b : ℕ, a ^ 2 + b ^ 2 = 5 := ⟨1, 2, by norm_num⟩

-- 13 = 2² + 3² (13 ≡ 1 mod 4)
example : ∃ a b : ℕ, a ^ 2 + b ^ 2 = 13 := ⟨2, 3, by norm_num⟩

-- 17 = 1² + 4² (17 ≡ 1 mod 4)
example : ∃ a b : ℕ, a ^ 2 + b ^ 2 = 17 := ⟨1, 4, by norm_num⟩

-- 29 = 2² + 5² (29 ≡ 1 mod 4)
example : ∃ a b : ℕ, a ^ 2 + b ^ 2 = 29 := ⟨2, 5, by norm_num⟩

-- 3 is NOT a sum of two squares (3 ≡ 3 mod 4)
example : ¬ ∃ a b : ℕ, a ^ 2 + b ^ 2 = 3 :=
  not_sum_sq_of_mod4_eq_three (by decide) (by decide)

-- 7 is NOT a sum of two squares (7 ≡ 3 mod 4)
example : ¬ ∃ a b : ℕ, a ^ 2 + b ^ 2 = 7 :=
  not_sum_sq_of_mod4_eq_three (by decide) (by decide)

-- 11 is NOT a sum of two squares (11 ≡ 3 mod 4)
example : ¬ ∃ a b : ℕ, a ^ 2 + b ^ 2 = 11 :=
  not_sum_sq_of_mod4_eq_three (by decide) (by decide)

/-! ## Part 4: Gaussian Integer Connection -/

/-- An inert prime p ≡ 3 (mod 4) is simultaneously prime in ℤ[i] and inexpressible
    as a sum of two squares. Both facts arise from the same ZMod 4 obstruction:
    squares are 0 or 1 mod 4, so norm(z) = z.re² + z.im² can never equal p ≡ 3 mod 4.
    This is why inert primes cannot factor in ℤ[i]: if p = z·w, then
    norm(z)·norm(w) = p², but neither factor can have norm p (a non-square mod 4),
    so one has norm 1 (a unit) and one has norm p². -/
theorem inert_prime_not_sum_sq {p : ℕ} (hp : p.Prime) (hmod : p % 4 = 3) :
    Prime ((↑p : GaussianInt)) ∧ ¬ ∃ a b : ℕ, a ^ 2 + b ^ 2 = p :=
  ⟨inert_prime hp hmod, not_sum_sq_of_mod4_eq_three hp hmod⟩

/-- The converse: if p is a prime that splits in ℤ[i] (has a Gaussian factor of norm p),
    then p is a sum of two squares, hence p = 2 or p ≡ 1 (mod 4). -/
theorem split_prime_sum_sq {p : ℕ} (hp : p.Prime)
    (hz : ∃ z : GaussianInt, z.norm.natAbs = p ∧ ¬ IsUnit z) :
    ∃ a b : ℕ, a ^ 2 + b ^ 2 = p := by
  obtain ⟨z, hnorm, _⟩ := hz
  exact ⟨z.re.natAbs, z.im.natAbs, by
    have h1 : z.re ^ 2 + z.im ^ 2 = z.norm := by
      simp [GaussianIntEuclidean.gaussian_norm_formula]; ring
    have h2 : z.norm = (p : ℤ) := by
      rw [← Int.natAbs_of_nonneg (GaussianInt.norm_nonneg z), hnorm]
    have h3 : (z.re.natAbs : ℤ) ^ 2 + (z.im.natAbs : ℤ) ^ 2 = (p : ℤ) := by
      rw [Int.natAbs_sq, Int.natAbs_sq]
      linarith
    exact_mod_cast h3⟩

end BezoutIdentityOQ02OQ01OQ02OQ02OQ02
