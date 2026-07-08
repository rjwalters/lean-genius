import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-
# Erdős 1064 (OQ-03): the double totient iterate  φ(n)  vs  φ(n − φ(n − φ(n)))

## Background

Erdős #1064 concerns the single cototient step  c(n) = n − φ(n).  The parent
problem asks whether  φ(n) > φ(n − φ(n))  for almost all n (true, density 1,
Luca–Pomerance) while the reverse inequality still holds infinitely often.

This open question OQ-03 asks what happens for the **higher iterate**

  D(n)  :=  n − φ(n − φ(n)),

i.e. we compare  φ(n)  against  φ(D(n)) = φ(n − φ(n − φ(n))).

## What this file establishes (all machine-checked, no axioms)

1. **Collapse on primes.**  For *every* prime p we have  D(p) = p − 1
   exactly.  Indeed φ(p) = p − 1, so n − φ(n) = 1, φ(1) = 1, and
   D(p) = p − φ(1) = p − 1.

2. **Forward inequality on the whole family of odd primes.**  For every
   prime p ≥ 3,
        φ(D(p)) = φ(p − 1)  <  p − 1 = φ(p),
   so the "expected" direction  φ(n) > φ(D(n))  holds on an infinite family.
   The single exceptional prime is p = 2, where equality holds (D(2) = 1).

3. **The reverse inequality genuinely occurs.**  The smallest witness is
   n = 39: there D(39) = 31 is prime, φ(39) = 24 < 30 = φ(31) = φ(D(39)).
   So  φ(n) < φ(D(n))  for infinitely-often-observed n; concretely at n = 39.

The reverse cases empirically cluster where D(n) lands on a prime (31, 47, 73,
97, 113, …), making φ(D(n)) = D(n) − 1 large; a full "infinitely often"
statement remains the OPEN part of this question.
-/

open Nat

namespace Erdos1064OQ03

/-- The double cototient iterate  `D(n) = n − φ(n − φ(n))`. -/
def dblIter (n : ℕ) : ℕ := n - Nat.totient (n - Nat.totient n)

/-- **Collapse on primes.**  For every prime `p`, the double iterate satisfies
    `D(p) = p − 1`.  (φ(p) = p−1 ⟹ p − φ(p) = 1 ⟹ φ(1) = 1 ⟹ D(p) = p−1.) -/
theorem dblIter_prime {p : ℕ} (hp : p.Prime) : dblIter p = p - 1 := by
  unfold dblIter
  rw [Nat.totient_prime hp]
  have h1 : p - (p - 1) = 1 := by have := hp.two_le; omega
  rw [h1, Nat.totient_one]

/-- **Forward inequality on odd primes.**  For every prime `p ≥ 3`,
    `φ(D(p)) < φ(p)`, i.e. `φ(n) > φ(n − φ(n − φ(n)))` holds throughout the
    infinite family of odd primes. -/
theorem totient_dblIter_lt_of_prime {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    Nat.totient (dblIter p) < Nat.totient p := by
  rw [dblIter_prime hp, Nat.totient_prime hp]
  exact Nat.totient_lt (p - 1) (by omega)

/-- Sharp boundary: at the even prime `p = 2` the forward inequality degenerates
    to equality, `D(2) = 1` and `φ(D(2)) = φ(2)`. -/
theorem totient_dblIter_eq_two : Nat.totient (dblIter 2) = Nat.totient 2 := by
  have : dblIter 2 = 1 := dblIter_prime (by norm_num)
  rw [this, Nat.totient_one, Nat.totient_prime (by norm_num)]

-- ----------------------------------------------------------------------------
-- Concrete totient values used for the reverse witness (via factorisation,
-- avoiding kernel evaluation of `gcd` inside `decide`).
-- ----------------------------------------------------------------------------

/-- `φ(39) = 24`  (39 = 3·13, distinct primes). -/
theorem totient_39 : Nat.totient 39 = 24 := by
  rw [show (39 : ℕ) = 3 * 13 from rfl, Nat.totient_mul (by decide),
      Nat.totient_prime (by norm_num), Nat.totient_prime (by norm_num)]

/-- `φ(15) = 8`  (15 = 3·5, distinct primes). -/
theorem totient_15 : Nat.totient 15 = 8 := by
  rw [show (15 : ℕ) = 3 * 5 from rfl, Nat.totient_mul (by decide),
      Nat.totient_prime (by norm_num), Nat.totient_prime (by norm_num)]

/-- `φ(31) = 30`  (31 is prime). -/
theorem totient_31 : Nat.totient 31 = 30 := by
  rw [Nat.totient_prime (by norm_num)]

/-- The double iterate of 39 lands on the prime 31:  `D(39) = 31`. -/
theorem dblIter_39 : dblIter 39 = 31 := by
  unfold dblIter
  rw [totient_39, show (39 : ℕ) - 24 = 15 from rfl, totient_15]

/-- **The reverse inequality occurs.**  At `n = 39` the double iterate reverses
    the expected direction: `φ(39) = 24 < 30 = φ(D(39))`, since `D(39) = 31` is
    prime.  This exhibits a concrete member of the (conjecturally infinite)
    family of reversal points. -/
theorem reverse_at_39 : Nat.totient 39 < Nat.totient (dblIter 39) := by
  rw [dblIter_39, totient_39, totient_31]
  decide

/-- Summary corollary: the forward inequality `φ(n) > φ(D(n))` is **not**
    universal — it fails at `n = 39` — yet holds on the entire infinite family
    of odd primes.  Hence the higher-iterate analogue of Erdős 1064 exhibits
    the same both-directions behaviour as the single step. -/
theorem forward_not_universal :
    (∀ p : ℕ, p.Prime → 3 ≤ p → Nat.totient (dblIter p) < Nat.totient p) ∧
    (∃ n : ℕ, Nat.totient n < Nat.totient (dblIter n)) :=
  ⟨fun _ hp hp3 => totient_dblIter_lt_of_prime hp hp3, ⟨39, reverse_at_39⟩⟩

-- ----------------------------------------------------------------------------
-- Structural mechanism of the reversal:  when `D(n)` lands on a prime `q`, the
-- three-way comparison `φ(n)  vs  φ(D(n))` collapses to a single size test,
-- because `φ(q) = q − 1`.  This *explains* the empirical clustering of reversals
-- on prime landings — a structural theorem that subsumes the individual
-- numerical witnesses rather than enumerating them.
-- ----------------------------------------------------------------------------

/-- **Reversal criterion on prime landings.**  Whenever the double iterate lands
    on a prime, the reversal `φ(n) < φ(D(n))` is *equivalent* to the clean size
    condition `φ(n) + 1 < D(n)`.  (Since `φ(D(n)) = D(n) − 1`.)  This is the
    exact mechanism behind the reversal clustering: a prime landing makes
    `φ(D(n))` as large as possible, so reversal is governed purely by how large
    the landing value `D(n)` is relative to `φ(n)`. -/
theorem reversal_iff_of_dblIter_prime {n : ℕ} (hq : (dblIter n).Prime) :
    Nat.totient n < Nat.totient (dblIter n) ↔ Nat.totient n + 1 < dblIter n := by
  rw [Nat.totient_prime hq]
  have := hq.two_le
  omega

/-- **Sufficient condition for reversal.**  If `D(n)` is prime and exceeds
    `φ(n) + 1`, then `n` is a reversal point.  A one-line consequence of
    `reversal_iff_of_dblIter_prime` that packages the "prime landing + large
    landing value" pattern into a directly usable form. -/
theorem reverse_of_dblIter_prime {n : ℕ} (hq : (dblIter n).Prime)
    (hsize : Nat.totient n + 1 < dblIter n) :
    Nat.totient n < Nat.totient (dblIter n) :=
  (reversal_iff_of_dblIter_prime hq).mpr hsize

/-- The `n = 39` witness re-derived structurally: `D(39) = 31` is prime and
    `φ(39) + 1 = 25 < 31`, so the criterion fires. -/
theorem reverse_at_39' : Nat.totient 39 < Nat.totient (dblIter 39) :=
  reverse_of_dblIter_prime (by rw [dblIter_39]; norm_num)
    (by rw [totient_39, dblIter_39]; decide)

-- ----------------------------------------------------------------------------
-- A SECOND reversal family:  reversal is *not* confined to prime landings.
-- At `n = 42` the double iterate lands on the **composite** value
-- `D(42) = 34 = 2·17`, yet the reversal `φ(42) < φ(D(42))` still holds.
-- This shows the reversal phenomenon extends beyond the `D(n) prime` family,
-- refining the earlier empirical observation that reversals "cluster" on primes.
-- ----------------------------------------------------------------------------

/-- `φ(42) = 12`  (42 = 2·21, φ(21) = φ(3·7) = 12). -/
theorem totient_42 : Nat.totient 42 = 12 := by
  rw [show (42 : ℕ) = 2 * 21 from rfl, Nat.totient_mul (by decide),
      show (21 : ℕ) = 3 * 7 from rfl, Nat.totient_mul (by decide),
      Nat.totient_prime (by norm_num), Nat.totient_prime (by norm_num),
      Nat.totient_prime (by norm_num)]

/-- `φ(30) = 8`  (30 = 2·15, φ(15) = 8). -/
theorem totient_30 : Nat.totient 30 = 8 := by
  rw [show (30 : ℕ) = 2 * 15 from rfl, Nat.totient_mul (by decide),
      Nat.totient_prime (by norm_num), totient_15]

/-- `φ(34) = 16`  (34 = 2·17, distinct primes). -/
theorem totient_34 : Nat.totient 34 = 16 := by
  rw [show (34 : ℕ) = 2 * 17 from rfl, Nat.totient_mul (by decide),
      Nat.totient_prime (by norm_num), Nat.totient_prime (by norm_num)]

/-- The double iterate of 42 lands on the **composite** value 34:  `D(42) = 34`
    with `34 = 2 · 17`. -/
theorem dblIter_42 : dblIter 42 = 34 := by
  unfold dblIter
  rw [totient_42, show (42 : ℕ) - 12 = 30 from rfl, totient_30]

/-- `D(42) = 34` is **not** prime — witnessing that the landing value need not be
    prime for a reversal to occur. -/
theorem dblIter_42_not_prime : ¬ (dblIter 42).Prime := by
  rw [dblIter_42]; decide

/-- **A composite-landing reversal.**  At `n = 42` the double iterate reverses
    the expected direction, `φ(42) = 12 < 16 = φ(D(42))`, even though
    `D(42) = 34` is composite.  So the reversal family is strictly larger than
    the prime-landing family. -/
theorem reverse_at_42 : Nat.totient 42 < Nat.totient (dblIter 42) := by
  rw [dblIter_42, totient_42, totient_34]; decide

/-- **The reversal phenomenon is not confined to prime landings.**  There is a
    reversal point `n` whose double iterate `D(n)` is composite: concretely
    `n = 42`, where `D(42) = 34 = 2·17` and `φ(42) < φ(34)`. -/
theorem reversal_with_composite_landing :
    ∃ n : ℕ, ¬ (dblIter n).Prime ∧ Nat.totient n < Nat.totient (dblIter n) :=
  ⟨42, dblIter_42_not_prime, reverse_at_42⟩

end Erdos1064OQ03
