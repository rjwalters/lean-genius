import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic

/-
# The Reciprocity Swap Sign as a mod-4 Decision Rule

Open Question (from `quadratic-reciprocity-oq-03`, sibling of the `p % 8`
factor-2 decision form `quadratic-reciprocity-oq-03-oq-01`):

  The parent's reduction toolkit carries the reciprocity sign as the opaque
  exponent `(-1)^((p/2)·(q/2))`. Package that sign as a **decidable mod-4 test**:
  a branch-free criterion, in terms of `p % 4` and `q % 4` alone, telling the
  Legendre-symbol algorithm whether the swap `(q/p) ↔ (p/q)` is sign-preserving
  or sign-flipping.

Answer: **YES.** The textbook rule — the two symbols *agree* unless **both**
primes are `≡ 3 (mod 4)`, in which case they have *opposite* signs — becomes a
proved biconditional. Mathlib provides only the two one-directional special
cases `legendreSym.quadratic_reciprocity_one_mod_four` (if `p ≡ 1`, agree) and
`legendreSym.quadratic_reciprocity_three_mod_four` (if both `≡ 3`, flip), plus
the exponent-form swap `legendreSym.quadratic_reciprocity'`. It has **no single
iff** stating the full agree/disagree dichotomy in residue terms. This file
supplies it.

## Results

1. `reciprocity_sign_eq_neg_one_iff` — the standalone sign lemma
   `(-1)^((p/2)(q/2)) = -1 ↔ p ≡ 3 ∧ q ≡ 3 (mod 4)` (pure parity arithmetic).
2. `reciprocity_disagree_iff` — `(p/q) = -(q/p) ↔ p ≡ 3 ∧ q ≡ 3 (mod 4)`.
3. `reciprocity_agree_iff` — `(p/q) = (q/p) ↔ p ≡ 1 ∨ q ≡ 1 (mod 4)`.
4. `reciprocity_swap_value` — the sign as a branch: `(p/q) = (if both ≡ 3 then
   -1 else 1) · (q/p)`, the form a recursive algorithm actually evaluates.
5. `agree_iff_not_disagree` — the dichotomy is exhaustive and exclusive.
6. `decide`-verified corroboration on small primes.

Here `legendreSym n a` is the symbol `(a / n)` (modulus first), so
`legendreSym q p` is `(p / q)` and `legendreSym p q` is `(q / p)`.

## Status
- [x] Complete — 0 sorries, 0 axioms
-/

set_option linter.unusedVariables false

open ZMod

namespace QRMod4Sign

-- ============================================================
-- PART 1: The standalone sign lemma (pure parity arithmetic)
-- ============================================================

/-- **The reciprocity sign as a mod-4 condition.**

    For odd `p, q`, the swap sign `(-1)^((p/2)·(q/2))` is `-1` exactly when both
    `p` and `q` are `≡ 3 (mod 4)`. This is the purely arithmetic core of the
    decision rule: it ties the exponent `(p/2)(q/2)` to the joint residue
    condition. The exponent is odd iff both factors `p/2` and `q/2` are odd, and
    for an odd number `p` the half `p/2` is odd iff `p ≡ 3 (mod 4)`. -/
theorem reciprocity_sign_eq_neg_one_iff (p q : ℕ) (hp : p % 2 = 1) (hq : q % 2 = 1) :
    ((-1 : ℤ)) ^ (p / 2 * (q / 2)) = -1 ↔ (p % 4 = 3 ∧ q % 4 = 3) := by
  have hpow : ((-1 : ℤ)) ^ (p / 2 * (q / 2)) = -1 ↔ Odd (p / 2 * (q / 2)) := by
    constructor
    · intro h
      by_contra hodd
      rw [Nat.not_odd_iff_even] at hodd
      rw [hodd.neg_one_pow] at h
      norm_num at h
    · intro h
      exact h.neg_one_pow
  have key : Odd (p / 2 * (q / 2)) ↔ (p % 4 = 3 ∧ q % 4 = 3) := by
    rw [Nat.odd_mul, Nat.odd_iff, Nat.odd_iff]
    omega
  exact hpow.trans key

-- ============================================================
-- PART 2: The agree / disagree biconditionals
-- ============================================================

/-- An odd prime is `≡ 1` or `≡ 3 (mod 4)`. -/
private theorem mod_two_one (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) : p % 2 = 1 :=
  ((Fact.out : p.Prime).eq_two_or_odd).resolve_left hp

/-- `(q / p)` (i.e. `legendreSym p q`) is nonzero when `p ≠ q` are primes, since
    then `p ∤ q`. -/
private theorem legendre_ne_zero (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hpq : p ≠ q) : ((q : ℤ) : ZMod p) ≠ 0 := by
  have e : ((q : ℤ) : ZMod p) = ((q : ℕ) : ZMod p) := by norm_cast
  rw [e]
  intro hz
  rw [ZMod.natCast_eq_zero_iff] at hz
  rw [Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (Fact.out : q.Prime)] at hz
  exact hpq hz

/-- **Disagree criterion.** For distinct odd primes `p, q`, the reciprocity swap
    flips the sign — `(p/q) = -(q/p)` — **iff** both primes are `≡ 3 (mod 4)`.

    This is the genuine biconditional behind Mathlib's one-directional
    `quadratic_reciprocity_three_mod_four`. The forward direction uses that the
    symbols are `±1` (hence nonzero), so `(p/q) = -(q/p)` cannot hold when the
    swap sign is `+1`. -/
theorem reciprocity_disagree_iff (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) :
    legendreSym q p = - legendreSym p q ↔ (p % 4 = 3 ∧ q % 4 = 3) := by
  have hp2 := mod_two_one p hp
  have hq2 := mod_two_one q hq
  have hL0 := legendre_ne_zero p q hpq
  have hval := legendreSym.eq_one_or_neg_one (p := p) hL0
  have hrec := legendreSym.quadratic_reciprocity' (p := p) (q := q) hp hq
  have hsign := reciprocity_sign_eq_neg_one_iff p q hp2 hq2
  rcases Nat.even_or_odd (p / 2 * (q / 2)) with hev | hod
  · -- swap sign is +1: both sides of the iff are false
    rw [hev.neg_one_pow, one_mul] at hrec
    rw [hrec]
    constructor
    · intro hbad
      rcases hval with h1 | h1 <;> rw [h1] at hbad <;> norm_num at hbad
    · intro hbad
      have heq : ((-1 : ℤ)) ^ (p / 2 * (q / 2)) = -1 := hsign.mpr hbad
      rw [hev.neg_one_pow] at heq
      norm_num at heq
  · -- swap sign is -1: both sides of the iff are true
    rw [hod.neg_one_pow, neg_one_mul] at hrec
    constructor
    · intro _
      exact hsign.mp hod.neg_one_pow
    · intro _
      exact hrec

/-- **Agree criterion.** For distinct odd primes `p, q`, the reciprocity swap is
    sign-preserving — `(p/q) = (q/p)` — **iff** at least one of `p, q` is
    `≡ 1 (mod 4)`. This is the exact complement of `reciprocity_disagree_iff`. -/
theorem reciprocity_agree_iff (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) :
    legendreSym q p = legendreSym p q ↔ (p % 4 = 1 ∨ q % 4 = 1) := by
  have hp2 := mod_two_one p hp
  have hq2 := mod_two_one q hq
  have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
  have hq4 : q % 4 = 1 ∨ q % 4 = 3 := by omega
  have hL0 := legendre_ne_zero p q hpq
  have hval := legendreSym.eq_one_or_neg_one (p := p) hL0
  have hrec := legendreSym.quadratic_reciprocity' (p := p) (q := q) hp hq
  have hsign := reciprocity_sign_eq_neg_one_iff p q hp2 hq2
  rcases Nat.even_or_odd (p / 2 * (q / 2)) with hev | hod
  · -- swap sign is +1: LHS holds, and RHS holds since not both ≡ 3
    rw [hev.neg_one_pow, one_mul] at hrec
    constructor
    · intro _
      have hnb : ¬ (p % 4 = 3 ∧ q % 4 = 3) := by
        rw [← hsign, hev.neg_one_pow]; norm_num
      omega
    · intro _
      exact hrec
  · -- swap sign is -1: LHS fails (symbols are ±1) and RHS fails (both ≡ 3)
    rw [hod.neg_one_pow, neg_one_mul] at hrec
    constructor
    · intro hbad
      rw [hrec] at hbad
      rcases hval with h1 | h1 <;> rw [h1] at hbad <;> norm_num at hbad
    · intro hbad
      have heq : ((-1 : ℤ)) ^ (p / 2 * (q / 2)) = -1 := hod.neg_one_pow
      rw [hsign] at heq
      omega

-- ============================================================
-- PART 3: The sign as a branch, and exhaustive/exclusive dichotomy
-- ============================================================

/-- **The swap sign as a branch-free decision.** This is the form a recursive
    Legendre-symbol algorithm actually evaluates: read `p % 4` and `q % 4`, and
    the swap multiplies by `-1` precisely when both are `3`, otherwise by `1`. -/
theorem reciprocity_swap_value (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp : p ≠ 2) (hq : q ≠ 2) :
    legendreSym q p = (if p % 4 = 3 ∧ q % 4 = 3 then (-1 : ℤ) else 1) * legendreSym p q := by
  have hp2 := mod_two_one p hp
  have hq2 := mod_two_one q hq
  have hsign := reciprocity_sign_eq_neg_one_iff p q hp2 hq2
  rw [legendreSym.quadratic_reciprocity' hp hq]
  congr 1
  by_cases h : p % 4 = 3 ∧ q % 4 = 3
  · rw [if_pos h]; exact hsign.mpr h
  · rw [if_neg h]
    rcases Nat.even_or_odd (p / 2 * (q / 2)) with hev | hod
    · exact hev.neg_one_pow
    · exact absurd (hsign.mp hod.neg_one_pow) h

/-- **The dichotomy is exhaustive and exclusive.** For distinct odd primes the
    swap either preserves or flips the sign — never both, never neither — so the
    agree predicate is exactly the negation of the disagree predicate. -/
theorem agree_iff_not_disagree (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) :
    legendreSym q p = legendreSym p q ↔ ¬ (legendreSym q p = - legendreSym p q) := by
  have hp2 := mod_two_one p hp
  have hq2 := mod_two_one q hq
  have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
  have hq4 : q % 4 = 1 ∨ q % 4 = 3 := by omega
  rw [reciprocity_agree_iff p q hp hq hpq, reciprocity_disagree_iff p q hp hq hpq]
  omega

-- ============================================================
-- PART 4: Verified corroboration on small primes
-- ============================================================

section Examples

local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 13) := ⟨by norm_num⟩

/-- `3, 7 ≡ 3 (mod 4)`, so the swap **disagrees**: `(7/3) = -(3/7)`. -/
example : legendreSym 7 3 = - legendreSym 3 7 := by decide

/-- `13 ≡ 1 (mod 4)`, so the swap **agrees**: `(5/13) = (13/5)`. -/
example : legendreSym 13 5 = legendreSym 5 13 := by decide

/-- `11, 7 ≡ 3 (mod 4)`, so the swap **disagrees**: `(7/11) = -(11/7)`. -/
example : legendreSym 11 7 = - legendreSym 7 11 := by decide

/-- `5 ≡ 1 (mod 4)`, so the swap **agrees**: `(3/5) = (5/3)`. -/
example : legendreSym 5 3 = legendreSym 3 5 := by decide

/-- The standalone sign lemma, checked at `p = q = 3` (both `≡ 3 (mod 4)`). -/
example : ((-1 : ℤ)) ^ (3 / 2 * (3 / 2)) = -1 := by decide

end Examples

#check @reciprocity_sign_eq_neg_one_iff
#check @reciprocity_agree_iff
#check @reciprocity_disagree_iff
#check @reciprocity_swap_value
#check @agree_iff_not_disagree

end QRMod4Sign
