import Mathlib.NumberTheory.SumFourSquares
import Mathlib.Tactic

/-!
# Legendre's Three Squares Theorem

## What This Proves
A natural number n can be expressed as the sum of three squares of integers
if and only if n is NOT of the form 4^a(8b + 7), where a and b are non-negative integers.

This is a deeper refinement of Lagrange's Four Squares Theorem (every natural is a sum of
four squares). The "excluded" numbers form a sparse but infinite set: 7, 15, 23, 28, 31, ...

## Historical Context
- **1770**: Lagrange proves every natural is a sum of four squares
- **1797-1798**: Legendre proves this three-squares characterization
- **1801**: Gauss provides a more general result using quadratic form theory
- **1850**: Dirichlet gives an elegant proof using his theorem on primes in arithmetic progressions

## Approach
- **Necessity (→)**: FULLY PROVED. Squares mod 8 are in {0, 1, 4}, so sums of three squares
  mod 8 can only achieve {0, 1, 2, 3, 4, 5, 6}. Numbers ≡ 7 (mod 8) cannot be sums of three
  squares. The 4^a factor is handled by strong induction with a descent argument.

- **Sufficiency (←)**: This direction requires either:
  1. Dirichlet's theorem on primes in arithmetic progressions (recently added to Mathlib), OR
  2. Theory of ternary quadratic forms (class numbers, genera)

## Status
- [x] Characterization of excluded form defined
- [x] Key lemmas stated (squares mod 8)
- [x] **Necessity direction FULLY PROVED** (no axioms!)
- [x] Examples and computational verification
- [ ] Sufficiency proof (requires ternary quadratic form theory)

## Mathlib Dependencies
- `Nat.sum_four_squares` : Every n is a sum of 4 squares
- Modular arithmetic lemmas

## Connection to Wiedijk 100
This is a candidate for the Wiedijk 100 theorems list. The four squares theorem is #19;
the three squares theorem is a natural strengthening.

## What Would Be Needed for Full Proof
1. **Necessity**: DONE! Proved via modular arithmetic and descent.
2. **Sufficiency**: Either prove via Dirichlet's theorem on primes in arithmetic progressions
   (showing every n ≡ 3 (mod 8) has prime factors ≡ 1 (mod 4)), or use ternary quadratic
   form theory and class number formulas.
-/

namespace ThreeSquares

/-! ## The Excluded Form -/

/-- Predicate for numbers of the form 4^a(8b + 7).
These are exactly the numbers that CANNOT be written as sums of three squares. -/
def IsExcludedForm (n : ℕ) : Prop :=
  ∃ a b : ℕ, n = 4 ^ a * (8 * b + 7)

/-- The excluded form is decidable. -/
noncomputable instance : DecidablePred IsExcludedForm :=
  fun _ => Classical.propDecidable _

/-- 7 is in excluded form (a=0, b=0). -/
example : IsExcludedForm 7 := ⟨0, 0, rfl⟩

/-- 15 is in excluded form (a=0, b=1). -/
example : IsExcludedForm 15 := ⟨0, 1, rfl⟩

/-- 28 = 4 * 7 is in excluded form (a=1, b=0). -/
example : IsExcludedForm 28 := ⟨1, 0, rfl⟩

/-- 23 is in excluded form (a=0, b=2). -/
example : IsExcludedForm 23 := ⟨0, 2, rfl⟩

/-- 112 = 16 * 7 is in excluded form (a=2, b=0). -/
example : IsExcludedForm 112 := ⟨2, 0, rfl⟩

/-! ## Key Lemmas: Squares Modulo 8 and 4 -/

/-- Natural number version: A square is congruent to 0, 1, or 4 modulo 8. -/
lemma nat_sq_mod_eight (x : ℕ) : x ^ 2 % 8 = 0 ∨ x ^ 2 % 8 = 1 ∨ x ^ 2 % 8 = 4 := by
  have h : x % 8 < 8 := Nat.mod_lt x (by norm_num)
  have key : ∀ r : ℕ, r < 8 → r ^ 2 % 8 = 0 ∨ r ^ 2 % 8 = 1 ∨ r ^ 2 % 8 = 4 := by
    intro r hr
    interval_cases r <;> decide
  have hxmod := key (x % 8) h
  have hsq : x ^ 2 % 8 = (x % 8) ^ 2 % 8 := by conv_lhs => rw [Nat.pow_mod]
  rw [hsq]; exact hxmod

/-- Integer version: A square is congruent to 0, 1, or 4 modulo 8. -/
lemma int_sq_mod_eight (x : ℤ) : x ^ 2 % 8 = 0 ∨ x ^ 2 % 8 = 1 ∨ x ^ 2 % 8 = 4 := by
  have key : x ^ 2 % 8 = ((x % 8) * (x % 8)) % 8 := by rw [pow_two, Int.mul_emod]
  rw [key]
  have hres : x % 8 = 0 ∨ x % 8 = 1 ∨ x % 8 = 2 ∨ x % 8 = 3 ∨
              x % 8 = 4 ∨ x % 8 = 5 ∨ x % 8 = 6 ∨ x % 8 = 7 := by omega
  rcases hres with h | h | h | h | h | h | h | h <;> simp [h]

/-- Helper: checking that sum of three residues in {0,1,4} is never 7 mod 8. -/
private lemma check_sum_ne_7 (ra rb rc : ℤ) (hra : ra = 0 ∨ ra = 1 ∨ ra = 4)
    (hrb : rb = 0 ∨ rb = 1 ∨ rb = 4) (hrc : rc = 0 ∨ rc = 1 ∨ rc = 4) :
    (ra + rb + rc) % 8 ≠ 7 := by
  rcases hra with h | h | h <;> rcases hrb with h' | h' | h' <;>
  rcases hrc with h'' | h'' | h'' <;> simp only [h, h', h''] <;> decide

/-- Sum of three integer squares mod 8 can never be 7. -/
lemma sum_three_sq_mod_eight_ne_seven (a b c : ℤ) : (a ^ 2 + b ^ 2 + c ^ 2) % 8 ≠ 7 := by
  have ha := int_sq_mod_eight a
  have hb := int_sq_mod_eight b
  have hc := int_sq_mod_eight c
  have hmod : (a ^ 2 + b ^ 2 + c ^ 2) % 8 = ((a^2 % 8) + (b^2 % 8) + (c^2 % 8)) % 8 := by
    simp only [Int.add_emod, Int.emod_emod_of_dvd _ (by norm_num : (8 : ℤ) ∣ 8)]
  rw [hmod]
  exact check_sum_ne_7 (a^2 % 8) (b^2 % 8) (c^2 % 8) ha hb hc

/-- Numbers ≡ 7 (mod 8) cannot be sums of three squares. -/
lemma seven_mod_eight_not_sum_three_sq_int (n : ℤ) (h : n % 8 = 7) :
    ¬∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = n := by
  intro ⟨a, b, c, hab⟩
  have hne7 := sum_three_sq_mod_eight_ne_seven a b c
  rw [hab] at hne7
  exact hne7 h

/-- Integer squares mod 4 are 0 or 1. -/
lemma int_sq_mod_four (x : ℤ) : x ^ 2 % 4 = 0 ∨ x ^ 2 % 4 = 1 := by
  have key : x ^ 2 % 4 = ((x % 4) * (x % 4)) % 4 := by rw [pow_two, Int.mul_emod]
  rw [key]
  have : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3 := by omega
  rcases this with h | h | h | h <;> simp [h]

/-- If an integer square is 0 mod 4, the integer is even. -/
lemma sq_mod_four_zero_implies_even (x : ℤ) (h : x ^ 2 % 4 = 0) : 2 ∣ x := by
  have hx : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3 := by omega
  have key : x ^ 2 % 4 = ((x % 4) * (x % 4)) % 4 := by rw [pow_two, Int.mul_emod]
  rw [key] at h
  rcases hx with hx' | hx' | hx' | hx'
  · exact Int.dvd_of_emod_eq_zero (by omega : x % 2 = 0)
  · simp [hx'] at h
  · exact Int.dvd_of_emod_eq_zero (by omega : x % 2 = 0)
  · simp [hx'] at h

/-- If 4 divides a sum of three squares, each square's root is even. -/
lemma four_dvd_sum_three_sq_implies_even (a b c : ℤ)
    (h : 4 ∣ a ^ 2 + b ^ 2 + c ^ 2) : 2 ∣ a ∧ 2 ∣ b ∧ 2 ∣ c := by
  have ha := int_sq_mod_four a
  have hb := int_sq_mod_four b
  have hc := int_sq_mod_four c
  have hsum : (a^2 % 4 + b^2 % 4 + c^2 % 4) % 4 = 0 := by
    have hdiv : (a ^ 2 + b ^ 2 + c ^ 2) % 4 = 0 := by obtain ⟨k, hk⟩ := h; omega
    have : (a ^ 2 + b ^ 2 + c ^ 2) % 4 = (a^2 % 4 + b^2 % 4 + c^2 % 4) % 4 := by simp [Int.add_emod]
    omega
  rcases ha with ha' | ha' <;> rcases hb with hb' | hb' <;> rcases hc with hc' | hc'
  all_goals simp only [ha', hb', hc'] at hsum
  · exact ⟨sq_mod_four_zero_implies_even a ha', sq_mod_four_zero_implies_even b hb',
           sq_mod_four_zero_implies_even c hc'⟩
  all_goals omega

/-- Helper: dividing excluded form by 4 preserves the structure. -/
private lemma div_four_excluded {n k m : ℕ} (hn : n = 4 ^ (k + 1) * (8 * m + 7)) :
    n / 4 = 4 ^ k * (8 * m + 7) := by
  have h1 : n = 4 * (4 ^ k * (8 * m + 7)) := by rw [hn, pow_succ]; ring
  rw [h1]
  exact Nat.mul_div_cancel_left _ (by norm_num : 0 < 4)

/-! ## Necessity: FULLY PROVED -/

/-- **Necessity Theorem** (PROVED): Numbers of excluded form are NOT sums of three squares.

The proof uses:
1. Squares mod 8 ∈ {0, 1, 4}, so sums of three squares mod 8 ∈ {0,1,2,3,4,5,6} - never 7
2. Strong induction on n with descent: if 4|n and n = a² + b² + c², then 2|a,b,c,
   so n/4 = (a/2)² + (b/2)² + (c/2)² is also a sum of three squares, contradicting IH -/
theorem excluded_form_not_sum_three_sq {n : ℕ} (h : IsExcludedForm n) :
    ¬∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    obtain ⟨k, m, hn⟩ := h
    cases k with
    | zero =>
      -- Base case: n = 8m + 7 ≡ 7 (mod 8)
      simp only [pow_zero, one_mul] at hn
      have hmod : (n : ℤ) % 8 = 7 := by omega
      exact seven_mod_eight_not_sum_three_sq_int n hmod
    | succ k' =>
      -- Inductive case: n = 4^(k'+1) * (8m+7)
      intro ⟨x, y, z, hsum⟩
      -- 4 | n
      have hdiv4_n : 4 ∣ n := by
        use 4^k' * (8 * m + 7)
        rw [hn, pow_succ]; ring
      -- So 4 | x² + y² + z²
      have hdiv4 : 4 ∣ (x ^ 2 + y ^ 2 + z ^ 2) := by
        rw [hsum]; exact_mod_cast hdiv4_n
      -- Therefore 2 | x, 2 | y, 2 | z
      have heven := four_dvd_sum_three_sq_implies_even x y z hdiv4
      obtain ⟨x', hx⟩ := heven.1
      obtain ⟨y', hy⟩ := heven.2.1
      obtain ⟨z', hz⟩ := heven.2.2
      -- n/4 is also in excluded form
      have hn' : n / 4 = 4 ^ k' * (8 * m + 7) := div_four_excluded hn
      have hexcl' : IsExcludedForm (n / 4) := ⟨k', m, hn'⟩
      -- n/4 < n (since n > 0)
      have hn_pos : 0 < n := by rw [hn]; positivity
      have hlt : n / 4 < n := Nat.div_lt_self hn_pos (by norm_num : 1 < 4)
      -- By IH, n/4 is not a sum of three squares
      have ih' := ih (n / 4) hlt hexcl'
      -- But we can derive: n/4 = x'^2 + y'^2 + z'^2
      have hsum' : x' ^ 2 + y' ^ 2 + z' ^ 2 = (n / 4 : ℕ) := by
        have hcalc : (x ^ 2 + y ^ 2 + z ^ 2 : ℤ) = 4 * (x' ^ 2 + y' ^ 2 + z' ^ 2) := by
          simp only [hx, hy, hz]; ring
        rw [hsum] at hcalc
        have hpos_sum : 0 ≤ x' ^ 2 + y' ^ 2 + z' ^ 2 := by positivity
        have hnat_div : (n : ℤ) / 4 = ((n / 4 : ℕ) : ℤ) := (Int.ofNat_ediv n 4).symm
        have hdiv_result : x' ^ 2 + y' ^ 2 + z' ^ 2 = (n : ℤ) / 4 := by omega
        rw [hnat_div] at hdiv_result
        have : (x' ^ 2 + y' ^ 2 + z' ^ 2).toNat = n / 4 := by
          have := congrArg Int.toNat hdiv_result
          simp at this
          exact this
        omega
      -- Contradiction!
      exact ih' ⟨x', y', z', hsum'⟩

/-- **Sufficiency Axiom**: Numbers NOT of excluded form ARE sums of three squares.

This requires Dirichlet's theorem on primes in arithmetic progressions or
ternary quadratic form theory. -/
axiom not_excluded_form_is_sum_three_sq {n : ℕ} (h : ¬IsExcludedForm n) :
    ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = n

/-- **Legendre's Three Squares Theorem** (1797-1798)

A natural number n can be expressed as a sum of three integer squares
if and only if n is NOT of the form 4^a(8b + 7). -/
theorem legendre_three_squares (n : ℕ) :
    (∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = n) ↔ ¬IsExcludedForm n :=
  ⟨fun h hf => excluded_form_not_sum_three_sq hf h, not_excluded_form_is_sum_three_sq⟩

/-! ## Examples: Numbers that ARE sums of three squares -/

example : ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = 0 := ⟨0, 0, 0, rfl⟩
example : ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = 1 := ⟨1, 0, 0, rfl⟩
example : ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = 2 := ⟨1, 1, 0, rfl⟩
example : ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = 3 := ⟨1, 1, 1, rfl⟩
example : ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = 5 := ⟨2, 1, 0, rfl⟩
example : ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = 6 := ⟨2, 1, 1, rfl⟩
example : ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = 8 := ⟨2, 2, 0, rfl⟩
example : ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = 9 := ⟨3, 0, 0, rfl⟩
example : ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = 10 := ⟨3, 1, 0, rfl⟩
example : ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = 12 := ⟨2, 2, 2, rfl⟩
example : ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = 14 := ⟨3, 2, 1, rfl⟩

/-! ## Examples: Numbers that are NOT sums of three squares -/

/-- 7 cannot be written as a sum of three squares. -/
example : ¬∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = 7 :=
  excluded_form_not_sum_three_sq ⟨0, 0, rfl⟩

/-- 15 cannot be written as a sum of three squares. -/
example : ¬∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = 15 :=
  excluded_form_not_sum_three_sq ⟨0, 1, rfl⟩

/-- 28 = 4 * 7 cannot be written as a sum of three squares. -/
example : ¬∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = 28 :=
  excluded_form_not_sum_three_sq ⟨1, 0, rfl⟩

/-- 31 cannot be written as a sum of three squares. -/
example : ¬∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = 31 :=
  excluded_form_not_sum_three_sq ⟨0, 3, rfl⟩

/-! ## Relationship to Four Squares Theorem -/

/-- Connection: Four squares always suffice (Lagrange). -/
theorem four_squares_always_suffice (n : ℕ) :
    ∃ a b c d : ℕ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = n :=
  Nat.sum_four_squares n

/-- For excluded numbers, the fourth square is essential. -/
theorem fourth_square_essential {n : ℕ} (h : IsExcludedForm n) :
    (∃ a b c d : ℕ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = n) ∧
    ¬∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = n :=
  ⟨Nat.sum_four_squares n, excluded_form_not_sum_three_sq h⟩

/-- 7 = 1² + 1² + 1² + 2² (four squares work) -/
example : ∃ a b c d : ℕ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 7 := ⟨1, 1, 1, 2, rfl⟩

#check legendre_three_squares

end ThreeSquares
