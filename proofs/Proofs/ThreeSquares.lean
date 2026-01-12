import Mathlib.NumberTheory.SumFourSquares
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic
import Proofs.ZsqrtdNegTwo

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
        have hnat_div : (n : ℤ) / 4 = ((n / 4 : ℕ) : ℤ) := by
          obtain ⟨k, hk⟩ := hdiv4_n
          subst hk
          simp only [Nat.mul_div_cancel_left k (by norm_num : 0 < 4)]
          have h1 : ((4 * k : ℕ) : ℤ) = 4 * (k : ℤ) := by push_cast; ring
          rw [h1]
          exact Int.mul_ediv_cancel_left k (by norm_num : (4 : ℤ) ≠ 0)
        have hdiv_result : x' ^ 2 + y' ^ 2 + z' ^ 2 = (n : ℤ) / 4 := by omega
        rw [hnat_div] at hdiv_result
        have : (x' ^ 2 + y' ^ 2 + z' ^ 2).toNat = n / 4 := by
          have := congrArg Int.toNat hdiv_result
          simp at this
          exact this
        omega
      -- Contradiction!
      exact ih' ⟨x', y', z', hsum'⟩

/-! ## Partial Sufficiency: Special Cases

The following lemmas prove sufficiency for specific cases. These narrow the gap
toward a full proof of sufficiency. -/

/-- Structural lemma: if n is a sum of 3 squares, so is 4n.
This allows us to reduce the sufficiency proof to cases where 4 ∤ n. -/
lemma four_mul_sum_three_sq {n : ℕ} (h : ∃ a b c : ℤ, a^2 + b^2 + c^2 = n) :
    ∃ a b c : ℤ, a^2 + b^2 + c^2 = (4 * n : ℕ) := by
  obtain ⟨a, b, c, hab⟩ := h
  use 2*a, 2*b, 2*c
  have : (2*a)^2 + (2*b)^2 + (2*c)^2 = 4*(a^2 + b^2 + c^2) := by ring
  rw [this, hab]
  simp

/-- **Square scaling**: If m is a sum of 3 squares, so is k²m.
This is the "easy direction" of the square-free reduction.
Combined with the reverse (which requires more work), this allows reducing
the sufficiency proof to square-free numbers. -/
lemma sq_mul_sum_three_sq {m : ℕ} {k : ℤ} (h : ∃ a b c : ℤ, a^2 + b^2 + c^2 = m) :
    ∃ a b c : ℤ, a^2 + b^2 + c^2 = k^2 * m := by
  obtain ⟨a, b, c, hab⟩ := h
  use k*a, k*b, k*c
  have : (k*a)^2 + (k*b)^2 + (k*c)^2 = k^2 * (a^2 + b^2 + c^2) := by ring
  rw [this, hab]

/-- Natural number version of square scaling. -/
lemma sq_mul_sum_three_sq_nat {m k : ℕ} (h : ∃ a b c : ℤ, a^2 + b^2 + c^2 = m) :
    ∃ a b c : ℤ, a^2 + b^2 + c^2 = (k^2 * m : ℕ) := by
  obtain ⟨a, b, c, hab⟩ := h
  use (k : ℤ)*a, (k : ℤ)*b, (k : ℤ)*c
  have : ((k : ℤ)*a)^2 + ((k : ℤ)*b)^2 + ((k : ℤ)*c)^2 = (k : ℤ)^2 * (a^2 + b^2 + c^2) := by ring
  rw [this, hab]
  push_cast; ring

/-- Every number of the form k²(a² + b² + c²) is a sum of 3 squares.
This provides a path: prove base cases (small numbers or primes),
then scale by squares to cover more. -/
lemma sum_three_sq_of_sq_mul {n k : ℕ} {a b c : ℤ} (h : (k : ℤ)^2 * (a^2 + b^2 + c^2) = n) :
    ∃ x y z : ℤ, x^2 + y^2 + z^2 = n := by
  use (k : ℤ)*a, (k : ℤ)*b, (k : ℤ)*c
  have : ((k : ℤ)*a)^2 + ((k : ℤ)*b)^2 + ((k : ℤ)*c)^2 = (k : ℤ)^2 * (a^2 + b^2 + c^2) := by ring
  rw [this, h]

/-- Odd squares are ≡ 1 (mod 8). -/
private lemma odd_sq_mod_eight {k : ℕ} (hk : Odd k) : k^2 % 8 = 1 := by
  have hkne : k ≠ 0 := by
    intro h
    rw [h] at hk
    exact Nat.not_odd_zero hk
  have hk_mod8 : k % 8 = 1 ∨ k % 8 = 3 ∨ k % 8 = 5 ∨ k % 8 = 7 := by
    have : k % 2 = 1 := Nat.odd_iff.mp hk
    omega
  -- Check each case explicitly
  have hsq_mod : k^2 % 8 = (k % 8)^2 % 8 := Nat.pow_mod k 2 8
  rw [hsq_mod]
  rcases hk_mod8 with h | h | h | h <;> (rw [h]; native_decide)

/-- Excluded form is preserved by odd square multiplication.
If m is in excluded form and k is odd, then k²m is also in excluded form.
This is because k² ≡ 1 (mod 8) when k is odd, so it doesn't change the 8b+7 part. -/
lemma excluded_form_of_odd_sq_mul {m k : ℕ} (hm : IsExcludedForm m) (hk : Odd k) :
    IsExcludedForm (k^2 * m) := by
  obtain ⟨a, b, hm⟩ := hm
  -- k² ≡ 1 (mod 8) when k is odd
  have hodd_sq : k^2 % 8 = 1 := odd_sq_mod_eight hk
  -- k² = 8q + 1 for some q
  obtain ⟨q, hq⟩ : ∃ q, k^2 = 8 * q + 1 := ⟨k^2 / 8, by omega⟩
  -- k² * (8b + 7) = (8q + 1)(8b + 7) = 64qb + 56q + 8b + 7 = 8(8qb + 7q + b) + 7
  use a, 8 * q * b + 7 * q + b
  calc k^2 * m = k^2 * (4^a * (8 * b + 7)) := by rw [hm]
    _ = 4^a * (k^2 * (8 * b + 7)) := by ring
    _ = 4^a * ((8 * q + 1) * (8 * b + 7)) := by rw [hq]
    _ = 4^a * (8 * (8 * q * b + 7 * q + b) + 7) := by ring

/-- **Key structural property**: Excluded form is preserved under square multiplication.
If m is in excluded form, then k²m is also in excluded form.
This follows because 4^a factors can absorb powers of 4 from k²,
and the remaining odd part preserves the 8b+7 structure. -/
lemma excluded_form_of_sq_mul {m k : ℕ} (hm : IsExcludedForm m) (hk : k ≠ 0) :
    IsExcludedForm (k^2 * m) := by
  -- Factor k = 2^e * r where r is odd
  obtain ⟨e, r, hr_odd, hk_eq⟩ := Nat.exists_eq_two_pow_mul_odd hk
  rw [hk_eq]
  -- k² = 4^e * r²
  have hk2 : (2^e * r)^2 = 4^e * r^2 := by
    rw [mul_pow, ← pow_mul]
    congr 1
    have h4 : (4 : ℕ) = 2^2 := by norm_num
    rw [h4, ← pow_mul]
    ring_nf
  rw [hk2]
  -- k²m = 4^e * (r²m)
  have h1 : 4^e * r^2 * m = 4^e * (r^2 * m) := by ring
  rw [h1]
  -- r²m is in excluded form (by odd square preservation)
  have hr2m : IsExcludedForm (r^2 * m) := excluded_form_of_odd_sq_mul hm hr_odd
  -- 4^e * (excluded form) is also excluded form
  obtain ⟨a, b, hr2m_eq⟩ := hr2m
  use e + a, b
  calc 4^e * (r^2 * m) = 4^e * (4^a * (8 * b + 7)) := by rw [hr2m_eq]
    _ = 4^(e + a) * (8 * b + 7) := by rw [pow_add]; ring

/-- **Contrapositive**: If k²m is NOT in excluded form, then m is NOT in excluded form.
This is key for reduction: to show m is a sum of 3 squares, it suffices to
show k²m is a sum of 3 squares for some k. -/
lemma not_excluded_of_sq_mul_not_excluded {m k : ℕ} (hk : k ≠ 0)
    (h : ¬IsExcludedForm (k^2 * m)) : ¬IsExcludedForm m := by
  intro hm
  exact h (excluded_form_of_sq_mul hm hk)

/-- Primes ≡ 1 (mod 4) are sums of 3 squares.
This follows from Fermat's two-squares theorem (they're sums of 2 squares). -/
lemma prime_one_mod_four_is_sum_three_sq {p : ℕ} (hp : Nat.Prime p) (hmod : p % 4 = 1) :
    ∃ a b c : ℤ, a^2 + b^2 + c^2 = p := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have h4 : p % 4 ≠ 3 := by omega
  obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq h4
  refine ⟨a, b, 0, ?_⟩
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
  have h1 : (a : ℤ)^2 = (a^2 : ℕ) := by norm_cast
  have h2 : (b : ℤ)^2 = (b^2 : ℕ) := by norm_cast
  rw [h1, h2]
  norm_cast

/-- Primes ≡ 5 (mod 8) are sums of 3 squares.
Since 5 ≡ 1 (mod 4), this follows from the previous lemma. -/
lemma prime_five_mod_eight_is_sum_three_sq {p : ℕ} (hp : Nat.Prime p) (hmod : p % 8 = 5) :
    ∃ a b c : ℤ, a^2 + b^2 + c^2 = p := by
  apply prime_one_mod_four_is_sum_three_sq hp
  omega

/-- 2 is a sum of 3 squares: 2 = 1² + 1² + 0² -/
lemma two_is_sum_three_sq : ∃ a b c : ℤ, a^2 + b^2 + c^2 = (2 : ℕ) := ⟨1, 1, 0, by norm_num⟩

/-- Primes ≡ 1 (mod 8) are sums of 3 squares.
Since 1 ≡ 1 (mod 4), this follows from the prime_one_mod_four lemma. -/
lemma prime_one_mod_eight_is_sum_three_sq {p : ℕ} (hp : Nat.Prime p) (hmod : p % 8 = 1) :
    ∃ a b c : ℤ, a^2 + b^2 + c^2 = p := by
  apply prime_one_mod_four_is_sum_three_sq hp
  omega

/-! ## Infrastructure for Primes ≡ 3 (mod 8)

The hardest case is primes p ≡ 3 (mod 8). The approach (Ankeny 1957) uses:
1. Find an auxiliary prime q ≡ 1 (mod 4) with specific Jacobi symbol
2. Use Fermat's theorem: q = a² + b²
3. Apply a lattice/Minkowski argument to construct the representation

Key infrastructure available:
- `Nat.infinite_setOf_prime_and_modEq` : Dirichlet's theorem on primes in AP
- `Nat.Prime.sq_add_sq` : Fermat's two squares theorem
- `jacobiSym` : Jacobi symbol with quadratic reciprocity
-/

/-- **Existence of auxiliary primes** (from Dirichlet's theorem).
For any coprime a, q with q > 0, infinitely many primes are ≡ a (mod q). -/
lemma exists_prime_in_ap {q a : ℕ} (hq : q ≠ 0) (hcop : Nat.Coprime a q) (n : ℕ) :
    ∃ p : ℕ, Nat.Prime p ∧ p > n ∧ p % q = a % q := by
  have hinf := Nat.infinite_setOf_prime_and_modEq hq hcop
  have hne : {p | Nat.Prime p ∧ p ≡ a [MOD q]}.Nonempty := hinf.nonempty
  -- Get a prime greater than n
  have := Set.Infinite.exists_gt hinf n
  obtain ⟨p, ⟨hp_prime, hp_mod⟩, hp_gt⟩ := this
  use p
  refine ⟨hp_prime, hp_gt, ?_⟩
  -- Convert the modular congruence
  simp only [Nat.ModEq] at hp_mod
  exact hp_mod

/-- For p ≡ 3 (mod 8), there exists a prime q ≡ 1 (mod 4) with q > p. -/
lemma exists_auxiliary_prime_for_3_mod_8 (p : ℕ) (_hp : Nat.Prime p) (_hmod : p % 8 = 3) :
    ∃ q : ℕ, Nat.Prime q ∧ q > p ∧ q % 4 = 1 := by
  have h4 : (4 : ℕ) ≠ 0 := by norm_num
  have hcop : Nat.Coprime 1 4 := by norm_num
  obtain ⟨q, hq_prime, hq_gt, hq_mod⟩ := exists_prime_in_ap h4 hcop p
  exact ⟨q, hq_prime, hq_gt, by simpa using hq_mod⟩

/-- The auxiliary prime q ≡ 1 (mod 4) is a sum of two squares.
This follows directly from Fermat's two squares theorem. -/
lemma auxiliary_prime_is_sum_two_sq {q : ℕ} (hq : Nat.Prime q) (hmod : q % 4 = 1) :
    ∃ a b : ℕ, a^2 + b^2 = q := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  have h4 : q % 4 ≠ 3 := by omega
  exact Nat.Prime.sq_add_sq h4

/-! ## Quadratic Residue Infrastructure for Ankeny's Approach

For primes p ≡ 3 (mod 8), the Ankeny approach uses:
1. Find auxiliary prime q ≡ 1 (mod 4) with specific Jacobi symbol properties
2. Use q = a² + b² (Fermat)
3. Apply lattice/Minkowski argument

The key quadratic residue facts we need:
- For p ≡ 3 (mod 4): -1 is NOT a QR mod p (first supplementary law)
- For q ≡ 1 (mod 4): -1 IS a QR mod q (first supplementary law)
- Quadratic reciprocity relates (p|q) and (q|p)
-/

/-- For primes p ≡ 3 (mod 4), -1 is not a quadratic residue mod p.
This is the first supplementary law of quadratic reciprocity. -/
lemma neg_one_not_qr_of_three_mod_four {p : ℕ} [Fact (Nat.Prime p)] (hmod : p % 4 = 3) :
    legendreSym p (-1) = -1 := by
  have hp2 : p ≠ 2 := by omega
  rw [legendreSym.at_neg_one hp2, ZMod.χ₄_nat_three_mod_four hmod]

/-- For primes q ≡ 1 (mod 4), -1 is a quadratic residue mod q.
This is the first supplementary law of quadratic reciprocity. -/
lemma neg_one_is_qr_of_one_mod_four {q : ℕ} [Fact (Nat.Prime q)] (hmod : q % 4 = 1) :
    legendreSym q (-1) = 1 := by
  have hq2 : q ≠ 2 := by omega
  rw [legendreSym.at_neg_one hq2, ZMod.χ₄_nat_one_mod_four hmod]

/-- The product pq where p ≡ 3 (mod 8) and q ≡ 1 (mod 4) can be analyzed
using quadratic reciprocity to find representations.
For p ≡ 3 (mod 8), we have p ≡ 3 (mod 4), so legendreSym p (-1) = -1.
For q ≡ 1 (mod 4), we have legendreSym q (-1) = 1, and q = a² + b². -/
lemma product_structure_for_three_mod_eight {p q : ℕ} (_hp : Nat.Prime p) (hq : Nat.Prime q)
    (_hp_mod : p % 8 = 3) (hq_mod : q % 4 = 1) :
    ∃ a b : ℕ, a^2 + b^2 = q := by
  exact auxiliary_prime_is_sum_two_sq hq hq_mod

/-- **KEY LEMMA (via ℤ[√-2] approach)**:
A prime p ≡ 3 (mod 8) is a sum of three squares.

**Proof strategy**:
1. p ≡ 3 (mod 8) ⟹ -2 is a QR mod p (second supplementary law)
2. -2 is QR mod p ⟹ p = a² + 2b² (ℤ[√-2] is a Euclidean domain)
3. p = a² + 2b² = a² + b² + b² (trivial identity)

The first step uses `ZMod.exists_sq_eq_neg_two_iff` from Mathlib.
The second step requires proving ℤ[√-2] is a UFD, which is axiomatized in ZsqrtdNegTwo.lean.
The third step is a trivial algebraic identity. -/
lemma prime_three_mod_eight_is_sum_three_sq {p : ℕ} (hp : Nat.Prime p) (hmod : p % 8 = 3) :
    ∃ a b c : ℤ, a^2 + b^2 + c^2 = p :=
  SqAddTwoSq.prime_three_mod_eight_is_sum_three_sq' hp hmod

/-- **Odd primes NOT ≡ 7 (mod 8) are sums of 3 squares.**
This combines the cases p ≡ 1, 3, 5 (mod 8).
Note: primes ≡ 7 (mod 8) are excluded form (= 4^0 * (8b + 7)) and cannot be sums of 3 squares. -/
lemma odd_prime_not_7_mod_8_is_sum_three_sq {p : ℕ} (hp : Nat.Prime p) (hodd : Odd p)
    (hne7 : p % 8 ≠ 7) :
    ∃ a b c : ℤ, a^2 + b^2 + c^2 = p := by
  -- Odd primes have p % 8 ∈ {1, 3, 5, 7}
  have hodd8 : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by
    have h2 : p % 2 = 1 := Nat.odd_iff.mp hodd
    have h82 : p % 8 % 2 = p % 2 := Nat.mod_mod_of_dvd p (by norm_num : 2 ∣ 8)
    omega
  rcases hodd8 with h | h | h | h
  · exact prime_one_mod_eight_is_sum_three_sq hp h
  · exact prime_three_mod_eight_is_sum_three_sq hp h
  · exact prime_five_mod_eight_is_sum_three_sq hp h
  · omega  -- contradicts hne7

/-! ## Dirichlet's Key Lemma (Bridge to Sufficiency)

**The Real Gap**: All PRIMES ≢ 7 (mod 8) are already proved to be sums of three squares:
- p ≡ 1 (mod 8): `prime_one_mod_eight_is_sum_three_sq`
- p ≡ 3 (mod 8): `prime_three_mod_eight_is_sum_three_sq` (via ℤ[√-2])
- p ≡ 5 (mod 8): `prime_five_mod_eight_is_sum_three_sq`

**Why composites aren't automatic**: Sums of 3 squares are NOT multiplicatively closed!
Example: 3 = 1² + 1² + 1² and 5 = 1² + 2² + 0², but 3 × 5 = 15 is EXCLUDED (= 8×1 + 7).

**Dirichlet's Key Lemma** (1850): The bridge for arbitrary n.
> If n > 1, d > 0, and -d is a quadratic residue mod (dn - 1), then n = x² + y² + z².

This directly represents ANY n (not through factorization) by finding appropriate d based on n mod 8.
-/

/-- **Dirichlet's Key Lemma** (Lemma 4.1, 1850)

For n > 1, d > 0, and p = dn - 1 a prime, if -d is a quadratic residue modulo p,
then n can be expressed as a sum of three integer squares.

**How this completes the proof**:
For each n ≢ 0 (mod 4) that is not excluded:
- n ≡ 1 (mod 8): Use d = 1, need -1 QR mod (n-1). Since n ≡ 1 (mod 8), n-1 ≡ 0 (mod 8).
- n ≡ 2 (mod 8): Use d = 2, need -2 QR mod (2n-1).
- n ≡ 3 (mod 8): Use d = 2, find suitable prime factor.
- n ≡ 5 (mod 8): Similar to n ≡ 1.
- n ≡ 6 (mod 8): Similar to n ≡ 2.

The 4^a factor is handled by scaling: if 4n = (2a)² + (2b)² + (2c)², then n = a² + b² + c².

**Proof sketch**: Uses Minkowski's theorem on lattices (available in Mathlib as
`exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`) to find lattice points
in a suitable ellipsoid.

**Key insight**: The Jacobi symbol can be used instead of Legendre symbol, avoiding
the prime requirement on p directly - but for the Minkowski construction, we need
p prime anyway to get the right lattice structure.
-/
axiom dirichlet_key_lemma {n d p : ℕ} (hn : n > 1) (hd : d > 0) (hp : p = d * n - 1)
    [Fact (Nat.Prime p)] (hqr : legendreSym p (-d : ℤ) = 1) :
    ∃ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = n

/-! ### Infrastructure for Minkowski's Theorem Application

To prove `dirichlet_key_lemma`, we need:
1. Define ℤ³ as an AddSubgroup of EuclideanSpace ℝ (Fin 3)
2. Establish the unit cube as a fundamental domain with Haar measure 1
3. Define ellipsoid E_d,n = {(x,y,z) | x² + dy² + dz² ≤ dn}
4. Show vol(E_d,n) = (4π/3)·dn·√d > 8 for suitable parameters
5. Apply Minkowski's theorem to extract a nonzero lattice point
-/

open MeasureTheory in
/-- The standard integer lattice ℤ³ embedded in ℝ³. -/
def intLattice3 : AddSubgroup (EuclideanSpace ℝ (Fin 3)) where
  carrier := {v | ∀ i, ∃ n : ℤ, v i = n}
  zero_mem' := fun i => ⟨0, by simp⟩
  add_mem' := fun {a b} ha hb i => by
    obtain ⟨na, hna⟩ := ha i
    obtain ⟨nb, hnb⟩ := hb i
    exact ⟨na + nb, by simp [hna, hnb]⟩
  neg_mem' := fun {a} ha i => by
    obtain ⟨na, hna⟩ := ha i
    exact ⟨-na, by simp [hna]⟩

/-- The lattice ℤ³ is countable via injection to (Fin 3 → ℤ). -/
instance : Countable intLattice3 := by
  -- Use Function.Injective.countable: if f : A → B is injective and B is countable, then A is countable
  have h : Function.Injective (fun (v : intLattice3) i => (v.2 i).choose) := by
    intro ⟨v, hv⟩ ⟨w, hw⟩ heq
    simp only [Subtype.mk.injEq]
    ext i
    have hvi : v i = ↑((hv i).choose) := (hv i).choose_spec
    have hwi : w i = ↑((hw i).choose) := (hw i).choose_spec
    have heqi : (hv i).choose = (hw i).choose := congr_fun heq i
    rw [hvi, hwi, heqi]
  exact h.countable

/-- The standard fundamental domain: the unit cube [0,1)³. -/
def unitCube3 : Set (EuclideanSpace ℝ (Fin 3)) :=
  {v | ∀ i, 0 ≤ v i ∧ v i < 1}

/-- The unit cube is measurable. -/
theorem unitCube3_measurableSet : MeasurableSet unitCube3 := by
  sorry -- Would use MeasurableSet.pi and Icc measurability

/-- The unit cube is a fundamental domain for ℤ³.

This establishes that every point in ℝ³ can be uniquely written as
(lattice point) + (point in unit cube). -/
theorem unitCube3_isAddFundamentalDomain :
    MeasureTheory.IsAddFundamentalDomain intLattice3 unitCube3 MeasureTheory.volume := by
  sorry -- Standard fundamental domain argument for integer lattice

/-- The Haar measure of the unit cube is 1. -/
theorem unitCube3_volume : MeasureTheory.volume unitCube3 = 1 := by
  sorry -- Would use volume_pi and volume_Ico

/-- Ellipsoid for Dirichlet's Key Lemma: {(x,y,z) | x² + dy² + dz² ≤ R}. -/
def dirichletEllipsoid (d : ℕ) (R : ℝ) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {v | v 0 ^ 2 + d * (v 1) ^ 2 + d * (v 2) ^ 2 ≤ R}

/-- The Dirichlet ellipsoid is convex.
This follows from the fact that sublevel sets of convex functions are convex,
and f(v) = v₀² + d*v₁² + d*v₂² is a convex function (positive semidefinite quadratic). -/
theorem dirichletEllipsoid_convex (d : ℕ) (R : ℝ) (_hd : 0 < d) (_hR : 0 ≤ R) :
    Convex ℝ (dirichletEllipsoid d R) := by
  intro x hx y hy a b ha hb hab
  simp only [dirichletEllipsoid, Set.mem_setOf_eq] at hx hy ⊢
  -- Key lemma: for t ∈ [0,1], (tx + (1-t)y)² ≤ t·x² + (1-t)·y² (convexity of square)
  have sq_convex : ∀ u v : ℝ, (a * u + b * v) ^ 2 ≤ a * u ^ 2 + b * v ^ 2 := by
    intro u v
    -- Algebraic identity: a*u² + b*v² - (a*u + b*v)² = a*b*(u-v)² when a+b=1
    have key : a * u^2 + b * v^2 - (a * u + b * v)^2 = a * b * (u - v)^2 := by
      have h1 : b = 1 - a := by linarith
      have h2 : a = 1 - b := by linarith
      rw [h1, h2]
      ring
    -- Since ab(u-v)² ≥ 0, we have a*u² + b*v² ≥ (au+bv)²
    have h_nonneg : 0 ≤ a * b * (u - v)^2 := by
      apply mul_nonneg
      apply mul_nonneg ha hb
      exact sq_nonneg _
    linarith
  -- Apply to each coordinate
  have h0 := sq_convex (x 0) (y 0)
  have h1 := sq_convex (x 1) (y 1)
  have h2 := sq_convex (x 2) (y 2)
  have hd' : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  -- Calculate using PiLp structure
  have heq : (a • x + b • y) 0 ^ 2 + ↑d * (a • x + b • y) 1 ^ 2 + ↑d * (a • x + b • y) 2 ^ 2
           = (a * x 0 + b * y 0) ^ 2 + d * (a * x 1 + b * y 1) ^ 2 + d * (a * x 2 + b * y 2) ^ 2 := by
    congr 1 <;> congr 1 <;> simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rw [heq]
  calc (a * x 0 + b * y 0) ^ 2 + d * (a * x 1 + b * y 1) ^ 2 + d * (a * x 2 + b * y 2) ^ 2
      ≤ (a * (x 0)^2 + b * (y 0)^2) + d * (a * (x 1)^2 + b * (y 1)^2) + d * (a * (x 2)^2 + b * (y 2)^2) := by
        gcongr
      _ = a * (x 0^2 + d * (x 1)^2 + d * (x 2)^2) + b * (y 0^2 + d * (y 1)^2 + d * (y 2)^2) := by ring
      _ ≤ a * R + b * R := by gcongr
      _ = R := by rw [← add_mul, hab, one_mul]

/-- The Dirichlet ellipsoid is symmetric. -/
theorem dirichletEllipsoid_symmetric (d : ℕ) (R : ℝ) :
    ∀ x ∈ dirichletEllipsoid d R, -x ∈ dirichletEllipsoid d R := by
  intro x hx
  unfold dirichletEllipsoid at hx ⊢
  simp only [Set.mem_setOf_eq] at hx ⊢
  -- (-x) i = -(x i), and (-(x i))² = (x i)², so the inequality is preserved
  have h0 : (-x) 0 ^ 2 = x 0 ^ 2 := neg_sq (x 0)
  have h1 : (-x) 1 ^ 2 = x 1 ^ 2 := neg_sq (x 1)
  have h2 : (-x) 2 ^ 2 = x 2 ^ 2 := neg_sq (x 2)
  simp only [h0, h1, h2]
  exact hx

/-- Volume of the Dirichlet ellipsoid: (4π/3) · R^(3/2) / √d.

For the standard ellipsoid x²/a² + y²/b² + z²/c² ≤ 1, the volume is (4π/3)abc.
Our ellipsoid x² + dy² + dz² ≤ R has a = √R, b = c = √(R/d).
So volume = (4π/3) · √R · √(R/d) · √(R/d) = (4π/3) · R^(3/2) / √d. -/
theorem dirichletEllipsoid_volume (d : ℕ) (R : ℝ) (hd : 0 < d) (hR : 0 < R) :
    MeasureTheory.volume (dirichletEllipsoid d R) = ENNReal.ofReal ((4 * Real.pi / 3) * R ^ (3/2 : ℝ) / Real.sqrt d) := by
  sorry -- Would require integration / ellipsoid volume formula

/-- **Sufficiency Axiom**: Numbers NOT of excluded form ARE sums of three squares.

**Current status**: All PRIMES are proved. Composites need Dirichlet's Key Lemma above.

To complete this proof, implement:
1. Case analysis on n mod 8 to choose appropriate d
2. Use Dirichlet's theorem (PrimesInAP, now available) to find suitable primes
3. Apply `dirichlet_key_lemma` for each case
4. Handle small cases (n ≤ 6) directly

**Estimated remaining work**: ~150-200 lines using the Key Lemma framework above. -/
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

/-! ### Primes ≡ 3 (mod 8) - The hardest case for sufficiency -/

/-- 3 ≡ 3 (mod 8): 3 = 1² + 1² + 1² -/
example : ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = 3 := ⟨1, 1, 1, rfl⟩

/-- 11 ≡ 3 (mod 8): 11 = 1² + 1² + 3² -/
example : ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = 11 := ⟨1, 1, 3, rfl⟩

/-- 19 ≡ 3 (mod 8): 19 = 1² + 3² + 3² -/
example : ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = 19 := ⟨1, 3, 3, rfl⟩

/-- 43 ≡ 3 (mod 8): 43 = 3² + 3² + 5² -/
example : ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = 43 := ⟨3, 3, 5, rfl⟩

/-- 59 ≡ 3 (mod 8): 59 = 1² + 3² + 7² -/
example : ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = 59 := ⟨1, 3, 7, rfl⟩

/-- 67 ≡ 3 (mod 8): 67 = 3² + 3² + 7² -/
example : ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = 67 := ⟨3, 3, 7, rfl⟩

/-- 83 ≡ 3 (mod 8): 83 = 1² + 1² + 9² -/
example : ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = 83 := ⟨1, 1, 9, rfl⟩

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
