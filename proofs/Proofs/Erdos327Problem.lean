/-
# Erdős Problem 327: Sum-Divides-Product Avoidance

Let `A ⊆ {1, ..., N}` have the property that for all distinct `a, b ∈ A`,
`a + b ∤ a * b`. Note that `a + b ∣ a * b` iff `1/a + 1/b` is a unit fraction.

Can `A` be substantially larger than the set of odd numbers in `{1, ..., N}`?

Van Doorn showed: if `|A| ≥ (25/28 + o(1)) * N`, then `A` must contain
`a ≠ b` with `a + b ∣ a * b`.

A variant asks: if `a + b ∤ 2 * a * b` for all distinct `a, b ∈ A`, must `|A| = o(N)`?

*Reference:* [erdosproblems.com/327](https://www.erdosproblems.com/327)
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

open Finset
open scoped Classical

/- ## Sum-divides-product property -/

/-- `SumNotDvdProd A` means for all distinct `a, b ∈ A`, `a + b ∤ a * b`. -/
def SumNotDvdProd (A : Finset ℕ) : Prop :=
    ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬(a + b ∣ a * b)

/-- `SumNotDvdTwoProd A` means for all distinct `a, b ∈ A`, `a + b ∤ 2 * a * b`. -/
def SumNotDvdTwoProd (A : Finset ℕ) : Prop :=
    ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬(a + b ∣ 2 * a * b)

/-- The maximum size of a subset of `{1, ..., N}` with `SumNotDvdProd`. -/
noncomputable def maxAvoidSize (N : ℕ) : ℕ :=
    ((Finset.Icc 1 N).powerset.filter SumNotDvdProd).sup Finset.card

/- ## Main conjecture -/

/-- Erdős Problem 327: The maximum size of a SumNotDvdProd subset of `{1,...,N}`
is asymptotically at most `N/2 + o(N)` (no larger than the odd numbers). -/
def ErdosProblem327 : Prop :=
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (maxAvoidSize N : ℝ) ≤ (1 / 2 + ε) * N

/- ## Van Doorn's bound -/

/-- Van Doorn's result: if `|A| ≥ (25/28) * N`, then `A` contains `a ≠ b`
with `a + b ∣ a * b`. -/
axiom vanDoorn_bound (N : ℕ) (A : Finset ℕ) :
    A ⊆ Finset.Icc 1 N → (25 * N ≤ 28 * A.card) →
      ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ a + b ∣ a * b

/- ## Variant: factor-of-2 condition -/

/-- Variant conjecture: if `a + b ∤ 2ab` for distinct `a, b ∈ A ⊆ {1,...,N}`,
then `|A| = o(N)`. -/
def ErdosProblem327_variant : Prop :=
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N → SumNotDvdTwoProd A →
        (A.card : ℝ) ≤ ε * N

/- ## Unit fraction equivalence -/

/-- `a + b ∣ a * b` iff `1/a + 1/b` is a unit fraction (i.e., `1/c` for some `c`).
    Proof: 1/a + 1/b = (a+b)/(ab), which equals 1/c iff c = ab/(a+b), iff (a+b) | ab. -/
theorem sumDvdProd_iff_unitFraction (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    a + b ∣ a * b ↔ ∃ c : ℕ, 0 < c ∧ (1 : ℚ) / a + (1 : ℚ) / b = (1 : ℚ) / c := by
  have ha' : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hb' : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hab : (a : ℚ) * b ≠ 0 := mul_ne_zero ha' hb'
  have hab_pos : 0 < (a : ℚ) * b := by positivity
  constructor
  · -- (→) If (a+b) | ab, then c = ab/(a+b) is a positive natural number
    intro ⟨c, hc⟩
    have hc_pos : 0 < c := by
      by_contra h; push_neg at h
      have hc0 : c = 0 := by omega
      rw [hc0, mul_zero] at hc
      have := Nat.mul_pos ha hb
      omega
    refine ⟨c, hc_pos, ?_⟩
    -- 1/a + 1/b = (a+b)/(ab) = (a+b)/((a+b)*c) = 1/c
    have hc_ne : (c : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [div_add_div _ _ ha' hb', div_eq_div_iff (mul_ne_zero ha' hb') hc_ne]
    have hc_q : (↑a : ℚ) * ↑b = (↑a + ↑b) * ↑c := by exact_mod_cast hc
    linarith
  · -- (←) If 1/a + 1/b = 1/c, then (a+b) | ab
    intro ⟨c, hc_pos, heq⟩
    have hc' : (c : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hab' : (↑a + ↑b : ℚ) ≠ 0 := by positivity
    -- From 1/a + 1/b = 1/c: (a+b)/(ab) = 1/c, so c*(a+b) = ab
    have key : (↑c : ℚ) * (↑a + ↑b) = ↑a * ↑b := by
      have := heq; field_simp at this; linarith
    -- Extract the ℕ identity
    have key_nat : c * (a + b) = a * b := by exact_mod_cast key
    exact ⟨c, by linarith [key_nat]⟩

/- ## Basic properties -/

/-- The empty set trivially satisfies SumNotDvdProd. -/
theorem sumNotDvdProd_empty : SumNotDvdProd ∅ := by
  intro a ha; exact absurd ha (Finset.notMem_empty a)

/-- A singleton trivially satisfies SumNotDvdProd. -/
theorem sumNotDvdProd_singleton (n : ℕ) : SumNotDvdProd {n} := by
  intro a ha b hb hab
  rw [Finset.mem_singleton] at ha hb
  exact absurd (ha.trans hb.symm) hab

/-- If `B ⊆ A` and `A` has SumNotDvdProd, then so does `B`. -/
theorem sumNotDvdProd_subset {A B : Finset ℕ} (h : B ⊆ A) (hA : SumNotDvdProd A) :
    SumNotDvdProd B := fun a ha b hb => hA a (h ha) b (h hb)

/- ## Structural results -/

/-- The odd numbers in `{1,...,N}` satisfy SumNotDvdProd.
For odd `a, b`: their product `a*b` is odd (has odd remainder mod 2),
while their sum `a+b` is even (divisible by 2). An even number cannot
divide an odd number, so `a+b ∤ a*b`. -/
theorem oddNumbers_sumNotDvdProd (N : ℕ) :
    SumNotDvdProd ((Finset.Icc 1 N).filter (fun n => n % 2 = 1)) := by
  intro a ha b hb _hab hdvd
  simp only [Finset.mem_filter, Finset.mem_Icc] at ha hb
  -- Product of odd numbers is odd: (a*b) % 2 = 1
  have h_prod_odd : (a * b) % 2 = 1 := by
    have h := Nat.mul_mod a b 2
    rw [ha.2, hb.2] at h
    simpa using h
  -- Sum of odd numbers is even: 2 ∣ (a + b)
  have h_sum_even : 2 ∣ (a + b) := by omega
  -- By transitivity, 2 ∣ (a * b)
  obtain ⟨k, hk⟩ := dvd_trans h_sum_even hdvd
  -- But (2 * k) % 2 = 0, contradicting h_prod_odd
  rw [hk] at h_prod_odd
  omega

/-- If `a` and `b` are coprime positive naturals, then `a + b ∤ a * b`.
Proof: `gcd(a+b, a) = gcd(a, b) = 1`, so by Euclid's lemma
`(a+b) ∣ (a*b)` would force `(a+b) ∣ b`, but `a+b > b` for `a > 0`. -/
theorem coprime_sumNotDvdProd {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hcop : Nat.Coprime a b) : ¬(a + b ∣ a * b) := by
  intro hdvd
  -- gcd(a, a+b) = gcd(a, b) = 1, so Coprime a (a+b)
  have h_cop_a : Nat.Coprime a (a + b) := by
    rwa [Nat.coprime_self_add_right]
  -- Equivalently, Coprime (a+b) a
  have h_cop : Nat.Coprime (a + b) a := h_cop_a.symm
  -- By Euclid's lemma: (a+b) | (a * b) and Coprime (a+b) a → (a+b) | b
  have h_dvd_b : (a + b) ∣ b := h_cop.dvd_of_dvd_mul_left hdvd
  -- But a + b > b since a > 0, contradicting (a+b) | b for b > 0
  exact absurd (Nat.le_of_dvd hb h_dvd_b) (by omega)

/-- Any set of pairwise coprime positive naturals satisfies SumNotDvdProd. -/
theorem sumNotDvdProd_of_pairwise_coprime {A : Finset ℕ} (hA : ∀ a ∈ A, 0 < a)
    (hcop : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → Nat.Coprime a b) : SumNotDvdProd A := by
  intro a ha b hb hab hdvd
  exact coprime_sumNotDvdProd (hA a ha) (hA b hb) (hcop a ha b hb hab) hdvd

/- ## GCD characterization -/

/-- Characterization: `a + b ∣ a * b` iff `(a/d + b/d) ∣ d` where `d = gcd(a,b)`.
Writing `a = d*a', b = d*b'` with `gcd(a',b') = 1`:
  `a + b = d(a'+b')` and `a*b = d²*a'*b'`.
So `d(a'+b') ∣ d²*a'*b'` iff `(a'+b') ∣ d*a'*b'`.
Since `gcd(a'*b', a'+b') = 1` (from `gcd(a',b')=1`), this reduces to `(a'+b') ∣ d`.

Consequences:
- Coprime pairs (d=1): need `(a+b) ∣ 1`, impossible for `a+b ≥ 2`.
- Odd pairs: `d` is odd, `a'+b'` is even (both odd/d are odd), even ∤ odd. -/
theorem sumDvdProd_iff_reduced_divides_gcd {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    a + b ∣ a * b ↔ (a / Nat.gcd a b + b / Nat.gcd a b) ∣ Nat.gcd a b := by
  set d := Nat.gcd a b with hd_def
  set a' := a / d with ha'_def
  set b' := b / d with hb'_def
  have hd_pos : 0 < d := Nat.pos_of_ne_zero (by
    intro h; rw [Nat.gcd_eq_zero_iff.mp h |>.1] at ha; exact Nat.lt_irrefl 0 ha)
  have hda : d ∣ a := Nat.gcd_dvd_left a b
  have hdb : d ∣ b := Nat.gcd_dvd_right a b
  have ha_eq : a = d * a' := (Nat.mul_div_cancel' hda).symm
  have hb_eq : b = d * b' := (Nat.mul_div_cancel' hdb).symm
  have hcop : Nat.Coprime a' b' := Nat.coprime_div_gcd_div_gcd hd_pos
  -- (a'+b') is coprime to a'*b' since gcd(a',b')=1
  have hcop1 : Nat.Coprime (a' + b') a' :=
    (Nat.coprime_self_add_right.mpr hcop).symm
  have hcop2 : Nat.Coprime (a' + b') b' := by
    rw [show a' + b' = b' + a' from add_comm a' b']
    exact (Nat.coprime_self_add_right.mpr hcop.symm).symm
  have hcop_prod : Nat.Coprime (a' + b') (a' * b') := hcop1.mul_right hcop2
  -- Reduce: a+b = d*(a'+b'), a*b = d*(d*a'*b'), cancel d
  have sum_eq : a + b = d * (a' + b') := by rw [ha_eq, hb_eq]; ring
  have prod_eq : a * b = d * (d * (a' * b')) := by rw [ha_eq, hb_eq]; ring
  rw [sum_eq, prod_eq, mul_dvd_mul_iff_left (by omega : d ≠ 0)]
  -- (a'+b') | d*(a'*b') ↔ (a'+b') | d, by coprimality
  exact ⟨hcop_prod.dvd_of_dvd_mul_right, fun h => dvd_mul_of_dvd_left h _⟩
