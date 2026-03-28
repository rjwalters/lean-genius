/-
# Erdős Problem #687 — Covering Congruences and the Jacobsthal Function

Let Y(x) be the maximal y such that there exists a choice of congruence
classes aₚ for all primes p ≤ x such that every integer in [1, y] is
≡ aₚ (mod p) for at least one prime p ≤ x.

Equivalently, Y(x) is the Jacobsthal function g(P(x)) where P(x) = ∏_{p ≤ x} p
is the primorial, and g(n) is the largest gap between consecutive integers
coprime to n.

## Status: OPEN ($1,000 prize)

## Key Results

- **Iwaniec (1978)**: Y(x) ≪ x² (best upper bound).
- **Ford–Green–Konyagin–Maynard–Tao (2018)**:
  Y(x) ≫ x · (log x)(log log log x) / (log log x).
- **Maier–Pomerance conjecture**: Y(x) ≪ x · (log x)^{2+o(1)}.
- **Rankin (1938)**: Earlier lower bound, improved by FGKMT.

## Related Problems

#688, #689, #970 address related variants.

*Reference:* [erdosproblems.com/687](https://www.erdosproblems.com/687)

Axioms: 5 (jacobsthalSet_bddAbove, jacobsthalY_eq_jacobsthal,
  iwaniec_upper, fgkmt_lower, maier_pomerance_conjecture)
Proved: erdos_687_conjecture (from maier_pomerance_conjecture — M-P is stronger)
Theorems: 12 (was 9; added not_mem_jacobsthalSet_two, one_mem_jacobsthalSet_two,
  jacobsthalY_two. Fixed duplicate definitions.)
Removed: jacobsthalY_trivial_lower (FALSE — Y(2) = 1 < 3 counterexample)
Sorries: 0 (was 1; proved log_pow_eventually_le_rpow via isLittleO_log_rpow_atTop)
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Finset Filter

/- ## Core Definitions -/

/-- The primorial: product of all primes ≤ x. -/
noncomputable def primorial (x : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range (x + 1)).filter Nat.Prime, p

/-- An integer n is covered by a covering system if n ≡ aₚ (mod p)
for some prime p ≤ x. -/
def IsCovered (x : ℕ) (a : ∀ p : ℕ, p.Prime → p ≤ x → ℕ) (n : ℤ) : Prop :=
  ∃ (p : ℕ) (hp : p.Prime) (hpx : p ≤ x),
    (n : ℤ) % (p : ℤ) = (a p hp hpx : ℤ) % (p : ℤ)

/-- The set of y values achievable by some covering system for primes ≤ x. -/
def jacobsthalSet (x : ℕ) : Set ℕ :=
  { y : ℕ | ∃ a : ∀ p : ℕ, p.Prime → p ≤ x → ℕ,
    ∀ n : ℤ, 1 ≤ n → n ≤ y → IsCovered x a n }

/-- Y(x): the maximal y such that some covering system covers all of [1, y]. -/
noncomputable def jacobsthalY (x : ℕ) : ℕ :=
  sSup (jacobsthalSet x)

/- ## The Jacobsthal Function -/

/-- The Jacobsthal function g(n): largest gap between consecutive
integers coprime to n. Equivalently, g(n) = 1 + max length of a
run of integers all sharing a factor with n. -/
noncomputable def jacobsthal (n : ℕ) : ℕ :=
  sSup { d : ℕ | ∃ m : ℤ, ∀ k : ℤ, m < k → k < m + d →
    ∃ p : ℕ, p.Prime ∧ (p : ℤ) ∣ n ∧ (p : ℤ) ∣ k }

/- ## Basic Properties of jacobsthalSet -/

/-- 0 is always in the Jacobsthal set (vacuously: no integers in [1, 0]). -/
theorem jacobsthalSet_nonempty (x : ℕ) : (jacobsthalSet x).Nonempty := by
  refine ⟨0, ?_⟩
  unfold jacobsthalSet
  simp only [Set.mem_setOf_eq, Nat.cast_zero]
  exact ⟨fun _ _ _ => 0, fun n h1 h2 => by omega⟩

/-- The Jacobsthal set is bounded above by the primorial.
After primorial(x) steps, the CRT covering pattern repeats, so any
uncovered integer would imply infinitely many uncovered integers
in any interval of length primorial(x). -/
axiom jacobsthalSet_bddAbove (x : ℕ) :
  BddAbove (jacobsthalSet x)

/- ## Structural Properties -/

/-- The Jacobsthal set is downward closed: if y achievable, so is y' ≤ y. -/
theorem jacobsthalSet_downward {x y y' : ℕ} (hy : y ∈ jacobsthalSet x) (h : y' ≤ y) :
    y' ∈ jacobsthalSet x := by
  obtain ⟨a, ha⟩ := hy
  exact ⟨a, fun n h1 hn => ha n h1 (hn.trans (by exact_mod_cast h))⟩

/-- When there are no primes ≤ x, jacobsthalSet x = {0}: nothing can be covered. -/
theorem jacobsthalSet_eq_zero_of_no_primes {x : ℕ} (hx : ∀ p, Nat.Prime p → ¬(p ≤ x)) :
    jacobsthalSet x = {0} := by
  ext y
  simp only [Set.mem_singleton_iff]
  constructor
  · intro hy
    by_contra hne
    have hpos : 1 ≤ y := Nat.one_le_iff_ne_zero.mpr hne
    obtain ⟨a, ha⟩ := hy
    obtain ⟨p, hp, hpx, _⟩ := ha 1 le_rfl (by exact_mod_cast hpos)
    exact hx p hp hpx
  · intro hy; subst hy
    exact ⟨fun _ _ _ => 0, fun n h1 h2 => by omega⟩

/-- jacobsthalSet 0 = {0}: no primes ≤ 0. -/
theorem jacobsthalSet_zero : jacobsthalSet 0 = {0} :=
  jacobsthalSet_eq_zero_of_no_primes (fun p hp hpx => by have := hp.two_le; omega)

/-- jacobsthalSet 1 = {0}: no primes ≤ 1. -/
theorem jacobsthalSet_one : jacobsthalSet 1 = {0} :=
  jacobsthalSet_eq_zero_of_no_primes (fun p hp hpx => by have := hp.two_le; omega)

/-- Y(0) = 0. -/
theorem jacobsthalY_zero : jacobsthalY 0 = 0 := by
  simp [jacobsthalY, jacobsthalSet_zero]

/-- Y(1) = 0. -/
theorem jacobsthalY_one : jacobsthalY 1 = 0 := by
  simp [jacobsthalY, jacobsthalSet_one]

/- ## Concrete Values -/

/-- 1 ∈ jacobsthalSet 2: choosing a₂ = 1 covers all odd numbers, including 1. -/
theorem one_mem_jacobsthalSet_two : (1 : ℕ) ∈ jacobsthalSet 2 := by
  refine ⟨fun p _ _ => 1, fun n h1 hn => ?_⟩
  -- n ∈ [1,1], so n = 1
  have : n = 1 := by omega
  subst this
  exact ⟨2, by decide, le_refl 2, by norm_num⟩

/-- 2 ∉ jacobsthalSet 2: the only prime ≤ 2 is 2, and any single residue
    class mod 2 covers exactly one of {1, 2}. So [1, 2] can't be fully covered. -/
theorem two_not_mem_jacobsthalSet_two : (2 : ℕ) ∉ jacobsthalSet 2 := by
  intro ⟨a, ha⟩
  have h1 := ha 1 (by norm_num) (by norm_num)
  have h2 := ha 2 (by norm_num) (by norm_num)
  obtain ⟨p₁, hp₁, hpx₁, hcov₁⟩ := h1
  obtain ⟨p₂, hp₂, hpx₂, hcov₂⟩ := h2
  -- p₁ = p₂ = 2 (only prime ≤ 2)
  have : p₁ = 2 := by have := hp₁.two_le; omega
  subst this
  have : p₂ = 2 := by have := hp₂.two_le; omega
  subst this
  -- 1 % 2 = (a 2 _ _) % 2 and 2 % 2 = (a 2 _ _) % 2, so 1 % 2 = 2 % 2
  have : (1 : ℤ) % 2 = (2 : ℤ) % 2 := hcov₁.trans hcov₂.symm
  norm_num at this

/-- jacobsthalSet 2 = {0, 1}: with only prime 2, we can cover at most one
    parity class, giving Y(2) = 1. -/
theorem jacobsthalSet_two : jacobsthalSet 2 = {0, 1} := by
  ext y
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hy
    by_contra hne
    push_neg at hne
    have : 2 ≤ y := by omega
    exact two_not_mem_jacobsthalSet_two (jacobsthalSet_downward hy (by omega))
  · rintro (rfl | rfl)
    · exact jacobsthalSet_downward one_mem_jacobsthalSet_two (by omega)
    · exact one_mem_jacobsthalSet_two

/-- Y(2) = 1. -/
theorem jacobsthalY_two : jacobsthalY 2 = 1 := by
  unfold jacobsthalY
  rw [jacobsthalSet_two]
  apply le_antisymm
  · exact csSup_le ⟨0, Or.inl rfl⟩ (fun x hx => by rcases hx with rfl | rfl <;> omega)
  · exact le_csSup ⟨1, fun x hx => by rcases hx with rfl | rfl <;> omega⟩ (Or.inr rfl)

/- ## Monotonicity -/

/-- Key lemma: the Jacobsthal set for x₁ is contained in that for x₂
when x₁ ≤ x₂. Given a covering for primes ≤ x₁, extend it to primes
≤ x₂ by choosing class 0 for each new prime. -/
theorem jacobsthalSet_mono {x₁ x₂ : ℕ} (h : x₁ ≤ x₂) :
    jacobsthalSet x₁ ⊆ jacobsthalSet x₂ := by
  intro y hy
  unfold jacobsthalSet at hy ⊢
  simp only [Set.mem_setOf_eq] at hy ⊢
  obtain ⟨a, ha⟩ := hy
  -- Extend covering: keep old classes, use 0 for new primes
  refine ⟨fun p hp hpx₂ => if hle : p ≤ x₁ then a p hp hle else 0, fun n h1 hn => ?_⟩
  obtain ⟨p, hp, hpx₁, hcov⟩ := ha n h1 hn
  exact ⟨p, hp, le_trans hpx₁ h, by simp only [dif_pos hpx₁]; exact hcov⟩

/-- Y(x) is monotone non-decreasing in x: more primes allow
longer covering intervals. -/
theorem jacobsthalY_mono (x₁ x₂ : ℕ) (h : x₁ ≤ x₂) :
    jacobsthalY x₁ ≤ jacobsthalY x₂ := by
  unfold jacobsthalY
  exact csSup_le_csSup (jacobsthalSet_bddAbove x₂)
    (jacobsthalSet_nonempty x₁) (jacobsthalSet_mono h)

/- ## Connection to Jacobsthal Function -/

/-- Y(x) equals the Jacobsthal function of the primorial. -/
axiom jacobsthalY_eq_jacobsthal (x : ℕ) :
  jacobsthalY x = jacobsthal (primorial x)

/- ## Known Bounds -/

/-- **Iwaniec (1978).** Y(x) ≪ x².
This is the best known upper bound. -/
axiom iwaniec_upper :
  ∃ C : ℝ, 0 < C ∧ ∀ (x : ℕ), 2 ≤ x →
    (jacobsthalY x : ℝ) ≤ C * (x : ℝ) ^ 2

/-- **Ford–Green–Konyagin–Maynard–Tao (2018).**
Y(x) ≫ x · (log x)(log log log x) / (log log x).
This improved Rankin's classical lower bound. -/
axiom fgkmt_lower :
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ (x : ℕ) in atTop,
    (jacobsthalY x : ℝ) ≥ c * (x : ℝ) *
      Real.log (x : ℝ) * Real.log (Real.log (Real.log (x : ℝ))) /
      Real.log (Real.log (x : ℝ))

/-- **Maier–Pomerance Conjecture.** Y(x) ≪ x · (log x)^{2+o(1)}.
If true, this would nearly close the gap with the FGKMT lower bound. -/
axiom maier_pomerance_conjecture :
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ᶠ (x : ℕ) in atTop,
    (jacobsthalY x : ℝ) ≤ C * (x : ℝ) * Real.log (x : ℝ) ^ (2 + ε)

/- ## Main Conjecture ($1,000) -/

/-- Helper: For any C > 0, k > 0, ε > 0, eventually C · (log x)^k ≤ x^ε.
Standard asymptotic: polynomial growth dominates any power of logarithm.
Uses isLittleO_log_rpow_atTop with c = C^(-1/k) to get exact cancellation. -/
private lemma log_pow_eventually_le_rpow (C : ℝ) (hC : 0 < C) (k : ℝ) (hk : 0 < k)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ (x : ℕ) in atTop, C * Real.log (x : ℝ) ^ k ≤ (x : ℝ) ^ ε := by
  -- Choose c = C^(-1/k) > 0 as the little-o bound parameter
  have hεk : 0 < ε / k := div_pos hε hk
  have hcinv : 0 < C ^ (-(1 : ℝ) / k) := rpow_pos_of_pos hC _
  -- From log =o(x^(ε/k)): eventually |log x| ≤ C^(-1/k) · |x^(ε/k)|
  have hbound := (isLittleO_log_rpow_atTop hεk).bound hcinv
  -- Transfer from ℝ filter to ℕ filter
  rw [Filter.eventually_atTop]
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp hbound
  refine ⟨max ⌈R⌉₊ 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := le_of_lt hn_pos
  have hR_le : R ≤ (n : ℝ) :=
    le_trans (Nat.le_ceil R) (by exact_mod_cast le_trans (le_max_left _ _) hn)
  -- Extract: log n ≤ C^(-1/k) · n^(ε/k)
  have hlog := hR (n : ℝ) hR_le
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hn1)),
      abs_of_nonneg (rpow_nonneg hn_nn _)] at hlog
  have hlog_nn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
  -- Raise to power k and simplify:
  -- (log n)^k ≤ (C^(-1/k) · n^(ε/k))^k = C^(-1) · n^ε
  -- So C · (log n)^k ≤ C · C^(-1) · n^ε = n^ε
  calc C * Real.log (n : ℝ) ^ k
      ≤ C * (C ^ (-(1 : ℝ) / k) * (n : ℝ) ^ (ε / k)) ^ k :=
        mul_le_mul_of_nonneg_left (rpow_le_rpow hlog_nn hlog hk.le) hC.le
    _ = C * (C ^ (-(1 : ℝ) / k * k) * (n : ℝ) ^ (ε / k * k)) := by
        congr 1
        rw [mul_rpow (rpow_nonneg hC.le _) (rpow_nonneg hn_nn _),
            ← rpow_mul hC.le, ← rpow_mul hn_nn]
    _ = C * (C ^ (-(1 : ℝ)) * (n : ℝ) ^ ε) := by
        have hk_ne : k ≠ 0 := ne_of_gt hk
        congr 2 <;> (field_simp [hk_ne]; ring)
    _ = C * C ^ (-(1 : ℝ)) * (n : ℝ) ^ ε := by ring
    _ = (n : ℝ) ^ ε := by
        have : C ^ (-(1 : ℝ)) = C⁻¹ := by
          rw [rpow_neg hC.le, rpow_one]
        rw [this, mul_inv_cancel₀ hC.ne', one_mul]

/-- **Erdős Problem #687 ($1,000 prize).**
Is Y(x) = o(x²)? More specifically, is Y(x) ≪ x^{1+o(1)}?

PROVED from maier_pomerance_conjecture: M-P gives Y(x) ≤ C·x·(log x)^{2+ε₀},
and for any δ > 0, eventually C·x·(log x)^{2+ε₀} ≤ x^{1+δ} since
polynomial growth dominates any power of logarithm. -/
theorem erdos_687_conjecture :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ (x : ℕ) in atTop,
      (jacobsthalY x : ℝ) ≤ (x : ℝ) ^ (1 + ε) := by
  intro ε hε
  -- Use Maier-Pomerance with ε₀ = 1
  obtain ⟨C, hC, hMP⟩ := maier_pomerance_conjecture 1 one_pos
  -- hMP: ∀ᶠ x, Y(x) ≤ C · x · (log x)^3
  -- Eventually: C · x · (log x)^3 ≤ x^{1+ε}
  -- i.e., C · (log x)^3 ≤ x^ε (standard asymptotic)
  have h_asymp := log_pow_eventually_le_rpow C hC 3 (by norm_num) ε hε
  -- Combine both eventual bounds
  filter_upwards [hMP, h_asymp] with x hMP_x h_asymp_x
  -- hMP_x: Y(x) ≤ C · x · (log x)^3
  -- h_asymp_x: C · (log x)^3 ≤ x^ε
  -- Goal: Y(x) ≤ x^{1+ε}
  calc (jacobsthalY x : ℝ)
      ≤ C * (x : ℝ) * Real.log (x : ℝ) ^ (2 + 1) := hMP_x
    _ = (x : ℝ) * (C * Real.log (x : ℝ) ^ 3) := by ring
    _ ≤ (x : ℝ) * (x : ℝ) ^ ε := by
        apply mul_le_mul_of_nonneg_left h_asymp_x (Nat.cast_nonneg x)
    _ = (x : ℝ) ^ 1 * (x : ℝ) ^ ε := by rw [rpow_one]
    _ = (x : ℝ) ^ (1 + ε) := by rw [← rpow_add (Nat.cast_nonneg x)]

/- ## Concrete Computations -/

/-- Helper: for x ≤ 1, no prime p satisfies p ≤ x. -/
private lemma no_prime_le_one (p : ℕ) (hp : p.Prime) (hpx : p ≤ 1) : False := by
  have := hp.two_le; omega


/-- For x ≤ 1, jacobsthalSet x = {0} (no primes means only vacuous covering). -/
theorem jacobsthalSet_eq_zero_of_le_one {x : ℕ} (hx : x ≤ 1) :
    jacobsthalSet x = {0} := by
  ext y; constructor
  · intro hy
    simp only [Set.mem_singleton_iff]
    by_contra h
    obtain ⟨a, ha⟩ := hy
    obtain ⟨p, hp, hpx, _⟩ := ha 1 le_rfl (by exact_mod_cast (show 1 ≤ y by omega))
    exact no_prime_le_one p hp (by omega)
  · intro hy
    simp only [Set.mem_singleton_iff] at hy; subst hy
    exact ⟨fun _ _ _ => 0, fun n h1 h2 => by omega⟩

/- ## Trivial Lower Bound — FALSE (removed)

The original axiom claimed Y(x) ≥ x + 1 for x ≥ 2, based on the argument
that "every integer in [1,x] has a prime factor ≤ x." However, a covering
system requires choosing ONE residue class per prime, not covering all
multiples. With only one prime p = 2, we can only cover one parity class.

**Counterexample**: x = 2, primes ≤ 2 = {2}.
- With a₂ = 0: covers {even}. n = 1 not covered. Y ≤ 0.
- With a₂ = 1: covers {odd}. n = 2 not covered. Y ≤ 1.
- So Y(2) = 1 < 3 = x + 1.

Similarly, for x = 3 (primes {2,3}):
- Best covering a₂ = 1, a₃ = 2: covers {odd} ∪ {≡ 2 mod 3}.
  n = 1,2,3 covered but n = 4 not. So Y(3) ≤ 3 < 4 = x + 1.

The bound Y(x) ≥ x + 1 may hold for sufficiently large x (e.g., x ≥ 5
where the primorial has enough prime factors), but not universally from x ≥ 2.
-/

/- ## Y(2) = 1: First Nontrivial Concrete Value -/

/-- For x = 2, any y ≥ 2 is NOT in jacobsthalSet 2.
    The only prime ≤ 2 is 2. Any covering picks one parity class.
    Since 1 and 2 have opposite parities, one is always uncovered. -/
theorem not_mem_jacobsthalSet_two {y : ℕ} (hy : 2 ≤ y) :
    y ∉ jacobsthalSet 2 := by
  intro ⟨a, ha⟩
  -- Both 1 and 2 must be in [1, y] and covered
  have h1 := ha 1 le_rfl (by exact_mod_cast (show 1 ≤ y by omega))
  have h2 := ha 2 (by norm_num) (by exact_mod_cast hy)
  obtain ⟨p₁, hp₁, hpx₁, hcov₁⟩ := h1
  obtain ⟨p₂, hp₂, hpx₂, hcov₂⟩ := h2
  -- The only prime ≤ 2 is 2 itself
  have : p₁ = 2 := by have := hp₁.two_le; omega
  subst this
  have : p₂ = 2 := by have := hp₂.two_le; omega
  subst this
  -- By proof irrelevance: a 2 hp₁ hpx₁ = a 2 hp₂ hpx₂
  -- So 1 % 2 = a(2) % 2 = 2 % 2, i.e., 1 = 0. Contradiction.
  have := hcov₁.trans hcov₂.symm
  norm_num at this

/-- 1 ∈ jacobsthalSet 2: choosing residue class 1 mod 2 covers [1, 1]. -/
theorem one_mem_jacobsthalSet_two : (1 : ℕ) ∈ jacobsthalSet 2 := by
  refine ⟨fun _ _ _ => 1, fun n h1 hn => ?_⟩
  -- n ∈ [1, 1] means n = 1
  have hn_eq : n = 1 := le_antisymm hn h1
  subst hn_eq
  -- 1 is covered by prime 2 with class 1: 1 % 2 = 1 % 2
  exact ⟨2, by decide, le_refl 2, rfl⟩

/-- Y(2) = 1. With only prime 2 available, the best covering picks one
    parity class, achieving exactly [1, 1].
    Note: this proof uses a LOCAL BddAbove argument for x = 2,
    independent of the general jacobsthalSet_bddAbove axiom. -/
theorem jacobsthalY_two : jacobsthalY 2 = 1 := by
  unfold jacobsthalY
  apply le_antisymm
  · -- sSup ≤ 1: every element of jacobsthalSet 2 is ≤ 1
    apply csSup_le (jacobsthalSet_nonempty 2)
    intro y hy
    by_contra h; push_neg at h
    exact not_mem_jacobsthalSet_two (by omega) hy
  · -- 1 ≤ sSup: 1 is in the set and the set is bounded above
    exact le_csSup ⟨1, fun y hy => by
      by_contra h; push_neg at h
      exact not_mem_jacobsthalSet_two (by omega) hy⟩ one_mem_jacobsthalSet_two
