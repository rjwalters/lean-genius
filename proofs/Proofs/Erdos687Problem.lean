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

Axioms: 4 (jacobsthalY_eq_jacobsthal,
  iwaniec_upper, fgkmt_lower, maier_pomerance_conjecture)
Proved: jacobsthalSet_bddAbove (CRT induction: any covering leaves gaps within primorial)
  erdos_687_conjecture (from maier_pomerance_conjecture — M-P is stronger)
Theorems: 14 (plus private CRT helper lemmas)
Removed: jacobsthalSet_bddAbove axiom → proved as theorem
Sorries: 0
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

/- ## CRT induction: proving jacobsthalSet is bounded -/

/-- Product of primes in a Finset (as integers) is positive. -/
private lemma prod_primes_pos' (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) :
    (0 : ℤ) < ∏ p ∈ S, (p : ℤ) :=
  Finset.prod_pos fun p hp => Int.natCast_pos.mpr (hS p hp).pos

/-- A prime not in a Finset of primes doesn't divide their integer product. -/
private lemma prime_not_dvd_int_prod
    (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
    (q : ℕ) (hq : q.Prime) (hq_not : q ∉ S) :
    ¬ (q : ℤ) ∣ ∏ p ∈ S, (p : ℤ) := by
  rw [← Nat.cast_prod, Int.natCast_dvd_natCast]
  intro hdvd
  obtain ⟨r, hrS, hqr⟩ := hq.prime.dvd_finset_prod_iff.mp hdvd
  have : q = r := ((hS r hrS).eq_one_or_self_of_dvd q hqr).resolve_left hq.ne_one
  subst this
  exact hq_not hrS

/-- CRT induction: for any Finset of primes and covering function,
    some integer in [1, product] avoids all residue classes.

    Proof: Finset.induction. If m avoids primes in S', check m mod q.
    If m already avoids a(q), done. Otherwise m + P' avoids a(q)
    (since gcd(P', q) = 1 implies adding P' changes residue mod q)
    while still avoiding S' (since P' ≡ 0 mod each p ∈ S'). -/
private lemma exists_uncovered_in_prod
    (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) (a : ℕ → ℕ) :
    ∃ n : ℤ, 1 ≤ n ∧ n ≤ ∏ p ∈ S, (p : ℤ) ∧
      ∀ p ∈ S, n % (p : ℤ) ≠ (a p : ℤ) % (p : ℤ) := by
  induction S using Finset.induction with
  | empty =>
    exact ⟨1, le_rfl, by simp, fun _ hp => absurd hp (Finset.not_mem_empty _)⟩
  | insert hq_not ih =>
    rename_i q S'
    have hS' : ∀ p ∈ S', Nat.Prime p := fun p hp => hS p (Finset.mem_insert_of_mem hp)
    have hq : q.Prime := hS q (Finset.mem_insert_self q S')
    obtain ⟨m, hm1, hm2, hm_avoid⟩ := ih hS' a
    set P' : ℤ := ∏ p ∈ S', (p : ℤ) with hP'_def
    have hP'_pos : (0 : ℤ) < P' := prod_primes_pos' S' hS'
    have hq2 : (2 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq.two_le
    rw [Finset.prod_insert hq_not]
    by_cases hcase : m % (q : ℤ) = (a q : ℤ) % (q : ℤ)
    · -- m matches a(q) mod q: use m + P' instead
      refine ⟨m + P', by linarith, by nlinarith, ?_⟩
      intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hp'
      · -- p = q: (m + P') % q ≠ (a q) % q because q ∤ P'
        intro heq
        have hmod : (m + P') % (q : ℤ) = m % (q : ℤ) := heq.trans hcase.symm
        have hq_dvd : (q : ℤ) ∣ P' := by
          have h_neg := Int.modEq_iff_dvd.mp hmod
          -- h_neg : q ∣ (m - (m + P')) = -P'
          rwa [show m - (m + P') = -P' from by ring, dvd_neg] at h_neg
        exact prime_not_dvd_int_prod S' hS' q hq hq_not hq_dvd
      · -- p ∈ S': (m + P') % p = m % p since p | P'
        obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun i => (i : ℤ)) hp'
        rw [show m + P' = m + (p : ℤ) * k from by rw [hk], Int.add_mul_emod_self_left]
        exact hm_avoid p hp'
    · -- m already avoids a(q) mod q: use m directly
      exact ⟨m, hm1, le_trans hm2 (le_mul_of_one_le_left hP'_pos.le (by linarith)),
        fun p hp => by
          rcases Finset.mem_insert.mp hp with rfl | hp'
          · exact hcase
          · exact hm_avoid p hp'⟩

/-- The Jacobsthal set is bounded above by the primorial.
    Proof: by CRT induction, for any covering system, some integer
    in [1, primorial(x)] is uncovered. So no y > primorial(x) is
    achievable. -/
theorem jacobsthalSet_bddAbove (x : ℕ) :
    BddAbove (jacobsthalSet x) := by
  refine ⟨primorial x, fun y hy => ?_⟩
  by_contra h
  push_neg at h
  -- h : primorial x < y, hy : y ∈ jacobsthalSet x
  obtain ⟨a, ha⟩ := hy
  -- Extract simple function from dependent covering
  let a' : ℕ → ℕ := fun p =>
    if h : p.Prime ∧ p ≤ x then a p h.1 h.2 else 0
  set S := (Finset.range (x + 1)).filter Nat.Prime with hS_def
  have hS_prime : ∀ p ∈ S, Nat.Prime p := fun p hp => (Finset.mem_filter.mp hp).2
  have hprod_eq : ∏ p ∈ S, (p : ℤ) = (primorial x : ℤ) :=
    Nat.cast_prod.symm
  obtain ⟨n, hn1, hn2, hn_avoid⟩ := exists_uncovered_in_prod S hS_prime a'
  rw [hprod_eq] at hn2
  have hny : n ≤ (y : ℤ) := le_trans hn2 (by exact_mod_cast h.le)
  obtain ⟨p, hp, hpx, hcov⟩ := ha n hn1 hny
  have hpS : p ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp⟩
  have ha'_eq : (a' p : ℤ) % (p : ℤ) = (a p hp hpx : ℤ) % (p : ℤ) := by
    congr 1; exact_mod_cast show a' p = a p hp hpx from dif_pos ⟨hp, hpx⟩
  exact hn_avoid p hpS (by rwa [ha'_eq])

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
