/-
# Erdős Problem 461: Distinct Smooth Components in Short Intervals

Let `sₜ(n)` be the `t`-smooth component of `n`, i.e., the largest divisor
of `n` whose prime factors are all less than `t`. Define `f(n, t)` as the
number of distinct values of `sₜ(m)` for `m ∈ {n+1, …, n+t}`.

Is `f(n, t) ≫ t` for all `n` and `t`?

Erdős and Graham proved the weaker bound `f(n, t) ≫ t / log t`.

*Reference:* [erdosproblems.com/461](https://www.erdosproblems.com/461),
Erdős–Graham (1980), p. 92.
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/- ## Smooth components -/

/-- The `t`-smooth component of `n`: product of prime factors of `n`
(with multiplicity) that are strictly less than `t`. -/
noncomputable def smoothComponent (t n : ℕ) : ℕ :=
    (n.factors.filter (· < t)).prod

/- ### Infrastructure lemmas -/

-- Product of a filtered sublist divides the product of the full list.
private lemma list_prod_filter_dvd (l : List ℕ) (p : ℕ → Bool) :
    (l.filter p).prod ∣ l.prod := by
  induction l with
  | nil => simp
  | cons a tl ih =>
    simp only [List.filter_cons, List.prod_cons]
    split
    · simp only [List.prod_cons]; exact mul_dvd_mul_left a ih
    · exact dvd_mul_of_dvd_right ih a

-- A prime dividing a product of primes must equal one of them.
private lemma prime_dvd_list_prod_mem {p : ℕ} (hp : p.Prime) :
    ∀ (l : List ℕ), (∀ q ∈ l, q.Prime) → p ∣ l.prod → p ∈ l := by
  intro l
  induction l with
  | nil =>
    intro _ hd
    simp at hd
    exact absurd hd (by omega)
  | cons a tl ih =>
    intro hall hd
    simp only [List.prod_cons] at hd
    have ha_prime := hall a (List.mem_cons_self a tl)
    rcases hp.dvd_mul.mp hd with hpa | hptl
    · have := ha_prime.eq_one_or_self_of_dvd p hpa
      rcases this with rfl | rfl
      · exact absurd hp.one_lt (by omega)
      · exact List.mem_cons_self p tl
    · exact List.mem_cons.mpr (Or.inr
        (ih (fun q hq => hall q (List.mem_cons.mpr (Or.inr hq))) hptl))

/- ### Core properties -/

/-- `smoothComponent t n` always divides `n` (for positive `n`). -/
theorem smoothComponent_dvd (t n : ℕ) (hn : n ≠ 0) : smoothComponent t n ∣ n := by
  unfold smoothComponent
  have h := list_prod_filter_dvd n.factors (fun x => decide (x < t))
  rwa [Nat.prod_factors hn] at h

/-- `smoothComponent t n` is `t`-smooth: every prime factor is `< t`. -/
theorem smoothComponent_smooth (t n p : ℕ) (hp : p.Prime)
    (hd : p ∣ smoothComponent t n) : p < t := by
  unfold smoothComponent at hd
  have hall : ∀ q ∈ n.factors.filter (· < t), q.Prime := fun q hq =>
    Nat.prime_of_mem_factors (List.mem_filter.mp hq).1
  have hmem := prime_dvd_list_prod_mem hp _ hall hd
  exact (List.mem_filter.mp hmem).2

/-- `smoothComponent t n` is nonzero (product of primes, all ≥ 2). -/
theorem smoothComponent_pos (t n : ℕ) : 0 < smoothComponent t n := by
  unfold smoothComponent
  apply List.prod_pos
  intro x hx
  exact (Nat.prime_of_mem_factors (List.mem_filter.mp hx).1).pos

/-- No prime `< t` divides the complement part of the factorization. -/
private lemma no_small_prime_in_complement (t n p : ℕ) (hp : p.Prime)
    (hpt : p < t) (hd : p ∣ (n.factors.filter (fun x => ¬ decide (x < t))).prod) :
    False := by
  have hall : ∀ q ∈ n.factors.filter (fun x => ¬ decide (x < t)), q.Prime := fun q hq =>
    Nat.prime_of_mem_factors (List.mem_filter.mp hq).1
  have hmem := prime_dvd_list_prod_mem hp _ hall hd
  have := (List.mem_filter.mp hmem).2
  simp at this
  omega

/-- Product of filtered list times product of complement equals product of original.
    This is the multiplicative partition identity for filter predicates. -/
private lemma list_prod_filter_mul_not (l : List ℕ) (P : ℕ → Bool) :
    (l.filter P).prod * (l.filter (fun x => !P x)).prod = l.prod := by
  induction l with
  | nil => simp
  | cons a tl ih =>
    simp only [List.filter_cons, Bool.not_eq_true']
    by_cases hP : P a <;> simp [hP, List.prod_cons]
    · rw [mul_assoc, ih]
    · rw [mul_left_comm, ih]

/-- `smoothComponent t n` is the largest `t`-smooth divisor of `n`.
    Requires `n ≠ 0` since `smoothComponent t 0 = 1` but any
    `d` with all primes `< t` divides 0.
    Proof strategy: n = smoothComponent * complementPart where
    complementPart has all primes ≥ t. Then d and complementPart
    are coprime (disjoint prime support), so d ∣ smoothComponent. -/
theorem smoothComponent_largest (t n d : ℕ) (hn : n ≠ 0) :
    d ∣ n → (∀ p : ℕ, p.Prime → p ∣ d → p < t) → d ∣ smoothComponent t n := by
  intro hdn hsmooth
  -- Define the complement part: product of prime factors ≥ t
  set comp := (n.factors.filter (fun x => ¬ x < t)).prod with hcomp_def
  -- Key fact: n = smoothComponent * comp (partition of prime factorization)
  have hfact : smoothComponent t n * comp = n := by
    unfold smoothComponent
    rw [list_prod_filter_mul_not, Nat.prod_factors hn]
  -- d and comp are coprime: no prime divides both
  have hcop : Nat.Coprime d comp := by
    rw [Nat.coprime_comm, Nat.coprime_iff_gcd_eq_one]
    by_contra h
    push_neg at h
    -- gcd > 1 means some prime divides both
    have hgcd := Nat.exists_prime_and_dvd (by omega : Nat.gcd comp d ≠ 1)
    obtain ⟨p, hp, hpg⟩ := hgcd
    have hpcomp := (Nat.dvd_gcd.mp hpg).1
    have hpd := (Nat.dvd_gcd.mp hpg).2
    -- p | d → p < t (by smoothness of d)
    have hpt := hsmooth p hp hpd
    -- p | comp → p ≥ t (all factors of comp are ≥ t)
    exact no_small_prime_in_complement t n p hp hpt hpcomp
  -- d | smoothComponent * comp and coprime d comp → d | smoothComponent
  have hdn' : d ∣ smoothComponent t n * comp := hfact ▸ hdn
  exact (Nat.Coprime.dvd_of_dvd_mul_right hcop) hdn'

/- ## Counting distinct smooth components -/

/-- `f(n, t)` counts the distinct values of `sₜ(m)` for `m ∈ {n+1, …, n+t}`. -/
noncomputable def smoothDistinctCount (n t : ℕ) : ℕ :=
    ((Finset.Icc (n + 1) (n + t)).image (smoothComponent t)).card

/- ## Main conjecture -/

/-- Erdős Problem 461: There exists `C > 0` such that `f(n, t) ≥ C · t`
for all `n` and sufficiently large `t`. -/
def ErdosProblem461 : Prop :=
    ∃ C : ℝ, 0 < C ∧
      ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
        ∀ n : ℕ, C * (t : ℝ) ≤ (smoothDistinctCount n t : ℝ)

/- ## Known results -/

/-- Erdős–Graham: `f(n, t) ≫ t / log t`. -/
axiom erdos_graham_lower :
    ∃ C : ℝ, 0 < C ∧
      ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
        ∀ n : ℕ, C * (t : ℝ) / Real.log (t : ℝ) ≤ (smoothDistinctCount n t : ℝ)

/- ## Basic properties -/

/-- The smooth component of 1 is always 1. -/
theorem smoothComponent_one (t : ℕ) : smoothComponent t 1 = 1 := by
  simp [smoothComponent, Nat.factors_one]

/-- For `t ≤ 1`, every smooth component is 1 (no primes below 1). -/
theorem smoothComponent_t_le_one {t : ℕ} (n : ℕ) (ht : t ≤ 1) :
    smoothComponent t n = 1 := by
  simp only [smoothComponent]
  suffices h : n.factors.filter (· < t) = [] by simp [h]
  apply List.filter_eq_nil.mpr
  intro p hp
  simp only [decide_eq_true_eq, not_lt]
  have := (Nat.prime_of_mem_factors hp).two_le
  omega

/-- The count is at most `t` (there are only `t` values in the interval). -/
theorem smoothDistinctCount_le (n t : ℕ) : smoothDistinctCount n t ≤ t := by
  unfold smoothDistinctCount
  have h1 := @Finset.card_image_le _ _ (Finset.Icc (n + 1) (n + t)) (smoothComponent t)
  have h2 : (Finset.Icc (n + 1) (n + t)).card = t := by
    simp only [Finset.card_Icc]; omega
  linarith

/-- For `t = 0`, the interval is empty, so the count is 0. -/
theorem smoothDistinctCount_zero (n : ℕ) : smoothDistinctCount n 0 = 0 := by
  simp [smoothDistinctCount, Finset.Icc_eq_empty (by omega : ¬(n + 1 ≤ n + 0))]

/-- Smooth component of 0 is 1 (0 has no prime factors). -/
theorem smoothComponent_zero (t : ℕ) : smoothComponent t 0 = 1 := by
  simp [smoothComponent, Nat.factors_zero]

/-- For a prime `p`, `smoothComponent t p = p` if `p < t`, else `1`. -/
theorem smoothComponent_prime (t p : ℕ) (hp : p.Prime) :
    smoothComponent t p = if p < t then p else 1 := by
  unfold smoothComponent
  rw [Nat.factors_prime hp]
  simp only [List.filter_cons, List.filter_nil, List.append_nil]
  split <;> rename_i h
  · simp [List.prod_cons]
  · simp
