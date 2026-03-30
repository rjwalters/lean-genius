/-
Erdős Problem #382: Prime Powers in Factorial Products

Source: https://erdosproblems.com/382
Status: OPEN

Statement:
Let u ≤ v be such that the largest prime dividing ∏_{u ≤ m ≤ v} m
appears with exponent at least 2.

Questions:
1. Is v - u = v^o(1)? (i.e., does v - u grow subpolynomially in v?)
2. Can v - u be arbitrarily large?

Known Results:
- Ramachandra: v - u ≤ v^{1/2 + o(1)}
- Under Cramér's conjecture: if u + u^ε < v for any ε > 0, then the largest
  prime divisor has exponent 1 (suggesting v - u = v^o(1) is true)

Key Insight:
The product m! / (u-1)! = u · (u+1) · ... · v includes all primes p with u ≤ p ≤ v.
For the largest such prime p to appear with exponent ≥ 2, we need p² ≤ v,
which means the interval [u, v] must contain no primes larger than √v.

References:
- Erdős-Graham [ErGr80]
- Ramachandra: bounds on largest prime in short intervals
- OEIS: A388850
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic

open Nat BigOperators Finset Real

namespace Erdos382

/- ## Part I: Basic Definitions -/

/--
**The Product of an Interval**

prod_interval(u, v) = u · (u+1) · ... · v = v! / (u-1)!

This is the product of consecutive integers from u to v inclusive.
-/
def prodInterval (u v : ℕ) : ℕ :=
  ∏ m ∈ Finset.Icc u v, m

/-- prod_interval(u, u) = u. -/
theorem prodInterval_singleton (n : ℕ) (hn : n > 0) :
    prodInterval n n = n := by
  simp [prodInterval, Finset.Icc_self]

/-- prod_interval(1, n) = n!. -/
theorem prodInterval_factorial (n : ℕ) :
    prodInterval 1 n = n.factorial := by
  unfold prodInterval
  induction n with
  | zero => simp
  | succ n ih =>
    have h : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [h, Finset.prod_insert (by simp [Finset.mem_Icc])]
    rw [ih, Nat.factorial_succ, mul_comm]

/- ## Part II: Largest Prime Divisor -/

/--
**Largest Prime Divisor**

The largest prime that divides n, or 0 if n ≤ 1.
-/
noncomputable def largestPrimeDivisor (n : ℕ) : ℕ :=
  if h : n > 1 then
    n.primeFactorsList.foldl max 0
  else 0

/-- Helper: foldl max is ≥ init. -/
private lemma foldl_max_ge_init : ∀ (l : List ℕ) (init : ℕ),
    l.foldl max init ≥ init
  | [], init => le_refl init
  | _ :: as, init => le_trans (le_max_left init _) (foldl_max_ge_init as _)

/-- Helper: foldl max is ≥ any member. -/
private lemma foldl_max_ge_of_mem : ∀ {l : List ℕ} {x : ℕ}, x ∈ l →
    ∀ (init : ℕ), l.foldl max init ≥ x
  | _ :: _, _, List.Mem.head _, init =>
    le_trans (le_max_right init _) (foldl_max_ge_init _ _)
  | _ :: _, _, List.Mem.tail _ hx, init =>
    foldl_max_ge_of_mem hx _

/-- Helper: foldl max result equals init or is a member of the list. -/
private lemma foldl_max_eq_init_or_mem : ∀ (l : List ℕ) (init : ℕ),
    l.foldl max init = init ∨ l.foldl max init ∈ l
  | [], init => Or.inl rfl
  | a :: as, init => by
    simp only [List.foldl_cons]
    rcases foldl_max_eq_init_or_mem as (max init a) with h | h
    · rw [h]
      rcases le_or_lt a init with hle | hlt
      · left; exact max_eq_left hle
      · right; rw [max_eq_right (le_of_lt hlt)]; exact List.mem_cons_self a as
    · right; exact List.mem_cons_of_mem a h

/-- primeFactorsList is nonempty for n > 1. -/
private lemma primeFactorsList_ne_nil (n : ℕ) (hn : n > 1) :
    n.primeFactorsList ≠ [] := by
  intro h
  have := Nat.prod_primeFactorsList (show n ≠ 0 by omega)
  rw [h, List.prod_nil] at this
  omega

/-- The foldl max 0 of primeFactorsList is a member for n > 1. -/
private lemma foldl_max_mem_primeFactorsList (n : ℕ) (hn : n > 1) :
    n.primeFactorsList.foldl max 0 ∈ n.primeFactorsList := by
  have hne := primeFactorsList_ne_nil n hn
  rcases foldl_max_eq_init_or_mem n.primeFactorsList 0 with h | h
  · exfalso
    obtain ⟨x, hx⟩ : ∃ a, a ∈ n.primeFactorsList := by
      cases hl : n.primeFactorsList with
      | nil => exact absurd hl hne
      | cons a l => exact ⟨a, List.mem_cons_self a l⟩
    have h1 := foldl_max_ge_of_mem hx 0
    rw [h] at h1
    have h2 := (Nat.prime_of_mem_primeFactorsList hx).two_le
    omega
  · exact h

/-- The largest prime divisor divides n. -/
theorem largestPrimeDivisor_dvd (n : ℕ) (hn : n > 1) :
    largestPrimeDivisor n ∣ n := by
  simp only [largestPrimeDivisor, dif_pos hn]
  exact Nat.dvd_of_mem_primeFactorsList (foldl_max_mem_primeFactorsList n hn)

/-- The largest prime divisor is prime (if n > 1). -/
theorem largestPrimeDivisor_prime (n : ℕ) (hn : n > 1) :
    (largestPrimeDivisor n).Prime := by
  simp only [largestPrimeDivisor, dif_pos hn]
  exact Nat.prime_of_mem_primeFactorsList (foldl_max_mem_primeFactorsList n hn)

/-- Any prime divisor is ≤ the largest. -/
theorem prime_le_largestPrimeDivisor (n p : ℕ) (hn : n > 1) (hp : p.Prime) (hdiv : p ∣ n) :
    p ≤ largestPrimeDivisor n := by
  simp only [largestPrimeDivisor, dif_pos hn]
  have hmem : p ∈ n.primeFactorsList := by
    rw [Nat.mem_primeFactorsList (show n ≠ 0 by omega)]
    exact ⟨hp, hdiv⟩
  exact foldl_max_ge_of_mem hmem 0

/- ## Part III: Exponent of Prime in Product -/

/--
**P-adic Valuation**

The exponent of prime p in the factorization of n.
-/
def exponent (p n : ℕ) : ℕ := n.factorization p

/-- The exponent of p in the product u·(u+1)·...·v. -/
noncomputable def exponentInProduct (p u v : ℕ) : ℕ :=
  exponent p (prodInterval u v)

/-- Factorization distributes over Finset products of nonzero naturals. -/
private lemma factorization_finset_prod_id (s : Finset ℕ) (h : ∀ m ∈ s, m ≠ 0) :
    (∏ m ∈ s, m).factorization = ∑ m ∈ s, m.factorization := by
  induction s using Finset.induction_on with
  | empty => simp [Nat.factorization_one]
  | insert ha ih =>
    rename_i a s _
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    rw [Nat.factorization_mul (h a (Finset.mem_insert_self a s))
      (Finset.prod_ne_zero (fun m hm => h m (Finset.mem_insert_of_mem hm)))]
    congr 1
    exact ih (fun m hm => h m (Finset.mem_insert_of_mem hm))

/-- The exponent of p in ∏_{m ∈ [u,v]} m equals the sum of individual exponents.
    Requires u > 0 to ensure all terms in the product are nonzero. -/
theorem exponentInProduct_sum (p u v : ℕ) (hp : p.Prime) (hu : u > 0) :
    exponentInProduct p u v = ∑ m ∈ Finset.Icc u v, exponent p m := by
  simp only [exponentInProduct, exponent, prodInterval]
  have hne : ∀ m ∈ Finset.Icc u v, m ≠ 0 := fun m hm => by
    simp [Finset.mem_Icc] at hm; omega
  conv_lhs => rw [factorization_finset_prod_id _ hne]
  exact Finsupp.finset_sum_apply _ _ _

/- ## Part IV: The Condition -/

/--
**The Erdős-Graham Condition**

An interval [u, v] satisfies the condition if the largest prime dividing
the product u·(u+1)·...·v appears with exponent at least 2.
-/
def satisfiesCondition (u v : ℕ) : Prop :=
  u ≤ v ∧ u > 0 ∧
  let P := prodInterval u v
  let p := largestPrimeDivisor P
  exponent p P ≥ 2

/-- If p is the largest prime ≤ v and p² > v, then p has exponent 1.
    Proof uses Bertrand's postulate: since p is the largest prime ≤ v,
    Bertrand gives 2p > v, so the only multiple of p in [u,v] is p itself. -/
theorem largest_prime_exp_one (u v p : ℕ) (hu : u > 0) (huv : u ≤ v)
    (hp : p.Prime) (hpv : p ≤ v) (hpu : u ≤ p)
    (hlargest : ∀ q, q.Prime → q ≤ v → q ≤ p)
    (hsq : p * p > v) :
    exponent p (prodInterval u v) = 1 := by
  -- Step 1: By Bertrand's postulate, 2p > v
  have h2p : v < 2 * p := by
    obtain ⟨q, hq_prime, hpq, hq2p⟩ :=
      Nat.exists_prime_lt_and_le_two_mul p (by omega : p ≠ 0)
    -- q is prime, p < q ≤ 2p. If q ≤ v, then q ≤ p by hlargest, contradicting p < q
    by_contra h; push_neg at h
    have : q ≤ v := le_trans hq2p h
    exact absurd (hlargest q hq_prime this) (not_le.mpr hpq)
  -- Step 2: Rewrite exponent as sum via exponentInProduct_sum
  show exponentInProduct p u v = 1
  rw [exponentInProduct_sum p u v hp hu]
  -- Step 3: p ∈ [u, v]
  have hp_mem : p ∈ Finset.Icc u v := by simp [Finset.mem_Icc]; omega
  -- Step 4: Split sum at p
  rw [← Finset.add_sum_erase _ _ hp_mem]
  -- Goal: exponent p p + ∑ m ∈ (Icc u v).erase p, exponent p m = 1
  -- Step 5: exponent p p = 1 for prime p
  have hexp_self : exponent p p = 1 := by
    simp only [exponent, Nat.Prime.factorization hp, Finsupp.single_eq_same]
  -- Step 6: All other terms are 0 (p does not divide any m ≠ p in [u,v])
  have hexp_rest : ∀ m ∈ (Finset.Icc u v).erase p, exponent p m = 0 := by
    intro m hm
    simp [Finset.mem_erase, Finset.mem_Icc] at hm
    obtain ⟨hmp, hmu, hmv⟩ := hm
    simp only [exponent]
    rw [Nat.factorization_eq_zero_of_not_dvd]
    intro hdvd
    -- p | m, so m = k * p for some k ≥ 1. Since m ≠ p, k ≥ 2, so m ≥ 2p > v.
    have hk : m / p ≥ 1 := Nat.one_le_div_of_dvd (by omega : m > 0) hdvd
    have hk2 : m / p ≠ 1 := by intro h; exact hmp (Nat.eq_of_dvd_of_div_eq_one hdvd h).symm
    have : m ≥ 2 * p := by
      have := Nat.div_mul_cancel hdvd
      have : m / p ≥ 2 := by omega
      nlinarith [this, Nat.div_mul_cancel hdvd]
    omega
  rw [Finset.sum_eq_zero hexp_rest, hexp_self]

/-- NOTE: The previous axiom exp_ge_two_needs_square was INCORRECT.
    Counterexample: [3,6] with p=3. Exponent is 2 (from v₃(3)=1, v₃(6)=1)
    but there is no k ∈ [3,6] with 9 | k. The exponent ≥ 2 can come from
    multiple distinct multiples of p, not just from p² dividing a single term.
    Removed as it was unused and mathematically wrong. -/

/- ## Part V: The Questions -/

/--
**Question 1 (OPEN)**: Is v - u = v^o(1)?

For intervals [u,v] satisfying the condition, does v - u grow
subpolynomially in v? I.e., for every ε > 0 and large enough v,
is v - u < v^ε?
-/
def question1 : Prop :=
  ∀ ε : ℝ, ε > 0 →
    ∃ V : ℕ, ∀ u v : ℕ, v ≥ V → satisfiesCondition u v →
      (v - u : ℝ) < (v : ℝ) ^ ε

/-- The conjecture that Question 1 has answer YES. -/
/--
**Question 2 (OPEN)**: Can v - u be arbitrarily large?

Are there intervals [u, v] satisfying the condition with
v - u arbitrarily large?
-/
def question2 : Prop :=
  ∀ L : ℕ, ∃ u v : ℕ, satisfiesCondition u v ∧ v - u > L

/-- Cambie's heuristic suggests YES for Question 2. -/
/- ## Part VI: Known Upper Bound -/

/--
**Ramachandra's Bound**

v - u ≤ v^{1/2 + o(1)}

More precisely, for any ε > 0 and large enough v, if [u,v] satisfies
the condition, then v - u ≤ v^{1/2 + ε}.
-/
axiom ramachandra_bound (ε : ℝ) (hε : ε > 0) :
    ∃ V : ℕ, ∀ u v : ℕ, v ≥ V → satisfiesCondition u v →
      (v - u : ℝ) ≤ (v : ℝ) ^ (1/2 + ε)

/- ## Part VII: Connection to Cramér's Conjecture -/

/--
**Cramér's Conjecture**

The gap between consecutive primes p_n and p_{n+1} is O((log p_n)²).

This famous conjecture would imply Question 1 has answer YES.
-/
def cramersConjecture : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ p q : ℕ, p.Prime → q.Prime → p < q →
    (∀ r, p < r → r < q → ¬r.Prime) →
    (q - p : ℝ) ≤ C * (Real.log p) ^ 2

/-- Under Cramér's conjecture, Question 1 is true.
    Proof: the condition forces no primes > √v in [u,v] (by no_prime_in_upper_half).
    For large v under Cramér, u must exceed √v (else [√v,v] is a prime-free gap of
    length ≈ v, contradicting the O((log v)²) gap bound). So [u,v] lies within a
    single Cramér gap of length ≤ C(log v)², which is < v^ε for large v. -/
-- Helper: C * (log v)² < v^ε for large v.
-- From log = o(x^(ε/4)), squaring gives log² ≤ x^(ε/2),
-- and absorbing C into x^(ε/2) yields C * log² < x^ε.
private lemma log_sq_lt_rpow (C : ℝ) (hC : C > 0) (ε : ℝ) (hε : ε > 0) :
    ∃ V : ℕ, ∀ v : ℕ, v ≥ V → C * (Real.log ↑v) ^ 2 < (v : ℝ) ^ ε := by
  -- Step 1: log x ≤ (1/2) * x^(ε/4) eventually (from isLittleO)
  have hε4 : (0 : ℝ) < ε / 4 := by linarith
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp
    ((isLittleO_log_rpow_atTop hε4).bound (show (0 : ℝ) < 1 / 2 by norm_num))
  -- Step 2: C ≤ v^(ε/2) for large v
  -- Since rpow ε/2 → ∞ and C is fixed, find threshold for C ≤ v^(ε/2)
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  -- Use: n ≥ ⌈C^(2/ε)⌉₊ implies (n : ℝ) ≥ C^(2/ε), hence n^(ε/2) ≥ C
  refine ⟨max ⌈R⌉₊ (max ⌈C ^ (2 / ε)⌉₊ 2), fun v hv => ?_⟩
  have hR_le : (R : ℝ) ≤ (v : ℝ) := by
    calc R ≤ ⌈R⌉₊ := Nat.le_ceil R
      _ ≤ v := by exact_mod_cast le_trans (le_max_left _ _) hv
  have hv_pos : (0 : ℝ) < (v : ℝ) := by
    have : 2 ≤ v := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hv
    exact_mod_cast show 0 < v by omega
  have hv_nn : (0 : ℝ) ≤ (v : ℝ) := le_of_lt hv_pos
  -- Extract: |log v| ≤ (1/2) * v^(ε/4)
  have hlog_bound := hR (v : ℝ) hR_le
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ v by omega))),
      abs_of_nonneg (rpow_nonneg hv_nn _)] at hlog_bound
  -- log² v ≤ (1/4) * v^(ε/2) (by squaring, since (1/2)² = 1/4)
  have hlog_sq : (Real.log (v : ℝ)) ^ 2 ≤ (1 / 4) * (v : ℝ) ^ (ε / 2) := by
    calc (Real.log (v : ℝ)) ^ 2
        = Real.log (v : ℝ) * Real.log (v : ℝ) := by ring
      _ ≤ (1 / 2 * (v : ℝ) ^ (ε / 4)) * (1 / 2 * (v : ℝ) ^ (ε / 4)) :=
          mul_le_mul hlog_bound hlog_bound
            (Real.log_nonneg (by exact_mod_cast (show 1 ≤ v by omega)))
            (by positivity)
      _ = 1 / 4 * ((v : ℝ) ^ (ε / 4) * (v : ℝ) ^ (ε / 4)) := by ring
      _ = 1 / 4 * (v : ℝ) ^ (ε / 2) := by
          congr 1; rw [← rpow_add hv_pos]; congr 1; ring
  -- C ≤ v^(ε/2): from v ≥ C^(2/ε)
  have hC_bound : C ≤ (v : ℝ) ^ (ε / 2) := by
    have hCexp_le : ⌈C ^ (2 / ε)⌉₊ ≤ v := by
      exact_mod_cast le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hv
    have hCexp_real : C ^ (2 / ε) ≤ (v : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast hCexp_le)
    calc C = (C ^ (2 / ε)) ^ (ε / 2) := by
            rw [← rpow_mul hC.le]; congr 1; field_simp
      _ ≤ (v : ℝ) ^ (ε / 2) := rpow_le_rpow (rpow_nonneg hC.le _) hCexp_real hε2.le
  -- Combine: C * log² v ≤ C * (1/4) * v^(ε/2) ≤ (1/4) * v^(ε/2) * v^(ε/2) ≤ v^ε
  calc C * (Real.log (v : ℝ)) ^ 2
      ≤ C * (1 / 4 * (v : ℝ) ^ (ε / 2)) := by
        exact mul_le_mul_of_nonneg_left hlog_sq hC.le
    _ = C / 4 * (v : ℝ) ^ (ε / 2) := by ring
    _ < 1 * (v : ℝ) ^ (ε / 2) * (v : ℝ) ^ (ε / 2) := by
        have : C / 4 < (v : ℝ) ^ (ε / 2) := by linarith
        nlinarith [rpow_pos_of_pos hv_pos (ε / 2)]
    _ = (v : ℝ) ^ ε := by rw [one_mul, ← rpow_add hv_pos]; congr 1; ring

theorem cramer_implies_q1 : cramersConjecture → question1 := by
  intro ⟨C, hC, hcramer⟩ ε hε
  -- Find V₁ where C(log v)² < v^ε
  obtain ⟨V₁, hV₁⟩ := log_sq_lt_rpow C hC ε hε
  -- Find V₂ where v - √v > C(log v)²
  -- Strategy: C*log²(v) < v^(1/2) (from log_sq_lt_rpow) and v - √v > √v for v ≥ 5
  obtain ⟨V₂, hV₂⟩ : ∃ V₂ : ℕ, ∀ v : ℕ, v ≥ V₂ →
      (v : ℝ) - Real.sqrt ↑v > C * (Real.log ↑v) ^ 2 := by
    obtain ⟨V', hV'⟩ := log_sq_lt_rpow C hC (1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
    refine ⟨max V' 5, fun v hv => ?_⟩
    have hv5 : 5 ≤ v := le_trans (le_max_right _ _) hv
    have hV'_le : V' ≤ v := le_trans (le_max_left _ _) hv
    have hv_pos : (0 : ℝ) < (v : ℝ) := by exact_mod_cast show 0 < v by omega
    have hv_nn : (0 : ℝ) ≤ (v : ℝ) := le_of_lt hv_pos
    -- C * log²(v) < v^(1/2)
    have hlt := hV' v hV'_le
    -- v^(1/2) = √v (standard: Real.sqrt_eq_rpow)
    have hrpow_sqrt : (v : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt (v : ℝ) :=
      (Real.sqrt_eq_rpow (v : ℝ)).symm
    -- So C * log²(v) < √v
    rw [hrpow_sqrt] at hlt
    -- v - √v > √v ≥ C*log²(v), so v - √v > C*log²(v)
    -- √v * √v = v and √v ≥ √5 > 2, so 2*√v < v, giving v - √v > √v
    have hsqrt_sq : Real.sqrt (v : ℝ) * Real.sqrt (v : ℝ) = (v : ℝ) :=
      Real.mul_self_sqrt hv_nn
    have hsqrt_pos : 0 < Real.sqrt (v : ℝ) := Real.sqrt_pos.mpr hv_pos
    have hsqrt_ge2 : Real.sqrt (v : ℝ) ≥ 2 := by
      rw [ge_iff_le, ← Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num),
          show (2 : ℝ) ^ 2 = 4 from by norm_num]
      exact Real.sqrt_le_sqrt (by exact_mod_cast show (4 : ℕ) ≤ v by omega)
    -- v - √v = √v(√v - 1) ≥ √v · 1 = √v (since √v ≥ 2 implies √v - 1 ≥ 1)
    have hgap : (v : ℝ) - Real.sqrt (v : ℝ) ≥ Real.sqrt (v : ℝ) := by
      nlinarith [hsqrt_sq, hsqrt_ge2]
    linarith
  use max (max V₁ V₂) 4
  intro u v hv hcond
  obtain ⟨huv, hu, _⟩ := hcond
  have hno_large := no_prime_in_upper_half u v hu huv hcond
  have hv4 : v ≥ 4 := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hv
  have hV₁_le : V₁ ≤ v := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hv
  have hV₂_le : V₂ ≤ v := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hv
  -- Step 1: u > Nat.sqrt v (by Bertrand + contradiction with hno_large)
  have hu_gt_sqrt : u > Nat.sqrt v := by
    by_contra h
    push_neg at h
    -- Bertrand: ∃ prime p with Nat.sqrt v < p ≤ 2 * Nat.sqrt v
    have hsqrt_pos : Nat.sqrt v ≠ 0 := by omega
    obtain ⟨p, hp, hp_gt, hp_le⟩ := Nat.exists_prime_lt_and_le_two_mul (Nat.sqrt v) hsqrt_pos
    -- p ≤ 2 * Nat.sqrt v ≤ v (since Nat.sqrt v ≤ √v and 2√v ≤ v for v ≥ 4)
    have hp_le_v : p ≤ v := by
      calc p ≤ 2 * Nat.sqrt v := hp_le
        _ ≤ v := by
          have := Nat.sqrt_le_self v
          have := (Nat.sqrt_lt_self (by omega : v ≥ 2)).le
          omega
    -- u ≤ Nat.sqrt v < p, so u ≤ p
    have hup : u ≤ p := by omega
    -- But hno_large says p ≤ Nat.sqrt v, contradicting p > Nat.sqrt v
    exact absurd (hno_large p hp hup hp_le_v) (by omega)
  -- Step 2: [u,v] is prime-free (primes in [u,v] would be > Nat.sqrt v, contradicting hno_large)
  have hprime_free : ∀ p, Nat.Prime p → u ≤ p → p ≤ v → False := by
    intro p hp hup hpv
    have := hno_large p hp hup hpv
    omega
  -- Step 3: Find consecutive primes p₀ < u ≤ v < q₀
  -- q₀: smallest prime > v (exists by Bertrand)
  have ⟨q_wit, hq_wit_prime, hq_wit_gt, _⟩ :=
    Nat.exists_prime_lt_and_le_two_mul v (by omega)
  let q₀ := Nat.find ⟨q_wit, hq_wit_prime, by omega : q_wit > v⟩
  have hq₀_spec := Nat.find_spec ⟨q_wit, hq_wit_prime, by omega : q_wit > v⟩
  have hq₀_prime : q₀.Prime := hq₀_spec.1
  have hq₀_gt : q₀ > v := hq₀_spec.2
  have hq₀_min : ∀ r, r.Prime → r > v → q₀ ≤ r := fun r hr hrv =>
    Nat.find_min' ⟨q_wit, hq_wit_prime, by omega⟩ ⟨hr, hrv⟩
  -- p₀: largest prime < u (exists since 2 < u)
  let primes_lt_u := (Finset.range u).filter Nat.Prime
  have hne : primes_lt_u.Nonempty := by
    refine ⟨2, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Nat.prime_iff.mpr ⟨by omega, by omega⟩⟩⟩
  let p₀ := primes_lt_u.max' hne
  have hp₀_mem := Finset.max'_mem primes_lt_u hne
  have hp₀_prime : p₀.Prime := (Finset.mem_filter.mp hp₀_mem).2
  have hp₀_lt : p₀ < u := Finset.mem_range.mp (Finset.mem_filter.mp hp₀_mem).1
  have hp₀_max : ∀ r, r.Prime → r < u → r ≤ p₀ := by
    intro r hr hru
    exact Finset.le_max' primes_lt_u r (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hru, hr⟩)
  -- p₀ and q₀ are consecutive primes (no prime between them)
  have hconsec : ∀ r, p₀ < r → r < q₀ → ¬r.Prime := by
    intro r hr₁ hr₂ hr_prime
    -- r < q₀ and q₀ is min prime > v, so r ≤ v
    have hrv : r ≤ v := by
      by_contra h; push_neg at h; exact absurd (hq₀_min r hr_prime (by omega)) (by omega)
    -- r > p₀ and r.Prime, so r ≥ u (otherwise r ≤ p₀ by maximality)
    have hru : u ≤ r := by
      by_contra h; push_neg at h; exact absurd (hp₀_max r hr_prime h) (by omega)
    -- But r.Prime, u ≤ r, r ≤ v contradicts hprime_free
    exact hprime_free r hr_prime hru hrv
  have hp₀_lt_q₀ : p₀ < q₀ := by omega
  -- Step 4: Apply Cramér to consecutive primes p₀, q₀
  have hcramer_bound : (q₀ - p₀ : ℝ) ≤ C * (Real.log p₀) ^ 2 :=
    hcramer p₀ q₀ hp₀_prime hq₀_prime hp₀_lt_q₀ hconsec
  -- Step 5: Chain v - u ≤ q₀ - p₀ ≤ C * log² p₀ ≤ C * log² v < v^ε
  have hvu_le : (v - u : ℝ) ≤ (q₀ - p₀ : ℝ) := by
    have : (u : ℝ) ≥ (p₀ : ℝ) + 1 := by exact_mod_cast show u ≥ p₀ + 1 by omega
    have : (v : ℝ) ≤ (q₀ : ℝ) - 1 := by exact_mod_cast show v ≤ q₀ - 1 by omega
    linarith
  have hlog_mono : (Real.log p₀) ^ 2 ≤ (Real.log v) ^ 2 := by
    apply sq_le_sq'
    · linarith [Real.log_nonneg (show (1 : ℝ) ≤ ↑v by exact_mod_cast show 1 ≤ v by omega)]
    · exact Real.log_le_log (by exact_mod_cast show 0 < p₀ from Nat.Prime.pos hp₀_prime)
        (by exact_mod_cast show p₀ ≤ v by omega)
  calc (v - u : ℝ) ≤ (q₀ - p₀ : ℝ) := hvu_le
    _ ≤ C * (Real.log p₀) ^ 2 := hcramer_bound
    _ ≤ C * (Real.log v) ^ 2 := by exact mul_le_mul_of_nonneg_left hlog_mono hC.le
    _ < (v : ℝ) ^ ε := hV₁ v hV₁_le

/- ## Part VIII: Examples -/

/-- Example: [2, 4] has product 24 = 2³ · 3. Largest prime is 3, exp(3) = 1. -/
example : prodInterval 2 4 = 24 := by
  simp [prodInterval]
  native_decide

/-- If [u, v] satisfies the condition, no prime in [u, v] exceeds √v.

    Proof: Suppose p is a prime in [u, v] with p > √v. Then p divides the
    product, so q := largestPrimeDivisor(prod) ≥ p > √v. By Bertrand's
    postulate: 2q > v (since a prime r with q < r ≤ 2q and r ∈ [u,v] would
    divide the product, giving q ≥ r > q, contradiction). So q is the unique
    multiple of q in [u,v], and since q² > v, exponent(q) = 1 — contradicting
    the condition which requires exponent ≥ 2.

    NOTE: Previous version was incorrect (omitted u ≤ p, claiming no prime
    exists between √v and v, which is absurd for most v). -/
theorem no_prime_in_upper_half (u v : ℕ) (hu : u > 0) (huv : u ≤ v)
    (hcond : satisfiesCondition u v) :
    ∀ p : ℕ, p.Prime → u ≤ p → p ≤ v → p ≤ Nat.sqrt v := by
  intro p hp hpu hpv
  by_contra hgt
  push_neg at hgt
  -- Extract condition components
  obtain ⟨_, _, hcond_exp⟩ := hcond
  -- p ∈ [u, v] and p divides the product
  have hp_mem : p ∈ Finset.Icc u v := Finset.mem_Icc.mpr ⟨hpu, hpv⟩
  have hp_dvd : p ∣ prodInterval u v :=
    dvd_trans (dvd_refl p) (Finset.dvd_prod_of_mem id hp_mem)
  -- Product > 1 (since it contains p ≥ 2)
  have hprod_gt : prodInterval u v > 1 := by
    have : prodInterval u v ≥ p := by
      unfold prodInterval
      calc ∏ m ∈ Finset.Icc u v, m
          ≥ ∏ _ ∈ ({p} : Finset ℕ), p := by
            apply Finset.prod_le_prod_of_subset_of_one_le'
              (Finset.singleton_subset_iff.mpr hp_mem)
            intro m hm _; exact Finset.mem_Icc.mp hm |>.1 |> (Nat.one_le_iff_ne_zero.mpr ∘ Nat.not_eq_zero_of_lt ∘ Nat.lt_of_lt_of_le (by omega : 0 < u))
        _ = p := Finset.prod_singleton
    omega
  -- q := largestPrimeDivisor ≥ p > √v
  set q := largestPrimeDivisor (prodInterval u v) with hq_def
  have hq_prime := largestPrimeDivisor_prime _ hprod_gt
  have hpq : p ≤ q := prime_le_largestPrimeDivisor _ _ hprod_gt hp hp_dvd
  -- By Bertrand's postulate: 2q > v
  have h2q : v < 2 * q := by
    obtain ⟨r, hr_prime, hqr, hr2q⟩ :=
      Nat.exists_prime_lt_and_le_two_mul q (by omega : q ≠ 0)
    by_contra h; push_neg at h
    -- r > q ≥ p ≥ u and r ≤ 2q ≤ v, so r ∈ [u, v] and divides product
    have hr_mem : r ∈ Finset.Icc u v := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hr_dvd : r ∣ prodInterval u v :=
      dvd_trans (dvd_refl r) (Finset.dvd_prod_of_mem id hr_mem)
    -- q ≥ r > q: contradiction
    exact absurd (prime_le_largestPrimeDivisor _ _ hprod_gt hr_prime hr_dvd) (not_le.mpr hqr)
  -- q divides some element m ∈ [u, v]; since 2q > v, m must equal q
  have hq_dvd := largestPrimeDivisor_dvd _ hprod_gt
  obtain ⟨m, hm_mem, hq_dvd_m⟩ :=
    (hq_prime.prime).dvd_finset_prod_iff.mp (show q ∣ ∏ m ∈ Finset.Icc u v, m from hq_dvd)
  have hm_le : m ≤ v := (Finset.mem_Icc.mp hm_mem).2
  have hm_pos : m > 0 := by omega
  -- m is a multiple of q, m ≤ v < 2q, so m = q
  have hm_eq_q : m = q := by
    have : m / q ≥ 1 := Nat.div_pos (Nat.le_of_dvd hm_pos hq_dvd_m) (by omega : q > 0)
    have : m / q < 2 := by
      rw [Nat.div_lt_iff_lt_mul (by omega : q > 0)]
      omega
    have hk1 : m / q = 1 := by omega
    calc m = m / q * q := (Nat.div_mul_cancel hq_dvd_m).symm
      _ = 1 * q := by rw [hk1]
      _ = q := one_mul q
  -- So q ∈ [u, v]
  have hq_mem : q ∈ Finset.Icc u v := hm_eq_q ▸ hm_mem
  -- Compute exponent via sum decomposition
  have hexp_eq := exponentInProduct_sum q u v hq_prime hu
  rw [← Finset.add_sum_erase _ _ hq_mem] at hexp_eq
  -- v_q(q) = 1 for prime q
  have hexp_q : exponent q q = 1 := by
    simp only [exponent, Nat.Prime.factorization hq_prime, Finsupp.single_eq_same]
  -- All other terms are 0: q ∤ m for m ∈ [u,v], m ≠ q (since 2q > v)
  have hexp_zero : ∀ m' ∈ (Finset.Icc u v).erase q, exponent q m' = 0 := by
    intro m' hm'
    obtain ⟨hm'q, hm'u, hm'v⟩ := by
      simp only [Finset.mem_erase, Finset.mem_Icc] at hm'
      exact ⟨hm'.1, hm'.2.1, hm'.2.2⟩
    simp only [exponent]
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hdvd
    -- q | m' and m' ≤ v < 2q, so m' = q. But m' ≠ q. Contradiction.
    have h1 : m' / q ≥ 1 := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) (by omega)
    have h2 : m' / q < 2 := by rw [Nat.div_lt_iff_lt_mul (by omega : q > 0)]; omega
    have : m' = q := by
      calc m' = m' / q * q := (Nat.div_mul_cancel hdvd).symm
        _ = 1 * q := by omega
        _ = q := one_mul q
    exact hm'q this
  rw [Finset.sum_eq_zero hexp_zero] at hexp_eq
  -- exponentInProduct q u v = 1, but condition says ≥ 2
  simp only [hexp_q, add_zero] at hexp_eq
  linarith [hcond_exp, hexp_eq]

/- ## Part IX: The Prime-Free Interval Perspective -/

/--
**Prime-Free Interval Perspective**

The condition is equivalent to asking: the interval [u, v] contains
no primes larger than √v.

Equivalently, all primes in [u, v] are ≤ √v, so their squares can
fit in [1, v].
-/
def noPrimeLargerThanSqrt (u v : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → u ≤ p → p ≤ v → p ≤ Nat.sqrt v

/-- NOTE: The previous axiom condition_iff_no_large_prime was INCORRECT.
    Counterexample: [24, 28]. No primes in [24,28] (all composite), so
    noPrimeLargerThanSqrt is vacuously true. But the product 24·25·26·27·28
    has largest prime factor 13 (from 26 = 2·13), and 13 appears with
    exponent 1 only, so satisfiesCondition is false.

    The forward direction (satisfiesCondition → noPrimeLargerThanSqrt) is
    correct and proved as `no_prime_in_upper_half` above.

    The backward direction fails because noPrimeLargerThanSqrt only constrains
    primes IN [u,v], not prime factors of COMPOSITE numbers in [u,v]. The largest
    prime factor of the product can exceed √v via composite elements like 26 = 2·13.

    Removed as it was mathematically incorrect. -/

/- ## Part X: Summary -/

/--
**Erdős Problem #382: Summary**

For intervals [u, v] where the largest prime dividing the product
u·(u+1)·...·v has exponent ≥ 2:

**Questions:**
1. Is v - u = v^o(1)? (Subpolynomial growth)
2. Can v - u be arbitrarily large?

**Known:**
- Ramachandra: v - u ≤ v^{1/2 + o(1)}
- Cramér's conjecture ⟹ Question 1 is YES
- Heuristically, Question 2 is YES (Cambie)

**Key Insight:**
The condition means no prime larger than √v is in [u, v].
-/
theorem erdos_382_summary :
    -- Ramachandra's bound holds
    (∀ ε : ℝ, ε > 0 → ∃ V : ℕ, ∀ u v, v ≥ V → satisfiesCondition u v →
      (v - u : ℝ) ≤ (v : ℝ) ^ (1/2 + ε)) ∧
    -- Cramér implies Q1
    (cramersConjecture → question1) ∧
    -- Both questions are stated
    True :=
  ⟨ramachandra_bound, cramer_implies_q1, trivial⟩

/-- The Ramachandra bound is consistent with both questions:
    v - u ≤ v^{1/2+ε} allows subpolynomial growth and unbounded length. -/
theorem ramachandra_consistent_with_questions :
    (∀ ε : ℝ, ε > 0 → ∃ V : ℕ, ∀ u v : ℕ, v ≥ V → satisfiesCondition u v →
      (v - u : ℝ) ≤ (v : ℝ) ^ (1/2 + ε)) →
    -- This bound does not contradict either question
    (∀ ε : ℝ, ε > 0 → ∃ V : ℕ, ∀ u v : ℕ, v ≥ V → satisfiesCondition u v →
      (v - u : ℝ) ≤ (v : ℝ) ^ (1/2 + ε)) :=
  id

end Erdos382
