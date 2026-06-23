/-
Erdos Problem #951: Beurling Prime Numbers

Source: https://erdosproblems.com/951
Status: OPEN

Statement:
Let 1 < a_1 < a_2 < ... be a sequence of real numbers such that for every
distinct pair of non-negative finitely supported integer tuples (k_i), (l_j):

  |prod_i a_i^{k_i} - prod_j a_j^{l_j}| >= 1

Question: Is it true that #{a_i <= x} <= pi(x)?

Such sequences are called Beurling prime numbers or generalized primes.
The condition ensures that products of these "primes" are well-separated,
mimicking a key property of ordinary primes.

Historical Context:
- Erdos reports this question was posed during his lecture at Queens College
  by a member of the audience (perhaps S. Shapiro)
- Beurling introduced generalized primes in 1937

Related Result (Beurlings Conjecture):
If the count of "integers" (products prod a_i^{k_i}) in [1,x] equals x + o(log x),
then the a_i must be the actual primes.

References:
- Beurling, A. (1937): "Analyse de la loi asymptotique de la distribution
  des nombres premiers generalises"
- Diamond, H. G. (1977): "A set of generalized numbers showing Beurlings theorem to be sharp"
-/

import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.Factorization.Basic

open Nat BigOperators Finset Real

namespace Erdos951

/-- A sequence (a_i) has well-separated products if for any two distinct
    products, their difference is at least 1. -/
def WellSeparatedProducts (a : ℕ → ℝ) : Prop :=
  ∀ k ℓ : ℕ →₀ ℕ, k ≠ ℓ →
    |∏ i ∈ k.support, a i ^ (k i) - ∏ j ∈ ℓ.support, a j ^ (ℓ j)| ≥ 1

/-- A Beurling prime sequence: strictly increasing, all > 1, well-separated products. -/
structure BeurlingPrimes where
  a : ℕ → ℝ
  strictly_increasing : ∀ n m, n < m → a n < a m
  all_gt_one : ∀ n, a n > 1
  well_separated : WellSeparatedProducts a

/-- Beurling prime counting function: #{n : a_n <= x}.
    Since the sequence is strictly increasing with all terms > 1,
    this set is finite for any x. We use Set.ncard. -/
noncomputable def beurlingPi (a : ℕ → ℝ) (x : ℝ) : ℕ :=
  Set.ncard {n : ℕ | a n ≤ x}

/-- Standard prime counting function: π(x) = number of primes ≤ x.
    Nat.primeCounting n counts primes ≤ n (unfolding: count Prime (n+1) = #{p < n+1 | Prime p}). -/
noncomputable def primePi (x : ℝ) : ℕ := Nat.primeCounting (Nat.floor x)

/-- Consecutive Beurling primes differ by at least 1.
    This follows from well-separation applied to single-element Finsupp representations. -/
theorem beurling_consec_gap (bp : BeurlingPrimes) (n : ℕ) :
    bp.a (n + 1) ≥ bp.a n + 1 := by
  have hne : Finsupp.single (n + 1) (1 : ℕ) ≠ Finsupp.single n 1 :=
    fun h => absurd (Finsupp.single_left_injective (by omega) h) (by omega)
  have hsep := bp.well_separated _ _ hne
  have hs1 : (Finsupp.single (n + 1) (1 : ℕ)).support = {n + 1} :=
    Finsupp.support_single_ne_zero _ (by omega)
  have hs2 : (Finsupp.single n (1 : ℕ)).support = {n} :=
    Finsupp.support_single_ne_zero _ (by omega)
  rw [hs1, hs2, Finset.prod_singleton, Finset.prod_singleton] at hsep
  simp only [Finsupp.single_eq_same] at hsep
  rw [abs_of_pos (by linarith [bp.strictly_increasing n (n + 1) (by omega)])] at hsep
  linarith

/-- Beurling primes grow at least linearly: aₙ ≥ a₀ + n.
    Proved by induction using `beurling_consec_gap`. -/
theorem beurling_linear_growth (bp : BeurlingPrimes) (n : ℕ) :
    bp.a n ≥ bp.a 0 + n := by
  induction n with
  | zero => simp
  | succ k ih => push_cast at *; linarith [beurling_consec_gap bp k]

/-- The first element of a Beurling prime sequence is at least 2.

    This is derivable from `WellSeparatedProducts` (no extra hypothesis needed):
    take `k = 0` (the zero Finsupp, with empty support and product `1`) and
    `ℓ = Finsupp.single 0 1` (support `{0}`, product `bp.a 0`). Well-separation
    forces `|1 - bp.a 0| ≥ 1`, and combined with `bp.a 0 > 1` this gives
    `bp.a 0 ≥ 2`. -/
theorem beurling_a_zero_ge_two (bp : BeurlingPrimes) : 2 ≤ bp.a 0 := by
  have hne : (0 : ℕ →₀ ℕ) ≠ Finsupp.single 0 1 := fun h => by
    have h0 := DFunLike.congr_fun h 0
    simp [Finsupp.single_eq_same] at h0
  have hsep := bp.well_separated 0 (Finsupp.single 0 1) hne
  have hs2 : (Finsupp.single 0 (1 : ℕ)).support = {0} :=
    Finsupp.support_single_ne_zero _ one_ne_zero
  rw [Finsupp.support_zero, hs2, Finset.prod_empty, Finset.prod_singleton,
      Finsupp.single_eq_same, pow_one] at hsep
  have h_a0 := bp.all_gt_one 0
  rw [abs_of_neg (by linarith : (1 : ℝ) - bp.a 0 < 0)] at hsep
  linarith

/-- Sharpened linear growth: `aₙ ≥ n + 2`. Combines `beurling_linear_growth`
    (`aₙ ≥ a₀ + n`) with `beurling_a_zero_ge_two` (`a₀ ≥ 2`). -/
theorem beurling_linear_growth_strong (bp : BeurlingPrimes) (n : ℕ) :
    bp.a n ≥ (n : ℝ) + 2 := by
  have h1 := beurling_linear_growth bp n
  have h2 := beurling_a_zero_ge_two bp
  linarith

/-- The counting set {n | a n <= x} is finite for Beurling prime sequences.
    Since a is strictly increasing with all a_n > 1, only finitely many
    indices satisfy a_n <= x. -/
theorem beurlingPi_finite (bp : BeurlingPrimes) (x : ℝ) :
    Set.Finite {n : ℕ | bp.a n ≤ x} := by
  apply Set.Finite.subset (Set.finite_Iic ⌊x⌋₊)
  intro n hn
  simp only [Set.mem_setOf_eq] at hn
  simp only [Set.mem_Iic]
  have : (n : ℝ) < x := by
    linarith [beurling_linear_growth bp n, bp.all_gt_one 0]
  exact Nat.le_floor this.le

/-- **Trivial upper bound** (weaker than Erdős 951): for any Beurling prime
    sequence, `π_a(x) ≤ ⌊x⌋₊`. This follows from the linear growth `aₙ ≥ a₀ + n > n + 1`,
    so the indices satisfying `aₙ ≤ x` are contained in `{0, 1, …, ⌊x⌋₊ - 1}`.

    The Erdős 951 conjecture asserts the much stronger bound `π_a(x) ≤ π(x)`,
    which would refine `⌊x⌋₊` (linear in x) down to `π(x)` (sublinear `~ x/log x`).
    The gap between these bounds is exactly what makes the conjecture nontrivial. -/
theorem beurlingPi_le_floor (bp : BeurlingPrimes) (x : ℝ) :
    beurlingPi bp.a x ≤ ⌊x⌋₊ := by
  unfold beurlingPi
  have hsub : {n : ℕ | bp.a n ≤ x} ⊆ ↑(Finset.range ⌊x⌋₊) := by
    intro n hn
    simp only [Set.mem_setOf_eq] at hn
    simp only [Finset.coe_range, Set.mem_Iio]
    have h1 := beurling_linear_growth bp n
    have h2 := bp.all_gt_one 0
    have h3 : ((n + 1 : ℕ) : ℝ) ≤ x := by push_cast; linarith
    exact Nat.lt_of_succ_le (Nat.le_floor h3)
  calc Set.ncard {n : ℕ | bp.a n ≤ x}
      ≤ Set.ncard (↑(Finset.range ⌊x⌋₊) : Set ℕ) :=
        Set.ncard_le_ncard hsub (Finset.range _).finite_toSet
    _ = ⌊x⌋₊ := by rw [Set.ncard_coe_finset, Finset.card_range]

/-- **Sharpened trivial upper bound**: `π_a(x) ≤ ⌊x⌋₊ - 1` (natural truncated
    subtraction). Saves one over `beurlingPi_le_floor` by exploiting the
    well-separation-derived strengthening `aₙ ≥ n + 2`.

    Holds unconditionally: when `⌊x⌋₊ ≤ 1` (i.e. `x < 2`) the RHS truncates
    to `0` and the bound holds because every Beurling prime is `≥ 2 > x`.

    This is still far weaker than the Erdős 951 conjecture `π_a(x) ≤ π(x)`
    (`π(x) ~ x/log x` sublinear vs. `⌊x⌋₊ - 1` linear). The conjecture's
    content is the `log x` improvement; this lemma is a one-step refinement
    within the trivial-bound regime. -/
theorem beurlingPi_le_floor_pred (bp : BeurlingPrimes) (x : ℝ) :
    beurlingPi bp.a x ≤ ⌊x⌋₊ - 1 := by
  unfold beurlingPi
  have hsub : {n : ℕ | bp.a n ≤ x} ⊆ ↑(Finset.range (⌊x⌋₊ - 1)) := by
    intro n hn
    simp only [Set.mem_setOf_eq] at hn
    simp only [Finset.coe_range, Set.mem_Iio]
    have h1 := beurling_linear_growth_strong bp n
    have h3 : ((n + 2 : ℕ) : ℝ) ≤ x := by push_cast; linarith
    have h4 : n + 2 ≤ ⌊x⌋₊ := Nat.le_floor h3
    omega
  calc Set.ncard {n : ℕ | bp.a n ≤ x}
      ≤ Set.ncard (↑(Finset.range (⌊x⌋₊ - 1)) : Set ℕ) :=
        Set.ncard_le_ncard hsub (Finset.range _).finite_toSet
    _ = ⌊x⌋₊ - 1 := by rw [Set.ncard_coe_finset, Finset.card_range]

/-- The nth prime as a real number. -/
noncomputable def primeSeq (n : ℕ) : ℝ := Nat.nth Nat.Prime n

/-- The nth element of primeSeq is prime. -/
theorem primeSeq_isPrime (n : ℕ) : Nat.Prime (Nat.nth Nat.Prime n) :=
  Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n

/-- Prime sequence is strictly increasing.
    Proved via Nat.nth_strictMono for the infinite set of primes. -/
theorem primeSeq_strictly_increasing : ∀ n m, n < m → primeSeq n < primeSeq m := by
  intro n m h
  simp only [primeSeq]
  exact_mod_cast Nat.nth_strictMono Nat.infinite_setOf_prime h

/-- All primes are > 1.
    Proved from Nat.Prime.one_lt applied to nth prime. -/
theorem primeSeq_gt_one : ∀ n, primeSeq n > 1 := by
  intro n
  simp only [primeSeq]
  exact_mod_cast (primeSeq_isPrime n).one_lt

/-- The factorization of a product of indexed prime powers, evaluated at the nth prime,
    gives the exponent of that index. This is the key step for unique factorization:
    distinct Finsupp exponent tuples yield distinct natural number products. -/
private lemma factorization_prod_at (S : Finset ℕ) (e : ℕ → ℕ) (n : ℕ) :
    (∏ i ∈ S, (Nat.nth Nat.Prime i) ^ (e i)).factorization (Nat.nth Nat.Prime n) =
      if n ∈ S then e n else 0 := by
  induction S using Finset.induction with
  | empty => simp [Nat.factorization_one]
  | insert j s hjs ih =>
    have ha : (Nat.nth Nat.Prime j) ^ (e j) ≠ 0 :=
      Nat.pos_iff_ne_zero.mp
        (pow_pos (Nat.nth_mem_of_infinite Nat.infinite_setOf_prime j).pos _)
    have hb : (∏ i ∈ s, (Nat.nth Nat.Prime i) ^ (e i)) ≠ 0 :=
      Nat.pos_iff_ne_zero.mp (Finset.prod_pos fun i _ =>
        pow_pos (Nat.nth_mem_of_infinite Nat.infinite_setOf_prime i).pos _)
    rw [Finset.prod_insert hjs, Nat.factorization_mul ha hb, Finsupp.add_apply, ih,
        Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
        (Nat.nth_mem_of_infinite Nat.infinite_setOf_prime j).factorization,
        Finsupp.single_apply]
    have h_inj := (Nat.nth_strictMono Nat.infinite_setOf_prime).injective
    by_cases hn : j = n
    · subst hn; simp [hjs]
    · simp [show Nat.nth Nat.Prime j ≠ Nat.nth Nat.Prime n from fun h => hn (h_inj h),
            Ne.symm hn]

/-- The ordinary primes have well-separated products by the
    Fundamental Theorem of Arithmetic: distinct exponent tuples yield
    distinct natural number products, and distinct naturals differ by ≥ 1. -/
theorem primeSeq_well_separated : WellSeparatedProducts primeSeq := by
  intro k ℓ hne
  simp only [primeSeq]
  -- Define the products as natural numbers
  set Pk := ∏ i ∈ k.support, (Nat.nth Nat.Prime i) ^ (k i) with hPk_def
  set Pℓ := ∏ j ∈ ℓ.support, (Nat.nth Nat.Prime j) ^ (ℓ j) with hPℓ_def
  -- Step 1: Products are distinct (by unique prime factorization)
  have hne_prod : Pk ≠ Pℓ := by
    intro heq
    apply hne; ext n
    have h := congr_arg (fun m => Nat.factorization m (Nat.nth Nat.Prime n)) heq
    simp only [hPk_def, hPℓ_def, factorization_prod_at] at h
    split_ifs at h with hk hℓ hℓ <;> simp_all
  -- Step 2: The real-valued products equal the natural products cast to ℝ
  have h_cast_k :
      ∏ i ∈ k.support, (↑(Nat.nth Nat.Prime i) : ℝ) ^ (k i) = (↑Pk : ℝ) := by
    norm_cast
  have h_cast_ℓ :
      ∏ j ∈ ℓ.support, (↑(Nat.nth Nat.Prime j) : ℝ) ^ (ℓ j) = (↑Pℓ : ℝ) := by
    norm_cast
  rw [h_cast_k, h_cast_ℓ]
  -- Step 3: Distinct natural numbers cast to ℝ differ by at least 1
  rcases hne_prod.lt_or_gt with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr (Nat.cast_le.mpr h.le))]
    linarith [show (↑Pk : ℝ) + 1 ≤ ↑Pℓ from by exact_mod_cast Nat.succ_le_of_lt h]
  · rw [abs_of_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr h.le))]
    linarith [show (↑Pℓ : ℝ) + 1 ≤ ↑Pk from by exact_mod_cast Nat.succ_le_of_lt h]

/-- The ordinary primes form a Beurling prime sequence. -/
noncomputable def actualPrimes : BeurlingPrimes where
  a := primeSeq
  strictly_increasing := primeSeq_strictly_increasing
  all_gt_one := primeSeq_gt_one
  well_separated := primeSeq_well_separated

/-- The 0th prime is 2 (cast to ℝ). Proved by `Nat.nth_count` applied to
    `Nat.prime_two`, using that `Nat.count Nat.Prime 2 = 0` (no primes
    are strictly less than 2). -/
theorem primeSeq_zero : primeSeq 0 = 2 := by
  show (Nat.nth Nat.Prime 0 : ℝ) = 2
  have hcount : Nat.count Nat.Prime 2 = 0 := by decide
  have hnth : Nat.nth Nat.Prime 0 = 2 := by
    rw [← hcount]; exact Nat.nth_count Nat.prime_two
  rw [hnth]; norm_num

/-- **Tightness of `beurling_a_zero_ge_two`**: the lower bound `2 ≤ a₀`
    is best possible — the actual primes witness equality `a₀ = 2`.

    Consequence: any attempt to derive `a₀ ≥ 3` (or any stronger absolute
    constant) from the `BeurlingPrimes` axioms alone must fail.
    Strengthening requires additional hypotheses (e.g. excluding the
    actual primes, or restricting to integer sequences with `a₀ ≠ 2`). -/
theorem beurling_a_zero_lower_bound_tight :
    ∃ bp : BeurlingPrimes, bp.a 0 = 2 :=
  ⟨actualPrimes, primeSeq_zero⟩

/-- For the actual primes, beurlingPi equals primePi.
    Uses the Galois connection: n < count Prime m ↔ nth Prime n < m
    to show {n | nth Prime n ≤ ⌊x⌋₊} = Finset.range(count Prime (⌊x⌋₊ + 1)). -/
theorem actualPrimes_counting : ∀ x : ℝ, beurlingPi primeSeq x = primePi x := by
  intro x
  simp only [beurlingPi, primePi, primeSeq]
  -- Unfold primeCounting to expose count Prime (⌊x⌋₊ + 1)
  unfold Nat.primeCounting Nat.primeCounting'
  -- Goal: ncard {n | (↑(nth Prime n) : ℝ) ≤ x} = count Prime (⌊x⌋₊ + 1)
  -- Show set = ↑(Finset.range (count Prime (⌊x⌋₊ + 1)))
  have hset : {n : ℕ | (↑(Nat.nth Nat.Prime n) : ℝ) ≤ x} =
      ↑(Finset.range (Nat.count Nat.Prime (⌊x⌋₊ + 1))) := by
    ext n; simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_range]
    constructor
    · -- (↑(nth Prime n) : ℝ) ≤ x → n < count Prime (⌊x⌋₊ + 1)
      intro hle
      have h1 : Nat.nth Nat.Prime n ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hle)
      exact (Nat.lt_nth_iff_count_lt Nat.infinite_setOf_prime).mpr
        (Nat.lt_succ_of_le h1)
    · -- n < count Prime (⌊x⌋₊ + 1) → (↑(nth Prime n) : ℝ) ≤ x
      intro hlt
      have h1 : Nat.nth Nat.Prime n < ⌊x⌋₊ + 1 :=
        (Nat.lt_nth_iff_count_lt Nat.infinite_setOf_prime).mp hlt
      have h2 : Nat.nth Nat.Prime n ≤ ⌊x⌋₊ := Nat.lt_succ_iff.mp h1
      have hx_nn : 0 ≤ x := by
        by_contra hlt_x; push_neg at hlt_x
        have hfloor : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.mpr (show x < 1 by linarith)
        have hge2 : 2 ≤ ⌊x⌋₊ := le_trans
          (Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n).two_le h2
        omega
      exact le_trans (Nat.cast_le.mpr h2) (Nat.floor_le hx_nn)
  rw [hset, Set.ncard_coe_finset, Finset.card_range]

-- NOTE: A previous version claimed powers of 2 form a Beurling prime sequence.
-- This is FALSE: the well-separation property fails because products can collide.
-- Counterexample: k = {0 ↦ 2} gives (2^1)^2 = 4, ℓ = {1 ↦ 1} gives (2^2)^1 = 4.
-- These are distinct tuples with equal products, violating |prod - prod| ≥ 1.
-- This is formalized as `powers_of_two_not_well_separated` below.

/-- **Counter-example**: the geometric sequence `aₙ = 2^(n+1)` (i.e.
    `a₀ = 2, a₁ = 4, a₂ = 8, …`) does NOT satisfy `WellSeparatedProducts`.

    The exponent tuples `k = Finsupp.single 0 2` (product `(a₀)² = 4`)
    and `ℓ = Finsupp.single 1 1` (product `(a₁)¹ = 4`) are distinct
    Finsupps but yield identical products, so `|4 - 4| = 0 < 1`.

    This formalizes the comment immediately above. The takeaway:
    `BeurlingPrimes` is not just "any geometric-style sequence" — the
    well-separation requirement is genuinely restrictive. -/
theorem powers_of_two_not_well_separated :
    ¬ WellSeparatedProducts (fun n => (2 : ℝ) ^ (n + 1)) := by
  intro h
  have hne : (Finsupp.single 0 2 : ℕ →₀ ℕ) ≠ Finsupp.single 1 1 := by
    intro heq
    have h0 := DFunLike.congr_fun heq 0
    simp at h0
  have hsep := h (Finsupp.single 0 2) (Finsupp.single 1 1) hne
  have hk_supp : (Finsupp.single 0 (2 : ℕ)).support = {0} :=
    Finsupp.support_single_ne_zero _ (by decide : (2 : ℕ) ≠ 0)
  have hℓ_supp : (Finsupp.single 1 (1 : ℕ)).support = {1} :=
    Finsupp.support_single_ne_zero _ one_ne_zero
  rw [hk_supp, hℓ_supp, Finset.prod_singleton, Finset.prod_singleton] at hsep
  simp only [Finsupp.single_eq_same] at hsep
  norm_num at hsep

/-- Well-separated products implies distinct products. -/
theorem separation_implies_distinct (a : ℕ → ℝ) (h : WellSeparatedProducts a) :
    ∀ k ℓ : ℕ →₀ ℕ, k ≠ ℓ →
      ∏ i ∈ k.support, a i ^ (k i) ≠ ∏ j ∈ ℓ.support, a j ^ (ℓ j) := by
  intro k ℓ hne
  have := h k ℓ hne
  intro heq
  simp only [heq, sub_self, abs_zero] at this
  linarith

/-- A Beurling integer is a product of Beurling primes. -/
def IsBeurlingInteger (a : ℕ → ℝ) (x : ℝ) : Prop :=
  ∃ k : ℕ →₀ ℕ, x = ∏ i ∈ k.support, a i ^ (k i)

/-- Beurling integer counting function: number of Beurling integers in [1,x]. -/
noncomputable def beurlingN (a : ℕ → ℝ) (x : ℝ) : ℕ :=
  Set.ncard {y : ℝ | IsBeurlingInteger a y ∧ 1 ≤ y ∧ y ≤ x}

/-- Beurlings conjecture: if N_a(x) = x + o(log x), then a_i must be the primes.
    This is an open conjecture; we state it as a Prop without asserting truth. -/
def beurlings_conjecture : Prop :=
    ∀ bp : BeurlingPrimes,
      (∀ ε > 0, ∃ X : ℝ, ∀ x ≥ X, |beurlingN bp.a x - x| ≤ ε * Real.log x) →
      bp.a = primeSeq

/-- Erdos #951 Conjecture: For any Beurling prime sequence,
    #{a_i <= x} <= pi(x) for all x > 0. -/
def erdos951_conjecture : Prop :=
  ∀ bp : BeurlingPrimes, ∀ x : ℝ, x > 0 → beurlingPi bp.a x ≤ primePi x

-- Note: erdos951_conjecture is OPEN. We do NOT axiomatize it.

/-- The actual primes achieve equality in the conjecture bound. -/
theorem erdos_951_primes_equality :
    ∀ x : ℝ, beurlingPi primeSeq x = primePi x :=
  actualPrimes_counting

end Erdos951
