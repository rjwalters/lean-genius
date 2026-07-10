/-
  Erdős Problem #490: Distinct Products of Two Sets

  Source: https://erdosproblems.com/490
  Status: SOLVED (Szemerédi 1976)

  Statement:
  Let A, B ⊆ {1,...,N} be such that all products ab with a ∈ A, b ∈ B are distinct.
  Is it true that |A||B| ≪ N²/log N?

  Answer: YES - Szemerédi (1976) proved this bound is correct.

  Best Possible Example:
  A = [1, N/2] ∩ ℕ and B = {p : N/2 < p ≤ N, p prime}
  This achieves |A||B| ~ N² / (2 log N).

  Open Question (Erdős 1972):
  Does lim_{N→∞} max |A||B| log N / N² exist? If so, what is its value?
  (It must be ≥ 1 by van Doorn's observation.)

  References:
  - [Sz76] Szemerédi, "On a problem of P. Erdős", J. Number Theory (1976)
  - [Er72] Erdős, "Extremal problems in number theory",
    Proceedings of the 1972 Number Theory Conference
  - See also Problems #425 and #896
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Proofs.Erdos490Chebyshev

open Finset Real
open scoped Classical

namespace Erdos490

/-
## Part I: Basic Definitions
-/

/-- A set A ⊆ {1,...,N}. -/
def IsSubsetUpTo (A : Finset ℕ) (N : ℕ) : Prop :=
  ∀ a ∈ A, 1 ≤ a ∧ a ≤ N

/-- The product set A·B = {ab : a ∈ A, b ∈ B}. -/
def productSet (A B : Finset ℕ) : Finset ℕ :=
  A.biUnion (fun a => B.image (fun b => a * b))

/-- All products ab are distinct. -/
def HasDistinctProducts (A B : Finset ℕ) : Prop :=
  (productSet A B).card = A.card * B.card

/-- Alternative definition: the product map is injective. -/
def ProductMapInjective (A B : Finset ℕ) : Prop :=
  ∀ a₁ a₂ b₁ b₂, a₁ ∈ A → a₂ ∈ A → b₁ ∈ B → b₂ ∈ B →
    a₁ * b₁ = a₂ * b₂ → (a₁ = a₂ ∧ b₁ = b₂)

/-- The product set `A·B` is exactly the image of the product map `(a, b) ↦ a·b`
on `A ×ˢ B`. -/
theorem productSet_eq_image (A B : Finset ℕ) :
    productSet A B = (A ×ˢ B).image (fun p : ℕ × ℕ => p.1 * p.2) := by
  ext n
  simp only [productSet, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩
  · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩; exact ⟨a, ha, b, hb, rfl⟩

/-- **`HasDistinctProducts` is injectivity of the product map.**  The cardinality
condition `|A·B| = |A||B|` holds iff `(a, b) ↦ a·b` is injective on `A ×ˢ B`
(via `Finset.card_image_iff`). -/
theorem hasDistinctProducts_iff_injOn (A B : Finset ℕ) :
    HasDistinctProducts A B ↔ Set.InjOn (fun p : ℕ × ℕ => p.1 * p.2) ↑(A ×ˢ B) := by
  rw [HasDistinctProducts, productSet_eq_image, ← Finset.card_product A B,
    Finset.card_image_iff]

/-- **The two distinctness notions agree.**  `ProductMapInjective` (the elementwise
quantified form) is equivalent to `HasDistinctProducts` (the cardinality form). -/
theorem productMapInjective_iff_hasDistinctProducts (A B : Finset ℕ) :
    ProductMapInjective A B ↔ HasDistinctProducts A B := by
  rw [hasDistinctProducts_iff_injOn]
  constructor
  · intro h
    rintro ⟨a₁, b₁⟩ hx ⟨a₂, b₂⟩ hy hfxy
    rw [Finset.mem_coe, Finset.mem_product] at hx hy
    have := h a₁ a₂ b₁ b₂ hx.1 hy.1 hx.2 hy.2 hfxy
    rw [Prod.mk.injEq]; exact this
  · intro h a₁ a₂ b₁ b₂ ha₁ ha₂ hb₁ hb₂ heq
    have hx : ((a₁, b₁) : ℕ × ℕ) ∈ A ×ˢ B := Finset.mem_product.mpr ⟨ha₁, hb₁⟩
    have hy : ((a₂, b₂) : ℕ × ℕ) ∈ A ×ˢ B := Finset.mem_product.mpr ⟨ha₂, hb₂⟩
    have := h (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) heq
    rw [Prod.mk.injEq] at this; exact this

/-- **The product set is symmetric**: `A·B = B·A` as finsets.  Commutativity of
multiplication (`a·b = b·a`) means the two product sets contain exactly the same
elements, so they are literally equal (not merely equinumerous). -/
theorem productSet_comm (A B : Finset ℕ) :
    productSet A B = productSet B A := by
  ext n
  simp only [productSet, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨b, hb, a, ha, by rw [mul_comm]⟩
  · rintro ⟨b, hb, a, ha, rfl⟩; exact ⟨a, ha, b, hb, by rw [mul_comm]⟩

/-- **Distinct products is symmetric in the two factors**: `HasDistinctProducts A B ↔
HasDistinctProducts B A`.  Since `A·B = B·A` (`productSet_comm`) and `|A||B| = |B||A|`,
the cardinality condition `|A·B| = |A||B|` is unchanged by swapping `A` and `B`.  This
records that the whole distinctness/energy theory is symmetric — one need only study
`|A| ≤ |B|`. -/
theorem hasDistinctProducts_comm (A B : Finset ℕ) :
    HasDistinctProducts A B ↔ HasDistinctProducts B A := by
  rw [HasDistinctProducts, HasDistinctProducts, productSet_comm A B,
    Nat.mul_comm A.card B.card]

/-
## Part II: The Erdős Question
-/

/-- The maximum of |A||B| over all pairs with distinct products. -/
noncomputable def maxProductSize (N : ℕ) : ℕ :=
  Nat.find (max_exists N)
where
  max_exists : ∀ N, ∃ k, ∀ A B : Finset ℕ,
    IsSubsetUpTo A N → IsSubsetUpTo B N →
    HasDistinctProducts A B → A.card * B.card ≤ k := by
    intro N
    use N^2  -- trivial bound
    intro A B hA hB _
    have hAcard : A.card ≤ N := by
      have hsub : A ⊆ Finset.Icc 1 N :=
        fun a ha => Finset.mem_Icc.mpr (hA a ha)
      calc A.card ≤ (Finset.Icc 1 N).card := Finset.card_le_card hsub
        _ = N + 1 - 1 := by rw [Nat.card_Icc]
        _ = N := by omega
    have hBcard : B.card ≤ N := by
      have hsub : B ⊆ Finset.Icc 1 N :=
        fun b hb => Finset.mem_Icc.mpr (hB b hb)
      calc B.card ≤ (Finset.Icc 1 N).card := Finset.card_le_card hsub
        _ = N + 1 - 1 := by rw [Nat.card_Icc]
        _ = N := by omega
    calc A.card * B.card ≤ N * N := Nat.mul_le_mul hAcard hBcard
      _ = N ^ 2 := by ring

/-- Erdős's Question: Is |A||B| ≪ N²/log N? -/
def ErdosQuestion490 : Prop :=
  ∃ C : ℝ, C > 0 ∧
    ∀ N : ℕ, N ≥ 2 →
      ∀ A B : Finset ℕ, IsSubsetUpTo A N → IsSubsetUpTo B N →
        HasDistinctProducts A B →
        (A.card * B.card : ℝ) ≤ C * N^2 / Real.log N

/-
## Part III: Szemerédi's Theorem (1976)
-/

/-- **Szemerédi's Theorem (1976):**
    If A, B ⊆ {1,...,N} have distinct products, then |A||B| ≪ N²/log N. -/
axiom szemeredi_theorem :
  ∃ C : ℝ, C > 0 ∧
    ∀ N : ℕ, N ≥ 2 →
      ∀ A B : Finset ℕ, IsSubsetUpTo A N → IsSubsetUpTo B N →
        HasDistinctProducts A B →
        (A.card * B.card : ℝ) ≤ C * N^2 / Real.log N

/-- The answer to Erdős Problem #490 is YES. -/
theorem erdos_490_answer : ErdosQuestion490 := szemeredi_theorem

/-- **The extremal function `maxProductSize` is monotone.**
Enlarging the ambient range `{1,…,N} → {1,…,N+1}` can only add admissible pairs:
any `A, B ⊆ {1,…,N}` with distinct products are still `⊆ {1,…,N+1}` with the same
(distinct) products, so the supremum `maxProductSize N` of `|A|·|B|` never decreases.
This is the structural fact behind the growth `maxProductSize N = Θ(N²/log N)`: the
supply of distinct-product pairs is non-decreasing in `N`. Proved by `Nat.find_mono`,
since a bound valid for all `{1,…,N+1}`-pairs is a fortiori valid for all
`{1,…,N}`-pairs. -/
theorem maxProductSize_monotone : Monotone maxProductSize := by
  apply monotone_nat_of_le_succ
  intro N
  unfold maxProductSize
  apply Nat.find_mono
  intro k hk A B hA hB hAB
  exact hk A B
    (fun a ha => ⟨(hA a ha).1, (hA a ha).2.trans (Nat.le_succ N)⟩)
    (fun b hb => ⟨(hB b hb).1, (hB b hb).2.trans (Nat.le_succ N)⟩) hAB

/-
## Part IV: The Optimal Example
-/

/-- The first half of [1, N]: A = [1, N/2]. -/
def optimalA (N : ℕ) : Finset ℕ :=
  Finset.filter (fun n => 1 ≤ n ∧ n ≤ N / 2) (Finset.range (N + 1))

/-- The primes in the second half: B = {p : N/2 < p ≤ N, p prime}. -/
def optimalB (N : ℕ) : Finset ℕ :=
  Finset.filter (fun p => Nat.Prime p ∧ N / 2 < p ∧ p ≤ N) (Finset.range (N + 1))

/- The optimal example has distinct products.  **Proved** (0-axiom) as
`optimal_has_distinct_products` below, once the elementwise distinctness lemma
`optimal_works_because_primes` is available; placed there to respect dependency order. -/

/-- The first half is exactly `Icc 1 (N/2)`, so it has `⌊N/2⌋` elements. -/
theorem optimalA_card (N : ℕ) : (optimalA N).card = N / 2 := by
  have hset : optimalA N = Finset.Icc 1 (N / 2) := by
    ext n
    simp only [optimalA, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨_, h1, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      -- `n ≤ N/2 ≤ N < N+1`, so the `range (N+1)` membership is automatic.
      exact ⟨by omega, h1, h2⟩
  rw [hset, Nat.card_Icc]; omega

/- The Chebyshev θ-gap lower bound `θ(N) − θ(N/2) ≥ c·N` was formerly an axiom here.
   It is now a **theorem** (`chebyshev_theta_upper_half_lower_bound`, 0 axioms), proved
   below immediately after `theta_gap_eq_sum_optimalB`, by combining the elementary
   central-binomial estimate `Erdos490Cheb.theta_gap_lower_bound` with the analytic-tail
   lemma `Erdos490Cheb.erdos490_analytic_tail` (`log n`, `√(2n)·log(2n) = o(n)`), plus a
   Bertrand-based positive lower bound `θ(N) − θ(N/2) ≥ log 2` for the finitely many small
   `N`.  This eliminates the last analytic axiom of the *lower*-bound half of #490 (only
   `szemeredi_theorem`, the deep `N²/log N` *upper* bound, remains axiomatized). -/

/-- **θ-gap as a sum over the optimal `B` (0-axiom).** The primes counted by
`Chebyshev.theta N − Chebyshev.theta (N/2)` are exactly the primes in `(N/2, N]`, i.e. the
elements of `optimalB N`, so the θ-gap equals `∑_{p ∈ optimalB N} log p`.  This is the
combinatorial heart of the `θ → π` bridge: it re-expresses Mathlib's Chebyshev θ-difference
as a sum ranging over our optimal example. -/
theorem theta_gap_eq_sum_optimalB (N : ℕ) :
    Chebyshev.theta (N : ℝ) - Chebyshev.theta ((N / 2 : ℕ) : ℝ)
      = ∑ p ∈ optimalB N, Real.log (p : ℝ) := by
  -- `θ ↑m = ∑_{p ∈ Ioc 0 m, p prime} log p`, using `⌊↑m⌋₊ = m`.
  have e1 : Chebyshev.theta (N : ℝ)
      = ∑ p ∈ {p ∈ Finset.Ioc 0 N | p.Prime}, Real.log (p : ℝ) := by
    simp only [Chebyshev.theta, Nat.floor_natCast]
  have e2 : Chebyshev.theta ((N / 2 : ℕ) : ℝ)
      = ∑ p ∈ {p ∈ Finset.Ioc 0 (N / 2) | p.Prime}, Real.log (p : ℝ) := by
    simp only [Chebyshev.theta, Nat.floor_natCast]
  -- The primes `≤ N/2` are a subset of the primes `≤ N`.
  have hsub : {p ∈ Finset.Ioc 0 (N / 2) | p.Prime} ⊆ {p ∈ Finset.Ioc 0 N | p.Prime} :=
    Finset.filter_subset_filter _ (Finset.Ioc_subset_Ioc_right (Nat.div_le_self N 2))
  -- The set difference is exactly the primes in `(N/2, N]`, i.e. `optimalB N`.
  have hset : {p ∈ Finset.Ioc 0 N | p.Prime} \ {p ∈ Finset.Ioc 0 (N / 2) | p.Prime}
      = optimalB N := by
    ext p
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Ioc, optimalB,
      Finset.mem_range]
    constructor
    · rintro ⟨⟨⟨hp0, hpN⟩, hpr⟩, hnot⟩
      refine ⟨by omega, hpr, ?_, hpN⟩
      by_contra h; push_neg at h
      exact hnot ⟨⟨hp0, by omega⟩, hpr⟩
    · rintro ⟨_, hpr, hlt, hle⟩
      exact ⟨⟨⟨hpr.pos, hle⟩, hpr⟩, by rintro ⟨⟨_, h2⟩, _⟩; omega⟩
  rw [e1, e2, ← hset, Finset.sum_sdiff_eq_sub hsub]

/-- **Qualitative lower bound (0-axiom, via Bertrand's postulate).** For every `N ≥ 2`
the half-open interval `(N/2, N]` contains a prime, so the optimal `B` is nonempty.
Proof: apply Bertrand's postulate `Nat.exists_prime_lt_and_le_two_mul` at `m = ⌊N/2⌋`
(nonzero since `N ≥ 2`) to get a prime `p` with `N/2 < p ≤ 2·⌊N/2⌋ ≤ N`. -/
theorem optimalB_nonempty {N : ℕ} (hN : 2 ≤ N) : (optimalB N).Nonempty := by
  have hm : N / 2 ≠ 0 := by omega
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (N / 2) hm
  refine ⟨p, ?_⟩
  have hpN : p ≤ N := by omega
  simp only [optimalB, Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, hp, hlt, hpN⟩

/-- The optimal `B` has at least one element for `N ≥ 2` (0-axiom, via Bertrand). -/
theorem optimalB_card_pos {N : ℕ} (hN : 2 ≤ N) : 0 < (optimalB N).card :=
  Finset.card_pos.mpr (optimalB_nonempty hN)

/-- **Chebyshev θ-gap lower bound (0 axioms, 0 sorries).** `∃ c > 0, ∀ N ≥ 4,
`c·N ≤ θ(N) − θ(N/2)`.  This is the classical Chebyshev-strength lower bound, now fully
verified — formerly the analytic axiom `chebyshev_theta_upper_half_lower_bound`.

The proof assembles three verified ingredients:
* `Erdos490Cheb.theta_gap_lower_bound`: the elementary central-binomial estimate
  `n·log 4 − ⌊2n/3⌋·log 4 − log n − √(2n)·log(2n) ≤ θ(2n) − θ(n)` (Erdős's Bertrand proof);
* `Erdos490Cheb.erdos490_analytic_tail`: `∃ c₀ > 0, ∃ N₀, ∀ n ≥ N₀`, the real form of that
  RHS is `≥ c₀·n` (because `log n` and `√(2n)·log(2n)` are `o(n)`);
* `optimalB_nonempty` (Bertrand): `θ(N) − θ(N/2) ≥ log 2 > 0` for every `N ≥ 2`, covering
  the finitely many `N` below the asymptotic threshold `N₁ = 2·max(N₀, 4)`.

Alignment `N ↦ n = ⌊N/2⌋` uses `Chebyshev.theta_mono` (`2⌊N/2⌋ ≤ N`) and `N ≤ 3⌊N/2⌋`. -/
theorem chebyshev_theta_upper_half_lower_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ N : ℕ, N ≥ 4 →
      c * N ≤ Chebyshev.theta (N : ℝ) - Chebyshev.theta ((N / 2 : ℕ) : ℝ) := by
  obtain ⟨c₀, hc₀, N₀, htail⟩ := Erdos490Cheb.erdos490_analytic_tail
  set M : ℕ := max N₀ 4 with hMdef
  set N₁ : ℕ := 2 * M with hN₁def
  have hM4 : 4 ≤ M := le_max_right N₀ 4
  have hMN0 : N₀ ≤ M := le_max_left N₀ 4
  have hMpos : 0 < M := by omega
  have hN₁pos : 0 < N₁ := by omega
  -- Uniform positive lower bound: `log 2 ≤ θ(N) − θ(N/2)` for `N ≥ 2`.
  have hgap2 : ∀ N : ℕ, 2 ≤ N →
      Real.log 2 ≤ Chebyshev.theta (N : ℝ) - Chebyshev.theta ((N / 2 : ℕ) : ℝ) := by
    intro N hN
    rw [theta_gap_eq_sum_optimalB N]
    obtain ⟨p₀, hp₀⟩ := optimalB_nonempty hN
    have hp₀mem := hp₀
    simp only [optimalB, Finset.mem_filter, Finset.mem_range] at hp₀mem
    have hp₀prime : Nat.Prime p₀ := hp₀mem.2.1
    have hp₀2 : (2 : ℝ) ≤ (p₀ : ℝ) := by exact_mod_cast hp₀prime.two_le
    have hp₀pos : (0 : ℝ) < (p₀ : ℝ) := by exact_mod_cast hp₀prime.pos
    have hnn : ∀ p ∈ optimalB N, 0 ≤ Real.log (p : ℝ) := by
      intro p hp
      simp only [optimalB, Finset.mem_filter, Finset.mem_range] at hp
      exact Real.log_nonneg (by exact_mod_cast hp.2.1.one_lt.le)
    calc Real.log 2 ≤ Real.log (p₀ : ℝ) :=
          (Real.log_le_log_iff (by norm_num) hp₀pos).mpr hp₀2
      _ ≤ ∑ p ∈ optimalB N, Real.log (p : ℝ) := Finset.single_le_sum hnn hp₀
  -- Large branch: for `n ≥ M`, `c₀·n ≤ θ(2n) − θ(n)`.
  have hlarge : ∀ n : ℕ, M ≤ n →
      c₀ * (n : ℝ) ≤ Chebyshev.theta ((2 * n : ℕ) : ℝ) - Chebyshev.theta ((n : ℕ) : ℝ) := by
    intro n hnM
    have hn4 : 4 ≤ n := le_trans hM4 hnM
    have hnN0 : N₀ ≤ n := le_trans hMN0 hnM
    have ht := Erdos490Cheb.theta_gap_lower_bound n hn4
    have ha := htail n hnN0
    have hL : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    -- Nat floor / Nat.sqrt only make the elementary RHS larger than its real form.
    have hfloor : ((2 * n / 3 : ℕ) : ℝ) ≤ 2 * (n : ℝ) / 3 := by
      calc ((2 * n / 3 : ℕ) : ℝ) ≤ ((2 * n : ℕ) : ℝ) / ((3 : ℕ) : ℝ) := Nat.cast_div_le
        _ = 2 * (n : ℝ) / 3 := by push_cast; ring
    have hsqrt : (Nat.sqrt (2 * n) : ℝ) ≤ Real.sqrt (2 * (n : ℝ)) := by
      rw [show (2 * (n : ℝ)) = ((2 * n : ℕ) : ℝ) by push_cast; ring]
      exact Real.nat_sqrt_le_real_sqrt
    have hlog2n : 0 ≤ Real.log (2 * (n : ℝ)) := Real.log_nonneg (by linarith)
    have h1 : ((2 * n / 3 : ℕ) : ℝ) * Real.log 4 ≤ (2 * (n : ℝ) / 3) * Real.log 4 :=
      mul_le_mul_of_nonneg_right hfloor hL.le
    have h2 : (Nat.sqrt (2 * n) : ℝ) * Real.log (2 * (n : ℝ))
        ≤ Real.sqrt (2 * (n : ℝ)) * Real.log (2 * (n : ℝ)) :=
      mul_le_mul_of_nonneg_right hsqrt hlog2n
    linarith [ha, ht, h1, h2]
  refine ⟨min (c₀ / 3) (Real.log 2 / N₁), ?_, ?_⟩
  · have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hN₁R : (0 : ℝ) < (N₁ : ℝ) := by exact_mod_cast hN₁pos
    exact lt_min (div_pos hc₀ (by norm_num)) (div_pos hlog2 hN₁R)
  · intro N hN
    rcases lt_or_ge N N₁ with hsmall | hbig
    · -- Small `N` (`4 ≤ N < N₁`): the uniform gap `≥ log 2` and `c ≤ log 2 / N₁ ≤ log 2 / N`.
      have hgap := hgap2 N (by omega)
      have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
      have hNle : (N : ℝ) ≤ (N₁ : ℝ) := by exact_mod_cast hsmall.le
      have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      have hN₁R : (0 : ℝ) < (N₁ : ℝ) := by exact_mod_cast hN₁pos
      have hcmin : min (c₀ / 3) (Real.log 2 / N₁) ≤ Real.log 2 / N₁ := min_le_right _ _
      have hle : (Real.log 2 / N₁) * (N : ℝ) ≤ Real.log 2 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hN₁R]
        exact mul_le_mul_of_nonneg_left hNle hlog2.le
      have hstep : min (c₀ / 3) (Real.log 2 / N₁) * (N : ℝ) ≤ Real.log 2 :=
        le_trans (mul_le_mul_of_nonneg_right hcmin hNpos.le) hle
      linarith [hgap, hstep]
    · -- Large `N` (`N ≥ N₁ = 2M`): set `n = ⌊N/2⌋ ≥ M`, align via `θ` monotone.
      have hnM : M ≤ N / 2 := by omega
      have hbranch := hlarge (N / 2) hnM
      have h2le : (2 * (N / 2) : ℕ) ≤ N := by omega
      have hmono : Chebyshev.theta ((2 * (N / 2) : ℕ) : ℝ) ≤ Chebyshev.theta (N : ℝ) :=
        Chebyshev.theta_mono (by exact_mod_cast h2le)
      have hN3 : (N : ℝ) ≤ 3 * ((N / 2 : ℕ) : ℝ) := by
        have : N ≤ 3 * (N / 2) := by omega
        exact_mod_cast this
      have hcmin : min (c₀ / 3) (Real.log 2 / N₁) ≤ c₀ / 3 := min_le_left _ _
      have hcN : min (c₀ / 3) (Real.log 2 / N₁) * (N : ℝ) ≤ (c₀ / 3) * (N : ℝ) :=
        mul_le_mul_of_nonneg_right hcmin (by positivity)
      have hstep2 : (c₀ / 3) * (N : ℝ) ≤ c₀ * ((N / 2 : ℕ) : ℝ) := by
        have hmul := mul_le_mul_of_nonneg_left hN3 (le_of_lt (div_pos hc₀ (by norm_num : (0:ℝ) < 3)))
        calc (c₀ / 3) * (N : ℝ) ≤ (c₀ / 3) * (3 * ((N / 2 : ℕ) : ℝ)) := hmul
          _ = c₀ * ((N / 2 : ℕ) : ℝ) := by ring
      calc min (c₀ / 3) (Real.log 2 / N₁) * (N : ℝ)
          ≤ (c₀ / 3) * (N : ℝ) := hcN
        _ ≤ c₀ * ((N / 2 : ℕ) : ℝ) := hstep2
        _ ≤ Chebyshev.theta ((2 * (N / 2) : ℕ) : ℝ) - Chebyshev.theta ((N / 2 : ℕ) : ℝ) :=
            hbranch
        _ ≤ Chebyshev.theta (N : ℝ) - Chebyshev.theta ((N / 2 : ℕ) : ℝ) := by linarith [hmono]

/-- **θ → π bridge (0-axiom).** Since every prime `p` counted in the θ-gap satisfies
`p ≤ N`, each `log p ≤ log N`, so the θ-gap is bounded by `|optimalB N| · log N`.  Dividing
by `log N` turns a Chebyshev θ lower bound into the prime-counting lower bound we need. -/
theorem theta_gap_le_card_mul_log {N : ℕ} (hN : 2 ≤ N) :
    Chebyshev.theta (N : ℝ) - Chebyshev.theta ((N / 2 : ℕ) : ℝ)
      ≤ ((optimalB N).card : ℝ) * Real.log N := by
  rw [theta_gap_eq_sum_optimalB]
  have h : ∀ p ∈ optimalB N, Real.log (p : ℝ) ≤ Real.log N := by
    intro p hp
    simp only [optimalB, Finset.mem_filter, Finset.mem_range] at hp
    exact Real.log_le_log (by exact_mod_cast hp.2.1.pos) (by exact_mod_cast hp.2.2.2)
  calc ∑ p ∈ optimalB N, Real.log (p : ℝ)
      ≤ ∑ _p ∈ optimalB N, Real.log (N : ℝ) := Finset.sum_le_sum h
    _ = ((optimalB N).card : ℝ) * Real.log N := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- **Chebyshev-type prime-counting lower bound** (the one irreducible analytic input to
the optimal-example *lower* bound), now a *theorem* (0 new axioms) derived from the
Chebyshev θ-gap axiom `chebyshev_theta_upper_half_lower_bound` via the verified `θ → π`
bridge.  The number of primes in `(N/2, N]` — i.e. `(optimalB N).card = π(N) − π(N/2)` — is
`≳ N / log N`, because `θ(N) − θ(N/2) = ∑_{N/2 < p ≤ N} log p ≤ (π(N)−π(N/2))·log N` and the
θ-gap is `≳ N`.  The eventual elimination of the remaining axiom is now *exactly* the
classical Chebyshev θ-gap lower bound `θ(N) − θ(N/2) ≥ c·N`, cleanly pinned to Mathlib's
`Chebyshev.theta` API rather than a bespoke prime-counting difference. -/
theorem primes_upper_half_lower_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ N : ℕ, N ≥ 4 →
      c * N / Real.log N ≤ ((optimalB N).card : ℝ) := by
  obtain ⟨c, hc, hgap⟩ := chebyshev_theta_upper_half_lower_bound
  refine ⟨c, hc, fun N hN => ?_⟩
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have h1 : c * (N : ℝ) ≤ ((optimalB N).card : ℝ) * Real.log N :=
    (hgap N hN).trans (theta_gap_le_card_mul_log (by omega))
  rw [div_le_iff₀ hlogN]
  exact h1

/-- **Bridge to Mathlib's prime-counting function** (0-axiom). The optimal `B` is exactly
the set of primes in `(N/2, N]`, so its cardinality is `π(N) − π(N/2)`, where
`π = Nat.primeCounting` counts the primes `≤ ·`. This pins the analytic axiom
`primes_upper_half_lower_bound` to Mathlib's `Nat.primeCounting` API: eliminating the axiom
is now *exactly* the problem of supplying a Chebyshev-strength lower bound for
`π(N) − π(N/2)`, with the combinatorial cardinality identity already discharged here. -/
theorem optimalB_card_eq_primeCounting (N : ℕ) :
    (optimalB N).card = N.primeCounting - (N / 2).primeCounting := by
  -- `π m` as the cardinality of the prime-filtered range `[0, m]`.
  have hπ : ∀ m : ℕ, m.primeCounting
      = ((Finset.range (m + 1)).filter Nat.Prime).card := by
    intro m
    unfold Nat.primeCounting Nat.primeCounting'
    rw [Nat.count_eq_card_filter_range]
  -- `optimalB` drops the `p ≤ N` conjunct, which is automatic inside `range (N + 1)`.
  have hB : optimalB N
      = (Finset.range (N + 1)).filter (fun p => Nat.Prime p ∧ N / 2 < p) := by
    ext p
    simp only [optimalB, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hr, hp, hlt, _⟩; exact ⟨hr, hp, hlt⟩
    · rintro ⟨hr, hp, hlt⟩; exact ⟨hr, hp, hlt, by omega⟩
  -- The primes `≤ N/2` are exactly the prime-filtered range `[0, N/2]`.
  have hlow : (Finset.range (N + 1)).filter (fun p => Nat.Prime p ∧ ¬ N / 2 < p)
      = (Finset.range (N / 2 + 1)).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨_, hp, hle⟩; exact ⟨by omega, hp⟩
    · rintro ⟨hlt, hp⟩; exact ⟨by omega, hp, by omega⟩
  -- Partition the primes `≤ N` by whether they exceed `N/2`.
  have hpart := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (Finset.range (N + 1)).filter Nat.Prime) (p := fun p => N / 2 < p)
  rw [Finset.filter_filter, Finset.filter_filter, ← hB, hlow] at hpart
  rw [hπ N, hπ (N / 2)]
  omega

/-- **Strict prime-counting gap (0-axiom).** For `N ≥ 2`, `π(N/2) < π(N)`: the upper
half `(N/2, N]` always contributes at least one new prime. This is the qualitative
(constant `c = 1/N`-strength) shadow of `primes_upper_half_lower_bound`, obtained by
combining `optimalB_card_pos` (Bertrand) with the counting identity
`optimalB_card_eq_primeCounting`. -/
theorem primeCounting_half_lt {N : ℕ} (hN : 2 ≤ N) :
    (N / 2).primeCounting < N.primeCounting := by
  have h := optimalB_card_pos hN
  rw [optimalB_card_eq_primeCounting] at h
  omega

/- The optimal example achieves |A||B| ~ N²/(2 log N). -/
/-- Why it works: products `a·p` are distinct because each prime `p > N/2` exceeds
every `a ≤ N/2`, so `p` cannot divide a nonzero `a`.  Positivity `1 ≤ aᵢ` (which holds
for the elements of `optimalA`) is needed: without it `a₁ = a₂ = 0` gives `0 = 0` for
any distinct primes. -/
theorem optimal_works_because_primes (a₁ a₂ : ℕ) (p₁ p₂ : ℕ)
    (ha₁_pos : 1 ≤ a₁) (ha₂_pos : 1 ≤ a₂)
    (ha₁ : a₁ ≤ N / 2) (ha₂ : a₂ ≤ N / 2)
    (hp₁ : Nat.Prime p₁) (hp₂ : Nat.Prime p₂)
    (hp₁_large : N / 2 < p₁) (hp₂_large : N / 2 < p₂)
    (heq : a₁ * p₁ = a₂ * p₂) : a₁ = a₂ ∧ p₁ = p₂ := by
  -- `p₁ ∣ a₂ * p₂ = a₁ * p₁`.  As `p₁` is prime, `p₁ ∣ a₂` or `p₁ ∣ p₂`.
  -- `p₁ > N/2 ≥ a₂ ≥ 1`, so `p₁ ∣ a₂` is impossible (a positive multiple of `p₁`
  -- is `≥ p₁ > a₂`).  Hence `p₁ ∣ p₂`, and both prime gives `p₁ = p₂`; cancelling
  -- the nonzero `p₁` yields `a₁ = a₂`.
  have ha₂_lt : a₂ < p₁ := lt_of_le_of_lt ha₂ hp₁_large
  have hdvd : p₁ ∣ a₂ * p₂ := ⟨a₁, by rw [← heq]; ring⟩
  have hp₁p₂ : p₁ = p₂ := by
    rcases (hp₁.prime.dvd_mul.mp hdvd) with hda | hdp
    · -- p₁ ∣ a₂ with 0 < a₂ < p₁ is impossible
      have : p₁ ≤ a₂ := Nat.le_of_dvd (by omega) hda
      omega
    · exact (Nat.prime_dvd_prime_iff_eq hp₁ hp₂).mp hdp
  refine ⟨?_, hp₁p₂⟩
  -- cancel p₁ = p₂ (nonzero) from a₁ * p₁ = a₂ * p₂
  have hp₁_pos : 0 < p₁ := hp₁.pos
  have : a₁ * p₁ = a₂ * p₁ := by rw [heq, hp₁p₂]
  exact Nat.eq_of_mul_eq_mul_right hp₁_pos this

/-- **The optimal example has distinct products** (0-axiom).  Formerly an axiom;
now derived from `optimal_works_because_primes` via the
`ProductMapInjective ↔ HasDistinctProducts` bridge.  Every `a ∈ optimalA N` lies in
`[1, N/2]` (so `1 ≤ a` and `a ≤ N/2`) and every `p ∈ optimalB N` is a prime in
`(N/2, N]`, exactly the hypotheses of `optimal_works_because_primes`. -/
theorem optimal_has_distinct_products (N : ℕ) (hN : N ≥ 4) :
    HasDistinctProducts (optimalA N) (optimalB N) := by
  rw [← productMapInjective_iff_hasDistinctProducts]
  intro a₁ a₂ b₁ b₂ ha₁ ha₂ hb₁ hb₂ heq
  simp only [optimalA, Finset.mem_filter, Finset.mem_range] at ha₁ ha₂
  simp only [optimalB, Finset.mem_filter, Finset.mem_range] at hb₁ hb₂
  obtain ⟨_, ha₁1, ha₁2⟩ := ha₁
  obtain ⟨_, ha₂1, ha₂2⟩ := ha₂
  obtain ⟨_, hb₁p, hb₁lt, _⟩ := hb₁
  obtain ⟨_, hb₂p, hb₂lt, _⟩ := hb₂
  exact optimal_works_because_primes a₁ a₂ b₁ b₂ ha₁1 ha₂1 ha₁2 ha₂2
    hb₁p hb₂p hb₁lt hb₂lt heq

/-
## Part V: The Limit Question (Open)
-/

/-- The ratio |A||B| log N / N². -/
noncomputable def productRatio (N : ℕ) : ℝ :=
  (maxProductSize N : ℝ) * Real.log N / N^2

/-- Erdős asked: Does lim productRatio(N) exist? If so, what is it? -/
def LimitQuestion : Prop :=
  ∃ L : ℝ, Filter.Tendsto productRatio Filter.atTop (nhds L)

/- Van Doorn observed: If the limit exists, it must be ≥ 1. -/
/-- The limit question is OPEN. -/
def LimitQuestionOpen : Prop :=
  -- We don't know if the limit exists
  True

/-
## Part VI: Special Cases
-/

/-- Case A = B (multiplicative Sidon sets). -/
def IsMultiplicativeSidon (A : Finset ℕ) : Prop :=
  HasDistinctProducts A A

/- For A = B, the bound is |A|² ≪ N²/log N, so |A| ≪ N/√(log N). -/
/-- The genuine multiplicative-Sidon property of the primes.  Note that the *ordered*
notion `IsMultiplicativeSidon P = HasDistinctProducts P P` (`(productSet P P).card =
|P|²`) is **false** for `|P| ≥ 2`, because commutativity collapses `p·q` and `q·p` to a
single element of the product set (e.g. `P = {2,3}` gives `productSet = {4,6,9}` of card
`3 ≠ 4 = |P|²`).  The correct statement is that a product of two primes determines the
unordered pair: if `p₁·q₁ = p₂·q₂` with all four prime then `{p₁,q₁} = {p₂,q₂}`.  This is
the honest "multiplicative Sidon" content, a direct consequence of prime divisibility. -/
theorem primes_products_determine_pair {p₁ q₁ p₂ q₂ : ℕ}
    (hp₁ : Nat.Prime p₁) (hq₁ : Nat.Prime q₁) (hp₂ : Nat.Prime p₂) (hq₂ : Nat.Prime q₂)
    (h : p₁ * q₁ = p₂ * q₂) :
    (p₁ = p₂ ∧ q₁ = q₂) ∨ (p₁ = q₂ ∧ q₁ = p₂) := by
  -- `p₁ ∣ p₂ * q₂`, and `p₁` prime, so `p₁ = p₂` or `p₁ = q₂`; cancel and finish.
  have hdvd : p₁ ∣ p₂ * q₂ := ⟨q₁, by rw [← h]⟩
  rcases (hp₁.prime.dvd_mul.mp hdvd) with hd | hd
  · -- p₁ = p₂
    have hp₁p₂ : p₁ = p₂ := (Nat.prime_dvd_prime_iff_eq hp₁ hp₂).mp hd
    refine Or.inl ⟨hp₁p₂, ?_⟩
    rw [← hp₁p₂] at h
    exact Nat.eq_of_mul_eq_mul_left hp₁.pos h
  · -- p₁ = q₂
    have hp₁q₂ : p₁ = q₂ := (Nat.prime_dvd_prime_iff_eq hp₁ hq₂).mp hd
    refine Or.inr ⟨hp₁q₂, ?_⟩
    rw [← hp₁q₂, Nat.mul_comm p₂ p₁] at h
    exact Nat.eq_of_mul_eq_mul_left hp₁.pos h

/-
## Part VII: Related Problems
-/

/-- Connection to Problem #425 (sumsets). -/
def RelatedProblem425 : Prop :=
  -- Analogous question for sums instead of products
  True

/-- Connection to Problem #896 (product set sizes). -/
def RelatedProblem896 : Prop :=
  -- More general product set questions
  True

/-- The multiplicative energy E(A, B) counts coincidences. -/
noncomputable def multiplicativeEnergy (A B : Finset ℕ) : ℕ :=
  ((A ×ˢ A) ×ˢ (B ×ˢ B)).filter
    (fun ((a₁, a₂), (b₁, b₂)) => a₁ * b₁ = a₂ * b₂)
    |>.card

/-- **Distinct products means minimal energy.**  PROVED via the diagonal-subset
argument (cleaner than the fiber-sum route): the multiplicative-energy set `E`
always contains the diagonal `Δ = {((a,a),(b,b))}`, whose size is exactly
`|A||B|`.  The product map is injective on `A ×ˢ B` iff `E = Δ` (no off-diagonal
coincidences), and since `Δ ⊆ E` that is equivalent to `|E| = |Δ| = |A||B|`.
The injectivity is in turn equivalent to `HasDistinctProducts` via
`Finset.card_image_iff` (the product set is the image of the product map). -/
theorem distinct_minimal_energy (A B : Finset ℕ) :
    HasDistinctProducts A B ↔ multiplicativeEnergy A B = A.card * B.card := by
  classical
  set s : Finset (ℕ × ℕ) := A ×ˢ B with hsdef
  set f : ℕ × ℕ → ℕ := fun p => p.1 * p.2 with hfdef
  have hcard : s.card = A.card * B.card := Finset.card_product A B
  -- HasDistinctProducts ⇔ the product map is injective on `A ×ˢ B`.
  have hps : productSet A B = s.image f := by
    ext n
    simp only [productSet, hsdef, hfdef, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_product]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩
    · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩; exact ⟨a, ha, b, hb, rfl⟩
  have hHD : HasDistinctProducts A B ↔ Set.InjOn f ↑s := by
    rw [HasDistinctProducts, hps, ← hcard, Finset.card_image_iff]
  -- The energy filter `E` and its diagonal `Δ` inside `S = (A×A)×(B×B)`.
  set S : Finset ((ℕ × ℕ) × (ℕ × ℕ)) := (A ×ˢ A) ×ˢ (B ×ˢ B) with hSdef
  set E : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
    S.filter (fun q => q.1.1 * q.2.1 = q.1.2 * q.2.2) with hEdef
  set Δ : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
    S.filter (fun q => q.1.1 = q.1.2 ∧ q.2.1 = q.2.2) with hΔdef
  have henergy : multiplicativeEnergy A B = E.card := rfl
  -- Δ ⊆ E.
  have hsub : Δ ⊆ E := by
    intro q hq
    rw [hΔdef, Finset.mem_filter] at hq
    rw [hEdef, Finset.mem_filter]
    exact ⟨hq.1, by rw [hq.2.1, hq.2.2]⟩
  -- |Δ| = |A||B|, via the bijection ((a,a),(b,b)) ↔ (a,b).
  have hΔcard : Δ.card = A.card * B.card := by
    rw [← hcard]
    refine Finset.card_bij' (fun q _ => (q.1.1, q.2.1))
      (fun p _ => ((p.1, p.1), (p.2, p.2))) ?hi ?hj ?left ?right
    case hi =>
      rintro ⟨⟨a₁, a₂⟩, ⟨b₁, b₂⟩⟩ hq
      rw [hΔdef, Finset.mem_filter] at hq
      simp only [hSdef, Finset.mem_product] at hq
      rw [hsdef, Finset.mem_product]
      exact ⟨hq.1.1.1, hq.1.2.1⟩
    case hj =>
      rintro ⟨a, b⟩ hp
      rw [hsdef, Finset.mem_product] at hp
      rw [hΔdef, Finset.mem_filter]
      simp only [hSdef, Finset.mem_product]
      exact ⟨⟨⟨hp.1, hp.1⟩, hp.2, hp.2⟩, trivial, trivial⟩
    case left =>
      rintro ⟨⟨a₁, a₂⟩, ⟨b₁, b₂⟩⟩ hq
      rw [hΔdef, Finset.mem_filter] at hq
      obtain ⟨_, h1, h2⟩ := hq
      simp only at h1 h2
      subst h1; subst h2; rfl
    case right =>
      rintro ⟨a, b⟩ _; rfl
  -- InjOn ⇔ E = Δ.
  have hED : Set.InjOn f ↑s ↔ E = Δ := by
    constructor
    · intro hinj
      refine Finset.Subset.antisymm ?_ hsub
      rintro ⟨⟨a₁, a₂⟩, ⟨b₁, b₂⟩⟩ hq
      rw [hEdef, Finset.mem_filter] at hq
      simp only [hSdef, Finset.mem_product] at hq
      obtain ⟨⟨⟨ha1, ha2⟩, hb1, hb2⟩, hprod⟩ := hq
      have hx : (a₁, b₁) ∈ s := by rw [hsdef, Finset.mem_product]; exact ⟨ha1, hb1⟩
      have hy : (a₂, b₂) ∈ s := by rw [hsdef, Finset.mem_product]; exact ⟨ha2, hb2⟩
      have heq := hinj hx hy hprod
      rw [Prod.mk.injEq] at heq
      rw [hΔdef, Finset.mem_filter]
      simp only [hSdef, Finset.mem_product]
      exact ⟨⟨⟨ha1, ha2⟩, hb1, hb2⟩, heq.1, heq.2⟩
    · intro hEΔ
      rintro ⟨a₁, b₁⟩ hx ⟨a₂, b₂⟩ hy hfxy
      rw [Finset.mem_coe, hsdef, Finset.mem_product] at hx hy
      have hqE : (((a₁, a₂), (b₁, b₂)) : (ℕ × ℕ) × (ℕ × ℕ)) ∈ E := by
        rw [hEdef, Finset.mem_filter]
        simp only [hSdef, Finset.mem_product]
        exact ⟨⟨⟨hx.1, hy.1⟩, hx.2, hy.2⟩, hfxy⟩
      rw [hEΔ, hΔdef, Finset.mem_filter] at hqE
      obtain ⟨_, h1, h2⟩ := hqE
      simp only at h1 h2
      rw [Prod.mk.injEq]
      exact ⟨h1, h2⟩
  -- Assemble.
  rw [hHD, henergy, hED]
  constructor
  · intro h; rw [h, hΔcard]
  · intro h
    exact (Finset.eq_of_subset_of_card_le hsub (by rw [h, hΔcard])).symm

/-- **General lower bound on multiplicative energy**: `|A|·|B| ≤ E(A, B)`.  The diagonal
quadruples `((a, a), (b, b))` always satisfy the energy relation `a·b = a·b`, and
`(a, b) ↦ ((a, a), (b, b))` injects `A ×ˢ B` into the energy set.  Together with
`distinct_minimal_energy` (which identifies the equality case) this shows the energy is
*minimized exactly* when the products are distinct: `E(A, B) ≥ |A||B|` always, with
equality iff `HasDistinctProducts A B`. -/
theorem multiplicativeEnergy_ge (A B : Finset ℕ) :
    A.card * B.card ≤ multiplicativeEnergy A B := by
  classical
  have hinj : Set.InjOn (fun p : ℕ × ℕ => ((p.1, p.1), (p.2, p.2))) ↑(A ×ˢ B) := by
    intro p _ p' _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext_iff.mpr ⟨h.1.1, h.2.1⟩
  have hsub : (A ×ˢ B).image (fun p : ℕ × ℕ => ((p.1, p.1), (p.2, p.2))) ⊆
      ((A ×ˢ A) ×ˢ (B ×ˢ B)).filter (fun ((a₁, a₂), (b₁, b₂)) => a₁ * b₁ = a₂ * b₂) := by
    intro q hq
    simp only [Finset.mem_image, Finset.mem_product] at hq
    obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩ := hq
    refine Finset.mem_filter.mpr ⟨?_, rfl⟩
    simp only [Finset.mem_product]
    exact ⟨⟨ha, ha⟩, hb, hb⟩
  calc A.card * B.card
      = (A ×ˢ B).card := (Finset.card_product A B).symm
    _ = ((A ×ˢ B).image (fun p : ℕ × ℕ => ((p.1, p.1), (p.2, p.2)))).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ multiplicativeEnergy A B := Finset.card_le_card hsub

/-- **Multiplicative energy is symmetric**: `E(A, B) = E(B, A)`.  Swapping the two
factors, `((a₁, a₂), (b₁, b₂)) ↦ ((b₁, b₂), (a₁, a₂))`, is a bijection between the two
energy sets: the defining relation `a₁·b₁ = a₂·b₂` is carried to `b₁·a₁ = b₂·a₂` by
`mul_comm`, and the swap is its own inverse. -/
theorem multiplicativeEnergy_comm (A B : Finset ℕ) :
    multiplicativeEnergy A B = multiplicativeEnergy B A := by
  classical
  unfold multiplicativeEnergy
  refine Finset.card_bij'
    (fun q _ => ((q.2.1, q.2.2), (q.1.1, q.1.2)))
    (fun q _ => ((q.2.1, q.2.2), (q.1.1, q.1.2)))
    ?hi ?hj ?left ?right
  case hi =>
    rintro ⟨⟨a₁, a₂⟩, ⟨b₁, b₂⟩⟩ hq
    rw [Finset.mem_filter] at hq
    simp only [Finset.mem_product] at hq
    obtain ⟨⟨⟨ha1, ha2⟩, hb1, hb2⟩, hrel⟩ := hq
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · simp only [Finset.mem_product]; exact ⟨⟨hb1, hb2⟩, ha1, ha2⟩
    · show b₁ * a₁ = b₂ * a₂
      rw [mul_comm b₁ a₁, mul_comm b₂ a₂]; exact hrel
  case hj =>
    rintro ⟨⟨b₁, b₂⟩, ⟨a₁, a₂⟩⟩ hq
    rw [Finset.mem_filter] at hq
    simp only [Finset.mem_product] at hq
    obtain ⟨⟨⟨hb1, hb2⟩, ha1, ha2⟩, hrel⟩ := hq
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · simp only [Finset.mem_product]; exact ⟨⟨ha1, ha2⟩, hb1, hb2⟩
    · show a₁ * b₁ = a₂ * b₂
      rw [mul_comm a₁ b₁, mul_comm a₂ b₂]; exact hrel
  case left =>
    rintro ⟨⟨a₁, a₂⟩, ⟨b₁, b₂⟩⟩ _; rfl
  case right =>
    rintro ⟨⟨b₁, b₂⟩, ⟨a₁, a₂⟩⟩ _; rfl

/-- **Strict energy excess characterizes product collisions.**  Combining the general
lower bound `|A||B| ≤ E(A, B)` (`multiplicativeEnergy_ge`) with its equality case
(`distinct_minimal_energy`): the energy *strictly* exceeds `|A||B|` exactly when the
products are not all distinct.  This completes the trichotomy — energy equals `|A||B|`
iff products are distinct, and exceeds it otherwise. -/
theorem multiplicativeEnergy_gt_iff_not_distinctProducts (A B : Finset ℕ) :
    A.card * B.card < multiplicativeEnergy A B ↔ ¬HasDistinctProducts A B := by
  rw [distinct_minimal_energy]
  constructor
  · intro hlt heq; rw [heq] at hlt; exact lt_irrefl _ hlt
  · intro hne; exact lt_of_le_of_ne (multiplicativeEnergy_ge A B) (Ne.symm hne)

/-
## Part VIII: Bounds History
-/

/-- Trivial bound: |A||B| ≤ N². -/
theorem trivial_bound (N : ℕ) (A B : Finset ℕ)
    (hA : IsSubsetUpTo A N) (hB : IsSubsetUpTo B N) :
    A.card * B.card ≤ N^2 := by
  have hAN : A.card ≤ N :=
    (Finset.card_le_card (fun a ha => Finset.mem_Icc.mpr (hA a ha))).trans
      (by rw [Nat.card_Icc]; omega)
  have hBN : B.card ≤ N :=
    (Finset.card_le_card (fun b hb => Finset.mem_Icc.mpr (hB b hb))).trans
      (by rw [Nat.card_Icc]; omega)
  calc A.card * B.card ≤ N * N := Nat.mul_le_mul hAN hBN
    _ = N ^ 2 := (sq N).symm

/-- Counting bound: |A||B| ≤ N² (since products are ≤ N²). -/
theorem counting_bound (N : ℕ) (A B : Finset ℕ)
    (hA : IsSubsetUpTo A N) (hB : IsSubsetUpTo B N)
    (h : HasDistinctProducts A B) :
    A.card * B.card ≤ N^2 :=
  trivial_bound N A B hA hB

/-- Szemerédi's improvement: |A||B| ≤ C·N²/log N. -/
theorem szemeredi_bound (N : ℕ) (hN : N ≥ 2) (A B : Finset ℕ)
    (hA : IsSubsetUpTo A N) (hB : IsSubsetUpTo B N)
    (h : HasDistinctProducts A B) :
    ∃ C : ℝ, C > 0 ∧ (A.card * B.card : ℝ) ≤ C * N^2 / Real.log N := by
  obtain ⟨C, hC, hBound⟩ := szemeredi_theorem
  exact ⟨C, hC, hBound N hN A B hA hB h⟩

/-
## Part IX: Summary
-/

/-- **Erdős Problem #490: SOLVED by Szemerédi (1976)**

Question: If A, B ⊆ {1,...,N} have all products ab distinct,
is |A||B| ≪ N²/log N?

Answer: YES

Optimal: A = [1, N/2], B = {p prime : N/2 < p ≤ N}
achieves |A||B| ~ N²/(2 log N).

Open: Does lim |A||B| log N / N² exist? If so, what is its value?
(Must be ≥ 1 by van Doorn.)
-/
theorem erdos_490 : ErdosQuestion490 := szemeredi_theorem

/-- Main theorem statement. -/
theorem erdos_490_main :
    ∃ C : ℝ, C > 0 ∧
      ∀ N : ℕ, N ≥ 2 →
        ∀ A B : Finset ℕ, IsSubsetUpTo A N → IsSubsetUpTo B N →
          HasDistinctProducts A B →
          (A.card * B.card : ℝ) ≤ C * N^2 / Real.log N :=
  szemeredi_theorem

/-- The bound is optimal up to a constant.

The lower-bound constant is *not* hardcoded: a fixed `c` such as `1/3` is in fact
**false** at small `N` (e.g. `N = 10`, where the product ratio dips to `≈ 0.115`),
so the theorem is stated and proved in its honest `∃ c > 0` form.  The constant is
produced from the Chebyshev-type input `primes_upper_half_lower_bound`: from
`(optimalB N).card ≥ c·N/log N` and `(optimalA N).card = ⌊N/2⌋ ≥ N/4` (for `N ≥ 4`),
the product is `≥ (c/4)·N²/log N`. -/
theorem bound_is_optimal :
    ∃ c : ℝ, c > 0 ∧
      ∀ N : ℕ, N ≥ 4 →
        ∃ A B : Finset ℕ,
          IsSubsetUpTo A N ∧ IsSubsetUpTo B N ∧
          HasDistinctProducts A B ∧
          (A.card * B.card : ℝ) ≥ c * N^2 / Real.log N := by
  obtain ⟨c, hc, hcB⟩ := primes_upper_half_lower_bound
  refine ⟨c / 4, by positivity, ?_⟩
  intro N hN
  use optimalA N, optimalB N
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- IsSubsetUpTo (optimalA N) N : elements satisfy 1 ≤ n ≤ N/2 ≤ N
    intro a ha
    simp only [optimalA, Finset.mem_filter, Finset.mem_range] at ha
    obtain ⟨_, ha1, ha2⟩ := ha
    exact ⟨ha1, le_trans ha2 (Nat.div_le_self N 2)⟩
  · -- IsSubsetUpTo (optimalB N) N : primes p with N/2 < p ≤ N satisfy 1 ≤ p ≤ N
    intro b hb
    simp only [optimalB, Finset.mem_filter, Finset.mem_range] at hb
    obtain ⟨_, hbprime, _, hbN⟩ := hb
    exact ⟨hbprime.one_lt.le, hbN⟩
  · exact optimal_has_distinct_products N (by linarith)
  · -- Lower bound: combine |optimalA N| ≥ N/4 with the Chebyshev input on |optimalB N|.
    have hNR : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hlogpos : 0 < Real.log N := Real.log_pos (by linarith)
    -- |optimalA N| = ⌊N/2⌋, and `N ≤ 4·⌊N/2⌋` for `N ≥ 4` gives `↑⌊N/2⌋ ≥ N/4`.
    have hAcard : (optimalA N).card = N / 2 := optimalA_card N
    have hAnat : N ≤ 4 * (N / 2) := by omega
    have hAR : (N : ℝ) / 4 ≤ ((optimalA N).card : ℝ) := by
      rw [hAcard]
      have : (N : ℝ) ≤ 4 * ((N / 2 : ℕ) : ℝ) := by exact_mod_cast hAnat
      linarith
    -- |optimalB N| ≥ c·N/log N from the axiom.
    have hBR : c * N / Real.log N ≤ ((optimalB N).card : ℝ) := hcB N hN
    -- Both lower bounds are nonnegative, so the products multiply.
    have hA0 : (0 : ℝ) ≤ (N : ℝ) / 4 := by positivity
    have hB0 : (0 : ℝ) ≤ c * N / Real.log N := by positivity
    have hprod : ((N : ℝ) / 4) * (c * N / Real.log N) ≤
        ((optimalA N).card : ℝ) * ((optimalB N).card : ℝ) :=
      mul_le_mul hAR hBR hB0 (le_trans hA0 hAR)
    -- The left-hand product equals (c/4)·N²/log N (a formal field identity).
    have hsimp : ((N : ℝ) / 4) * (c * N / Real.log N) = c / 4 * (N : ℝ) ^ 2 / Real.log N := by
      ring
    rw [ge_iff_le]
    linarith [hprod, hsimp]

/-- **Upper bound on the optimal `B` (0 new axioms).** For `N ≥ 4`, the primes in
`(N/2, N]` satisfy `|optimalB N| · log(N/2) ≤ log 4 · N`.  Each `p ∈ optimalB N` has
`p > N/2`, so `log(N/2) ≤ log p`; summing gives `|optimalB N| · log(N/2) ≤ ∑ log p =
θ(N) − θ(N/2) ≤ θ(N) ≤ log 4 · N`, the last step being Mathlib's Chebyshev upper bound
`Chebyshev.theta_le_log4_mul_x`.  This is the upper-bound companion to
`primes_upper_half_lower_bound`. -/
theorem optimalB_card_upper_bound {N : ℕ} (hN : 4 ≤ N) :
    ((optimalB N).card : ℝ) * Real.log ((N : ℝ) / 2) ≤ Real.log 4 * N := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hhalf_pos : (0 : ℝ) < (N : ℝ) / 2 := by linarith
  -- Every prime `p ∈ optimalB N` exceeds `N/2`, so `log(N/2) ≤ log p`.
  have hlb : ∀ p ∈ optimalB N, Real.log ((N : ℝ) / 2) ≤ Real.log (p : ℝ) := by
    intro p hp
    simp only [optimalB, Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨_, _, hlt, _⟩ := hp
    have hNp : (N : ℝ) < 2 * (p : ℝ) := by
      have : N < 2 * p := by omega
      exact_mod_cast this
    exact Real.log_le_log hhalf_pos (by linarith)
  -- `|B| · log(N/2) ≤ ∑_{p ∈ B} log p` (constant lower bound on each term).
  have hsum : ((optimalB N).card : ℝ) * Real.log ((N : ℝ) / 2)
      ≤ ∑ p ∈ optimalB N, Real.log (p : ℝ) := by
    calc ((optimalB N).card : ℝ) * Real.log ((N : ℝ) / 2)
        = ∑ _p ∈ optimalB N, Real.log ((N : ℝ) / 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ p ∈ optimalB N, Real.log (p : ℝ) := Finset.sum_le_sum hlb
  -- The sum is `θ(N) − θ(N/2) ≤ θ(N) ≤ log 4 · N`.
  have heq := theta_gap_eq_sum_optimalB N
  have hθnn : 0 ≤ Chebyshev.theta ((N / 2 : ℕ) : ℝ) := Chebyshev.theta_nonneg _
  have hθub : Chebyshev.theta (N : ℝ) ≤ Real.log 4 * N :=
    Chebyshev.theta_le_log4_mul_x (by positivity)
  calc ((optimalB N).card : ℝ) * Real.log ((N : ℝ) / 2)
      ≤ ∑ p ∈ optimalB N, Real.log (p : ℝ) := hsum
    _ = Chebyshev.theta (N : ℝ) - Chebyshev.theta ((N / 2 : ℕ) : ℝ) := heq.symm
    _ ≤ Chebyshev.theta (N : ℝ) := by linarith
    _ ≤ Real.log 4 * N := hθub

/-- **The optimal example attains order `N²/log N` from above (0 new axioms).** For
`N ≥ 4`, `|optimalA N| · |optimalB N| ≤ log 4 · N² / log N`.  Combined with
`bound_is_optimal` (the matching `≥ c·N²/log N` lower bound) this shows the explicit
extremal construction `A = [1, N/2]`, `B = {primes in (N/2, N]}` achieves
`|A|·|B| = Θ(N²/log N)` — the full order of magnitude of Erdős #490 — *without* invoking
the deep axiom `szemeredi_theorem` (only Mathlib's Chebyshev upper bound `θ(x) ≤ log 4·x`).

Proof: `|optimalA N| = ⌊N/2⌋ ≤ N/2`, and `optimalB_card_upper_bound` gives
`|optimalB N| ≤ log 4·N / log(N/2)`.  For `N ≥ 4`, `log(N/2) = log N − log 2 ≥ (1/2) log N`
(because `log N ≥ log 4 = 2 log 2`), so the product is `≤ (N/2)·log 4·N / ((1/2) log N) =
log 4·N² / log N`. -/
theorem optimal_example_upper_bound (N : ℕ) (hN : 4 ≤ N) :
    ((optimalA N).card * (optimalB N).card : ℝ) ≤ Real.log 4 * N ^ 2 / Real.log N := by
  have hNR : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := by linarith
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hlog4nn : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlogN4 : Real.log 4 ≤ Real.log N := Real.log_le_log (by norm_num) hNR
  -- `log(N/2) = log N − log 2`, and `log 4 = 2 log 2`.
  have hlogNhalf_eq : Real.log ((N : ℝ) / 2) = Real.log N - Real.log 2 :=
    Real.log_div (by exact_mod_cast (by omega : N ≠ 0)) (by norm_num)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  -- `log(N/2) ≥ (1/2) log N > 0`.
  have hhalf_lb : Real.log N / 2 ≤ Real.log ((N : ℝ) / 2) := by
    rw [hlogNhalf_eq]
    have h2 : 2 * Real.log 2 ≤ Real.log N := by rw [← hlog4]; exact hlogN4
    linarith
  have hhalf_pos : 0 < Real.log ((N : ℝ) / 2) := by linarith
  -- `|optimalA N| ≤ N/2`, and the two cardinalities are nonnegative.
  have hAcard : (optimalA N).card = N / 2 := optimalA_card N
  have hAR : ((optimalA N).card : ℝ) ≤ (N : ℝ) / 2 := by
    rw [hAcard]
    have hnat : (N / 2 : ℕ) * 2 ≤ N := by omega
    have : ((N / 2 : ℕ) : ℝ) * 2 ≤ (N : ℝ) := by exact_mod_cast hnat
    linarith
  have hA0 : (0 : ℝ) ≤ ((optimalA N).card : ℝ) := by positivity
  have hB0 : (0 : ℝ) ≤ ((optimalB N).card : ℝ) := by positivity
  have hBub := optimalB_card_upper_bound hN
  -- Clear the denominator and finish with the nonnegative-product chain.
  rw [le_div_iff₀ hlogN]
  nlinarith [hBub, hAR, hhalf_lb, hA0, hB0, hlogN.le, hlog4nn, hNnn,
    mul_nonneg hA0 hB0,
    mul_le_mul_of_nonneg_left hBub hA0,
    mul_le_mul_of_nonneg_right hAR (mul_nonneg hlog4nn hNnn),
    mul_le_mul_of_nonneg_left (show Real.log N ≤ 2 * Real.log ((N : ℝ) / 2) by linarith)
      (mul_nonneg hA0 hB0)]

end Erdos490
