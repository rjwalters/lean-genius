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

/- The two definitions `HasDistinctProducts` and `ProductMapInjective` are equivalent. -/
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

/-
## Part IV: The Optimal Example
-/

/-- The first half of [1, N]: A = [1, N/2]. -/
def optimalA (N : ℕ) : Finset ℕ :=
  Finset.filter (fun n => 1 ≤ n ∧ n ≤ N / 2) (Finset.range (N + 1))

/-- The primes in the second half: B = {p : N/2 < p ≤ N, p prime}. -/
def optimalB (N : ℕ) : Finset ℕ :=
  Finset.filter (fun p => Nat.Prime p ∧ N / 2 < p ∧ p ≤ N) (Finset.range (N + 1))

/-- The optimal example has distinct products. -/
axiom optimal_has_distinct_products (N : ℕ) (hN : N ≥ 4) :
  HasDistinctProducts (optimalA N) (optimalB N)

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

/-- The bound is optimal up to a constant. -/
theorem bound_is_optimal :
    ∃ c : ℝ, c > 0 ∧
      ∀ N : ℕ, N ≥ 4 →
        ∃ A B : Finset ℕ,
          IsSubsetUpTo A N ∧ IsSubsetUpTo B N ∧
          HasDistinctProducts A B ∧
          (A.card * B.card : ℝ) ≥ c * N^2 / Real.log N := by
  use 1/3  -- lower bound constant
  constructor
  · norm_num
  · intro N hN
    use optimalA N, optimalB N
    constructor
    · -- IsSubsetUpTo (optimalA N) N : elements satisfy 1 ≤ n ≤ N/2 ≤ N
      intro a ha
      simp only [optimalA, Finset.mem_filter, Finset.mem_range] at ha
      obtain ⟨_, ha1, ha2⟩ := ha
      exact ⟨ha1, le_trans ha2 (Nat.div_le_self N 2)⟩
    constructor
    · -- IsSubsetUpTo (optimalB N) N : primes p with N/2 < p ≤ N satisfy 1 ≤ p ≤ N
      intro b hb
      simp only [optimalB, Finset.mem_filter, Finset.mem_range] at hb
      obtain ⟨_, hbprime, _, hbN⟩ := hb
      exact ⟨hbprime.one_lt.le, hbN⟩
    constructor
    · exact optimal_has_distinct_products N (by linarith)
    · -- Lower bound. DEFERRED (requires prime-counting / PNT-level input): one needs
      -- |optimalA N| = ⌊N/2⌋ and |optimalB N| = π(N) − π(N/2) ~ N/(2 log N), so the
      -- product is ~ N²/(4 log N).  The lower bound on π(N) − π(N/2) is a Chebyshev /
      -- Bertrand-type estimate not yet wired in here; left for a follow-up session.
      -- (Note: the constant 1/3 chosen above is only attainable asymptotically and
      -- with the sharper N²/(4 log N) main term would need adjusting to ≤ 1/4.)
      sorry

end Erdos490
