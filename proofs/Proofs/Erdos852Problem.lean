-- Erdős Problem #852 — Maximal Runs of Distinct Consecutive Prime Gaps
--
-- Let dₙ = pₙ₊₁ − pₙ be the n-th prime gap. Define h(x) as the maximal
-- length such that for some n with pₙ < x, the gaps dₙ, dₙ₊₁, ..., dₙ₊ₕ₍ₓ₎₋₁
-- are all distinct.
--
-- Erdős asked:
-- (1) Is h(x) > (log x)^c for some constant c > 0?
-- (2) Is h(x) = o(log x)?
--
-- Brun's sieve implies h(x) → ∞ as x → ∞.
--
-- Status: OPEN
-- Reference: erdosproblems.com/852, Er85c

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

open Filter Asymptotics Real

-- ## Prime Sequence and Gaps (PROVED from Mathlib)

/-- The n-th prime (0-indexed: nthPrime 0 = 2, nthPrime 1 = 3, ...).
    Previously axiomatized; now defined using Mathlib's Nat.nth. -/
noncomputable def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

theorem nthPrime_prime (n : ℕ) : Nat.Prime (nthPrime n) :=
  Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n

theorem nthPrime_strictMono : StrictMono nthPrime :=
  fun _ _ h => Nat.nth_strictMono Nat.infinite_setOf_prime h

theorem nthPrime_initial : nthPrime 0 = 2 ∧ nthPrime 1 = 3 :=
  ⟨by unfold nthPrime; exact Nat.nth_prime_zero_eq_two,
   by unfold nthPrime; exact Nat.nth_prime_one_eq_three⟩

/-- The n-th prime gap: dₙ = pₙ₊₁ − pₙ -/
noncomputable def primeGap (n : ℕ) : ℕ := nthPrime (n + 1) - nthPrime n

/-- Prime gaps are positive (since nthPrime is strictly monotone). -/
theorem primeGap_pos (n : ℕ) : 0 < primeGap n := by
  unfold primeGap
  have h : nthPrime n < nthPrime (n + 1) := nthPrime_strictMono (by omega)
  omega

/-- nthPrime is monotone (follows from strict monotonicity). -/
theorem nthPrime_mono : Monotone nthPrime :=
  nthPrime_strictMono.monotone

/-- nthPrime n ≥ 2 for all n (all primes are ≥ 2). -/
theorem nthPrime_ge_two (n : ℕ) : nthPrime n ≥ 2 :=
  (nthPrime_prime n).two_le

/-- The first prime gap d₀ = p₁ - p₀ = 3 - 2 = 1. -/
theorem primeGap_zero : primeGap 0 = 1 := by
  unfold primeGap
  have := nthPrime_initial
  rw [this.1, this.2]

-- ## Distinct Gap Runs

/-- A run of gaps starting at index n has all distinct values up to length k. -/
def IsDistinctRun (n k : ℕ) : Prop :=
  ∀ i j : ℕ, i < k → j < k → i ≠ j → primeGap (n + i) ≠ primeGap (n + j)

/-- An empty run is trivially distinct. -/
theorem isDistinctRun_zero (n : ℕ) : IsDistinctRun n 0 := by
  intro i j hi; omega

/-- A single-element run is always distinct. -/
theorem isDistinctRun_one (n : ℕ) : IsDistinctRun n 1 := by
  intro i j hi hj hne; omega

/-- If a run of length k is distinct, then any prefix is distinct. -/
theorem isDistinctRun_prefix (n k₁ k₂ : ℕ) (h : k₁ ≤ k₂)
    (hk : IsDistinctRun n k₂) : IsDistinctRun n k₁ := by
  intro i j hi hj hne
  exact hk i j (lt_of_lt_of_le hi h) (lt_of_lt_of_le hj h) hne

/-- Combining: IsDistinctRun is downward-closed in k. -/
theorem isDistinctRun_le {n k₁ k₂ : ℕ} (hle : k₁ ≤ k₂)
    (h : IsDistinctRun n k₂) : IsDistinctRun n k₁ :=
  isDistinctRun_prefix n k₁ k₂ hle h

-- ## h(x): Maximal Distinct Run Length (DEFINED)
--
-- Previously axiomatized with 4 axioms (function + witness + optimality + bound).
-- Now defined as sSup of achievable distinct run lengths bounded by x,
-- with all three properties proved from the definition.

/-- The set of achievable distinct run lengths for primes below x, bounded by x. -/
private def validRunLengths (x : ℕ) : Set ℕ :=
  {k : ℕ | k ≤ x ∧ ∃ n, nthPrime n < x ∧ IsDistinctRun n k}

private lemma validRunLengths_bddAbove (x : ℕ) : BddAbove (validRunLengths x) :=
  ⟨x, fun _ hk => hk.1⟩

private lemma validRunLengths_nonempty (x : ℕ) (hx : 3 ≤ x) :
    (validRunLengths x).Nonempty :=
  ⟨0, Nat.zero_le x, 0, by have := nthPrime_initial.1; omega, isDistinctRun_zero 0⟩

private lemma validRunLengths_empty_of_le_two (x : ℕ) (hx : x ≤ 2) :
    validRunLengths x = ∅ := by
  ext k
  simp only [validRunLengths, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro _; rintro ⟨n, hn, -⟩
  exact absurd hn (by have := nthPrime_ge_two n; omega)

private lemma validRunLengths_mono {x y : ℕ} (hxy : x ≤ y) :
    validRunLengths x ⊆ validRunLengths y :=
  fun _ ⟨hkx, n, hn, hd⟩ => ⟨le_trans hkx hxy, n, lt_of_lt_of_le hn hxy, hd⟩

/-- In ℕ, the supremum of a nonempty bounded-above set is a member
    (since bounded subsets of ℕ are finite and have a maximum). -/
private lemma nat_sSup_mem {s : Set ℕ} (hne : s.Nonempty) (hba : BddAbove s) :
    sSup s ∈ s := by
  by_contra hmem
  have hlt : ∀ b ∈ s, b < sSup s := fun b hb =>
    lt_of_le_of_ne (le_csSup hba hb) (fun h => hmem (h ▸ hb))
  have hpos : 1 ≤ sSup s := by obtain ⟨a, ha⟩ := hne; have := hlt a ha; omega
  have : sSup s ≤ sSup s - 1 :=
    csSup_le hne (fun b hb => by have := hlt b hb; omega)
  omega

/-- h(x): maximal length of a run of distinct consecutive gaps
    among primes pₙ < x. Defined as the supremum of achievable
    distinct run lengths bounded by x. -/
noncomputable def maxDistinctRun (x : ℕ) : ℕ :=
  sSup (validRunLengths x)

/-- h(x) is achieved by some starting index with pₙ < x. -/
theorem maxDistinctRun_witness (x : ℕ) (hx : 3 ≤ x) :
    ∃ n : ℕ, nthPrime n < x ∧ IsDistinctRun n (maxDistinctRun x) :=
  (nat_sSup_mem (validRunLengths_nonempty x hx) (validRunLengths_bddAbove x)).2

/-- h(x) is maximal among run lengths ≤ x. -/
theorem maxDistinctRun_optimal (x : ℕ) (n k : ℕ)
    (hn : nthPrime n < x) (hk : IsDistinctRun n k) (hle : k ≤ x) :
    k ≤ maxDistinctRun x :=
  le_csSup (validRunLengths_bddAbove x) (show k ∈ validRunLengths x from ⟨hle, n, hn, hk⟩)

-- ## Properties of h(x)

/-- h(x) ≥ 1 for x ≥ 3 (there always exists at least a single gap). -/
theorem maxDistinctRun_ge_one (x : ℕ) (hx : 3 ≤ x) :
    1 ≤ maxDistinctRun x := by
  have h2 : nthPrime 0 < x := by
    have := nthPrime_initial.1; omega
  exact maxDistinctRun_optimal x 0 1 h2 (isDistinctRun_one 0) (by omega)

/-- h(x) is non-decreasing: if x ≤ y, then h(x) ≤ h(y). -/
theorem maxDistinctRun_mono (x y : ℕ) (hx : 2 ≤ x) (hxy : x ≤ y) :
    maxDistinctRun x ≤ maxDistinctRun y := by
  unfold maxDistinctRun
  by_cases hx3 : 3 ≤ x
  · exact csSup_le_csSup (validRunLengths_bddAbove y) (validRunLengths_nonempty x hx3)
      (validRunLengths_mono hxy)
  · rw [validRunLengths_empty_of_le_two x (by omega), csSup_empty]
    exact bot_le

-- ## Brun's Sieve Result

/-- Brun's sieve: h(x) → ∞ as x → ∞.
    For any bound C, there exists X such that h(x) ≥ C for all x ≥ X. -/
axiom brun_sieve_divergence :
  ∀ C : ℕ, ∃ X : ℕ, ∀ x : ℕ, X ≤ x → C ≤ maxDistinctRun x

/-- Brun's result in filter form: h tends to infinity. -/
theorem maxDistinctRun_tendsto_atTop :
    Tendsto (fun x : ℕ => (maxDistinctRun x : ℝ)) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  obtain ⟨C, hC⟩ := exists_nat_ge b
  obtain ⟨X, hX⟩ := brun_sieve_divergence C
  exact ⟨X, fun x hx => le_trans hC (Nat.cast_le.mpr (hX x hx))⟩

-- ## Erdős Conjectures (OPEN)

/-- Erdős Problem 852, Part 1 (OPEN): h(x) > (log x)^c for some c > 0.
    Formalized: ∃ c > 0, eventually (log x)^c < h(x). -/
axiom erdos852_lower_bound :
  ∃ c : ℝ, 0 < c ∧
    ∀ᶠ (x : ℕ) in atTop,
      (Real.log (x : ℝ)) ^ c < (maxDistinctRun x : ℝ)

/-- Erdős Problem 852, Part 2 (OPEN): h(x) = o(log x).
    Formalized using Asymptotics.IsLittleO. -/
axiom erdos852_upper_bound :
  (fun x : ℕ => (maxDistinctRun x : ℝ)) =o[atTop] (fun x : ℕ => Real.log (x : ℝ))

/-- The upper bound implies h(x) ≤ ε · log x for any ε > 0, eventually. -/
theorem erdos852_upper_eventually (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ (x : ℕ) in atTop,
      ‖(maxDistinctRun x : ℝ)‖ ≤ ε * ‖Real.log (x : ℝ)‖ :=
  erdos852_upper_bound.def hε

/-- Combined growth rate (OPEN): h(x) is between (log x)^c and o(log x),
    placing it strictly between polynomial-in-log and logarithmic growth. -/
theorem erdos852_growth_rate :
    (∃ c : ℝ, 0 < c ∧
      ∀ᶠ (x : ℕ) in atTop, (Real.log (x : ℝ)) ^ c < (maxDistinctRun x : ℝ)) ∧
    (fun x : ℕ => (maxDistinctRun x : ℝ)) =o[atTop] (fun x : ℕ => Real.log (x : ℝ)) :=
  ⟨erdos852_lower_bound, erdos852_upper_bound⟩

-- ## Upper Bound

/-- h(x) ≤ x (follows from the definition: the supremum is taken
    over run lengths bounded by x). -/
theorem maxDistinctRun_le_x (x : ℕ) (hx : 2 ≤ x) :
    maxDistinctRun x ≤ x := by
  unfold maxDistinctRun
  by_cases hx3 : 3 ≤ x
  · exact csSup_le (validRunLengths_nonempty x hx3) (fun _ hk => hk.1)
  · rw [validRunLengths_empty_of_le_two x (by omega), csSup_empty]
    exact bot_le

/-- If all gaps in a distinct run of length k are ≤ M, then k ≤ M
    (by pigeonhole: k distinct positive values in {1, ..., M} implies k ≤ M).
    Previously axiomatized; now proved via Finset.card_image_of_injOn. -/
theorem distinct_run_bounded_by_max_gap (n k M : ℕ)
    (hk : IsDistinctRun n k)
    (hbound : ∀ i, i < k → primeGap (n + i) ≤ M)
    (hpos : ∀ i, i < k → 0 < primeGap (n + i)) :
    k ≤ M := by
  -- The k values primeGap(n+i) for i < k are distinct elements of Icc 1 M
  have hinj : Set.InjOn (fun i => primeGap (n + i)) (↑(Finset.range k)) := by
    intro a ha b hb heq
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    by_contra hne
    exact hk a b ha hb hne heq
  have hsub : (Finset.range k).image (fun i => primeGap (n + i)) ⊆ Finset.Icc 1 M := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [Finset.mem_range] at hi
    exact Finset.mem_Icc.mpr ⟨hpos i hi, hbound i hi⟩
  calc k = (Finset.range k).card := (Finset.card_range k).symm
    _ = ((Finset.range k).image (fun i => primeGap (n + i))).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.Icc 1 M).card := Finset.card_le_card hsub
    _ = M := by rw [Finset.card_Icc]; omega
