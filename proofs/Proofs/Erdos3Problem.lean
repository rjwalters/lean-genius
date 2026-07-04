/-
  Erdős Problem #3: Arithmetic Progressions in Large Sets

  Source: https://erdosproblems.com/3
  Status: OPEN
  Prize: $5,000

  Statement:
  If A ⊆ ℕ has Σ(1/n : n ∈ A) = ∞, must A contain arbitrarily long
  arithmetic progressions?

  This is equivalent to asking: for all k, is r_k(N) = o(N / log N)?
  where r_k(N) is the maximum size of a subset of {1,...,N} without k-term AP.

  Key Results:
  - Roth (1953): r_3(N) = o(N), first non-trivial bound
  - Szemerédi (1975): r_k(N) = o(N) for all k
  - Gowers (2001): r_k(N) ≪ N / (log log N)^{c_k}
  - Bloom-Sisask (2020): Better bounds for k=3
  - Kelley-Meka (2023): r_3(N) ≪ N / exp((log N)^{1/11})
  - Leng-Sah-Sawhney (2024): r_k(N) ≪ N / exp((log log N)^{c_k})

  The conjecture remains OPEN because current bounds are not strong enough
  to imply r_k(N) = o(N / log N).
-/

import Mathlib

open Set Filter Nat Finset

open scoped Classical
-- Register classical decidability as a genuine local instance for the whole file.
-- Recent Mathlib no longer exposes `Classical.propDecidable` as a resolvable
-- instance from `open scoped Classical` alone, so the `Finset.filter` predicates
-- below (`· ∈ A`, `IsAPFree ↑S k`) fail `DecidablePred` synthesis without this.
attribute [local instance] Classical.propDecidable

namespace Erdos3

/- ## Core Definitions -/

/-- A k-term arithmetic progression starting at a with common difference d.
    Defined via `Finset.image`, which needs no injectivity hypothesis on the
    generating map (the map `i ↦ a + i·d` collapses when `d = 0`; callers that
    care about genuine progressions require `d > 0`). -/
def ArithProg (a d k : ℕ) : Finset ℕ :=
  (Finset.range k).image (fun i => a + i * d)

/-- A set contains a k-term AP if some (a, d) with d > 0 gives a subset -/
def ContainsAP (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, d > 0 ∧ ↑(ArithProg a d k) ⊆ A

/-- A set contains arbitrarily long APs -/
def ContainsArbitrarilyLongAP (A : Set ℕ) : Prop :=
  ∀ k : ℕ, ContainsAP A k

/-- A set is AP-free of length k (avoids k-term APs) -/
def IsAPFree (A : Set ℕ) (k : ℕ) : Prop :=
  ¬ContainsAP A k

/-- The reciprocal sum of a set -/
noncomputable def reciprocalSum (A : Set ℕ) : ℝ :=
  ∑' (n : A), (1 : ℝ) / n

/-- A set has divergent reciprocal sum -/
def HasDivergentSum (A : Set ℕ) : Prop :=
  ¬Summable (fun n : A => (1 : ℝ) / n)

/- ## Roth Function r_k(N) -/

/-- r_k(N) = maximum size of subset of {1,...,N} avoiding k-term APs -/
noncomputable def rothNumber (k N : ℕ) : ℕ :=
  Finset.sup
    ((Finset.range (N + 1)).powerset.filter
      (fun S : Finset ℕ => IsAPFree (↑S : Set ℕ) k))
    Finset.card

/-- The counting function for A up to N -/
noncomputable def countingFunction (A : Set ℕ) (N : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter (· ∈ A)).card

/- ## Key Threshold -/

/-- The conjecture is equivalent to: r_k(N) = o(N / log N) for all k -/
def SublogarithmicGrowth (k : ℕ) : Prop :=
  ∀ c : ℝ, c > 0 → ∀ᶠ N in atTop,
    (rothNumber k N : ℝ) < c * N / Real.log N

/-- Erdős Problem #3: Main Conjecture (OPEN) -/
def Erdos3Conjecture : Prop :=
  ∀ A : Set ℕ, HasDivergentSum A → ContainsArbitrarilyLongAP A

/- ## Historical Results -/

/- ## The Gap -/

/- **The Critical Gap**: Why the conjecture remains open.
    For Erdős' conjecture, we need r_k(N) = o(N / log N).
    But current bounds only give r_k(N) = o(N / exp((log log N)^c)).
    Since exp((log log N)^c) grows slower than log N, there's a gap. -/

/-- The required bound for the conjecture -/
def RequiredBound (k : ℕ) : Prop :=
  ∀ c : ℝ, c > 0 → ∀ᶠ N in atTop,
    (rothNumber k N : ℝ) ≤ c * N / Real.log N

/-- **Bridge lemma (density from AP-freeness).**
    If `A` avoids `k`-term arithmetic progressions, then its counting function up to
    `N` is bounded by the Roth number `r_k(N)`. This turns the *structural* hypothesis
    "`A` is `k`-AP-free" into a *quantitative* density bound, and is the first honest
    step of any proof of `required_bound_implies_conjecture`.

    Proof: the finite slice `A ∩ {0,…,N}` is itself `k`-AP-free (a `k`-AP inside the
    slice would be a `k`-AP inside `A`), hence it is one of the sets over which
    `rothNumber` takes its supremum, so its cardinality is `≤ r_k(N)`.

    This lemma is fully proved (no `sorry`, no new axiom). -/
theorem countingFunction_le_rothNumber (A : Set ℕ) (k N : ℕ)
    (hA : IsAPFree A k) : countingFunction A N ≤ rothNumber k N := by
  -- The slice coerces into `A`, so any AP it contains is an AP of `A`.
  have hSA : (↑((Finset.range (N + 1)).filter (· ∈ A)) : Set ℕ) ⊆ A := by
    intro x hx
    rw [Finset.mem_coe, Finset.mem_filter] at hx
    exact hx.2
  -- The slice is a member of the family `rothNumber` sups over.
  have hmem : ((Finset.range (N + 1)).filter (· ∈ A)) ∈
      ((Finset.range (N + 1)).powerset.filter
        (fun S : Finset ℕ => IsAPFree (↑S : Set ℕ) k)) := by
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.filter_subset _ _, ?_⟩
    intro hAP
    apply hA
    obtain ⟨a, d, hd, hsub⟩ := hAP
    exact ⟨a, d, hd, hsub.trans hSA⟩
  -- Its cardinality is therefore `≤` the supremum, which is `r_k(N)`.
  unfold countingFunction rothNumber
  exact Finset.le_sup hmem

/-- **The analytic gap, made precise.**
    The bound `RequiredBound k` (i.e. `r_k(N) = o(N / log N)`) is *not strong enough*
    to prove `required_bound_implies_conjecture`. Combining the bridge lemma above
    with dyadic (Abel) summation, a `k`-AP-free set `A` satisfies
    `∑_{a ∈ A, a ≤ 2^J} 1/a ≤ ∑_{j} r_k(2^j)·2^{1-j}`. Under `r_k(N) = o(N/log N)`
    the `j`-th term is `o(1/j)`, and `∑ o(1/j)` may still diverge (e.g. the counting
    function `N / (log N · log log N)` is `o(N/log N)` yet has divergent reciprocal
    sum). The genuinely sufficient hypothesis is the stronger
    `r_k(N) = O(N / (log N)^{1+δ})` for some `δ > 0`, which is recorded here as the
    correct threshold for a future proof of the reduction. -/
def StrongRequiredBound (k : ℕ) : Prop :=
  ∃ δ : ℝ, δ > 0 ∧ ∃ C : ℝ, C > 0 ∧ ∀ᶠ N in atTop,
    (rothNumber k N : ℝ) ≤ C * N / (Real.log N) ^ (1 + δ)

/-- If r_k(N) = o(N / log N) for all k, then the conjecture holds.

    OPEN CRUX. See `countingFunction_le_rothNumber` (proved) for the first step and
    `StrongRequiredBound` for why `RequiredBound` alone is insufficient: closing the
    remaining gap requires an analytic (Abel-summation) argument that only goes
    through under a bound of the form `r_k(N) = O(N / (log N)^{1+δ})`. With the
    `RequiredBound` hypothesis exactly as stated the implication is not known to be
    provable. -/
theorem required_bound_implies_conjecture :
    (∀ k : ℕ, k ≥ 3 → RequiredBound k) → Erdos3Conjecture := by
  intro hbound A hdiv
  intro k
  -- If r_k(N) = o(N / log N), then any set with divergent reciprocal sum
  -- cannot avoid k-APs because its counting function grows too fast.
  -- The structural first step (AP-free ⟹ density ≤ r_k(N)) is now the proved lemma
  -- `countingFunction_le_rothNumber`; the remaining step is the analytic summation
  -- gap documented at `StrongRequiredBound`.
  sorry

/- ## Constructive reduction at the `(log N)^{1+δ}` threshold

   `RequiredBound` (the `o(N/log N)` threshold) is not known to imply the
   conjecture (see the `StrongRequiredBound` docstring for the counterexample
   profile). The strictly stronger `StrongRequiredBound` threshold
   `r_k(N) = O(N/(log N)^{1+δ})`, however, *does* imply it, via an honest
   dyadic-blocking + p-series argument. We prove that reduction below as a
   fully machine-checked, 0-axiom conditional theorem. It isolates exactly the
   analytic strength Erdős #3 is missing: the gap between `o(N/log N)` and
   `O(N/(log N)^{1+δ})`. -/

/-- Monotonicity of `ContainsAP` in the length: containing an `m`-term progression
    implies containing every shorter `k`-term progression (`k ≤ m`), since the
    first `k` terms of that progression already lie in `A`. -/
theorem containsAP_of_le {A : Set ℕ} {k m : ℕ} (hkm : k ≤ m)
    (h : ContainsAP A m) : ContainsAP A k := by
  obtain ⟨a, d, hd, hsub⟩ := h
  refine ⟨a, d, hd, subset_trans ?_ hsub⟩
  rw [Finset.coe_subset]
  apply Finset.image_subset_image
  intro x hx
  rw [Finset.mem_range] at hx ⊢
  omega

/-- **A genuine `k`-term AP has exactly `k` elements.**
    When the common difference `d` is positive, the generating map `i ↦ a + i·d`
    is injective on `range k`, so `ArithProg a d k` has cardinality `k`.  (This is
    exactly why `ContainsAP` insists on `d > 0`: without it the progression can
    collapse to a single point.)  A reusable counting fact for turning
    AP-containment into cardinality lower bounds. -/
theorem arithProg_card (a d k : ℕ) (hd : 0 < d) :
    (ArithProg a d k).card = k := by
  have hinj : Function.Injective (fun i => a + i * d) := by
    intro i j hij
    dsimp only at hij
    exact Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel hij)
  unfold ArithProg
  rw [Finset.card_image_of_injective _ hinj, Finset.card_range]

/-- **Only infinite sets contain arbitrarily long APs.**
    If `A` contains a `k`-term arithmetic progression (with positive common
    difference) for every `k`, then `A` is infinite.  Indeed, were `A` finite with
    `n = |A|` elements, the `(n+1)`-term AP it must contain would be an
    `(n+1)`-element subset of `A` (`arithProg_card`), contradicting `|A| = n`.

    A basic sanity check on the *conclusion* of Erdős #3: the property
    `ContainsArbitrarilyLongAP` can only hold for infinite sets, matching the
    hypothesis side (`HasDivergentSum` likewise forces infinitude).  Elementary,
    `sorry`-free and axiom-free. -/
theorem infinite_of_containsArbitrarilyLongAP {A : Set ℕ}
    (h : ContainsArbitrarilyLongAP A) : A.Infinite := by
  by_contra hfin
  rw [Set.not_infinite] at hfin
  obtain ⟨a, d, hd, hsub⟩ := h (hfin.toFinset.card + 1)
  have hsubF : ArithProg a d (hfin.toFinset.card + 1) ⊆ hfin.toFinset := by
    intro x hx
    rw [Set.Finite.mem_toFinset]
    exact hsub (Finset.mem_coe.mpr hx)
  have hcard := Finset.card_le_card hsubF
  rw [arithProg_card a d _ hd] at hcard
  omega

/-- **Divergent reciprocal sum forces infinitude.**
    If `∑_{a ∈ A} 1/a` diverges then `A` is infinite. Contrapositive: a *finite* set
    is a `Fintype`, over which every real-valued family is summable (`hasSum_fintype`),
    so its reciprocal sum converges.

    This is the hypothesis-side companion to `infinite_of_containsArbitrarilyLongAP`
    (the conclusion side): *both* sides of Erdős #3 can only be nontrivial on infinite
    sets. Elementary, `sorry`-free and axiom-free. -/
theorem infinite_of_hasDivergentSum {A : Set ℕ} (h : HasDivergentSum A) :
    A.Infinite := by
  by_contra hfin
  rw [Set.not_infinite] at hfin
  haveI : Fintype ↥A := hfin.fintype
  exact h (hasSum_fintype (fun n : A => (1 : ℝ) / n)).summable

/-- **Two elements make a 2-term AP.**
    Any `a < b` both lying in `A` give the 2-term progression `{a, b}` (common
    difference `b - a > 0`), so `A` contains a 2-term AP. -/
theorem containsAP_two_of_lt {A : Set ℕ} {a b : ℕ} (ha : a ∈ A) (hb : b ∈ A)
    (hab : a < b) : ContainsAP A 2 := by
  refine ⟨a, b - a, by omega, ?_⟩
  intro z hz
  simp only [Finset.mem_coe, ArithProg, Finset.mem_image, Finset.mem_range] at hz
  obtain ⟨i, hi, rfl⟩ := hz
  interval_cases i
  · simpa using ha
  · show a + 1 * (b - a) ∈ A
    have hb' : a + 1 * (b - a) = b := by omega
    rw [hb']; exact hb

/-- **Every infinite set contains a 2-term AP.**
    An infinite set of naturals is nontrivial, so it has two distinct elements, which
    form a 2-term arithmetic progression (`containsAP_two_of_lt`). -/
theorem containsAP_two_of_infinite {A : Set ℕ} (h : A.Infinite) : ContainsAP A 2 := by
  obtain ⟨x, hx, y, hy, hxy⟩ := h.nontrivial
  rcases lt_or_gt_of_ne hxy with hlt | hlt
  · exact containsAP_two_of_lt hx hy hlt
  · exact containsAP_two_of_lt hy hx hlt

/-- **Unconditional base cases of Erdős #3 (lengths `k ≤ 2`).**
    For progressions of length at most `2`, Erdős #3 holds *without any Roth-type
    threshold hypothesis*: a set with divergent reciprocal sum is infinite
    (`infinite_of_hasDivergentSum`), hence already contains a `2`-term — and by length
    monotonicity (`containsAP_of_le`) every `k ≤ 2`-term — arithmetic progression.

    This isolates exactly where the difficulty of Erdős #3 begins: the `k ≤ 2` slice is
    elementary and unconditional, whereas the `k ≥ 3` content needs the analytic
    strength recorded in `strong_required_bound_implies_conjecture`. `sorry`-free and
    axiom-free. -/
theorem erdos3_holds_length_le_two {A : Set ℕ} (h : HasDivergentSum A) {k : ℕ}
    (hk : k ≤ 2) : ContainsAP A k :=
  containsAP_of_le hk (containsAP_two_of_infinite (infinite_of_hasDivergentSum h))

/-- **Analytic core of the reduction.**
    If the counting function of `A` obeys `f_A(N) ≤ C · N / (log N)^{1+δ}` for all
    large `N` (`δ > 0`), then `∑_{a ∈ A} 1/a` converges. Proof by dyadic blocking:
    the reciprocal mass of the block `A ∩ [2^j, 2^{j+1})` is at most
    `f_A(2^{j+1}) / 2^j ≤ 2C / ((j+1)·log 2)^{1+δ}`, the general term of a convergent
    `p`-series (`p = 1 + δ > 1`). -/
theorem summable_of_strongBound {A : Set ℕ} {C δ : ℝ} (hδ : 0 < δ) (hC : 0 < C)
    (hbound : ∀ᶠ N in atTop,
      (countingFunction A N : ℝ) ≤ C * (N : ℝ) / (Real.log N) ^ (1 + δ)) :
    Summable (fun n : A => (1 : ℝ) / (n : ℝ)) := by
  classical
  set F : ℕ → ℝ := fun n => (1 : ℝ) / (n : ℝ) with hF
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set K : ℝ := 2 * C / (Real.log 2) ^ (1 + δ) with hKdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  set g : ℕ → ℝ := fun j => K / ((j : ℝ) + 1) ^ (1 + δ) with hgdef
  have hg_nonneg : ∀ j, 0 ≤ g j := by intro j; rw [hgdef]; positivity
  -- g is summable: it is a constant multiple of a p-series with p = 1 + δ > 1.
  have hg_summable : Summable g := by
    have hp : (1 : ℝ) < 1 + δ := by linarith
    have h1 : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ (1 + δ)) :=
      Real.summable_one_div_nat_rpow.mpr hp
    have h2 : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ (1 + δ)) := by
      have h1' := (summable_nat_add_iff 1).mpr h1
      simpa using h1'
    rw [hgdef]
    simpa [mul_one_div] using h2.mul_left K
  -- Threshold beyond which the counting bound holds.
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hbound
  -- Dyadic block masses.
  set block : ℕ → ℝ := fun j => ∑ i ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), A.indicator F i
    with hblockdef
  -- Every term of block j is ≤ 1/2^j (since 2^j ≤ i).
  have hterm_le : ∀ j, ∀ i ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)),
      A.indicator F i ≤ 1 / (2 : ℝ) ^ j := by
    intro j i hi
    rw [Finset.mem_Ico] at hi
    have h2j : (2 : ℝ) ^ j ≤ (i : ℝ) := by exact_mod_cast hi.1
    by_cases hmem : i ∈ A
    · rw [Set.indicator_of_mem hmem, hF]
      exact one_div_le_one_div_of_le (by positivity) h2j
    · rw [Set.indicator_of_not_mem hmem]; positivity
  -- Crude bound: every block has mass ≤ 1.
  have hcrude : ∀ j, block j ≤ 1 := by
    intro j
    simp only [hblockdef]
    calc ∑ i ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), A.indicator F i
        ≤ ∑ _i ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), (1 / (2 : ℝ) ^ j) :=
          Finset.sum_le_sum (hterm_le j)
      _ = (Finset.Ico (2 ^ j) (2 ^ (j + 1))).card • (1 / (2 : ℝ) ^ j) := by
          rw [Finset.sum_const]
      _ = 1 := by
          rw [Nat.card_Ico, nsmul_eq_mul]
          have hsub : 2 ^ (j + 1) - 2 ^ j = 2 ^ j := by rw [pow_succ]; omega
          rw [hsub, Nat.cast_pow, Nat.cast_ofNat, mul_one_div,
            div_self (by positivity)]
  -- Strong bound: for j ≥ N0, block mass ≤ g j.
  have hstrong : ∀ j, N0 ≤ j → block j ≤ g j := by
    intro j hj
    have hbe : block j
        = ∑ i ∈ (Finset.Ico (2 ^ j) (2 ^ (j + 1))).filter (· ∈ A), F i := by
      simp only [hblockdef, Set.indicator_apply]
      rw [← Finset.sum_filter]
    have hN0le : N0 ≤ 2 ^ (j + 1) :=
      le_trans hj (le_trans (Nat.le_succ j) (Nat.le_of_lt Nat.lt_two_pow_self))
    have hcb := hN0 (2 ^ (j + 1)) hN0le
    have hcard : ((Finset.Ico (2 ^ j) (2 ^ (j + 1))).filter (· ∈ A)).card
        ≤ countingFunction A (2 ^ (j + 1)) := by
      rw [countingFunction]
      apply Finset.card_le_card
      intro x hx
      rw [Finset.mem_filter, Finset.mem_Ico] at hx
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hx.2⟩
    have hlogval : Real.log ((2 ^ (j + 1) : ℕ) : ℝ) = ((j : ℝ) + 1) * Real.log 2 := by
      rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]; push_cast; ring
    have hden : (Real.log ((2 ^ (j + 1) : ℕ) : ℝ)) ^ (1 + δ)
        = ((j : ℝ) + 1) ^ (1 + δ) * (Real.log 2) ^ (1 + δ) := by
      rw [hlogval, Real.mul_rpow (by positivity) (le_of_lt hlog2)]
    have hnum : ((2 ^ (j + 1) : ℕ) : ℝ) = (2 : ℝ) ^ j * 2 := by
      rw [Nat.cast_pow, Nat.cast_ofNat, pow_succ]
    rw [hbe]
    calc ∑ i ∈ (Finset.Ico (2 ^ j) (2 ^ (j + 1))).filter (· ∈ A), F i
        ≤ ∑ _i ∈ (Finset.Ico (2 ^ j) (2 ^ (j + 1))).filter (· ∈ A), (1 / (2 : ℝ) ^ j) := by
          apply Finset.sum_le_sum
          intro i hi
          rw [Finset.mem_filter, Finset.mem_Ico] at hi
          rw [hF]
          exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hi.1.1)
      _ = (((Finset.Ico (2 ^ j) (2 ^ (j + 1))).filter (· ∈ A)).card : ℝ) * (1 / (2 : ℝ) ^ j) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (countingFunction A (2 ^ (j + 1)) : ℝ) * (1 / (2 : ℝ) ^ j) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast hcard
      _ ≤ (C * ((2 ^ (j + 1) : ℕ) : ℝ) / (Real.log ((2 ^ (j + 1) : ℕ) : ℝ)) ^ (1 + δ))
            * (1 / (2 : ℝ) ^ j) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact hcb
      _ = g j := by
          simp only [hgdef, hKdef]
          rw [hden, hnum]
          have ha : (2 : ℝ) ^ j ≠ 0 := by positivity
          have hb : ((j : ℝ) + 1) ^ (1 + δ) ≠ 0 := by positivity
          have hc : (Real.log 2) ^ (1 + δ) ≠ 0 := by positivity
          field_simp
  -- Combine into a uniform partial-sum bound and conclude summability.
  have hcombine : ∀ j, block j ≤ (if j < N0 then (1 : ℝ) else 0) + g j := by
    intro j
    by_cases hjN0 : j < N0
    · simp only [hjN0, if_true]
      linarith [hcrude j, hg_nonneg j]
    · simp only [hjN0, if_false, zero_add]
      exact hstrong j (Nat.le_of_not_lt hjN0)
  have hind0 : A.indicator F 0 = 0 := by simp [Set.indicator_apply, hF]
  have hdyadic : ∀ J : ℕ, ∑ i ∈ Finset.Ico 1 (2 ^ J), A.indicator F i
      = ∑ j ∈ Finset.range J, block j := by
    intro J
    induction J with
    | zero => simp
    | succ J ih =>
      rw [Finset.sum_range_succ, ← ih]
      simp only [hblockdef]
      exact (Finset.sum_Ico_consecutive (A.indicator F)
        (Nat.one_le_pow J 2 (by norm_num))
        (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ J))).symm
  suffices hind : Summable (A.indicator F) by
    exact summable_subtype_iff_indicator.mpr hind
  apply summable_of_sum_range_le (c := (N0 : ℝ) + ∑' j, g j)
  · intro n
    exact Set.indicator_nonneg (fun i _ => by rw [hF]; positivity) n
  · intro M
    have hsubM : Finset.range M ⊆ Finset.range (2 ^ M) := by
      intro x hx
      rw [Finset.mem_range] at hx ⊢
      exact lt_of_lt_of_le hx (Nat.le_of_lt Nat.lt_two_pow_self)
    have hle1 : ∑ i ∈ Finset.range M, A.indicator F i
        ≤ ∑ i ∈ Finset.range (2 ^ M), A.indicator F i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubM
      intro i _ _
      exact Set.indicator_nonneg (fun a _ => by rw [hF]; positivity) i
    have hsplit : ∑ i ∈ Finset.range (2 ^ M), A.indicator F i
        = ∑ i ∈ Finset.Ico 1 (2 ^ M), A.indicator F i := by
      rw [Finset.range_eq_Ico,
        ← Finset.sum_Ico_consecutive (A.indicator F) (Nat.zero_le 1)
          (Nat.one_le_pow M 2 (by norm_num)),
        ← Finset.range_eq_Ico, Finset.sum_range_one, hind0, zero_add]
    calc ∑ i ∈ Finset.range M, A.indicator F i
        ≤ ∑ j ∈ Finset.range M, block j := by rw [← hdyadic M, ← hsplit]; exact hle1
      _ ≤ ∑ j ∈ Finset.range M, ((if j < N0 then (1 : ℝ) else 0) + g j) :=
          Finset.sum_le_sum (fun j _ => hcombine j)
      _ = (∑ j ∈ Finset.range M, (if j < N0 then (1 : ℝ) else 0))
            + ∑ j ∈ Finset.range M, g j := by rw [Finset.sum_add_distrib]
      _ ≤ (N0 : ℝ) + ∑' j, g j := by
          apply _root_.add_le_add
          · rw [Finset.sum_boole]
            have hsub2 : (Finset.range M).filter (· < N0) ⊆ Finset.range N0 := by
              intro x hx
              rw [Finset.mem_filter] at hx
              exact Finset.mem_range.2 hx.2
            calc (((Finset.range M).filter (· < N0)).card : ℝ)
                ≤ ((Finset.range N0).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub2
              _ = (N0 : ℝ) := by rw [Finset.card_range]
          · exact Summable.sum_le_tsum _ (fun j _ => hg_nonneg j) hg_summable

/-- **The reduction actually goes through at the `(log N)^{1+δ}` threshold.**
    If `r_k(N) = O(N / (log N)^{1+δ})` for some `δ > 0` and every `k ≥ 3`
    (`StrongRequiredBound`), then Erdős #3 holds: every set with divergent
    reciprocal sum contains arbitrarily long arithmetic progressions.

    This is a fully machine-checked, `sorry`-free, axiom-free conditional theorem.
    The proof: a length-`m` AP-free set has counting function bounded by `r_m(N)`
    (`countingFunction_le_rothNumber`), hence `= O(N/(log N)^{1+δ})`, hence has a
    *convergent* reciprocal sum (`summable_of_strongBound`) — contradicting
    divergence. Contrast `required_bound_implies_conjecture`, whose `o(N/log N)`
    hypothesis is *not* known to suffice: the gap between the two thresholds is
    exactly the open content of Erdős #3. -/
theorem strong_required_bound_implies_conjecture :
    (∀ k : ℕ, k ≥ 3 → StrongRequiredBound k) → Erdos3Conjecture := by
  intro hbound A hdiv k
  apply containsAP_of_le (le_max_left k 3)
  by_contra hAPfree
  have hApf : IsAPFree A (max k 3) := hAPfree
  obtain ⟨δ, hδ, C, hC, hev⟩ := hbound (max k 3) (le_max_right k 3)
  have hcount : ∀ᶠ N in atTop,
      (countingFunction A N : ℝ) ≤ C * (N : ℝ) / (Real.log N) ^ (1 + δ) := by
    filter_upwards [hev] with N hN
    calc (countingFunction A N : ℝ) ≤ (rothNumber (max k 3) N : ℝ) := by
          exact_mod_cast countingFunction_le_rothNumber A (max k 3) N hApf
      _ ≤ C * (N : ℝ) / (Real.log N) ^ (1 + δ) := hN
  exact hdiv (summable_of_strongBound hδ hC hcount)

/-- **The strong threshold dominates the weak one.**
    `StrongRequiredBound k` (`r_k(N) = O(N/(log N)^{1+δ})` for some `δ > 0`) implies the
    weaker `RequiredBound k` (`r_k(N) = o(N/log N)`). Writing the strong bound as
    `r_k(N) ≤ (C/(log N)^δ) · (N/log N)` and using `1/(log N)^δ → 0`, the leading
    factor `C/(log N)^δ` eventually drops below any prescribed `c > 0`, so
    `r_k(N) ≤ c·N/log N` eventually.

    This makes precise the ordering asserted in the `StrongRequiredBound` docstring:
    the two thresholds bracketing Erdős #3 are genuinely comparable, with
    `StrongRequiredBound ⇒ RequiredBound`. The *converse* is exactly the open content
    of the problem — it is precisely the gap that keeps `required_bound_implies_conjecture`
    a `sorry` while `strong_required_bound_implies_conjecture` is fully proved.
    Fully machine-checked, `sorry`-free, axiom-free. -/
theorem strongRequiredBound_implies_requiredBound {k : ℕ}
    (h : StrongRequiredBound k) : RequiredBound k := by
  obtain ⟨δ, hδ, C, hC, hev⟩ := h
  intro c hc
  -- `log N → ∞` along `N → ∞`, hence `(log N)^(-δ) → 0` and `C·(log N)^(-δ) → 0`.
  have hlog : Filter.Tendsto (fun N : ℕ => Real.log (N : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hneg : Filter.Tendsto (fun N : ℕ => C * (Real.log (N : ℝ)) ^ (-δ))
      Filter.atTop (nhds 0) := by
    have hmul := ((tendsto_rpow_neg_atTop hδ).comp hlog).const_mul C
    simpa using hmul
  -- Eventually the leading factor is below `c`, and `log N > 0`.
  have hlt : ∀ᶠ N : ℕ in Filter.atTop, C * (Real.log (N : ℝ)) ^ (-δ) < c := by
    have hmem : Set.Iio c ∈ nhds (0 : ℝ) := isOpen_Iio.mem_nhds hc
    filter_upwards [hneg.eventually hmem] with N hN using hN
  have hLpos : ∀ᶠ N : ℕ in Filter.atTop, 0 < Real.log (N : ℝ) :=
    hlog.eventually (eventually_gt_atTop 0)
  filter_upwards [hev, hlt, hLpos] with N hN hNlt hL
  set L : ℝ := Real.log (N : ℝ) with hLdef
  have hP : (0 : ℝ) < L ^ δ := Real.rpow_pos_of_pos hL δ
  have hsplit : L ^ (1 + δ) = L ^ δ * L := by
    rw [add_comm, Real.rpow_add hL, Real.rpow_one]
  -- Turn the leading-factor bound `C · L^(-δ) < c` into `C ≤ c · L^δ`.
  rw [Real.rpow_neg hL.le, ← div_eq_mul_inv] at hNlt
  have hCle : C ≤ c * L ^ δ := (div_le_iff₀ hP).mp hNlt.le
  -- Clear denominators and finish by nonnegativity of `N·L·(c·L^δ − C)`.
  refine le_trans hN ?_
  rw [hsplit, div_le_div_iff₀ (by positivity) hL]
  have hfac : 0 ≤ (N : ℝ) * L * (c * L ^ δ - C) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg N) hL.le) (by linarith)
  nlinarith [hfac]

/-- **The two `o(N/log N)` formulations in this file coincide.**
    `RequiredBound k` (a non-strict `r_k(N) ≤ c·N/log N` for every `c > 0`) is
    equivalent to `SublogarithmicGrowth k` (the strict `r_k(N) < c·N/log N`). The
    strict form trivially gives the non-strict one; conversely, applying the
    non-strict bound with `c/2` yields `r_k(N) ≤ (c/2)·N/log N < c·N/log N` once
    `N ≥ 2` (so `N/log N > 0`). This records that the file's two spellings of the
    `o(N/log N)` threshold are interchangeable. Fully machine-checked, axiom-free. -/
theorem requiredBound_iff_sublogarithmicGrowth {k : ℕ} :
    RequiredBound k ↔ SublogarithmicGrowth k := by
  constructor
  · intro h c hc
    filter_upwards [h (c / 2) (by linarith), eventually_ge_atTop 2] with N hN hN2
    have hLpos : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < N))
    have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have hpos : 0 < (N : ℝ) / Real.log (N : ℝ) := div_pos hN0 hLpos
    have hstrict : (c / 2) * (N : ℝ) / Real.log (N : ℝ)
        < c * (N : ℝ) / Real.log (N : ℝ) := by
      rw [mul_div_assoc, mul_div_assoc]
      exact mul_lt_mul_of_pos_right (by linarith) hpos
    exact lt_of_le_of_lt hN hstrict
  · intro h c hc
    filter_upwards [h c hc] with N hN using hN.le

/- ## Equivalent Formulations -/

/- **Equivalent to Behrend-type bounds**: The conjecture asks whether
    Behrend's construction cannot be improved to achieve N / log N density. -/

/- ## Green-Tao Connection -/

/-- The primes have divergent reciprocal sum (Euler, 1737).

    Previously an `axiom`; now discharged from Mathlib's
    `not_summable_one_div_on_primes` (`∑ 1/p` over primes diverges). The set-subtype
    form `HasDivergentSum {p | p.Prime}` matches Mathlib's `Set.indicator` form via
    `summable_subtype_iff_indicator`, so this is a fully machine-checked, 0-axiom
    theorem — one fewer assumption in the file. -/
theorem euler_prime_sum_diverges :
    HasDivergentSum { p : ℕ | Nat.Prime p } := by
  have h := not_summable_one_div_on_primes
  rwa [← summable_subtype_iff_indicator] at h

/-- If Erdős #3 were true, Green-Tao would be a corollary -/
theorem erdos3_implies_green_tao :
    Erdos3Conjecture → ContainsArbitrarilyLongAP { p : ℕ | Nat.Prime p } := by
  intro hconj
  exact hconj { p : ℕ | Nat.Prime p } euler_prime_sum_diverges

/- ## Small Examples -/

/-- 3-term AP: {a, a+d, a+2d} -/
example : ArithProg 1 2 3 = {1, 3, 5} := by decide

/-- 4-term AP: {a, a+d, a+2d, a+3d} -/
example : ArithProg 2 3 4 = {2, 5, 8, 11} := by decide

/- The set {1, 2, 4, 5, 10, 11, 13, 14} is 3-AP-free (Roth's example);
   this is a classic construction avoiding 3-term APs. -/

/- ## Problem Status -/

/-- **Erdős Problem #3: OPEN ($5,000 prize)**

The conjecture that every set with divergent reciprocal sum contains
arbitrarily long arithmetic progressions remains unresolved.

**What we know:**
- Szemerédi (1975): Positive density implies all APs ✓
- Gowers (2001): Improved density bounds
- Kelley-Meka (2023): Near-optimal for k=3
- Leng-Sah-Sawhney (2024): Best general bounds

**What we need:**
- Prove r_k(N) = o(N / log N) for all k, OR
- Find a counterexample: a set with divergent sum avoiding some k-AP

**Difficulty:**
- The current gap between constructions (≈ N/exp(√log N)) and
  required bound (N/log N) seems very hard to close.
- Neither a proof nor counterexample appears within reach.

References:
- Bloom, Sisask (2020): "Breaking the logarithmic barrier"
- Kelley, Meka (2023): "Strong bounds for 3-progressions"
- Leng, Sah, Sawhney (2024): "Improved bounds for Szemerédi's theorem"
-/
theorem erdos_3_open : Erdos3Conjecture ∨ ¬Erdos3Conjecture := by
  exact Classical.em Erdos3Conjecture


end Erdos3
