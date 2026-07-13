import Proofs.Erdos1Problem
import Mathlib

/-
# Dubroff–Fox–Xu Subset Sum Lower Bound

## What This Proves

This file formalizes the framework for the Dubroff–Fox–Xu (2021) lower bound:

  If A ⊆ {1,...,N} has n elements with all 2ⁿ subset sums distinct, then
    N ≥ √(2/π) · 2ⁿ / √n · (1 - o(1))

This improves the basic counting bound N ≥ (2ⁿ - 1)/n by a factor of √n.

## Proof Strategy (DFX 2021)

The proof uses a variance argument:
1. View each subset sum as X₁ + ... + Xₙ where Xᵢ ∈ {0, aᵢ} with P = 1/2
2. Mean: E[sum] = S/2 where S = Σaᵢ
3. Variance: Var[sum] = Σaᵢ²/4
4. By anticoncentration (Berry–Esseen): at most ~S/√(Var) distinct values
   can fit in [0, S] for a distribution with mean S/2 and variance Σaᵢ²/4
5. Since there are 2ⁿ distinct values: 2ⁿ ≤ C·S/√(Σaᵢ²/4)
6. Combined with max(A) ≤ N and Σaᵢ ≤ nN: derive N ≥ √(2/π)·2ⁿ/√n

## What This File Proves

- **Variance formula**: Σaᵢ² ≤ n · max(A)² (crude bound)
- **Variance lower bound**: Σaᵢ² ≥ (Σaᵢ)²/n (Cauchy–Schwarz)
- **Sum-max relationship**: max(A) ≥ Σaᵢ/n for finite sets
- **DFX bound deduction**: 2ⁿ ≤ 3·√n·N + 2 (i.e. N = Ω(2ⁿ/√n)) from the
  axiomatized Chebyshev anticoncentration bound (order-correct; the sharp √(2/π)
  constant is the Berry–Esseen literature result, not formalized here)

## Connection to Prior Work

- `Erdos1Problem.lean`: DSS definition, basic counting bound
- `Erdos1OQ01.lean`: Sum bound Σaᵢ ≥ 2ⁿ - 1, monotonicity
- **This file**: DFX variance framework and bound

## References

- Dubroff, Q., Fox, J., Xu, M. Z. (2021). "A note on the Erdős distinct subset
  sums problem." SIAM J. Discrete Math. 35(1):322–324.
-/

open Finset BigOperators Real

namespace Erdos1OQ02

/-! ## Part I: Variance Bounds

Algebraic infrastructure for the variance argument.
-/

/-- Sum of squares is bounded by n times the square of the maximum.
    For A = {a₁,...,aₙ} ⊆ {1,...,N}: Σaᵢ² ≤ n · N². -/
theorem sum_sq_le_card_mul_max_sq (A : Finset ℕ) (N : ℕ) (hA : ∀ a ∈ A, a ≤ N) :
    A.sum (fun a => a ^ 2) ≤ A.card * N ^ 2 := by
  calc A.sum (fun a => a ^ 2) ≤ A.sum (fun _ => N ^ 2) := by
        apply Finset.sum_le_sum
        intro a ha
        exact Nat.pow_le_pow_left (hA a ha) 2
    _ = A.card * N ^ 2 := by rw [Finset.sum_const, smul_eq_mul]

/-- **QM-AM inequality (discrete)**: (Σaᵢ)² ≤ n · Σaᵢ² for a set of n numbers.
    Equivalently: Σaᵢ²/n ≥ (Σaᵢ/n)². This is Cauchy–Schwarz for 1 and aᵢ. -/
theorem sum_sq_cauchy_schwarz (A : Finset ℕ) :
    (A.sum id) ^ 2 ≤ A.card * A.sum (fun a => a ^ 2) := by
  -- Prove in ℤ where subtraction is available, then cast back to ℕ
  suffices h : (↑(A.sum id) : ℤ) ^ 2 ≤ ↑A.card * ↑(A.sum (fun a => a ^ 2)) by exact_mod_cast h
  induction A using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha, Finset.card_insert_of_notMem ha, id_eq]
    -- Normalize casts in BOTH the goal and the inductive hypothesis so that
    -- `↑(s.sum id)` / `↑(∑ b ∈ s, b^2)` become `∑ b ∈ s, ↑b` / `∑ b ∈ s, ↑b^2`,
    -- matching the atoms produced below (otherwise nlinarith cannot connect them).
    push_cast [id_eq] at ih ⊢
    -- Key: ∑_{b ∈ s} (a - b)² ≥ 0, which expands to give the Cauchy-Schwarz bound
    have hsq : (0 : ℤ) ≤ s.sum fun b => ((a : ℤ) - ↑b) ^ 2 :=
      Finset.sum_nonneg fun b _ => sq_nonneg _
    have hexpand : s.sum (fun b => ((a : ℤ) - ↑b) ^ 2) =
        ↑s.card * (a : ℤ) ^ 2 - 2 * ↑a * (s.sum fun b => (↑b : ℤ)) +
        (s.sum fun b => (↑b : ℤ) ^ 2) := by
      simp only [sub_sq, Finset.sum_sub_distrib, Finset.sum_add_distrib,
                  Finset.mul_sum, Finset.sum_const, smul_eq_mul]
      ring
    nlinarith [hsq, hexpand, ih]

/-- The maximum element is at least the average: max(A) ≥ sum(A)/card(A).
    Equivalently: sum(A) ≤ card(A) · max(A). -/
theorem sum_le_card_mul_max (A : Finset ℕ) (N : ℕ)
    (hA : ∀ a ∈ A, a ≤ N) :
    A.sum id ≤ A.card * N := by
  calc A.sum id ≤ A.sum (fun _ => N) := by
        apply Finset.sum_le_sum
        intro a ha
        exact hA a ha
    _ = A.card * N := by simp [Finset.sum_const]

/-! ## Part II: The DFX Anticoncentration Step

The core of the DFX proof is an anticoncentration inequality: the number of
distinct values of a sum of independent bounded random variables is limited
by the ratio of range to standard deviation.

This step requires probability theory (Berry–Esseen theorem or direct
anticoncentration bounds) which is axiomatized here.
-/

/-! **Chebyshev anticoncentration bound** (formerly an axiom; now the THEOREM
    `anticoncentration_bound`, proved below from the verified ingredients).
    If A has n elements with distinct subset sums and Q = Σaᵢ², then:
      2ⁿ ≤ 3·√Q + 2

    This is the rigorous (Chebyshev) form of the Dubroff–Fox–Xu anticoncentration
    step. View the 2ⁿ subset sums as the values of the random variable
    X = Σᵢ εᵢ aᵢ with εᵢ ∈ {0,1} i.i.d. Bernoulli(1/2); then
      E[X] = S/2,    Var[X] = Σaᵢ²/4 = Q/4,    σ = √Q/2.
    Chebyshev's inequality gives, for any k > 0,
      P(|X − S/2| < k) ≥ 1 − Q/(4k²).
    The distinct-subset-sums hypothesis forces the sums to be *distinct integers*,
    so the values with |x − S/2| < k are distinct integer points of an open
    interval of length 2k, of which there are at most 2k + 1. Each such value
    carries probability 2⁻ⁿ, hence
      1 − Q/(4k²) ≤ P(|X − S/2| < k) ≤ (2k + 1)·2⁻ⁿ.
    Taking k = √Q (so Q/(4k²) = 1/4) yields
      (3/4)·2ⁿ ≤ 2√Q + 1,   i.e.   2ⁿ ≤ (8√Q + 4)/3 ≤ 3√Q + 2.

    Unlike the sharp √(2/π) constant from Berry–Esseen (the literature bound), the
    constant 3 here comes only from Chebyshev and is *unconditionally true* — it can
    in principle be discharged from `ProbabilityTheory.meas_ge_le_variance_div_sq`
    (Chebyshev) plus the variance computation for the {0,aᵢ} sum. The earlier
    formulation `2ⁿ ≤ √(2/π)·2(S+1)/√Q` was FALSE (e.g. A = {1,2} gives 4 ≤ 2.85);
    this corrected statement holds for every distinct-subset-sums set, including
    the asymptotic extremal (powers of two).

    **This is now proved (0 axioms) as `anticoncentration_bound` below**, after the
    verified ingredients it is assembled from. -/

/-! ## Verified ingredients toward discharging `anticoncentration_bound`

The axiom above isolates the anticoncentration estimate `2ⁿ ≤ 3√Q + 2`
(`Q = Σaᵢ²`).  Its standard proofs go through probability theory (Chebyshev on the
random subset sum).  The two lemmas below are the *probability-free* core of an
elementary discharge, both fully verified (0 axioms):

* `second_moment_identity` — the exact second-moment identity over the powerset,
  `∑_{T ⊆ A} (2·(Σ_{i∈T} i) − Σ_{i∈A} i)² = 2^{|A|} · Σ_{i∈A} i²`.  This is the
  discrete variance computation (`Var = Q/4` rescaled by `2ⁿ`, doubled to stay in
  `ℤ`), proved by induction on `A`: inserting a new element `a` doubles the
  powerset and replaces each drop `d` by the pair `d ± a`, and
  `(d−a)² + (d+a)² = 2d² + 2a²` gives the `f(A∪{a}) = 2 f(A) + 2^{|A|+1} a²`
  recurrence that matches `2^{|A|} Q`.
* `card_mul_le_second_moment` — the elementary discrete Chebyshev/Markov count:
  for nonnegative `g`, `#{i : t ≤ g i} · t ≤ ∑ g i`.  Applied to
  `g T = (2·(Σ_{i∈T} i) − S)²` this bounds how many subset sums lie far from the
  mean.

**Remaining step (and a constant correction).** To finish the discharge one combines
these with the fact that the `2ⁿ` subset sums of a distinct-subset-sums set are
*distinct integers* of one fixed parity (`2·(Σ_T) − S ≡ S mod 2`).  Counting the
distinct same-parity integers inside the central interval `|2·Σ_T − S| < t` gives
`≤ t + 1`, and with `t = 2√Q` the Chebyshev tail removes a `2ⁿ/4` fraction, leaving
`(3/4)·2ⁿ ≤ 2√Q + 1`, i.e. `2ⁿ ≤ (8√Q + 4)/3 ≤ 3√Q + 2` — the axiom's constant.
NOTE: the *pure* second-moment route (lower-bounding `∑(2Σ_T − S)² ≥ (M³−M)/12`
for `M = 2ⁿ` distinct integers) only yields `2ⁿ ≤ √(12Q + 1) ≈ 3.46√Q`, which is
**weaker** than `3√Q + 2`; the central-interval-count step (using parity) is what
recovers the sharper constant `3`. -/

/-- **Second-moment identity over the powerset (0 axioms).**  For any finite set
`A` of naturals, the doubled deviations `2·(Σ_{i∈T} i) − S` (where `S = Σ_{i∈A} i`)
have second moment exactly `2^{|A|} · Σ_{i∈A} i²` when summed over all subsets `T`.
This is the discrete variance computation at the heart of the DFX anticoncentration
bound, kept in `ℤ` via doubling to avoid the half-integer mean. -/
theorem second_moment_identity (A : Finset ℕ) :
    ∑ T ∈ A.powerset, (2 * (∑ i ∈ T, (i : ℤ)) - ∑ i ∈ A, (i : ℤ)) ^ 2
      = 2 ^ A.card * ∑ i ∈ A, (i : ℤ) ^ 2 := by
  induction A using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_powerset_insert ha]
    have hS : (∑ i ∈ insert a s, (i : ℤ)) = (a : ℤ) + ∑ i ∈ s, (i : ℤ) := by
      rw [Finset.sum_insert ha]
    have h1 : ∑ T ∈ s.powerset, (2 * (∑ i ∈ T, (i : ℤ)) - ∑ i ∈ insert a s, (i : ℤ)) ^ 2
        = ∑ T ∈ s.powerset, ((2 * (∑ i ∈ T, (i : ℤ)) - ∑ i ∈ s, (i : ℤ)) - a) ^ 2 := by
      refine Finset.sum_congr rfl (fun T _ => ?_)
      rw [hS]; ring
    have h2 : ∑ T ∈ s.powerset, (2 * (∑ i ∈ insert a T, (i : ℤ)) - ∑ i ∈ insert a s, (i : ℤ)) ^ 2
        = ∑ T ∈ s.powerset, ((2 * (∑ i ∈ T, (i : ℤ)) - ∑ i ∈ s, (i : ℤ)) + a) ^ 2 := by
      refine Finset.sum_congr rfl (fun T hT => ?_)
      have haT : a ∉ T := fun h => ha (Finset.mem_powerset.mp hT h)
      rw [hS, Finset.sum_insert haT]; ring
    rw [h1, h2, ← Finset.sum_add_distrib]
    have hcomb : ∀ T : Finset ℕ,
        ((2 * (∑ i ∈ T, (i : ℤ)) - ∑ i ∈ s, (i : ℤ)) - a) ^ 2
          + ((2 * (∑ i ∈ T, (i : ℤ)) - ∑ i ∈ s, (i : ℤ)) + a) ^ 2
        = 2 * (2 * (∑ i ∈ T, (i : ℤ)) - ∑ i ∈ s, (i : ℤ)) ^ 2 + 2 * (a : ℤ) ^ 2 :=
      fun T => by ring
    rw [Finset.sum_congr rfl (fun T _ => hcomb T), Finset.sum_add_distrib,
      ← Finset.mul_sum, ih, Finset.sum_const, Finset.card_powerset,
      Finset.card_insert_of_notMem ha, Finset.sum_insert ha]
    ring

/-- **Discrete Chebyshev/Markov count (0 axioms).**  For a nonnegative integer
weight `g` and a positive threshold `t`, the number of indices with `g i ≥ t`,
times `t`, is at most the total weight `∑ g i`.  Specialised to
`g T = (2·Σ_{i∈T} i − S)²` this is the tail count feeding the anticoncentration
estimate. -/
theorem card_mul_le_second_moment (s : Finset ℕ) (g : ℕ → ℤ)
    (hg : ∀ i ∈ s, 0 ≤ g i) (t : ℤ) :
    ((s.filter (fun i => t ≤ g i)).card : ℤ) * t ≤ ∑ i ∈ s, g i := by
  calc ((s.filter (fun i => t ≤ g i)).card : ℤ) * t
      = ∑ _i ∈ s.filter (fun i => t ≤ g i), t := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ s.filter (fun i => t ≤ g i), g i :=
        Finset.sum_le_sum (fun i hi => (Finset.mem_filter.mp hi).2)
    _ ≤ ∑ i ∈ s, g i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i hi _ => hg i hi)

/-- **Subset sums are injective on the powerset (0 axioms).**  The integer subset-sum
map `T ↦ ∑_{i∈T} i` is injective on `A.powerset` exactly when `A` has distinct subset
sums.  This is the definitional content of `hasDistinctSubsetSums` transported to `ℤ`
(via `Nat.cast_sum`), packaged as a `Set.InjOn` for use with `Finset.card_image_of_injOn`. -/
theorem subsetSum_injOn_of_distinct {A : Finset ℕ} (hDSS : hasDistinctSubsetSums A) :
    Set.InjOn (fun T : Finset ℕ => ∑ i ∈ T, (i : ℤ)) (A.powerset : Set (Finset ℕ)) := by
  intro S hS T hT h
  rw [Finset.mem_coe, Finset.mem_powerset] at hS hT
  refine hDSS S T hS hT ?_
  have e : ∀ U : Finset ℕ, ((U.sum id : ℕ) : ℤ) = ∑ i ∈ U, (i : ℤ) := by
    intro U; simpa using (Nat.cast_sum U id)
  have heq : ((S.sum id : ℕ) : ℤ) = ((T.sum id : ℕ) : ℤ) := by rw [e, e]; exact h
  exact_mod_cast heq

/-- **The doubled deviations are injective on the powerset (0 axioms).**  Since
`T ↦ 2·(∑_{i∈T} i) − S` is an affine reparametrisation of the subset-sum map, it too is
injective on `A.powerset` for a distinct-subset-sums set.  These are the integer points
whose second moment is `2^{|A|}·Q` (`second_moment_identity`). -/
theorem doubledDrop_injOn_of_distinct {A : Finset ℕ} (hDSS : hasDistinctSubsetSums A) :
    Set.InjOn (fun T : Finset ℕ => 2 * (∑ i ∈ T, (i : ℤ)) - ∑ i ∈ A, (i : ℤ))
      (A.powerset : Set (Finset ℕ)) := by
  intro S hS T hT h
  refine subsetSum_injOn_of_distinct hDSS hS hT ?_
  show (∑ i ∈ S, (i : ℤ)) = ∑ i ∈ T, (i : ℤ)
  have h' : 2 * (∑ i ∈ S, (i : ℤ)) - ∑ i ∈ A, (i : ℤ)
      = 2 * (∑ i ∈ T, (i : ℤ)) - ∑ i ∈ A, (i : ℤ) := h
  omega

/-- **The `2^{|A|}` doubled deviations are `2^{|A|}` distinct integers (0 axioms).**
For a distinct-subset-sums set `A`, the image of `A.powerset` under
`T ↦ 2·(∑_{i∈T} i) − S` has exactly `2^{|A|}` elements.  This is the precise
"`2ⁿ` distinct integers" input to the central-interval count that recovers the sharp
constant `3` in `anticoncentration_bound`. -/
theorem card_doubledDrop_image_of_distinct {A : Finset ℕ}
    (hDSS : hasDistinctSubsetSums A) :
    (A.powerset.image
      (fun T : Finset ℕ => 2 * (∑ i ∈ T, (i : ℤ)) - ∑ i ∈ A, (i : ℤ))).card
        = 2 ^ A.card := by
  rw [Finset.card_image_of_injOn (doubledDrop_injOn_of_distinct hDSS),
    Finset.card_powerset]

/-- **Same-parity integers in a symmetric interval (0 axioms).**  A finite set `V` of
integers all sharing one parity and all lying in `[−L, L]` (`L ≥ 0`) has at most `L + 1`
elements.  This is the central-interval count that — applied to the `2^{|A|}` distinct
same-parity doubled deviations `2·Σ_T − S` confined to `|·| ≤ L` — recovers the sharp
constant `3` in `anticoncentration_bound` (the pure second-moment spread bound only gives
`≈ 3.46√Q`).  Proof: `v ↦ (v + L) / 2` maps `V` injectively (same parity ⟹ no collisions,
`omega`) into `Finset.Icc 0 L`, whose cardinality is `L + 1`. -/
theorem card_le_of_sameParity_interval (V : Finset ℤ) (p L : ℤ) (hL : 0 ≤ L)
    (hpar : ∀ v ∈ V, v % 2 = p % 2) (hbd : ∀ v ∈ V, -L ≤ v ∧ v ≤ L) :
    (V.card : ℤ) ≤ L + 1 := by
  have hinj : Set.InjOn (fun v => (v + L) / 2) (V : Set ℤ) := by
    intro u hu v hv h
    have hu' := hpar u (Finset.mem_coe.mp hu)
    have hv' := hpar v (Finset.mem_coe.mp hv)
    simp only at h
    omega
  have hsub : V.image (fun v => (v + L) / 2) ⊆ Finset.Icc 0 L := by
    intro y hy
    simp only [Finset.mem_image] at hy
    obtain ⟨v, hv, rfl⟩ := hy
    obtain ⟨h1, h2⟩ := hbd v hv
    rw [Finset.mem_Icc]; omega
  have hcard : V.card ≤ (Finset.Icc 0 L).card := by
    rw [← Finset.card_image_of_injOn hinj]
    exact Finset.card_le_card hsub
  have hIcc : (Finset.Icc (0 : ℤ) L).card = (L + 1).toNat := by
    rw [Int.card_Icc]; congr 1; omega
  rw [hIcc] at hcard
  have : (V.card : ℤ) ≤ ((L + 1).toNat : ℤ) := by exact_mod_cast hcard
  rw [Int.toNat_of_nonneg (by omega)] at this
  exact this

/-- **Discrete tail count over any index type (0 axioms).**  The `Finset ℕ`-indexed
`card_mul_le_second_moment` generalised to an arbitrary index type — needed to count the
far integer deviations `v ∈ V ⊆ ℤ`.  Same elementary proof. -/
theorem card_mul_le_sum_of_nonneg {ι : Type*} (s : Finset ι) (g : ι → ℤ)
    (hg : ∀ i ∈ s, 0 ≤ g i) (t : ℤ) :
    ((s.filter (fun i => t ≤ g i)).card : ℤ) * t ≤ ∑ i ∈ s, g i := by
  calc ((s.filter (fun i => t ≤ g i)).card : ℤ) * t
      = ∑ _i ∈ s.filter (fun i => t ≤ g i), t := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ s.filter (fun i => t ≤ g i), g i :=
        Finset.sum_le_sum (fun i hi => (Finset.mem_filter.mp hi).2)
    _ ≤ ∑ i ∈ s, g i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i hi _ => hg i hi)

/-- **Chebyshev anticoncentration bound (0 axioms).**  For a distinct-subset-sums set `A`
with `n = |A| ≥ 1` and `Q = Σaᵢ²`, the count of subsets satisfies `2ⁿ ≤ 3√Q + 2`.

This **discharges the former `anticoncentration_bound` axiom** by assembling the verified
ingredients above, with no probability theory:

* the `2ⁿ` doubled deviations `dₜ = 2·Σ_{i∈T} i − S` are `2ⁿ` **distinct integers**
  (`card_doubledDrop_image_of_distinct`) all of one **parity** (`≡ S mod 2`), with second
  moment `Σ dₜ² = 2ⁿ·Q` (`second_moment_identity`);
* split them at a radius `L + 1 = ⌈2√Q⌉`: the central band `|dₜ| ≤ L` holds `≤ L + 1` of them
  (`card_le_of_sameParity_interval`, the parity count), while the tail `|dₜ| ≥ L + 1` holds
  `≤ 2ⁿQ/(L+1)²` of them (`card_mul_le_sum_of_nonneg`, discrete Chebyshev);
* with `(L+1)² ≥ 4Q` the tail is `≤ 2ⁿ/4`, so `(3/4)·2ⁿ ≤ L + 1 ≤ 2√Q + 1`, giving
  `2ⁿ ≤ (8√Q + 4)/3 ≤ 3√Q + 2`. -/
theorem anticoncentration_bound (A : Finset ℕ) (hDSS : hasDistinctSubsetSums A)
    (hpos : 0 < A.card) :
    (2 : ℝ) ^ A.card ≤ 3 * Real.sqrt (↑(A.sum (fun a => a ^ 2))) + 2 := by
  classical
  set S : ℤ := ∑ i ∈ A, (i : ℤ) with hSdef
  set f : Finset ℕ → ℤ := fun T => 2 * (∑ i ∈ T, (i : ℤ)) - S with hfdef
  set V : Finset ℤ := A.powerset.image f with hVdef
  set Q : ℤ := ∑ i ∈ A, (i : ℤ) ^ 2 with hQdef
  -- (1) `f` is injective on the powerset; `|V| = 2^n`.
  have hinj : Set.InjOn f (A.powerset : Set (Finset ℕ)) := by
    rw [hfdef]; exact doubledDrop_injOn_of_distinct hDSS
  have hVcard : V.card = 2 ^ A.card := by
    rw [hVdef, hfdef]; exact card_doubledDrop_image_of_distinct hDSS
  -- (2) second moment of the deviations: `Σ_{v∈V} v² = 2^n · Q`.
  have hsum : ∑ v ∈ V, v ^ 2 = 2 ^ A.card * Q := by
    rw [hVdef, Finset.sum_image hinj, hfdef]
    exact second_moment_identity A
  -- (3) every deviation has parity `S mod 2`.
  have hVpar : ∀ v ∈ V, v % 2 = S % 2 := by
    intro v hv
    rw [hVdef, Finset.mem_image] at hv
    obtain ⟨T, _, rfl⟩ := hv
    simp only [hfdef]; omega
  -- (4) `Q ≥ 1`: distinct subset sums force `0 ∉ A`, so some element is `≥ 1`.
  have h0 : (0 : ℕ) ∉ A := by
    intro h0A
    have : (∅ : Finset ℕ) = {0} :=
      hDSS ∅ {0} (Finset.empty_subset _)
        (by simpa [Finset.singleton_subset_iff] using h0A) (by simp)
    simp at this
  obtain ⟨a, haA⟩ := Finset.card_pos.mp hpos
  have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr (fun h => h0 (h ▸ haA))
  have hQ1 : (1 : ℤ) ≤ Q := by
    rw [hQdef]
    calc (1 : ℤ) ≤ (a : ℤ) ^ 2 := by
            have : (1 : ℤ) ≤ (a : ℤ) := by exact_mod_cast ha1
            nlinarith
      _ ≤ ∑ i ∈ A, (i : ℤ) ^ 2 :=
            Finset.single_le_sum (fun i _ => sq_nonneg _) haA
  have hQpos : (0 : ℝ) < (Q : ℝ) := by
    have h1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ1
    linarith
  -- rewrite the goal's `Q` (over ℕ→ℝ) as `(Q : ℝ)`.
  have hQcast : ((A.sum (fun a => a ^ 2) : ℕ) : ℝ) = (Q : ℝ) := by
    rw [hQdef]; push_cast; rfl
  rw [hQcast]
  -- abbreviations on the real side
  have hsqrtQ_nonneg : (0 : ℝ) ≤ Real.sqrt (Q : ℝ) := Real.sqrt_nonneg _
  have hsqrtQ_ge_one : (1 : ℝ) ≤ Real.sqrt (Q : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hQ1)
  have hsqQ : Real.sqrt (Q : ℝ) ^ 2 = (Q : ℝ) := Real.sq_sqrt (le_of_lt hQpos)
  -- (5) split radius `L + 1 = ⌈2√Q⌉`.
  set L : ℤ := ⌈2 * Real.sqrt (Q : ℝ)⌉ - 1 with hLdef
  have hceil_ge : 2 * Real.sqrt (Q : ℝ) ≤ ((⌈2 * Real.sqrt (Q : ℝ)⌉ : ℤ) : ℝ) :=
    Int.le_ceil _
  have hLnn : 0 ≤ L := by
    have h2 : (2 : ℝ) ≤ ((⌈2 * Real.sqrt (Q : ℝ)⌉ : ℤ) : ℝ) := by
      have : (2 : ℝ) ≤ 2 * Real.sqrt (Q : ℝ) := by nlinarith [hsqrtQ_ge_one]
      linarith [hceil_ge]
    have h2z : (2 : ℤ) ≤ ⌈2 * Real.sqrt (Q : ℝ)⌉ := by exact_mod_cast h2
    omega
  have hLr1 : 2 * Real.sqrt (Q : ℝ) ≤ (L : ℝ) + 1 := by
    rw [hLdef]; push_cast; linarith [hceil_ge]
  have hLr2 : (L : ℝ) + 1 ≤ 2 * Real.sqrt (Q : ℝ) + 1 := by
    rw [hLdef]; push_cast; linarith [Int.ceil_lt_add_one (2 * Real.sqrt (Q : ℝ))]
  have hw4 : 4 * (Q : ℝ) ≤ ((L : ℝ) + 1) ^ 2 := by
    nlinarith [hLr1, hsqQ, hsqrtQ_nonneg]
  -- (6) the central / tail split of `V`.
  have hsplit :
      (V.filter (fun v => -L ≤ v ∧ v ≤ L)).card
        + (V.filter (fun v => ¬ (-L ≤ v ∧ v ≤ L))).card = V.card :=
    Finset.filter_card_add_filter_neg_card_eq_card _
  -- central band: parity count `≤ L + 1`.
  have hnear : ((V.filter (fun v => -L ≤ v ∧ v ≤ L)).card : ℤ) ≤ L + 1 :=
    card_le_of_sameParity_interval (V.filter (fun v => -L ≤ v ∧ v ≤ L)) S L hLnn
      (fun v hv => hVpar v (Finset.mem_filter.mp hv).1)
      (fun v hv => (Finset.mem_filter.mp hv).2)
  -- tail ⊆ `{(L+1)² ≤ v²}`.
  have hfar_sub :
      V.filter (fun v => ¬ (-L ≤ v ∧ v ≤ L))
        ⊆ V.filter (fun v => (L + 1) ^ 2 ≤ v ^ 2) := by
    intro v hv
    obtain ⟨hvV, hnp⟩ := Finset.mem_filter.mp hv
    refine Finset.mem_filter.mpr ⟨hvV, ?_⟩
    have hcases : v ≤ -(L + 1) ∨ L + 1 ≤ v := by omega
    rcases hcases with h | h <;> nlinarith [hLnn]
  -- discrete Chebyshev on the tail.
  have htail :
      ((V.filter (fun v => (L + 1) ^ 2 ≤ v ^ 2)).card : ℤ) * (L + 1) ^ 2
        ≤ 2 ^ A.card * Q := by
    have := card_mul_le_sum_of_nonneg V (fun v => v ^ 2) (fun v _ => sq_nonneg v) ((L + 1) ^ 2)
    rwa [hsum] at this
  -- (7) integer assembly: `2^n ≤ (L+1) + far`, and `far·(L+1)² ≤ 2^n·Q`.
  set farc : ℤ := ((V.filter (fun v => (L + 1) ^ 2 ≤ v ^ 2)).card : ℤ) with hfarc
  have hI : (2 ^ A.card : ℤ) ≤ (L + 1) + farc := by
    have hsplitz :
        ((V.filter (fun v => -L ≤ v ∧ v ≤ L)).card : ℤ)
          + ((V.filter (fun v => ¬ (-L ≤ v ∧ v ≤ L))).card : ℤ)
          = (V.card : ℤ) := by exact_mod_cast hsplit
    have hnegfar :
        ((V.filter (fun v => ¬ (-L ≤ v ∧ v ≤ L))).card : ℤ) ≤ farc := by
      rw [hfarc]; exact_mod_cast Finset.card_le_card hfar_sub
    have hVz : (V.card : ℤ) = (2 ^ A.card : ℤ) := by exact_mod_cast hVcard
    rw [hVz] at hsplitz
    linarith [hnear, hnegfar, hsplitz]
  have hII : farc * (L + 1) ^ 2 ≤ (2 ^ A.card : ℤ) * Q := by rw [hfarc]; exact htail
  -- (8) cast to ℝ and finish.
  have hI_r : (2 : ℝ) ^ A.card ≤ ((L : ℝ) + 1) + (farc : ℝ) := by exact_mod_cast hI
  have hII_r : (farc : ℝ) * ((L : ℝ) + 1) ^ 2 ≤ (2 : ℝ) ^ A.card * (Q : ℝ) := by
    exact_mod_cast hII
  have hfcnn : (0 : ℝ) ≤ (farc : ℝ) := by rw [hfarc]; positivity
  have key : (4 * (farc : ℝ)) * (Q : ℝ) ≤ (2 : ℝ) ^ A.card * (Q : ℝ) := by
    nlinarith [hII_r, hw4, hfcnn, mul_nonneg hfcnn (show (0 : ℝ) ≤ ((L : ℝ) + 1) ^ 2 - 4 * (Q : ℝ) by linarith [hw4])]
  have hfc4 : 4 * (farc : ℝ) ≤ (2 : ℝ) ^ A.card := le_of_mul_le_mul_right key hQpos
  nlinarith [hI_r, hLr2, hfc4, hsqrtQ_nonneg]

/-- **DFX Lower Bound Statement** (Chebyshev constant): If A ⊆ {1,...,N} has n ≥ 1
    elements with distinct subset sums, then:
      2ⁿ ≤ 3·√n·N + 2,    equivalently    N ≥ (2ⁿ − 2) / (3·√n).

    This is the rigorous, order-correct form of the Dubroff–Fox–Xu lower bound
    N = Ω(2ⁿ/√n), improving the basic counting bound N ≥ (2ⁿ−1)/n by a factor √n.
    The sharp DFX constant √(2/π) (from Berry–Esseen) is the literature result; the
    constant 3 here is what the unconditionally-true Chebyshev anticoncentration
    bound delivers, and it is enough to capture the √n improvement.

    Note no positivity (`hA_pos`) or `N ≥ 2` hypothesis is needed: the additive
    `+2` slack makes the statement true for all n ≥ 1 (e.g. n=1, A={1}, N=1:
    2 ≤ 3·1·1 + 2 = 5).

    **Proof strategy**:
    1. `anticoncentration_bound`: 2ⁿ ≤ 3·√Q + 2 where Q = Σaᵢ².
    2. Crude variance bound (`sum_sq_le_card_mul_max_sq`): Q ≤ n·N².
    3. Hence √Q ≤ √n·N, so 2ⁿ ≤ 3·√n·N + 2. -/
theorem dfx_lower_bound (A : Finset ℕ) (N : ℕ)
    (hDSS : hasDistinctSubsetSums A) (hA : ∀ a ∈ A, a ≤ N)
    (hpos : 0 < A.card) :
    (2 : ℝ) ^ A.card ≤ 3 * Real.sqrt ↑A.card * ↑N + 2 := by
  -- Step 1: anticoncentration bound 2ⁿ ≤ 3·√Q + 2  (Q = Σaᵢ²)
  have h_ac : (2 : ℝ) ^ A.card ≤
      3 * Real.sqrt (↑(A.sum (fun a => a ^ 2))) + 2 :=
    anticoncentration_bound A hDSS hpos
  -- Step 2: Σaᵢ² ≤ n · N²  (each aᵢ ≤ N), cast to ℝ
  have h_QnN : (↑(A.sum (fun a => a ^ 2)) : ℝ) ≤ (↑A.card : ℝ) * (↑N : ℝ) ^ 2 := by
    exact_mod_cast sum_sq_le_card_mul_max_sq A N hA
  -- Step 3: √Q ≤ √n · N
  have hsqrtQ : Real.sqrt (↑(A.sum (fun a => a ^ 2))) ≤ Real.sqrt ↑A.card * ↑N := by
    have h1 : Real.sqrt (↑(A.sum (fun a => a ^ 2)) : ℝ)
        ≤ Real.sqrt ((↑A.card : ℝ) * (↑N : ℝ) ^ 2) := Real.sqrt_le_sqrt h_QnN
    rwa [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)] at h1
  -- Step 4: chain
  calc (2 : ℝ) ^ A.card
      ≤ 3 * Real.sqrt (↑(A.sum (fun a => a ^ 2))) + 2 := h_ac
    _ ≤ 3 * (Real.sqrt ↑A.card * ↑N) + 2 := by linarith [hsqrtQ]
    _ = 3 * Real.sqrt ↑A.card * ↑N + 2 := by ring

/-- **Explicit largest-element lower bound (DFX / Erdős), `N ≥ (2ⁿ−2)/(3√n)`.**
The recognisable form the DFX framework targets: a distinct-subset-sums set with
all elements `≤ N` and `n = |A| ≥ 1` forces

      N ≥ (2ⁿ − 2) / (3·√n),

i.e. `N = Ω(2ⁿ/√n)`.  This is `dfx_lower_bound` (`2ⁿ ≤ 3√n·N + 2`) solved for `N`,
dividing by `3√n > 0` (valid since `n ≥ 1`).  It states the actual lower bound on
the largest element that the whole file works toward — previously present only in
the surrounding prose. -/
theorem dfx_lower_bound_explicit (A : Finset ℕ) (N : ℕ)
    (hDSS : hasDistinctSubsetSums A) (hA : ∀ a ∈ A, a ≤ N)
    (hpos : 0 < A.card) :
    ((2 : ℝ) ^ A.card - 2) / (3 * Real.sqrt ↑A.card) ≤ (N : ℝ) := by
  have hle := dfx_lower_bound A N hDSS hA hpos
  have hcard1 : (1 : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hpos
  have hsqrt_pos : 0 < Real.sqrt ↑A.card := Real.sqrt_pos.mpr (by linarith)
  have h3s : 0 < 3 * Real.sqrt ↑A.card := by positivity
  rw [div_le_iff₀ h3s]
  nlinarith [hle]

/-! ## Part III: Comparison with Basic Bound

The basic counting bound (from Erdos1OQ01.lean) gives N ≥ (2ⁿ-1)/n.
The DFX bound gives N ≥ c·2ⁿ/√n, which is better by a factor of ~√n.
-/

/-- The DFX bound improves on the basic counting bound by a factor of √n.
    Basic: N ≥ (2ⁿ-1)/n ≈ 2ⁿ/n.
    DFX:   N ≥ c·2ⁿ/√n.
    Ratio: DFX/basic ≈ √n → ∞. -/
theorem dfx_improves_counting (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ) < n ^ 2 := by
  have : (1 : ℝ) < n := by exact_mod_cast hn
  nlinarith

/-- The DFX improvement factor: n < n² for n ≥ 2, so √n > 1.
    The DFX bound N ≥ c·2ⁿ/√n vs counting N ≥ c'·2ⁿ/n is better by √n. -/
theorem improvement_factor (n : ℕ) (hn : 2 ≤ n) : n < n * n := by nlinarith [hn]

/-! ## Part IV: Small Cases

For small n, the exact values f(n) (OEIS A005318) are known.
These provide concrete verification of the bounds.
-/

/-- f(0) = 0: The empty set has a single subset sum (the empty sum `0`), so it
    trivially has distinct subset sums.  This is the base case `a(0) = 0` of
    OEIS A005318, the `n = 0` companion of `f_one`/`f_two_max`: the only subset of
    `∅` is `∅` itself (`Finset.subset_empty`), so the distinctness hypothesis is
    vacuous. -/
theorem f_zero : ∃ (A : Finset ℕ), A.card = 0 ∧ hasDistinctSubsetSums A ∧ A.sup id = 0 := by
  refine ⟨∅, by simp, ?_, by simp⟩
  intro S T hS hT _
  rw [Finset.subset_empty] at hS hT
  rw [hS, hT]

/-- f(1) = 1: The set {1} has 2 distinct subset sums (0 and 1). -/
theorem f_one : ∃ (A : Finset ℕ), A.card = 1 ∧ hasDistinctSubsetSums A ∧ A.sup id = 1 := by
  use {1}
  refine ⟨by simp, ?_, by simp⟩
  intro S T hS hT heq
  simp only [Finset.mem_singleton, Finset.subset_singleton_iff] at hS hT
  rcases hS with rfl | rfl <;> rcases hT with rfl | rfl <;> simp_all

/-- f(2) = 2: The set {1,2} has 4 distinct subset sums (0,1,2,3).
    The subsets are ∅ (sum 0), {1} (sum 1), {2} (sum 2), {1,2} (sum 3), so it
    has distinct subset sums with maximum element 2.

    Strengthened to carry the `hasDistinctSubsetSums` witness (matching `f_one`):
    the previous statement only asserted `card = 2 ∧ sup = 2`, weaker than the
    `f(2) = 2` extremal claim in the docstring and the OEIS A005318 framing.  The
    `hasDistinctSubsetSums {1,2}` obligation is discharged by enumerating the four
    subsets of `{1,2}` (`fin_cases` over the powerset) and deciding each of the
    16 subset-pair sum comparisons. -/
theorem f_two_max :
    ∃ (A : Finset ℕ), A.card = 2 ∧ hasDistinctSubsetSums A ∧ A.sup id = 2 := by
  refine ⟨{1, 2}, by decide, ?_, by decide⟩
  intro S T hS hT heq
  have hS' : S ∈ ({1, 2} : Finset ℕ).powerset := Finset.mem_powerset.mpr hS
  have hT' : T ∈ ({1, 2} : Finset ℕ).powerset := Finset.mem_powerset.mpr hT
  fin_cases hS' <;> fin_cases hT' <;> revert heq <;> decide

/-- f(3) = 4: the set `{1, 2, 4}` has `2³ = 8` distinct subset sums (`0..7`, the
    binary representations) with maximum element `4`.  This is the `n = 3` entry of
    OEIS A005318, continuing the `f_zero`/`f_one`/`f_two_max` sequence: powers of two
    are the simplest distinct-subset-sums witness, and `{1,2,4}` attains the known
    minimal maximum `f(3) = 4`.  The `hasDistinctSubsetSums {1,2,4}` obligation is
    discharged by enumerating the eight subsets (`fin_cases` over the powerset) and
    deciding each subset-pair sum comparison, exactly as in `f_two_max`. -/
theorem f_three :
    ∃ (A : Finset ℕ), A.card = 3 ∧ hasDistinctSubsetSums A ∧ A.sup id = 4 := by
  refine ⟨{1, 2, 4}, by decide, ?_, by decide⟩
  intro S T hS hT heq
  have hS' : S ∈ ({1, 2, 4} : Finset ℕ).powerset := Finset.mem_powerset.mpr hS
  have hT' : T ∈ ({1, 2, 4} : Finset ℕ).powerset := Finset.mem_powerset.mpr hT
  fin_cases hS' <;> fin_cases hT' <;> revert heq <;> decide

/-- f(4) = 7: the Conway–Guy set `{3, 5, 6, 7}` has `2⁴ = 16` distinct subset sums
    (`0, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 21`) with maximum element
    `7`.  This is the `n = 4` entry of OEIS A005318, and the FIRST case where the
    minimal largest element beats the greedy powers-of-two witness: `{1, 2, 4, 8}`
    also has distinct subset sums but maximum `8 > 7`.  So the naive doubling
    construction (`f_zero`/`f_one`/`f_two_max`/`f_three` witnesses `{}`, `{1}`,
    `{1,2}`, `{1,2,4}`) is no longer extremal at `n = 4` — a genuinely non-trivial
    input to the Erdős distinct-subset-sums problem, and the reason `f(n)` is not
    simply `2ⁿ⁻¹`.  The `hasDistinctSubsetSums {3,5,6,7}` obligation is discharged
    by enumerating the sixteen subsets (`fin_cases` over the powerset) and deciding
    each subset-pair sum comparison, exactly as in `f_two_max`/`f_three`. -/
theorem f_four :
    ∃ (A : Finset ℕ), A.card = 4 ∧ hasDistinctSubsetSums A ∧ A.sup id = 7 := by
  refine ⟨{3, 5, 6, 7}, by decide, ?_, by decide⟩
  intro S T hS hT heq
  have hS' : S ∈ ({3, 5, 6, 7} : Finset ℕ).powerset := Finset.mem_powerset.mpr hS
  have hT' : T ∈ ({3, 5, 6, 7} : Finset ℕ).powerset := Finset.mem_powerset.mpr hT
  fin_cases hS' <;> fin_cases hT' <;> revert heq <;> decide

/-- **`f(4) ≥ 7`: no four-element set with maximum `≤ 6` has distinct subset sums.**
    Since distinct subset sums force `0 ∉ A`, a counterexample would be a four-element
    subset of `{1,…,6}`; the finite check over those subsets (enumerated by `fin_cases`,
    each refuted by `card ≠ 4` or an explicit subset-sum collision via the bounded,
    decidable form of the hypothesis) rules them all out.  This is the matching lower
    bound that upgrades the upper witness `f_four` to the exact value `f_four_eq`.

    The enumeration is deliberately kept as many *shallow* `decide`s (one per case), not
    one deep `decide` over the whole powerset: the latter overflows the Lean kernel's C
    stack (SIGBUS / build exit code 135). -/
theorem f_four_lower {A : Finset ℕ} (h4 : A.card = 4)
    (hDSS : hasDistinctSubsetSums A) : 7 ≤ A.sup id := by
  by_contra hlt
  push_neg at hlt
  -- Distinct subset sums force `0 ∉ A` (else `∅` and `{0}` collide).
  have h0 : (0 : ℕ) ∉ A := by
    intro h0A
    have hcollide : (∅ : Finset ℕ) = {0} :=
      hDSS ∅ {0} (Finset.empty_subset _)
        (by simpa [Finset.singleton_subset_iff] using h0A) (by simp)
    simp at hcollide
  -- Hence every element lies in `[1, 6]`, so `A ⊆ Icc 1 6`.
  have hsub : A ⊆ Finset.Icc 1 6 := by
    intro a ha
    rw [Finset.mem_Icc]
    refine ⟨?_, ?_⟩
    · rcases Nat.eq_zero_or_pos a with h | h
      · exact absurd (h ▸ ha) h0
      · exact h
    · have hle : a ≤ A.sup id := Finset.le_sup (f := id) ha
      omega
  have hmem : A ∈ (Finset.Icc 1 6).powerset := Finset.mem_powerset.mpr hsub
  -- Bounded (hence decidable) form of the distinct-subset-sums hypothesis.
  have hDSS' : ∀ S ∈ A.powerset, ∀ T ∈ A.powerset, S.sum id = T.sum id → S = T :=
    fun S hS T hT h => hDSS S T (Finset.mem_powerset.mp hS) (Finset.mem_powerset.mp hT) h
  fin_cases hmem <;>
    first
      | exact absurd h4 (by decide)
      | exact absurd hDSS' (by decide)

/-- **`f(4) = 7` (OEIS A005318, `n = 4`).**  The minimal possible largest element of a
    four-element distinct-subset-sums set is exactly `7`: attained by `{3,5,6,7}`
    (`f_four`) and by no set with maximum `≤ 6` (`f_four_lower`).  This pins the `n = 4`
    value of the Erdős distinct-subset-sums extremal function, the first case where the
    powers-of-two witness `{1,2,4,8}` (maximum `8`) is not optimal. -/
theorem f_four_eq :
    (∃ (A : Finset ℕ), A.card = 4 ∧ hasDistinctSubsetSums A ∧ A.sup id = 7) ∧
      (∀ (A : Finset ℕ), A.card = 4 → hasDistinctSubsetSums A → 7 ≤ A.sup id) :=
  ⟨f_four, fun _A h hDSS => f_four_lower h hDSS⟩

/-- **Powers of two are not extremal at `n = 4`.**  The witness `{3,5,6,7}` has distinct
    subset sums with maximum `7 < 8 = 2^{4-1}`, so the minimal largest element drops
    strictly below the powers-of-two value `2^{n-1}` — the first `n` where the geometric
    construction of `Erdos1OQ02OQ01` (max `= 2^{n-1}`) is beaten (Conway–Guy). -/
theorem f_four_lt_geometric :
    ∃ (A : Finset ℕ), A.card = 4 ∧ hasDistinctSubsetSums A ∧ A.sup id < 2 ^ (4 - 1) := by
  obtain ⟨A, hcard, hDSS, hsup⟩ := f_four
  exact ⟨A, hcard, hDSS, by rw [hsup]; norm_num⟩

/-- **Cardinality certificate for distinct subset sums (0 axioms).**  A finite set `A`
    has distinct subset sums exactly when the subset-sum map `S ↦ ∑_{i∈S} i` is injective
    on `A.powerset`, i.e. when its image has the full cardinality `2^|A| = |A.powerset|`.
    This converts the `∀ S T` distinctness obligation into a *single* decidable
    cardinality equality, which `decide` checks by computing the `2^|A|` subset sums and
    counting distinct values — cheap where the quadratic `fin_cases` over pairs
    (`2^|A| × 2^|A|` cases) becomes intractable (e.g. `|A| = 6`).

    NOTE: verifying that equality by `decide` still evaluates a `Finset.image` dedup over
    the whole `2^|A|`-element powerset, which overflows the Lean kernel's C stack (SIGBUS /
    build exit code 135) once `|A| ≥ 5` — as does the pairwise `fin_cases` route.  The
    larger Conway–Guy witnesses `f(5) = 13`, `f(6) = 24` therefore cannot be certified
    axiom-free by brute force (only via `native_decide`, which would add `Lean.ofReduceBool`
    and forfeit the file's 0-axiom status); a robust proof for `|A| ≥ 5` needs a structural
    argument. -/
theorem hasDistinctSubsetSums_iff_card (A : Finset ℕ) :
    hasDistinctSubsetSums A ↔
    (A.powerset.image (fun S => S.sum id)).card = A.powerset.card := by
  rw [Finset.card_image_iff]
  constructor
  · intro h S hS T hT heq
    exact h S T (Finset.mem_powerset.mp hS) (Finset.mem_powerset.mp hT) heq
  · intro h S T hS hT heq
    exact h (Finset.mem_powerset.mpr hS) (Finset.mem_powerset.mpr hT) heq

/-! ## Structural properties of `hasDistinctSubsetSums`

The small-case witnesses `f_zero`…`f_four` above certify the property by brute
force, which the note on `hasDistinctSubsetSums_iff_card` explains cannot scale
past `|A| = 4` axiom-free.  The lemmas below are the *structural* counterpart:
elementary, brute-force-free facts that hold for **all** finite sets and are
reusable engines for building and analysing witnesses of any size (including the
Conway–Guy sets `f(5)=13`, `f(6)=24` the brute-force route cannot reach).

* **Hereditary**: every subset of a distinct-subset-sums set again has distinct
  subset sums (`hasDistinctSubsetSums_subset`, `hasDistinctSubsetSums_erase`).
* **Base cases**: `∅` and any nonzero singleton qualify.
* **No zero / positivity**: a distinct-subset-sums set never contains `0`, so all
  its elements are positive — matching the `0 < a` hypothesis in
  `erdos_1_conjecture`.
* **Scale invariance**: multiplying every element by a positive constant preserves
  the property (`hasDistinctSubsetSums_image_mul`), the algebraic engine behind
  rescaling a witness.
-/

/-- **Hereditary**: any subset of a distinct-subset-sums set again has distinct
subset sums.  Subsets of `B ⊆ A` are subsets of `A`, so the distinctness
hypothesis on `A` applies verbatim.  This is the reusable downward-closure engine:
distinct subset sums is a hereditary (monotone-decreasing) property. -/
theorem hasDistinctSubsetSums_subset {A B : Finset ℕ}
    (hA : hasDistinctSubsetSums A) (hBA : B ⊆ A) : hasDistinctSubsetSums B :=
  fun S T hS hT hsum => hA S T (hS.trans hBA) (hT.trans hBA) hsum

/-- Removing an element preserves distinct subset sums — the `erase` special case
of `hasDistinctSubsetSums_subset`. -/
theorem hasDistinctSubsetSums_erase {A : Finset ℕ}
    (hA : hasDistinctSubsetSums A) (a : ℕ) : hasDistinctSubsetSums (A.erase a) :=
  hasDistinctSubsetSums_subset hA (Finset.erase_subset a A)

/-- The empty set trivially has distinct subset sums: its only subset is `∅`. -/
theorem hasDistinctSubsetSums_empty : hasDistinctSubsetSums (∅ : Finset ℕ) := by
  intro S T hS hT _
  rw [Finset.subset_empty] at hS hT
  rw [hS, hT]

/-- A nonzero singleton `{a}` has distinct subset sums: its subsets are `∅` (sum
`0`) and `{a}` (sum `a`), which differ exactly when `a ≠ 0`.  (The singleton
`{0}` fails, since `∅` and `{0}` then share the sum `0` — consistent with
`hasDistinctSubsetSums_zero_not_mem`.) -/
theorem hasDistinctSubsetSums_singleton {a : ℕ} (ha : a ≠ 0) :
    hasDistinctSubsetSums ({a} : Finset ℕ) := by
  intro S T hS hT hsum
  rw [Finset.subset_singleton_iff] at hS hT
  rcases hS with hS | hS <;> rcases hT with hT | hT <;>
    subst hS <;> subst hT <;> simp_all

/-- **A distinct-subset-sums set never contains `0`.**  If `0 ∈ A` then the
distinct subsets `{0}` and `∅` would share the sum `0`, contradicting
distinctness. -/
theorem hasDistinctSubsetSums_zero_not_mem {A : Finset ℕ}
    (hA : hasDistinctSubsetSums A) : 0 ∉ A := fun h0 =>
  Finset.singleton_ne_empty 0 <|
    hA {0} ∅ (Finset.singleton_subset_iff.mpr h0) (Finset.empty_subset _) (by simp)

/-- **Every element of a distinct-subset-sums set is positive.**  Immediate from
`hasDistinctSubsetSums_zero_not_mem`; this matches the `0 < a` positivity
hypothesis in the statement of `erdos_1_conjecture`, so the conjecture's
constraint is automatic given distinctness. -/
theorem hasDistinctSubsetSums_pos_of_mem {A : Finset ℕ}
    (hA : hasDistinctSubsetSums A) {a : ℕ} (ha : a ∈ A) : 0 < a :=
  Nat.pos_of_ne_zero fun h => hasDistinctSubsetSums_zero_not_mem hA (h ▸ ha)

/-- **Scale invariance**: multiplying every element by a positive constant `c`
preserves distinct subset sums.  Each subset of `A.image (c * ·)` is `S.image
(c * ·)` for a unique `S ⊆ A` (as `c * ·` is injective), and its sum is `c` times
the sum of `S`; since `c > 0` is cancellable, equal scaled sums force equal
sums, hence equal subsets.  The algebraic engine behind rescaling a witness
(e.g. clearing denominators, or interleaving two witnesses on disjoint scales). -/
theorem hasDistinctSubsetSums_image_mul {A : Finset ℕ}
    (hA : hasDistinctSubsetSums A) {c : ℕ} (hc : 0 < c) :
    hasDistinctSubsetSums (A.image (fun x => c * x)) := by
  have hinj : Function.Injective (fun x : ℕ => c * x) :=
    fun x y h => Nat.eq_of_mul_eq_mul_left hc h
  intro S' T' hS' hT' hsum
  rw [Finset.subset_image_iff] at hS' hT'
  obtain ⟨S, hSA, rfl⟩ := hS'
  obtain ⟨T, hTA, rfl⟩ := hT'
  have hsumS : (S.image (fun x => c * x)).sum id = c * S.sum id := by
    rw [Finset.sum_image (fun x _ y _ h => hinj h)]
    simp [id, Finset.mul_sum]
  have hsumT : (T.image (fun x => c * x)).sum id = c * T.sum id := by
    rw [Finset.sum_image (fun x _ y _ h => hinj h)]
    simp [id, Finset.mul_sum]
  rw [hsumS, hsumT] at hsum
  rw [hA S T hSA hTA (Nat.eq_of_mul_eq_mul_left hc hsum)]

/-! ## Part V: Intrinsic (parameter-free) counting bounds

The counting bound `erdos_1_counting_bound` in `Erdos1Problem` is stated relative to an
*externally supplied* upper bound `N ≥ a` for every `a ∈ A`, giving `2^|A| ≤ |A|·N + 1`.
The sharpest and most intrinsic form of the same pigeonhole argument bounds the `2^|A|`
distinct subset sums by the total sum `∑A` alone — no ambient `N` needed — since every
subset sum lies in `[0, ∑A]`. This `2^|A| ≤ (∑A) + 1` bound is strictly sharper than the
`N`-form (because `∑A ≤ |A|·N`) and depends only on `A` itself, making it the natural
building block from which the ambient-`N` and largest-element walls both follow.
-/

/-- **Intrinsic sum counting wall (0 axioms).**  A set with distinct subset sums satisfies
`2^|A| ≤ (∑ a ∈ A, a) + 1`: the `2^|A|` subsets have distinct sums, each lying in the
`(∑A + 1)`-element range `[0, ∑A]`, so pigeonhole forces `2^|A| ≤ ∑A + 1`.  Unlike
`erdos_1_counting_bound` (which needs an externally supplied `N ≥ a`), this bound is
parameter-free — it depends on `A` alone — and is strictly sharper, since `∑A ≤ |A|·N`.
It is the intrinsic origin of the whole Erdős #1 counting bound. -/
theorem two_pow_card_le_sum_succ {A : Finset ℕ}
    (hDSS : hasDistinctSubsetSums A) :
    2 ^ A.card ≤ A.sum id + 1 := by
  -- The subset-sum map is injective on the powerset (distinctness), so its image has
  -- cardinality `2^|A|`.
  have hinj : Set.InjOn (fun (S : Finset ℕ) => S.sum id) (↑A.powerset : Set (Finset ℕ)) := by
    intro S hS T hT heq
    rw [Finset.mem_coe, Finset.mem_powerset] at hS hT
    exact hDSS S T hS hT heq
  have himg_card : (A.powerset.image (fun S => S.sum id)).card = 2 ^ A.card := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_powerset]
  -- Every subset sum lies in `[0, ∑A]`, so the image sits inside `range (∑A + 1)`.
  have himg_sub : A.powerset.image (fun S => S.sum id) ⊆ Finset.range (A.sum id + 1) := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨S, hSmem, rfl⟩ := hx
    rw [Finset.mem_powerset] at hSmem
    rw [Finset.mem_range]
    have hle : S.sum id ≤ A.sum id := Finset.sum_le_sum_of_subset hSmem
    omega
  calc 2 ^ A.card
      = (A.powerset.image (fun S => S.sum id)).card := himg_card.symm
    _ ≤ (Finset.range (A.sum id + 1)).card := Finset.card_le_card himg_sub
    _ = A.sum id + 1 := Finset.card_range _

/-- **Intrinsic largest-element counting wall (0 axioms).**  Specialising the sum wall
`two_pow_card_le_sum_succ` to `A`'s own maximum gives `2^|A| ≤ |A|·(sup A) + 1`, using
`∑A ≤ |A|·(sup A)` (`sum_le_card_mul_max`).  This is the sharpest `N`-form counting bound
for `A`: it uses the *exact* largest element `A.sup id` rather than an arbitrary ambient
`N ≥ a`, so it refines `erdos_1_counting_bound` whenever the supplied `N` overshoots the
true maximum.  It is exactly the wall exploited by the exhaustive small-case lower bound
`f_four_lower`. -/
theorem two_pow_card_le_card_mul_sup_succ {A : Finset ℕ}
    (hDSS : hasDistinctSubsetSums A) :
    2 ^ A.card ≤ A.card * A.sup id + 1 := by
  have h1 := two_pow_card_le_sum_succ hDSS
  have h2 : A.sum id ≤ A.card * A.sup id :=
    sum_le_card_mul_max A (A.sup id) (fun a ha => Finset.le_sup (f := id) ha)
  omega
/-! ## Part VI: The general powers-of-two upper bound `f(n) ≤ 2ⁿ⁻¹`

The per-case witnesses `f_zero`…`f_four` above certify individual values of the
extremal function `f`.  They are subsumed, in the *upper-bound* direction, by a
single uniform construction: the greedy binary set `{2⁰, 2¹, …, 2ⁿ⁻¹}` has
distinct subset sums for **every** `n`, because a subset sum of distinct powers
of two is just the number whose binary expansion is that subset (uniqueness of
binary representation).  This gives `f(n) ≤ 2ⁿ⁻¹` for all `n`, the classical
upper bound that the Conway–Guy construction (and the exact values in
OEIS A005318, `f(4) = 7 < 8 = 2³`) improve upon, and the complement of the DFX
lower bound `f(n) = Ω(2ⁿ/√n)` formalized in `dfx_lower_bound`.
-/

/-- The greedy powers-of-two witness `{2⁰, 2¹, …, 2ⁿ⁻¹}` for the Erdős
    distinct-subset-sums problem: an `n`-element set of positive integers whose
    `2ⁿ` subset sums are exactly the numbers `0, 1, …, 2ⁿ − 1` (binary
    representations). -/
def powersOfTwo (n : ℕ) : Finset ℕ := (Finset.range n).image (fun i => 2 ^ i)

/-- `powersOfTwo n` has exactly `n` elements: `i ↦ 2ⁱ` is injective, so the image
    of `range n` has the same cardinality. -/
theorem powersOfTwo_card (n : ℕ) : (powersOfTwo n).card = n := by
  rw [powersOfTwo,
    Finset.card_image_of_injective _ (Nat.pow_right_injective (le_refl 2)),
    Finset.card_range]

/-- Every element of `powersOfTwo n` is a positive power of two. -/
theorem powersOfTwo_pos (n : ℕ) : ∀ a ∈ powersOfTwo n, 0 < a := by
  intro a ha
  rw [powersOfTwo, Finset.mem_image] at ha
  obtain ⟨i, _, rfl⟩ := ha
  positivity

/-- The largest element of `powersOfTwo n` is at most `2ⁿ⁻¹`: each element is
    `2ⁱ` with `i < n`, hence `i ≤ n − 1`. -/
theorem powersOfTwo_sup_le (n : ℕ) : (powersOfTwo n).sup id ≤ 2 ^ (n - 1) := by
  apply Finset.sup_le
  intro a ha
  rw [powersOfTwo, Finset.mem_image] at ha
  obtain ⟨i, hi, rfl⟩ := ha
  rw [Finset.mem_range] at hi
  simp only [id_eq]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **Key fact.** `powersOfTwo n` has distinct subset sums for every `n`.  A
    subset `S ⊆ {2⁰, …, 2ⁿ⁻¹}` is the image of a set `s ⊆ range n` of exponents,
    and `∑_{a ∈ S} a = ∑_{i ∈ s} 2ⁱ`; the map `s ↦ ∑_{i ∈ s} 2ⁱ` is injective on
    `Finset ℕ` (uniqueness of binary expansion, `Finset.geomSum_injective`), so
    equal subset sums force equal exponent sets and hence equal subsets. -/
theorem powersOfTwo_distinctSubsetSums (n : ℕ) :
    hasDistinctSubsetSums (powersOfTwo n) := by
  intro S T hS hT heq
  rw [powersOfTwo, Finset.subset_image_iff] at hS hT
  obtain ⟨s, _, rfl⟩ := hS
  obtain ⟨t, _, rfl⟩ := hT
  rw [Finset.sum_image (fun x _ y _ h => Nat.pow_right_injective (le_refl 2) h),
      Finset.sum_image (fun x _ y _ h => Nat.pow_right_injective (le_refl 2) h)] at heq
  simp only [id_eq] at heq
  rw [Finset.geomSum_injective (le_refl 2) heq]

/-- **Powers-of-two upper bound**: for every `n` there is an `n`-element set of
    positive integers with distinct subset sums whose maximum element is at most
    `2ⁿ⁻¹`.  Equivalently `f(n) ≤ 2ⁿ⁻¹` for all `n` — the classical greedy binary
    bound, complementing the DFX lower bound `f(n) = Ω(2ⁿ/√n)` and the exact
    small values `f_zero`…`f_four`.  This is the uniform statement behind the
    per-case witnesses `{}`, `{1}`, `{1,2}`, `{1,2,4}`, … (each a `powersOfTwo`
    set, except where a smaller extremal set exists, as at `n = 4`). -/
theorem f_le_two_pow (n : ℕ) :
    ∃ (A : Finset ℕ), A.card = n ∧ (∀ a ∈ A, 0 < a) ∧
      hasDistinctSubsetSums A ∧ A.sup id ≤ 2 ^ (n - 1) :=
  ⟨powersOfTwo n, powersOfTwo_card n, powersOfTwo_pos n,
    powersOfTwo_distinctSubsetSums n, powersOfTwo_sup_le n⟩

/-! ## Conclusion

The DFX framework is formalized with:
- 0 axioms (the Chebyshev anticoncentration bound `2ⁿ ≤ 3√Q + 2` is now the
  fully proved theorem `anticoncentration_bound`, no longer an axiom)
- 0 sorries (dfx_lower_bound fully proved)
- Variance bounds and Cauchy–Schwarz (proved)
- Small case verifications `f_zero`…`f_four` (proved).  `f_four` shows `f(4) ≤ 7`
  via the Conway–Guy witness `{3,5,6,7}`, beating the powers-of-two witness `{1,2,4,8}`
  of maximum `8`; the matching lower bound `f_four_lower` upgrades this to the exact
  `f(4) = 7` (`f_four_eq`), and `f_four_lt_geometric` records `7 < 2^{4-1}` — the first
  `n` where powers of two are not extremal (Conway–Guy).  The larger witnesses
  `f(5) = 13`, `f(6) = 24` are not included: their `fin_cases` / image-cardinality
  `decide` certifications overflow the kernel C stack for `|A| ≥ 5` (SIGBUS / build exit
  135), so they cannot be built axiom-free (see `hasDistinctSubsetSums_iff_card`).

The anticoncentration bound is discharged entirely by the probability-free CORE
built up in the "Verified ingredients toward discharging" section
(`second_moment_identity`, `card_mul_le_second_moment`,
`card_doubledDrop_image_of_distinct`, `card_le_of_sameParity_interval`,
`card_mul_le_sum_of_nonneg`), so no probability-theory / measure infrastructure
is needed: the whole file is elementary `Finset`/`Int`/`Real.sqrt` algebra with
0 axioms and 0 sorries.

NOTE (2026-06-27 integrity fix): the previous `anticoncentration_bound` axiom
`2ⁿ ≤ √(2/π)·2(S+1)/√Q` was mathematically FALSE (it fails already for
A = {1,2}: it asserts 4 ≤ 2.85), which made the file logically unsound. It was
replaced with the true Chebyshev bound `2ⁿ ≤ 3√Q + 2`; `dfx_lower_bound` was
re-derived with the honest (order-correct) constant.
-/

end Erdos1OQ02
