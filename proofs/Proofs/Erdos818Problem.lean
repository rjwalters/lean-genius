/-
Erdős Problem #818: Product Set Lower Bound for Small Sumsets

Source: https://erdosproblems.com/818
Status: SOLVED

Statement:
Let A be a finite set of integers such that |A + A| ≪ |A|.
Is it true that |A · A| ≫ |A|² / (log |A|)^C for some constant C > 0?

Answer: YES
Proved by Solymosi (2009) in the stronger form:
  |A · A| ≫ |A|² / log |A|

Background:
This is a consequence of the sum-product phenomenon. If a set A has small
additive doubling (|A+A| is close to |A|), then it must have large multiplicative
expansion (|AA| is close to |A|²).

The intuition is that sets cannot simultaneously have both strong additive
AND multiplicative structure. If sums are constrained, products must expand.

Key Insight:
- If |A+A| ≤ K·|A| (small sumset), then |AA| ≥ |A|² / (C · log|A|)
- The log factor in the denominator is essentially tight
- This is a quantitative version of the "either expand or be structured" dichotomy

Reference:
[So09d] Solymosi, József, "Bounding multiplicative energy by the sumset",
Advances in Mathematics 222 (2009), 402-408.

Related: Problem 52 (the original Erdős-Szemerédi sum-product conjecture)

Tags: additive-combinatorics, sum-product, sumset, product-set
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Additive.Energy
import Mathlib.Combinatorics.Additive.CauchyDavenport

open Finset Real
open scoped Pointwise

namespace Erdos818

/-
## Part I: Basic Definitions
-/

/--
**Sumset:**
A + A = {a + b : a, b ∈ A}, the set of all pairwise sums.
-/
def sumset (A : Finset ℤ) : Finset ℤ :=
  (A ×ˢ A).image (fun p => p.1 + p.2)

/--
**Product set:**
A · A = {a · b : a, b ∈ A}, the set of all pairwise products.
-/
def productSet (A : Finset ℤ) : Finset ℤ :=
  (A ×ˢ A).image (fun p => p.1 * p.2)

/--
**Additive doubling constant:**
The ratio |A + A| / |A|. Small doubling means this is close to 1.
-/
noncomputable def additiveDoubling (A : Finset ℤ) : ℝ :=
  (sumset A).card / A.card

/--
**Small sumset condition:**
A has a "small" sumset if |A + A| ≤ K · |A| for some constant K.
-/
def hasSmallSumset (A : Finset ℤ) (K : ℝ) : Prop :=
  ((sumset A).card : ℝ) ≤ K * A.card

/-
## Part II: The Trivial Bounds
-/

/-
**Lower bound on sumset:**
|A + A| ≥ 2|A| - 1 for any nonempty set A.
(Take a + min A and a + max A for each a.)
-/

/-
**Lower bound on product set:**
|A · A| ≥ |A| for A ⊆ ℤ⁺ (roughly, since products spread out).
-/

/--
**Upper bound on product set:**
|A · A| ≤ |A|² always.
-/
theorem productSet_upper_bound (A : Finset ℤ) :
    (productSet A).card ≤ A.card ^ 2 := by
  unfold productSet
  calc ((A ×ˢ A).image (fun p => p.1 * p.2)).card
      ≤ (A ×ˢ A).card := Finset.card_image_le
    _ = A.card * A.card := Finset.card_product A A
    _ = A.card ^ 2 := by ring

/-- `sumset A` is the pointwise sum `A + A`. -/
theorem sumset_eq_add (A : Finset ℤ) : sumset A = A + A := by
  rw [sumset, Finset.add_def]

/--
**Sumset lower bound (proved):** `2|A| - 1 ≤ |A + A|` for nonempty `A ⊆ ℤ`.

This is the elementary lower bound quoted in Part II. It is the additive
Cauchy–Davenport bound for linearly ordered cancellative additive monoids
(`|A + B| ≥ |A| + |B| - 1`), specialized to `B = A` on `ℤ`, via Mathlib's
`cauchy_davenport_add_of_linearOrder_isCancelAdd`. Axiom-free.
-/
theorem sumset_lower_bound (A : Finset ℤ) (hne : A.Nonempty) :
    2 * A.card - 1 ≤ (sumset A).card := by
  rw [sumset_eq_add, two_mul]
  exact cauchy_davenport_add_of_linearOrder_isCancelAdd hne hne

/--
**Product set lower bound (proved):** `|A| ≤ |A · A|` for any `A ⊆ ℤ` containing a
nonzero element.

This is the multiplicative analogue of `sumset_lower_bound`, completing the
comment-only "Lower bound on product set" of Part II. Fix a nonzero `a₀ ∈ A`;
since `ℤ` is an integral domain, `a ↦ a₀ · a` is injective (`mul_left_cancel₀`),
and it maps `A` into the product set `A · A` (each `a₀ · a` is the product of two
elements of `A`). Hence `|A| = |a₀ · A| ≤ |A · A|`. Axiom-free.

The nonzero hypothesis is necessary: for `A = {0}`, `A · A = {0}`, so `|A| = 1`
holds, but for e.g. `A = {0}` the injection argument needs the nonzero pivot; a
set can fail to have a nonzero element only when `A ⊆ {0}`, where the bound is
still trivially true but not via this cancellation route.
-/
theorem productSet_lower_bound (A : Finset ℤ) {a₀ : ℤ} (ha₀ : a₀ ∈ A)
    (hne : a₀ ≠ 0) :
    A.card ≤ (productSet A).card := by
  have hinj : Set.InjOn (fun a => a₀ * a) A :=
    fun x _ y _ h => mul_left_cancel₀ hne h
  calc A.card
      = (A.image (fun a => a₀ * a)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (productSet A).card := by
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_image] at hx
        obtain ⟨a, ha, rfl⟩ := hx
        rw [productSet, Finset.mem_image]
        exact ⟨(a₀, a), Finset.mem_product.mpr ⟨ha₀, ha⟩, rfl⟩

/-
## Part III: The Original Conjecture
-/

/--
**Erdős Conjecture #818:**
If |A + A| ≤ K · |A| for some constant K, then
|A · A| ≫ |A|² / (log |A|)^C for some constants C, c > 0.

The absolute constant `c > 0` is essential and faithful to the `≫` in the
original statement: without it the claim is false on small sets. For example
A = {1, 2} has |A+A| = 3 ≤ 2·|A| (small sumset) and |A·A| = 3, but
|A|²/(log|A|)^C = 4/(log 2)^C > 4 for every C > 0 (since log 2 < 1). The
constant `c` absorbs these boundary effects, exactly as `≫` intends.
-/
def ErdosConjecture818 : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∃ c : ℝ, c > 0 ∧
    ∀ K : ℝ, K > 0 →
      ∀ A : Finset ℤ, A.card ≥ 2 →
        hasSmallSumset A K →
        ((productSet A).card : ℝ) ≥ c * (A.card : ℝ)^2 / (log A.card)^C

/-
## Part IV: Solymosi's Theorem (2009)
-/

/--
**Solymosi's Theorem (2009):**
If |A + A| ≤ K · |A|, then |A · A| ≥ c · |A|² / log |A|
for some absolute constant c > 0.

This is STRONGER than the original conjecture (C = 1 instead of arbitrary C).
-/
axiom solymosi_theorem :
    ∃ c : ℝ, c > 0 ∧
      ∀ K : ℝ, K > 0 →
        ∀ A : Finset ℤ, A.card ≥ 2 →
          hasSmallSumset A K →
          ((productSet A).card : ℝ) ≥ c * (A.card : ℝ)^2 / log A.card

/--
**The conjecture is true:**
Solymosi's theorem implies Erdős's conjecture.
-/
theorem erdos_818_proved : ErdosConjecture818 := by
  obtain ⟨c, hc_pos, hc_bound⟩ := solymosi_theorem
  -- Take C = 1 and the same absolute constant c as Solymosi's theorem.
  refine ⟨1, by norm_num, c, hc_pos, ?_⟩
  intro K hK A hA_card hA_small
  have hSoly := hc_bound K hK A hA_card hA_small
  -- (log |A|)^(1 : ℝ) = log |A|, so the goal is exactly Solymosi's bound.
  rw [Real.rpow_one]
  exact hSoly

/-
## Part V: Multiplicative Energy
-/

/--
**Multiplicative energy:**
E×(A) = |{(a₁, a₂, a₃, a₄) ∈ A⁴ : a₁a₂ = a₃a₄}|
Counts 4-tuples with equal products.
-/
def multiplicativeEnergy (A : Finset ℤ) : ℕ :=
  ((A ×ˢ A) ×ˢ (A ×ˢ A)).filter
    (fun x => x.1.1 * x.1.2 = x.2.1 * x.2.2) |>.card

/--
**Additive energy:**
E⁺(A) = |{(a₁, a₂, a₃, a₄) ∈ A⁴ : a₁+a₂ = a₃+a₄}|
-/
def additiveEnergy (A : Finset ℤ) : ℕ :=
  ((A ×ˢ A) ×ˢ (A ×ˢ A)).filter
    (fun x => x.1.1 + x.1.2 = x.2.1 + x.2.2) |>.card

/-
**Energy-cardinality relationship:**
E×(A) ≥ |A|⁴ / |AA| (by pigeonhole on products).
-/

/-
## Part V·b: The Cauchy–Schwarz energy lower bound (proved)

The first ingredient of Solymosi's strategy is the elementary Cauchy–Schwarz
lower bound `|A|⁴ ≤ |A·A| · E×(A)`. It is *not* the deep part of the argument —
it follows from grouping the `|A|²` pairs `(a, b)` by their product and applying
Cauchy–Schwarz to the fiber sizes. Mathlib already provides exactly this fact as
`Finset.le_card_mul_mul_mulEnergy`, so we connect our local definitions to
Mathlib's pointwise product and multiplicative energy and transport the bound.
-/

/-- `productSet A` is the pointwise product `A * A`. -/
theorem productSet_eq_mul (A : Finset ℤ) : productSet A = A * A := by
  rw [productSet, Finset.mul_def]

/-- Our `multiplicativeEnergy A` is Mathlib's `Finset.mulEnergy A A`. -/
theorem multiplicativeEnergy_eq_mulEnergy (A : Finset ℤ) :
    multiplicativeEnergy A = Finset.mulEnergy A A := by
  unfold multiplicativeEnergy
  exact (Finset.mulEnergy_eq_card_filter A A).symm

/--
**Cauchy–Schwarz energy lower bound (proved):**
`|A|⁴ ≤ |A·A| · E×(A)`.

This is step 1 of Solymosi's proof strategy. It is a genuine, fully verified
lemma (no axioms, no `sorry`): grouping the `|A|²` pairs `(a,b) ∈ A × A` by their
product and applying Cauchy–Schwarz to the fiber sizes gives the bound, which is
exactly Mathlib's `Finset.le_card_mul_mul_mulEnergy` specialized to `s = t = A`.
-/
theorem cauchy_schwarz_energy (A : Finset ℤ) :
    A.card ^ 4 ≤ (productSet A).card * multiplicativeEnergy A := by
  rw [productSet_eq_mul, multiplicativeEnergy_eq_mulEnergy]
  calc A.card ^ 4 = A.card ^ 2 * A.card ^ 2 := by ring
    _ ≤ (A * A).card * Finset.mulEnergy A A := Finset.le_card_mul_mul_mulEnergy A A

/--
**Solymosi reduction (proved, axiom-free modulo the stated energy hypothesis).**

Solymosi's strategy combines two ingredients:
* the Cauchy–Schwarz lower bound `|A|⁴ ≤ |A·A| · E×(A)` (proved above as
  `cauchy_schwarz_energy`, axiom-free), and
* the multiplicative-energy *upper* bound `E×(A) ≤ C · |A + A|² · log|A|`
  (Solymosi's core inequality, not yet in Mathlib).

Taking the second as an explicit hypothesis `hEnergy`, this lemma machine-checks
the full reduction to the product-set bound
`|A·A| ≥ |A|² / (C · K² · log|A|)` for any set with `|A + A| ≤ K·|A|`. It thereby
isolates the genuine external input (`hEnergy`) *without* introducing a new
axiom.

**Honest constant note.** The standard argument delivers the denominator
`C · K² · log|A|`, i.e. a `K²` dependence, not the `K` recorded in
`proof_outline` below (see that theorem's docstring): substituting the sumset
bound `|A + A| ≤ K·|A|` into `E×(A) ≤ C·|A+A|²·log|A|` costs the square. So this
lemma is the faithful consequence of the energy inequality; `proof_outline`'s
sharper `1/(K·log|A|)` form is a strictly stronger, still-open target. -/
theorem product_lower_of_mult_energy
    (A : Finset ℤ) (hA : A.card ≥ 2)
    (K : ℝ) (hK : K > 0) (hsmall : hasSmallSumset A K)
    (C : ℝ) (hC : C > 0)
    (hEnergy : (multiplicativeEnergy A : ℝ)
        ≤ C * ((sumset A).card : ℝ) ^ 2 * log A.card) :
    ((productSet A).card : ℝ)
        ≥ (A.card : ℝ) ^ 2 / (C * K ^ 2 * log A.card) := by
  -- Positivity facts.
  have hn2 : (2 : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hA
  have hnpos : (0 : ℝ) < (A.card : ℝ) := by linarith
  have hn2pos : (0 : ℝ) < (A.card : ℝ) ^ 2 := by positivity
  have hLpos : (0 : ℝ) < log (A.card : ℝ) := Real.log_pos (by linarith)
  have hSnn : (0 : ℝ) ≤ ((sumset A).card : ℝ) := by positivity
  have hPnn : (0 : ℝ) ≤ ((productSet A).card : ℝ) := by positivity
  have hM : (0 : ℝ) < C * K ^ 2 * log (A.card : ℝ) :=
    mul_pos (mul_pos hC (by positivity)) hLpos
  -- Square the small-sumset hypothesis: |A+A|² ≤ K²·|A|².
  have hS2 : ((sumset A).card : ℝ) ^ 2 ≤ K ^ 2 * (A.card : ℝ) ^ 2 := by
    nlinarith [mul_le_mul hsmall hsmall hSnn (mul_nonneg hK.le hnpos.le)]
  -- Energy is controlled by K²·|A|²·log|A|.
  have hE2 : (multiplicativeEnergy A : ℝ)
      ≤ C * (K ^ 2 * (A.card : ℝ) ^ 2) * log (A.card : ℝ) := by
    refine hEnergy.trans ?_
    apply mul_le_mul_of_nonneg_right _ hLpos.le
    exact mul_le_mul_of_nonneg_left hS2 hC.le
  -- Cauchy–Schwarz lower bound, transported to ℝ.
  have hcs : (A.card : ℝ) ^ 4
      ≤ ((productSet A).card : ℝ) * (multiplicativeEnergy A : ℝ) := by
    exact_mod_cast cauchy_schwarz_energy A
  -- Combine: |A|⁴ ≤ |A·A| · C·K²·|A|²·log|A|.
  have hchain : (A.card : ℝ) ^ 4
      ≤ ((productSet A).card : ℝ)
          * (C * (K ^ 2 * (A.card : ℝ) ^ 2) * log (A.card : ℝ)) :=
    hcs.trans (mul_le_mul_of_nonneg_left hE2 hPnn)
  -- Clear the denominator and cancel |A|².
  rw [ge_iff_le, div_le_iff₀ hM]
  nlinarith [hchain, hn2pos]

/-
**Solymosi's key lemma:**
Bounds multiplicative energy in terms of sumset size.
-/

/-
## Part VI: Proof Sketch
-/

/-
**Proof strategy:**
1. By Cauchy-Schwarz: E×(A) ≥ |A|⁴ / |AA|
2. Solymosi shows: E×(A) ≤ |A|² · |A+A| · log|A|
3. Combining: |A|⁴ / |AA| ≤ |A|² · |A+A| · log|A|
4. Rearranging: |AA| ≥ |A|⁴ / (|A|² · |A+A| · log|A|)
5. If |A+A| ≤ K|A|: |AA| ≥ |A|² / (K · log|A|)
-/
/-- The energy bounds combine to give Solymosi's result:
    From E×(A) ≥ |A|⁴/|AA| and E×(A) ≤ |A|²·|A+A|·log|A|,
    we get |AA| ≥ |A|²/(K·log|A|) when |A+A| ≤ K|A|.

    REMAINING GAP (sorry): this is the genuine energy argument and is the one
    open formalization target left in this file. It is *not* a consequence of
    `solymosi_theorem`: that axiom supplies an absolute constant `c > 0` with
    bound `c·|A|²/log|A|`, whereas this K-dependent bound `|A|²/(K·log|A|)`
    would require `c·K ≥ 1`, which the axiom does not provide.

    Step 1 of the strategy — the Cauchy–Schwarz lower bound
    `|A|⁴ ≤ |A·A|·E×(A)` — is now PROVED (`cauchy_schwarz_energy`, axiom-free,
    via Mathlib's `Finset.le_card_mul_mul_mulEnergy`). The remaining gap is
    therefore *exactly* Solymosi's multiplicative-energy upper bound
    `E×(A) ≤ C·|A+A|²·log|A|`, which is not yet formalized in Mathlib.

    The reduction from that energy inequality to a product-set bound is now
    machine-checked, axiom-free, as `product_lower_of_mult_energy` — but it
    delivers the `1/(C·K²·log|A|)` form, since substituting `|A+A| ≤ K·|A|`
    into the energy bound costs a factor of `K`. This theorem's sharper
    `1/(K·log|A|)` denominator is a strictly stronger, still-open target. -/
theorem proof_outline (A : Finset ℤ) (hA : A.card ≥ 2) (hne : A.Nonempty)
    (K : ℝ) (hK : K > 0) (hsmall : hasSmallSumset A K) :
    ((productSet A).card : ℝ) ≥
      (A.card : ℝ)^2 / (K * log A.card) := by
  sorry

/-
**The log factor is necessary:**
There exist sets A with small sumset where |AA| = O(|A|² / log|A|).
So the log factor cannot be removed entirely.
-/
/- The log factor is tight: there exist sets A with |A+A| ≤ 2|A| - 1 -/

/-
## Part VII: Connection to Sum-Product Conjecture
-/

/-
**Sum-Product Dichotomy:**
For any finite A ⊂ ℤ, max(|A+A|, |AA|) is large.

This problem (818) explores what happens when we force |A+A| to be small:
the product set must compensate and be large.
-/

/-
**Connection to Problem 52:**
Problem 52 asks: max(|A+A|, |AA|) ≥ |A|^{2-ε}?

Problem 818 asks: if |A+A| ≤ K|A|, then |AA| ≥ |A|²/log|A|?

The latter is a conditional result: GIVEN small sumset, product set is large.
-/
/- Problem 52 conjectures max(|A+A|, |AA|) ≥ |A|^{2-ε}. -/

/-
## Part VIII: Examples
-/

/-
**Example: Arithmetic progression**
If A = {1, 2, ..., n}, then:
- |A + A| = 2n - 1 (small, additive doubling ~2)
- |A · A| ≈ n²/log n (by Erdős multiplication table problem)
-/
/- For A = {1, ..., n}: |A+A| = 2n-1, |AA| ~ n²/log n. -/

/-
**Example: Geometric progression**
If A = {1, r, r², ..., r^{n-1}}, then:
- |A + A| ≈ n² (large, no additive structure)
- |A · A| = 2n - 1 (small, multiplicative structure)
This shows the opposite extreme.
-/
/- For A = {1, r, r², ..., r^{n-1}} with r > n: -/

/-
## Part IX: Summary
-/

/-
**Erdős Problem #818: SOLVED**

QUESTION: If |A+A| ≪ |A|, is |AA| ≫ |A|²/(log|A|)^C for some C?

ANSWER: YES

PROOF: Solymosi (2009) proved the stronger bound |AA| ≫ |A|²/log|A|.

KEY TECHNIQUE: Bound multiplicative energy using sumset structure.
-/
/-- **Summary theorem:** Original conjecture + Solymosi's stronger result. -/
theorem erdos_818_summary :
    -- Original conjecture is true
    ErdosConjecture818 ∧
    -- Solymosi's stronger result holds
    (∃ c : ℝ, c > 0 ∧
      ∀ K : ℝ, K > 0 →
        ∀ A : Finset ℤ, A.card ≥ 2 →
          hasSmallSumset A K →
          ((productSet A).card : ℝ) ≥ c * (A.card : ℝ)^2 / log A.card) := by
  constructor
  · exact erdos_818_proved
  · exact solymosi_theorem

/-- Small additive doubling forces large multiplicative expansion:
    the sum-product phenomenon quantified. For an absolute constant `c > 0`,
    a set with small sumset has product set of size `≥ c·|A|²/log|A|`. The
    constant is necessary (see the discussion on `ErdosConjecture818`), so we
    state the bound with it explicitly rather than the unsound `c = 1` form. -/
theorem key_insight (A : Finset ℤ) (hA : A.card ≥ 2)
    (K : ℝ) (hK : K > 0) (hsmall : hasSmallSumset A K) :
    ∃ c : ℝ, c > 0 ∧
      ((productSet A).card : ℝ) ≥ c * (A.card : ℝ)^2 / log A.card := by
  obtain ⟨c, hc_pos, hc_bound⟩ := solymosi_theorem
  exact ⟨c, hc_pos, hc_bound K hK A hA hsmall⟩

end Erdos818
