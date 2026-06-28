/-
Erdős Problem #818: Product Set Lower Bound for Small Sumsets

Source: https://erdosproblems.com/818
Status: SOLVED (axiomatized analytic core)

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
- If |A+A| ≤ K·|A| (small sumset), then |AA| ≥ |A|² / (C · K² · log|A|)
- The log factor in the denominator is essentially tight
- This is a quantitative version of the "either expand or be structured" dichotomy

Architecture of this file:
The deep, irreducible input is Solymosi's multiplicative-energy upper bound
`E×(A) ≤ C·|A+A|²·log|A|` (not in Mathlib), which we *axiomatize*
(`solymosi_energy_bound`). Everything else — the Cauchy–Schwarz energy lower
bound, the derivation of the product-set estimate, and the headline theorems —
is then *proved* from that single axiom. In particular `solymosi_theorem`,
`erdos_818_proved`, `key_insight` and `proof_outline` are no longer axioms or
sorries; they are machine-checked consequences of `solymosi_energy_bound`.

A previous version of this file axiomatized the entire conclusion with the
quantifier order `∃ c, ∀ K, ...`. That statement is in fact FALSE: with `c`
chosen before `K`, taking `K` large makes `hasSmallSumset A K` hold for every
set `A`, so the claim would force `|AA| ≥ c·|A|²/log|A|` for all sets — which
fails for geometric progressions (|AA| = 2|A|−1 ≪ |A|²/log|A|). The honest
statement makes `c` depend on `K`, i.e. `∀ K, ∃ c, ...`; this is what we prove.

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

/-
## Part III: Multiplicative and Additive Energy
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
## Part IV: The Cauchy–Schwarz energy lower bound (proved)

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

/-
## Part V: Solymosi's energy bound (axiomatized) and the product-set estimate

Solymosi's genuine contribution — and the only part not provable from Mathlib
today — is the multiplicative-energy upper bound

  E×(A) ≤ C · |A+A|² · log|A|

for an absolute constant `C > 0`. (For positive reals one may take `C = 4` with
`log` to base 2; over ℤ the same bound holds up to the absolute constant, by
splitting into sign classes.) Its proof is the dyadic-slopes geometric argument
of [So09d], which Mathlib does not yet contain, so we state it as the single
axiom of this file. Everything below is *proved* from this axiom.
-/

/--
**Solymosi's multiplicative-energy bound (axiomatized analytic core).**

`E×(A) ≤ C · |A+A|² · log|A|` for an absolute constant `C > 0`.

This is the irreducible deep input (Solymosi 2009): it is a true theorem of
additive combinatorics that is not currently formalized in Mathlib. Reducing the
whole problem to this single, honest assumption (rather than axiomatizing the
conclusion outright) is the point of this file.
-/
axiom solymosi_energy_bound :
    ∃ C : ℝ, C > 0 ∧
      ∀ A : Finset ℤ, A.card ≥ 2 →
        (multiplicativeEnergy A : ℝ) ≤ C * ((sumset A).card : ℝ) ^ 2 * Real.log A.card

/--
**The product-set estimate (proved from the energy bound).**

Combining the proved Cauchy–Schwarz lower bound `|A|⁴ ≤ |A·A|·E×(A)` with the
axiomatized upper bound `E×(A) ≤ C·|A+A|²·log|A|`, and using `|A+A| ≤ K|A|`,
gives the quantitative lower bound

  |A·A| ≥ |A|² / (C · K² · log|A|).

The `K²` (rather than `K`) is genuine: it comes from squaring `|A+A| ≤ K|A|` in
Solymosi's `|A+A|²` energy bound. This corrects the earlier (dimensionally
inconsistent) sketch `|A·A| ≥ |A|²/(K·log|A|)`.
-/
theorem productSet_lower_bound_of_smallSumset :
    ∃ C : ℝ, C > 0 ∧
      ∀ K : ℝ, K > 0 →
        ∀ A : Finset ℤ, A.card ≥ 2 →
          hasSmallSumset A K →
            ((productSet A).card : ℝ) ≥ (A.card : ℝ) ^ 2 / (C * K ^ 2 * Real.log A.card) := by
  obtain ⟨C, hC, hEbound⟩ := solymosi_energy_bound
  refine ⟨C, hC, ?_⟩
  intro K hK A hA hsmall
  -- Positivity facts.
  have hn1 : (1 : ℝ) < (A.card : ℝ) := by
    have h : 1 < A.card := by omega
    exact_mod_cast h
  have hL : 0 < Real.log A.card := Real.log_pos hn1
  have hP : 0 ≤ ((productSet A).card : ℝ) := by positivity
  have hS : 0 ≤ ((sumset A).card : ℝ) := by positivity
  -- Cauchy–Schwarz, cast to ℝ.
  have hCS : (A.card : ℝ) ^ 4 ≤ ((productSet A).card : ℝ) * (multiplicativeEnergy A : ℝ) := by
    exact_mod_cast cauchy_schwarz_energy A
  -- Small sumset as a real inequality, then squared.
  have hsmall' : ((sumset A).card : ℝ) ≤ K * (A.card : ℝ) := hsmall
  have hKn : 0 ≤ K * (A.card : ℝ) := le_trans hS hsmall'
  have hS2 : ((sumset A).card : ℝ) ^ 2 ≤ K ^ 2 * (A.card : ℝ) ^ 2 := by
    have h := mul_le_mul hsmall' hsmall' hS hKn
    calc ((sumset A).card : ℝ) ^ 2
        = ((sumset A).card : ℝ) * ((sumset A).card : ℝ) := by ring
      _ ≤ (K * (A.card : ℝ)) * (K * (A.card : ℝ)) := h
      _ = K ^ 2 * (A.card : ℝ) ^ 2 := by ring
  -- Energy upper bound with the squared sumset.
  have hE : (multiplicativeEnergy A : ℝ) ≤ C * (K ^ 2 * (A.card : ℝ) ^ 2) * Real.log A.card := by
    calc (multiplicativeEnergy A : ℝ)
        ≤ C * ((sumset A).card : ℝ) ^ 2 * Real.log A.card := hEbound A hA
      _ ≤ C * (K ^ 2 * (A.card : ℝ) ^ 2) * Real.log A.card := by
          apply mul_le_mul_of_nonneg_right _ hL.le
          exact mul_le_mul_of_nonneg_left hS2 hC.le
  -- Combine Cauchy–Schwarz with the energy bound.
  have hPE : (A.card : ℝ) ^ 4 ≤
      ((productSet A).card : ℝ) * (C * (K ^ 2 * (A.card : ℝ) ^ 2) * Real.log A.card) :=
    le_trans hCS (mul_le_mul_of_nonneg_left hE hP)
  -- Cancel the common factor |A|².
  have hn2 : (0 : ℝ) < (A.card : ℝ) ^ 2 := by positivity
  have key : (A.card : ℝ) ^ 2 ≤
      ((productSet A).card : ℝ) * (C * K ^ 2 * Real.log A.card) := by
    have e : ((productSet A).card : ℝ) * (C * (K ^ 2 * (A.card : ℝ) ^ 2) * Real.log A.card)
            = (((productSet A).card : ℝ) * (C * K ^ 2 * Real.log A.card)) * (A.card : ℝ) ^ 2 := by
      ring
    have e4 : (A.card : ℝ) ^ 4 = (A.card : ℝ) ^ 2 * (A.card : ℝ) ^ 2 := by ring
    rw [e, e4] at hPE
    exact le_of_mul_le_mul_right hPE hn2
  -- Conclude by dividing.
  have hden : 0 < C * K ^ 2 * Real.log A.card :=
    mul_pos (mul_pos hC (pow_pos hK 2)) hL
  rw [ge_iff_le, div_le_iff₀ hden]
  exact key

/-
## Part VI: The original conjecture and Solymosi's theorem
-/

/--
**Erdős Conjecture #818 (with corrected quantifiers):**
There is a constant `C > 0` such that, for every doubling threshold `K > 0`,
there is a constant `c = c(K) > 0` with

  |A·A| ≥ c · |A|² / (log|A|)^C   whenever |A+A| ≤ K·|A|.

The dependence `c = c(K)` is essential and faithful to the original `≫`/`≪`
notation: the implied constant in the conclusion depends on the implied constant
in the hypothesis. The earlier `∃ c, ∀ K, ...` form is false (take `K` large to
cover every set, including product-poor geometric progressions).
-/
def ErdosConjecture818 : Prop :=
  ∃ C : ℝ, C > 0 ∧
    ∀ K : ℝ, K > 0 → ∃ c : ℝ, c > 0 ∧
      ∀ A : Finset ℤ, A.card ≥ 2 →
        hasSmallSumset A K →
          ((productSet A).card : ℝ) ≥ c * (A.card : ℝ) ^ 2 / (Real.log A.card) ^ C

/--
**Solymosi's Theorem (2009), proved from the energy bound.**

For each doubling threshold `K > 0` there is a constant `c = c(K) > 0` with
`|A·A| ≥ c·|A|²/log|A|` whenever `|A+A| ≤ K·|A|`. Concretely one may take
`c = 1/(C·K²)` where `C` is the constant from `solymosi_energy_bound`.

This is no longer an axiom: it is derived from `productSet_lower_bound_of_smallSumset`.
-/
theorem solymosi_theorem :
    ∀ K : ℝ, K > 0 → ∃ c : ℝ, c > 0 ∧
      ∀ A : Finset ℤ, A.card ≥ 2 →
        hasSmallSumset A K →
          ((productSet A).card : ℝ) ≥ c * (A.card : ℝ) ^ 2 / Real.log A.card := by
  obtain ⟨C, hC, hbound⟩ := productSet_lower_bound_of_smallSumset
  intro K hK
  refine ⟨1 / (C * K ^ 2), by positivity, ?_⟩
  intro A hA hsmall
  have hb := hbound K hK A hA hsmall
  -- Rewrite the `c·|A|²/log` shape into the `|A|²/(C·K²·log)` shape proved above.
  have hCK : C * K ^ 2 ≠ 0 := mul_ne_zero (ne_of_gt hC) (pow_ne_zero 2 (ne_of_gt hK))
  have heq : (1 / (C * K ^ 2)) * (A.card : ℝ) ^ 2 / Real.log A.card
           = (A.card : ℝ) ^ 2 / (C * K ^ 2 * Real.log A.card) := by
    rw [div_mul_eq_mul_div, one_mul, div_div]
  rw [ge_iff_le, heq]
  exact hb

/--
**The conjecture is true:**
`ErdosConjecture818` holds with `C = 1`, using Solymosi's theorem (which already
gives the stronger `log¹` denominator).
-/
theorem erdos_818_proved : ErdosConjecture818 := by
  refine ⟨1, by norm_num, ?_⟩
  intro K hK
  obtain ⟨c, hc, hbound⟩ := solymosi_theorem K hK
  refine ⟨c, hc, ?_⟩
  intro A hA hsmall
  have hb := hbound A hA hsmall
  -- (log |A|)^(1 : ℝ) = log |A|.
  rw [Real.rpow_one]
  exact hb

/-
## Part VII: Proof recap

**Proof strategy (now fully formalized modulo `solymosi_energy_bound`):**
1. Cauchy–Schwarz: E×(A) ≥ |A|⁴/|AA|            (`cauchy_schwarz_energy`, proved)
2. Solymosi's bound: E×(A) ≤ C·|A+A|²·log|A|    (`solymosi_energy_bound`, axiom)
3. Combine: |A|⁴/|AA| ≤ C·|A+A|²·log|A|
4. If |A+A| ≤ K|A|, then |A+A|² ≤ K²|A|², so |A|⁴/|AA| ≤ C·K²·|A|²·log|A|
5. Rearrange: |AA| ≥ |A|²/(C·K²·log|A|)         (`productSet_lower_bound_of_smallSumset`)
-/

/-- The energy bounds combine to give Solymosi's result, in the explicit
    `K`-dependent form. This is the former `proof_outline` `sorry`, now *proved*:
    it is a direct corollary of `productSet_lower_bound_of_smallSumset`. Note the
    `K²` denominator — the earlier `|A|²/(K·log|A|)` target was not provable, as
    Solymosi's `|A+A|²` energy bound necessarily contributes `K²`. -/
theorem proof_outline (A : Finset ℤ) (hA : A.card ≥ 2)
    (K : ℝ) (hK : K > 0) (hsmall : hasSmallSumset A K) :
    ∃ C : ℝ, C > 0 ∧
      ((productSet A).card : ℝ) ≥ (A.card : ℝ) ^ 2 / (C * K ^ 2 * Real.log A.card) := by
  obtain ⟨C, hC, hbound⟩ := productSet_lower_bound_of_smallSumset
  exact ⟨C, hC, hbound K hK A hA hsmall⟩

/-
**The log factor is necessary:**
There exist sets A with small sumset where |AA| = O(|A|² / log|A|).
So the log factor cannot be removed entirely (Erdős multiplication table problem).
-/

/-
## Part VIII: Connection to Sum-Product Conjecture

**Sum-Product Dichotomy:**
For any finite A ⊂ ℤ, max(|A+A|, |AA|) is large. This problem (818) explores what
happens when we force |A+A| to be small: the product set must compensate.

**Connection to Problem 52:**
Problem 52 asks: max(|A+A|, |AA|) ≥ |A|^{2-ε}? Problem 818 is the conditional
version: GIVEN small sumset, the product set is large.

**Examples.**
- Arithmetic progression A = {1, …, n}: |A+A| = 2n−1 (small), |AA| ≈ n²/log n.
- Geometric progression A = {1, r, …, r^{n-1}} with r > n: |A+A| ≈ n² (large),
  |AA| = 2n−1 (small). This is the opposite extreme, and is exactly why the
  `∃ c, ∀ K` form of the statement fails.
-/

/-
## Part IX: Summary
-/

/-- **Summary theorem:** the corrected conjecture together with Solymosi's
    `K`-dependent quantitative bound. -/
theorem erdos_818_summary :
    ErdosConjecture818 ∧
    (∀ K : ℝ, K > 0 → ∃ c : ℝ, c > 0 ∧
      ∀ A : Finset ℤ, A.card ≥ 2 →
        hasSmallSumset A K →
          ((productSet A).card : ℝ) ≥ c * (A.card : ℝ) ^ 2 / Real.log A.card) :=
  ⟨erdos_818_proved, solymosi_theorem⟩

/-- Small additive doubling forces large multiplicative expansion: the
    sum-product phenomenon quantified. For a set with small sumset `|A+A| ≤ K|A|`,
    there is a constant `c = c(K) > 0` with product set of size `≥ c·|A|²/log|A|`.
    The constant depends on `K` (necessarily — see the geometric-progression
    discussion), so we state it under the fixed-`K` hypothesis. -/
theorem key_insight (A : Finset ℤ) (hA : A.card ≥ 2)
    (K : ℝ) (hK : K > 0) (hsmall : hasSmallSumset A K) :
    ∃ c : ℝ, c > 0 ∧
      ((productSet A).card : ℝ) ≥ c * (A.card : ℝ) ^ 2 / Real.log A.card := by
  obtain ⟨c, hc, hbound⟩ := solymosi_theorem K hK
  exact ⟨c, hc, hbound A hA hsmall⟩

end Erdos818
