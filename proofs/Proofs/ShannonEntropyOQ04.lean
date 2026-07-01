/-
  Shannon Entropy is a Concave Functional

  The parent entry `shannon-entropy` establishes the *value* half of the
  maximum-entropy principle: `H(p) ≤ log |α|`, with equality iff `p` is
  uniform (`entropy_le_log_card`, `entropy_eq_log_card_iff_uniform`), proved
  via the Gibbs inequality.

  This child proves the complementary *structural* half stated in the same
  open question: the Shannon entropy functional

      H(p) = -∑ₓ p(x) log p(x)

  is a **concave** function of the distribution `p`. Concavity is the reason
  the maximum is attained at the barycentre of the simplex (the uniform
  distribution) and underpins every "mixing increases entropy" argument in
  coding, statistics, and thermodynamics.

  The clean route bridges the file's ad-hoc summand (with the convention
  `0 log 0 = 0`) to Mathlib's `Real.negMulLog x = -x log x`, which already
  carries `Real.negMulLog_zero : negMulLog 0 = 0` and, crucially,
  `Real.concaveOn_negMulLog : ConcaveOn ℝ (Ici 0) negMulLog`. Entropy is then
  a finite sum of concavities-of-a-coordinate, hence concave.

  Key results:
  - `shannonEntropy_eq_sum_negMulLog`: `H(p) = ∑ₓ negMulLog (p x)` (the bridge).
  - `concaveOn_shannonEntropy`: `H` is concave on the non-negative orthant.
  - `concaveOn_shannonEntropy_stdSimplex`: `H` is concave on the probability
    simplex — the standard textbook statement.

  Claude Shannon (1948)
-/
import Mathlib

namespace InformationTheory.EntropyConcavity

open Finset

-- Shannon entropy for finite distributions (matches the parent `shannon-entropy`).
-- Convention: 0 log 0 = 0.
noncomputable def shannonEntropy {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → ℝ) : ℝ :=
  -∑ x : α, if p x = 0 then 0 else p x * Real.log (p x)

-- ============================================================
-- Bridge to Mathlib's `negMulLog`
-- ============================================================

/-- **Bridge lemma.** The entropy summand `if p x = 0 then 0 else p x log p x`,
    once negated, is exactly `Real.negMulLog (p x) = -p x log p x`: the `x = 0`
    branch matches `negMulLog 0 = 0`, the `x ≠ 0` branch matches the definition.
    Hence `H(p) = ∑ₓ negMulLog (p x)`, connecting the file's convention-based
    definition to Mathlib's `negMulLog` API. -/
theorem shannonEntropy_eq_sum_negMulLog {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → ℝ) :
    shannonEntropy p = ∑ x : α, Real.negMulLog (p x) := by
  unfold shannonEntropy
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases h : p x = 0
  · simp [h]
  · simp only [if_neg h, Real.negMulLog_def]; ring

-- ============================================================
-- Concavity of a finite sum of concave coordinate functions
-- ============================================================

/-- A finite sum of functions, each concave on a common convex set `s`, is
    concave on `s`. Mathlib has `ConcaveOn.add` but no packaged `Finset` sum
    version; this is the straightforward `Finset.induction` fold. -/
private theorem concaveOn_finset_sum {ι E : Type*} [AddCommGroup E] [Module ℝ E]
    {s : Set E} (hs : Convex ℝ s) (g : ι → E → ℝ) :
    ∀ t : Finset ι, (∀ i ∈ t, ConcaveOn ℝ s (g i)) →
      ConcaveOn ℝ s (fun x => ∑ i ∈ t, g i x) := by
  classical
  intro t
  induction t using Finset.induction_on with
  | empty => intro _; simpa using concaveOn_const (0 : ℝ) hs
  | @insert a u ha ih =>
      intro hg
      rw [show (fun x => ∑ i ∈ insert a u, g i x)
            = g a + (fun x => ∑ i ∈ u, g i x) from by
              funext x; simp [Finset.sum_insert ha]]
      exact (hg a (Finset.mem_insert_self a u)).add
        (ih (fun i hi => hg i (Finset.mem_insert_of_mem hi)))

-- ============================================================
-- Concavity of Shannon entropy
-- ============================================================

/-- The non-negative orthant `{p | ∀ i, 0 ≤ p i}` is convex. -/
theorem convex_nonneg_orthant {α : Type*} [Fintype α] :
    Convex ℝ {p : α → ℝ | ∀ i, 0 ≤ p i} := by
  intro p hp q hq a b ha hb _ i
  simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    using add_nonneg (mul_nonneg ha (hp i)) (mul_nonneg hb (hq i))

/-- **Shannon entropy is concave.** As a function of the distribution `p`, the
    entropy `H(p) = -∑ₓ p(x) log p(x)` is concave on the non-negative orthant.

    Proof: rewrite `H` as `∑ₓ negMulLog (p x)` (`shannonEntropy_eq_sum_negMulLog`).
    Each coordinate map `p ↦ negMulLog (p x)` is the concave function
    `Real.negMulLog` (concave on `Ici 0`) precomposed with the linear coordinate
    projection `LinearMap.proj x`, restricted to the orthant where every
    coordinate is `≥ 0`. A finite sum of concave functions is concave. -/
theorem concaveOn_shannonEntropy {α : Type*} [Fintype α] [DecidableEq α] :
    ConcaveOn ℝ {p : α → ℝ | ∀ i, 0 ≤ p i} shannonEntropy := by
  have hconv := convex_nonneg_orthant (α := α)
  rw [show shannonEntropy = fun p : α → ℝ => ∑ i : α, Real.negMulLog (p i) from
        funext shannonEntropy_eq_sum_negMulLog]
  refine concaveOn_finset_sum hconv (fun i p => Real.negMulLog (p i)) Finset.univ
    (fun i _ => ?_)
  -- `p ↦ negMulLog (p i)` = `negMulLog ∘ proj i`, concave via comp_linearMap + subset.
  have hcomp :=
    Real.concaveOn_negMulLog.comp_linearMap (LinearMap.proj i : (α → ℝ) →ₗ[ℝ] ℝ)
  have hsub : {p : α → ℝ | ∀ j, 0 ≤ p j}
      ⊆ (LinearMap.proj i : (α → ℝ) →ₗ[ℝ] ℝ) ⁻¹' Set.Ici 0 := by
    intro p hp
    simp only [Set.mem_preimage, Set.mem_Ici, LinearMap.proj_apply]
    exact hp i
  have hcongr : (Real.negMulLog ∘ (LinearMap.proj i : (α → ℝ) →ₗ[ℝ] ℝ))
      = fun p : α → ℝ => Real.negMulLog (p i) := by
    funext p; simp [Function.comp, LinearMap.proj_apply]
  have := (hcomp.subset hsub hconv)
  rwa [hcongr] at this

/-- **Shannon entropy is concave on the probability simplex.** The standard
    textbook statement: restricting `concaveOn_shannonEntropy` to the standard
    simplex `stdSimplex ℝ α = {p | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1}`. -/
theorem concaveOn_shannonEntropy_stdSimplex {α : Type*} [Fintype α] [DecidableEq α] :
    ConcaveOn ℝ (stdSimplex ℝ α) shannonEntropy :=
  concaveOn_shannonEntropy.subset (fun _ hp => hp.1) (convex_stdSimplex ℝ α)

end InformationTheory.EntropyConcavity
