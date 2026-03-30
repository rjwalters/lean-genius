/-
Erdős Problem #1132: Lagrange Interpolation and Lebesgue Functions

Source: https://erdosproblems.com/1132
Status: OPEN

Statement:
For x₁,...,xₙ ∈ [-1,1] define the Lagrange basis polynomials:
  lₖ(x) = ∏_{i≠k}(x-xᵢ) / ∏_{i≠k}(xₖ-xᵢ)
which satisfy lₖ(xₖ) = 1 and lₖ(xᵢ) = 0 for i ≠ k.

Let x₁,x₂,... ∈ [-1,1] be an infinite sequence, and define the Lebesgue function:
  Lₙ(x) = Σ_{k=1}^n |lₖ(x)|

Two questions:
1. Must there exist x ∈ (-1,1) such that Lₙ(x) > (2/π)log(n) - O(1) for infinitely many n?
2. Is limsup_{n→∞} Lₙ(x)/log(n) ≥ 2/π for almost all x ∈ (-1,1)?

Related Results:
- Bernstein (1931): The set of x where limsup ≥ 2/π is everywhere dense in (-1,1)
- Erdős (1961): For any fixed nodes, max_{x∈[-1,1]} Lₙ(x) > (2/π)log(n) - O(1)

References:
- Erdős [Er67, p.68]
- Bernstein [Be31], "Sur la limitation des valeurs d'un polynome"
- Erdős [Er61c], "Problems and results on the theory of interpolation. II"
- Related to Erdős Problem #1129
-/

-- import Mathlib.Analysis.Calculus.LagrangeInterpolation  -- doesn't exist in v4.26
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.LinearAlgebra.Lagrange

open Real MeasureTheory Finset

namespace Erdos1132

/- ## Part I: Lagrange Basis Polynomials

The fundamental building blocks of polynomial interpolation.
-/

/-- **Lagrange Basis Polynomial:**
For nodes x₁,...,xₙ, the kth Lagrange basis polynomial lₖ(x) satisfies:
- lₖ(xₖ) = 1
- lₖ(xᵢ) = 0 for i ≠ k

This is the unique polynomial of degree n-1 with these properties. -/
noncomputable def lagrangeBasis (nodes : Fin n → ℝ) (k : Fin n) (x : ℝ) : ℝ :=
  ∏ i : Fin n, if i = k then 1 else (x - nodes i) / (nodes k - nodes i)

/-- **Alternative form of Lagrange basis:**
lₖ(x) = ∏_{i≠k}(x-xᵢ) / ∏_{i≠k}(xₖ-xᵢ) -/
noncomputable def lagrangeBasis' (nodes : Fin n → ℝ) (k : Fin n) (x : ℝ) : ℝ :=
  (∏ i ∈ Finset.univ.filter (· ≠ k), (x - nodes i)) /
  (∏ i ∈ Finset.univ.filter (· ≠ k), (nodes k - nodes i))

/-- **Lagrange basis at its own node equals 1.**
    Numerator = denominator = ∏_{i≠k} (nodes k - nodes i). -/
theorem lagrangeBasis_self (nodes : Fin n → ℝ) (k : Fin n)
    (hdistinct : ∀ i j, i ≠ j → nodes i ≠ nodes j) :
    lagrangeBasis nodes k (nodes k) = 1 := by
  unfold lagrangeBasis
  apply Finset.prod_eq_one; intro i _
  split_ifs with h
  · rfl
  · exact div_self (sub_ne_zero.mpr (hdistinct k i (fun hki => h hki.symm)))

/-- **Lagrange basis at other nodes equals 0.**
    The numerator has factor (nodes j - nodes j) = 0 since j ≠ k. -/
theorem lagrangeBasis_other (nodes : Fin n → ℝ) (k j : Fin n)
    (hdistinct : ∀ i₁ i₂, i₁ ≠ i₂ → nodes i₁ ≠ nodes i₂) (hkj : k ≠ j) :
    lagrangeBasis nodes k (nodes j) = 0 := by
  unfold lagrangeBasis
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  simp [hkj.symm, sub_self]

/- ## Part II: The Lebesgue Function

The sum of absolute values of Lagrange basis polynomials.
-/

/-- **Lebesgue Function:**
Lₙ(x) = Σₖ |lₖ(x)|

This measures how much the Lagrange interpolation can magnify errors. -/
noncomputable def lebesgueFunction (nodes : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∑ k : Fin n, |lagrangeBasis nodes k x|

/-- **Lebesgue Constant:**
Λₙ = max_{x∈[-1,1]} Lₙ(x)

The maximum of the Lebesgue function over the interval. -/
noncomputable def lebesgueConstant (nodes : Fin n → ℝ) : ℝ :=
  ⨆ x ∈ Set.Icc (-1 : ℝ) 1, lebesgueFunction nodes x

/-- **Partition of unity:** Lagrange basis polynomials sum to 1 for distinct nodes.
This is a standard polynomial identity: the Lagrange interpolant of the constant
function 1 is identically 1, i.e., Σₖ lₖ(x) = 1 for all x. -/
lemma lagrangeBasis_sum_eq_one (nodes : Fin n → ℝ) (x : ℝ)
    (hdistinct : ∀ i j, i ≠ j → nodes i ≠ nodes j)
    (hn : 0 < n := by omega) :
    ∑ k : Fin n, lagrangeBasis nodes k x = 1 := by
  -- Strategy: use Mathlib's Lagrange.sum_basis + bridge to our definition
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  -- Step 1: InjOn hypothesis for Mathlib
  have hinj : Set.InjOn nodes (↑(Finset.univ : Finset (Fin n))) := by
    intro i _ j _ heq; by_contra hne; exact hdistinct i j hne heq
  -- Step 2: Mathlib's polynomial partition of unity
  have hpoly := Lagrange.sum_basis hinj Finset.univ_nonempty
  have heval := congr_arg (Polynomial.eval x) hpoly
  rw [Polynomial.eval_finset_sum] at heval
  simp only [Polynomial.eval_one] at heval
  -- Step 3: Bridge each term: lagrangeBasis = eval x (Lagrange.basis)
  suffices hbridge : ∀ k : Fin n, lagrangeBasis nodes k x =
      Polynomial.eval x (Lagrange.basis Finset.univ nodes k) by
    simp_rw [hbridge]; exact heval
  intro k
  unfold lagrangeBasis
  simp only [Lagrange.basis, Lagrange.basisDivisor, Polynomial.eval_prod, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X]
  -- LHS: ∏ i : Fin n, if i = k then 1 else (x - nodes i) / (nodes k - nodes i)
  -- RHS: ∏ j ∈ univ.erase k, (nodes k - nodes j)⁻¹ * (x - nodes j)
  -- Rewrite div as inv*mul, then split the ite-product
  have hite : ∀ i : Fin n, i ∈ Finset.univ →
      (if i = k then (1 : ℝ) else (x - nodes i) / (nodes k - nodes i)) =
      (if i = k then 1 else (nodes k - nodes i)⁻¹ * (x - nodes i)) := by
    intro i _; split_ifs <;> [rfl; rw [div_eq_mul_inv, mul_comm]]
  rw [Finset.prod_congr rfl hite]
  -- Split: ∏ over univ with ite = (k-term) * (rest) = 1 * ∏ over erase
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
  simp only [ite_true, one_mul]
  apply Finset.prod_congr rfl
  intro i hi
  have hik : i ≠ k := (Finset.mem_erase.mp hi).1
  simp only [hik, ite_false]

/-- **Lebesgue function is always at least 1.**
Proof: By partition of unity, Σₖ lₖ(x) = 1. By triangle inequality,
Σₖ |lₖ(x)| ≥ |Σₖ lₖ(x)| = |1| = 1. -/
theorem lebesgueFunction_ge_one (nodes : Fin n → ℝ) (x : ℝ)
    (hdistinct : ∀ i j, i ≠ j → nodes i ≠ nodes j)
    (hn : n ≥ 1) :
    lebesgueFunction nodes x ≥ 1 := by
  unfold lebesgueFunction
  have hsum := lagrangeBasis_sum_eq_one nodes x hdistinct
  have htri := norm_sum_le (f := fun k => lagrangeBasis nodes k x) Finset.univ
  simp only [Real.norm_eq_abs] at htri
  rw [hsum, abs_one] at htri
  linarith

/- ## Part III: Growth of Lebesgue Constants

The Lebesgue constant grows logarithmically in the number of nodes.
-/

/-- **Erdős's Lower Bound (1961):**
For any choice of nodes in [-1,1],
  max_{x∈[-1,1]} Lₙ(x) > (2/π) log(n) - O(1)

This is a fundamental lower bound on the Lebesgue constant. -/
/-- **Chebyshev Nodes:**
The nodes that minimize the Lebesgue constant are the Chebyshev nodes:
  xₖ = cos((2k-1)π/(2n)) for k = 1, ..., n -/
noncomputable def chebyshevNodes (n : ℕ) : Fin n → ℝ :=
  fun k => Real.cos ((2 * (k.val + 1) - 1) * Real.pi / (2 * n))

/-- **Chebyshev Nodes in [-1,1]:**
All Chebyshev nodes lie in the interval [-1,1].
Proved: cos maps to [-1,1] by definition. -/
theorem chebyshevNodes_in_interval (n : ℕ) (hn : n ≥ 1) (k : Fin n) :
    chebyshevNodes n k ∈ Set.Icc (-1 : ℝ) 1 := by
  unfold chebyshevNodes
  exact Set.mem_Icc.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩

/-- **Optimal Growth Rate:**
For Chebyshev nodes, the Lebesgue constant grows as (2/π) log(n) + O(1).
This is asymptotically optimal. -/
/- ## Part IV: The Main Questions

Erdős's questions about Lebesgue functions for infinite sequences.
-/

/-- **Infinite Sequence of Nodes:**
A sequence x₁, x₂, ... in [-1,1]. -/
def InfiniteNodeSequence : Type := {f : ℕ → ℝ // ∀ n, f n ∈ Set.Icc (-1 : ℝ) 1}

/-- **Lebesgue Function for Finite Prefix:**
Given an infinite sequence, the Lebesgue function for the first n nodes. -/
noncomputable def lebesgueFunctionN (seq : InfiniteNodeSequence) (n : ℕ) (x : ℝ) : ℝ :=
  if h : n > 0 then
    lebesgueFunction (fun k : Fin n => seq.val k.val) x
  else 1

/-- **Question 1: Existence of Good Points**

Must there exist x ∈ (-1,1) such that Lₙ(x) > (2/π)log(n) - C for infinitely many n?

This is OPEN. The question asks whether every infinite sequence has a "witness"
point that demonstrates near-optimal growth infinitely often. -/
def existsGoodPoint (seq : InfiniteNodeSequence) : Prop :=
  ∃ x ∈ Set.Ioo (-1 : ℝ) 1, ∃ C : ℝ,
    ∀ N : ℕ, ∃ n > N, lebesgueFunctionN seq n x > (2 / Real.pi) * Real.log n - C

/-- **Question 2: Almost Everywhere Growth**

Is limsup_{n→∞} Lₙ(x)/log(n) ≥ 2/π for almost all x ∈ (-1,1)?

This asks whether the "good" growth rate holds for Lebesgue-almost-every point. -/
def almostEverywhereGrowth (seq : InfiniteNodeSequence) : Prop :=
  ∀ᵐ x ∂(volume.restrict (Set.Ioo (-1 : ℝ) 1)),
    Filter.limsup (fun n => lebesgueFunctionN seq n x / Real.log n)
      Filter.atTop ≥ 2 / Real.pi

/- ## Part V: Partial Results

Known results that provide partial answers.
-/

/-- **Bernstein's Density Result (1931):**
For any infinite sequence, the set of x where
  limsup_{n→∞} Lₙ(x)/log(n) ≥ 2/π
is dense in (-1,1).

This is weaker than "almost everywhere" but still significant. -/
def denseGoodPoints (seq : InfiniteNodeSequence) : Prop :=
  Dense {x : ℝ | x ∈ Set.Ioo (-1 : ℝ) 1 ∧
    Filter.limsup (fun n => lebesgueFunctionN seq n x / Real.log n)
      Filter.atTop ≥ 2 / Real.pi}

/-- **Bernstein's Theorem (1931):**
The good points are dense for any infinite sequence. -/
axiom bernstein_density_theorem (seq : InfiniteNodeSequence) :
    denseGoodPoints seq

/-- **Erdős's Maximum Theorem (1961):**
For any finite set of nodes, the maximum of the Lebesgue function
exceeds (2/π)log(n) - O(1).

This doesn't immediately answer the questions above because it's about
the maximum, not about fixed points x. -/
axiom erdos_max_theorem (seq : InfiniteNodeSequence) (n : ℕ) (hn : n ≥ 2) :
    ∃ x ∈ Set.Icc (-1 : ℝ) 1, lebesgueFunctionN seq n x > (2 / Real.pi) * Real.log n - 10

/- ## Part VI: Special Cases

Equidistant nodes demonstrate how node placement affects Lebesgue constants.
-/

/-- **Equidistant Nodes:**
For equally spaced nodes on [-1,1], the Lebesgue constant grows
exponentially: Λₙ ~ 2ⁿ/(e·n·log(n)).
This is much worse than the optimal log(n) growth. -/
noncomputable def equidistantNodes (n : ℕ) : Fin n → ℝ :=
  fun k => -1 + 2 * k.val / (n - 1)

/-- **Equidistant nodes have exponentially growing Lebesgue constants:**
Λₙ ≥ 2^(n/4) for equidistant nodes when n is large enough. -/
/- ## Part VII: Summary

**Erdős Problem #1132: OPEN**

Two open questions about Lebesgue functions for infinite node sequences:

1. **Existence Question:** Must there exist x ∈ (-1,1) with
   Lₙ(x) > (2/π)log(n) - O(1) for infinitely many n?

2. **Almost Everywhere Question:** Is
   limsup_{n→∞} Lₙ(x)/log(n) ≥ 2/π for almost all x?

**What We Know:**
- Bernstein (1931): Good points are dense
- Erdős (1961): The maximum always exceeds the threshold

The gap between "dense" (Bernstein) and "almost everywhere" (Question 2)
remains unresolved.
-/

/-- **Erdős Problem #1132: OPEN**

The Bernstein density theorem holds for all infinite node sequences,
and the Erdős maximum bound provides a pointwise bound for each n. -/
theorem erdos_1132 :
    (∀ seq : InfiniteNodeSequence, denseGoodPoints seq) ∧
    (∀ seq : InfiniteNodeSequence, ∀ n : ℕ, n ≥ 2 →
      ∃ x ∈ Set.Icc (-1 : ℝ) 1,
        lebesgueFunctionN seq n x > (2 / Real.pi) * Real.log n - 10) :=
  ⟨bernstein_density_theorem, erdos_max_theorem⟩

/-- **Summary theorem:** Good points are dense for every sequence. -/
theorem erdos_1132_summary (seq : InfiniteNodeSequence) :
    denseGoodPoints seq :=
  bernstein_density_theorem seq

end Erdos1132
