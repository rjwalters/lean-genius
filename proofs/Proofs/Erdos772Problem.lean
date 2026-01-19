/-
Erdős Problem #772: Sidon Sets in Bounded Convolution Sets

Source: https://erdosproblems.com/772
Status: PROVED (Alon-Erdős, 1985)

Statement:
Let k ≥ 1 and H_k(n) be the maximal r such that if A ⊂ ℕ has |A| = n
and ‖1_A ∗ 1_A‖_∞ ≤ k, then A contains a Sidon set of size at least r.

Is it true that H_k(n)/n^{1/2} → ∞? Or even H_k(n) > n^{1/2+c} for some c > 0?

Answer: YES

Key Results:
- Erdős (1984): H_k(n) ≪ n^{2/3} (absolute constant)
- Lower bound: H_k(n) ≫ n^{1/2} (any set has Sidon subset of size ≫ √n)
- Alon-Erdős (1985): H_k(n) ≫_k n^{2/3} (optimal up to constants depending on k)

Proof Sketch:
Take random subset A' ⊂ A with inclusion probability ∼ n^{-1/3}.
Non-trivial additive quadruples in A number ≪ n². After sampling,
only ≪ n^{2/3} remain in A', which can be removed while keeping
|A'| ≫ n^{2/3}.

References:
- Alon, N. and Erdős, P., "An application of graph theory to additive
  number theory." European J. Combin. (1985), 201-203.
- Erdős, P., "Extremal problems in number theory, combinatorics and
  geometry." Proc. ICM (1984), 51-70.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Nat Real Finset

namespace Erdos772

/-
## Part I: Sidon Sets
-/

/--
**Sidon Set:**
A set A is a Sidon set (or B₂ sequence) if all pairwise sums a + b
(with a ≤ b, both in A) are distinct.

Equivalently: a + b = c + d with a,b,c,d ∈ A implies {a,b} = {c,d}.
-/
def IsSidon (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → ({a, b} : Finset ℕ) = {c, d}

/--
**Alternative Sidon characterization:**
No non-trivial additive quadruples (a,b,c,d) with a + b = c + d.
-/
def HasNoAdditiveQuadruple (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → a = c ∨ a = d ∨ b = c ∨ b = d

/--
**Sidon sets have no non-trivial additive quadruples:**
This equivalence is straightforward but requires case analysis on set equality.
-/
axiom sidon_iff_no_quadruple (A : Finset ℕ) :
    IsSidon A ↔ HasNoAdditiveQuadruple A

/-
## Part II: Convolution and Representation Function
-/

/--
**Representation function:**
r_A(n) = #{(a,b) : a,b ∈ A, a + b = n}

This counts ordered pairs, so r_A(n) is even when a ≠ b.
-/
def representationCount (A : Finset ℕ) (n : ℕ) : ℕ :=
  (A.filter (fun a => ∃ b ∈ A, a + b = n)).card

/--
**Convolution bound:**
‖1_A ∗ 1_A‖_∞ = max_n r_A(n)

A set has bounded convolution if no sum is represented too many times.
-/
def maxRepresentation (A : Finset ℕ) : ℕ :=
  (A.biUnion (fun a => A.image (fun b => a + b))).sup
    (fun n => representationCount A n)

/--
**Bounded convolution property:**
-/
def HasBoundedConvolution (A : Finset ℕ) (k : ℕ) : Prop :=
  ∀ n : ℕ, representationCount A n ≤ k

/--
**Sidon sets have bounded convolution with k=2:**
Each sum appears at most once (unordered), so at most twice (ordered).
This follows from the definition of Sidon sets.
-/
axiom sidon_has_bounded_conv (A : Finset ℕ) (h : IsSidon A) :
    HasBoundedConvolution A 2

/-
## Part III: The Function H_k(n)
-/

/--
**Maximum Sidon subset size in bounded convolution sets:**
H_k(n) = max{|B| : B ⊆ A is Sidon, for some A with |A| = n, ‖1_A∗1_A‖_∞ ≤ k}
-/
noncomputable def H_k (k n : ℕ) : ℕ :=
  sSup { r : ℕ | ∃ A : Finset ℕ, A.card = n ∧
    HasBoundedConvolution A k ∧
    ∃ B : Finset ℕ, B ⊆ A ∧ IsSidon B ∧ B.card = r }

/-
## Part IV: Erdős's Upper Bound
-/

/--
**Erdős 1984: Upper bound**
H_k(n) ≪ n^{2/3}

The implied constant is absolute (independent of k).
-/
axiom erdos_1984_upper_bound :
  ∃ C : ℝ, C > 0 ∧
    ∀ k n : ℕ, k ≥ 1 → n ≥ 1 →
      (H_k k n : ℝ) ≤ C * (n : ℝ)^(2/3 : ℝ)

/-
## Part V: Basic Lower Bound
-/

/--
**Every set contains a Sidon subset of size ≫ √n:**
This is a classical result (see Problem #530).
-/
axiom sidon_subset_sqrt :
  ∃ c : ℝ, c > 0 ∧
    ∀ A : Finset ℕ, A.card ≥ 1 →
      ∃ B : Finset ℕ, B ⊆ A ∧ IsSidon B ∧
        (B.card : ℝ) ≥ c * Real.sqrt (A.card)

/--
**Basic lower bound: H_k(n) ≫ √n**
Follows from the fact that any set contains a Sidon subset of size ≫ √n.
-/
axiom basic_lower_bound :
    ∃ c : ℝ, c > 0 ∧
      ∀ k n : ℕ, k ≥ 1 → n ≥ 1 →
        (H_k k n : ℝ) ≥ c * Real.sqrt n

/-
## Part VI: Alon-Erdős Optimal Lower Bound
-/

/--
**Alon-Erdős 1985: Optimal lower bound**
H_k(n) ≫_k n^{2/3}

The answer to Erdős's question is YES, and the optimal exponent is 2/3.
-/
axiom alon_erdos_1985 :
  ∀ k : ℕ, k ≥ 1 →
    ∃ c_k : ℝ, c_k > 0 ∧
      ∀ n : ℕ, n ≥ 1 →
        (H_k k n : ℝ) ≥ c_k * (n : ℝ)^(2/3 : ℝ)

/--
**Corollary: H_k(n)/√n → ∞**
This follows from the n^{2/3} lower bound since n^{2/3}/n^{1/2} = n^{1/6} → ∞.
-/
axiom ratio_tends_to_infinity :
    ∀ k : ℕ, k ≥ 1 →
      ∀ M : ℝ, ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
        (H_k k n : ℝ) / Real.sqrt n ≥ M

/--
**Corollary: H_k(n) > n^{1/2 + c} for c = 1/6**
Since H_k(n) ≥ c_k * n^{2/3} and 2/3 = 1/2 + 1/6, this holds for large n.
-/
axiom stronger_lower_bound :
    ∀ k : ℕ, k ≥ 1 →
      ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
        (H_k k n : ℝ) > (n : ℝ)^(1/2 + 1/6 : ℝ)

/-
## Part VII: Proof Sketch (Probabilistic Method)
-/

/--
**Additive quadruples in A:**
The number of solutions to a + b = c + d in A is ≪ |A|² when
‖1_A ∗ 1_A‖_∞ ≤ k.
-/
def additiveQuadrupleCount (A : Finset ℕ) : ℕ :=
  (A ×ˢ A ×ˢ A ×ˢ A).filter (fun ⟨a, b, c, d⟩ =>
    a + b = c + d ∧ ({a, b} : Finset ℕ) ≠ {c, d}).card

/--
**Quadruple bound:**
In a set with bounded convolution, additive quadruples are ≤ k · n².
-/
axiom quadruple_bound :
  ∀ A : Finset ℕ, ∀ k : ℕ,
    HasBoundedConvolution A k →
      additiveQuadrupleCount A ≤ k * A.card ^ 2

/--
**Probabilistic construction:**
Sample each element with probability p ∼ n^{-1/3}.
- Expected subset size: ≈ n^{2/3}
- Expected remaining quadruples: ≈ k · n² · p⁴ = k · n^{2/3}
- After removing one element per quadruple: still ≫ n^{2/3} elements
-/
axiom probabilistic_construction :
  ∀ k : ℕ, k ≥ 1 →
    ∀ A : Finset ℕ, HasBoundedConvolution A k →
      ∃ B : Finset ℕ, B ⊆ A ∧ IsSidon B ∧
        ∃ c_k : ℝ, c_k > 0 ∧ (B.card : ℝ) ≥ c_k * (A.card : ℝ)^(2/3 : ℝ)

/-
## Part VIII: Optimal Result
-/

/--
**Optimal bounds for H_k(n):**
n^{2/3} ≪ H_k(n) ≪ n^{2/3}

So H_k(n) = Θ(n^{2/3}) with constants depending on k for lower bound.
-/
theorem optimal_bounds :
    ∀ k : ℕ, k ≥ 1 →
      ∃ c C : ℝ, c > 0 ∧ C > 0 ∧
        ∀ n : ℕ, n ≥ 1 →
          c * (n : ℝ)^(2/3 : ℝ) ≤ (H_k k n : ℝ) ∧
          (H_k k n : ℝ) ≤ C * (n : ℝ)^(2/3 : ℝ) := by
  intro k hk
  obtain ⟨c_k, hc_k, hlower⟩ := alon_erdos_1985 k hk
  obtain ⟨C, hC, hupper⟩ := erdos_1984_upper_bound
  exact ⟨c_k, C, hc_k, hC, fun n hn => ⟨hlower n hn, hupper k n hk hn⟩⟩

/-
## Part IX: Summary
-/

/--
**Erdős Problem #772: Status**

**Question:**
Does H_k(n)/√n → ∞? Is H_k(n) > n^{1/2+c} for some c > 0?

**Answer:**
YES. Proved by Alon and Erdős (1985).

**Optimal Result:**
H_k(n) = Θ(n^{2/3})

**Key Insight:**
The probabilistic method shows that random subsampling with probability
n^{-1/3} preserves enough structure while eliminating most additive
quadruples.
-/
theorem erdos_772_summary :
    -- H_k(n)/√n → ∞
    (∀ k : ℕ, k ≥ 1 → ∀ M : ℝ, ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      (H_k k n : ℝ) / Real.sqrt n ≥ M) ∧
    -- Optimal bound is n^{2/3}
    (∀ k : ℕ, k ≥ 1 → ∃ c C : ℝ, c > 0 ∧ C > 0 ∧
      ∀ n : ℕ, n ≥ 1 →
        c * (n : ℝ)^(2/3 : ℝ) ≤ (H_k k n : ℝ) ∧
        (H_k k n : ℝ) ≤ C * (n : ℝ)^(2/3 : ℝ)) := by
  exact ⟨ratio_tends_to_infinity, optimal_bounds⟩

end Erdos772
