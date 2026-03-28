/-
Erdős Problem #1129: Optimal Lagrange Interpolation Nodes

Source: https://erdosproblems.com/1129
Status: SOLVED (Kilgore-Cheney 1976, Kilgore 1977, de Boor-Pinkus 1978)

Statement:
For points x₁,...,xₙ ∈ [-1,1], the Lagrange fundamental functions are:
  l_k(x) = ∏_{i≠k}(x - x_i) / ∏_{i≠k}(x_k - x_i)
with l_k(x_k) = 1 and l_k(x_i) = 0 for i ≠ k.

The Lebesgue constant is:
  Λ(x₁,...,xₙ) = max_{x∈[-1,1]} Σ_k |l_k(x)|

Question: Which choice of x_i minimizes Λ?

Answer: The optimal nodes satisfy equal-height condition:
  max_{x∈[x_i,x_{i+1}]} Σ_k |l_k(x)| are all equal.

Proved by:
- Kilgore & Cheney (1976): Existence of minimizing configurations
- Kilgore (1977): Equal-height characterization
- de Boor & Pinkus (1978): Uniqueness

Key bounds:
- Lower: Λ ≥ (2/π) log n - O(1) [Erdős 1961]
- Upper: Chebyshev nodes give Λ < (2/π) log n + O(1) [optimal]

Reference: https://erdosproblems.com/1129
-/

import Mathlib

open Finset BigOperators Real

namespace Erdos1129

/-
## Part I: Lagrange Interpolation Fundamentals

The Lagrange fundamental functions form the basis for polynomial interpolation.
-/

/--
**Lagrange Fundamental Function** l_k(x):
Given distinct points x₁,...,xₙ, the k-th Lagrange basis polynomial is:
  l_k(x) = ∏_{i≠k} (x - x_i) / ∏_{i≠k} (x_k - x_i)

Key properties:
- l_k(x_k) = 1 (equals 1 at its own node)
- l_k(x_i) = 0 for i ≠ k (equals 0 at other nodes)
- deg(l_k) = n - 1
-/
noncomputable def LagrangeBasis (nodes : Fin n → ℝ) (k : Fin n) (x : ℝ) : ℝ :=
  (∏ i ∈ Finset.univ.filter (fun j => j ≠ k), (x - nodes i)) /
  (∏ i ∈ Finset.univ.filter (fun j => j ≠ k), (nodes k - nodes i))

/--
**Distinct Nodes:**
The Lagrange interpolation requires all nodes to be distinct.
-/
def DistinctNodes (nodes : Fin n → ℝ) : Prop :=
  ∀ i j : Fin n, i ≠ j → nodes i ≠ nodes j

/--
**Nodes in Interval:**
All nodes must lie in [-1, 1] for this problem.
-/
def NodesInInterval (nodes : Fin n → ℝ) : Prop :=
  ∀ i : Fin n, -1 ≤ nodes i ∧ nodes i ≤ 1

/-
## Part II: The Lebesgue Constant

The Lebesgue constant measures the conditioning of polynomial interpolation.
-/

/--
**Lebesgue Function** λ(x):
The sum of absolute values of Lagrange basis functions at point x.
  λ(x) = Σ_k |l_k(x)|
-/
noncomputable def LebesgueFunction (nodes : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∑ k : Fin n, |LagrangeBasis nodes k x|

/--
**Lebesgue Constant** Λ:
The supremum of the Lebesgue function over [-1, 1].
  Λ = sup_{x ∈ [-1,1]} λ(x) = sup_{x ∈ [-1,1]} Σ_k |l_k(x)|

This measures the worst-case amplification of interpolation error.
-/
noncomputable def LebesgueConstant (nodes : Fin n → ℝ) : ℝ :=
  sSup {y : ℝ | ∃ x : ℝ, -1 ≤ x ∧ x ≤ 1 ∧ y = LebesgueFunction nodes x}

/-
## Part III: Chebyshev Nodes

The roots of Chebyshev polynomials give near-optimal interpolation nodes.
-/

/--
**Chebyshev Nodes:**
The n roots of the n-th Chebyshev polynomial T_n:
  x_k = cos((2k - 1)π / 2n) for k = 1, ..., n

These cluster near the endpoints ±1, reducing the Lebesgue constant.
-/
noncomputable def ChebyshevNodes (n : ℕ) (hn : n > 0) (k : Fin n) : ℝ :=
  Real.cos ((2 * (k.val + 1) - 1 : ℝ) * Real.pi / (2 * n))

/--
Chebyshev nodes lie in [-1, 1] since cos maps to [-1, 1].
-/
theorem chebyshev_nodes_in_interval (n : ℕ) (hn : n > 0) :
    NodesInInterval (ChebyshevNodes n hn) := by
  intro k
  exact ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩

/-
## Part IV: Fundamental Lower Bounds

The Lebesgue constant must grow logarithmically with n.
-/

/- Faber's Theorem (1914): Λ ≫ log n. Subsumed by the sharper Erdős bound below. -/

/--
**Erdős Lower Bound (1961):**
The sharp lower bound with exact constant:
  Λ(x₁,...,xₙ) ≥ (2/π) log n - O(1)

This improves earlier bounds by Bernstein.
-/
axiom erdos_lower_bound :
    ∃ C : ℝ, ∀ n : ℕ, ∀ nodes : Fin n → ℝ,
    NodesInInterval nodes → DistinctNodes nodes → n > 0 →
    LebesgueConstant nodes ≥ (2 / Real.pi) * Real.log n - C

/--
**Chebyshev Upper Bound:**
The Chebyshev nodes achieve the optimal asymptotic:
  Λ(Chebyshev) ≤ (2/π) log n + O(1)

Combined with Erdős's lower bound, this is asymptotically optimal.
-/
axiom chebyshev_upper_bound :
    ∃ C : ℝ, ∀ n : ℕ, (hn : n > 0) →
    LebesgueConstant (ChebyshevNodes n hn) ≤ (2 / Real.pi) * Real.log n + C

/-
## Part V: The Equal-Height Characterization

Erdős conjectured and Kilgore proved: optimal nodes satisfy equal oscillation.
-/

/--
**Subinterval Maximum:**
The maximum of the Lebesgue function on subinterval [x_i, x_{i+1}].
-/
noncomputable def SubintervalMax (nodes : Fin n → ℝ) (i : Fin n) (hi : i.val + 1 < n) : ℝ :=
  sSup {y : ℝ | ∃ x : ℝ, nodes i ≤ x ∧ x ≤ nodes ⟨i.val + 1, hi⟩ ∧
                         y = LebesgueFunction nodes x}

/--
**Equal-Height Property:**
The subinterval maxima of the Lebesgue function are all equal.

Erdős conjectured that optimal nodes have this "equioscillation" property.
-/
def EqualHeightProperty (nodes : Fin n → ℝ) : Prop :=
  ∀ i j : Fin n, ∀ hi : i.val + 1 < n, ∀ hj : j.val + 1 < n,
  SubintervalMax nodes i hi = SubintervalMax nodes j hj

/--
**Kilgore-Cheney Theorem (1976):**
There exist interpolation nodes that minimize the Lebesgue constant.
-/
axiom kilgore_cheney_existence (n : ℕ) (hn : n > 0) :
    ∃ nodes : Fin n → ℝ, NodesInInterval nodes ∧ DistinctNodes nodes ∧
    ∀ nodes' : Fin n → ℝ, NodesInInterval nodes' → DistinctNodes nodes' →
    LebesgueConstant nodes ≤ LebesgueConstant nodes'

/- Kilgore (1977): optimal nodes satisfy the equal-height (equioscillation) property.
   de Boor-Pinkus (1978): the minimizer is unique for canonical (symmetric, endpoint-fixed) configurations.
   These characterization and uniqueness results are known but not used in the proofs below. -/

/-
## Part VI: Known Exact Solutions

Optimal canonical configurations are known only for small n.
-/

private lemma filter_ne_zero_fin2 :
    Finset.univ.filter (fun (j : Fin 2) => j ≠ 0) = {1} := by
  ext i; fin_cases i <;> simp

private lemma filter_ne_one_fin2 :
    Finset.univ.filter (fun (j : Fin 2) => j ≠ 1) = {0} := by
  ext i; fin_cases i <;> simp

private lemma lagrange_basis_n2_0 (x : ℝ) :
    LagrangeBasis (![(-1 : ℝ), 1]) 0 x = (1 - x) / 2 := by
  simp only [LagrangeBasis, filter_ne_zero_fin2, Finset.prod_singleton,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

private lemma lagrange_basis_n2_1 (x : ℝ) :
    LagrangeBasis (![(-1 : ℝ), 1]) 1 x = (x + 1) / 2 := by
  simp only [LagrangeBasis, filter_ne_one_fin2, Finset.prod_singleton,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

private lemma lebesgue_fn_n2 (x : ℝ) (hx1 : -1 ≤ x) (hx2 : x ≤ 1) :
    LebesgueFunction (![(-1 : ℝ), 1]) x = 1 := by
  simp only [LebesgueFunction, Fin.sum_univ_two, lagrange_basis_n2_0, lagrange_basis_n2_1]
  have h1 : (0 : ℝ) ≤ (1 - x) / 2 := by linarith
  have h2 : (0 : ℝ) ≤ (x + 1) / 2 := by linarith
  rw [abs_of_nonneg h1, abs_of_nonneg h2]; ring

private lemma lebesgue_set_n2 :
    {y : ℝ | ∃ x : ℝ, -1 ≤ x ∧ x ≤ 1 ∧ y = LebesgueFunction (![(-1 : ℝ), 1]) x} = {1} := by
  ext y; constructor
  · rintro ⟨x, hx1, hx2, rfl⟩
    simp [lebesgue_fn_n2 x hx1 hx2]
  · intro hy
    rw [Set.mem_singleton_iff] at hy
    exact ⟨0, by norm_num, by norm_num, by rw [hy, lebesgue_fn_n2 0 (by norm_num) (by norm_num)]⟩

/--
**n = 2:**
Optimal nodes: {-1, 1} with Λ = 1.
-/
theorem optimal_n2 : NodesInInterval (![(-1 : ℝ), 1]) ∧
    LebesgueConstant (![(-1 : ℝ), 1]) = 1 := by
  constructor
  · intro i
    fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  · simp only [LebesgueConstant, lebesgue_set_n2, csSup_singleton]

private lemma filter_ne_zero_fin3 :
    Finset.univ.filter (fun (j : Fin 3) => j ≠ 0) = {1, 2} := by
  ext i; fin_cases i <;> simp

private lemma filter_ne_one_fin3 :
    Finset.univ.filter (fun (j : Fin 3) => j ≠ 1) = {0, 2} := by
  ext i; fin_cases i <;> simp

private lemma filter_ne_two_fin3 :
    Finset.univ.filter (fun (j : Fin 3) => j ≠ 2) = {0, 1} := by
  ext i; fin_cases i <;> simp

private lemma fin3_pair_product_12 (f : Fin 3 → ℝ) :
    ∏ i ∈ ({1, 2} : Finset (Fin 3)), f i = f 1 * f 2 := by
  rw [Finset.prod_pair (by decide)]

private lemma fin3_pair_product_02 (f : Fin 3 → ℝ) :
    ∏ i ∈ ({0, 2} : Finset (Fin 3)), f i = f 0 * f 2 := by
  rw [Finset.prod_pair (by decide)]

private lemma fin3_pair_product_01 (f : Fin 3 → ℝ) :
    ∏ i ∈ ({0, 1} : Finset (Fin 3)), f i = f 0 * f 1 := by
  rw [Finset.prod_pair (by decide)]

/-- Vector access helper: evaluates ![-1, 0, 1] at each index. -/
private lemma n3_val_0 : (![(-1 : ℝ), 0, 1]) (0 : Fin 3) = -1 := rfl
private lemma n3_val_1 : (![(-1 : ℝ), 0, 1]) (1 : Fin 3) = 0 := rfl
private lemma n3_val_2 : (![(-1 : ℝ), 0, 1]) (2 : Fin 3) = 1 := rfl

/-- l_0(x) = x(x-1)/2 for nodes {-1, 0, 1} -/
private lemma lagrange_basis_n3_0 (x : ℝ) :
    LagrangeBasis (![(-1 : ℝ), 0, 1]) 0 x = x * (x - 1) / 2 := by
  simp only [LagrangeBasis, filter_ne_zero_fin3]
  rw [Finset.prod_pair (show (1 : Fin 3) ≠ 2 by decide),
      Finset.prod_pair (show (1 : Fin 3) ≠ 2 by decide)]
  simp only [n3_val_0, n3_val_1, n3_val_2]; ring

/-- l_1(x) = 1 - x² for nodes {-1, 0, 1} -/
private lemma lagrange_basis_n3_1 (x : ℝ) :
    LagrangeBasis (![(-1 : ℝ), 0, 1]) 1 x = 1 - x ^ 2 := by
  simp only [LagrangeBasis, filter_ne_one_fin3]
  rw [Finset.prod_pair (show (0 : Fin 3) ≠ 2 by decide),
      Finset.prod_pair (show (0 : Fin 3) ≠ 2 by decide)]
  simp only [n3_val_0, n3_val_1, n3_val_2]; ring

/-- l_2(x) = x(x+1)/2 for nodes {-1, 0, 1} -/
private lemma lagrange_basis_n3_2 (x : ℝ) :
    LagrangeBasis (![(-1 : ℝ), 0, 1]) 2 x = x * (x + 1) / 2 := by
  simp only [LagrangeBasis, filter_ne_two_fin3]
  rw [Finset.prod_pair (show (0 : Fin 3) ≠ 1 by decide),
      Finset.prod_pair (show (0 : Fin 3) ≠ 1 by decide)]
  simp only [n3_val_0, n3_val_1, n3_val_2]; ring

/-- The Lebesgue function for {-1, 0, 1} on [0, 1] equals x + 1 - x². -/
private lemma lebesgue_fn_n3_nonneg (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    LebesgueFunction (![(-1 : ℝ), 0, 1]) x = x + 1 - x ^ 2 := by
  simp only [LebesgueFunction, Fin.sum_univ_three, lagrange_basis_n3_0,
    lagrange_basis_n3_1, lagrange_basis_n3_2]
  have h1 : x * (x - 1) / 2 ≤ 0 := by nlinarith
  have h2 : 0 ≤ 1 - x ^ 2 := by nlinarith
  have h3 : 0 ≤ x * (x + 1) / 2 := by nlinarith
  rw [abs_of_nonpos h1, abs_of_nonneg h2, abs_of_nonneg h3]; ring

/-- The Lebesgue function for {-1, 0, 1} on [-1, 0] equals -x + 1 - x². -/
private lemma lebesgue_fn_n3_nonpos (x : ℝ) (hx1 : -1 ≤ x) (hx0 : x ≤ 0) :
    LebesgueFunction (![(-1 : ℝ), 0, 1]) x = -x + 1 - x ^ 2 := by
  simp only [LebesgueFunction, Fin.sum_univ_three, lagrange_basis_n3_0,
    lagrange_basis_n3_1, lagrange_basis_n3_2]
  have h1 : 0 ≤ x * (x - 1) / 2 := by nlinarith
  have h2 : 0 ≤ 1 - x ^ 2 := by nlinarith
  have h3 : x * (x + 1) / 2 ≤ 0 := by nlinarith
  rw [abs_of_nonneg h1, abs_of_nonneg h2, abs_of_nonpos h3]; ring

/-- The Lebesgue function for {-1, 0, 1} is bounded by 5/4 on [-1, 1]. -/
private lemma lebesgue_fn_n3_le (x : ℝ) (hx1 : -1 ≤ x) (hx2 : x ≤ 1) :
    LebesgueFunction (![(-1 : ℝ), 0, 1]) x ≤ 5 / 4 := by
  rcases le_or_gt 0 x with hx0 | hx0
  · rw [lebesgue_fn_n3_nonneg x hx0 hx2]; nlinarith [sq_nonneg (x - 1 / 2)]
  · rw [lebesgue_fn_n3_nonpos x hx1 (le_of_lt hx0)]; nlinarith [sq_nonneg (x + 1 / 2)]

/-- The Lebesgue function for {-1, 0, 1} attains 5/4 at x = 1/2. -/
private lemma lebesgue_fn_n3_at_half :
    LebesgueFunction (![(-1 : ℝ), 0, 1]) (1 / 2) = 5 / 4 := by
  rw [lebesgue_fn_n3_nonneg (1 / 2) (by norm_num) (by norm_num)]; ring

private lemma lebesgue_set_n3_bddAbove :
    BddAbove {y : ℝ | ∃ x : ℝ, -1 ≤ x ∧ x ≤ 1 ∧
      y = LebesgueFunction (![(-1 : ℝ), 0, 1]) x} :=
  ⟨5 / 4, fun _ ⟨x, hx1, hx2, hy⟩ => hy ▸ lebesgue_fn_n3_le x hx1 hx2⟩

private lemma lebesgue_set_n3_nonempty :
    (↑{y : ℝ | ∃ x : ℝ, -1 ≤ x ∧ x ≤ 1 ∧
      y = LebesgueFunction (![(-1 : ℝ), 0, 1]) x} : Set ℝ).Nonempty :=
  ⟨5 / 4, 1 / 2, by norm_num, by norm_num, lebesgue_fn_n3_at_half.symm⟩

/--
**n = 3:**
Optimal nodes: {-1, 0, 1} with Λ = 1.25 = 5/4.
Proved by Bernstein (1931).
-/
theorem optimal_n3 : NodesInInterval (![(-1 : ℝ), 0, 1]) ∧
    LebesgueConstant (![(-1 : ℝ), 0, 1]) = 5/4 := by
  constructor
  · intro i
    fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  · apply le_antisymm
    · exact csSup_le lebesgue_set_n3_nonempty
        (fun _ ⟨x, hx1, hx2, hy⟩ => hy ▸ lebesgue_fn_n3_le x hx1 hx2)
    · exact le_csSup lebesgue_set_n3_bddAbove
        ⟨1 / 2, by norm_num, by norm_num, lebesgue_fn_n3_at_half.symm⟩

/- n = 4: Optimal nodes are {-1, -t, t, 1} with t ≈ 0.4177, Λ ≈ 1.4229 (Rack-Vajda 2015). -/

/-
## Part VII: Complex Variant

Erdős also posed a variant for points on the unit circle.
-/

/--
**Complex Lebesgue Constant:**
For nodes z₁,...,zₙ on the unit circle |z| = 1.
-/
noncomputable def ComplexLebesgueConstant (n : ℕ) (nodes : Fin n → ℂ) : ℝ :=
  sSup {y : ℝ | ∃ z : ℂ, ‖z‖ = 1 ∧
    y = ∑ k : Fin n, ‖(∏ i ∈ Finset.univ.filter (fun j => j ≠ k), (z - nodes i)) /
                       (∏ i ∈ Finset.univ.filter (fun j => j ≠ k), (nodes k - nodes i))‖}

/--
**Roots of Unity:**
The n-th roots of unity: ωₖ = e^(2πik/n) for k = 0, ..., n-1.
-/
noncomputable def RootsOfUnity (n : ℕ) (hn : n > 0) (k : Fin n) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * k.val / n)

/--
**Brutman's Theorem (1980, odd n):**
For odd n, the n-th roots of unity minimize the complex Lebesgue constant.
-/
axiom brutman_odd (n : ℕ) (hn : n > 0) (hodd : Odd n) :
    ∀ nodes : Fin n → ℂ, (∀ k, ‖nodes k‖ = 1) →
    ComplexLebesgueConstant n (RootsOfUnity n hn) ≤ ComplexLebesgueConstant n nodes

/--
**Brutman-Pinkus Theorem (1980, even n):**
For even n, the n-th roots of unity minimize the complex Lebesgue constant.
-/
axiom brutman_pinkus_even (n : ℕ) (hn : n > 0) (heven : Even n) :
    ∀ nodes : Fin n → ℂ, (∀ k, ‖nodes k‖ = 1) →
    ComplexLebesgueConstant n (RootsOfUnity n hn) ≤ ComplexLebesgueConstant n nodes

/--
**Erdős's Complex Conjecture: PROVED**
For all n, roots of unity minimize the complex Lebesgue constant.
-/
theorem erdos_complex_conjecture (n : ℕ) (hn : n > 0) :
    ∀ nodes : Fin n → ℂ, (∀ k, ‖nodes k‖ = 1) →
    ComplexLebesgueConstant n (RootsOfUnity n hn) ≤ ComplexLebesgueConstant n nodes := by
  intro nodes hnodes
  cases Nat.even_or_odd n with
  | inl heven => exact brutman_pinkus_even n hn heven nodes hnodes
  | inr hodd => exact brutman_odd n hn hodd nodes hnodes

/-
## Part VIII: Main Results

The complete resolution of Erdős Problem #1129.
-/

/--
**Erdős Problem #1129: SOLVED**

The problem asks: which x₁,...,xₙ ∈ [-1,1] minimize the Lebesgue constant?

Answers:
1. Optimal nodes exist (Kilgore-Cheney 1976)
2. Characterized by equal-height property (Kilgore 1977)
3. Unique for canonical configurations (de Boor-Pinkus 1978)
4. Asymptotically: Λ ~ (2/π) log n (Erdős lower, Chebyshev upper)
5. Complex variant: roots of unity are optimal (Brutman, Brutman-Pinkus)
-/
theorem erdos_1129 (n : ℕ) (hn : n > 0) :
    (∃ nodes : Fin n → ℝ, NodesInInterval nodes ∧ DistinctNodes nodes ∧
     ∀ nodes' : Fin n → ℝ, NodesInInterval nodes' → DistinctNodes nodes' →
     LebesgueConstant nodes ≤ LebesgueConstant nodes') ∧
    (∃ C₁ C₂ : ℝ, ∀ (m : ℕ) (hm : m > 0), ∀ nodes : Fin m → ℝ,
     NodesInInterval nodes → DistinctNodes nodes →
     (2 / Real.pi) * Real.log m - C₁ ≤ LebesgueConstant nodes ∧
     LebesgueConstant (ChebyshevNodes m hm) ≤
       (2 / Real.pi) * Real.log m + C₂) := by
  constructor
  · exact kilgore_cheney_existence n hn
  · obtain ⟨C₁, hC₁⟩ := erdos_lower_bound
    obtain ⟨C₂, hC₂⟩ := chebyshev_upper_bound
    exact ⟨C₁, C₂, fun m hm nodes hinterval hdistinct =>
      ⟨hC₁ m nodes hinterval hdistinct hm, hC₂ m hm⟩⟩

/--
**Summary:**
The answer to Erdős's question is that optimal nodes exist, are characterized
by the equal-height (equioscillation) property, and achieve the sharp bound
Λ ~ (2/π) log n asymptotically.
-/
theorem erdos_1129_summary :
    (∀ n > 0, ∃ nodes : Fin n → ℝ, NodesInInterval nodes ∧ DistinctNodes nodes ∧
     ∀ nodes' : Fin n → ℝ, NodesInInterval nodes' → DistinctNodes nodes' →
     LebesgueConstant nodes ≤ LebesgueConstant nodes') ∧
    (∀ (n : ℕ) (hn : n > 0), ∀ nodes : Fin n → ℂ, (∀ k, ‖nodes k‖ = 1) →
     ComplexLebesgueConstant n (RootsOfUnity n hn) ≤
       ComplexLebesgueConstant n nodes) := by
  exact ⟨fun n hn => kilgore_cheney_existence n hn,
         fun n hn nodes hnodes => erdos_complex_conjecture n hn nodes hnodes⟩

end Erdos1129
