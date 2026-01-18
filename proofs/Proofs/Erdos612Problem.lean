/-
  Erdős Problem #612: Diameter Bounds for Clique-Free Graphs

  Source: https://erdosproblems.com/612
  Status: OPEN (original conjecture DISPROVED for r ≥ 2)

  Statement:
  Let G be a connected graph with n vertices, minimum degree d, diameter D.

  Original Conjectures (Erdős-Pach-Pollack-Tuza 1989):
  1. If G is K_{2r}-free and (r-1)(3r+2) | d:
     D ≤ (2(r-1)(3r+2))/(2r²-1) · n/d + O(1)
  2. If G is K_{2r+1}-free and (3r-1) | d:
     D ≤ (3r-1)/r · n/d + O(1)

  Counterexamples:
  - Czabarka-Singgih-Székely (2021): Disproved for r ≥ 2
  - Constructed graphs with D = (6r-5)n/((2r-1)d + 2r-3) + O(1)

  Amended Conjecture:
  For K_{k+1}-free graphs: D ≤ (3 - 2/k) · n/d + O(1)

  The base case r=1 (triangle-free) remains valid.
-/

import Mathlib

open Finset Function SimpleGraph

namespace Erdos612

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Graph Properties -/

/-- The diameter of a connected graph -/
noncomputable def diameter (G : SimpleGraph V) : ℕ :=
  sorry -- Maximum distance between any two vertices

/-- The minimum degree of a graph -/
noncomputable def minDegree (G : SimpleGraph V) : ℕ :=
  Finset.univ.image (fun v => G.degree v) |>.min' (by simp)

/-- A graph is K_r-free if it contains no complete subgraph on r vertices -/
def IsKFree (G : SimpleGraph V) (r : ℕ) : Prop :=
  ∀ S : Finset V, S.card = r → ¬(∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.Adj u v)

/-- Triangle-free is K_3-free -/
def IsTriangleFree (G : SimpleGraph V) : Prop := IsKFree G 3

/-! ## The Basic Bound -/

/-- The fundamental Erdős-Pach-Pollack-Tuza bound:
    Any connected graph has D ≤ 3n/(d+1) + O(1) -/
axiom basic_diameter_bound :
  ∃ C : ℝ, ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    G.Connected →
    let n := Fintype.card V
    let d := minDegree G
    (diameter G : ℝ) ≤ 3 * n / (d + 1) + C

/-! ## Original Conjecture 1: K_{2r}-free -/

/-- The coefficient in the original conjecture for K_{2r}-free graphs -/
def alpha_2r (r : ℕ) : ℝ :=
  (2 * (r - 1) * (3 * r + 2)) / (2 * r^2 - 1)

/-- Divisibility condition for Conjecture 1 -/
def divides_d_2r (r d : ℕ) : Prop :=
  (r - 1) * (3 * r + 2) ∣ d

/-- Original Conjecture 1 (DISPROVED for r ≥ 2) -/
def OriginalConjecture1 (r : ℕ) : Prop :=
  r ≥ 1 →
  ∃ C : ℝ, ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    G.Connected →
    IsKFree G (2 * r) →
    divides_d_2r r (minDegree G) →
    let n := Fintype.card V
    let d := minDegree G
    (diameter G : ℝ) ≤ alpha_2r r * n / d + C

/-! ## Original Conjecture 2: K_{2r+1}-free -/

/-- The coefficient for K_{2r+1}-free graphs -/
def alpha_2r1 (r : ℕ) : ℝ :=
  (3 * r - 1) / r

/-- Divisibility condition for Conjecture 2 -/
def divides_d_2r1 (r d : ℕ) : Prop :=
  (3 * r - 1) ∣ d

/-- Original Conjecture 2 (DISPROVED for r ≥ 2) -/
def OriginalConjecture2 (r : ℕ) : Prop :=
  r ≥ 1 →
  ∃ C : ℝ, ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    G.Connected →
    IsKFree G (2 * r + 1) →
    divides_d_2r1 r (minDegree G) →
    let n := Fintype.card V
    let d := minDegree G
    (diameter G : ℝ) ≤ alpha_2r1 r * n / d + C

/-! ## Counterexamples (Czabarka-Singgih-Székely 2021) -/

/-- The counterexample diameter bound -/
def counterexample_diameter (r n d : ℕ) : ℝ :=
  (6 * r - 5) * n / ((2 * r - 1) * d + 2 * r - 3)

/-- Counterexamples exist for r ≥ 2 -/
axiom counterexample_exists :
  ∀ r : ℕ, r ≥ 2 →
    ∀ᶠ n in Filter.atTop,
      ∃ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
        Fintype.card V = n ∧
        G.Connected ∧
        IsKFree G (2 * r) ∧
        (diameter G : ℝ) > alpha_2r r * n / (minDegree G) - 10

/-- The original conjecture is FALSE for r ≥ 2 -/
theorem original_conjecture1_false (r : ℕ) (hr : r ≥ 2) :
    ¬OriginalConjecture1 r := by
  sorry

/-! ## The Base Case: Triangle-Free (r = 1) -/

/-- For triangle-free graphs (r=1, so K_3-free):
    D ≤ 5n/(2d) + O(1) -/
axiom triangle_free_diameter :
  ∃ C : ℝ, ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    G.Connected →
    IsTriangleFree G →
    let n := Fintype.card V
    let d := minDegree G
    (diameter G : ℝ) ≤ 5 * n / (2 * d) + C

/-- The base case r = 1 of Conjecture 1 is TRUE -/
theorem conjecture1_base_case : OriginalConjecture1 1 := by
  sorry

/-! ## The Amended Conjecture -/

/-- The amended coefficient: (3 - 2/k) for K_{k+1}-free -/
def amended_alpha (k : ℕ) : ℝ :=
  3 - 2 / k

/-- Amended Conjecture (Czabarka-Singgih-Székely):
    For K_{k+1}-free graphs: D ≤ (3 - 2/k) · n/d + O(1) -/
def AmendedConjecture (k : ℕ) : Prop :=
  k ≥ 2 →
  ∃ C : ℝ, ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    G.Connected →
    IsKFree G (k + 1) →
    let n := Fintype.card V
    let d := minDegree G
    (diameter G : ℝ) ≤ amended_alpha k * n / d + C

/-- For k = 2 (K_3-free): coefficient is 3 - 2/2 = 2 -/
theorem amended_k2 : amended_alpha 2 = 2 := by
  simp [amended_alpha]
  ring

/-- For k = 3 (K_4-free): coefficient is 3 - 2/3 = 7/3 -/
theorem amended_k3 : amended_alpha 3 = 7/3 := by
  simp [amended_alpha]
  ring

/-- As k → ∞, coefficient → 3 (matching basic bound) -/
theorem amended_limit :
    Filter.Tendsto (fun k : ℕ => amended_alpha k) Filter.atTop (nhds 3) := by
  sorry

/-! ## Verified Cases -/

/-- k = 3 verified for 3-colorable graphs -/
axiom amended_k3_colorable :
  ∃ C : ℝ, ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    G.Connected →
    IsKFree G 4 →
    sorry → -- G is 3-colorable
    let n := Fintype.card V
    let d := minDegree G
    (diameter G : ℝ) ≤ amended_alpha 3 * n / d + C

/-- k = 4 verified for 4-colorable graphs -/
axiom amended_k4_colorable :
  ∃ C : ℝ, ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    G.Connected →
    IsKFree G 5 →
    sorry → -- G is 4-colorable
    let n := Fintype.card V
    let d := minDegree G
    (diameter G : ℝ) ≤ amended_alpha 4 * n / d + C

/-! ## Further Counterexamples -/

/-- Cambie-Jooken (2025): K_4-free counterexample -/
axiom cambie_jooken_counterexample :
  ∃ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    G.Connected ∧
    IsKFree G 4 ∧
    ¬(∃ C : ℝ, let n := Fintype.card V; let d := minDegree G;
      (diameter G : ℝ) ≤ amended_alpha 3 * n / d + C)

/-! ## Special Graph Classes -/

/-- Path graph: D = n-1, d = 1 (extreme case) -/
theorem path_diameter (n : ℕ) (hn : n ≥ 2) :
    sorry -- diameter of path = n - 1
    := by sorry

/-- Cycle graph: D = ⌊n/2⌋, d = 2 -/
theorem cycle_diameter (n : ℕ) (hn : n ≥ 3) :
    sorry -- diameter of cycle = n / 2
    := by sorry

/-- Complete graph: D = 1, d = n-1 -/
theorem complete_diameter [Nontrivial V] :
    diameter (⊤ : SimpleGraph V) = 1 := by
  sorry

/-- Complete bipartite K_{m,n}: D = 2 (if m,n ≥ 1) -/
theorem complete_bipartite_diameter (m n : ℕ) (hm : m ≥ 1) (hn : n ≥ 1) :
    sorry -- diameter = 2
    := by sorry

/-! ## Degree-Diameter Trade-off -/

/-- Higher minimum degree implies smaller diameter (for fixed n) -/
theorem degree_diameter_tradeoff :
    ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      G.Connected →
      let n := Fintype.card V
      let d := minDegree G
      (diameter G : ℝ) ≤ 3 * n / (d + 1) + 5 := by
  sorry

/-- The Moore bound perspective -/
theorem moore_bound (d D : ℕ) (hd : d ≥ 2) :
    sorry -- n ≤ 1 + d * ((d-1)^D - 1) / (d - 2) for d ≥ 3
    := by sorry

/-! ## Main Problem Status -/

/-- Erdős Problem #612: OPEN (PARTIALLY DISPROVED)

    Original conjectures: DISPROVED for r ≥ 2 (Czabarka-Singgih-Székely 2021)
    Base case r = 1: TRUE (triangle-free graphs)
    Amended conjecture: D ≤ (3 - 2/k) · n/d + O(1) for K_{k+1}-free

    The amended conjecture is verified for k = 3, 4 under colorability assumptions.
    Further counterexamples by Cambie-Jooken (2025) for K_4-free. -/
theorem erdos_612_status :
    (OriginalConjecture1 1) ∧
    (∀ r ≥ 2, ¬OriginalConjecture1 r) ∧
    (∃ C : ℝ, ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      G.Connected → IsTriangleFree G →
      (diameter G : ℝ) ≤ 5 * Fintype.card V / (2 * minDegree G) + C) := by
  refine ⟨conjecture1_base_case, ?_, triangle_free_diameter⟩
  intro r hr
  exact original_conjecture1_false r hr

#check erdos_612_status
#check AmendedConjecture
#check counterexample_exists
#check triangle_free_diameter

end Erdos612
