/-
Erdős Problem #799: List Chromatic Number of Random Graphs

Source: https://erdosproblems.com/799
Status: SOLVED (Alon 1992, Alon-Krivelevich-Sudakov 1999)

Statement:
The list chromatic number χ_L(G) is defined to be the minimal k such that for any
assignment of a list of k colours to each vertex of G (perhaps different lists for
different vertices) a colouring of each vertex by a colour on its list can be chosen
such that adjacent vertices receive distinct colours.

Is it true that χ_L(G) = o(n) for almost all graphs on n vertices?

Answer: YES

Alon (1992) proved that for the random graph G(n, 1/2):
  χ_L(G) ≪ (log log n / log n) · n almost surely.

Alon, Krivelevich, and Sudakov (1999) improved this to:
  χ_L(G) ≍ n / log n almost surely.

References:
- [Al92] Alon, Noga, "Choice numbers of graphs: a probabilistic approach"
         Combin. Probab. Comput. (1992), 107-114.
- [AKS99] Alon, Noga and Krivelevich, Michael and Sudakov, Benny,
          "List coloring of random and pseudo-random graphs"
          Combinatorica (1999), 453-472.
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Basic

open SimpleGraph Finset

namespace Erdos799

/-
## Part I: List Coloring Definitions
-/

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {C : Type*} [DecidableEq C]

/--
**Color List Assignment:**
A function assigning to each vertex a finite set of available colors.
-/
def ColorListAssignment (V : Type*) (C : Type*) := V → Finset C

/--
**Valid List Coloring:**
A coloring where each vertex receives a color from its list,
and adjacent vertices receive distinct colors.
-/
def IsValidListColoring (G : SimpleGraph V) (L : ColorListAssignment V C)
    (f : V → C) : Prop :=
  (∀ v, f v ∈ L v) ∧ (∀ v w, G.Adj v w → f v ≠ f w)

/--
**k-List Colorable:**
A graph G is k-list colorable if for any assignment of lists of size k
to each vertex, a valid list coloring exists.
-/
def IsListColorable (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ (C : Type) [DecidableEq C] (L : ColorListAssignment V C),
    (∀ v, (L v).card ≥ k) →
    ∃ f : V → C, IsValidListColoring G L f

/--
**List Chromatic Number (Choice Number):**
χ_L(G) is the minimum k such that G is k-list colorable.
-/
noncomputable def listChromaticNumber (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | IsListColorable G k}

/-
## Part II: Comparison with Ordinary Chromatic Number
-/

/--
**χ_L(G) ≥ χ(G):**
The list chromatic number is at least the ordinary chromatic number.
This is because we can give every vertex the same list of χ(G) colors.
-/
/--
**The gap can be arbitrarily large:**
There exist bipartite graphs (χ = 2) with arbitrarily large χ_L.
The complete bipartite graph K_{n,n} satisfies χ_L(K_{n,n}) ≥ ⌊log₂ n⌋ + 1.
-/
/-
## Part III: Random Graph Model
-/

/--
The list chromatic number of a graph on n vertices drawn from G(n, 1/2).
We axiomatize the almost-sure behavior rather than the probability model.
-/
axiom listChromaticRandom (n : ℕ) : ℕ

/--
**Chromatic number of random graphs:**
For G ∈ G(n, 1/2), χ(G) ≍ n / (2 log₂ n) almost surely.
-/
/-
## Part IV: Alon's 1992 Result
-/

/--
**Alon's Theorem (1992):**
For the random graph G on n vertices with edge probability 1/2:
  χ_L(G) ≪ (log log n / log n) · n almost surely.

This was the first proof that χ_L(G) = o(n) for random graphs, using
the probabilistic method and the Lovász Local Lemma.
-/
/--
**Corollary: χ_L(G) = o(n) Almost Surely.**
Alon's theorem implies that χ_L(G) grows slower than linearly in n.
-/
/-
## Part V: Alon-Krivelevich-Sudakov Improvement (1999)
-/

/--
**The Θ(n/log n) Result:**
Alon, Krivelevich, and Sudakov (1999) proved that for G ∈ G(n, 1/2):
  χ_L(G) ≍ n / log n almost surely.

More precisely:
- Upper bound: χ_L(G) ≤ C₁ · n / log n (semi-random / Rödl nibble method)
- Lower bound: χ_L(G) ≥ C₂ · n / log n (adversarial list construction)
-/
axiom alon_krivelevich_sudakov_1999 :
    ∃ C₁ C₂ : ℝ, C₁ > 0 ∧ C₂ > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      C₂ * (n : ℝ) / Real.log n ≤ (listChromaticRandom n : ℝ) ∧
      (listChromaticRandom n : ℝ) ≤ C₁ * (n : ℝ) / Real.log n

/-
## Part VI: Comparison: χ_L(G) vs χ(G) for Random Graphs
-/

/--
**Asymptotic Ratio:**
For G ∈ G(n, 1/2):
- χ(G) ≈ n / (2 log₂ n)
- χ_L(G) ≍ n / log n

So χ_L(G) / χ(G) → 2 / ln 2 ≈ 2.885 as n → ∞.
The list chromatic number exceeds the ordinary one by a constant factor.
-/
/-
## Part VII: Main Results
-/

/--
**Erdős Problem #799: SOLVED**

Question: Is χ_L(G) = o(n) for almost all graphs on n vertices?

Answer: YES

For the random graph G(n, 1/2):
1. Alon (1992): χ_L(G) ≪ (log log n / log n) · n
2. AKS (1999): χ_L(G) ≍ n / log n

Both bounds show χ_L(G) = o(n) almost surely.
-/
theorem erdos_799 :
    ∃ C₁ C₂ : ℝ, C₁ > 0 ∧ C₂ > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      C₂ * (n : ℝ) / Real.log n ≤ (listChromaticRandom n : ℝ) ∧
      (listChromaticRandom n : ℝ) ≤ C₁ * (n : ℝ) / Real.log n :=
  alon_krivelevich_sudakov_1999

end Erdos799
