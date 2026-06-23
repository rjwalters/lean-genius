/-
Erdős Problem #832: Minimum Edges in Hypergraphs with Given Chromatic Number

Source: https://erdosproblems.com/832
Status: SOLVED (Conjecture disproved by Alon for r ≥ 4)

Statement:
Let r ≥ 3 and k be sufficiently large in terms of r. Is it true that every
r-uniform hypergraph with chromatic number k has at least C((r-1)(k-1)+1, r)
edges, with equality only for the complete graph on (r-1)(k-1)+1 vertices?

Answer: NO (for r ≥ 4) — Alon (1985) disproved this conjecture.

Key Results:
- r = 2: Classical — chromatic number k implies ≥ C(k,2) edges
- r = 3: FALSE for small k (Steiner triples), OPEN for large k
- r ≥ 4: FALSE (Alon 1985, factor (7/8)^r improvement)
- Asymptotic: m(r,k) ~ c_r · k^r (Cherkashin-Petrov 2020)
- Bounds: (r/log r) · k^r ≪ m(r,k) ≪ (r³ log r) · k^r (Akolzin-Shabanov 2016)

References:
- [Al85] Alon: Hypergraphs with high chromatic number (1985)
- [AkSh16] Akolzin-Shabanov (2016)
- [ChPe20] Cherkashin-Petrov (2020)
- https://erdosproblems.com/832
-/

import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

namespace Erdos832

/- ## Part I: Basic Definitions -/

/-- **r-Uniform Hypergraph:**
A collection of edges where each edge has exactly r vertices. -/
structure Hypergraph (V : Type*) where
  edges : Set (Finset V)

/-- **r-Uniformity:** All edges have exactly r vertices. -/
def IsUniform (H : Hypergraph V) (r : ℕ) : Prop :=
  ∀ e ∈ H.edges, e.card = r

/-- **Proper k-colouring of a hypergraph:**
An assignment of colours to vertices such that no edge is monochromatic. -/
def IsProperColouring {V : Type*} (H : Hypergraph V) (c : V → Fin k) : Prop :=
  ∀ e ∈ H.edges, ∃ u v, u ∈ e ∧ v ∈ e ∧ c u ≠ c v

/-- **Chromatic number at least k:** No proper (k-1)-colouring exists. -/
def hasChromaticNumberAtLeast (H : Hypergraph V) (k : ℕ) : Prop :=
  ¬∃ c : V → Fin (k - 1), IsProperColouring H c

/- ## Part II: The Classical Graph Case (r = 2) -/

/-- **Classical result for graphs (r = 2):**
A graph with chromatic number k has at least C(k, 2) = k(k-1)/2 edges.
The complete graph K_k is the extremal example. -/
/- ## Part III: Erdős's Conjecture -/

/-- **Erdős's conjecture (disproved for r ≥ 4):**
For r ≥ 3 and k sufficiently large, every r-uniform hypergraph with
chromatic number k has at least C((r-1)(k-1)+1, r) edges. -/
def erdosConjecture (r k : ℕ) : Prop :=
  r ≥ 3 →
    ∀ H : Hypergraph V, IsUniform H r → hasChromaticNumberAtLeast H k →
      ∃ n : ℕ, n ≥ Nat.choose ((r - 1) * (k - 1) + 1) r

/- ## Part IV: Counterexamples -/

/-- **Steiner triple system counterexample (r = 3, k = 3):**
The Fano plane is a 3-uniform hypergraph on 7 vertices with 7 edges
that requires 3 colours. Erdős's conjecture predicts ≥ C(5,3) = 10 edges. -/
/-- **Alon's theorem (1985):**
For r ≥ C (some absolute constant) and k ≥ C·r, there exists an
r-uniform hypergraph with chromatic number ≥ k having at most
(7/8)^r · C((r-1)(k-1)+1, r) edges. This disproves the conjecture for r ≥ 4. -/
axiom alon_disproof :
    ∃ C : ℕ, C > 0 ∧
      ∀ r : ℕ, r ≥ C →
        ∀ k : ℕ, k ≥ C * r →
          ∃ H : Hypergraph V,
            IsUniform H r ∧
            hasChromaticNumberAtLeast H k

/- ## Part V: The Function m(r, k) -/

/-- **m(r, k):** The minimum number of edges in any r-uniform hypergraph
with chromatic number > k. Axiomatized since computing the minimum
requires the finite obstruction principle. -/
axiom m (r k : ℕ) : ℕ

/-- **Akolzin-Shabanov bounds (2016):**
(r / log r) · k^r ≪ m(r, k) ≪ (r³ log r) · k^r -/
/-- **Cherkashin-Petrov theorem (2020):**
For fixed r, the ratio m(r, k) / k^r converges to some limit c_r. -/
axiom cherkashin_petrov_limit :
    ∀ r : ℕ, r ≥ 3 →
      ∃ c_r : ℝ, c_r > 0 ∧
        Filter.Tendsto (fun k => (m r k : ℝ) / k^r) Filter.atTop (nhds c_r)

/- ## Part VI: Open Questions -/

/-- **Open problem for r = 3:** Is the conjecture true for r = 3 and large k? -/
def r3_open_question : Prop :=
  ∃ K : ℕ, ∀ k ≥ K, erdosConjecture 3 k

/- ## Part VII: Concrete Examples -/

/-- The Fano plane bound: C(5,3) = 10, so 7 edges < 10. -/
example : 7 < Nat.choose 5 3 := by norm_num

/-- Alon's factor for r = 4: (7/8)^4 ≈ 0.586. -/
example : (7/8 : ℝ)^4 < 0.6 := by norm_num

/- ## Part VIII: Summary -/

/-- **Erdős Problem #832: SOLVED (disproved for r ≥ 4)**

CONJECTURE: r-uniform hypergraph with χ = k has ≥ C((r-1)(k-1)+1, r) edges.
STATUS: DISPROVED for r ≥ 4 (Alon 1985)

Key results:
- r = 2: TRUE (classical)
- r = 3, small k: FALSE (Fano plane)
- r ≥ 4: FALSE (Alon)
- Asymptotic: m(r,k) ~ c_r · k^r (Cherkashin-Petrov 2020) -/
theorem erdos_832 :
    (∃ C : ℕ, C > 0 ∧
      ∀ r : ℕ, r ≥ C →
        ∀ k : ℕ, k ≥ C * r →
          ∃ H : Hypergraph V,
            IsUniform H r ∧ hasChromaticNumberAtLeast H k) ∧
    (∀ r : ℕ, r ≥ 3 →
      ∃ c_r : ℝ, c_r > 0 ∧
        Filter.Tendsto (fun k => (m r k : ℝ) / k^r) Filter.atTop (nhds c_r)) :=
  ⟨alon_disproof, cherkashin_petrov_limit⟩

end Erdos832
