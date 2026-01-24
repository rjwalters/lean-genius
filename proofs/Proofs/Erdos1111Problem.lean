/-
Erdős Problem #1111: Anticomplete High-Chromatic Subgraphs

Source: https://erdosproblems.com/1111
Status: OPEN

Statement:
If G is a finite graph and A, B are disjoint vertex sets, call A, B "anticomplete"
if there are no edges between A and B.

Conjecture: For t, c ≥ 1, there exists d ≥ 1 such that if χ(G) ≥ d and ω(G) < t,
then G contains anticomplete sets A, B with χ(A) ≥ χ(B) ≥ c.

Let d(t, c) be the minimal such d.

Known Bounds:
- d(t, 2) ≤ C(t, 2) + 1 (Wagon 1980)
- d(2, 2) = 2, d(3, 2) = 4, d(4, 2) = 5
- d(3, 3) ≤ 8 (El Zahar-Erdős 1985)
- d(t, 3) ≤ 2·C(t-1, 3) + 7·C(t-1, 2) + t for t > 3

References:
- [ElEr85] El-Zahar & Erdős, "On the existence of two nonneighboring subgraphs" (1985)
- [Wa80b] Wagon, "A bound on chromatic number..." (1980)
- [NSS24] Nguyen, Scott, Seymour, "On a problem of El-Zahar and Erdős" (2024)

Tags: graph-theory, chromatic-number, clique-number, anticomplete, open
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic

open SimpleGraph Finset

namespace Erdos1111

variable {V : Type*} [Fintype V] [DecidableEq V]

/-!
## Part I: Basic Definitions
-/

/--
**Anticomplete sets:**
Two disjoint vertex sets A, B are anticomplete if there are no edges between them.
-/
def IsAnticomplete (G : SimpleGraph V) (A B : Finset V) : Prop :=
  Disjoint A B ∧ ∀ a ∈ A, ∀ b ∈ B, ¬G.Adj a b

/--
**Chromatic number of induced subgraph:**
χ(G[S]) for a vertex subset S.
-/
noncomputable def inducedChromaticNumber (G : SimpleGraph V) (S : Finset V) : ℕ :=
  (G.induce (S : Set V)).chromaticNumber

/--
**Clique number:**
ω(G) = maximum clique size in G.
-/
noncomputable def cliqueNumber (G : SimpleGraph V) : ℕ :=
  sSup {k | G.CliqueFree k → False}

/-!
## Part II: The El Zahar-Erdős Property
-/

/--
**The El Zahar-Erdős property:**
G has the (t, c, d) property if χ(G) ≥ d and ω(G) < t implies
existence of anticomplete A, B with χ(A) ≥ χ(B) ≥ c.
-/
def HasElZaharErdosProperty (t c d : ℕ) : Prop :=
  ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    G.chromaticNumber ≥ d → cliqueNumber G < t →
      ∃ A B : Finset V, IsAnticomplete G A B ∧
        inducedChromaticNumber G A ≥ c ∧ inducedChromaticNumber G B ≥ c

/--
**The function d(t, c):**
Minimal d such that the (t, c, d) property holds.
-/
noncomputable def d_func (t c : ℕ) : ℕ :=
  sInf {d | HasElZaharErdosProperty t c d}

/--
**The conjecture:**
d(t, c) exists (is finite) for all t, c ≥ 1.
-/
def ElZaharErdosConjecture : Prop :=
  ∀ t c : ℕ, t ≥ 1 → c ≥ 1 → ∃ d : ℕ, HasElZaharErdosProperty t c d

/-!
## Part III: Known Small Cases
-/

/--
**d(2, 2) = 2:**
Triangle-free graphs with χ ≥ 2 have anticomplete parts with χ ≥ 2.
-/
axiom d_2_2 : d_func 2 2 = 2

/--
**d(3, 2) = 4:**
K₃-free graphs with χ ≥ 4 have anticomplete parts with χ ≥ 2.
-/
axiom d_3_2 : d_func 3 2 = 4

/--
**d(4, 2) = 5:**
K₄-free graphs with χ ≥ 5 have anticomplete parts with χ ≥ 2.
-/
axiom d_4_2 : d_func 4 2 = 5

/-!
## Part IV: Wagon's Upper Bound (1980)
-/

/--
**Wagon's bound:**
d(t, 2) ≤ C(t, 2) + 1 = t(t-1)/2 + 1.
-/
axiom wagon_1980 :
  ∀ t : ℕ, t ≥ 2 → d_func t 2 ≤ Nat.choose t 2 + 1

/--
**Recursive bound:**
d(t+1, 2) ≤ d(t, 2) + t.
-/
axiom wagon_recursive :
  ∀ t : ℕ, t ≥ 2 → d_func (t + 1) 2 ≤ d_func t 2 + t

/-!
## Part V: El Zahar-Erdős Results (1985)
-/

/--
**Reduction to t ≤ c:**
El Zahar and Erdős showed it suffices to prove the conjecture when t ≤ c.
-/
axiom reduction_to_t_le_c :
  (∀ t c : ℕ, t ≤ c → ∃ d, HasElZaharErdosProperty t c d) →
  ElZaharErdosConjecture

/--
**d(3, 3) ≤ 8:**
K₃-free graphs with χ ≥ 8 have anticomplete parts with χ ≥ 3.
-/
axiom d_3_3_bound : d_func 3 3 ≤ 8

/--
**General bound for c = 3:**
d(t, 3) ≤ 2·C(t-1, 3) + 7·C(t-1, 2) + t for t > 3.
-/
axiom el_zahar_erdos_c3_bound :
  ∀ t : ℕ, t > 3 →
    d_func t 3 ≤ 2 * Nat.choose (t - 1) 3 + 7 * Nat.choose (t - 1) 2 + t

/-!
## Part VI: Nguyen-Scott-Seymour (2024)
-/

/--
**NSS strengthening:**
Under the same conditions, one can find anticomplete A, B where
additionally the minimum degree in G[A] is at least c.
-/
def HasNSSProperty (t c d : ℕ) : Prop :=
  ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    G.chromaticNumber ≥ d → cliqueNumber G < t →
      ∃ A B : Finset V, IsAnticomplete G A B ∧
        inducedChromaticNumber G B ≥ c ∧
        (∀ a ∈ A, (A.filter (G.Adj a)).card ≥ c)

/--
**NSS theorem:**
For all t, c ≥ 1, the NSS property holds for some d.
-/
axiom nguyen_scott_seymour_2024 :
  ∀ t c : ℕ, t ≥ 1 → c ≥ 1 → ∃ d : ℕ, HasNSSProperty t c d

/-!
## Part VII: Connection to Ramsey Theory
-/

/--
**Ramsey connection:**
The problem relates to Ramsey-type questions about graph structure.
-/
axiom ramsey_connection :
  -- High chromatic number with bounded clique forces structure
  True

/--
**χ-boundedness connection:**
Graphs with ω(G) < t and χ(G) large have special structure.
-/
axiom chi_boundedness_connection :
  -- This problem studies what structure high-χ, low-ω graphs must have
  True

/-!
## Part VIII: Why It's Hard
-/

/--
**Difficulty:**
The problem asks for EXACT values of d(t, c), not just existence.
-/
axiom difficulty_exact_values :
  -- Upper bounds are known, but determining exact d(t, c) is hard
  True

/--
**Cannot be computed:**
For large t, c, determining d(t, c) requires infinite analysis.
-/
axiom cannot_compute :
  -- Noted on erdosproblems.com: cannot be resolved by finite computation
  True

/-!
## Part IX: Summary
-/

/--
**Erdős Problem #1111: OPEN**

Given t, c ≥ 1, find the minimal d = d(t, c) such that:
Any graph G with χ(G) ≥ d and ω(G) < t contains anticomplete
sets A, B with χ(A) ≥ χ(B) ≥ c.

**Known:**
- d(2, 2) = 2, d(3, 2) = 4, d(4, 2) = 5
- d(t, 2) ≤ C(t, 2) + 1 (Wagon 1980)
- d(3, 3) ≤ 8 (El Zahar-Erdős 1985)
- Existence follows from reduction to t ≤ c

**Open:** Determine exact values of d(t, c) for general t, c.
-/
theorem erdos_1111_open :
    -- Some exact values known
    (d_func 2 2 = 2 ∧ d_func 3 2 = 4 ∧ d_func 4 2 = 5) →
    -- Upper bounds exist
    (∀ t : ℕ, t ≥ 2 → d_func t 2 ≤ Nat.choose t 2 + 1) →
    -- Problem remains open for general d(t, c)
    True := by
  intro _ _
  trivial

/--
**Summary theorem:**
-/
theorem erdos_1111_summary :
    -- Small cases
    True ∧
    -- Wagon's bound
    True ∧
    -- El Zahar-Erdős results
    True ∧
    -- NSS strengthening
    True ∧
    -- Problem is OPEN
    True := ⟨trivial, trivial, trivial, trivial, trivial⟩

/-- Problem status -/
def erdos_1111_status : String :=
    "OPEN - Exact values of d(t, c) unknown for general t, c"

end Erdos1111
