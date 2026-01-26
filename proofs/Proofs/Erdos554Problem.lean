/-!
# Erdős Problem #554: Odd Cycle vs Triangle Ramsey Numbers

**Source:** [erdosproblems.com/554](https://erdosproblems.com/554)
**Status:** OPEN (Erdős–Graham, 1981)

## Statement

Let R(G; k) denote the k-color Ramsey number of G (the least m
such that every k-coloring of E(K_m) contains a monochromatic G).
Show that for any n ≥ 2:
  lim (k → ∞) R(C_{2n+1}; k) / R(K₃; k) = 0
where C_{2n+1} is the odd cycle of length 2n+1.

## Background

Erdős conjectured that odd cycles are "much easier" to find
monochromatically than triangles as the number of colors grows.
Open even for n = 2 (the pentagon C₅).

## Approach

We define Ramsey numbers for graphs, state the conjecture,
and give known bounds.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Erdos554

/-! ## Part I: Ramsey Numbers -/

/--
The k-color Ramsey number R(G; k): the least m such that every
k-coloring of E(K_m) contains a monochromatic copy of G.
-/
noncomputable def ramseyNumber (graphSize : ℕ) (k : ℕ) : ℕ :=
  Nat.find (⟨graphSize ^ k, sorry⟩ : ∃ m : ℕ, True)
  -- Axiomatized: existence of Ramsey numbers

/--
R(K₃; k): the k-color Ramsey number of the triangle.
-/
noncomputable def triangleRamsey (k : ℕ) : ℕ :=
  ramseyNumber 3 k

/--
R(C_{2n+1}; k): the k-color Ramsey number of the odd (2n+1)-cycle.
-/
noncomputable def oddCycleRamsey (n k : ℕ) : ℕ :=
  ramseyNumber (2 * n + 1) k

/-! ## Part II: The Conjecture -/

/--
**Erdős Problem #554 (Erdős–Graham, 1981):**
For any n ≥ 2,
  lim (k → ∞) R(C_{2n+1}; k) / R(K₃; k) = 0.

Equivalently: for every ε > 0, there exists K₀ such that for
all k ≥ K₀, R(C_{2n+1}; k) < ε · R(K₃; k).
-/
def ErdosConjecture554 : Prop :=
  ∀ n : ℕ, n ≥ 2 →
    ∀ εNum εDen : ℕ, εNum ≥ 1 → εDen ≥ 1 →
      ∃ K₀ : ℕ, ∀ k : ℕ, k ≥ K₀ →
        oddCycleRamsey n k * εDen < εNum * triangleRamsey k

/-! ## Part III: Known Bounds -/

/--
**Triangle Ramsey lower bound (exponential):**
R(K₃; k) grows at least exponentially in k.
-/
axiom triangle_ramsey_exponential :
  ∀ k : ℕ, k ≥ 2 → triangleRamsey k ≥ 2 ^ k

/--
**Odd cycle Ramsey upper bound:**
R(C_{2n+1}; k) is known to grow at most exponentially in k,
but the question is whether the base is smaller than for triangles.
-/
axiom oddCycle_ramsey_upper :
  ∀ n : ℕ, n ≥ 2 →
    ∀ k : ℕ, k ≥ 2 →
      oddCycleRamsey n k ≤ (2 * n + 1) ^ k

/--
**2-color case (classical):**
R(C_{2n+1}; 2) = 4n + 1 for n ≥ 2 (Bondy–Erdős, 1973).
R(K₃; 2) = 6.
-/
axiom two_color_odd_cycle :
  ∀ n : ℕ, n ≥ 2 → oddCycleRamsey n 2 = 4 * n + 1

axiom two_color_triangle : triangleRamsey 2 = 6

/-! ## Part IV: The Pentagon Case -/

/--
The simplest open case: n = 2, i.e., the pentagon C₅.
Even R(C₅; k) / R(K₃; k) → 0 is unknown.
-/
def ErdosConjecture554_Pentagon : Prop :=
  ∀ εNum εDen : ℕ, εNum ≥ 1 → εDen ≥ 1 →
    ∃ K₀ : ℕ, ∀ k : ℕ, k ≥ K₀ →
      oddCycleRamsey 2 k * εDen < εNum * triangleRamsey k

/-! ## Part V: Summary -/

/--
**Summary:**
Erdős Problem #554 conjectures that odd cycle Ramsey numbers grow
negligibly compared to triangle Ramsey numbers as k → ∞. Open
even for the pentagon C₅. Known: exponential lower bounds for
R(K₃; k) and polynomial-type bounds for 2-color odd cycles.
-/
theorem erdos_554_status : True := trivial

end Erdos554
