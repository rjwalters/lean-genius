/-
# Erdős Problem #1012 — OQ-04: the Woodall threshold as a deficiency from the complete graph

## Background

Erdős Problem #1012 (Woodall, 1972) concerns long cycles in dense graphs: every
graph on `n` vertices with at least

      edgeThreshold n k = C(n-k-1, 2) + C(k+2, 2) + 1

edges contains a cycle on `n - k` vertices.  The parent entry `Erdos1012OQ01`
formalizes this threshold and evaluates it at the extremal points `n = 2k+2`,
`n = 2k+3`; the sibling `Erdos1012OQ01OQ02` records its monotonicity / recurrence
*in `n`*.  What none of them records is how the threshold sits inside the
**complete graph** `K_n`, which has `C(n, 2)` edges.

This file supplies that structural decomposition.  The clean closed identity is

      C(n, 2) = C(n-k-1, 2) + C(k+2, 2) + (k+1)(n-k-2)              (n ≥ k+2),

so the maximal edge count that *avoids* the long cycle, `edgeThreshold n k − 1
= C(n-k-1, 2) + C(k+2, 2)`, is exactly the complete graph minus a **deficiency**
of `(k+1)(n-k-2)` edges:

      edgeThreshold n k = C(n, 2) − (k+1)(n-k-2) + 1.

The deficiency `(k+1)(n-k-2)` is itself the edge count of the complete bipartite
graph `K_{k+1, n-k-2}` — the bipartite "gap" between the `(k+1)`-part governing the
defect and the remaining `n-k-2` vertices.  This is precisely the structure of the
Woodall extremal construction, now pinned down arithmetically.

Everything is elementary `Nat.choose` arithmetic.  To keep the file self-contained
and machine-checked end to end (matching the style of `Erdos1012OQ03OQ02`), the
parent's one-line `edgeThreshold` definition is re-declared verbatim.

All results: 0 sorries, 0 axioms, no `native_decide`.

Reference: Woodall, D.R. (1972), *Sufficient conditions for circuits in graphs*;
https://erdosproblems.com/1012
-/

import Mathlib

open Nat

namespace Erdos1012OQ04

/-- The Erdős/Woodall edge threshold for the `(n-k)`-cycle problem, re-declared
verbatim from the parent `Erdos1012` namespace so this file stands alone. -/
def edgeThreshold (n k : ℕ) : ℕ :=
  Nat.choose (n - k - 1) 2 + Nat.choose (k + 2) 2 + 1

/-- The complete-bipartite **deficiency** `(k+1)(n-k-2)` separating the Woodall
threshold from the complete graph `K_n`. -/
def deficiency (n k : ℕ) : ℕ := (k + 1) * (n - k - 2)

/-! ## Core arithmetic: doubling `C(·, 2)` -/

/-- `2 · C(x+1, 2) = (x+1) · x`.  The successor form avoids truncated `ℕ`
subtraction, since `(x+1) - 1 = x` reduces definitionally. -/
theorem two_mul_choose_two_succ (x : ℕ) :
    2 * Nat.choose (x + 1) 2 = (x + 1) * x := by
  rw [Nat.choose_two_right]
  -- goal: `2 * ((x+1) * ((x+1) - 1) / 2) = (x+1) * x`
  rw [Nat.add_sub_cancel]
  -- `(x+1) * x` is even, so `2 * (· / 2)` recovers it
  rcases Nat.even_or_odd x with hx | hx
  · obtain ⟨t, ht⟩ := hx
    subst ht
    ring_nf
    omega
  · obtain ⟨t, ht⟩ := hx
    subst ht
    ring_nf
    omega

/-! ## The complete-graph decomposition -/

/-- **Core split identity (successor form).**  Writing `n = m + k + 2`
(so `m = n - k - 2 ≥ 0`), the complete-graph edge count `C(n, 2)` splits as

    C(m+k+2, 2) = C(m+1, 2) + C(k+2, 2) + (k+1)·m.

This is the parameter-clean heart of the file; the `n`-indexed form follows. -/
theorem choose_two_split (m k : ℕ) :
    Nat.choose (m + k + 2) 2
      = Nat.choose (m + 1) 2 + Nat.choose (k + 2) 2 + (k + 1) * m := by
  have key :
      2 * Nat.choose (m + k + 2) 2
        = 2 * (Nat.choose (m + 1) 2 + Nat.choose (k + 2) 2 + (k + 1) * m) := by
    have h1 : 2 * Nat.choose (m + k + 2) 2 = (m + k + 2) * (m + k + 1) := by
      have := two_mul_choose_two_succ (m + k + 1)
      simpa [Nat.add_assoc] using this
    have h2 : 2 * Nat.choose (m + 1) 2 = (m + 1) * m := two_mul_choose_two_succ m
    have h3 : 2 * Nat.choose (k + 2) 2 = (k + 2) * (k + 1) := two_mul_choose_two_succ (k + 1)
    -- expand the RHS doubling and finish by polynomial arithmetic
    rw [Nat.mul_add, Nat.mul_add, h1, h2, h3]
    ring
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) key

/-- **Core split identity (`n`-indexed form).**  For `n ≥ k + 2`,

    C(n, 2) = C(n-k-1, 2) + C(k+2, 2) + (k+1)(n-k-2).

The complete graph on `n` vertices decomposes into the Woodall extremal blocks
plus the bipartite deficiency. -/
theorem choose_two_split_n {n k : ℕ} (h : k + 2 ≤ n) :
    Nat.choose n 2
      = Nat.choose (n - k - 1) 2 + Nat.choose (k + 2) 2 + (k + 1) * (n - k - 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + k + 2 := ⟨n - k - 2, by omega⟩
  have e1 : m + k + 2 - k - 1 = m + 1 := by omega
  have e2 : m + k + 2 - k - 2 = m := by omega
  rw [e1, e2]
  exact choose_two_split m k

/-! ## Threshold ↔ complete graph -/

/-- **Threshold as complete minus deficiency (additive, successor form).**
`edgeThreshold (m+k+2) k + (k+1)·m = C(m+k+2, 2) + 1`. -/
theorem edgeThreshold_add_deficiency (m k : ℕ) :
    edgeThreshold (m + k + 2) k + (k + 1) * m = Nat.choose (m + k + 2) 2 + 1 := by
  have e1 : m + k + 2 - k - 1 = m + 1 := by omega
  rw [edgeThreshold, e1, choose_two_split m k]
  ring

/-- **Threshold as complete minus deficiency (`n`-indexed).**  For `n ≥ k + 2`,
`edgeThreshold n k + deficiency n k = C(n, 2) + 1`.  Equivalently, the threshold
is the complete-graph edge count reduced by the deficiency, plus one. -/
theorem edgeThreshold_add_deficiency_n {n k : ℕ} (h : k + 2 ≤ n) :
    edgeThreshold n k + deficiency n k = Nat.choose n 2 + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + k + 2 := ⟨n - k - 2, by omega⟩
  have e2 : m + k + 2 - k - 2 = m := by omega
  rw [deficiency, e2]
  exact edgeThreshold_add_deficiency m k

/-- **Maximal long-cycle-free edge count.**  The largest edge count that may avoid
the `(n-k)`-cycle is `edgeThreshold n k − 1`, and it equals the complete graph
minus the deficiency:  `(edgeThreshold n k − 1) + deficiency n k = C(n, 2)`. -/
theorem maxEdges_add_deficiency_n {n k : ℕ} (h : k + 2 ≤ n) :
    (edgeThreshold n k - 1) + deficiency n k = Nat.choose n 2 := by
  have hpos : 1 ≤ edgeThreshold n k := by
    rw [edgeThreshold]; omega
  have := edgeThreshold_add_deficiency_n h
  omega

/-! ## The deficiency is a complete-bipartite edge count -/

/-- The deficiency `(k+1)(n-k-2)` is the number of edges of the complete bipartite
graph `K_{k+1,\,n-k-2}` — the product of the two part sizes.  This is the precise
sense in which the Woodall threshold is "the complete graph minus a bipartite gap". -/
theorem deficiency_eq_bipartite_edges (n k : ℕ) :
    deficiency n k = (k + 1) * (n - k - 2) := rfl

/-! ## Sanity specializations -/

/-- **Hamiltonian (Ore) case `k = 0`.**  Avoiding an `n`-cycle, the maximal edge
count is `C(n,2) − (n-2) = C(n-1, 2) + 1`, i.e. one more than the complete graph on
`n − 1` vertices: removing a single vertex's worth of "long-cycle" connectivity. -/
theorem maxEdges_hamiltonian {n : ℕ} (h : 2 ≤ n) :
    (edgeThreshold n 0 - 1) + (n - 2) = Nat.choose n 2 := by
  have := maxEdges_add_deficiency_n (k := 0) (n := n) (by omega)
  simpa [deficiency] using this

/-- **Extremal point `n = 2k+2`.**  At the lower Woodall extremal size the
deficiency is `(k+1)·k = 2·C(k+1, 2)`. -/
theorem deficiency_at_extremal (k : ℕ) :
    deficiency (2 * k + 2) k = (k + 1) * k := by
  have e : 2 * k + 2 - k - 2 = k := by omega
  rw [deficiency, e]

end Erdos1012OQ04
