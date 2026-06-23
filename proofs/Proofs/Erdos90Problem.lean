/-
# Erdős Problem #90 — The Unit Distance Problem

Given n points in the plane ℝ², what is the maximum number u(n) of pairs
at unit distance apart? Erdős (1946) conjectured u(n) = n^{1+O(1/log log n)}.

Known results:
- Upper bound: u(n) = O(n^{4/3}) (Spencer–Szemerédi–Trotter 1984)
- Lower bound: u(n) ≥ n^{1+c/log log n} for some c > 0 (lattice constructions)
- The upper bound cannot be improved by methods that work in general metrics (Valtr)
- On 2026-05-20, OpenAI announced a construction (rings of integers in number fields
  with infinite class field towers, via Golod–Shafarevich) reportedly disproving the
  conjectured exponent — peer review pending. The Spencer–Szemerédi–Trotter O(n^{4/3})
  upper bound is unaffected, and the true asymptotic order of u(n) remains open.

$500 prize offered by Erdős.

References:
- https://erdosproblems.com/90
- OpenAI announcement (2026-05-20):
    https://openai.com/index/model-disproves-discrete-geometry-conjecture/
- OpenAI technical note:
    https://cdn.openai.com/pdf/74c24085-19b0-4534-9c90-465b8e29ad73/unit-distance-remarks.pdf
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

/- ## Unit Distance Counting -/

/-- Count unordered pairs of distinct points at unit distance -/
noncomputable def unitDistancePairsCount (points : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  (points.offDiag.filter (fun p => dist p.1 p.2 = 1)).card / 2

/-- The set of achievable unit distance counts for n-point configurations -/
noncomputable def unitDistanceCounts (n : ℕ) : Set ℕ :=
  {unitDistancePairsCount pts |
    (pts : Finset (EuclideanSpace ℝ (Fin 2))) (_ : pts.card = n)}

/-- The maximum number of unit distances among n points in the plane -/
noncomputable def maxUnitDistances (n : ℕ) : ℕ :=
  sSup (unitDistanceCounts n)

/- ## Trivial Bound -/

/-- The set of unit distance counts is bounded above by C(n,2),
    the total number of pairs -/
/- ## Spencer–Szemerédi–Trotter Upper Bound -/

/-- u(n) = O(n^{4/3}): the best known upper bound on unit distances.
    Proved by Spencer, Szemerédi, and Trotter (1984) using the
    Szemerédi–Trotter incidence theorem. -/
/- ## Lattice Lower Bound -/

/-- There exist n-point configurations with n^{1+c/log log n} unit distances
    for some constant c > 0, achieved by lattice-point constructions -/
/- ## Erdős's 1946 Conjecture (reportedly disproved by OpenAI 2026-05-20,
       peer review pending) -/

/-- Erdős's 1946 conjecture (now reportedly false, peer review pending):
    u(n) = n^{1+O(1/log log n)}, i.e. the maximum number of unit distances
    among n points in ℝ² is at most n^{1+O(1/log log n)}. This would have
    matched the lattice lower bound up to the constant in the exponent.
    $500 prize. Posed 1946. On 2026-05-20, OpenAI announced a construction
    via number fields with infinite class field towers (Golod–Shafarevich)
    reportedly giving a polynomial improvement over the lattice lower bound,
    disproving the conjectured exponent — peer review pending. -/
/-- Stronger (now also in doubt) form: u(n) = n^{1+o(1)}, meaning the exponent
    approaches 1. Erdős offered $300 (later $250) for this weaker conjecture.
    Status of this weak form under the OpenAI 2026 construction depends on the
    precise exponent achieved (peer review pending). -/
/- ## Valtr's Obstruction -/

/-- Valtr showed that there exists a metric on ℝ² (not Euclidean) where
    n points can have Θ(n^{4/3}) unit distances. This means any improvement
    over the n^{4/3} upper bound must use specific properties of Euclidean
    distance, not just the incidence structure. -/
