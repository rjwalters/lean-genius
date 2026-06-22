import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-
# The Discharging Base for Planar Graphs

## What This Proves

The parent gallery proof (`FiveColorTheorem.lean`, "Five Color Theorem via Kempe
Chain Argument") establishes as its key structural ingredient that **every planar
graph has a vertex of degree ≤ 5** (`exists_low_degree`). That statement only
asserts the *existence* of one low-degree vertex.

This file proves the **quantitative foundation** behind it — the *discharging
base inequality* that is the starting point of every discharging proof in the
Four/Five Color Theorem literature:

For a planar graph (`E ≤ 3V - 6`), assigning each vertex `v` the **charge**
`6 - deg(v)`, the total charge is at least `12`:

  ∑_v (6 - deg v) ≥ 12.

Equivalently, with Euler's relation behind `E ≤ 3V-6`, the total charge equals
exactly `6V - 2E ≥ 12` (with equality iff the graph is a triangulation).

From this single linear fact we recover and sharpen the parent's result:

* `exists_low_degree'` — at least **one** vertex of degree ≤ 5 (re-derived);
* `two_low_degree` — at least **two** vertices of degree ≤ 5 (strict sharpening);
* `no_min_degree_six` — there is **no** planar graph of minimum degree ≥ 6;
* `sum_degrees_le` / `average_degree_lt_six` — the average degree is `< 6`.

Everything here is **fully machine-checked and axiom-free** (no `sorry`, no
`axiom`, no `native_decide`). The only planarity input is the edge bound
`E ≤ 3V - 6`, exactly the hypothesis used in the parent file; we do not touch the
parent's three planarity axioms.

## Why the Discharging Base Matters

The "charge" `6 - deg(v)` is the discrete Gauss–Bonnet curvature of a planar
graph: handshaking + Euler force the total to be a positive constant (`12`),
no matter how large the graph is. Discharging proofs redistribute this fixed
positive total to force the existence of unavoidable local configurations. The
`exists_low_degree` fact used by the Five Color Theorem is the very simplest
consequence: a positive total charge means some vertex carries positive charge,
i.e. `deg < 6`.

## References
- Diestel, "Graph Theory", 5th ed., §5.1 (the bound E ≤ 3V-6) and §5.4 (discharging)
- Appel–Haken (1977); Robertson–Sanders–Seymour–Thomas (1997) — discharging for 4CT
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace PlanarGraphDischarging

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ============================================================
-- PART 1: The discharging identity (no planarity needed)
-- ============================================================

/-- **Charge identity.** With charge `6 - deg(v)` at each vertex, the total
    charge equals `6V - 2E`. This is pure handshaking: `∑ deg = 2E`. No
    planarity hypothesis is required. -/
theorem total_charge_eq (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∑ v, (6 - (G.degree v : ℤ)) = 6 * (Fintype.card V : ℤ) - 2 * G.edgeFinset.card := by
  have hdeg : (∑ v, (G.degree v : ℤ)) = 2 * (G.edgeFinset.card : ℤ) := by
    calc (∑ v, (G.degree v : ℤ))
        = ((∑ v, G.degree v : ℕ) : ℤ) := by push_cast; ring
      _ = ((2 * G.edgeFinset.card : ℕ) : ℤ) := by rw [G.sum_degrees_eq_twice_card_edges]
      _ = 2 * (G.edgeFinset.card : ℤ) := by push_cast; ring
  have hconst : (∑ _v : V, (6 : ℤ)) = 6 * (Fintype.card V : ℤ) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  rw [Finset.sum_sub_distrib, hconst, hdeg]

-- ============================================================
-- PART 2: The discharging base inequality (planar graphs)
-- ============================================================

/-- **Discharging base.** For a planar graph (`E ≤ 3V - 6`) the total charge
    `∑ (6 - deg v)` is at least `12`. This is the quantitative core behind every
    discharging argument and behind the parent file's `exists_low_degree`. -/
theorem discharging_base (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_edge : (G.edgeFinset.card : ℤ) ≤ 3 * Fintype.card V - 6) :
    (12 : ℤ) ≤ ∑ v, (6 - (G.degree v : ℤ)) := by
  rw [total_charge_eq]
  linarith

-- ============================================================
-- PART 3: Consequences for low-degree vertices
-- ============================================================

/-- **At least one vertex of degree ≤ 5** (the parent's `exists_low_degree`,
    re-derived directly from the discharging base: a positive total charge forces
    a vertex of positive charge, i.e. degree `< 6`). -/
theorem exists_low_degree' (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_edge : (G.edgeFinset.card : ℤ) ≤ 3 * Fintype.card V - 6) :
    ∃ v : V, G.degree v ≤ 5 := by
  by_contra h
  push_neg at h
  have hbase := discharging_base G h_edge
  have hnonpos : ∑ v, (6 - (G.degree v : ℤ)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro v _
    have : (6 : ℤ) ≤ (G.degree v : ℤ) := by exact_mod_cast h v
    linarith
  linarith

/-- **At least two vertices of degree ≤ 5** — a strict sharpening of the parent's
    existence statement. Each low-degree vertex carries charge `6 - deg ≤ 6`,
    while high-degree vertices carry charge `≤ 0`; since the total is `≥ 12`,
    at least two vertices must be low-degree. -/
theorem two_low_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_edge : (G.edgeFinset.card : ℤ) ≤ 3 * Fintype.card V - 6) :
    2 ≤ (Finset.univ.filter (fun v => G.degree v ≤ 5)).card := by
  classical
  set L := Finset.univ.filter (fun v => G.degree v ≤ 5) with hL
  have hbase := discharging_base G h_edge
  -- Split the total charge over low-degree vertices and the rest.
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun v => G.degree v ≤ 5) (fun v => 6 - (G.degree v : ℤ))
  -- High-degree vertices carry non-positive charge.
  have hneg : ∑ v ∈ Finset.univ.filter (fun v => ¬ G.degree v ≤ 5),
      (6 - (G.degree v : ℤ)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro v hv
    rw [Finset.mem_filter] at hv
    have : (6 : ℤ) ≤ (G.degree v : ℤ) := by
      have : 5 < G.degree v := by omega
      exact_mod_cast this
    linarith
  -- Each low-degree vertex carries charge at most 6.
  have hpos : ∑ v ∈ L, (6 - (G.degree v : ℤ)) ≤ 6 * (L.card : ℤ) := by
    calc ∑ v ∈ L, (6 - (G.degree v : ℤ))
        ≤ ∑ _v ∈ L, (6 : ℤ) := by
          apply Finset.sum_le_sum
          intro v _
          have : (0 : ℤ) ≤ (G.degree v : ℤ) := by positivity
          linarith
      _ = 6 * (L.card : ℤ) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  -- Combine: 12 ≤ total = (low part) + (high part) ≤ 6|L| + 0.
  have hkey : (12 : ℤ) ≤ 6 * (L.card : ℤ) := by
    have : (12 : ℤ) ≤ ∑ v ∈ L, (6 - (G.degree v : ℤ))
        + ∑ v ∈ Finset.univ.filter (fun v => ¬ G.degree v ≤ 5), (6 - (G.degree v : ℤ)) := by
      rw [hsplit]; exact hbase
    linarith
  have : (2 : ℤ) ≤ (L.card : ℤ) := by linarith
  exact_mod_cast this

/-- **No planar graph has minimum degree ≥ 6.** Immediate from `exists_low_degree'`:
    a planar graph always has a vertex of degree ≤ 5. -/
theorem no_min_degree_six (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_edge : (G.edgeFinset.card : ℤ) ≤ 3 * Fintype.card V - 6) :
    ¬ (∀ v : V, 6 ≤ G.degree v) := by
  intro h
  obtain ⟨v, hv⟩ := exists_low_degree' G h_edge
  exact absurd (h v) (by omega)

-- ============================================================
-- PART 4: Average degree bound
-- ============================================================

/-- The sum of degrees of a planar graph is at most `6V - 12`; equivalently the
    average degree is strictly below `6`. -/
theorem sum_degrees_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_edge : (G.edgeFinset.card : ℤ) ≤ 3 * Fintype.card V - 6) :
    (∑ v, (G.degree v : ℤ)) ≤ 6 * (Fintype.card V : ℤ) - 12 := by
  have hcharge := total_charge_eq G
  have hbase := discharging_base G h_edge
  have hconst : (∑ _v : V, (6 : ℤ)) = 6 * (Fintype.card V : ℤ) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  -- ∑ (6 - deg) = (∑ 6) - (∑ deg)
  have hsplit : ∑ v, (6 - (G.degree v : ℤ))
      = (∑ _v : V, (6 : ℤ)) - ∑ v, (G.degree v : ℤ) := by
    rw [Finset.sum_sub_distrib]
  rw [hsplit, hconst] at hbase
  linarith

/-- **Average degree < 6.** For a nonempty planar graph the average degree is
    strictly less than `6` (stated as `∑ deg < 6V`). -/
theorem average_degree_lt_six (G : SimpleGraph V) [DecidableRel G.Adj]
    (hV : 0 < Fintype.card V)
    (h_edge : (G.edgeFinset.card : ℤ) ≤ 3 * Fintype.card V - 6) :
    (∑ v, (G.degree v : ℤ)) < 6 * (Fintype.card V : ℤ) := by
  have := sum_degrees_le G h_edge
  linarith

-- ============================================================
-- PART 5: Sharpness of the discharging base
-- ============================================================

/-- The discharging base is **sharp**: equality `∑ (6 - deg v) = 12` holds exactly
    when the graph is an edge-maximal planar graph (a triangulation, `E = 3V-6`).
    This records the equality case of `total_charge_eq`. -/
theorem charge_eq_twelve_iff_triangulation (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ v, (6 - (G.degree v : ℤ)) = 12) ↔ (G.edgeFinset.card : ℤ) = 3 * Fintype.card V - 6 := by
  rw [total_charge_eq]; constructor <;> intro h <;> linarith

end PlanarGraphDischarging
