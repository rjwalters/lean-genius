# erdos-1009-oq-03 — Integrality Gap for Edge-Disjoint Triangle Packing

**Parent**: Erdős #1009 (Edge-Disjoint Triangles Beyond Turán, Győri 1988).

**OQ-03**: *What is the computational complexity of finding the maximum
edge-disjoint triangle packing? The fractional relaxation is polynomial, but
the integer version is NP-hard in general.*

## Summary

The general complexity classification (NP-hardness of integer triangle
packing — Holyer 1981) is a reduction-style CS theorem, not a single
formalizable Lean statement. What *is* formalizable, and is the structural
heart of the separation, is a **certified integrality gap**: an explicit graph
where the LP relaxation strictly exceeds the integer optimum, proving the two
problems genuinely differ.

We certify the canonical smallest witness, **K₄**:

| Quantity | Value | Theorem |
|----------|-------|---------|
| Integer optimum ν(K₄) | **1** | `integral_optimum : IsGreatest {n | ∃ F, IsPacking F ∧ F.card = n} 1` |
| Fractional optimum ν*(K₄) | **≥ 2** | `wHalf_isFracPacking`, `wHalf_value : fracValue wHalf = 2` |
| Gap | **2 > 1** | `integrality_gap`, `lp_relaxation_not_tight`, `gap_factor_ge_two` |

## Why K₄

- K₄ has exactly four triangles — the four 3-subsets of its vertices
  (`triangles_eq_all`).
- Any two distinct triangles share exactly one edge ⇒ never edge-disjoint
  (`no_two_edge_disjoint`), so an integer packing holds at most one triangle.
- Each of the 6 edges lies in exactly two triangles, so weight ½ on every
  triangle keeps each edge-load at ½+½ = 1 (feasible) while the objective
  totals 4·½ = 2.

## Session 2026-06-28 (Session 1) — FRESH

**Mode**: FRESH · **Outcome**: completed (VERIFIED, 0-axiom)

### What I did
- Built a decidable model of K₄'s triangles/edges on `Fin 4`
  (`triangles`, `edgesOf`, `allEdges`, `EdgeDisjoint` + Decidable instance).
- Integer side: `no_two_edge_disjoint` (by `decide`) ⇒ `packing_card_le_one`
  ⇒ `integral_optimum` (ν = 1, `IsGreatest`).
- Fractional side: `IsFracPacking`, `fracValue`, witness `wHalf ≡ ½`;
  edge-incidence count ≤ 2 (by `decide`) drives feasibility via
  `Finset.sum_filter` + `nsmul_eq_mul` + `linarith`; value computed via
  `Finset.sum_const` + `triangles_card`.
- Packaged the gap: `integrality_gap`, `lp_relaxation_not_tight`,
  `gap_factor_ge_two`.

### Verification
Host `lake env lean` exit 0 (Docker down). `#print axioms` on
`integrality_gap` / `integral_optimum` / `wHalf_isFracPacking` =
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no
`Lean.ofReduceBool` (only `decide`, no `native_decide`).

### Honest framing
This is **infrastructure / a certified textbook witness**, not a resolution of
the open complexity question. It formalizes the standard LP-vs-IP integrality
gap that explains *why* the integer packing problem is harder than its
polynomial fractional relaxation. New Lean content: a small decidable model of
fractional combinatorial packing (absent from Mathlib).

### Files
- `proofs/Proofs/Erdos1009OQ03.lean` (new, 191 lines, 13 thms, 9 defs, 0 axioms)
- `proofs/Proofs.lean` (registered)
- `src/data/research/problems/erdos-1009-oq-03.json`

### Next steps
- Generalize the gap to a growing family to lower-bound ν*−ν as n→∞.
- Formalize the LP dual (fractional triangle cover) and ν* = τ* on a small case.
