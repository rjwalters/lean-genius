# Knowledge: erdos-666-incomplete-01

## Overview

Gallery entry `erdos-666` (Erdős #666: C₆ in hypercube subgraphs). The conjecture
"every ε-dense subgraph of Qₙ contains C₆" is FALSE (Chung 1992; Brouwer–Dejter–
Thomassen 1993; Conder 1993). The Lean entry is complete (0 sorries) apart from a
single deep axiom.

## Gallery Proof Summary

- Sorries: 0. Axioms: 1 (`chung_no_threshold`).
- Tags: erdos, graph-theory, hypercube, cycles, extremal-graph-theory, disproved.

## Known Results / Structure

- `Hypercube n : SimpleGraph (Fin (2^n))`, `Adj x y := ∃ i, x.val ^^^ y.val = 2^i`
  (differ in exactly one bit ⇔ xor is a power of two; note the ∃ i is over all ℕ,
  the bound i<n is automatic since x⊕y < 2ⁿ).
- **Structural invariants (proved, researcher-3 2026-07-08):**
  - Qₙ is n-regular: `hypercube_degree`, `hypercube_isRegular`.
  - Edge count: `hypercube_card_edges : edgeFinset.card = hypercubeEdges n = n·2ⁿ⁻¹`.
  - Method: neighbours of x are exactly `{x ⊕ 2ⁱ : i<n}`; explicit injection
    `Fin n ↪ neighborFinset x`, then handshake lemma for the edge count.
- `chung_no_threshold : ¬ ConjectureAt (1/4)` — the ONE remaining axiom. Chung
  edge-partitions Qₙ (n≥3) into four C₆-free subgraphs; pigeonhole gives a
  (1/4)-dense C₆-free subgraph for every candidate threshold. Stated in negation
  form because the `∃ H, dense H ∧ ¬HasC6 H` form triggers a Mathlib v4.26
  elaborator stack overflow (see file header).

## Techniques that worked

- `Nat.xor_lt_two_pow (h1 : x<2ⁿ)(h2 : y<2ⁿ) : x^^^y < 2ⁿ` — well-definedness of bit-flip.
- xor left-cancellation without the deprecated `Nat.xor_cancel_left`: rewrite with
  `← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor`.
- `2ⁱ < 2ⁿ → i < n` via `(Nat.pow_lt_pow_iff_right (by norm_num)).mp`.
- `Nat.pow_right_injective (le_refl 2)` for `2ⁱ = 2ʲ → i = j`.
- `SimpleGraph.card_neighborFinset_eq_degree` (rfl), `Finset.card_image_of_injective`,
  `sum_degrees_eq_twice_card_edges` (handshake).
- Adjacency decidability supplied classically (`Classical.propDecidable`) — needed
  only so `degree`/`edgeFinset` are meaningful; counts as Classical.choice, not a
  new axiom.

## Blockers

- `chung_no_threshold`: needs Chung's explicit 4-partition construction (constant
  density for all n) — not in Mathlib, >1000 lines. BLOCKED.

## Key References

- Gallery: `src/data/proofs/erdos-666/`
- Lean source: `proofs/Proofs/Erdos666Problem.lean` (namespace `Erdos666`)
- Chung (1992) "Subgraphs of a hypercube containing no small even cycles"
