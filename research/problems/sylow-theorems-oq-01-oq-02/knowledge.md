# Knowledge Base: sylow-theorems-oq-01-oq-02

## Problem Understanding

oq-01-oq-02 = openQuestions[2] of sylow-theorems-oq-01 ("Classification of Groups
of Order pq"): formalize the full squarefree-order classification — every group of
squarefree order n = p₁···pₖ is a semidirect product of cyclic groups, generalizing
the pq case.

## Deliverables (verified, 0-axiom)

`Proofs/SylowTheoremOQ01OQ02.lean` — 9 thm / 0 axioms / 0 sorries / 124 lines.
Routes entirely through Mathlib's `IsZGroup` theory.

- `isZGroup_of_squarefree_order` — IsZGroup.of_squarefree
- `sylow_isCyclic` — every Sylow subgroup cyclic
- `isSolvable_of_squarefree_order`
- `isCyclic_commutator` / `isCyclic_abelianization`
- `exponent_eq_card`
- `metacyclic_of_squarefree_order` — cyclic normal commutator + cyclic abelianization
- `semidirectProduct_of_squarefree_order` — G ≃* N ⋊ H, N,H cyclic, coprime orders
  (via `isZGroup_iff_exists_mulEquiv`) — THE classification
- `squarefree_card_of_pq` — recovers the parent two-prime case

## Gotchas

- `IsZGroup.isCyclic_commutator` / `exponent_eq_card` take `G` EXPLICIT.
- `IsCyclic (G ⧸ commutator G)` doesn't synthesize; use `Abelianization G` (defeq, has instance).
- `omit [..] in` must precede the docstring, not sit between docstring and theorem.

## Still open

- Explicit count of isomorphism classes via divisibility relations pᵢ ∣ (pⱼ−1).
