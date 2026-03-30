# Knowledge Base: furstenberg-correspondence-oq-01

Shift Dynamics on Cantor Space: Toward Furstenberg Correspondence

---

## Problem Understanding

OQ-01 asks: Can the Furstenberg correspondence construction be fully formalized using
Mathlib's ultrafilter/compactness tools? The parent proof (FurstenbergCorrespondence.lean)
axiomatizes the correspondence principle. This work builds the infrastructure toward
eliminating that axiom.

The correspondence translates positive upper density of A ⊆ ℕ into a measure-preserving
dynamical system on Cantor space Ω = {0,1}^ℕ where μ(B₀) ≥ d*(A).

---

## Insights

- `continuous_pi` + `continuous_apply` gives shift continuity in one line from Mathlib
- Cylinder sets are clopen because Bool has discrete topology — proved via `isOpen_eq_of_isOpen_singleton`
- The k-fold return property is the key bridge: ALL combinatorial content flows through it
  `1_A ∈ ⋂_{i<k} T^{-id}(B₀) ↔ ∀ i < k, id ∈ A`
- Compactness of Cantor space follows from `Pi.compactSpace` (Tychonoff)
- Metrizability follows from `inferInstance` (countable product of metrizable spaces)

**Main gap for full correspondence**: weak-* sequential compactness for probability
measures on compact metrizable spaces — not yet in Mathlib.

---

## Built Items (Session 1, 2026-03-30)

- `proofs/Proofs/FurstenbergCorrespondenceOQ01.lean` (250 lines, 0 axioms, 0 sorries)
- 15 theorems proved, 5 definitions, full gallery integration
- Key results: shift_continuous, cylinder_isClopen, indicator_in_kfold_return,
  orbit_indicator_hits, CompactSpace CantorSpace

---

## Dead Ends

(None yet — first session)
