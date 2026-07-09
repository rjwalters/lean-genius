# Knowledge Base: erdos-79-incomplete-01

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]

---

## Session 2026-07-08 (researcher-4) — grounding heredity + iso-invariance in atomic Ramsey properties

**Mode**: FRESH · **Outcome**: progress (structural; 0 sorries)

New companion `Erdos79Incomplete01OQ01.lean`. The parent treats size-linearity
heredity as a standalone axiom `ramsey_linear_hereditary`, and the sibling
companion's sharpest reduction `K4_subgraphs_linear_of_single` carries an
explicit iso-invariance hypothesis `hcongr` ("cannot be derived over the opaque
ramseyNumber"). This session shows both are *consequences* of the two atomic,
textbook-true structural properties of the primitive `ramseyNumber`:

- `ramseyNumber_mono_left`  : `G ≤ G' → R(G,K) ≤ R(G',K)`  (axiom)
- `ramseyNumber_congr_left` : `(G ≃g G') → R(G,K) = R(G',K)`  (axiom)

From these we DERIVE (0 sorry):
- `isRamseySizeLinear_hereditary` — heredity (same constant C via
  `R(H,K) ≤ R(G,K) ≤ C·e(K)`); recovers the parent axiom as a theorem.
- `isRamseySizeLinear_congr` — iso-invariance (same C; `R(G',K)=R(G,K)`);
  removes the companion's `hcongr` hypothesis.
- `K4_subgraphs_linear_of_edgeDeleted'` / `_of_single'` — the companion's
  6→1 reduction, re-derived using the derived heredity/iso-invariance.
- `K4_is_minimal_from_single_diamond` — K₄ minimal-non-linearity from a SINGLE
  diamond `K₄−{0,1}`. `#print axioms` confirms the basis is exactly
  `[propext, Classical.choice, Quot.sound, K4_not_linear,
    ramseyNumber_congr_left, ramseyNumber_mono_left]` — NO dependence on
  `ramsey_linear_hereditary` or `K4_subgraphs_linear`.

**Honest scope**: this does NOT reduce the assumption count (the two Ramsey
properties are themselves axioms over the opaque `ramseyNumber`; the real
content `R(K₄−e,H)=O(e(H))` needs Ramsey theory beyond Mathlib). The value is
structural: two meta-assumptions about the derived predicate become theorems
grounded in canonical primitive-level facts. meta.axiomCount 1→3 (two new
atomic axiom declarations), status stays `axiomatized`/`axiom`.

**Files**: `proofs/Proofs/Erdos79Incomplete01OQ01.lean` (new, 174 lines,
2 axioms / 6 theorems / 0 sorries), `src/data/proofs/erdos-79-incomplete-01/meta.json`
(register additionalFile + axiomCount).

VERIFIED docker exit 0 ([7745/7745], 3.6–3.8s, first try; `#print axioms`
output captured in-file).
