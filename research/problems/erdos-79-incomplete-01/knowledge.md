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

## Session 2026-07-08 (researcher-4) — minimal non-linearity is an isomorphism invariant

**Mode**: FRESH (continuation) · **Outcome**: progress (structural; 0 sorries; no new axioms)

Extended the OQ01 companion `Erdos79Incomplete01OQ01.lean`. The prior session
derived heredity + size-linearity iso-invariance from the two atomic Ramsey
properties. This session closes the natural structural gap: the ENTIRE predicate
`isMinimallyNonLinear` is an isomorphism invariant.

New (0 sorry, NO new axioms):
- `isRamseySizeSuperlinear_congr` — superlinearity transports across iso
  (negation of the iso-invariant size-linearity, via `e.symm`).
- `comapIso` / `comap_self` / `comap_properSubgraph` — subgraph transport:
  a proper subgraph `H' ⊊ G'` pulls back along `e : G ≃g G'` to a proper
  subgraph `comap ⇑e H' ⊊ G`, isomorphic to `H'` (bijection `e`, adjacency by
  `comap` definition). Monotonicity via `e.map_rel_iff`; properness via
  `congrArg` of the graph equality evaluated at preimages `e.symm`.
- `isMinimallyNonLinear_congr` — `G ≃g G' → isMinimallyNonLinear G →
  isMinimallyNonLinear G'`. Superlinear clause via `isRamseySizeSuperlinear_congr`;
  subgraph clause by pulling each `H' ⊊ G'` back to `comap ⇑e H' ⊊ G` (linear by
  hypothesis) then pushing linearity forward across `comapIso e H'`.
- `minimalNonLinearGraphs_iso_closed` — restatement on the parent's set.

**Axiom basis** (`#print axioms isMinimallyNonLinear_congr`):
`[propext, Classical.choice, Quot.sound, ramseyNumber_congr_left]` — only the
single CONGRUENCE axiom; monotonicity `ramseyNumber_mono_left` is not even
needed. So the well-posedness of Erdős #79's count of minimally non-linear
graphs *up to isomorphism* (`minimalNonLinearGraphs.Infinite`) reduces to
exactly one atomic fact: the Ramsey number depends only on the isomorphism type
of its first argument. Significant because the whole gallery formalisation works
with concrete graphs on the fixed vertex set `ℕ`.

**Honest scope**: no new axioms, no change to the assumption count; purely a
structural strengthening. Elementary scaffold now at terminus — the remaining
OPEN content (single-diamond size-linearity `R(K₄−e,H)=O(e(H))` and K₄
superlinearity) is genuine Ramsey theory beyond Mathlib.

**Files**: `proofs/Proofs/Erdos79Incomplete01OQ01.lean` (181→278 lines; +5
theorems, +1 def, +0 axioms). VERIFIED docker exit 0 ([7745/7745], 3.6s, first
try; `#print axioms` captured in-file).
