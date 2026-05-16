# Problem: Anning–Erdős Finiteness (slug `erdos-100-oq-01-wip-01`)

## Statement

### Plain Language
For any positive integer `d`, a non-collinear point set in the plane whose pairwise distances are all integers ≤ `d` has at most `2d² + 2` points.

This slug-name in the candidate pool ("Distance Set Diameter: Guth-Katz Linear vs Log Gap (WIP)") reflects the broader research arc this gallery proof contributes to — the gap between the linear lower bound on diameter and the Guth–Katz log/log bound on distinct-distance counts. The Anning–Erdős finiteness theorem (proved here) is a finiteness building block for that arc.

### Formal Statement

The main public theorem (per gallery `meta.json`):

```lean
theorem anning_erdos_finiteness
    (d : ℕ) (hd : 0 < d) (S : Finset (ℝ × ℝ))
    (hS_int_dist : ∀ P ∈ S, ∀ Q ∈ S, P ≠ Q → ∃ k : ℕ, k ≤ d ∧ dist P Q = k)
    (hS_noncollinear : ∃ P₁ ∈ S, ∃ P₂ ∈ S, ∃ P₃ ∈ S,
       P₁ ≠ P₂ ∧ P₁ ≠ P₃ ∧ P₂ ≠ P₃ ∧ ¬Collinear ℝ {P₁, P₂, P₃}) :
    S.card ≤ 2 * d ^ 2 + 2
```

(Lean source: `proofs/Proofs/Erdos100OQ01WIP01.lean:256`; full Lean signature matches the gallery `meta.json` and uses the slug-local `namespace Erdos100OQ01WIP01`.)

## Classification

```yaml
tier: B
significance: 7
tractability: 4
tags:
  - discrete-geometry
  - erdos
  - distance-sets
  - guth-katz
  - anning-erdos
  - mathlib-gap
```

**Significance**: 7/10 — closes a parent-file (`Erdos100OQ01.lean`) sorry by supplying the finiteness component of the Anning–Erdős → Erdős distance-set chain. Anning–Erdős is the classical 1945 finiteness result and the standard reference for any integer-distance-set bound.

**Tractability**: 4/10 — proved (gallery `meta.status = verified`, 0 sorries, 0 axioms, 274 LOC). The "4" in tractability reflects the parent slug's broader open question (Guth–Katz log/log gap), not this proven sub-result.

## Why This Matters

1. **Closes a parent-file sorry**: the proof of `anning_erdos_finiteness` in this slug discharges the `anning_erdos_finiteness` sorry that previously appeared in the parent file `proofs/Proofs/Erdos100OQ01.lean`, unblocking that parent's full machine-verification (modulo a separate `piepmeyer_upper` sorry that remains open in the parent).
2. **Mathlib gap**: Mathlib v4.26.0 has no `Anning_Erdos_finiteness` lemma; this slug supplies the construction (`quadratic_at_most_two_roots`, `three_pts_two_circles_contra`, `int_dist_card_le`, `anning_erdos_finiteness`) as an "original" gallery contribution.
3. **Building block for distance-set diameter research**: the `2d² + 2` bound is the starting point for the broader Erdős → Guth–Katz research arc on distance-set diameters and Solymosi–de Zeeuw `Ω(n^{4/3})` lower bound.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `Erdos100OQ01.lean` (parent) | Anning–Erdős sorry discharged by this slug; `piepmeyer_upper` sorry remains open |
| Solymosi–de Zeeuw 2010 (cited in `meta.references`) | `Ω(n^{4/3})` diameter bound via Szemerédi–Trotter |

## References (from gallery `meta.references`)

- Anning, N. H. and Erdős, P. (1945). "Integral distances." *Bulletin of the American Mathematical Society* 51(8):598–600.
- Erdős, P. (1946). "On sets of distances of n points." *American Mathematical Monthly* 53:248–250. — Companion paper posing several still-open distance set problems.
- Solymosi, J. and de Zeeuw, F. (2010). "On a question of Erdős and Ulam." *Discrete & Computational Geometry* 43(2):393–401. — Proves diameter `Ω(n^{4/3})` for non-collinear `n`-point integer distance sets via Szemerédi–Trotter.

## Status (as of S2 STATE-SYNC, 2026-05-16)

**COMPLETED**. Gallery `meta.status = verified`, `meta.badge = original`, 0 sorries, 0 axioms, 4 theorems, 274 LOC. Open follow-up questions Q1–Q3 documented in `state.md` and gallery `meta.openQuestions` remain genuinely open but are out of scope of this slug.
