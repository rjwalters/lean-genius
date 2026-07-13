# Session S6 — Incidence: the three Pascal points lie on `pascalProjLine`

**Researcher:** researcher-2
**Date:** 2026-06-27
**Phase:** ACT (OQ-03-OQ-02 core already COMPLETE + VERIFIED via #30806)
**Build:** Docker host back up (image `lean4-arm64:v4.26.0` present, disk 18%/55 GiB free).
`./proofs/scripts/docker-build.sh Proofs.PascalsHexagonOQ03` → **Build succeeded
(3070 jobs)**, only the two pre-existing open-counting `sorry`s remain
(`steiner_count_eq_20`, `kirkman_count_eq_60` = OQ-03-OQ-03/04, out of scope).

## Context

The OQ-03-OQ-02 well-definedness target (Pascal-line map descends from
`Equiv.Perm (Fin 6)` to the `hexagonalGroup ≅ D₆` quotient) was closed and
**machine-verified** by PR #30806 (`pascalProjLine_sameProjLine_of_mem` +
`…_of_quotient_eq` + `pascalLine_sameProjLine_rep`, full
`Subgroup.closure_induction`). The S5 parent-bitrot build blocker is resolved.

The well-definedness lemmas all establish that `pascalProjLine` is a
`D₆`-invariant *projective line vector* — but nothing yet said *which* line it is.

## What this session added (PART 4h, 0 sorry / 0 axiom, VERIFIED)

A small, self-contained incidence layer identifying `pascalProjLine hex` as the
genuine Pascal line — the common line of all three Pascal points
`P = AB ∩ DE`, `Q = BC ∩ EF`, `R = CD ∩ FA`.

Generic linear-algebra helpers (any `p q r : Fin 3 → ℝ`):
- `pointOnLine_cross_left  : pointOnLine p (crossProduct p q)` — `[p,p,q] = 0` (`ring`).
- `pointOnLine_cross_right : pointOnLine q (crossProduct p q)` — `[p,q,q] = 0` (`ring`).
- `pointOnLine_cross_of_collinear : collinear p q r → pointOnLine r (crossProduct p q)`.
  The scalar triple product `r · (p ×₃ q)` equals `det(p,q,r)` monomial-for-monomial
  (cyclic symmetry of the determinant), so `linear_combination h` closes it from the
  collinearity hypothesis `det(p,q,r) = 0`.

Pascal-specific corollaries (`{C : Conic} (hex : InscribedHexagon C)`):
- `pascalP_on_pascalProjLine`, `pascalQ_on_pascalProjLine` — unconditional.
- `pascalR_on_pascalProjLine` — the geometric content of **Pascal's theorem**:
  the R-incidence is exactly the collinearity `pascal_hexagon_theorem C hex`.
- `pascal_points_on_pascalProjLine :
     collinearOnLine (pascalP hex) (pascalQ hex) (pascalR hex) (pascalProjLine hex)`
  — packages all three; pins down `pascalProjLine` as *the* Pascal line, giving the
  descended quotient map `pascalLine` its intended geometric value.

## Honest significance

Modest but genuine. The deep content (closure-induction descent) was already done;
this is the natural finishing touch that connects the abstract invariant vector to
the classical Pascal line. The R-case is a one-line consequence of the parent's
Pascal theorem, but the packaged `collinearOnLine` statement is the clean reusable
form downstream Steiner/Kirkman incidence arguments will want. No new axioms, no new
sorries, fully machine-checked.

## Still open (out of scope for OQ-03-OQ-02)

- `steiner_count_eq_20` (OQ-03-OQ-03): 20 Steiner points — genuinely hard combinatorics
  (Conway–Ryba outer automorphism of S₆).
- `kirkman_count_eq_60` (OQ-03-OQ-04): 60 Kirkman points.
- Discharging the general-position hypothesis `hnd` (`∀ k, pascalProjLine
  (permuteHexagon hex k) ≠ 0`) from explicit distinctness of the six points — `hnd`
  is genuinely necessary (degenerate/coincident-point hexagons give a zero line), so
  this needs added distinctness hypotheses, not removal.
