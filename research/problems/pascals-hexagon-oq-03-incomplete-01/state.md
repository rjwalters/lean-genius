# State: pascals-hexagon-oq-03-incomplete-01

## Current Phase: ACT
## Iteration: 2

## Status
S2 (researcher-6, 2026-06-27): implemented the **OQ-03-OQ-02** well-definedness
backbone proposed by S1. Added PART 4c to `PascalsHexagonOQ03.lean` — the six
exact generator-action identities — and made `pascalLine` total. Shipped as
**PR #30630** (branch `research/pascals-hexagon-oq03-oq02-generator-action`).

**Local build verification BLOCKED** (host Data volume 100% full, 5.7 GiB free;
`lean4-arm64` Docker image absent → `docker-build.sh` failed at image build with
a containerd I/O error; direct `lake build` prohibited). Proofs are hand-verified
and reuse tactic patterns already compiled in the parent file; PR is flagged for
build-gating before merge.

## What was established (now machine-targeted, build pending)
- `pascalP/Q/R_permuteHexagon_hexRot` — `(P,Q,R) ↦ (Q, R, -P)`. P/Q by index
  reduction (`decide`) + `rfl`; R by one `cross_anticomm`.
- `pascalP/Q/R_permuteHexagon_hexRev` — `(P,Q,R) ↦ (-Q, -P, R)`. All three sign
  cases proved by coordinate expansion (`cross_apply` + `ring`) — the three S1
  `sorry` sketches are now real proofs.
- `pascalLine` total via `lbl.out'` (`Quotient.out'`): the blocking
  definition-`sorry` is gone; `SteinerPoint`/`KirkmanPoint` typecheck.

## Next Action
1. Build-verify PR #30630 once the host has disk/Docker (`docker-build.sh
   Proofs.PascalsHexagonOQ03`). Likely-fragile spots if it fails: numeral
   reduction `hexVertex hex (n : Fin 6) ≡ hex.<field>` (the `rfl`/`show` steps),
   and the `cons_val` simp set on nested cross products.
2. Promote set-invariance to a literal `ProjLine` equality: prove `P×Q ∝ Q×R`
   for collinear, pairwise-independent `P,Q,R` (`Q×R = -α(P×Q)` when
   `R = αP + βQ`), with a nonzero-scalar line-equivalence + nondegeneracy
   hypothesis. This closes OQ-03-OQ-02 at the quotient level.

## Out of scope
`steiner_count_eq_20`, `kirkman_count_eq_60` (OQ-03-OQ-03/04) — genuinely open
(Conway–Ryba concurrence combinatorics).
