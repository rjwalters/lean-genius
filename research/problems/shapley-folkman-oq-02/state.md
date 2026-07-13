# Research State: shapley-folkman-oq-02

## Current State
**Phase**: ORIENT → PRE-ACT (scaffold ready)
**Path**: full
**Since**: 2026-06-14
**Iteration**: 3

## Current Focus
Verification blackout STILL in force (iteration 3, 2026-06-26): Docker daemon
flapping + containerd "unexpected EOF" crash (exit 125); Aristotle MCP returns 404.
No gallery `.lean` committed. This iteration produced a **name-checked, ACT-ready Lean
scaffold** (`draft-ShapleyFolkmanOQ02.lean`, research dir only) and verified the bearer
API against actual source, correcting three points that would otherwise have broken the
eventual build (see knowledge.md "Session 3").

## Active Approach
Approach 1: build the metric upgrade on the parent's `sum_close_to_convexHull`. Scaffold
splits it into: `rad` def + `rad_le_diam`; `exists_nearby_point` (Carathéodory + nearest
point); `hausdorff_bound_linear` (routine `finrank·rad` triangle bound — first verified
target); `cassels_starr_aggregation` (the √n crux — open core); `shapley_folkman_starr`
(packaging via `hausdorffDist_le_of_mem_dist`).

## Attempt Count
- Total attempts: 2 (ORIENT survey + numerical verification; then API-verified scaffold)
- Current approach attempts: 2
- Approaches tried: 1

## Blockers
- Verification blackout persists (2026-06-26): Docker containerd EOF crash + Aristotle
  404. Cannot compile or prove-check any Lean. Scaffold statements are name-checked
  against source but the proofs are UNVERIFIED.
- The √n constant is NOT reachable by triangle/Cauchy–Schwarz (see knowledge.md
  Correction B); it requires the Cassels–Starr convex-geometry argument — the genuine
  open core.

## Next Action
ACT (when a backend returns), easiest → hardest:
1. `rad_nonneg` / `rad_le_diam` / `exists_nearby_point`.
2. `hausdorff_bound_linear` — land the **`finrank·rad` (triangle) Hausdorff bound** as a
   verified gallery entry first (honest milestone; no Cassels needed).
3. `shapley_folkman_starr` packaging.
4. `cassels_starr_aggregation` — the √n crux (open core).
Do NOT ship the √n statement as verified until step 4 is genuinely proved. Submit the
provable supporting lemmas (steps 1–3) to Aristotle the moment it is back up.
