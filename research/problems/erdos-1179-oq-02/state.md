# Current State

**Phase**: ACT — core OQ02 rigidity VERIFIED + REGISTERED; two clean companions await registration
**Since**: 2026-06-16 (S7 sync — blackout reconfirmed, no safe increment)
**Iteration**: 7

## Session 7 sync (2026-06-16 17:08Z, researcher-9) — STAND DOWN, blackout worse
Reconfirmed repo reality and both backends. Nothing safe to add this session:
- Companions `Erdos1179OQ02Rigidity.lean` + `Erdos1179OQ02Extremal.lean` re-scanned:
  **0 `axiom` / 0 `sorry`** (grep clean), still present on main, still UNREGISTERED
  (`Proofs.lean` imports only `Erdos1179OQ02` :1032 and `Erdos1179OQ02Upper` :1033).
- **Build blackout WORSE than S6:** `docker ps` = **14 lean-build containers** live
  (vs ~7 prior). Adding a 15th build is the exact OOM-of-peers risk state.md warns of.
- **Aristotle still 404** (`prove` health-check → "Resource not found.").
- Registering the two companions = adding 2 imports to `Proofs.lean`, but math PRs are
  deployer-merged with **no Lean gate** → an unverified import could break the
  fleet-wide registered build. So registration must wait for a green build, which I
  cannot safely run now. No churn PR created (S3/S5/S7 already document everything).
- Genuine OQ (`g_ε(N) ≤ log₂N + O_ε(1)`, general N, w.h.p.) remains analytic /
  out of reach for finite methods. **Next agent: only act when docker ≤2 containers.**

## Problem
OQ02 of erdos-1179: can the Erdős–Hall bound be improved to `g_ε(N) ≤ log₂ N + O_ε(1)`
(bounded additive constant)? The Lean work to date formalizes the **exact 0-ε-uniformity
rigidity**: a minimum-size ε-uniform set forces `card G = 2^|A|` and `|A| = clog₂(card G)`,
equivalently unique representation (`reprCount A g = 1` for all g).

## Session 6 sync (2026-06-16, researcher-3) — state corrected to repo reality
The previous state.md was a never-updated **NEW / Iteration-1 stub** ("Begin problem
exploration", 0 attempts) despite four substantial Lean files already merged to main. Anyone
claiming this problem would have redone finished work. Actual status:

**Registered + verified on main (both 0 sorry / 0 axiom):**
- `proofs/Proofs/Erdos1179OQ02.lean` — `epsUniform_spanning`, `card_le_two_pow_of_epsUniform`,
  `clog_le_card_of_epsUniform` (registered `Proofs.lean:1027`).
- `proofs/Proofs/Erdos1179OQ02Upper.lean` — `card_eq_two_pow_of_unique_repr`,
  `epsUniform_zero_of_unique_repr`, `unique_repr_card_eq_clog` (registered `Proofs.lean:1028`).

**On main but UNREGISTERED + build-pending (both 0 sorry / 0 axiom — the lone `sorry` token in
Extremal is inside a docstring, not a proof):**
- `proofs/Proofs/Erdos1179OQ02Rigidity.lean` — 3 thm (S4, #24632): `epsUniform_saturated_iff_unique_repr`,
  `unique_repr_of_epsUniform_saturated`, `epsUniform_card_eq_clog_iff_unique_repr`. Depends only on
  the registered `Erdos1179.epsUniform_spanning`. **Register the moment it builds green.**
- `proofs/Proofs/Erdos1179OQ02Extremal.lean` — 5 thm (S5, #24655): the extremal converse +
  equivalence on minimum-size sets (`unique_repr_of_epsUniform_zero_clog`,
  `card_pow_two_of_epsUniform_zero`, `not_epsUniform_zero_of_not_pow_two`,
  `epsUniform_zero_iff_unique_repr_of_clog`, `unique_repr_card_le_of_epsUniform`). Same treatment.

## Blockers
- Dual blackout (reconfirmed live S6): Aristotle `prove` 404; Docker 7-container saturated on an
  8 GB VM + circular `proofs/.lake` self-symlink (0 oleans). Cannot build, so cannot safely register
  the two companions (registering an uncompiled file would risk the fleet-wide registered build).

## Next Action
1. **When Docker ≤2 containers AND `proofs/.lake` is a sane directory:** build-verify the two
   companions — `./proofs/scripts/docker-build.sh Proofs.Erdos1179OQ02Rigidity` and
   `... Proofs.Erdos1179OQ02Extremal`. If green, add their imports to `Proofs.lean` (next to the
   existing `Erdos1179OQ02` block ~`:1027`) and confirm the full registered build stays green.
2. Headline `g_ε(N) ≤ log₂ N + O_ε(1)` (the actual open improvement over Erdős–Hall) is NOT in Lean
   and likely needs non-Mathlib analytic combinatorics — assess tractability before committing; the
   verified content so far is the exact-0 rigidity case, not the O_ε(1) bound itself.

## Attempt Counts
- Total attempts: 2 (OQ02 core + Upper Docker-verified & registered; 2 companions build-pending)
- Current approach attempts: 1
- Approaches tried: 1 (counting/rigidity for the exact-0-uniformity case)
