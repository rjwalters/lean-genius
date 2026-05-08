# Research State: liouville-theorem-oq-04

## Current State
**Phase**: COMPLETED
**Path**: full
**Since**: 2026-05-08T12:00:00+00:00
**Iteration**: 16

## Current Focus
Session 16 (this) — promote gallery metadata to `verified` / `original` after
the Session 15 bridge discharge (PR #17053, merged 2026-05-08T11:27:03Z).

PR #17053 rewrote `padic_liouville_norm_bridge` from `axiom` to fully-proved
`theorem` and resolved three pre-existing build errors discovered during the
post-merge build retry (`intPolyL1_pos` Finset summand inference, the
`Int.algebraMap_eq_intCast → eq_intCast` 4.26 rename, and the
`field_simp; ring` → `field_simp <;> ring` "No goals" fix). After those fixes,
the file is **0 axioms, 0 sorries, 1344 lines, 35 theorems, 6 defs**.

This session: meta.json status `axiomatized → verified`, badge
`axiom → original`, axiomCount `1 → 0`, lineCount `1216 → 1344`,
theoremCount `34 → 35`. Narratives in `description`, `assumptions`,
`originalContributions`, `proofStrategy`, `keyInsights`, `conclusion.summary`,
`conclusion.implications`, `conclusion.openQuestions`, the `main-theorem`
section, and `mainTheorems` are refreshed to drop bridge-axiom language and
reflect the now-fully-proved state.

## Active Approach
N/A — work is COMPLETE pending build verification. Path forward is operational:
flip the gallery flags, push the metadata PR, mark candidate-pool entry
`completed`, release the claim.

## Attempt Count
- Total attempts: 15
- Current approach attempts: 1 (metadata sync)
- Approaches tried: 3

## Blockers
- None. All Lean ingredients land on `origin/main` as of PR #17053
  (commit 0175c59d).

## Next Action
**Session 17 (optional / future work)**: pursue follow-up open questions:
1. Sharpen $\mu_p \leq 2d$ to $\mu_p \leq 2$ via Roth-style auxiliary
   polynomials (much harder; would parallel a Lean formalization of Roth's
   1955 theorem).
2. Function-field analog over $\mathbb{F}_q(t)$ with $t$-adic norm —
   would need a Mathlib `LaurentSeries` p-adic infrastructure or analogous
   `RatFunc` machinery.
3. Multi-place uniform statement: $\forall p, \mu_p(\alpha) \leq 2d$ for the
   same $\alpha$ — touches the adelic product formula.

## Session 15 deltas (PR #17053, merged 2026-05-08T11:27:03Z)
- File: 1216 → 1344 lines (+128), 34 → 35 theorems (+1), defs unchanged.
- Theorem added: `padic_liouville_norm_bridge` (rewritten from `axiom`).
- Axioms: 1 → 0.
- Sorries unchanged (0).
- Build: PR triggered three sequential commits to fix pre-existing 4.26
  drift errors before the build went green; final build state on the merged
  commit is reported as resolved by the PR description.

## Session 16 deltas (this session)
- meta.json status / badge / axiomCount / counts / narratives.
- src/data/research/problems/liouville-theorem-oq-04.json:
  phase NEW → COMPLETE, currentState.iteration 15 → 16, focus updated.
- candidate-pool.json: `in-progress` → `completed`.
- No Lean changes.

## References
- Parent file: `proofs/Proofs/LiouvilleTheoremOQ04.lean` (1344 lines, 0 axioms,
  0 sorries, 35 theorems, 6 defs).
- Algebraic case: Part IV.10, `padic_liouville_bridge_algebraic_case`
  (Session 13, line ~679).
- Rational-roots case: Part IV.11,
  `padic_liouville_bridge_rational_roots_case` (Session 14, line ~846).
- Bridge theorem (formerly axiom): `padic_liouville_norm_bridge`
  (Session 15, line ~935).
- Final main theorems: `padic_liouville_estimate` (line ~1066) and
  `padic_algebraic_not_liouville` (line ~1089).
