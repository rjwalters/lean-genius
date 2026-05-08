# Research State: birthday-problem-oq-03-oq-01-oq-02-oq-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-04-29T00:00:00Z
**Iteration**: 8

## Current Focus
Linkage layer between abstract `expectedTriples` (§2 definition) and the §5
asymptotic results: Session 8 adds `expectedTriples_3` and
`expectedTriples_threshold_tendsto`. Lemma C (axiom `p_no_triple_tendsto`)
remains the only assumption — ≈500 lines of method-of-factorial-moments
infrastructure, absent from Mathlib 4.26.

## Recently Merged / In Flight
- **Merged (PR #16150, Session 5, 2026-05-06)**: Restate axiom as Lemma C only;
  derive original `poisson_approx_birthday3` as a theorem.
- **Merged (PR #16730, Session 6, 2026-05-07)**: `p_no_triple_n3` (real-number
  form of n=3 base case) plus 4 Mathlib API drift fixes.
- **Open PR #16777 (Session 7)**: `p_no_triple_n3_tendsto` — n=3 fixed P→1
  corollary. Mergeable, build pending.
- **Open PR #16761 (Session 6 alt branch)**: `card_funs_shared_triple` — fixed
  triple cardinality lemma; conflicting at HEAD.

## Active Approach
Decomposition (Sessions 2–4):
- **Lemma A `lambda_tendsto` (PROVED, Session 4)**: `C(n_c(d),3)/d² → c³/6`.
- **Lemma B `exp_lambda_tendsto` (PROVED, Session 4)**: `exp(−λ(d)) → exp(−c³/6)`.
- **Lemma C `p_no_triple_tendsto` (axiom)**: `P_no_triple(n d, d) → exp(−c³/6)` —
  the only sublemma requiring new Mathlib infrastructure.

Session 8 (researcher-7) adds linkage:
- `expectedTriples_3 d : expectedTriples 3 d = 1/d²` — n=3 specialization.
- `expectedTriples_threshold_tendsto c hc : Tendsto (fun d => expectedTriples
  ⌊c·d^(2/3)⌋ d) atTop (nhds (c³/6))` — Lemma A in named form.

Both are short (≤5 lines) and provide a named-definition entry point so future
Bonferroni / method-of-moments work composes against `expectedTriples` rather
than the inlined ratio.

## Attempt Count
- Total attempts: 8 sessions
- Current approach: linkage / housekeeping (Session 8)
- Approaches tried: 1 (decomposition strategy from Session 2)

## Blockers
- Lemma C still requires method-of-factorial-moments → Poisson convergence,
  which is not in Mathlib 4.26. Either build it locally (~500 lines) or
  contribute upstream.

## Next Action
1. **Verify** Session 8 additions build cleanly (Docker — in flight).
2. **Open PR** for Session 8 once build passes.
3. **For Lemma C**: a coordinated multi-session push or a Mathlib contribution
   adding qualitative method-of-factorial-moments → Poisson convergence.
