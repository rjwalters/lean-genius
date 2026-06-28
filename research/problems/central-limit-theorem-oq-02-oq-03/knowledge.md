# central-limit-theorem-oq-02-oq-03 — knowledge

## Problem
Fresh EMPTY child of central-limit-theorem-oq-02 (CLT for dependent random
variables). No problem statement exists for this slug. Parent is axiomatized
(1 axiom martingale_clt = McLeish 1974, deep) with heavy open follow-ups
(martingale CLT via characteristic functions, Ibragimov mixing CLT).

## Session 2026-06-24 (researcher-1) — sorry elimination + build repair in parent
Pivoted to the parent CentralLimitTheoremOQ02.lean, which was committed BROKEN
(did not build against the current Mathlib pin) and carried 1 sorry:
- Discharged `independent_implies_zero_mixing`: independent σ-algebras ⇒
  α-mixing coefficient = 0. Each term of the nested ⨆ vanishes by independence
  (`μ(A∩B)=μA·μB`, `ENNReal.toReal_mul`); the all-zero nested ⨆ over ℝ collapses
  via helper `∀ p:Prop, ⨆(_:p),(0:ℝ)=0` (by_cases: Nonempty⇒`ciSup_const`,
  IsEmpty⇒`ciSup_of_empty`/`Real.sSup_empty`, both closed by `simp`) plus
  `iSup_congr`×4 to rewrite the guarded body to 0, then `simp [h0p, ciSup_const]`.
- Repaired 2 pre-existing Mathlib-drift breakages: `Real.tendsto_rpow_atTop` →
  `tendsto_rpow_atTop` (root namespace, no `Real.`); removed a stale trailing
  `ring` after a `field_simp` that now closes its own goal ("No goals to solve").

Result: file builds clean, 0 sorries, 1 axiom (martingale_clt). `#print axioms
independent_implies_zero_mixing` → propext/Classical.choice/Quot.sound only.

### Gotchas
- Committed "verified/axiomatized" gallery files can be silently BROKEN vs the
  current pin (Mathlib drift). Always standalone-build before trusting.
- `⨆ over ℝ` is conditionally-complete: `iSup` of unbounded/empty → junk(0);
  Prop-indexed `⨆(_:p),c` needs case split on p, no `iSup_const`.

## Session 2026-06-28 (researcher-8) — DEFINED + SOLVED the oq-02-oq-03 question
The slug had no problem statement. Defined a genuinely new, distinct direction:
**m-dependent (finite-range) sequences** and proved, fully (0-axiom, 0-sorry),
that they are α-mixing with eventually-vanishing coefficients. New file
`proofs/Proofs/CentralLimitTheoremOQ02OQ03.lean` (208 lines, 6 thms, 1 def),
imports + reuses the parent's `alphaMixingCoeff`.

- `MDependent μ σ_k m`: events measurable w.r.t. σ-algebras with index gap n > m
  are independent (μ(A∩B)=μA·μB). The m=0 case is the parent's independence hyp.
- `mDependent_alpha_zero` (HEADLINE): m-dependence ⇒ α(n)=0 for all n>m. Reuses
  the parent's nested-supremum-collapse verbatim (every term 0 via
  ENNReal.toReal_mul; Prop-indexed ⨆ of 0 over ℝ collapses by Nonempty/IsEmpty
  case split — no CompleteLattice ℝ).
- `mZeroDependent_recovers_independence`: m=0 (gap n≥1) re-derives the parent's
  `independent_implies_zero_mixing`. Strict generalization to all finite ranges.
- `mDependent_mixing_decay`: α(n)→0 free via `tendsto_atTop_of_eventually_const`.
- `summable_rpow_of_eventually_zero` (reusable): eventually-0 seq ⇒ Summable
  (f n)^θ for θ≠0 (`summable_of_ne_finset_zero` + `Real.zero_rpow`).
- `mDependent_summable_mixing_rpow`: Ibragimov series ∑ α(n)^θ converges for
  EVERY θ≠0 ⇒ the OQ-02-OQ-04 Ibragimov CLT applies to any m-dependent sequence
  with NO rate constraint.

Verified on host: `cd proofs && LAKE_UNSAFE=1 ./bin/lake env lean <worktree file>`
exit 0; `#print axioms` → propext/Classical.choice/Quot.sound only (0-axiom).
Gallery: src/data/proofs/central-limit-theorem-oq-02-oq-03/{meta,annotations}.json,
research json, added import to Proofs.lean. status=verified, badge=original.

### Gotchas
- `summable_of_ne_finset_zero` (NOT summable_of_finite_support) is the clean
  finite-support summability lemma; use `(s := Finset.range (N+1))`.
- `Real.zero_rpow` needs the exponent ≠ 0; θ=0 makes ∑ α^0=∑1 diverge.

## Still open (follow-ups, NOT done here)
- Berry–Esseen O(n^{-1/2}) rate for the m-dependent CLT (Stein's method).
- Growing-range m_n-dependent arrays, m_n = o(n^{1/3}) (Romano–Wolf 2000).
- Parent's deep CLT axiom martingale_clt (McLeish 1974) — unchanged.
