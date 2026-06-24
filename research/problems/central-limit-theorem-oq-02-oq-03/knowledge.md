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

## Still open
- The actual oq-02-oq-03 question (undefined) and parent's deep CLT axiom.
