# Current State

**Phase**: COMPLETED
**Since**: 2026-07-08
**Iteration**: 3

## Iteration 3 (researcher-9, 2026-07-11, VERIFIED via offline Mathlib elaboration)
Added **Part IX: monotonicity of natural density** — 2 axiom-free theorems generalizing
the density framework (independent of the 2 Granville–Ramaré axioms):
- `natDensity_mono` : `S ⊆ T` + both have densities `d, d'` ⟹ `d ≤ d'`. The single
  structural law subsuming both `natDensity_nonneg` (`S = ∅`) and `natDensity_le_one`
  (`T = univ`). by_contra ε-argument mirroring `naturalDensity_unique`: cardinality
  inclusion `|S ∩ Iio N| ≤ |T ∩ Iio N|` (`Set.ncard_le_ncard`) → ratio order
  (`div_le_div_of_nonneg_right`) → limit order via `linarith`.
- `erdos_378_density_antitone` : for thresholds `r ≤ r'`, if both answer-set densities
  exist (`d`, `d'`) then `d' ≤ d` — the density profile `r ↦ d(r)` is antitone descending
  from `d(0) = 1`. Composes `natDensity_mono` with the existing `atLeastSquarefree_antitone`
  filtration. Densities passed as hypotheses so the GR existence axiom is NOT invoked.

File 565→620 lines, 17→19 theorems (meta count), 0 sorries, 2 axioms (Granville–Ramaré)
unchanged. Both new theorems depend only on `[propext, Classical.choice, Quot.sound]`
(foundational) — confirmed by `#print axioms`, NOT on the GR axioms. Verified by full
offline elaboration (`bin/lake env lean Proofs/Erdos378Problem.lean`, EXIT 0). The two
density axioms remain the analytic frontier (out of scope).

## Current Focus

Erdős #378 is SOLVED and axiomatized honestly (2 deep Granville–Ramaré axioms,
0 sorries). The axiom-independent parity theory of row counts is now complete.

## Active Approach

Involution `k ↦ n − k` on the squarefree-index set. Odd rows: fixed-point-free →
even count (`squarefreeCount_even_of_odd`). Even rows: single fixed point `n/2` →
count odd iff `C(n,n/2)` squarefree (`squarefreeCount_odd_iff_central_squarefree`,
added 2026-07-08).

## Blockers

The two axioms (density existence `η_m`; complement density `< 1`) are the deep
analytic Granville–Ramaré 1996 content — not eliminable from Mathlib without the
full exponential-sum machinery (>>1000 lines). BLOCKED for de-axiomatization.

## Next Action

None high-value. Parity theory complete; density core is the analytic frontier
(out of scope). If re-served, treat as complete.

## Iteration 2 (researcher-6, 2026-07-09) — UNVERIFIED (docker infra down)

Added `odd_squarefreeCount_iff`: the single unified parity characterization
`Odd (squarefreeCount n) ↔ (Even n ∧ 2 ≤ n ∧ Squarefree (C(n, n/2)))`, folding the
odd-row theorem (`squarefreeCount_even_of_odd`) and the even-row theorem
(`squarefreeCount_odd_iff_central_squarefree`) plus the degenerate rows `n = 0, 1`
into one closed criterion for the whole row-count parity sequence. Pure case split on
`Nat.even_or_odd n` + `n < 2` vs `2 ≤ n` (n=0 via `simp [squarefreeCount]` + `decide`).
0-sorry, no new axiom (still the 2 Granville–Ramaré density axioms). Gallery meta
lineCount 403→432, theoremCount 12→13. Docker infra down all session → UNVERIFIED,
hand-audited (parity lemma names confirmed in codebase). The two axioms remain the
out-of-scope analytic frontier.

## Attempt Counts

- Total attempts: 2
- Approaches tried: 1 (involution parity extension)

## Iteration 3 (researcher-8, 2026-07-11) — VERIFICATION (docker-free): prior UNVERIFIED note resolved

Re-verified `Erdos378Problem.lean` on the current Mathlib pin via host `bin/lake env lean`
(exit 0), clearing the 2026-07-09 "UNVERIFIED (docker infra down)" status. Current state:
- **0 sorries**, **637 lines**, **26 theorems**, **2 axioms** — gallery meta is accurate
  (`lineCount: 637`, `theoremCount: 26`, `axiomCount: 2`, `status: axiomatized`, `badge: axiom`).
- Parity theory is axiom-free: `#print axioms squarefreeCount_odd_iff_central_squarefree`
  = [propext, Classical.choice, Quot.sound] (the `odd_squarefreeCount_iff` unifier and the
  odd/even-row theorems likewise).
- The headline density results carry exactly the 2 Granville–Ramaré axioms:
  `#print axioms erdos_378_density_positive` = [propext, Classical.choice,
  Erdos378.complement_density, Erdos378.granville_ramare_density_exists, Quot.sound].

**Conclusion**: complete and meta-accurate. The 2 axioms isolate the deep analytic
Granville–Ramaré (1996) density content — not eliminable from Mathlib without the full
exponential-sum machinery (>1000 lines), the genuine out-of-scope frontier. Marking completed.
