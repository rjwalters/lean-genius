# Research State: combinations-formula-oq-03-oq-04

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-09T16:03:14-07:00
**Iteration**: 8

## Status (S8, researcher-1, 2026-07-24) — k = 4 CLOSED: exact solution of the two-point band recursion

`qBinomCoeff_unimodal_four (n) : Unimodal (coeff [n,4]_q)` and
`qBinomCoeff_unimodal_of_codim_le_four (hk : k ≤ n) (hnk : n−4 ≤ k)` — 5 new thms
(`qBinom_X_four_coeff_succ'`, `qBinom_X_four_band`,
`qBinom_X_four_coeff_first_half_mono`, + the two above), 0 ax, 0 sorry,
host-verified v4.31 first try (`lake env lean` exit 0; `#print axioms` =
`[propext, Classical.choice, Quot.sound]` on all 5). Sylvester unimodality now
covers `k ≤ 4 ∨ k ≥ n−4`; the open interior is `5 ≤ k ≤ n−5` (first instance
`[10,5]_q`).

**Mechanism (the k=4 surprise — cleaner than k=3):** dual-Pascal recurrence
`coeff j [N+5,4] = coeff j [N+4,4] + [N+1 ≤ j]·coeff (j−(N+1)) [N+4,3]`. Growing
the box adds exactly TWO first-half indices (the band). With `u_N, v_N` the last
two first-half increments of the `4×N` array and `δ(N)` the k=3 box-free prefix
increment (`p₃(N)−p₃(N−1)`, = #partitions of N into 2s and 3s, closed form never
needed), palindromy reflects the just-past-half increments onto `−u_N, −v_N`,
giving the linear band recursion `u_{N+1} = δ(N+1) − v_N`, `v_{N+1} = δ(N) − u_N`
with EXACT closed solution `v ≡ 0`, `u = δ` (verified base `[5,4]=[5,1]` flat).
Band nonnegativity is then literally the k=3 first-half monotonicity — no new
analytic input. Below the band: IH + k=3 first-half increment ≥ 0 (the shifted
index always lands in the k=3 first half: `j−(N+1) ≤ N−2 < ⌈3(N+1)/2⌉`).
δ box-independence = k=3 prefix stability, inlined via `qBinom_X_three_coeff_succ'`
if_neg (no new lemma).

**Why k=5 does NOT follow the same way (recorded honestly):** the box step adds
5/2 indices — the band alternates 2/3 points across parity classes, the
compensating term is a k=4 increment that is itself only implicitly known
(`u = δ` gives the LAST band increment but not the interior near-center ones the
reflection would hit), and no analogue of the exact `v ≡ 0` solution is evident.
The general interior needs sl₂/O'Hara (existing blocked-route entry stands).

## Status (S4, researcher-1, 2026-07-21) — high-codimension cases k ≥ n−2 closed via symmetry

`qBinomCoeff_unimodal_of_codim_le_two (hk : k ≤ n) (hnk : n−2 ≤ k) : Unimodal (coeff [n,k]_q)`
— 1 thm, 0 ax, 0 sorry, host-verified v4.31 (`lake env lean` exit 0; `#print axioms` =
`[propext, Classical.choice, Quot.sound]`). Gaussian binomials satisfy `[n,k]_q = [n,n−k]_q`
*as polynomials* (`qBinom_symm`, already on main), so the proved low-`k` base cases
(`qBinomCoeff_unimodal_{zero,one,two}`) give unimodality for the whole high-`k` family
`k ∈ {n−2, n−1, n}` at no analytic cost. Combined with `k ≤ 2`, the ONLY range where
Sylvester unimodality remains open is now the genuine interior `3 ≤ k ≤ n−3` — whose first
hard instance is the `k=3` box-binding tail `N < j ≤ ⌊(3N−2)/2⌋` (needs sl₂/O'Hara; the
box-free prefix `j+1 ≤ N` is done, `qBinom_X_three_coeff_prefix_mono`).

Trivial proof once the symmetry is spotted: `rw [qBinom_symm]` then case `n−k ∈ {0,1,2}`.
The value is the coverage, not the difficulty — it retires an infinite family the deep
machinery would otherwise be needed for.

## Status (S2, researcher-1, 2026-07-20) — unimodality API + base cases k ≤ 1

NOTE: the S1 template below was never filled in even though a substantial companion
file (`CombinationsFormulaOQ03OQ04.lean`, 16 thm, 0 ax/sorry — palindromy, degree,
monicity, coeff-nonneg, pinned extreme coeffs) already existed. This is the first
real ACT status.

New file `CombinationsFormulaOQ03OQ04Unimodal.lean` (1 def + 5 thm, 0 ax, 0 sorry,
docker-VERIFIED `[propext, Classical.choice, Quot.sound]`). Supplies the unimodality
layer the target theorem needs and the first two milestones:

- `IsCoeffUnimodal p` — coefficient-sequence unimodality of `p : ℤ[X]` (a peak index
  below which coeffs weakly rise, above which they weakly fall). Fills the Mathlib gap
  named in problem.md ("no Unimodal predicate for integer sequences").
- `isCoeffUnimodal_of_antitone` — a globally non-increasing coeff sequence is unimodal
  (peak at 0); the reusable reduction both base cases use.
- `qNumber_X_coeff` — coeff array of `qNumber X n = 1 + X + ⋯ + X^{n-1}` is `[j < n]`.
- `qBinom_X_coeff_one` — hence coeffs of `[n,1]_q` are `[j < n]`.
- `qBinom_X_unimodal_zero` / `qBinom_X_unimodal_one` — the coeff sequences of `[n,0]_q`
  and `[n,1]_q` are unimodal (base cases k = 0, 1 of Sylvester's theorem).

**Honesty**: `k ≤ 1` is the *easy* regime — both sequences are flat/monotone, so
unimodality collapses to `isCoeffUnimodal_of_antitone`. The hard cases `k ≥ 2`, where
the sequence genuinely rises then falls (e.g. `[6,2]_q = 1,1,2,2,3,2,2,1,1`), are the
open crux and need the sl₂-action / hard-Lefschetz argument (Proctor 1982) or O'Hara's
combinatorial decomposition (1990). Not attempted here.

## Status (S3, researcher-1, 2026-07-20) — general reduction: Sylvester ⇐ first-half monotonicity

k=0,1,2 are already discharged (`qBinomCoeff_unimodal_{zero,one,two}`). This session
removed the last *structural* obstacle for all remaining k:

- `unimodal_of_palindrome_first_half_mono d` — general any-degree palindrome→unimodal
  criterion (odd degrees now covered; the previous lemma handled only even `2m`). The even
  lemma is refactored to a one-line corollary, statement unchanged.
- `qBinomCoeff_unimodal_of_first_half_mono (h : k ≤ n)` — the packaged reduction: supplies
  nonnegativity + support + palindromy, so proving Sylvester for a given `k` now needs ONLY
  the first-half inequality `coeff j ≤ coeff (j+1)` for `2j+2 ≤ k(n-k)`.

Both 0-axiom / 0-sorry, host-verified (`lake env lean` exit 0, axioms
`[propext, Classical.choice, Quot.sound]`).

## Next Action
The elementary per-k ladder has now closed k ∈ {0,1,2,3,4} and codim ≤ 4. A k=5
session should FIRST check whether the band analysis extends: derive the 2/3-point
band structure for `5×N` boxes, express the reflected increments via the k=4 band
solution (`u = δ`, `v = 0`), and see whether the resulting linear recursion again
has a closed solution. If the interior near-center k=4 increments (not covered by
`u = δ`) are needed, that is the wall — record it as the blocked-route extension
and stop. The general interior `5 ≤ k ≤ n−5` remains sl₂/O'Hara territory
(existing blocked-route entry: "materially new mechanism required").

## --- S1 template (never filled) below ---

## Current Focus
Initial problem understanding. Read problem.md and gather context.

## Active Approach
None yet.

## Attempt Count
- Total attempts: 0
- Current approach attempts: 0
- Approaches tried: 0

## Blockers
None.

## Next Action
Read problem.md thoroughly and acquire full context.
Then move to ORIENT phase to explore literature and related proofs.

## Status (S5, researcher-1, 2026-07-22) — k = 3 CLOSED: center-band recursion (elementary)

The box-binding tail is settled — the 07-21 "blocked" verdict is reopened legitimately by a
materially new mechanism, the **dual q-Pascal / center-band recursion**:

- `qBinom_X_three_coeff_succ'`: second-form recurrence `[N+4,3] = [N+3,3] + q^{N+1}[N+3,2]`
  — its correction term is the *unshifted, exactly known* k=2 ramp (the first form's shifted
  term was the blocker).
- The first half of box `3×(N+1)` exceeds box `3×N`'s by ≤ 2 indices (the *center band*);
  there the smaller-box increment is exact via palindromy. Band increments are 0/1 with
  period-2 pattern: odd box `2M+1` at `j=3M`: 0; even box `2M+2` at `j=3M+1,3M+2`:
  `[M even]`, `[M odd]` (`qBinom_X_three_band`, `_band_E1`).
- `qBinom_X_three_coeff_first_half_mono`: full first-half monotonicity for k=3.
- `qBinomCoeff_unimodal_three` + `qBinomCoeff_unimodal_of_codim_le_three`: **Sylvester's
  theorem now formalized for k ≤ 3 and k ≥ n−3**; open range = interior 4 ≤ k ≤ n−4
  (first open instance `[8,4]_q`).

All 0-axiom (`[propext, Classical.choice, Quot.sound]`), host-verified `lake env lean` exit 0.

Why this does NOT extend to k=4 as-is: the band widens to ~k−1 indices and the needed
increments become exact k=3 band values at general offsets (quasi-polynomial P3) — that is
where sl₂/O'Hara genuinely re-enter. Interior range stays blocked (reopen bar: materially
new mechanism).
