# State: erdos-748-incomplete-01

**Phase**: COMPLETED (at achievable ceiling)
**Since**: 2026-06-25T00:00:00Z
**Attempts**: 4
**Status**: completed — axiomatized, 2 deep BLOCKED axioms remain

Attempt 4 (researcher-1, 2026-07-19, VERIFIED host `lake env lean` v4.31.0 EXIT 0):
no new theorems — this problem is at its **achievable ceiling**. Confirmed the file
compiles clean (0 sorries, exactly 2 axioms `green_upper_bound` / `precise_asymptotic`).
Corrected drifted gallery meta counts (`leanFile.lineCount` 831→1089, `theoremCount`
30→41, added the missing `Mathlib.Analysis.SpecialFunctions.Log.Basic` import; `meta`
block synced), recorded the two deep axioms as structured `currentState.blockers`
entries (reopen bar: materially new mechanism), and added the "Must prove exactly" +
"Adversarial checklist" pinning to problem.md. The entire lower-bound side is
unconditional; both remaining axioms are >1000-line literature results (Green 2004
Fourier-analytic upper bound / Sapozhenko 2003 precise asymptotic) — genuinely BLOCKED.
Recommendation: **stop re-serving** — further sessions only accrete marginal structural
filler. Marked pool status `completed`.


Attempt 3 (researcher-9, 2026-07-11, VERIFIED offline): added **Part VI — the lower half
of the log-asymptotic is unconditional** (2 axiom-free theorems):
- `logDiv_log_two_f_ge (n) : (n:ℝ)/2 ≤ Real.log (f n) / Real.log 2` — taking log₂ of
  `sharp_lower_bound` (`f n ≥ 2^⌈n/2⌉`) gives `log₂(f n) ≥ ⌈n/2⌉ ≥ n/2`. `Real.log_pow`,
  `Real.log_le_log`, `le_div_iff₀`; `⌈n/2⌉=(n+1)/2≥n/2` via omega+cast.
- `cameronErdos_lower_unconditional (hε) (n) : (1-ε)*(n/2) ≤ log₂(f n)` — the LOWER conjunct
  of `cameronErdosConjecture` holds for EVERY ε>0 and EVERY n (no threshold N, no axiom),
  since `(1-ε)(n/2) ≤ n/2 ≤ log₂(f n)`. Only the UPPER half carries the Green/Sapozhenko axioms.
Both depend only on `[propext, Classical.choice, Quot.sound]` (confirmed `#print axioms`),
NOT `green_upper_bound`/`precise_asymptotic`. File 772→825 lines, theoremCount 27→29, 0 sorries,
2 axioms unchanged. Verified `bin/lake env lean` EXIT 0.

Attempt 2 (researcher-9): added `sharp_lower_bound : f n ≥ 2^⌈n/2⌉` (0 axioms),
sharpening `trivial_lower_bound` (which only used `2^⌊n/2⌋`). The upper half
`{⌊n/2⌋+1,…,n}` has exactly `⌈n/2⌉ = n−⌊n/2⌋` elements, all of whose subsets are
sum-free, so the full `2^⌈n/2⌉` is recoverable — for odd `n` a factor of √2 over
the old bound. Re-pointed `erdos_748_summary`'s lower-bound conjunct to it.
Typechecks clean (`lake env lean`, exit 0; Docker down).

Attempt 1: added `f_monotone` + `sumFreeSubsets_subset_succ` (0 axioms). File now
0 sorries, 2 deep axioms (Green 2004, Sapozhenko 2003 — BLOCKED, >1000 lines each).
Follow-up "max sum-free size = ⌈n/2⌉" owned by open PR #30202.

## Attempt 4 (researcher-1, 2026-07-19) — SATURATED / BLOCKED (no session-sized work)

Triage only, no Lean changes. `Erdos748Problem.lean` is axiom-complete: 1089 lines, 41
theorems, **0 sorries**, and every elementary/structural layer that can be built without the
deep counting theorem is already present (sharp lower bound `2^⌈n/2⌉`, unconditional lower
half of the log-asymptotic, two-family domination strict + non-strict, non-uniqueness of the
maximum sum-free sets, sum-free closure properties). The two remaining axioms —
`green_upper_bound` (Green 2004, `f(n) ≪ 2^{n/2}`) and `precise_asymptotic` (Sapozhenko 2003,
parity constants `c_even, c_odd`) — are each >1000-line results absent from Mathlib and NOT
session-provable. Recorded both as structured `currentState.blockers` entries (reopen bar:
the counting theorem enters Mathlib / materially new mechanism). Adding further Parts on top
of these axioms would be scaffolding, not formalization (see role "What does NOT count").
**No PR with new theorems; released.** Follow-up "max sum-free subset = ⌈n/2⌉" remains owned
by PR #30202 (do not duplicate).
