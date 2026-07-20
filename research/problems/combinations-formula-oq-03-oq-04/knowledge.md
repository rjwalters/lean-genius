# Knowledge Base: combinations-formula-oq-03-oq-04

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

### 2026-07-20 (researcher-1) — unimodality API + base cases k ≤ 1

- **Mathlib gap confirmed**: no `Unimodal` predicate for integer sequences. Introduced
  `IsCoeffUnimodal (p : ℤ[X])` = ∃ peak index m with coeffs weakly rising to m and weakly
  falling after, in `CombinationsFormulaOQ03OQ04Unimodal.lean`.
- **`isCoeffUnimodal_of_antitone`**: a globally non-increasing coeff sequence is unimodal
  (peak 0). The rising half is vacuous (only i=j=0 with i≤j≤0). Covers every flat/monotone
  base case cheaply.
- **Coefficient extraction that works**: `qBinom_one_right` (`[n,1]_q = qNumber X n`,
  general `R`) + an induction on `qNumber X (n+1) = 1 + X·qNumber X n` gives
  `qNumber_X_coeff n j = if j < n then 1 else 0`. Key simp lemmas: `coeff_add`, `coeff_one`,
  `coeff_X_mul` (for `(X·p).coeff (m+1) = p.coeff m`). Then both base cases reduce to
  `simp only [<coeff formula>]; split_ifs <;> omega`.
- **Base cases proved**: `qBinom_X_unimodal_zero` (k=0, coeff seq 1,0,0,…) and
  `qBinom_X_unimodal_one` (k=1, coeff seq 1,…,1,0,…). Both are antitone, so unimodal.

### Route to k = 2 (next, genuine content)
`[n,2]_q` coeffs count partitions in a 2×(n−2) box: `a_i = ⌊i/2⌋+1` for the rising half,
mirrored (peak interior). This is the first case where `_of_antitone` fails and the
rise-then-fall must be argued directly — the named tractable milestone in problem.md.

### Open crux (k ≥ 2 general)
Sylvester unimodality for general k needs sl₂-action / hard Lefschetz (Proctor 1982) or
O'Hara's (1990) combinatorial symmetric-chain decomposition — research-grade formalization,
not yet started.

---

## Dead Ends

[Approaches known not to work will be documented here]

### 2026-07-20 (researcher-1) — bridged the two forked unimodality predicates

**Fork discovered.** Two parallel developments exist on main:
- `CombinationsFormulaOQ03OQ04.lean` (PR #39392) — predicate `Unimodal (ℕ → ℤ)`
  (adjacent-step: `∃ p, (∀ i<p, f i ≤ f(i+1)) ∧ (∀ i≥p, f(i+1) ≤ f i)`). Already
  has k=0,1,**2** plus `unimodal_of_even_palindrome_first_half_mono` and the
  `[n,2]_q` coefficient machinery (`qBinom_X_two_coeff_succ/le`).
- `CombinationsFormulaOQ03OQ04Unimodal.lean` (PR #39438, this track) — predicate
  `IsCoeffUnimodal (ℤ[X])` (monotone-on-blocks). Was stuck at k≤1; its stated
  "route to k=2" was **duplicative** of the above.

**Resolution.** Added `isCoeffUnimodal_iff_unimodal_coeff : IsCoeffUnimodal p ↔
Unimodal (fun j => p.coeff j)`. Forward = specialise the monotone blocks to single
adjacent steps. Backward = telescope adjacent steps into monotone blocks by
induction on the index gap (two helpers `rise`/`fall`, `∀ d i, …`). Then
`qBinom_X_unimodal_two` transports the companion file's `qBinomCoeff_unimodal_two`
into `IsCoeffUnimodal` form with **no re-proof**.

Host-verified `bin/lake env lean` exit 0 (had to refresh stale
`CombinationsFormulaOQ03{,OQ04}.olean` in the cache — incompatible header from an
older toolchain — via `lake env lean … -o`). `#print axioms` on both new results =
`[propext, Classical.choice, Quot.sound]`.

**Guidance for future sessions:** prove new k-cases ONCE against `Unimodal` (it has
the palindrome criterion + coefficient extraction) and transport via the bridge.
Do not re-develop `IsCoeffUnimodal`-specific proofs. k≥3 (sl₂/hard-Lefschetz,
Proctor 1982, or O'Hara 1990) remains the open crux.
