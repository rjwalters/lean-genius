# Problem Selection Report

**Date**: 2026-04-05
**Mode**: SELECT
**Pool Status**: 21 available (JSON), 326 in-progress, 1218 completed, 1 graduated

## Selected Problem

- **ID**: dirichlets-theorem-oq-03-oq-01
- **Name**: Can `linnikConstant_pos` (L* ≥ 1) be proved in Lean from Bertrand's postulate?
- **Tier**: B
- **Significance**: 8/10
- **Tractability**: 6/10
- **Knowledge Score**: 0 (EMPTY)
- **Composite Score**: 68
- **Status**: available

## Selection Rationale

1. **EMPTY knowledge tier** — no prior research in the problem workspace; highest priority tier.
2. **Concrete sorry target** — `DirichletsTheoremOQ03.lean` line 63 has a single sorry in `linnikConstant_pos : linnikConstant ≥ 1`. Proof sketch: any prime p ≡ 1 (mod q) satisfies p = kq+1 ≥ q+1, so if L < 1 were admissible with constant c, then c·q^L < q+1 ≤ p(1,q) for large q — contradiction via `le_csInf`.
3. **Score 68** tied with buffons-needle-oq-02-oq-02-oq-01 (sig=8, tract=6), but preferred because the Buffon file explicitly notes "beyond current Mathlib infrastructure" for Cauchy-Crofton in ℝ³; the Linnik lower bound uses only `sInf` properties and elementary modular arithmetic.
4. **Not recently selected** — last 10 seeker commits: minkowski (×2), birthday, taylor, bezout. dirichlets-theorem-oq-03-oq-01 is fresh.
5. **Domain diversity** — analytic number theory; distinct from recent selections (number theory approximation, combinatorics/probability, analysis).

## Proof Strategy for Researcher

Goal: `sInf admissibleExponents ≥ 1`. Method: show 1 is a lower bound via `le_csInf`.

**Key lemma**: for any prime p ≡ 1 (mod q) with q ≥ 2, p ≥ q+1.
- p = kq+1 for some k ≥ 0; k=0 gives p=1 (not prime); so k ≥ 1 and p ≥ q+1.

**Growth contradiction**: if L < 1 with c·q^L bound:
- For large q: c·q^L = c·q^L where q^(L-1) → 0, so c·q^L/q → 0
- Hence c·q^L < q ≤ leastPrimeInAP 1 q - 1 for large q — contradicts admissibility

**Mathlib tools**:
- `le_csInf` for the sInf lower bound
- `Nat.Coprime.one_left` for Coprime 1 q
- Growth: `Filter.Tendsto`, `Real.tendsto_rpow_atTop` or explicit ε-N argument
- `leastPrimeInAP` lower bound via the mod arithmetic argument

**Complication**: `leastPrimeInAP` uses `Nat.find ⟨sorry, sorry⟩`. The existence sorry may prevent direct use. Alternative: derive the lower bound from `linnik_theorem` (the axiom) by showing the constant c and exponent L cannot satisfy L < 1.

## Rejection Summary

- **Candidates considered**: 21 available
- **Rejected** (recently selected): minkowski-theorem-oq-02-oq-01 (score 78, selected twice recently), bezout-identity-oq-04-oq-01-oq-03 (score 77), birthday-problem-oq-03-oq-01-oq-01-oq-03 (score 76), taylor-theorem-oq-03-oq-01 (WEAK tier, score −923)
- **Rejected** (lower tractability): buffons-needle-oq-02-oq-02-oq-01 (Cauchy-Crofton "beyond Mathlib"), hilbert-10-oq-03 (tract=4, open research)
- **Rejected** (low significance): binary-gcd-oq-01-oq-04-oq-01 (sig=5, C tier)
- **Remaining 14**: composite scores < 68
- **Confidence**: medium (two candidates tied at 68; chose on effective tractability grounds)

## Related Gallery Proofs

- `dirichlets-theorem`: parent (Dirichlet's theorem, axiomatized)
- `dirichlets-theorem-oq-03`: immediate parent (Linnik's theorem file `DirichletsTheoremOQ03.lean`)
- Analytic number theory family: adjacent domain

## Suggested First Steps

1. **OBSERVE**: Read `DirichletsTheoremOQ03.lean` completely; catalog all sorries/axioms (`linnik_theorem`, `xylouris_bound`, the two sorries in `leastPrimeInAP`, the sorry in `linnikConstant_pos`)
2. **ORIENT**: Search Mathlib for `le_csInf`, `Real.rpow` growth lemmas, and `Nat.find` properties; check if Dirichlet's theorem for arithmetic progressions is in Mathlib (it is not as of 2024, but check current state)
3. **DECIDE**: Attempt `le_csInf (admissible_nonempty.nonempty) (fun L hL => ...)` with the growth argument; formalize the key lemma that p ≡ 1 (mod q) implies p ≥ q+1

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 21 |
| In Progress | 326 |
| Completed | 1218 |
| Graduated | 1 |
| **Total** | **1566** |

## Candidate Pool Health

- **Pool depth**: adequate (21 available)
- **Recommendation**: Pool healthy; no refresh needed
- **Next refresh recommended**: when available drops below 10
