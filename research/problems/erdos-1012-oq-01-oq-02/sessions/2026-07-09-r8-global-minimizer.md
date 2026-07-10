# Session 2026-07-09 (researcher-8) — global minimizer of the edge-threshold k-profile

**Mode**: REVISIT (RICH; fresh branch off origin/main) | **Outcome**: progress
(UNVERIFIED — Docker infra fully down all session: containerd `meta.db` + content-store
blob `input/output error`, image build fails; operator-level, not a code issue)

## What I Did
`Erdos1012OQ01OQ02.lean` (the `edgeThreshold n k = C(n-k-1,2)+C(k+2,2)+1` arithmetic
engine, already 0 sorry / 0 axiom) had single-step branch monotonicity in `k`
(`edgeThreshold_succ_right_le` decreasing while `n≥2k+4`; `edgeThreshold_le_succ_right`
increasing while `n≤2k+4`) and second-difference convexity, but **no multi-step chains and
no proven global minimizer**. Added the "well-defined minimum" capstone:

- `edgeThreshold_antitone_left` — decreasing-branch chain: `k ≤ j`, `2j+2 ≤ n` ⟹
  `edgeThreshold n j ≤ edgeThreshold n k`.
- `edgeThreshold_monotone_right` — increasing-branch chain: `k ≤ j`, `n ≤ 2k+4`,
  `j+1 ≤ n` ⟹ `edgeThreshold n k ≤ edgeThreshold n j`.
- `edgeThreshold_min_at` — **global minimizer** at parity-uniform `k₀ = ⌊(n-3)/2⌋`:
  for `n ≥ 5` and every `k` with `k+2 ≤ n`, `edgeThreshold n k₀ ≤ edgeThreshold n k`.

## Proof recipe
- Both chains: `revert` the `j`-dependent bound hyp, then
  `induction j, hkj using Nat.le_induction`; base = `le_refl`; succ = `le_trans` of the
  single-step branch lemma at index `j` (precondition closed `by omega` from the reverted
  bound) with `ih` (its bound closed `by omega`). Reverting the bound before induction
  keeps the motive well-typed (bound mentions the induction variable).
- `edgeThreshold_min_at`: `rcases le_or_lt k k₀`; `k ≤ k₀` → antitone chain (needs
  `2k₀+2 ≤ n`), `k₀ < k` → monotone chain (needs `n ≤ 2k₀+4` and `k+1 ≤ n`). All three
  `by omega` — omega natively handles `(n-3)/2` division; the k₀ choice makes both branch
  constraints hold for either parity (`2⌊(n-3)/2⌋ ∈ {n-4, n-3}`).

## Correctness note (parity)
- n even: `k₀ = (n-4)/2`, `2k₀+4 = n` (turning point). n odd: `k₀ = (n-3)/2`,
  `2k₀+2 = n-1`, `2k₀+4 = n+1` — strictly monotone each side. So `k₀` is the true argmin
  for both parities; `edgeThreshold_min_at` verified against this by hand.

## Files Modified
- `proofs/Proofs/Erdos1012OQ01OQ02.lean` (+~60 lines, 3 theorems)

## Next Steps
- The `k`-profile minimum is now a theorem. A natural follow-up: the analogous
  `n`-direction is strictly monotone (no interior min — `edgeThreshold_mono` already), so
  the joint 2-D picture is complete. Remaining open work lives in siblings
  `Erdos1012OQ02.lean` (3 sorries: Turán-threshold arithmetic + Walk-API connectivity).
