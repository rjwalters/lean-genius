# Session 2026-07-08 (researcher-10) — AXIOM ELIMINATED: `optimal_lower` in Erdos490OQ01 (2→1 axioms)

**Mode**: ACT (family axiom-reduction). **Outcome**: progress — eliminated the axiom
`optimal_lower` in the sibling open-question file `Erdos490OQ01.lean`, proving it 0-axiom
by reusing the main file's now-verified `Erdos490.bound_is_optimal`. `Erdos490OQ01.lean`
axiom count **2 → 1** (only the deep `szemeredi_upper` remains). Docker build green
(7745 jobs).

## Context
The base completion task `erdos-490-incomplete-01` (`Erdos490Problem.lean`) is at a stable
frontier: **0 sorries, 1 axiom** (`szemeredi_theorem`, the deep Szemerédi 1976 *upper*
bound). Its matching *lower* bound `bound_is_optimal` was fully proved 0-axiom in the
07-08 (researcher-2) Chebyshev θ-gap session. Its gallery meta is in sync.

The sibling file `Erdos490OQ01.lean` (open question: does `maxProd(N)·logN/N²` converge?)
still carried **2 axioms**: `szemeredi_upper` (= Szemerédi, deep) and `optimal_lower`
(`maxProd(N) ≥ c·N²/logN`). The latter duplicates content already proved in the main file.

## What I did (verified, 0-axiom)
Converted `axiom optimal_lower` into a **theorem** by transferring the main file's proved
lower bound:
- `maxProd N` is the max of `|A||B|` over valid distinct-product pairs, and dominates the
  product of *any* single valid pair (`maxProd_is_upper`).
- `Erdos490.bound_is_optimal` (0-axiom) hands a specific pair `(A,B)` = `([1,N/2], primes
  in (N/2,N])` with `|A||B| ≥ c₀·N²/logN` for `N ≥ 4`. Its `Erdos490.IsSubsetUpTo` /
  `Erdos490.HasDistinctProducts` witnesses convert to OQ01's primed `IsSubsetUpTo'` /
  `HasDistinctProducts'` (identical bodies; `HasDistinctProducts'` = main's
  `ProductMapInjective`, via `Erdos490.productMapInjective_iff_hasDistinctProducts`).
  Feeding them to `maxProd_is_upper` gives `c₀·N²/logN ≤ |A||B| ≤ maxProd N` for `N ≥ 4`.
- **Small cases `N ∈ {2,3}`** (below `bound_is_optimal`'s `N ≥ 4` floor): new helper
  `maxProd_ge_self : (N:ℝ) ≤ maxProd N` (from the pair `A = Icc 1 N`, `B = {1}`,
  `|A||B| = N`). Choosing the final constant `c = min c₀ (min (log2/2) (log3/3))` makes
  `c ≤ logN/N` for `N ∈ {2,3}`, so `c·N²/logN ≤ N ≤ maxProd N`. No log *numerics* needed —
  only symbolic `min_le` + `Real.log_pos`.

Final constant `c = min c₀ (min (log 2/2) (log 3/3)) > 0`.

## Gotchas / API
- The two files use **distinct-but-identical** defs (`IsSubsetUpTo` vs `IsSubsetUpTo'`,
  `ProductMapInjective` vs `HasDistinctProducts'`): convert by `intro`+re-`exact`, they are
  not defeq by *name* but share bodies so the applied form typechecks.
- `bound_is_optimal` states `(A.card*B.card : ℝ) ≥ c₀*N²/logN`; keep the ℕ→ℝ cast of
  `maxProd_is_upper` in the **same** `(A.card * B.card : ℝ)` syntactic form so `linarith`
  sees one atom (`exact_mod_cast` into that shape, then `linarith [hge, hup]`).
- Constant scaling `c·N²/logN ≤ c₀·N²/logN` for `c ≤ c₀`: avoid `gcongr`/`div_le_div_*`
  name-drift — `rw [mul_div_assoc, mul_div_assoc]` then
  `mul_le_mul_of_nonneg_right (min_le_left _ _) (div_nonneg (by positivity) hlogN.le)`.
  (`positivity` can't prove `0 ≤ N²/logN` alone since `log N` isn't obviously ≥ 0; supply
  `hlogN.le` explicitly.)
- Small N: after `interval_cases N`, `push_cast at hself ⊢` normalises `((2:ℕ):ℝ) → 2` in
  **both** the goal and the `maxProd_ge_self` hypothesis so `linarith` connects them.

## Verification
Docker `docker-build.sh Proofs.Erdos490OQ01` (Lean 4.26.0, Mathlib pinned) → **7745 jobs,
Build succeeded**, 0 errors / 0 sorries in the file (only pre-existing unused-variable
warnings in `Erdos490Problem.lean`). `#print axioms optimal_lower` = `[propext,
Classical.choice, Quot.sound]` (no `sorryAx`, no `Lean.ofReduceBool`) — a clean 0-axiom
theorem.

Gallery meta `src/data/proofs/erdos-490-oq-01/meta.json`: axiomCount 2 → 1, lineCount
268 → 343, theoremCount 11 → 13; assumptions/description/proofStrategy prose reconciled
(also cleared pre-existing "3 axioms" drift — `maxProd_exists` had already been proved).

## Still open (NOT done here)
- `szemeredi_upper` / `szemeredi_theorem` (the N²/logN **upper** bound; Szemerédi 1976) —
  the genuinely deep result, correctly axiomatized in both files. Not attackable
  (Mathlib's `Chebyshev.lean` itself lists the lower bound as future work; the *upper*
  Szemerédi combinatorial bound is a separate, harder gap).
- The Erdős limit question itself (does the ratio converge?) — the open math question the
  file frames; unresolved.
