# S10 (2026-07-24): ACT — Quantitative Schnirelmann constant

**Researcher**: researcher-1
**Mode**: REVISIT (same-day follow-on to S9, PR #43368)
**Decision**: DEEP DIVE — state.md S10 candidate (b): quantitative
bookkeeping, estimated ~150 LOC; delivered in 136.

## Goal

The S9 bridge (`schnirelmann_goldbach_bridge`) derives "every n ≥ 2 is a
sum of ≤ 3h+2 primes" from σ(G) > 0, but the basis order `h` comes out of
the existential `schnirelmann_basis_theorem` — the constant is
unspecified. S10 replaces the existential step with explicit arithmetic:
given a *numeric* lower bound `δ ≤ σ(G)`, compute `k(δ)` in closed form.

## Deliverables (WeakGoldbach.lean §S10, lines 916–1043, +136 net)

1. `pow_deficiency_lt_half {δ} (0 < δ) (δ ≤ 1) : (1−δ)^(⌊1/δ⌋₊+1) < 1/2`
   — Bernoulli: `(1+δ)^ℓ ≥ 1+ℓδ > 2` (`one_add_mul_le_pow`,
   `Nat.lt_floor_add_one`), and `(1−δ)^ℓ(1+δ)^ℓ = (1−δ²)^ℓ ≤ 1`
   (`pow_le_one₀`); contradiction via `nlinarith`.
2. `schnirelmann_basis_explicit` : `0 ∈ A → δ ≤ σ(A) → IsAdditiveBasis A
   (2(⌊1/δ⌋₊+1))` — feeds 1 through
   `SchnirelmannTheorem.deficiency_sumsetPow_le` (iterated Schnirelmann
   inequality, monotonicity closed by bare `gcongr`) and
   `SchnirelmannBasis.isAdditiveBasis_of_sumsetPow_density_ge_half`.
3. `boundedPrimeSums_of_basis` : h-parameterized S9 bridge core —
   `IsAdditiveBasis G h → ∀ n ≥ 2, ∃ T primes, |T| ≤ 3h+2, Σ = n`.
4. `schnirelmann_goldbach_explicit` : headline — `0 < δ ≤ σ(G)` → every
   `n ≥ 2` is a sum of at most `6(⌊1/δ⌋₊+1)+2` primes.
5. `sum_of_at_most_608_primes_of_density` : instantiation at `δ = 1/100`
   → `k = 608` (`ℓ = 101`, basis order 202, `3·202+2 = 608`). Confirms
   the closed form reduces to a numeral; makes no claim about the true
   σ(G) — Schnirelmann's sieve estimate remains unformalized.

No new axioms (still 4), no assumption-bearing structures, 0 sorries.

## Verification

`lake env lean Proofs/WeakGoldbach.lean` — exit 0, warnings only
(pre-existing `push_neg` deprecations). Full `#check` roster prints all
S10 signatures as intended.

Incident: the worktree's `Proofs/Schnirelmann*.olean` files were built
pre-v4.31 → "incompatible header" on import. Repaired host-side without
Docker by regenerating in dependency order:
`lake env lean -o .lake/build/lib/lean/Proofs/{SchnirelmannBasis,
SchnirelmannCounting,SchnirelmannTheorem}.olean` (each ~minutes; `lake
env` is wrapper-safe). This is the standing recipe for toolchain-drift
olean rot in slimmed worktrees.

## Counts

lineCount 943 → 1079; axiomCount 4 (unchanged); theoremCount (meta)
38 → 43; definitionCount 17; sorries 0.

## Next (S11+)

(a) sieve toward σ(G) > 0 — multi-quarter HEROIC; (b) log-based sharper
exponent `⌈log2/(−log(1−δ))⌉` — cosmetic ~0.69× improvement, ~60–100
LOC; (c) park — quantitative tier now saturated alongside elementary
tier. Recommendation: (c) unless a sieve toolkit lands in Mathlib.
