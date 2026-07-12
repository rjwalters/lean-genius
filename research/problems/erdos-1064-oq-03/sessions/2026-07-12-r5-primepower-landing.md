# Session 2026-07-12 (researcher-5) — prime-power-landing reversal engine + witness 561

**Mode**: REVISIT (RICH tier; structural side already COMPLETE/VERIFIED) |
**Outcome**: progress (new engine, all VERIFIED 0 sorry / 0 axiom on host `bin/lake env lean`)

## Context

The file `EulerTotientOQ04OQ03.lean` (3746L before this session) already resolves
the tractable content of OQ-03: all three regimes (`ReversalSet`, `EqualitySet`,
`ForwardSet`) occur infinitely often, the classifier `classifySeed` decides every
family `n = a·2^(k+1)`, and there is a **prime-landing** engine
(`classifySeed_eq_compare_of_seedS_one_seedE_prime` and its `.lt/.eq/.gt`
corollaries) that collapses the classifier to a linear criterion when the landing
odd-part `seedE a` is prime. The seed `165` witnesses that reversals also occur on
composite landings, but `165`'s landing `115 = 5·23` is a general semiprime with no
closed form for `φ`, so it sat outside every closed-form engine.

## What I did

Built the **prime-power-landing engine** — the next tier where `φ(seedE a)` has a
closed form, `φ(p^m) = p^{m-1}(p−1)`:

- `classifySeed_eq_compare_of_seedS_one_seedE_primePow` — for `seedS a = 1` and
  `seedE a = p^m` (`p` prime, `m ≥ 1`):
  `classifySeed a = compare (φ(seedB a) + p^{m-1}·2^{seedT a}) (2·(a − φ(a)))`.
  Strictly generalises the prime engine: `m = 1` gives `p^{m-1} = 1` and recovers
  the exact prior criterion.
- `.lt / .eq / .gt` iff corollaries and `primePow_landing_family_reversal`
  (packages the reversal criterion into infinitely-often family membership).
- Concrete witness **`a = 561 = 3·11·17`** (the smallest Carmichael number): a
  reversal seed whose landing odd-part is the **prime square** `seedE 561 = 361 =
  19²` — composite, so outside the prime engine, but certified by the prime-power
  engine via `φ(401) + 19·2 = 438 < 482 = 2·(561 − 320)`.
  Lemmas: `totient_401/361/561`, `classifySeed_561`, `seedE_561`,
  `seedE_561_not_prime`, `mem_ReversalSet_561`, `reversal_seed_primePow_landing`.

Enumeration (sympy, seeds `a < 4000`): of 154 reversal seeds, 72 have prime
landings, 79 general-composite, and **3 are proper prime powers** — `561` (`19²`),
`1225` (`31²`), `1595` (`11³`). So the prime-power tier is genuinely non-empty and
sits strictly between the prime-landing seeds and the general composite seed `165`.

## Key Lean findings / gotchas

- `φ(p^m) = p^{m-1}(p−1)` via `Nat.totient_prime_pow hp (0 < m)`. The additive
  identity `φ(e) + p^{m-1} = e` (from `e = p^{m-1}·p`) is the crux; multiply
  through by `2^{t−1}` to get `φ(e)·2^{t−1} + p^{m-1}·2^{t−1} = e·2^{t−1}`.
- **omega + nonlinear substitution trap**: leaving `hφe : φ(seedE a) =
  p^{m-1}·(p−1)` and `hEfac : seedE a = p^{m-1}·p` in context makes `omega`
  substitute them into the products `φ(seedE a)·2^{t−1}` / `seedE a·2^{t−1}`,
  turning linear atoms into nonlinear ones it then *drops* — losing the `hAB`/`hCeq`
  linkage and failing. Fix: derive `hcls` via `Nat.eq_sub_of_add_eq hAB` (not
  omega), then `clear hφe hEfac hkey hepp` before the classifier trichotomy so
  omega keeps `seedE a·2^{…}` as opaque linear atoms.
- `maxRecDepth`: `seedE_561`'s `factor_two_split` extraction needed
  `set_option maxRecDepth 4000 in`; prefer `Nat.odd_iff.mpr (by norm_num)` over
  `by decide` for oddness of larger numerals, and `rw [totient_N]` over
  `norm_num [totient_N]` to avoid norm_num re-evaluating `Nat.totient`.

## Files modified

- `proofs/Proofs/EulerTotientOQ04OQ03.lean` (+~150L, 201 → 213 theorems, still 0/0)
- `src/data/research/problems/erdos-1064-oq-03.json`

## Next steps

- The only genuinely-open direction remains the density-1 forward statement
  (Luca–Pomerance smooth-number density) — not session-sized.
- Optional elementary follow-up: whether there are **infinitely many** reversal
  seeds with proper-prime-power landing (the `561, 1225, 1595, …` sequence),
  paralleling the prime-landing seeds; requires an unbounded parametric family, a
  genuinely new direction rather than a recursion on this index.
