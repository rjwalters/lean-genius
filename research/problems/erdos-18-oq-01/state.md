# State: erdos-18-oq-01

**Phase**: ACT
**Since**: 2026-07-12T00:00:00Z
**Attempts**: 5
**Status**: available

## Current Focus
Structural divisibility theory in `Proofs/Erdos18OQ01.lean` (now 45 theorems,
0 axioms, 0 sorries). Session 2026-07-12 (researcher-2) added the **third-smallest
divisor** constraint: `practical_three_or_four_dvd` (`4 < m` practical ⇒ `3 ∣ m ∨ 4 ∣ m`,
the `d₃ ≤ 4` fact, from the two distinct-divisor sums `{4}`/`{1,3}` for `4`) and
`practical_four_or_six_dvd` (⇒ `4 ∣ m ∨ 6 ∣ m`, combining the `3 ∣ m` branch with
`practical_even`). Every practical number `> 4` is thus a multiple of `4` or of `6`.

## Blockers
- The asymptotic density of practical numbers (`h(m)`, Vose / Mertens-type bounds)
  needs analytic number theory beyond elementary reach — out of single-session scope.
- The full Stewart–Sierpiński multiplicative criterion (odd-prime step
  `IsPractical m → p ≤ σ(m)+1 → IsPractical (p·m)`) is NOT reachable with current
  machinery: it needs full `[0,σ(m)]` coverage plus gcd(p,m) divisor analysis, not the
  base-m decomposition used by `practical_mul`.
- Full-range `[0,σ(m)]` representation for arbitrary abundancy needs the greedy
  sorted-divisor characterization (`d_{i+1} ≤ σ_i + 1`); the file currently reaches
  abundancy `< 4` via bottom/top double-blocks.

## Next Action
Options: (a) continue the `dₖ` divisor chain — `5,6` representable give further
divisibility constraints, but the subset-enumeration case analysis grows; (b) attempt
the greedy sorted-divisor full-range theorem (larger project, needs `Finset` sorting of
divisors); or (c) leave as-is — the structural + closure + sharpness + `d₃` results are
a self-contained body.
