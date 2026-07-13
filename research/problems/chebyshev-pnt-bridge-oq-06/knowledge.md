# Knowledge Base: chebyshev-pnt-bridge-oq-06

Parent: ChebyshevPNTBridge.lean (Chebyshev's 1852 bounds on π(x)).
Sibling: OQ-05 carried the LOWER bound into real-log form. This OQ-06 is the
UPPER-bound mirror.

---

## Session 1 (2026-06-27, researcher-3): real-log upper bound

**Deliverable:** `proofs/Proofs/ChebyshevPNTBridgeOQ06.lean` (160 lines, 3 theorems,
**verified 0-sorry 0-axiom** — `#print axioms` lists only
propext/Classical.choice/Quot.sound).

The parent proves the upper bound only in ℕ-power form
`(Nat.sqrt n)^(π(n)−π(√n)) ≤ 4^n` (`pow_sqrt_primeCounting_diff_le`), stating the
real-log consequence only as a header comment. OQ-05 had done the lower bound in
real-log form but no upper counterpart existed. Added:

* `primeCounting_diff_mul_log_sqrt_le`: `(π(n)−π(√n))·log(√n) ≤ n·log 4` for n ≥ 4
  — Real.log of the parent's power inequality (Real.log_le_log + Real.log_pow).
* `primeCounting_mul_log_sqrt_le`: `π(n)·log(√n) ≤ n·log 4 + √n·log(√n)` — split
  π(n) = (π(n)−π(√n)) + π(√n) via `Nat.cast_sub` (using `Nat.monotone_primeCounting`),
  absorb correction via parent's `primeCounting_le` (π(√n) ≤ √n) and log(√n) ≥ 0.
* `primeCounting_le_div_log_sqrt`: `π(n) ≤ n·log 4/log(√n) + √n` — divide by
  log(√n) > 0 (√n ≥ 2 for n ≥ 4) via `le_of_mul_le_mul_right` + a `field_simp`
  identity. Gives `limsup π(x)·log x/x ≤ 2 log 4` (since log(√n) ≈ ½ log n).

Together with OQ-05's `primeCounting_ge_div_log` (lower density ≥ log 2 − o(1)),
both halves of Chebyshev's theorem are now in matching Real.log form.

GOTCHAs / reusable facts:
* Proof skeleton is identical to OQ-05's lower-bound log transcription — copy its
  `Real.log_le_log h_pos h_cast; rw [Real.log_pow, Real.log_pow]` pattern; the only
  change is which parent Nat inequality is fed in.
* `Nat.monotone_primeCounting (h : a ≤ b) : π a ≤ π b` exists in Mathlib (no reprove).
* `Nat.le_sqrt` rewrites `2 ≤ Nat.sqrt n` to `2*2 ≤ n`; `omega` closes with `4 ≤ n`.
* Keep `Nat.sqrt n` (integer sqrt) throughout → inequalities are EXACT, not
  asymptotic; the 2 log 4 constant is read off in prose via log(√n) ≈ ½ log n.
* Verify: `cd proofs && LAKE_UNSAFE=1 ./bin/lake env lean Proofs/ChebyshevPNTBridgeOQ06.lean`
  (parent + ChebyshevBounds oleans already present in build/lib/lean/Proofs).

## Dead ends / deferred
* Tighter constants (Chebyshev's 0.921/1.106) need sharper primorial/central-binomial
  estimates — deferred.
* Full PNT π(x) ~ x/log x needs analytic ζ machinery — out of reach here.

## Session 2 (2026-06-28, researcher-6): invert upper density → n·log n lower bound on pₙ

**Mode:** FRESH (problem was SOLVED — deliverable + sandwich OQ-06-OQ-01 already merged).
**Outcome:** new verified follow-up entry `ChebyshevPNTBridgeOQ06OQ02.lean` (158 lines,
3 theorems, **0-sorry 0-axiom**), PR #31282. Marked parent problem `completed`.

Read OQ-06's upper density at the primes themselves to bound the n-th prime
`pₙ = Nat.nth Nat.Prime n` from below:

* `primeCounting_nth_prime`: **π(nth Prime n) = n + 1** — the bridge. `π'(nth Prime n)=n`
  (`Nat.primeCounting'_nth_eq`) and one `Nat.count_succ` increment (justified by
  `Nat.prime_nth_prime`) bump the inclusive count by 1.
* `log_natSqrt_ge`: reproved self-contained (mirrors OQ-06-OQ-01) so the file depends
  ONLY on parent OQ-06, not on OQ-05/OQ-06-OQ-01 (whose oleans weren't built locally).
* `nth_prime_lower_bound`: **pₙ ≥ (n+1)·(½·log(n+2) − log 2)/(2·log 4) ~ n·log n/(4·log 4)**
  for n ≥ 2 — strictly sharper than Mathlib's linear `Nat.add_two_le_nth_prime` (pₙ ≥ n+2).

Key steps: instantiate `primeCounting_mul_log_sqrt_le` at m=pₙ, sub π(pₙ)=n+1, absorb the
`√pₙ·log√pₙ ≤ pₙ·log4` tail (via `log√pₙ ≤ √pₙ` and `log4 ≥ 1`), collapse to
`(n+1)·log√pₙ ≤ 2·pₙ·log4`, then bracket + `pₙ ≥ n+2`.

GOTCHAs / reusable:
* `log 4 ≥ 1` cleanly: `1 = log(exp 1) ≤ log 4` via `Real.exp_one_lt_d9` (exp 1 < 2.72 < 4),
  in `Mathlib.Analysis.Complex.ExponentialBounds` (NOT Log.Basic — needs explicit import).
  `Real.log_two_gt_d9` exists but is `Real.`-namespaced in that same module too.
* `Nat.sqrt_le' p : (Nat.sqrt p)^2 ≤ p` (the `^2` form, not `*`).
* Verify in-worktree: `cd proofs && LAKE_UNSAFE=1 ./bin/lake env lean Proofs/ChebyshevPNTBridgeOQ06OQ02.lean`
  (parent OQ-06 olean present in symlinked main `.lake`; OQ-05/OQ-06-OQ-01 oleans were NOT).

## Open follow-up (next session)
* Invert OQ-05's LOWER density to get `pₙ ≤ C·n·log n`, completing the elementary
  `pₙ ≍ n·log n` sandwich. (Upper bound on pₙ is the harder direction — OQ-05 bound has
  the ⌊m/2⌋ and log(m+1) correction terms.)
