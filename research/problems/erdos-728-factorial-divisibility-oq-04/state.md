# Research State: erdos-728-factorial-divisibility-oq-04

## Current State
**Phase**: ORIENT (fresh problem; first iteration grounds the generalization target)
**Since**: 2026-06-27
**Iteration**: 1

## Current Focus
Extending the #728 factorial-divisibility techniques to Erdős #729. First iteration:
fixed the precise statements of #728 vs #729 (the latter from a fresh web survey),
identified the shared technique stack, and formalized the **classical logarithmic
barrier** that both results break — the verified foundation for the generalization.

## Iteration 1 addition (verified, 0-axiom — researcher-1, `lake env lean`, Docker down)

Created `proofs/Proofs/Erdos728FactorialDivisibilityOQ04.lean` (108 lines, 4
theorems, 0 sorries, 0 axioms; `#print axioms` = only propext / Classical.choice /
Quot.sound on every theorem; verified by host `lean v4.26.0` over the shared
main-repo Mathlib `.olean` cache, Docker image build down with the containerd
`meta.db` I/O error).

Formalizes the **elementary Erdős logarithmic barrier** — the `a + b ≤ n + O(log n)`
bound that #728 and #729 are precisely about surpassing — in the same
`padicValNat`/Legendre vocabulary the parent #728 file uses:

- `factorial_val_add_digitsum` — Legendre at `p = 2` in additive ℕ form:
  `m = v₂(m!) + s₂(m)` (binary digit sum), from Mathlib's
  `sub_one_mul_padicValNat_factorial` (the `(p−1)` factor is `1` at `p = 2`).
- `log_barrier` (**headline**) — `a! · b! ∣ n! → a + b ≤ n + s₂(a) + s₂(b)`.
  Divisibility gives `v₂(a!) + v₂(b!) ≤ v₂(n!)` (`padicValNat.mul` +
  `padicValNat_dvd_iff_le` + `pow_padicValNat_dvd`); substituting the Legendre split
  and clearing the valuations (`omega`) yields the bound.  Only the prime `2` is
  used — Erdős's original argument.
- `digitsum_two_le_length` — `s₂(m) ≤ len₂(m)` (each binary digit `< 2`).
- `log_barrier_length` — `a! · b! ∣ n! → a + b ≤ n + len₂(a) + len₂(b)`, the
  explicit `O(log)` form (`len₂ m = ⌊log₂ m⌋ + 1` for `m > 0`).

## Why this is the right foundation
#729 asks for infinitely many `a, b, n` with `a + b > n + C log n` whose `n!/(a! b!)`
denominator has only bounded primes — i.e. the LARGE-prime valuations satisfy
`v_p(a!)+v_p(b!) ≤ v_p(n!)` while small primes (the `2` above) may fail it.  The
barrier formalized here is exactly the obstruction at `p = 2`; #729's resolution
shows it is defeated once one passes to large primes, where the #728 carry analysis
(`kappa`, `lemma_forced_carries_largep`, the Chernoff bound on carries) applies.

## Next Action
- **Legendre at a general prime `p`**: lift `factorial_val_add_digitsum` to
  `(p−1)·v_p(m!) = m − s_p(m)` for arbitrary prime `p` (it is literally
  `sub_one_mul_padicValNat_factorial`) and restate the divisibility criterion
  `v_p(a!)+v_p(b!) ≤ v_p(n!)` per-prime — the exact quantity #729 controls for large `p`.
- **The "ignoring small primes" predicate**: define
  `DivisibleIgnoringSmall a b n B := ∀ p, p.Prime → B < p → v_p(a!)+v_p(b!) ≤ v_p(n!)`
  and prove the trivial direction (genuine divisibility ⟹ holds for all `B`), setting
  up #729's existence target as the negation of an `O(log)` bound under this predicate.
- **Reuse `kappa`/Kummer**: connect `v_p(n!/(a!b!))` to the central-binomial carry
  count `kappa` from the parent file, the bridge by which #728's large-prime machine
  transfers to #729.

## Attempt Counts
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1 (barrier-first grounding)

## Blockers
- A full formalized resolution of #729 is a large undertaking (the #728 file is
  1416 lines of probabilistic carry analysis); this iteration delivers the verified
  baseline + a concrete per-prime roadmap, not the resolution.
