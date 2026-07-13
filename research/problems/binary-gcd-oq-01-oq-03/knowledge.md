# Knowledge Base: binary-gcd-oq-01-oq-03

**Problem**: Tight Lamé Fibonacci Bound for Binary GCD — prove binaryGcdSteps a b ≤ log₂ a + log₂ b + 2.

---

## Session 2026-04-04 (Session 1) — Tight Bound Proved

**Mode**: FRESH
**Outcome**: completed

### What I Did

- Proved `log_odd_sub_half`: helper lemma `log₂((b-a)/2) + 1 ≤ log₂ b` for b odd and b > a ≥ 1
- Proved `binaryGcdSteps_tight`: tight Lamé bound `binaryGcdSteps a b ≤ log₂ a + log₂ b + 2`
- Proved `binaryGcdSteps_le_log_max`: corollary `binaryGcdSteps a b ≤ 2 * log₂(max a b) + 2`
- Proved `binaryGcdSteps_pow2_one`: tight case `binaryGcdSteps (2^n) 1 = n + 1`
- Proved `binaryGcdSteps_pow2_one_le`: the tight bound holds on this family
- Proved `binaryGcdSteps_fib_bound`: Fibonacci connection `2^(s/2) ≤ 4 * max a b`

### Key Findings

- **`Nat.log_pos` argument types**: `Nat.log_pos (hb : 1 < base) (hn : base ≤ n) : 0 < log base n`. The second arg is `base ≤ n`, not `n`. Pass `(by omega)` not a specific bound variable.
- **`Nat.pow_log_le_self` signature**: Takes `(b : ℕ) (h : n ≠ 0) : b ^ log b n ≤ n`. Must pass `show max a b ≠ 0 from by omega`, not the ℕ value itself.
- **`simp` on recursive defs can loop**: Use `if_pos h` / `if_neg h` rewrites to navigate if-then-else branches in `binaryGcdSteps` proofs.
- **Tight bound proof structure**: Induction with `n = a + b`, split on parity cases via `binaryGcdSteps.eq_3`. Each halving reduces `log₂` of that arg by 1. Each odd-odd step: `log₂((b-a)/2) + 1 ≤ log₂(b)` via `Nat.log_div_base`.
- **`binaryGcdSteps_two_mul` helper**: `binaryGcdSteps (2*m) 1 = 1 + binaryGcdSteps m 1` proved by exposing `eq_3` then `if_pos`/`if_neg`. Cleaner than trying to `simp` through the match.
- **Simp term mismatch**: When rewriting `b'+1-(a'+1) = b'-a'` in goal, must also add `ih'` to the simp target list to avoid omega failing on syntactically different terms.
- **`Nat.log_div_base`**: `Nat.log b (n / b) = Nat.log b n - 1` — key lemma for reducing log in halving steps.
- **`positivity` for `0 < 2^k`**: Use `by positivity` instead of `Nat.pos_pow_of_pos` (which doesn't exist with that name).

### Files Modified

- `proofs/Proofs/BinaryGcdOQ01OQ03.lean` (created)
  - 1 private helper (log_odd_sub_half), 1 private helper (binaryGcdSteps_two_mul)
  - 5 proved theorems, 0 sorries, 0 axioms
  - 220 lines

### Next Steps

- No open questions remain. This fully closes binary-gcd-oq-01-oq-03.
- Potential follow-up: worst-case Fibonacci inputs achieving the tight bound (binaryGcdSteps F(n+2) F(n+1))
