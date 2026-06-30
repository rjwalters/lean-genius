# Knowledge: prob-method-expectation-oq-04

## Established Facts

(None yet — populated during OBSERVE.)

## Open Questions Within This Problem

- The main open question (see `problem.md`).

## Failed Approaches

(None yet.)

## Promising Leads

(None yet.)

## Session 2026-06-28 (researcher-3) — Erdős <1 reduction stepping stones [OBSERVE/ORIENT]

**Mode**: OBSERVE→ORIENT. The problem.md question is the Erdős 1947 strengthening
("strengthen `expected_mono_cliques` to show the count is `< 1` for `n < 2^(k/2)`"); the
parent `ProbMethodExpectation.expected_mono_cliques` only proves the count `≥ 0` (trivial)
and `erdos_ramsey_lower_bound` is a VACUOUS existence (`∃ n, n ≥ 2^(k/2)`), not the
probabilistic-method bound. The full `< 1` proof is a hard multi-session formalization
(needs `C(n,k) ≤ n^k/k!`, a `k!` growth bound, and exponent arithmetic complicated by the
ℕ floor division in `2^(k/2)`). This session delivered verified **reductions**, not the
full bound.

### Delivered (in `ProbMethodExpectationOQ04.lean`, 83→129 L, 0-axiom)
- `expectedMonoCliques (n k) := (n.choose k : ℚ) * 2^(1 - (k.choose 2 : ℤ))` — names the
  parent's expected count.
- **`expectedMonoCliques_lt_one_iff`**: `E(n,k) < 1 ↔ (n.choose k : ℚ)*2 < 2^(k.choose 2)`.
  Eliminates the integer `zpow`; the RHS is a clean ℕ-power inequality — the exact target a
  future session / Aristotle must discharge.
- **`expectedMonoCliques_le`**: `E(n,k) ≤ (n^k/k!)·2^(1-C(k,2))` via `Nat.choose_le_pow_div`.
  Reduces OQ-04 to the elementary estimate `n^k·2 < k!·2^{C(k,2)}`.

### Key Mathlib API found
- `Nat.choose_le_pow_div (r n : ℕ) : (n.choose r : α) ≤ (n^r : α)/r!` (ordered field α).
- zpow split: `zpow_add₀ (h : a ≠ 0)`, `zpow_one`, `zpow_neg`, `zpow_natCast`; then
  `div_lt_one (hpos)` to turn `X/Y < 1` into `X < Y`.

### Remaining (the real crux)
Prove `(n.choose k : ℚ)*2 < 2^(k.choose 2)` (equiv. `n^k·2 < k!·2^{k(k-1)/2}`) under
`n < 2^(k/2)`, `k ≥ 3`. The crude `C(n,k) ≤ n^k` is too weak (fails for even k); must use
`C(n,k) ≤ n^k/k!` and `k! > 2^{1+k/2}`. Watch: `2^(k/2)` uses ℕ floor division → `n^k <
2^{k·⌊k/2⌋}`, NOT `2^{k²/2}`. Good Aristotle candidate once stated purely in ℕ.

### Note
The json `formalStatement` (non-strict averaging "some outcome meets the mean") was ALREADY
fully proved & 0-axiom in this file (exists_ge_average etc.); the problem.md Ramsey question
is the genuinely open one and is what this session targets.
