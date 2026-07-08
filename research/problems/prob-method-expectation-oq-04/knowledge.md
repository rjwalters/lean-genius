# Knowledge Base: prob-method-expectation-oq-04

OQ-04 asks to strengthen `expected_mono_cliques` to `E(n,k) < 1` for `n < 2^(k/2)` — the
Erdős 1947 diagonal Ramsey lower bound `R(k,k) > 2^(k/2)`.

## Current state (verified, #31500)

`ProbMethodExpectationOQ04.lean` (0-axiom / 0-sorry) already:
- defines `expectedMonoCliques n k = C(n,k) · 2^(1 - C(k,2))`;
- **reduces** `E < 1` to a pure ℕ-power inequality:
  `expectedMonoCliques_lt_one_iff : expectedMonoCliques n k < 1 ↔ (C(n,k):ℚ)·2 < 2^(C(k,2))`;
- records the first-moment upper bound `E ≤ (n^k/k!)·2^(1-C(k,2))` via `Nat.choose_le_pow_div`.

The file's docstring flags the power inequality as "the clean target a later session (or
Aristotle) must discharge."

## Precise, self-contained target (researcher-2, 2026-07-08)

The `n < 2^(k/2)` hypothesis is fiddly (half-integer exponent). It is **equivalent to the
clean ℕ statement `n^2 < 2^k`** (square both sides). So OQ-04 reduces to proving:

```lean
theorem erdos_1947_clique_bound (n k : ℕ) (hk : 3 ≤ k) (hn : n ^ 2 < 2 ^ k) :
    2 * (n.choose k) < 2 ^ (k.choose 2)
```

which, via `expectedMonoCliques_lt_one_iff` (cast to ℚ), gives `expectedMonoCliques n k < 1`
and hence (strict first-moment principle) a 2-colouring of `Kₙ` with no monochromatic
`k`-clique, i.e. `R(k,k) > n`. **This statement is TRUE** (spot-checked k=3,4,5,6,10) and
entirely in ℕ.

### Proof route (all ℕ, no half-integers)
1. `C(n,k) ≤ n^k / k!`  (`Nat.choose_le_pow_div`), so `2·C(n,k) ≤ 2·n^k/k!`.
2. `n^2 < 2^k ⟹ n^k < 2^(k*k/2)` (raise to the `k`; `(n^2)^k < (2^k)^k = 2^(k^2)`, and
   `n^(2k) = (n^k)^2`, `2^(k^2) = (2^(k*k/2))^2` when `k` even / handle `k` odd via `k*(k-1)`).
   Cleanest: compare **squares** to stay in ℕ — prove `(2·C(n,k))^2 < (2^(C(k,2)))^2`.
3. Key growth fact `2^(k+2) ≤ (k!)^2` for `k ≥ 3` (induction on `k`; base `k=3`: `2^5=32 ≤ 36`).
4. Combine: `(2·C(n,k))^2 ≤ 4·n^(2k)/(k!)^2 < 4·2^(k^2)/(k!)^2` and
   `(2^(C(k,2)))^2 = 2^(k(k-1)) = 2^(k^2-k)`, reducing to `2^(k+2) ≤ (k!)^2`.

### Discharge options
- **Aristotle** on `erdos_1947_clique_bound` (submitted 2026-07-08, backend returned
  "Resource not found" — retry when the Aristotle service is back up).
- A direct Lean proof following the square-comparison route above (~50–100 lines; the
  factorial growth lemma `2^(k+2) ≤ (k!)^2` is the main sub-lemma).

## Blocker note
Attempted to queue this on Aristotle 2026-07-08; MCP tool loaded but backend down
("Resource not found"). Direct Lean proof deferred (infra had transient exit-135/SIGBUS
cache corruption this session).

## RESOLVED (researcher-2, 2026-07-08)

The clean ℕ target set out above is now **proved** in
`ProbMethodExpectationOQ04.lean` (VERIFIED, 0 axioms, 0 sorries, no `native_decide`):

- `erdos_1947_clique_bound (hk : 3 ≤ k) (hn : n^2 < 2^k) : 2 * n.choose k < 2^(k.choose 2)`
- `expectedMonoCliques_lt_one_of_sq_lt (hk : 3 ≤ k) (hn : n^2 < 2^k) : expectedMonoCliques n k < 1`

This closes OQ-04: the expected number of monochromatic `k`-cliques is `< 1` whenever
`n² < 2^k` (⟺ `n < 2^(k/2)`), which is the Erdős 1947 diagonal Ramsey lower bound
`R(k,k) > n`.

### Proof (square-comparison, all ℕ)
1. `C(n,k)·k! ≤ nᵏ` via `Nat.descFactorial_eq_factorial_mul_choose` + `Nat.descFactorial_le_pow`.
2. Growth lemma `2^(k+2) ≤ (k!)²` for `k ≥ 3` (`Nat.le_induction`, base `2⁵=32 ≤ 36=(3!)²`).
3. Identity `2·C(k,2) + k = k²` (induction via `Nat.choose_succ_succ'`).
4. Multiply the target square through by `(k!)²`: `(2·C(n,k))²·(k!)² = 4·(C·k!)² ≤ 4·n^{2k}
   = 4·(n²)ᵏ < 4·(2ᵏ)ᵏ = 2^{k²+2} = 2^{2·C(k,2)}·2^{k+2} ≤ (2^{C(k,2)})²·(k!)²`, then
   `lt_of_mul_lt_mul_right` and `lt_of_pow_lt_pow_left₀`.

Build: first try, 7743 jobs, `#print axioms` = `[propext, Classical.choice, Quot.sound]` only.

## Follow-up: explicit unconditional witness (researcher-1, 2026-07-08)

`erdos_1947_clique_bound` / `expectedMonoCliques_lt_one_of_sq_lt` are *conditional*
(they need an `n` with `n² < 2^k`). Added the **explicit-witness / unconditional** form
that textbooks actually cite:

```lean
theorem expectedMonoCliques_lt_one_pow {k : ℕ} (hk : 3 ≤ k) :
    expectedMonoCliques (2 ^ ((k - 1) / 2)) k < 1
```

i.e. the diagonal Ramsey lower bound `R(k,k) > 2^⌊(k-1)/2⌋` (Erdős 1947). Proof: the
witness `n = 2^⌊(k-1)/2⌋` satisfies `n² = 2^{2⌊(k-1)/2⌋} < 2^k` because
`2·⌊(k-1)/2⌋ ≤ k-1 < k` (`omega`), then `Nat.pow_lt_pow_right`; feed into
`expectedMonoCliques_lt_one_of_sq_lt`. VERIFIED 0 axioms / 0 sorries, no `native_decide`.
Also corrected stale meta counts (lineCount 84→235, theoremCount 6→13; these lagged the
OQ-04 resolution content).
