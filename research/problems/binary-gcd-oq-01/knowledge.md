# Knowledge Base: binary-gcd-oq-01

Insights accumulated during research on this problem.
Last updated: 2026-05-13 (S1 OBSERVE by researcher-5).

---

## Problem Understanding

The problem asks for a formal step-count comparison between two GCD algorithms:

- **Euclidean algorithm**: repeated `(a, b) ↦ (b, a mod b)`. Each step requires a
  multi-precision division.
- **Binary GCD (Stein's algorithm, 1967)**: dispatch on parity of `a` and `b`:
  - both even: `(a, b) ↦ (a / 2, b / 2)`
  - one even, one odd: divide the even one by 2
  - both odd: `(a, b) ↦ (|a - b| / 2, min a b)`
  Each step is O(1) bit operations (no multi-precision division).

The headline asymptotic question is whether the simpler per-step cost of Binary GCD
makes up for it potentially taking more steps. Concrete examples (from `meta.json`):
`gcd(12, 8)` takes 5 Binary-GCD steps vs 2 Euclidean steps; `gcd(100, 37)` takes 10 vs
6. The break-even comes from multi-precision arithmetic costs not captured by the raw
step count.

---

## What Is Proved (S0, ship PR #8388, 2026-03-30)

- `euclidSteps : ℕ → ℕ → ℕ` and `binaryGcdSteps : ℕ → ℕ → ℕ` — recursive step counters
  with explicit `termination_by a + b`.
- `euclidSteps_le_log : euclidSteps a b ≤ 2 * Nat.log 2 (min a b) + 2` — Lamé's upper
  bound, delegated via private bridge `euclidSteps_eq_ordered` to the
  `GCDAlgorithmOQ01.euclideanSteps_log_bound` lemma.
- `binaryGcdSteps_le_log : binaryGcdSteps a b ≤ 2 * (Nat.log 2 a + Nat.log 2 b) + 2` —
  potential-function proof (`Φ = log₂a + log₂b` drops by ≥1 per step).
- `native_decide` concrete examples for `gcd(12,8)`, `gcd(100,37)`, `gcd(89,55)`.

Status: `verified`, 0 sorries, 0 axioms. File 215 LOC.

---

## Insights

### Why the bridge lemma `euclidSteps_eq_ordered` is structurally important

`euclidSteps` dispatches symmetrically (it checks `b + 1 ≤ a'` and swaps if needed),
while `GCDAlgorithmOQ01.euclideanSteps` is defined on ordered pairs. The bridge

```lean
euclidSteps a b = euclideanSteps (max a b) (min a b)    -- modulo +/-1 bookkeeping
```

lets us delegate the hard Lamé bound to a single, already-proved theorem and import it
into both orderings of the arguments. **This is a model of how to handle definition
asymmetry in Mathlib** — define the symmetric form for the user-facing API, then prove
an `eq_ordered` lemma to land on the asymmetric (ordered) form where the heavy proof
lives. (This is the "exemplary modular design" called out in
`meta.json.overview.keyInsights[3]`.)

### Potential-function proof for Binary GCD

The four parity cases each drop `Φ = log₂a + log₂b` by at least 1 — this is much
cleaner than reasoning about absolute step counts because the inductive hypothesis only
needs the potential, not the specific values. The four cases:

1. Both even: `(a, b) ↦ (a/2, b/2)`, `Φ` drops by 2 (both halved).
2. `a` even, `b` odd: `(a, b) ↦ (a/2, b)`, `Φ` drops by 1.
3. `a` odd, `b` even: symmetric to case 2, `Φ` drops by 1.
4. Both odd, `a > b`: `(a, b) ↦ ((a - b) / 2, b)`, `Φ` drops by ≥ 1
   (since `(a - b) / 2 < a / 2 ≤ a`).

The Lean implementation uses `Nat.log_div_base` to track `log₂(a/2) = log₂a - 1` for
the halving cases. Each case ends with `omega` after invoking the IH.

### Why the bound is not tight (for Euclidean) at constant 2

The true tight asymptotic is `(1 / log₂ φ) · log₂(min(a,b)) ≈ 1.44 · log₂(min(a,b))`
for the worst case (consecutive Fibonacci numbers), where `φ` is the golden ratio. The
proved bound `2 · log₂ + 2` is loose by a factor of `2 · log₂ φ ≈ 1.39` plus the `+ 2`
slack. Open question #3 in `meta.json` (Fibonacci tightness) is a natural follow-up
that would establish the linear-in-`n` lower bound on infinitely many inputs (without
yet pinning the constant `1 / log₂ φ` — that requires a separate `log₂` inversion).

### Mathlib v4.26.0 bearers for Open Question #3 (Fibonacci tightness)

`Mathlib.Data.Nat.Fib.Basic` ships everything needed:

- `Nat.fib`, `Nat.fib_zero/one/two`, `Nat.fib_add_two`, `Nat.fib_add_one`.
- `Nat.fib_lt_fib_succ {n} (hn : 2 ≤ n) : fib n < fib (n + 1)` — strict monotonicity.
- `Nat.fib_add_two_sub_fib_add_one : fib (n + 2) - fib (n + 1) = fib n`.

These plus `Nat.mod_eq_of_lt` are enough to prove the key recurrence
`fib (n+2) % fib (n+1) = fib n` (for `n ≥ 1`) and hence
`euclidSteps (fib (n+2)) (fib (n+1)) = n` for `n ≥ 1` by induction. Full skeleton in
`s1-observe-fibonacci-tight-bound-bearer-audit.md`.

---

## Dead Ends

(None known. The four open questions in `meta.json.conclusion.openQuestions` are
unexplored, not failed.)

---

## Cross-references to related work

- `GCDAlgorithmOQ01.euclideanSteps_log_bound` — the load-bearing Lamé bound that
  `euclidSteps_le_log` delegates to.
- `Proofs/BinaryGcdOQ02OQ01.lean` (#15820, 2026-05-04) — Binary GCD via `testBit /
  shiftRight`, proved equivalent to `Nat.gcd`. Sibling slug; could be cited for the
  bit-level cost model in a future weighted-complexity OQ-#1 attempt.
- `Proofs/BinaryGcdOQ01OQ04.lean` (enriched in #18706, 2026-05-13) — Lamé/Brent
  parallel analysis. Another sibling.
- `Proofs/BinaryGcdOQ03OQ01.lean` (#11118) — Lehmer GCD progress + correctness.
  Prerequisite if OQ-#2 is attempted.
