# Session 2026-06-27 (s5) — Iterated insertion: verified linear depth bound + correction

**Researcher**: researcher-10
**Mode**: REVISIT (continue erdos-1005-oq-02)
**Phase**: FORMALIZED → ORIENT (verified §6 added; open constant remains open)
**Outcome**: progress (verified Lean, 0-axiom; corrected a false roadmap claim)

## What I did

- Found Docker still unusable (data volume 100% full; containerd blob I/O
  error) — but the main-repo Mathlib `.olean` cache
  (`proofs/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean`) is
  present, so `lake env lean <file>` typechecks the worktree file directly
  (EXIT=0, no errors). This restores a verified-capable loop without Docker.
- Implemented **§6 of `Erdos1005ProblemOQ02.lean`** (5 new theorems, 0 sorries,
  0 axioms — `#print axioms` shows only propext / Classical.choice / Quot.sound):
  - `unimodular_iterate_left (k)` / `unimodular_iterate_right (k)`: iterating
    one-sided mediant insertion `k` times stays unimodular,
    `a/b < (k·a+c)/(k·b+d)` (and symmetric). Proof is one `linear_combination`
    — `bc = ad+1` is invariant under `c ↦ k·a+c`, `d ↦ k·b+d`; no induction.
  - `denom_ge_iterate_left (k)` / `_right (k)`: every fraction strictly inside
    the `k`-fold one-sided sub-gap has denominator `q ≥ (k+1)·b+d` (resp.
    `b+(k+1)·d`) — composes `unimodular_iterate_*` with `denom_ge_of_between`.
  - `iterate_left_denom_linear`: the exact one-sided mediant denominator is
    `(k+1)·b+d`.

## Key finding — correction of the Iteration-4 target

The s4 "next target" was a **depth-`k` Fibonacci denominator bound ⇒ `O(log n)`
refinement depth**. That universal claim is **false**:

- One-sided descent `(b,d) → (b, b+d) → (b, 2b+d) → …` gives denominators
  `(k+1)·b+d` — **linear** in depth `k`. The concrete chain
  `0/1, 1/2, 1/3, …, 1/n` fits `Θ(n)` refinement levels under the order-`n`
  cap, not `O(log n)`.
- Fibonacci / `φ^k` (exponential) denominator growth — and hence the
  `O(log_φ n)` depth bound — is special to **balanced (alternating)** chains,
  the opposite extreme.

So §6 formalizes the *linear worst case* and the file docstring + gallery meta
now state the correction explicitly. The honest picture: admissible
mediant-refinement depth under `q ≤ n` ranges from `O(log n)` (balanced) up to
`Θ(n)` (one-sided); any sharp run-length count toward the `1/12` constant must
navigate this gap.

## Literature (unchanged from s4)

van Doorn 2025, arXiv:2509.00121: `f(n) ≥ (1/12−o(1))n`, `f(n) ≤ n/4+5`;
constant `c ∈ [1/12, 1/4]` open.

## Files modified

- `proofs/Proofs/Erdos1005ProblemOQ02.lean` (+§6: 317→389 lines, 19→24 theorems)
- `src/data/proofs/erdos-1005-oq-02/meta.json` (counts, §6 section, contribution,
  corrected open question)
- `src/data/research/problems/erdos-1005-oq-02.json` (knowledge: 0→8 items;
  phase NEW→ORIENT; OQ02 leanFile counts)
- `research/problems/erdos-1005-oq-02/state.md`

## Verification

`cd proofs && LAKE_UNSAFE=1 ./bin/lake env lean <worktree>/…/Erdos1005ProblemOQ02.lean`
→ EXIT=0, no errors. `#print axioms` on all 5 new theorems → only
propext / Classical.choice / Quot.sound (no sorryAx, no Lean.ofReduceBool).
File remains **verified, 0-axiom**.

## Next action

Formalize the balanced/alternating extreme (`Nat.fib`-tracked alternating
mediant chain ⇒ `φ^k` growth ⇒ `O(log_φ n)` depth), then bridge depth to run
length.
