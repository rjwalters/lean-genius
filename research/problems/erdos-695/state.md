# Current State

**Phase**: ACTIVE — axiomatized partial formalization
**Since**: 2026-05-13 (STATE-SYNC; prior seeker-init stub from 2026-01-14)
**Iteration**: ≥4 (per `git log` on Lean files: PRs #1054, #8511, #9237, #10379, #15841, #15865)

## Current Focus

Both questions remain mathematically OPEN; Lean formalization captures the
problem statements, the equivalence reformulations (`question1_equiv`,
`erdos_695_main`, `erdos_695_variant`), and the unconditional exponential lower
bound `exponential_lower_bound : p(k) ≥ 2^k` (closed by `chain_step_ge`). Open
gap is the conditional implication `small_prime_conjecture → Question2`.

## Per-File Inventory (as of 2026-05-13)

| File                          | Lines | Theorems | Defs | Axioms | Sorries |
|-------------------------------|-------|----------|------|--------|---------|
| `Erdos695Problem.lean`        | 299   | 8        | 10   | 1      | 1       |
| `Erdos695Aristotle.lean`      | 119   | 0 (13 lemmas) | 2 | 0 | 2       |

> NOTE: gallery JSON `src/data/research/problems/erdos-695.json` carries stale
> `leanFiles[1].lineCount=102` and `leanFiles[1].sorryCount=13` for the
> Aristotle file (actual 119 / 2). That drift is auditor/mechanic territory —
> this state-sync does not touch the gallery JSON.

## Axiom Inventory (1)

1. **`small_prime_conjecture`** (`Erdos695Problem.lean:144`) — Linnik-style
   strengthening: `∃ C > 0, ∀ p prime, ∃ p' prime, p' % p = 1 ∧ p' ≤ p·(log p)^C`.
   Mathematically conjectural (would imply Question 2's quasi-polynomial bound).
   Not provable from Mathlib's current Dirichlet/Linnik content; requires the
   conjectural strengthening of Linnik's constant.

## Sorry Inventory (3)

1. **`conjecture_implies_question2`** (`Erdos695Problem.lean:152`) — derive
   `Question2` from the axiomatized small-prime conjecture. Conceptually:
   greedy chain construction by `Nat.rec`, applying the axiom at each step;
   `o(1)` witness comes from comparing the per-step `log·(log p_i)^C` cost
   against `(k+1)·log(k+1)^(1+o(k))`. Doable but requires careful
   `Asymptotics.IsLittleO` plumbing.

2. **`Erdos695.Aristotle.rpow_tendsto_atTop_iff`** (`Erdos695Aristotle.lean:75`) —
   `(p k)^(1/k) → ∞ ↔ ∀ c>1, eventually p k > c^k`. Already discharged in
   spirit by `Erdos695.question1_equiv` (Problem.lean:83) which proves the
   `c > 0` variant; the Aristotle restatement (`c > 1`, `∀ᶠ`) reduces directly.

3. **`Erdos695.Aristotle.prime_cong_one_exists`** (`Erdos695Aristotle.lean:105`) —
   `∀ p prime, ∃ q prime, q % p = 1`. Already used inside
   `Erdos695.smallestPrimeCongruentOne` (Problem.lean:162) via
   `Nat.forall_exists_prime_gt_and_modEq` + `Nat.coprime_one_left` + a
   `mod_eq_of_lt` rewrite. Extract that 4-line script.

## Forward Levers

- **L1 — Aristotle quick wins (2 sorries):** lemmas (2) and (3) above each
  have an existing in-repo proof to mirror. ~10–20 LOC each. Build cost: full
  `Erdos695Aristotle` rebuild (~3–5 min via docker-build). Suitable for an
  S-ACT discharge PR.

- **L2 — Question 2 conditional (1 sorry, 1 axiom retained):** plumb the
  greedy construction in `conjecture_implies_question2`. Requires:
  `Nat.rec` chain construction returning a `ℕ → ℕ`, witness for
  `IsPrimeChain` (the chain's `StrictMono` follows from `q > p` via
  `Erdos695.Aristotle.smallest_cong_prime_gt`), and an explicit `o(1)`
  function (e.g. `o k = C·log log(k+1) / log(k+1)`). Medium-hard.

- **L3 — Eliminate `small_prime_conjecture` (BLOCKED in math):** would
  require proving the Heath-Brown / Yitang-Zhang style refinement of Linnik's
  constant. Open mathematical problem; not actionable in Lean.

## Active Approach

L1 is the natural next iteration: extracts existing proofs into the Aristotle
companion, reduces total sorries from 3 → 1, and leaves only the substantive
`conjecture_implies_question2` open.

## Blockers

- L3 is mathematically blocked (open conjecture).
- L2 requires care with `Asymptotics.IsLittleO` and `Nat.rec`-based
  construction of a `ℕ → ℕ`. No build/tooling blockers.

## Next Action

S-ACT discharge of `rpow_tendsto_atTop_iff` and `prime_cong_one_exists` in
`Erdos695Aristotle.lean` (Lever L1), reducing total sorries 3 → 1.

## Attempt Counts

- Total attempts: ≥6 (PRs #1054, #8511, #9237, #10379, #15841, #15865)
- Current approach attempts: 0 (L1 not yet attempted as a discharge target)
- Approaches tried (per merged PRs):
  1. Enhancement (#1054 — 2026-01-25)
  2. Question 1 equiv strategy doc (#8511 — 2026-03-30)
  3. Aristotle companion add (#9237 — 2026-04-05)
  4. Axiom elimination + sorry discharge (#10379 — 2026-04-13)
  5. Bulk sorry proofs across 3 slugs incl. erdos-695 (#15841 — 2026-05-04)
  6. Additional bulk proofs (#15865 — 2026-05-04)

## Honesty Block

- This is a doc-only STATE-SYNC PR. No Lean source touched. No gallery JSON
  touched. No build performed (no Lean delta).
- The 3-sorry / 1-axiom count was verified by direct `grep` over the worktree
  Lean source as of 2026-05-13.
- Aristotle JSON drift (`sorryCount=13`, `lineCount=102`) is left for an
  auditor `audit/sync-erdos-695` PR; flagging in the inventory table above.
- Both Erdős questions (1: super-exp lower bound on `p_k^{1/k}`; 2: existence
  of chain with `exp(k·(log k)^{1+o(1)})` upper bound) remain OPEN in
  mathematics. Lean status remains `axiomatized` (badge `axiom`).
