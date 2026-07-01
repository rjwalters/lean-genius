# Knowledge Base: cramers-rule-oq-02-oq-01

Insights accumulated during research on this problem.

---

## Problem Understanding

Tighten the parent Cramer-vs-Gauss complexity comparison's loose `n³` Gaussian-elimination
model to the exact textbook flop counts. The forward-elimination multiplication/division
count `(n³ − n)/3`, the additions/subtractions `~n³/3`, and the full leading `~2n³/3` flop
total were formalized in prior sessions (#31414, #31586). The remaining stated open item was
the **back-substitution phase** and its composition into the complete solve cost.

---

## Insights

- **Back-substitution flop count is exactly `n²`** (clean, no truncated subtraction). Solving
  the upper-triangular `U x = b` from the bottom up, the row with `j` solved unknowns to its
  right costs `j` multiplications + `1` division (`backSubOps n = ∑_{j<n}(j+1)`,
  `2·backSubOps = n²+n`) and `j` subtractions (`backSubSubs n = ∑_{j<n} j`,
  `2·backSubSubs + n = n²`). The `n(n+1)/2` and `n(n−1)/2` sum to `n²` exactly
  (`backSubFlops_eq`).
- **Full solve cost** `fullSolveFlops n = gaussExactFlops n + backSubFlops n` has the
  subtraction-free closed form `6·fullSolveFlops n + n = 4n³ + 3n²`, leading term `2n³/3`.
- **Lower-order domination** `backSubFlops_le_gaussFlops` (n ≥ 3): proven by feeding `omega`
  the two component closed forms plus two pre-proved nonlinear bridges as opaque atoms —
  `3·n² ≤ n³` (via `calc … ≤ n·n² := by gcongr; _ = n³ := by ring`) and `n ≤ n²` (via
  `Nat.pow_le_pow_right`). omega then does the purely linear combination over the atoms
  `n, n², n³`.
- **Comparison preserved**: `fullSolveFlops n ≤ n³` for `n ≥ 2` (needs the bridge
  `3·n² ≤ 2·n³`, again `gcongr; omega`), so `fullSolve_beats_cramer` (n ≥ 4) follows a
  fortiori from the parent's `gauss_beats_cramer` — exactly the same "smaller cost can't
  overturn the verdict" pattern used for `gaussExact_beats_cramer`.

## Reusable techniques

- **Subtraction-free additive closed forms** (`k·sum + remainder = polynomial`) keep the
  induction in the ℕ semiring so plain `ring` closes the successor step; the conventional
  division form is a one-line corollary. Same recipe as the parent gaussExactOps work.
- **omega + nonlinear bridges**: to compare cubic/quadratic quantities, pre-prove the
  needed `a·n² ≤ b·n³` / `n ≤ n²` facts with `gcongr` (side goals discharged by `omega`/
  assumption), then hand them to `omega`, which treats `n, n², n³` as independent atoms.

---

## Dead Ends

- Trying to prove the domination/`≤ n³` inequalities with `omega` alone fails — omega cannot
  relate `n²` and `n³` without an explicit bridge lemma. `nlinarith` is also unreliable here
  because `n³` is an opaque atom unless the `n³ = n·n²` relation is supplied; `gcongr`+`ring`
  is the robust route.

---

## Session log

- **2026-06-30 (researcher-3)**: Added the back-substitution + full-solve section to
  `CramersRuleOQ02OQ01.lean` (now 333 LOC, 25 thm/lemma, 7 def, 0 axiom, 0 sorry, no
  native_decide). Completes the stated open item. Verified via host `lake env lean`
  (docker down); `#print axioms` shows only propext/Classical.choice/Quot.sound.
