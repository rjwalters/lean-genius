# Session 2026-09-29 S11 — general-`k` unwind: the Erdős–Rado recursive majorant

**Agent**: researcher-2
**Mode**: ACT (REVISIT, RICH depth-first claim)
**Base**: branch `research/erdos-szekeres-oq03-s10-rebased` (PR #43789, S9+S10) —
this session's PR supersedes it (same lineage, superset).

## Mathematical finding (negative + positive)

The S4/S11 plan in state.md hoped the unwind of `ramseyNumber_succ_le` would
give the classical tower bound `R_k(s,s) ≤ twr_{k-1}(c_k·s)`. **It cannot**:
at uniformity `k+1` the recursion is applied once per unit of `s+t`, and each
application feeds the (already exponential) level-`k` bound with the previous
inner value — a fixed uniformity costs tower height `≈ s+t`, not one
exponential. The height-`(k−1)` tower requires the genuinely different
Erdős–Rado 1956 tree/ramification argument
(`R_k(s,t) ≤ 2^{C(R_{k-1}(s-1,t-1), k-1)} + k − 1`). Registered as a
structured blocked route.

What the recursion honestly yields — and what S11 delivers — is the
**Ackermann-shaped majorant**:

```
erdosRadoBound 0 m = 2^m
erdosRadoBound (j+1) 0 = 1
erdosRadoBound (j+1) (m+1) = erdosRadoBound j (2·erdosRadoBound (j+1) m) + 1
```

with **`ramseyNumber_le_erdosRadoBound : R_{j+2}(s,t) ≤ erdosRadoBound j (s+t)`**
for all `j` and `s,t ≥ j+2` — an explicit, everywhere-defined computable
upper bound at every uniformity, completing OQ-03b's quantitative layer.

## Proof structure

Outer induction on the level `j` (base: `ramseyNumber_two_le_choose`
coarsened by `Nat.choose_le_two_pow`); inner fuel induction on `s+t`
(boundary rows `s = j+3` / `t = j+3` collapse via
`is_ramsey_self_right`/`left` + `le_erdosRadoBound`; interior = one
`ramseyNumber_succ_le` step, inner values certified `≥ j+2` by
`min_le_ramseyNumber`, bounded by the inner IH, aligned by
`erdosRadoBound_mono`). Supporting lemmas: `le_erdosRadoBound`
(`m ≤ B j m`, mutual lexicographic recursion), `erdosRadoBound_le_succ`,
`erdosRadoBound_mono`, plus the diagonal form
`ramseyNumber_self_le_erdosRadoBound : R_k(s,s) ≤ B (k−2) (2s)`.

## Lean gotchas (v4.31)

- WF-recursion equation lemmas introduce `m+1−1` residue — add
  `Nat.add_sub_cancel` to the `simp only [erdosRadoBound, …]` set.
- `omega` treats `j+2+1` and `j+3` as distinct atoms: restate hypotheses at
  the canonical numeral by defeq (`have hrec' : … (j+3) … := hrec`), and
  `show ramseyNumber 2 …` before omega when the goal carries `0+2`.
- `Nat.lt_two_pow_self` is projection-style (`m.lt_two_pow_self`); the
  `erdosRadoBound 0` case still needs `simpa [erdosRadoBound]` since WF
  defs don't unfold by rfl.
- Ackermann-shaped `def` + mutual-shape `theorem` by pattern matching both
  pass the automatic lexicographic termination checker — no
  `termination_by` needed.

## Build

`./proofs/scripts/docker-build.sh Proofs.RamseyHypergraph` — Build completed
successfully (8576 jobs). File 1133 → 1309 LOC, 30 → 35 theorems + 1 def,
0 sorries, 0 axioms, no native_decide.

## Next

- OQ-03c: Erdős–Hajnal stepping-up lower bound (S-up-4 PREP notes) — the
  deep half.
- Or: the Erdős–Rado 1956 tree argument as its own major rung (would unlock
  the true height-`(k−1)` tower and reopen the blocked route).
