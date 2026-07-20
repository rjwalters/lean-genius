# Knowledge Base: erdos-85-wip-01

## Session 2026-07-20 (researcher-1) — upper bound f(n) ≤ n-1 + full-degree ⟹ complete

Added 2 axiom-free lemmas to `Erdos85Problem.lean` (host-verified v4.31.0, `#print axioms` =
propext/Classical.choice/Quot.sound; theoremCount 11→13, lineCount 259→300):

- `eq_top_of_minDegree_ge` — on `Fin n`, `minDegree ≥ n-1` forces `G = ⊤`. Proof: `deg i =
  card (neighborFinset i)`, and `neighborFinset i ⊆ univ.erase i` (card `n-1`); `deg i ≥ n-1`
  + `Finset.eq_of_subset_of_card_le` ⟹ `neighborFinset i = univ.erase i`, so `i` is adjacent
  to every `j ≠ i`.
- `minDegreeForC4_le_sub_one` — `f(n) ≤ n-1` for `n≥4` via `Nat.sInf_le`: `minDegree ≥ n-1`
  ⟹ `G = ⊤` ⟹ `containsC4` (`completeGraph_containsC4`). Bonus: the threshold set is
  non-empty, so `f(n)` is a genuine minimum (not the junk `sInf ∅ = 0`).

Crude vs the true `f(n)=(1+o(1))√n` (needs Kővári–Sós–Turán, beyond Mathlib) but the first
honest bound tying the `sInf` definition to the structural `completeGraph_containsC4`.

### API used
`SimpleGraph.card_neighborFinset_eq_degree`, `minDegree_le_degree`, `mem_neighborFinset`,
`ne_of_adj`, `top_adj`, `Finset.card_erase_of_mem`, `Finset.eq_of_subset_of_card_le`,
`Nat.sInf_le`. The set membership binder `∀ G [DecidableRel G.Adj], …` is entered by `intro G _`.


Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]

---

## Session note (2026-07-20, researcher-1): 7 axiom-free foundational lemmas

`Erdos85Problem.lean` (min degree for C₄) was a definitions-only stub (7 defs, 0 theorems).
Added 7 axiom-free lemmas (host-verified, Lean v4.31.0; `#print axioms` =
propext/Classical.choice/Quot.sound): the four C₄ cycle edges (`C4_adj_*`), a diagonal
non-edge (`C4_not_adj_zero_two`), `containsC4_mono` (a C₄ copy survives adding edges), and
**`starGraph_not_containsC4`** — the star K_{1,n} is C₄-free (its two disjoint cycle-edges
0–1 and 2–3 would force two distinct cycle-vertices onto the centre, contradicting
injectivity). Note: `decide` fails on `C4.Adj 0 1` (structure-literal Adj field lacks a
Decidable instance) — use `by simp [C4]`. Deep results (asymptotics, f(4)=2, Ramsey
connection) remain documented-only. Meta synced (theoremCount 0 → 7, lineCount 184 → 230).
