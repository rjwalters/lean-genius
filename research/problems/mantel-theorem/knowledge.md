# Knowledge Base: mantel-theorem

Insights accumulated during research on this problem.

---

## Problem Understanding

Mantel's theorem (1907): a triangle-free (`K₃`-free, i.e. `CliqueFree 3`) simple graph
on `n` vertices has at most `⌊n²/4⌋` edges, attained by the balanced complete bipartite
graph. It is the `r = 2` base case of Turán's theorem.

---

## Insights

### M1 (researcher-6, 2026-06-15) — SOLVED via Mathlib Turán specialization (BUILD GREEN)

- **Mathlib already provides the general Turán edge bound.** The Turán development lives in
  `Mathlib/Combinatorics/SimpleGraph/Extremal/Turan.lean` (the old
  `Mathlib.Combinatorics.SimpleGraph.Turan` is now a `deprecated_module` redirect since
  2025-08-21). The load-bearing lemma is

      SimpleGraph.CliqueFree.card_edgeFinset_le (cf : G.CliqueFree (r + 1)) :
        let n := Fintype.card V;
        #G.edgeFinset ≤ (n ^ 2 - (n % r) ^ 2) * (r - 1) / (2 * r) + (n % r).choose 2

  Specializing at `r = 2` and simplifying the RHS to `⌊n²/4⌋` IS Mantel's theorem. No new
  graph theory required — the only real work is the closing arithmetic identity.

- **The arithmetic identity `turan_two_simp`:**
  `(n² − (n%2)²)·(2−1)/(2·2) + (n%2).choose 2 = n²/4`.
  Two facts close it: (1) the binomial term vanishes since `n%2 < 2 ≤ 2`
  (`Nat.choose_eq_zero_of_lt`); (2) `n² = 4·((n/2)² + (n/2)·(n%2)) + (n%2)²` (proved by
  `conv_lhs => rw [← Nat.div_add_mod n 2]; ring`), and `(n%2)² < 4`, so `omega` finishes
  `(n² − (n%2)²)/4 = n²/4` by abstracting `n²`, `(n%2)²`, `(n/2)²`, `(n/2)·(n%2)` as atoms.

- **Sharpness is free.** `turanGraph n 2` is triangle-free (`turanGraph_cliqueFree (0<2)`)
  and has exactly `⌊n²/4⌋` edges (`card_edgeFinset_turanGraph` + `turan_two_simp`). Packaged
  as `mantel_bound_is_tight`.

- **Gotchas:**
  - `r` is implicit in `CliqueFree.card_edgeFinset_le`; pass `(r := 2)` and supply
    `h : G.CliqueFree 3` directly — `3` and `2+1` are defeq for Nat literals.
  - The conclusion is wrapped in `let n := Fintype.card V; …`. A `calc` first step against
    the explicit (let-free) RHS mis-parses / fails to match; `exact le_trans hb
    (le_of_eq (turan_two_simp _))` reduces the `let` by `whnf` and works.

---

## Dead Ends

- A from-scratch AM–GM / degree-sum proof (the textbook route) was deemed unnecessary once
  the Mathlib Turán specialization was confirmed to compile; not attempted.

---

## Open Follow-ups

- **Equality characterization** (equality `#E = ⌊n²/4⌋` ⟺ `G ≅` balanced complete bipartite
  graph) is reachable from `SimpleGraph.isTuranMaximal_iff_nonempty_iso_turanGraph` but not
  yet packaged. This is the natural M2 target.
