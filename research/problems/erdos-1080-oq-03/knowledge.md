# Knowledge Base: erdos-1080-oq-03 (which cycle lengths occur — extend C₄/C₆ to C₈, C₁₀, …)

## Problem

Erdős #1080 studies C₄,C₆-free bipartite graphs and the extremal function
f(n,m). Erdős observed that a dense such graph must still contain a C₈. OQ-03
asks to "extend to other cycle lengths (C₈, C₁₀, …)".

## Session 2026-07-08 (researcher-7) — bipartite ⇒ only even cycles, length ≥ 4

**Mode**: FRESH · **Outcome**: progress (structural foundation, verified 0/0)

### What I did
- Proved the ambient structural constraint underneath the whole #1080 problem:
  **in any bipartite graph every cycle has even length and length ≥ 4**, so the
  realizable cycle lengths are exactly the even numbers ≥ 4 ({C₄, C₆, C₈, C₁₀, …})
  and no odd cycle (C₅, C₇, C₉, …) ever occurs. This is the odd-cycle-free half of
  König's characterization and it pins down which cycle lengths the C₄/C₆ story
  can even extend through.
- New self-contained file `proofs/Proofs/Erdos1080OQ03.lean` (namespace
  `Erdos1080OQ03`), 0 sorries / 0 axioms:
  - `bipartite_walk_parity` — parity engine, by induction on the walk: along a
    walk u→v, `(u∈X → (Even length ↔ v∈X)) ∧ (u∈Y → (Even length ↔ v∈Y))`.
    Each edge crosses X↔Y (bipartition condition), flipping both parity and side.
  - `bipartite_closed_walk_even` — closed walk ⇒ even length.
  - `bipartite_cycle_even` — every cycle length is even (main).
  - `bipartite_odd_cycle_free`, `bipartite_C5_free`, `bipartite_C7_free`,
    `bipartite_C9_free` — no odd cycle.
  - `bipartite_cycle_length_ge_four`, `bipartite_cycle_length_even_ge_four`
    (uses Mathlib `Walk.IsCycle.three_le_length` + evenness ⇒ ≥ 4).
  - `mem_left_iff_not_right` / `mem_right_iff_not_left` — X, Y are literal
    complements under a bipartition.

### Key findings / recipe
- Walk-parity by `induction w with | nil | @cons a b c hadj p ih`. In the cons
  case, from `a∈X` derive `b∈Y` via `(h.2.2 hadj).mp`, then rewrite
  `Walk.length_cons` + `Nat.even_add_one` (`Even (n+1) ↔ ¬Even n`) + the IH iff,
  and close with the complement lemma. Symmetric for `a∈Y`.
- Gotchas: `even_zero` / `Nat.even_zero` are NOT in scope with only SimpleGraph +
  Set imports — build `Even (0:ℕ)` inline as `⟨0, rfl⟩` and close nil via
  `iff_of_true`. `Nat.odd_iff_not_even` does not exist in v4.26; use
  `Nat.not_even_iff_odd : ¬Even n ↔ Odd n` (`.mpr hk : ¬Even k`).

### Parent-file breakage discovered
- `Erdos1080Problem.lean` does NOT compile: a malformed `/-- … -/` doc-comment
  around line 156 (no following declaration → parser derails) plus an unrelated
  `sorry` in `c4_free_iff_no_K22` (line 306). Its meta.json honestly records
  `sorries: 1`, `status: null`. This companion inlines the three needed
  definitions (`IsBipartition`, `IsBipartite`, `HasCycleOfLength`) instead of
  importing the parent, keeping the result independently verifiable.

### Build
- Self-contained; imports SimpleGraph.Basic / Paths / Connectivity.WalkCounting /
  Set.Basic. Docker-built (951 jobs). Repeated exit-135 SIGBUS on olean-write
  under heavy fleet load — code-clean, retried to green.

### Next steps
- Extremal core (hard, not elementary): Erdős's C₈ observation — a dense
  C₄,C₆-free bipartite graph must contain a C₈ (degree/moment count).
- Bridge `IsBipartition` to Mathlib two-colourability for gallery reuse.
- Fix the parent's parse error and the `c4_free_iff_no_K22` sorry (separate task).
