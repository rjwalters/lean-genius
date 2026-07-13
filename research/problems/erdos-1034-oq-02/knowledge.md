# erdos-1034-oq-02 — Beyond the Book Lemma (Erdős #1034)

## Problem

Erdős #1034: a graph on `n` vertices with `> n²/4` edges — must it contain a
triangle `T` with `> (1/2 - o(1))n` vertices each adjacent to ≥2 vertices of `T`?
**No** (Ma–Tang). Bounds on the threshold `h(n)`:

        (1/6 - o(1))·n  ≤  h(n)  ≤  (2 - √(5/2) + o(1))·n ≈ 0.419n.

**OQ-02:** can the `n/6` lower bound — which comes from the **book lemma** — be
improved beyond the book method (e.g. via flag algebras or regularity)? Genuinely open.

## What this entry does (does NOT resolve OQ-02)

Formalizes the lower-bound *mechanism* exactly, axiom-free:

- **`book_le_goodNeighborCount` (general):** if `{a,b}` is an edge and `P` a set of
  common neighbours of `a,b` (disjoint from `{a,b}`), the spine triangle `{a,b,p₀}`
  has `≥ |P| - 1` good neighbours. Proof: every page `q ≠ p₀` is adjacent to both
  `a` and `b` (two of the triangle's vertices), so `P.erase p₀ ⊆ goodNeighbors`;
  `card_erase_of_mem` finishes.
- **`book_goodNeighborCount_eq` / `book_goodNeighbors_eq` (sharp):** for the pure
  book graph on `Fin 5` (spine `{0,1}`, pages `{2,3,4}`, pages pairwise
  non-adjacent), the spine triangle `{0,1,2}` has good neighbours *exactly* `{3,4}`,
  i.e. `= |P| - 1 = 2`. By ordinary `decide` (not `native_decide`), so axiom-free.

**Interpretation:** the book method converts page count into good-neighbour count
one-for-one. `n/6` is exactly the largest book the Turán count guarantees, so any
improvement to `h(n)` must exploit structure the book argument ignores — which is
precisely why OQ-02 is "beyond the book lemma".

## Verification

- File: `proofs/Proofs/Erdos1034OQ02.lean` (194 lines, 4 theorems/lemmas, 10 defs).
- Host-verified against pinned Mathlib 4.26 oleans: 0 errors, 0 warnings, 0 sorries.
- `#print axioms` on all three theorems: only `propext, Classical.choice, Quot.sound`.
  No `sorryAx`, no `Lean.ofReduceBool`. Status **verified**, badge **verified**.

## Lean gotchas captured

- `Symmetric`/`Irreflexive` over a `Fintype` with strict-implicit binders (`⦃⦄`)
  has **no auto `Decidable` instance** — `symm := by decide` fails to synthesize.
  Use `symm := by intro i j h; exact h.symm` (the relation is `Or`-symmetric by
  construction) and `loopless := by intro i; fin_cases i <;> decide`.
- `rw [adjacentCount]` fails ("Failed to rewrite using equation theorems for a
  def"). Use `show 2 ≤ (T.vertices.filter …).card` to unfold the `def` definitionally.
- `Finset.card_pair (h : a ≠ b) : ({a,b}).card = 2`; `a ≠ b` from `hab.ne`
  (`SimpleGraph.Adj.ne`). `(h : G.Adj p a).symm : G.Adj a p`.
- A `SimpleGraph (Fin n)` built from a symmetric edge `List (Fin n × Fin n)` with
  `isEdge i j := (i,j) ∈ base ∨ (j,i) ∈ base` is fully `decide`-friendly for
  `goodNeighbors`/`goodNeighborCount` equalities — keeps the witness 0-axiom.

## Session log

### 2026-06-28 (Session 1) — FRESH

**Mode:** FRESH. **Outcome:** completed (verified, 0-axiom).

- Selected from EMPTY-tier available pool by tractability/value; chose the
  structural-theorem angle over chasing the (open) asymptotic improvement.
- Wrote `Erdos1034OQ02.lean` fresh and self-contained (the existing
  `Erdos1034Problem.lean` is an Aristotle file littered with "failed to load").
- Proved the general book bridge + matching finite sharpness witness; verified
  0-axiom on host.
- Added gallery entry `src/data/proofs/erdos-1034-oq-02/{meta,annotations}.json`.

**Next steps (future sessions, optional):**
- Generalize the sharpness `= |P| - 1` from the `Fin 5` witness to an *abstract*
  pure book graph on any `V` (characterize all good neighbours: isolated vertices
  contribute 0, pages see only the spine).
- Formalize the Turán-count step "(> n²/4 edges) ⟹ (∃ book of size ≥ n/6)" to
  connect this mechanism to the actual `h(n) ≥ n/6` bound.
