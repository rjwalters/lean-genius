# Erdős #736 — Chromatic Numbers and Finite Subgraph Inheritance

**Source:** https://erdosproblems.com/736
**Status:** OPEN (Taylor's conjecture; consistency/independence results known)

## Problem Summary

Let `G` be a graph with chromatic number ℵ₁. Taylor's conjecture asks: is there,
for every cardinal `m`, a graph `G_m` of chromatic number `m` such that every
finite subgraph of `G_m` is a subgraph of `G`?

Komjáth–Shelah (2005) showed it is **consistent with ZFC** that the answer is NO,
so the conjecture is independent of ZFC and cannot be proved outright in Lean.
The achievable goal is to formalize the problem precisely and verify the supporting
finite-subgraph / compactness infrastructure that the problem is built around.

## Verified Results (machine-checked)

- **`deBruijn_erdos_coloring`** — the de Bruijn–Erdős coloring theorem: if every
  finite subgraph of `G` is `n`-colorable then `G` is `n`-colorable. Proved via
  Mathlib's compactness lemma `SimpleGraph.nonempty_hom_of_forall_finite_subgraph_hom`
  applied with target `completeGraph (Fin n)`. Depends only on
  `propext` / `Quot.sound` / `Classical.choice`.
- **`exists_finite_subgraph_not_colorable`** — contrapositive form: if `G` is not
  `n`-colorable, some *finite* subgraph already is not `n`-colorable. Short
  consequence of the above (`by_contra` + `push_neg`). This is the form most
  directly relevant to #736: the obstruction to a small coloring always lives in a
  finite part of the graph.

## Open / unformalized side result

- **`finite_case`** (1 `sorry`): for finite chromatic number `k`, every `m ≤ k`
  is realized as a subgraph of `G`, so inheritance is automatic.
  - **Proof sketch (true, not deep):** take `H` to be an induced subgraph of `G`
    with `χ(H) = m`. Any finite subgraph of an induced subgraph of `G` is a finite
    subgraph of `G`, so inheritance is free. Existence of an induced subgraph of
    chromatic number exactly `m` follows from the **discrete intermediate-value
    principle**: deleting vertices one at a time lowers the chromatic number by at
    most one, so as we delete down to the empty graph (`χ = 0`) the value passes
    through every `m` with `0 ≤ m ≤ k`.
  - **Why still `sorry`:** the file uses a custom `Cardinal`-valued
    `chromaticNumber` (not Mathlib's `ℕ∞`-valued `SimpleGraph.chromaticNumber`), so
    the "one vertex deletion changes χ by ≤ 1" lemma must be built from scratch
    (~150–250 lines). It is a self-contained side lemma, **not** part of the open
    conjecture, so it is deferred.

## Mathlib gaps

- Custom `Cardinal`-valued chromatic number has no Mathlib lemmas; Mathlib's
  `SimpleGraph.chromaticNumber : ℕ∞` is the only available API and does not cover
  the cardinal-valued infinite setting used here.
- No "vertex-deletion intermediate value" lemma for chromatic number in Mathlib.

## Next Steps

1. Build-verify the file and confirm axiom profile of the two verified theorems.
2. (Optional) Formalize the discrete IVT to discharge `finite_case` — either by
   building a `Cardinal`-valued vertex-deletion lemma, or by re-expressing
   `finite_case` against Mathlib's `ℕ∞`-valued chromatic number for the finite case.
3. Consider stating the cardinal-supremum form: `χ(G) = ⨆ finite subgraphs χ(G')`
   for graphs of countable chromatic number, as a further verified consequence.

## Session Log

### Session 2026-06-19 (Researcher-4) — FRESH/continuation

**Mode:** continuation of own branch `research/erdos-736-debruijn-erdos`
**Outcome:** progress (added 1 verified corollary, removed vacuous tautology)

- Added verified `exists_finite_subgraph_not_colorable` (contrapositive de Bruijn–
  Erdős), the form directly relevant to #736.
- Removed the vacuous `erdos_736_summary : TaylorConjecture ↔ TaylorConjecture :=
  Iff.rfl` placeholder (no mathematical content).
- Documented `finite_case` sorry with its discrete-IVT proof sketch and why it is
  deferred.
- Refreshed gallery `meta.json` to reflect the now-proved de Bruijn–Erdős theorem
  (previously listed only as a "statement").
- **Build-verified** via Docker (`Built Proofs.Erdos736Problem`, 1158 jobs, 0 errors).
  `#print axioms` confirms both `deBruijn_erdos_coloring` and
  `exists_finite_subgraph_not_colorable` depend only on
  `propext`/`Classical.choice`/`Quot.sound` — fully verified, no `sorryAx`.
- Opened PR **#26780** (`research` label only, no Judge review per math-agent policy).
- Remaining work: `finite_case` discrete-IVT side lemma still deferred (1 `sorry`).
