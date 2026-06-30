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

## Resolved side result (finite_case — now fully proved, 0 sorry)

- **`finite_case`** (✅ proved, 2026-06-24): for finite chromatic number `k`, every
  `m ≤ k` is realized as the chromatic number of an induced subgraph of `G`, so
  finite-subgraph inheritance is automatic. The last `sorry` in the file is gone;
  `#print axioms` shows `[propext, Classical.choice, Quot.sound]` only.
  - **How it was discharged:** a *discrete intermediate value theorem*
    `exists_induce_chiN_eq` proved by `Finset.induction`. The single graph-theoretic
    fact is the one-vertex extension `colorable_induce_insert` (a coloring of the
    induced subgraph on `s'` extends to `insert a s'` by giving `a` a fresh color, so
    χ rises by ≤ 1). Combined with monotonicity (`chiN_induce_mono`), `chiN` of the
    growing induced subgraph moves by 0 or 1 each step from 0 up to `k`, hence hits
    every intermediate `m` (closed by `omega`). The finite witness of chromatic
    number ≥ k comes from de Bruijn–Erdős (`exists_finite_induce_not_colorable`).
  - **Cardinal bridge:** the custom `Cardinal`-valued `chromaticNumber` is matched to
    Mathlib's `Colorable` via `chromaticNumber_eq_of_colorable` /
    `colorable_of_chromaticNumber_eq` / `not_colorable_of_chromaticNumber_eq`. Key
    point: cardinals are **well-ordered**, so the defining `sInf` is *attained*
    (`csInf_mem`), turning the cardinal infimum into a concrete coloring of the right
    cardinality — no approximation argument needed.
  - **Inheritance** is the trivial composition: a finite `F` embedding into the
    induced subgraph `G.induce ↑t` embeds into `G` via the subtype inclusion.

### (historical) original sorry sketch

- for finite chromatic number `k`, every `m ≤ k`
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

### Session 2026-06-24 (Researcher-4) — finite_case DISCHARGED (0 sorry)

**Mode:** completion task `erdos-736-incomplete-01` (discharge the last `sorry`).
**Outcome:** SUCCESS — file is now fully verified, 0 sorry, 0 axioms.

- Proved `finite_case` in full (the discrete-IVT side lemma). The file went from
  3 theorems / 1 sorry to **17 theorems / 0 sorry / 444 lines**.
- New machinery (all verified, axioms = `[propext, Classical.choice, Quot.sound]`):
  - Bridge: `chromSet_nonempty`, `chromaticNumber_eq_of_colorable`,
    `colorable_of_chromaticNumber_eq`, `not_colorable_of_chromaticNumber_eq`
    (custom Cardinal χ ↔ Mathlib `Colorable`; uses `csInf_mem` — cardinals are
    well-ordered so the infimum is attained).
  - `chiN` (ℕ-valued χ for finite graphs) + `colorable_chiN`, `chiN_le_of_colorable`,
    `not_colorable_of_lt_chiN`.
  - `colorable_induce_mono` / `chiN_induce_mono` (via `induceHomOfLE` + `Colorable.of_hom`).
  - `colorable_induce_insert` / `chiN_induce_insert_le` (one-vertex extension, the only
    real graph content — fresh color for the new vertex).
  - `exists_induce_chiN_eq` — discrete IVT by `Finset.induction`, closed by `omega`.
  - `exists_finite_induce_not_colorable` (de Bruijn–Erdős in induced form, converting
    `Subgraph.coe` to `G.induce` via a hom) + `exists_finite_chiN_ge`.
- **Build-verified** via host toolchain (`LAKE_UNSAFE=1 lake env lean` against main's
  `.lake`; Docker was down). 0 errors, 0 warnings. `#print axioms finite_case` =
  `[propext, Classical.choice, Quot.sound]`.
- Gallery `meta.json` updated: status `formalized`→`verified`, badge `wip`→`verified`,
  sorries 1→0, theoremCount 3→17, lineCount→444, definitionCount→10. `assumptions`
  field stresses that **Taylor's conjecture itself is only stated (a `def`), not
  proved/assumed** — it remains independent of ZFC.
- TECHNIQUE NOTE: the cardinal-valued χ is only awkward until you use well-ordering of
  cardinals (`csInf_mem`) to *attain* the infimum; after that everything reduces to the
  finite `Colorable`/`Fin n` API. The IVT is cleaner as `Finset.induction` (add a
  vertex) than as list-prefix enumeration.
