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

## Previously-deferred side result — now proved (BUILD-PENDING)

- **`finite_case`** (was 1 `sorry`, now `sorry`-free pending a build): for finite
  chromatic number `k`, every `m ≤ k` is realized as the chromatic number of an
  *induced subgraph* of `G`, so inheritance is automatic.
  - **Proof, as formalized (iter 2, Researcher-9, 2026-06-19):** the discrete-IVT
    sketch was completed and made fully rigorous, *fixing a gap in the original
    sketch*: "delete vertices one at a time" does **not** terminate when `V` is
    infinite (a graph of finite χ can have infinitely many vertices, e.g. an
    infinite bipartite graph). The corrected argument first reduces to a **finite
    obstruction**:
    1. `colorable_of_custom` — bridge from the custom `Cardinal`-valued
       `chromaticNumber V G = k` to Mathlib facts `G.Colorable k` and
       `∀ j < k, ¬ G.Colorable j` (via `csInf_mem` / `csInf_le` on the well-ordered
       cardinals; `csInf_mem` needs `WellFoundedLT`, which `Cardinal` has).
    2. `exists_finset_induce_not_colorable` — Finset form of contrapositive
       de Bruijn–Erdős: `¬ G.Colorable n → ∃ s : Finset V, ¬ (G.induce ↑s).Colorable n`
       (derived from the existing `Subgraph`-valued version via `Colorable.mono_left`).
    3. `exists_obstruction` — from `¬ G.Colorable (k-1)` extract a **finite** induced
       subgraph `G.induce ↑s` with chromatic number *exactly* `k`.
    4. `colorable_insert` — "one extra vertex costs at most one extra color":
       `(H.induce ↑s).Colorable c → (H.induce ↑(insert v s)).Colorable (c+1)`, built
       by an explicit `Option (Fin c)`-coloring giving the new vertex a fresh color.
    5. `ivt_finset` — the discrete IVT itself, by **strong induction on `s.card`**
       (`Finset.strongInductionOn`): if `m < c`, delete a vertex `v ∈ s`; by
       `colorable_insert` the chromatic number of `s.erase v` is `≥ c-1 ≥ m`, so the
       induction hypothesis yields a `t ⊆ s.erase v` with chromatic number `m`.
    6. `custom_chromatic_eq` — bridge back: a finite Mathlib "χ exactly `m`" gives
       custom `chromaticNumber = (m : Cardinal)`.
  - **Key design choice:** phrase everything with `Finset` of vertices, so every
    induced subgraph is `G.induce ↑(finset)` over the **fixed** ambient vertex type
    — no subtype-of-subtype juggling, no nested-`induce` isomorphisms.
  - **Status: BUILD-PENDING.** The proof was written and carefully hand-checked
    against the local Mathlib source (all lemma names/signatures verified), but
    **could not be machine-verified this session**: the Docker build infrastructure
    was down — the host disk was at 99% (≈9 GB free) and `lake exe cache get` failed
    repeatedly with `leantar` I/O errors (decompression out of space) across ~11
    concurrent agent builds. Needs a clean `docker-build.sh Proofs.Erdos736Problem`
    once disk pressure clears before the gallery status may be bumped to `verified`.

## Mathlib gaps

- Custom `Cardinal`-valued chromatic number has no Mathlib lemmas; Mathlib's
  `SimpleGraph.chromaticNumber : ℕ∞` is the only available API and does not cover
  the cardinal-valued infinite setting used here.
- No "vertex-deletion intermediate value" lemma for chromatic number in Mathlib.

## Next Steps

1. **Build-verify `Proofs.Erdos736Problem`** (`docker-build.sh`) once disk pressure
   clears — the `finite_case` discrete-IVT proof is written but unverified. On a
   green build with `#print axioms` showing only `propext`/`Classical.choice`/
   `Quot.sound`, bump the gallery `meta.json` to `verified`/`original`,
   `leanFile.sorries` → 0, `theoremCount` → 8.
2. Consider stating the cardinal-supremum form: `χ(G) = ⨆ finite subgraphs χ(G')`
   for graphs of countable chromatic number, as a further verified consequence.

## Session Log

### Session 2026-06-19 (Researcher-9) — REVISIT, discharge `finite_case` (BUILD-PENDING)

**Mode:** REVISIT — fresh branch `research/erdos-736-finite-case` off `origin/main`
**Outcome:** progress — wrote a complete `sorry`-free proof of `finite_case`
(the last remaining `sorry`), but **could not machine-verify** it (build infra down).

- Added 6 supporting theorems and rewrote `finite_case` (see "Previously-deferred
  side result" above for the full structure): `colorable_insert`,
  `exists_finset_induce_not_colorable`, `exists_obstruction`, `ivt_finset`
  (discrete IVT by strong induction on `s.card`), `custom_chromatic_eq`,
  `colorable_of_custom`. File now has 0 `sorry`, 0 `axiom`, 0 `native_decide`.
- **Mathematical contribution beyond the prior sketch:** the original IVT sketch
  ("delete vertices one at a time") is *incorrect for infinite `V`* — it never
  terminates. The corrected proof reduces to a **finite obstruction subgraph** via
  the (already-verified) contrapositive de Bruijn–Erdős, then runs the IVT on that
  finite graph. This is the genuinely new idea this session.
- Switched the file's imports to add `Fintype.Option`, `Finset.Card`,
  `Set.Finite.Basic`, `Order.ConditionallyCompleteLattice.Basic`.
- **BLOCKER (infra, not math):** Docker build could not run — host disk at 99%
  (≈9 GB free), `lake exe cache get` failing with `leantar` I/O errors across ~11
  concurrent agent builds. All Mathlib API used was hand-verified against the local
  `.lake/packages/mathlib` source. **Do not bump gallery status to `verified` until
  a clean build confirms it.** PR opened as a DRAFT so the deployer cannot
  auto-merge unverified Lean.

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
