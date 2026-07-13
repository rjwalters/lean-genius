# Knowledge Base: prob-method-applications-wip-01-oq-03

Tournament domination lower bound via the first-moment method.

---

## Problem Understanding

**Goal.** Prove, via the first-moment method, that if
`C(n,k)·(2^k − 1)^{n−k} < 2^{k(n−k)}` (equivalently the classical
`C(n,k)(1 − 2^{−k})^{n−k} < 1`) then there is a tournament on `n` vertices in
which **no** `k`-set dominates — a tournament with domination number `> k`
(Erdős 1963, the "Schütte property"). The concrete obligation is to bound the
number of tournaments in which a fixed `k`-set dominates.

**Engine.** The parent entry `prob-method-applications-wip-01`
(`ProbMethod.Core`) already provides the abstract first-moment / union-bound
existence principle over an arbitrary finite sample space:

```
exists_good_of_card_bound :
  (s : Finset ι) (A : ι → Finset Ω) (B : ℕ)
  (∀ i ∈ s, (A i).card ≤ B) (s.card * B < |Ω|)
  ⟹ ∃ ω, ∀ i ∈ s, ω ∉ A i
```

The parent explicitly listed tournament domination as an open instantiation.

---

## Insights

- **Model:** a tournament on a finite linearly ordered `V` is an orientation
  `T : Edge V → Bool` where `Edge V = {p : V × V // p.1 < p.2}` (the `C(|V|,2)`
  edges stored as increasing ordered pairs). `beats T u v` reads the winner off
  the stored bit with a two-way case split. Sample space `Ω = Edge V → Bool`,
  `|Ω| = 2^{C(|V|,2)}`. Keeping `Ω` a plain function type avoids quotient
  bookkeeping.
- **The count factors.** Domination of a fixed `K` constrains only the
  `k(n−k)` cross edges, and independently for each outside vertex `v`: the `k`
  edges `v–K` must avoid the single all-lose configuration (`v` beats every
  member of `K`). So `2^k − 1` good configurations per outside vertex, times
  free non-cross edges.
- **Inequality suffices.** The union bound needs only `≤`, so we inject the
  dominating tournaments into `(Kᶜ → winning blocks) × (non-cross edges → Bool)`
  rather than proving an exact bijection. Combined with "there are `≥ k(n−k)`
  cross edges" (an explicit injection `K × Kᶜ ↪ cross edges`), this gives
  `|{T : K dominates T}| ≤ (2^k − 1)^{n−k}·2^{|Edge V| − k(n−k)}`.
- **Axiom hygiene.** The `Fin 3` cyclic-triangle witness is discharged by
  kernel `decide` (not `native_decide`), so the entry introduces no
  `Lean.ofReduceBool` and is genuinely axiom-free.

## Built Items

- `beats`, `Dominates`, `dominatingSet`, `IsCross`, `crossEdge` (defs) in
  `Proofs/ProbMethodApplicationsWIPOQ03.lean`.
- `card_block`: per-vertex winning-configuration count `2^k − 1`.
- `crossEdge_injective` / `crossEdge_surjective` / `card_cross_eq`: `crossEdge`
  is a **bijection** `K × Kᶜ ≃ {cross edges}`, so there are *exactly* `k(n−k)`
  cross edges. `card_cross_ge` (`≥ k(n−k)`) is now a one-line corollary
  (`(card_cross_eq K).ge`).
- `card_dominates_le`: the crux count
  `|{T : K dominates T}| ≤ (2^k − 1)^{n−k}·2^{|Edge V| − k(n−k)}`.
- `exists_no_dominating_kset`: the tournament domination lower bound.
- `exists_no_dominating_vertex_Fin3`: cyclic-triangle witness (`decide`).

Status: **VERIFIED**, 0 sorry, 0 axiom (Mathlib v4.26.0). Built via
`docker-build.sh Proofs.ProbMethodApplicationsWIPOQ03`.

---

## Dead Ends

- For the union bound alone, the `≤` count (`card_dominates_le` via injection)
  is already sufficient and avoids surjectivity — but the exact cross-edge
  bijection turned out to be cheap (`crossEdge_surjective` is a two-case
  `rintro` on the cross edge, mirroring `crossEdge_injective`), so
  `card_cross_eq` is now proved and `card_cross_ge` derives from it.

---

## Next Steps

- Upgrade `card_dominates_le` itself to an equality. The cross-edge count is now
  exact (`card_cross_eq`), so what remains is to show the injection into
  `(Kᶜ → winning blocks) × (non-cross edges → Bool)` is also surjective, then
  read off the exact fraction `(1 − 2^{−k})^{n−k}`.
- Extract the asymptotic: the criterion holds for `k ≈ log₂ n − 2 log₂ log₂ n`,
  giving domination numbers `≍ log₂ n`.
- Formalize the matching upper bound (every tournament has a dominating set of
  size `≤ ⌈log₂(n+1)⌉`) to pin the growth rate.

---

## Sessions

### 2026-07-02 (Session 1) — FRESH — Outcome: completed

**What I did.** Found a complete but uncommitted/unbuilt proof file for this
problem in the working tree (a prior session wrote it but never verified or
integrated it). Verified it builds with 0 sorry / 0 axiom via the docker
wrapper, then created the gallery integration (`meta.json`, `annotations.json`)
and recorded the knowledge here.

**Key findings.** The tournament domination bound instantiates the parent's
`exists_good_of_card_bound` cleanly; the only real work is the finite count
`card_dominates_le`, which the file discharges by an injection into a product
sample space (see Insights). Confirmed the `Fin 3` witness uses kernel `decide`,
keeping the entry axiom-free.

**Files.** `proofs/Proofs/ProbMethodApplicationsWIPOQ03.lean`,
`src/data/proofs/prob-method-applications-wip-01-oq-03/{meta,annotations}.json`.

### 2026-07-02 (Session 2) — researcher-11 — Outcome: extended + integrated

**Context.** Session 1's proof and gallery data were still **untracked** in a
shared dirty working tree (never committed or PR'd) — this session rescues that
work into a branch/PR and advances the first Next Step.

**What I did.** Proved `crossEdge_surjective` (every cross edge is hit by
`crossEdge`: `rintro` the cross edge, two-case split on which endpoint is in `K`,
put the in-`K` endpoint first and discharge via `crossEdge_fst`). Combined with
the existing `crossEdge_injective` this gives `card_cross_eq` — the exact count
`|{cross edges}| = k(n−k)` — via `Fintype.card_of_bijective`. Refactored
`card_cross_ge` to the one-liner `(card_cross_eq K).ge`, removing the earlier
standalone injection argument. Updated the header status note and the gallery
`meta.json`/`annotations.json` (line counts 310→338, theoremCount 7→9, exact-count
framing). Built via `docker-build.sh Proofs.ProbMethodApplicationsWIPOQ03`.

**Key findings.** The exact cross-edge count is cheap — surjectivity mirrors the
injectivity proof structurally. This pins the *free-edge exponent*
`|Edge V| − k(n−k)` exactly, so the remaining gap to an exact
`card_dominates_le` is now solely the surjectivity of the block/non-cross
injection (recorded as the sharpened Next Step).

**Files.** `proofs/Proofs/ProbMethodApplicationsWIPOQ03.lean` (+`crossEdge_surjective`,
`card_cross_eq`), `src/data/proofs/prob-method-applications-wip-01-oq-03/{meta,annotations}.json`.
