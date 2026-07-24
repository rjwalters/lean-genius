# S13 ACT — Incomparability pair (2026-07-24, researcher-1)

## Goal

Ship both items of the S12 "S13 menu": `¬ HasInfiniteEulerPath rayGraph` and
`¬ HasOneWayEulerPath lineGraph`, proving the one-way and bi-infinite
Euler-path predicates incomparable.

## What was proved

New section "Incomparability of the two Euler-path notions (S13)" in
`proofs/Proofs/KonigsbergOQ03.lean` (+161 LOC, 4 theorems, 0 sorry / 0 axiom):

1. **`not_hasInfiniteEulerPath_rayGraph`** — vertex `0` of the ray has degree
   one. A bi-infinite walk must both enter and leave every vertex it visits;
   the traversal of edge `{0, 1}` at step `t` therefore has a neighbour step
   (`t - 1` or `t + 1`) that traverses `{0, 1}` again — `sameEdge` in the
   `Or.inr` (reversed) orientation — contradicting edge-injectivity.
2. **`not_hasOneWayEulerPath_lineGraph`** — structured as:
   - `huniq`: the edge `{0, 1}` is traversed at a unique step `t` (4-way
     `sameEdge` case analysis, `Eq.trans`/`Eq.symm` only);
   - `hconf` (per crossing direction): `Nat.le_induction` from `t + 1` shows
     the walk never returns across the cut — a return step would be a second
     `{0, 1}` traversal, killed by `huniq`;
   - pigeonhole: every abandoned-side edge (`{-1 - k, -k}` for the upward
     crossing, `{k + 1, k + 2}` for the downward one) must be traversed at
     some step in `Set.Iic t`; `choose` extracts the traversal-time function,
     which is injective (`omega` on the endpoint equations), and
     `Set.infinite_of_injective_forall_mem` vs `(Set.finite_Iic t)` closes.
3. **`not_oneWay_imp_biInfinite` / `not_biInfinite_imp_oneWay`** — the
   ∀-quantified implication between the two predicates fails in both
   directions, witnessed by ray and line respectively.

## Verification

`./proofs/scripts/docker-build.sh Proofs.KonigsbergOQ03` — exit 0, 8576 jobs,
**first-try GREEN**. Only warnings: `push_neg` deprecation (v4.31 prefers
`push Not`; left as-is for repo consistency).

## Insights

- The S12 estimate ("~100+ LOC discrete-crossing each") was right for the
  line but wrong for the ray: a **degree-1 vertex kills bi-infinite Euler
  paths locally** (~25 LOC), because a ℤ-walk has no endpoint to hide at.
  The asymmetry is real: the one-way walk *may* start at the ray's degree-1
  vertex (S12's `rayWalk` does exactly that), but a bi-infinite walk cannot.
- All vertex-value reasoning closes by `omega` treating `w.vertex _` as
  atoms; the only rewrites needed are ℤ-index normalizations
  (`rw [show t - 1 + 1 = t from by ring]`).
- `apply hinj` on a goal `i = t` cleanly leaves the `sameEdge i t` obligation
  (defeq unfolding of the `IsEdgeInjective` ∀-statement).

## Next (S14 menu)

- (a) EGW necessity for locally finite graphs: one-way Euler path ⇒ at most
  2 odd-degree vertices — first structural EGW piece (~150+ LOC, degree
  counting over `infiniteDegree`).
- (b) Extract the cut-confinement argument (unique cut-edge traversal splits
  the timeline into side-confined halves) as a reusable lemma.
- (c) Park at plateau: 623 LOC / 27 theorems / 0 sorry / 0 axiom with the
  2×2 satisfiability picture complete. EGW full characterization and r ≥ 3
  hypergraph Euler tours remain structured blocked routes.
