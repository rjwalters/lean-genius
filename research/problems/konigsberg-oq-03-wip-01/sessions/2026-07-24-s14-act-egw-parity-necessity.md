# S14 ACT — EGW necessity via degree parity (2026-07-24, researcher-1)

## Goal

Ship S13 menu item (a): the first genuinely *structural* piece of the
Erdős–Grünwald–Weiszfeld characterisation — degree-parity necessity for
one-way Euler paths (every finite-degree non-start vertex is even, the start
is odd, hence at most one odd vertex).

## What was proved

New section "EGW necessity: degree parity (S14)" in
`proofs/Proofs/KonigsbergOQ03.lean` (+307 LOC, 20 theorems, 0 sorry /
0 axiom; file now 930 LOC, 47 theorems):

**Step-set infrastructure** (`InfiniteWalk` namespace):

1. `outSteps w v = {n | w.vertex n = v}` / `inSteps w v = {n | w.vertex
   (n + 1) = v}` — departure/arrival steps at `v`.
2. `disjoint_outSteps_inSteps` — a step both departing and arriving would be
   a loop (`step_ne`).
3. `image_succ_inSteps` — `(· + 1) '' inSteps v = outSteps v \ {0}`: the
   shift bijection pairing each arrival with the following departure. Time
   `0` is never an arrival, which is the entire source of the parity
   asymmetry.

**Counting layer** (`IsEulerWalk` namespace):

4. `image_outSteps_union_image_inSteps` — out-neighbours over departure steps
   ∪ in-neighbours over arrival steps = the neighbour set `{u | G.adj v u}`
   (Euler coverage gives ⊇; `step_adj` + `symm` give ⊆).
5. `injOn_vertex_succ_outSteps` / `injOn_vertex_inSteps` — each map is
   injective on its step set: two departures (arrivals) to (from) the same
   neighbour would traverse `{v, u}` twice (`sameEdge` `Or.inl`).
6. `disjoint_image_outSteps_image_inSteps` — no neighbour is reached both
   ways: `sameEdge` `Or.inr` forces the two steps equal, making the step a
   loop.
7. `finite_outSteps` / `finite_inSteps` — step sets inject into a finite
   neighbour set (`Set.Finite.of_finite_image`).
8. **`ncard_neighbors_eq`** — the census:
   `{u | G.adj v u}.ncard = (outSteps v).ncard + (outSteps v \ {0}).ncard`.
   Four-step `calc`: coverage, `Set.ncard_union_eq` (disjoint images),
   `Set.InjOn.ncard_image` twice, shift bijection +
   `Set.ncard_image_of_injective _ (add_left_injective 1)`.

**Parity theorems**:

9. **`even_ncard_neighbors_of_ne_start`** — `v ≠ w.vertex 0` ⇒
   `0 ∉ outSteps v` ⇒ degree `= 2 · |outSteps v|`, even.
10. **`odd_ncard_neighbors_start`** — `0 ∈ outSteps (w.vertex 0)` ⇒ degree
    `= k + (k - 1)` with `k ≥ 1` (`Set.ncard_sdiff_singleton_of_mem` +
    `Set.ncard_pos`), odd.
11. `infiniteDegree_eq_two_mul_of_ne_start` /
    `infiniteDegree_start_eq_two_mul_add_one` — ℕ∞ degree forms via
    `Set.encard_ne_top_iff` + `Set.Finite.cast_ncard_eq` + `push_cast; ring`.

**Headlines**:

12. **`oddVertices_subsingleton_of_hasOneWayEulerPath`** — the odd
    finite-degree vertices form a subsingleton (all equal the start).
13. **`not_hasOneWayEulerPath_of_two_odd_vertices`** — two distinct odd
    vertices rule out a one-way Euler path: Euler's Königsberg obstruction
    (four odd vertices), transplanted to infinite graphs.
14. Sanity instantiations: `rayGraph_neighbors_zero` (= `{1}`),
    `rayGraph_odd_ncard_neighbors_zero` (start of the S12 witness is odd —
    consistent); `lineGraph_neighbors` (= `{n + 1, n - 1}`),
    `lineGraph_even_ncard_neighbors`, and capstone
    **`lineGraph_parity_not_sufficient`** — the line graph has *zero* odd
    vertices yet no one-way Euler path (S13), so the parity clause is
    strictly weaker than the full EGW characterisation: the number of ends
    enters.

## Lean idioms

- v4.31 renames bit: `Set.mem_diff → Set.mem_sdiff`,
  `Set.diff_singleton_eq_self → Set.sdiff_singleton_eq_self`,
  `Set.ncard_image_of_injOn → Set.InjOn.ncard_image` (namespace change —
  dot-notation on the `InjOn` proof), and
  `Set.ncard_sdiff_singleton_of_mem` now takes *only* the membership proof
  (no `Finite` argument — applying the old two-argument form errors with
  "Function expected").
- Set-builder memberships are not defeq-transparent to dot-notation
  (`hm.trans` fails on `m ∈ {n | …}`): normalise first with
  `simp only [outSteps, Set.mem_setOf_eq] at hm`.
- `rcases (hE.covers v u hu)` destructures `CoversEdge` (nested `Or`/`∃`
  defs) directly — same precedent as the S12/S13 proofs.

## Verification

- Host: `lake env lean Proofs/KonigsbergOQ03.lean` (pinned
  `~/.elan/toolchains/leanprover--lean4---v4.31.0`) — exit 0, no new
  warnings (pre-existing `push_neg` deprecation notes only).
- Docker: `./proofs/scripts/docker-build.sh Proofs.KonigsbergOQ03` — GREEN
  (see PR).

## S15 menu

(a) EGW *sufficiency* fragments — still the multi-week König's-lemma
compactness route (blocked); (b) bi-infinite parity analogue (every
finite-degree vertex even — no start exception; same census with ℤ-shift,
no `\ {0}` asymmetry); (c) park — with witnesses, incomparability, and
parity necessity the file tells a complete story short of full EGW.
