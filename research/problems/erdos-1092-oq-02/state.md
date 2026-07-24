# Research State: erdos-1092-oq-02

## Current State
**Phase**: OBSERVE
**Path**: full
**Since**: 2026-07-04T18:35:43-07:00
**Iteration**: 2

## Current Focus
Initial problem understanding. Read problem.md and gather context.

## Active Approach
None yet.

## Attempt Count
- Total attempts: 0
- Current approach attempts: 0
- Approaches tried: 0

## Blockers
None.

## Next Action
Read problem.md thoroughly and acquire full context.
Then move to ORIENT phase to explore literature and related proofs.

## Status (researcher-3, 2026-07-24) — ACT: first exact value landed

`fThreshold 1 3 = 2` machine-checked (first exact value in the family), and the
parent's removed `f_trivial_lower` axiom refuted in Lean (`fThreshold 1 4 < 3`
via K₃ + isolated vertex). File 249 → 509 lines, 13 → 21 theorems, 0 axioms /
0 sorries. Next natural rung: `2 ∈ fThresholdSet 1 4` (exact value at (1,4));
parent OQ (Rödl for r ≥ 3) remains research-level.

## Status (researcher-3, 2026-07-24, second session) — ACT: second exact value

`fThreshold 1 4 = 2` machine-checked (second exact value; file 509 → 750 lines,
21 → 26 theorems, 0 axioms / 0 sorries, docker `[8577/8577]`, headline
`[propext, Classical.choice, Quot.sound]`). Mechanism: the THREE PERFECT
PAIRINGS of Fin 4 ({01|23}, {02|13}, {03|12}) — an edge kills exactly the one
pairing putting its endpoints together; three killed pairings = three distinct
edges > budget 2 (generic `three_slots_le_card` + `slot_nonempty` helpers,
factored out of the (1,3) K₃ counting); a surviving pairing IS a 2-coloring
(3 colorings × case tree, 8 contradiction leaves + 7 survival leaves).
Constancy corollary: `fThreshold 1 3 = fThreshold 1 4` — the threshold does
not grow at the next data point (further evidence against n-1-style growth).

Next rungs: (1,5) — five pairings... no: Fin 5 has no perfect pairings (odd);
use near-pairings (2+2+1) — a surviving near-pairing 2-colors iff isolated
vertex color free; count: C(5,2)·3 = 15 near-pairings hmm; more edges available
(budget k vs 10 slots). Likely fThreshold 1 5 = 2 or 3 — compute small models
first before formalizing. Alternatively (2,4): r=2, K₄-obstruction, budget vs
6 edges, 3-colorings. Parent OQ (Rödl r ≥ 3) remains research-level.

## Status (researcher-3, 2026-07-24, third session) — ACT: the COMPLETE r = 1 row

**`fThreshold 1 n = 2` for every `n ≥ 3`** (`fThreshold_one_eq_two`), machine-checked
(file 750 → ~1000 lines, host-verified `lake env lean` exit 0 on pinned v4.31.0, mathlib
rev `9a9483a929`; `#print axioms` = `[propext, Classical.choice, Quot.sound]` on all new
headline theorems; 0 sorries). The whole r = 1 row of the family is now closed — the
(1,5) rung the previous session flagged for "compute models first" is settled *for free*
(`fThreshold_one_five : fThreshold 1 5 = 2`), along with (1,6), (1,7), … at once, and the
row is constant (`fThreshold_one_constant`): the definitive refutation of any
`n−1`-style growth at r = 1.

**Mechanism (simpler than the pairings of (1,4))**: at `S = univ`, a budget-`k`
hypothesis at `r = 1` caps the *entire* edge set of `G` by `k` removed ordered pairs
(a 1-coloring tolerates no surviving edge). Lower bound: with `k = 2` all edges of `G`
lie inside two ordered pairs `p, q`, and such a graph is 2-colorable outright via the
explicit `coverColoring p q` (three-way split on head-to-tail endpoint sharing —
`p.1 = q.2` / `p.2 = q.1` / neither — 12 leaf cases, each two `if`-evaluations).
No pairing combinatorics, no parity argument: two ordered pairs cannot hide an odd
cycle. Upper bound: `trianglePlus n` (`K₃` + `n−3` isolated vertices) satisfies the
budget-3 hypothesis via `mem_killTri` (membership by `omega` after
`Prod.mk.injEq`/`Fin.ext_iff` reduction — no `fin_cases`, works at symbolic `n`) but
contains a triangle (pigeonhole on `Fin 2` values by `omega`).

**Lean idioms (v4.31)**: (a) `simp only [if_pos h]` pre-normalizes `u = u` conditions
to `True`, so follow-up `rw` needs `if_pos trivial` / `if_pos (Or.inl trivial)`, not
`if_pos rfl`; (b) symbolic-`n` vertex literals via `obtain ⟨v0, hv0⟩ : ∃ w : Fin n,
w.val = 0` keep all facts `omega`-visible and avoid `Fin.mk`-proof-term mismatch;
(c) `removed ⊆ {p, q}` extraction from `card ≤ 2` via `Finset.card_eq_zero/one/two`
with junk-pair padding — `coverColoring` is robust to diagonal/junk pairs since
coverage cases with `u = v` are vacuous; (d) avoid deprecated `push_neg` (v4.31 warns;
build the two negations by hand).

**Remaining**: r ≥ 2 rungs — (2,4) (K₄ obstruction, budget vs 6 edges, 3-colorings) is
the next finite rung; a general r-row would need the analogous "budget caps edges" story
at `r = 2` where a 2-coloring DOES tolerate edges — genuinely harder (bipartite-plus-
budget structure), likely pairing-style again. Parent OQ (Rödl r ≥ 3) research-level.

## Status (researcher-3, 2026-07-24, fourth session) — ACT: the r = 2 row opens

`fThreshold 2 4 = 1` machine-checked (first exact value in the r = 2 row; file
998 → 1179 lines, 0 axioms / 0 sorries, docker-verified). The anticipated
"pairing-style casework" turned out unnecessary: at n = 4 the ONLY
non-3-colorable graph is K₄, so a single obstruction governs the row entry.

* Upper (`two_notMem_fThresholdSet_two_four`): K₄ passes the budget-2 test —
  removing the opposite edges {0,1}, {2,3} leaves the bipartite C₄ 0–2–1–3–0,
  and the SAME removal + bipartition works for every induced S (subgraphs of
  bipartite are bipartite; 16-leaf fin_cases with decide discharges).
* Membership of 1 (`one_mem_fThresholdSet_two_four`): dichotomy on
  completeness. Non-complete → explicit 3-coloring (non-edge pair shares a
  color, other two vertices fresh; if-then-else case tree). Complete → the
  S = univ budget-1 hypothesis is absurd: `card_le_one_iff_subset_singleton`
  pads the removal to one pair p, the triangle {a, b, p.1} on the two
  vertices clear of p survives, and Fin 2 pigeonhole
  (`∀ x : Fin 2, x = 0 ∨ x = 1 := fun x => by omega`) forces a monochromatic
  surviving edge.
* **`fThreshold_lt_at_four : fThreshold 2 4 < fThreshold 1 4`** — the
  threshold strictly DROPS as r grows at n = 4 (1 < 2): the weaker target has
  a rarer obstruction whose own reducibility is cheap. First cross-row
  comparison in the family.

**Remaining**: (2,5) would need the K₄-subgraph obstruction analysis on 5
vertices (multiple embeddings — genuinely harder); (2,n) general row likely
needs the "K₄ is the only obstruction ⟹ budget caps" story to break. Parent
OQ (Rödl r ≥ 3) research-level — do not attempt.

## Status (researcher-1, 2026-07-24, fifth session) — ACT: the table closes

**`fThreshold` is completely determined on its good regime** (file 1177 → 1600
lines, 0 axioms / 0 sorries, docker-verified, axioms
`[propext, Classical.choice, Quot.sound]`):

    fThreshold r n = if r = 1 then 2 else 1     (1 ≤ r, r + 2 ≤ n)

(`fThreshold_determined`). The session landed in two stages:

* **The `r = 2` row closed** (`fThreshold_two_eq_one`: `fThreshold 2 n = 1`
  for all `n ≥ 4`; corollaries `fThreshold_two_five`,
  `fThreshold_two_constant`, `fThreshold_two_lt_fThreshold_one`). The
  anticipated "multiple K₄ embeddings on 5 vertices" analysis was never
  needed: membership of budget 1 needs only `S = univ` — one removed pair
  `p` leaves a 2-colorable graph, and recoloring the single vertex `p.1`
  with a fresh third color repairs every hidden edge (each is incident to
  `p.1`). No completeness dichotomy, no obstruction analysis; this subsumes
  the (2,4) lower-bound proof. Upper bound: `k4Plus n` (K₄ + isolated,
  the `trianglePlus` recipe one row down), 4-into-3 pigeonhole by `omega`.
* **Every row `r ≥ 2` closed at once** (`fThreshold_eq_one`). The
  third-color trick is uniform in `r` (`one_mem_fThresholdSet`:
  `Fin.last r` for `p.1`, `(c ·).castSucc` elsewhere). Upper bound
  (`two_notMem_fThresholdSet`): `cliquePlus (r+2) n` — shedding the
  2-matching `{(v0,v1), (v2,v3)}` drops `K_{r+2}`'s chromatic number to
  exactly `r` (merged pairs become 2-element color classes: `{0,1} ↦ 0`,
  `{2,3} ↦ 1`, clique vertex `j ↦ j−2`, `min`-padded for isolated
  vertices), uniformly in the induced `S`; non-`(r+1)`-colorability via
  `Fintype.card_le_of_injective` (`Fin (r+2) ↪ Fin (r+1)` refuted). The
  2-matching needs **four** clique vertices — exactly why `r = 1` sits at
  threshold 2 (`K₃` has no 2-matching) and every `r ≥ 2` sits at 1.

**Lean v4.31 gotchas**: `rw [if_pos h] at hcuv` fails on beta-unreduced
`(fun w => …) u = …` hypotheses — `simp only [if_pos h, …] at hcuv`
beta-reduces first. `congrArg Fin.val` on equations between `Fin.mk`s can
elaborate against the wrong implicit pair — use `Fin.mk_eq_mk.mp`.
`by_cases hv1` silently shadows an outer `obtain ⟨v1, hv1⟩` fact.

**Remaining**: nothing computable — every row is constant, every value
attained, the `r=1 → r=2` drop is the only jump. Parent OQ (Rödl's actual
construction for `r ≥ 3`) remains research-level. A documentation note on
the contrast with the true Erdős–Hajnal–Szemerédi `f_r(n)` growth (Rödl:
`O(n·polylog n)`) — collapsed here by the per-induced-subgraph fresh-budget
semantics — is a possible enrichment angle.
