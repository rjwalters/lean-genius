# Knowledge Base: erdos-89-wip-01

Insights accumulated during research on this problem.

---

## Session 2026-07-21 (researcher-1) — upper bound `g(6) ≤ 3` (regular pentagon + circumcentre)

**Mode**: continue RICH node (g(5)=2 was the previous milestone). **Outcome**:
progress — added the next rung of the exact table, `g(6) ≤ 3`, Docker-verified
(`Proofs.Erdos89WIP01`, 8577 jobs), all new decls `#print axioms` =
`[propext, Classical.choice, Quot.sound]` (0 sorry / 0 axiom).

### What I added (`proofs/Proofs/Erdos89WIP01.lean`, +~150 lines)
- `pentCenter := !₂[0,0]` — the circumcentre of the (circumradius-4) regular pentagon.
- `dist_centerP0..4 : Erdos89.dist pentCenter pentPᵢ = 4` — each vertex is at the
  circumradius from the centre. `rw [pentCenter, pentPᵢ, dist_eqPts]` then rewrite the
  radicand to `4^2` by `linear_combination pent_s_sq (+ pent_t1_sq | + pent_t2_sq)`,
  finish `Real.sqrt_sq`. (P0 needs no `linear_combination`, just `norm_num`.)
- `pentCenter_ne_pentPᵢ` — centre distinct from each vertex (norm 4 ≠ 0), by a coord
  projection + `Real.sqrt_nonneg`/`sqrt_pos`.
- `pentagonPlusCenter` (6 points) + `pentagonPlusCenter_card = 6`.
- `numDistinctDistances_pentagonPlusCenter_le_three` — the 15 pairwise distances lie in
  `{√(40−8√5), √(40+8√5), 4}`, mirroring the g(5) `numDistinctDistances_pentagon_le_two`
  proof but with a 6×6 `rcases` and the 3-element target set. **Needed
  `set_option maxHeartbeats 1600000 in` (before the docstring)** — the 36-case ×
  ~30-alternative `first |` combinator overruns the 200000 default (isDefEq/whnf timeout).
- `minDistinctDistances_six_le_three : g(6) ≤ 3` (via `minDistinctDistances_le_of_card_eq`).
- `minDistinctDistances_six_mem_Icc : g(6) ∈ [2,3]` — floor from monotonicity
  `g(6) ≥ g(5) = 2` (`minDistinctDistances_mono`), ceiling the pentagon+centre witness.

### Key findings / reusable recipe
- **Centre-to-vertex = circumradius reuse**: the pentagon+centre config recycles ALL ten
  g(5) side/diagonal distance lemmas; only the 5 spokes are new, and they collapse to the
  single value `4` because each vertex has norm exactly `4` (radicand → `16 = 4²`).
- The `first |`-combinator distance-dispatch scales O(pairs × alternatives): 5-pt pentagon
  (25×20) fits default heartbeats, 6-pt (36×30) does NOT — bump to ~1.6M.

### Why only the upper bound (the remaining gap)
- `g(6) = 3` is conjectural; the matching **lower bound `g(6) ≥ 3`** is equivalent to the
  SHARP planar statement "a two-distance set in `ℝ²` has ≤ 5 points" (Kelly/Erdős). The
  elementary Larman–Rogers–Seidel rank bound only gives `≤ (d+1)(d+2)/2 = 6` for `d=2`,
  which does NOT exclude a 6-point two-distance set — so `g(6) ≥ 3` needs the extra
  Blokhuis-type refinement and is left open (documented in the file docstring).

### Next steps
- `g(6) ≥ 3` via the sharp two-distance ≤ 5 bound (deep).
- `√n×√n` integer grid toward the conjectured `Θ(n/√(log n))` rate.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]

---

## Session (researcher-1, 2026-07-20) — first machine-checked theorems (axiom-free)

Created `proofs/Proofs/Erdos89WIP01.lean` (6 theorems, 0 sorry, 0 axiom;
host-verified `bin/lake env lean` exit 0, `#print axioms` = `[propext,
Classical.choice, Quot.sound]` on all — no `sorryAx`, no `ofReduceBool`). The
scaffold `Erdos89Problem.lean` proved facts *about the conjecture* (Guth–Katz
consistency) but nothing about the counting objects; this adds their structure.

- `dist_pos_of_ne` — `p ≠ q ⟹ 0 < ‖p − q‖` (`norm_pos_iff` + `sub_ne_zero`).
- `distinctDistances_eq_image` — the definitional `filter (· > 0)` is redundant:
  every off-diagonal pair already has positive distance, so
  `distinctDistances S = S.offDiag.image (dist · ·)` (`Finset.filter_true_of_mem`).
- `numDistinctDistances_le_offDiag` — `≤ |S|·(|S|−1)` (`card_image_le`,
  `Finset.offDiag_card`, `Nat.mul_sub_one`).
- `numDistinctDistances_eq_zero_of_card_le_one` — degenerate floor.
- `one_le_numDistinctDistances_of_two_le_card` — `2 ≤ |S| ⟹ ≥ 1`
  (`Finset.one_lt_card` gives a distinct pair; its distance is a member).
- `minDistinctDistances_le_of_card_eq` — `g(n) ≤ numDistinctDistances S` for any
  `n`-point `S` (`Nat.sInf_le`), the grid-upper-bound membership hook.

### Verification
Parent `Erdos89Problem.lean` fresh-built to olean host-side (Mathlib-only, v4.31,
docker-free), child compiled against it. Exit 0, no warnings.

### Next Steps
- Sharpen to `≤ S.card.choose 2` via distance symmetry.
- Formalize the `√n × √n` grid upper bound feeding `minDistinctDistances_le_*`,
  giving a concrete `g(n) = O(n)` ceiling.
- Connect `singlePointConjecture` (Problem #604) to the global count.

## Session (researcher-1, 2026-07-20 #2) — sharp choose-2 ceiling

Added `numDistinctDistances_le_choose_two` — `numDistinctDistances S ≤
S.card.choose 2`, the sharp unordered-pair ceiling (halves the crude
`|S|·(|S|−1)` bound from session #1). This was the first listed Next Step.

Key idea (identical to erdos-98-wip-01): the custom `Erdos89.dist p q = ‖p−q‖`
is symmetric via `norm_sub_rev`, so it factors as `g ∘ Sym2.mk.uncurry` with
`g = Sym2.lift ⟨fun a b => dist a b, norm_sub_rev⟩`. Then
`S.offDiag.image (dist ·.1 ·.2) = (S.offDiag.image Sym2.mk.uncurry).image g`
(`Finset.image_image`), and `Sym2.card_image_offDiag S` counts the off-diagonal
`Sym2` image as `S.card.choose 2`.

Host-verified `bin/lake env lean Proofs/Erdos89WIP01.lean` exit 0, no warnings;
`#print axioms numDistinctDistances_le_choose_two` = `[propext, Classical.choice,
Quot.sound]`. Now 7 theorems, 0 sorry, 0 axiom.

### Next Steps (unchanged)
- Formalize the `√n × √n` grid upper bound feeding `minDistinctDistances_le_*`
  for a concrete `g(n) = O(n)` ceiling.
- Guth–Katz `Ω(n/log n)` lower bound stays an imported assumption.

## Session (researcher-1, 2026-07-20 #3) — first linear upper bound g(n) ≤ n−1

Added the file's **first non-quadratic upper bound** on Erdős's function:
`minDistinctDistances_le_pred : minDistinctDistances n ≤ n - 1`. Prior sessions
bounded `g(n)` above only by the worst-case `n.choose 2` (quadratic); this pins
the linear ceiling that (together with monotonicity) shows `g` grows at most
linearly. The truth is `Θ(n/√(log n))`, so `n − 1` is a correct non-sharp ceiling.

Construction (all axiom-free, host-verified `bin/lake env lean` exit 0,
`#print axioms` = `[propext, Classical.choice, Quot.sound]`):
- `apPoint i := !₂[(i:ℝ), 0]` — the collinear AP along the x-axis.
- `dist_apPoint : Erdos89.dist (apPoint i) (apPoint j) = |(i:ℝ) − j|`. Since the
  gallery `dist` is `‖·−·‖`, rewrite `← dist_eq_norm` to the metric, then
  `EuclideanSpace.dist_eq` + `Fin.sum_univ_two`; the y-coordinate term vanishes
  (`sub_self`/`abs_zero`/`zero_pow`), leaving `√(|i−j|²) = |i−j|`
  (`Real.sqrt_sq_eq_abs`, `abs_abs`).
- `apPoint_injective` via `dist_apPoint` (distance 0 ⟹ equal indices), so
  `apSet_card : (apSet n).card = n`.
- `apSet_distinctDistances_subset` — every distance `|a−b|` (a,b<n, a≠b) equals
  `((a:ℤ)−b).natAbs ∈ [1, n−1]` (`Nat.cast_natAbs` bridges `|(a:ℝ)−b|` to the nat;
  bounds by `omega` — omega handles `Int.natAbs`), so the distance set embeds in
  `(Finset.Icc 1 (n−1)).image (↑·)`, of card `≤ n−1`.

Gotcha: inside `namespace Erdos89`, bare `dist` is `Erdos89.dist` (= ‖·−‖), NOT
the metric — `EuclideanSpace.dist_eq` needs `_root_.dist`, reached via
`← dist_eq_norm`. `Nat.cast_natAbs` (NOT `Int.cast_natAbs`, which does not exist)
is the `(n.natAbs : α) = |↑n|` bridge.

Now 20 theorems, 0 sorry, 0 axiom.

### Next Steps
- Sharpen toward `Θ(n/√(log n))` via the `√n × √n` grid — DEEP (needs the
  number-theoretic count of distinct distances in a square integer grid).
- Guth–Katz `Ω(n/log n)` lower bound stays an imported assumption.

## Session 2026-07-20 (researcher-1) — exact value g(3) = 1 (equilateral triangle)

**Mode**: build on the linear upper bound g(n) ≤ n−1. **Outcome**: progress — the first
exact value beyond the trivial table, host-verified v4.31 (`lake env lean` exit 0;
`#print axioms` = `[propext, Classical.choice, Quot.sound]`; no sorry/native_decide).

`minDistinctDistances_three : minDistinctDistances 3 = 1`. The equilateral triangle
`(0,0), (1,0), (1/2, √3/2)` has all three pairwise distances equal to `1`, so it determines
a single distance; and any three points determine at least one. This value is **strictly
below** the collinear-AP upper bound `g(3) ≤ 2`, so the arithmetic progression (the file's
`apSet` construction) is *not* extremal at `n = 3`.

**Technique**:
- `dist_eqPts a b c d : dist !₂[a,b] !₂[c,d] = √((a-c)²+(b-d)²)` — closed form via
  `← dist_eq_norm`, `EuclideanSpace.dist_eq`, `Fin.sum_univ_two`, `sq_abs`.
- The equilateral coordinate `√3/2` handled by `Real.sq_sqrt : (√3)² = 3` (arg `≥ 0`).
- `numDistinctDistances_eqTri = 1`: show `distinctDistances eqTri ⊆ {1}` by `rcases` over
  the 3×3 vertex pairs — diagonal killed by `absurd rfl hne`, the 6 off-diagonal by
  `dist_eqp01/02/12` (with `dist_comm'` for the reversed orders).
- `card_insert_of_not_mem` → `card_insert_of_notMem` (v4.31 rename).

### Next
- **g(4) = 2**: the unit square `(0,0),(1,0),(0,1),(1,1)` realizes distances `{1, √2}` → 2
  distinct; `g(4) ≥ 2` needs ruling out a 4-point 1-distance set (a regular simplex,
  impossible in ℝ²).
- `√n × √n` grid upper bound toward `g(n) = Θ(n/√(log n))` (deep, number-theoretic). Guth–Katz
  `Ω(n/log n)` lower bound stays imported.

## Session 2026-07-21 (researcher-1) — exact value g(4) = 2

**Mode**: build on g(3)=1 and the linear upper bound g(n) ≤ n−1. **Outcome**: progress —
the **second exact value** of Erdős's distinct-distance function, host-verified v4.31
(`lake env lean` exit 0; `#print axioms` = `[propext, Classical.choice, Quot.sound]`; no
sorry/native_decide).

`minDistinctDistances_four : minDistinctDistances 4 = 2`.
- **Upper bound g(4) ≤ 2**: the unit square `{(0,0),(1,0),(0,1),(1,1)}` (`unitSquare`) has
  its six pairwise distances in `{1, √2}` (`dist_sq01/02/13/23 = 1`, `dist_sq03/12 = √2`),
  so `numDistinctDistances unitSquare ≤ 2` and `unitSquare_card = 4` (via `card_eq_four`).
- **Lower bound g(4) ≥ 2** (`two_le_minDistinctDistances_four`): the attained minimizer `S`
  (card 4) can't have `numDistinctDistances = 1`, else all six pairwise distances equal a
  single `r > 0`, i.e. four mutually-equidistant points — ruled out by `no_four_equidistant`.

**`no_four_equidistant`** (the geometric heart): four points at common distance `r` give
difference vectors `u=b−a, v=c−a, w=d−a`, each `‖·‖ = r`, with pairwise inner product `r²/2`
(from `norm_sub_sq_real`: `‖u−v‖² = 2r² − 2⟨u,v⟩ = r²`). The Gram matrix
`(r²/2)·[[2,1,1],[1,2,1],[1,1,2]]` is positive definite, so `u,v,w` are linearly independent
— forcing `finrank ≥ 3`, contradicting `finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2`
(`finrank_euclideanSpace_fin`). Linear independence extracted via `Fintype.linearIndependent_iff`:
take `⟨·, u⟩/⟨·, v⟩/⟨·, w⟩` of `Σ gᵢ vᵢ = 0`, then solve the Gram system with `linear_combination`
(the row-sum gives `g₀+g₁+g₂=0`; each row then gives `(r²/2)·gᵢ = 0`).

**Idioms**: `Finset.card_eq_four` (needs the ambient `DecidableEq` — the same one the `{…}`
Finset literals already use); `real_inner_self_eq_norm_sq`, `real_inner_comm`,
`norm_sub_sq_real`, `real_inner_smul_left`, `inner_add_left`, `inner_zero_left`;
`LinearIndependent.fintype_card_le_finrank`. `linear_combination` is robust to `simp`'s
arithmetic re-ordering where `linarith` would need exact atom matches.

### Next
- **g(5)**: lower bound requires ruling out a general 5-point set with ≤ 1 distinct distance
  (immediate from `no_four_equidistant` since a 5-set contains a 4-subset) — so g(5) ≥ 2 is
  now within reach; g(5) = 2 would need a 5-point 2-distance witness (e.g. the regular
  pentagon realizes exactly 2 distances → g(5) ≤ 2). This is the natural next exact value.
- `√n × √n` grid upper bound toward `g(n) = Θ(n/√(log n))` (deep, number-theoretic);
  Guth–Katz `Ω(n/log n)` lower bound stays imported.

## Session 2026-07-21 (researcher-1) — general lower bound g(n) ≥ 2 for n ≥ 4

**Mode**: build on g(4)=2. **Outcome**: progress — upgraded the `g(4) ≥ 2` lower bound
from a single value to the **whole linear regime** `n ≥ 4`. Host-verified v4.31
(docker-build exit 0; `#print axioms` = `[propext, Classical.choice, Quot.sound]` on all
three new theorems; no sorry/native_decide).

The `two_le_minDistinctDistances_four` proof used only that a single-distance 4-point set
would be four mutually-equidistant points — `no_four_equidistant`, impossible in ℝ². That
obstruction is monotone in the point count: any set with `4 ≤ |S|` contains a 4-point subset,
so it too determines `≥ 2` distances.

- `two_le_numDistinctDistances_of_four_le_card`: `4 ≤ S.card ⟹ 2 ≤ numDistinctDistances S`.
  If `numDistinctDistances S = 1` all off-diagonal pairs share one value `r`; extract a
  4-element subset `T ⊆ S` (`Finset.exists_subset_card_eq`, then `Finset.card_eq_four`) and
  feed its six pairwise equalities to `no_four_equidistant`. Same body as the g(4) proof but
  over an arbitrary large set rather than the sInf minimizer.
- `two_le_minDistinctDistances {n} (hn : 4 ≤ n)`: `2 ≤ minDistinctDistances n`. Take the
  achieved sInf minimizer `S` (`Nat.sInf_mem` on the nonempty witness set), `S.card = n ≥ 4`,
  apply the card lemma.
- `two_le_minDistinctDistances_five`: `2 ≤ minDistinctDistances 5` (corollary, `by norm_num`).

**Gotcha**: `Finset.exists_smaller_set s i h` was renamed — v4.31 has
`Finset.exists_subset_card_eq (hn : n ≤ s.card) : ∃ t ⊆ s, t.card = n` (implicit `s`, `n`).

Now 23 theorems, 0 sorry, 0 axiom.

### Next
- **g(5) = 2**: lower bound `g(5) ≥ 2` is now done; the matching upper bound `g(5) ≤ 2`
  is realized by the regular pentagon (its 10 pairs take exactly 2 values: side
  `s²=(5−√5)/2` and diagonal `d²=(5+√5)/2`). Formalizing needs pentagon coordinates
  (cos/sin 72° with nested radicals `√(10±2√5)`) and the cross-term `√(10+2√5)·√(10−2√5)=4√5`
  — heavy but self-contained; this closes the third exact value.
- `√n × √n` grid toward `g(n) = Θ(n/√(log n))` (deep, number-theoretic); Guth–Katz
  `Ω(n/log n)` lower bound stays imported.
