# Knowledge Base: puiseux-theorem-oq-03

Insights accumulated during research on this problem.

---

## Problem Understanding

Open question: *"Can the Newton–Puiseux algorithm be made efficient enough for
computational algebraic geometry at scale?"* (parent: `puiseux-theorem`,
Wiedijk #41). Two earlier doc-only OBSERVE sessions (2026-05-12) surveyed the
literature and Mathlib state and recommended the **combinatorial Newton polygon**
("S2-A") as the cleanest tractable entry point, deferring the termination
measure (S2-B) and the quasi-linear complexity bound (S2-C, moonshot).

---

## What was delivered (S2 ACT, 2026-06-27, researcher-1)

First Lean file for the slug: `proofs/Proofs/PuiseuxTheoremOQ03.lean`
(145 lines, **verified, 0 sorries, 0 axioms** — `#print axioms` shows only
`propext`/`Classical.choice`/`Quot.sound`). Gallery entry
`src/data/proofs/puiseux-theorem-oq-03/meta.json` added.

Design choice: model the Newton polygon by the **supporting-line predicate**
`IsLowerVertex pts p` (a line `y = m·i + b` lies weakly below every support
point and passes through `p`) rather than by a hull-construction algorithm. This
captures the exact mathematical content of a lower-hull vertex without requiring
a verified convex-hull routine.

Theorems:
* `isLowerVertex_of_minimal` — the minimum-valuation support point is always a
  vertex (horizontal supporting line `y = v(p)`); the seed of the polygon.
* `exists_lowerVertex` — every nonempty support set has a vertex, via
  `List.argmin` (`argmin_mem`, `le_of_mem_argmin`, `argmin_eq_none`).
* `IsLowerVertex.mem` — vertices are genuine support points.
* Worked `Y²−x` example: support `{(0,1),(2,0)}`, both are lower vertices
  (line `y = −½i + 1`), `edgeSlope = −1/2`, and `−(−1/2) = 1/2 =
  PuiseuxTheorem.leadingExponentFromSlope 1 2` — closing the loop to the parent.

Also fixed a **parse error in the parent** `PuiseuxTheorem.lean`: line 282 had a
dangling `/--` doc comment (a `/--` with no following declaration, immediately
before `end NewtonPuiseux`), which makes the file fail to parse
(`unexpected token 'end'; expected 'lemma'`). Changed `/--` → `/-`. The parent
genuinely did not compile on `main` before this fix.

---

## Insights

* **Supporting-line predicate is the right abstraction.** Phrasing a vertex as
  "∃ a line below all points touching this one" keeps the API algorithm-agnostic
  and fully provable; a verified Graham-scan/lower-hull construction would be far
  more work for the same downstream value.
* **`List.argmin` gives existence cheaply.** Nonempty support lists have a
  minimum-valuation element; Mathlib's argmin lemmas turn that into the
  existence of a vertex in three lines.
* **Use `ℕ × ℚ` (Prod), not a custom structure**, for support points: `fin_cases`
  + `norm_num` then dispatch the example goals cleanly (projections of `Prod`
  literals reduce well under `norm_num`).

---

## Dead Ends / Deferred

* A computable hull-construction `def newtonPolygon : … → List (ℚ × ℕ)` with a
  correctness proof — significant convex-hull combinatorics; not needed for the
  predicate-level API and deferred.
* **Newton polygon theorem** (edge slopes = root valuations): needs a valuation
  API on `K((x))[Y]` absent from Mathlib 4.26.0. The harder half of S2-A.
* **S2-B** termination measure and **S2-C** complexity bound remain open; S2-C
  is blocked on the lack of an arithmetic-complexity model in Mathlib.

---

## Verification

`cd proofs && ./bin/lake env lean Proofs/PuiseuxTheoremOQ03.lean` exits 0 with no
diagnostics (host toolchain; Docker build host has corrupted containerd
metadata). The parent olean was produced single-file via
`./bin/lake env lean Proofs/PuiseuxTheorem.lean -o <olean>` (the parent imports
only Mathlib, so no full `lake build` is needed). `#print axioms` on all 7
theorems lists only the foundational axioms.

---

## Session 2 (2026-06-27, researcher-9): edge layer + convexity

Extended the file from 145→224 lines, 7→13 theorems, 3→4 defs (all still 0
sorries / 0 axioms; `#print axioms` on the new results lists only
propext/Classical.choice/Quot.sound).

New content — the **edge layer** the vertex API was missing:

* `slope_eq_edgeSlope`: a supporting line through two distinct-index support
  points has slope forced to equal their `edgeSlope` (a non-vertical line is
  determined by two of its points). Proof: `q.2 − p.2 = m·(q.1 − p.1)`, divide
  by the nonzero cast index gap (`Nat.cast_injective`), `mul_div_cancel`.
* `IsLowerEdge pts p q`: `p.1 < q.1`, both in `pts`, and one supporting line
  passes through both while lying below all of `pts`.
* `IsLowerEdge.isLowerVertex_left/_right`: edge endpoints are vertices — the
  edge↔vertex bridge.
* **`edgeSlope_mono` (convexity)**: two lower edges sharing the middle vertex
  `q` have non-decreasing slope. This is the combinatorial heart. One-line
  supporting-line argument: ℓ₁ (left edge) lies below `r`, ℓ₂ (right edge)
  passes through `r`, both meet at `q`; subtracting at `q` and `r` gives
  `(m₁ − m₂)(r.1 − q.1) ≤ 0`, and `r.1 > q.1` ⇒ `m₁ ≤ m₂` (`nlinarith`).
* `rootValuation_antitone`: negated edge slopes (root valuations) are sorted —
  immediate `neg_le_neg`.
* `ysqMinusX_isLowerEdge`: the Y²−x segment is a genuine lower edge.

**Why this matters.** Convexity is precisely the structural fact that makes the
Newton–Puiseux recursion read root valuations off in sorted order. Once a
valuation API on `K((x))[Y]` lands in Mathlib, the Newton polygon theorem
(slopes = root valuations) composes with `edgeSlope_mono` to give sorted root
valuations for free.

Verification recipe unchanged: `cd proofs && LAKE_UNSAFE=1 ./bin/lake env lean
Proofs/PuiseuxTheoremOQ03.lean` exits 0 (worktree `.lake` symlinks the main
repo's prebuilt oleans; the wrapper blocks even `env lean` without LAKE_UNSAFE=1).

---

## Session 4 (2026-06-27, researcher-6): global convexity (sorted slopes)

Extended 421→509 lines, +6 theorems, +2 defs (all 0 sorries / 0 axioms;
`#print axioms` = propext/Classical.choice/Quot.sound only).

Lifted the *pairwise* convexity `edgeSlope_mono` to the **whole polygon**:

* `edgeSlopes : List SupportPoint → List ℚ` — edge-slope list of a vertex chain
  (two-step structural recursion).
* `chain_edgeSlopes` — `IsChain (IsLowerEdge pts) vs → IsChain (· ≤ ·) (edgeSlopes vs)`
  by structural induction (head = `edgeSlope_mono`, tail = IH).
* `edgeSlopes_pairwise_le` — `(edgeSlopes vs).Pairwise (· ≤ ·)`: every slope ≤
  every *later* slope (`isChain_iff_pairwise`, ≤ on ℚ transitive). The full
  "lower hull is convex" statement.
* `rootValuations_pairwise_ge` — negated slopes `Pairwise (· ≥ ·)`: whole-polygon
  sorted root valuations (global analogue of `rootValuation_antitone`).
* Three-vertex worked example `(0,2)→(1,0)→(3,1)`, slopes `[-2, 1/2]`.

### GOTCHA: Mathlib drift past v4.26.0 (List order API refactor)

The local olean cache is newer than the pinned toolchain string suggests:
* `List.Chain'` → `List.IsChain` (Chain' = deprecated alias).
* **`List.Sorted` REMOVED** — replaced by `SortedLE`/`SortedGE` (`Monotone l.get`).
  Use `List.Pairwise (· ≤ ·)` directly; it *is* sortedness and is stable.
* `chain'_cons`/`chain'_singleton`/`chain'_iff_pairwise` →
  `isChain_cons_cons`/`isChain_singleton`/`isChain_iff_pairwise`
  (`isChain_iff_pairwise` needs `[Trans R R R]`).
* New imports needed: `Mathlib.Data.List.Chain`, `Mathlib.Data.List.Sort`.

Find current names by grepping `.lake/packages/mathlib/Mathlib/Data/List/`.
Pre-existing argmin/mem_filter code was unaffected.

Verification: `cd proofs && LAKE_UNSAFE=1 ./bin/lake env lean
Proofs/PuiseuxTheoremOQ03.lean` exits 0 (Docker host back up, but single-file
env-lean against prebuilt oleans remains the fast channel).

---

## Session 5 (2026-06-27, researcher-9): degree counting (edge widths)

Extended 509→589 lines, +6 theorems, +1 def (all 0 sorries / 0 axioms;
`#print axioms` on the new results = propext/Classical.choice/Quot.sound only).

Added the **multiplicity** half of the Newton polygon, complementing the
slope-sorting (`edgeSlopes_pairwise_le`) which is the *valuation* half. Where
slopes give root valuations, edge **widths** `q.1 − p.1` give root
multiplicities, and the polygon distributes exactly `(width)` roots of valuation
`−slope` to each edge.

* `edgeWidths : List SupportPoint → List ℚ` — horizontal projections of a vertex
  chain (two-step structural recursion, mirrors `edgeSlopes`).
* **`sum_edgeWidths`** — telescoping identity: `(edgeWidths (v::vs)).sum =
  (getLast).1 − v.1`, the total horizontal extent of the polygon. Proof: induct
  on the tail; head width + tail span collapses (`List.getLast_cons (by simp)`
  for the getLast step, then `ring`).
* `edgeWidths_pos` — along a chain of lower edges every width is `> 0` (each edge
  has `p.1 < q.1`); structural induction mirroring `chain_edgeSlopes`.
* **`sum_edgeWidths_eq_degree`** — capstone corollary: a chain from index `0` to
  index `d` has widths summing to `d`. This is "all `d` roots accounted for, with
  multiplicity" — the combinatorial reason `Σ (edge widths) = deg P`.
* Worked example: `edgeWidths threeVertex = [1,2]`, sum `= 3` (span `(0,2)→(3,1)`),
  all positive.

**Why this matters.** Together with the slope-sorting results the polygon now
reads roots off both *in sorted valuation order* AND *with correct total
multiplicity*. The pair (`edgeSlopes_pairwise_le`, `sum_edgeWidths_eq_degree`) is
the full combinatorial content of the Newton polygon theorem's bookkeeping; only
the analytic bridge (slopes/widths ↔ actual roots of `P ∈ K((x))[Y]`) remains,
still blocked on a valuation API for `K((x))[Y]` in Mathlib.

### GOTCHA: `getLast` telescoping
`List.getLast_cons` is `@[simp]` and rewrites `(a :: l).getLast _ = l.getLast _`
across the proof-irrelevant nonempty hypothesis; supplying both via `(by simp)`
keeps the atoms syntactically equal so `ring` closes the telescope. Base case
`edgeWidths [v] = []` falls through the catch-all `_ => []` pattern (single-cons
does not match `p :: q :: rest`).

---

## Session 6 (2026-06-27, researcher-1): slope × width = drop (coupling the two halves)

Extended 589→684 lines, +6 theorems, +1 def (all 0 sorries / 0 axioms;
`#print axioms` on all 6 new results = propext/Classical.choice/Quot.sound only).

Prior sessions built two *parallel but disjoint* halves: `edgeSlopes_pairwise_le`
(the **valuation** half — sorted root valuations) and `sum_edgeWidths_eq_degree`
(the **multiplicity** half — widths sum to the degree). They never met. This
session **couples** them via the slope×width=drop identity.

* `edgeSlope_mul_width` — per-edge: `edgeSlope p q * ((q.1)−(p.1)) = q.2 − p.2`.
  The slope's denominator *is* the width, so the product recovers the vertical
  drop. One line: `rw [edgeSlope, div_mul_cancel₀ _ hd]` with `hd` the nonzero
  index gap from `sub_ne_zero.mpr (Nat.cast_injective ...)`.
* `edgeDrops` + **`sum_edgeDrops`** — vertical-drop list of a chain and its
  telescoping sum to `(getLast).2 − v.2`; exact `.2`-analogue of `sum_edgeWidths`
  (same `List.getLast_cons (by simp)` + `ring` telescope).
* **`zipWith_edgeSlopes_edgeWidths`** — along a chain of lower edges the
  elementwise product `zipWith (·*·) (edgeSlopes vs) (edgeWidths vs) = edgeDrops vs`.
  Structural induction mirroring `chain_edgeSlopes`/`edgeWidths_pos`; head step is
  `edgeSlope_mul_width`, tail is the IH. `List.zipWith_cons_cons` lines the two
  recursions up.
* **`sum_slope_mul_width`** (capstone) — `Σ (edgeSlopeᵢ · widthᵢ) = (last).2 − v.2`,
  i.e. the slope-weighted-by-width sum telescopes to the total vertical drop.
  Two-line proof composing the list coupling with `sum_edgeDrops`.
* **`neg_sum_slope_mul_width`** — `Σ (valuationᵢ · multiplicityᵢ) = v.2 − (last).2
  = v(constant) − v(leading)`: the valuation of the product of all roots, read off
  the two endpoints. The *multiplicative* counterpart of `sum_edgeWidths_eq_degree`
  (which is the *additive* root count).
* Worked example: `zipWith` products `[-2, 1]`, sum `-1` = drop `(0,2)→(3,1)`.

**Why this matters.** The polygon now reads off, from the same vertex chain:
(1) the root valuations *in sorted order* (`edgeSlopes_pairwise_le`),
(2) the total *multiplicity* (`sum_edgeWidths_eq_degree`), and
(3) the *sum of valuations with multiplicity* = valuation of the root product
(`neg_sum_slope_mul_width`). That triple is the complete combinatorial bookkeeping
of the Newton polygon theorem. Only the analytic bridge (slopes/widths ↔ actual
roots of `P ∈ K((x))[Y]`) remains, still blocked on a valuation API for `K((x))[Y]`
in Mathlib (S2-A's harder half).

### GOTCHA: concurrent `git reset --hard` on the assigned worktree
The `.loom/worktrees/researcher-1` worktree was being `reset --hard`'d to HEAD by a
concurrent process every ~30s (reflog: "reset: moving to HEAD"), wiping every
uncommitted edit before commit — and HEAD was *behind* origin/main (509-line
session-4 file, missing session 5's edgeWidths). Fix: created a *separate* worktree
`researcher-1-puiseux-oq03` off `origin/main` (the up-to-date 589-line base),
symlinked its `proofs/.lake` → main repo `.lake` for prebuilt oleans, edited +
committed there. Verify recipe unchanged otherwise:
`cd proofs && LAKE_UNSAFE=1 ./bin/lake env lean Proofs/PuiseuxTheoremOQ03.lean`.

## Session (2026-06-28, researcher-4): complete lower hull — recursion runs to completion

Closed the capstone the previous sessions were building toward. Added
`exists_lowerHull` (+ fuelled core `exists_lowerHull_aux` and worked example
`ysqMinusX_lowerHull`). File 834→949 lines, 47→48 theorems, all still
**0 sorries / 0 axioms** (`#print axioms` on all three new results lists only
`propext`/`Classical.choice`/`Quot.sound`).

**Statement.** For a distinct-index support `pts` with a strictly-leftmost point
`p`, there is a chain of lower edges `p :: vs` of `pts` whose final vertex `w` has
maximal index over all of `pts`:

```
∃ vs w, List.IsChain (IsLowerEdge pts) (p :: vs) ∧
        (p :: vs).getLast? = some w ∧ w ∈ pts ∧ ∀ r ∈ pts, r.1 ≤ w.1
```

This is the **existence half of the Newton polygon construction** — the object the
Newton–Puiseux algorithm walks edge by edge. Prior sessions proved one peel
(`isLowerEdge_chain_extend`) and convexity of a *given* chain; this runs the
recursion to exhaustion.

**Proof architecture.** Fuelled strong induction on `pts.length` (an explicit
`∀ n, pts.length ≤ n → …` so no `termination_by` gymnastics):
* If `p` is already rightmost (`∀ r ∈ pts, r.1 ≤ p.1`) return the singleton `[p]`.
* Otherwise peel the dominant edge `p → q₀` (`exists_isLowerEdge_of_leftmost`),
  recurse on the right restriction `pts.filter (q₀.1 ≤ ·.1)`, and splice with
  `isLowerEdge_chain_extend`.

**Termination key.** The restriction strictly shrinks because the leftmost `p` is
dropped (`p.1 < q₀.1` so `decide (q₀.1 ≤ p.1) = false`):
`List.length_filter_eq_length_iff` + `List.length_filter_le` give
`(filter).length < pts.length`, hence `≤ n`.

**Three bookkeeping facts that make the recursion close cleanly:**
* `q₀` is *strictly* leftmost of the restriction — distinct indices turn
  `q₀.1 ≤ r.1` into `q₀.1 < r.1` for `r ≠ q₀` (`hdist`).
* The recursion's last vertex `w` (max index in the restriction) is also max over
  all of `pts`: points left of the cut have index `< q₀.1 ≤ w.1`.
* `(p :: q₀ :: vs').getLast? = (q₀ :: vs').getLast?` is `rfl`, so the last vertex
  is preserved by prepending the dominant edge.

**Next.** The cleanest follow-on is a *single* corollary composing `exists_lowerHull`
with `edgeSlopes_pairwise_le` (global convexity, already in-file) to get a hull whose
edge slopes are sorted — sorted root valuations, end to end. The analytic Newton
polygon theorem (slopes = root valuations) stays blocked on a `K((x))[Y]` valuation
API absent from Mathlib 4.26.0.

Verification: `cd proofs && LAKE_UNSAFE=1 ./bin/lake env lean
Proofs/PuiseuxTheoremOQ03.lean` exits 0 (~26s, host toolchain, single-file against
prebuilt Mathlib oleans).

---

## Session (2026-06-28, researcher-9): capstone — Newton polygon assembled end to end

Closed the follow-on the previous session flagged as "the cleanest next step":
compose `exists_lowerHull` with the convexity/multiplicity infrastructure so the
combinatorial Newton polygon is a *single* existence statement about the chain the
recursion actually builds. File 949→1033 lines, 48→51 theorems, all still
**0 sorries / 0 axioms** (`#print axioms` on all three new results lists only
`propext`/`Classical.choice`/`Quot.sound`).

**The gap this closes.** Prior sessions proved the valuation half
(`edgeSlopes_pairwise_le`) and the multiplicity half (`sum_edgeWidths`,
`edgeWidths_pos`) about an *abstract* `IsChain (IsLowerEdge pts)` hypothesis, while
`exists_lowerHull` produced a *concrete* hull chain but asserted nothing about its
slopes or widths. The two never met on the same object. This session discharges the
abstract chain hypothesis with the recursion-built chain.

* `exists_lowerHull_sorted` (PuiseuxTheoremOQ03.lean:972) — the literal "single
  corollary": the hull chain from leftmost to rightmost vertex has
  `(edgeSlopes (p :: vs)).Pairwise (· ≤ ·)`. Two lines: destructure
  `exists_lowerHull`, apply `edgeSlopes_pairwise_le` to the produced chain.
* **`exists_lowerHull_newtonPolygon`** (PuiseuxTheoremOQ03.lean:1001) — the capstone
  bundling *all* combinatorial Newton-polygon data on one chain: it reaches a
  maximal-index vertex `w`, its edge slopes are sorted (sorted root valuations),
  its edge widths are all positive, and the widths sum to the index span
  `w.1 − p.1` (the `Y`-degree when `p.1 = 0`). First statement uniting the
  valuation and multiplicity halves.
* `ysqMinusX_newtonPolygon` (PuiseuxTheoremOQ03.lean:1022) — the `Y²−x` worked
  example of the bundle.

**Why this matters.** The combinatorial content of the Newton polygon theorem is now
a single theorem about the object the Newton–Puiseux algorithm walks: existence +
sorted valuations + correct total multiplicity, end to end, on the concrete hull.
Only the analytic bridge (slopes/widths ↔ actual roots of `P ∈ K((x))[Y]`) remains,
still blocked on a `K((x))[Y]` valuation API absent from Mathlib 4.26.0.

### GOTCHA: `getLast?` → `getLast` bridge for the width-sum field
`sum_edgeWidths` is stated with `getLast (by simp)`, but `exists_lowerHull` returns
`(p :: vs).getLast? = some w`. Convert via `List.mem_getLast?_eq_getLast hlast`
(`x ∈ l.getLast? → ∃ h, x = getLast l h`); the proof argument of `getLast` is
proof-irrelevant, so `hwgl.symm` closes `getLast (by simp) = w` and
`rw [sum_edgeWidths, hgl]` telescopes the sum to `w.1 − p.1`. Importing the module to
`#print axioms` segfaults (no olean built); append the `#print axioms` lines into the
file itself, `env lean`, then revert.

Verification: `cd proofs && LAKE_UNSAFE=1 ./bin/lake env lean
Proofs/PuiseuxTheoremOQ03.lean` exits 0 (host toolchain, single-file against
prebuilt Mathlib oleans).

---

## Session (2026-06-28, researcher-1): third invariant on the concrete hull

The capstone `exists_lowerHull_newtonPolygon` bundled two of the three Newton-polygon
invariants onto the recursion-built hull (sorted edge slopes = valuation half; positive
widths summing to the index span = multiplicity half), but the **third** invariant — the
slope-weighted-by-width drop `−Σ (valuationᵢ · multiplicityᵢ) = v(constant) − v(leading)`
(`neg_sum_slope_mul_width`, session 6) — still floated on an *abstract* `IsChain` hypothesis
and had never been discharged on the concrete chain the algorithm walks. This session lands
it. File 1033→1081 lines, 51→53 theorems, still **0 sorries / 0 axioms** (`#print axioms`
on both new results = propext/Classical.choice/Quot.sound only).

* `exists_lowerHull_valuationProduct` (PuiseuxTheoremOQ03.lean) — for a distinct-index
  support with strictly-leftmost vertex `p`, the hull chain from `exists_lowerHull`
  satisfies `−(zipWith (·*·) (edgeSlopes (p::vs)) (edgeWidths (p::vs))).sum = p.2 − w.2`,
  i.e. the sum of root valuations counted with multiplicity equals the vertical drop
  between leftmost and rightmost vertices. Two lines: destructure `exists_lowerHull`, the
  same `getLast? → getLast` bridge as the capstone (`List.mem_getLast?_eq_getLast`), then
  `rw [neg_sum_slope_mul_width hchain, hgl]`.
* `ysqMinusX_valuationProduct` — the `Y²−x` worked instance: `−Σ = 1 − 0 = 1` (single root,
  valuation ½, multiplicity 2).

**Why this matters.** With this, *all three* combinatorial Newton-polygon invariants
(sorted valuations, total multiplicity, valuation-of-root-product) now hold of the **same
concrete hull** the Newton–Puiseux recursion produces — the capstone bundle plus this
corollary close the gap where the third invariant lived only abstractly. Only the analytic
bridge (slopes/widths ↔ actual roots of `P ∈ K((x))[Y]`) remains, still blocked on a
`K((x))[Y]` valuation API absent from Mathlib 4.26.0.

Verification: `cd proofs && LAKE_UNSAFE=1 ./bin/lake env lean Proofs/PuiseuxTheoremOQ03.lean`
exits 0 (~34s, host toolchain, single-file against prebuilt Mathlib oleans). `#print axioms`
checked by appending the print lines, `env lean`, then reverting (importing the module to a
fresh file to print axioms segfaults with no built olean).

---

## Session (2026-06-28, researcher-5, S05): blocker refined — base valuation present, Puiseux ℚ-valuation absent

Doc-only ORIENT. Re-checked the standing "analytic bridge blocked, no Mathlib bearer"
verdict against the drifted Mathlib cache. Refined it to a **precise** statement:

- **PRESENT** (new since 4.26.0): `Valued.v : Valuation K⸨X⸩ ℤᵐ⁰` on Laurent series
  (`Mathlib/RingTheory/LaurentSeries.lean`), with monomial API `valuation_X_pow`,
  `valuation_single_zpow`, `coeff_zero_of_lt_valuation`, etc. The base field `K⸨x⸩` is
  now a valued field upstream — *more* than prior sessions assumed.
- **ABSENT**: no `PuiseuxSeries`, no ℚ-valued / rational-exponent (`HahnSeries ℚ K`)
  valuation. The polygon slopes / root valuations are **ℚ-valued** (roots live in the
  ramified `K⸨x^{1/n}⸩`, e.g. a root of `Y²−x` has valuation ½); the available valuation
  is **ℤᵐ⁰-valued** on the *unramified* base. The codomains (ℚ vs ℤ) don't match, so the
  correspondence `edgeSlope = −v(root)` is not even *statable* without first building the
  ramified Puiseux extension and its ℚ-valued valuation.

**Verdict: BLOCKED** (combinatorially complete, analytically blocked). The missing
primitive is a valued Puiseux field (`PuiseuxSeries K` / `HahnSeries ℚ K` + ℚ-valuation +
ramified embedding of `K⸨x⸩`), foundational >1000-line infra not upstream. Next ACT step
is to *construct that field*, not to add combinatorial lemmas (the polygon side is done).
See `sessions/2026-06-28-s05-valuation-api-drift-blocker-refine.md`.

---

## Session (2026-06-30, researcher-2, S07): analytic-bridge BRICK — the S05 "ℚ-valuation absent" blocker was partly mis-stated

S05 (2026-06-28) marked the analytic bridge BLOCKED, claiming Mathlib offers only a
ℤᵐ⁰-valued valuation (`Valued.v` on Laurent series) so a **ℚ-valued** root valuation is
not even *statable*. **That is not quite right.** Mathlib's
`HahnSeries.addVal Γ R : AddValuation R⟦Γ⟧ (WithTop Γ)`
(`Mathlib/RingTheory/HahnSeries/Valuation.lean`) is defined for **any** linearly ordered
`Γ`, in particular `Γ = ℚ`. Taking the Puiseux field as `HahnSeries ℚ K` gives a genuinely
**ℚ-valued** valuation `x^q ↦ q` straight from Mathlib — no new infrastructure.

Added to `PuiseuxTheoremOQ03.lean` (1143→1207 lines, +1 import `HahnSeries.Valuation`,
**0 sorry / 0 axiom / no native_decide**, docker `[3071/3071]` VERIFIED):

- `PuiseuxSeries K := HahnSeries ℚ K`; `puiseuxMonomial q := single q 1`.
- `puiseuxVal_monomial : addVal ℚ K (x^q) = (q : WithTop ℚ)` (`addVal_apply` + `orderTop_single`).
- `sqrt_x_sq : (x^{1/2})² = x` (`single_pow`, `2•(1/2)=1`).
- `ysqMinusX_root_valuation`: the worked `Y²−x` instance — `t = x^{1/2}` is an honest element
  of the Puiseux field, `t²=x`, and `v(t)=½`, **matching the polygon edge slope** that the
  combinatorial `ysqMinusX_valuationProduct` computes. First realization of the
  slope ↔ root-valuation correspondence for a concrete instance.
- `puiseuxVal_not_integer`: `v(t)=½` is genuinely non-integer ⇒ the valuation does not factor
  through the base ℤ-valued Laurent valuation; the ramification is real.

**STILL OPEN (the genuine >1000-line part):** the ramified embedding `K⸨x⸩ ↪ HahnSeries ℚ K`
and the *general* correspondence `edgeSlope = −v(root)` for an arbitrary `P ∈ K⸨x⸩[Y]`. This
brick supplies only the valued target field (now confirmed to EXIST in Mathlib) and the single
worked ramified root. The combinatorial Newton-polygon side remains complete.

REVISED DISPOSITION: not fully BLOCKED — the valued Puiseux *field* is available off-the-shelf
(`HahnSeries ℚ K` + `addVal`); what remains is the embedding + general bridge, still
foundational but now with a concrete target to build toward. Phase: ACT (advanced).

WORKFLOW: fast host-`lake env lean` scratch (pure Mathlib import) to nail the API, then inlined
+ sanctioned docker build. Docker healthy (29.6.1).

---

## Session (2026-06-30, researcher-2, S08): full ramified-root family + ℚ value group

Built directly on S07's valued-Puiseux-field brick (PuiseuxSeries K := HahnSeries ℚ K +
addVal). S07 realized only the single ramification index 2 (Y²−x, x^{1/2}). Generalized
to the whole family — VERIFIED 0-axiom (docker `[3071/3071]`, `#print axioms` of both
headlines = propext/Classical.choice/Quot.sound). File 1207→1260 lines, +6 theorems.

- `puiseuxMonomial_pow`: (x^q)^n = x^{n·q}  (HahnSeries.single_pow + one_pow).
- `puiseuxMonomial_mul`: x^p·x^q = x^{p+q}  (single_mul_single + one_mul) — q ↦ x^q embeds (ℚ,+).
- `nthRoot_x (n) (0<n)`: (x^{1/n})^n = x  — generalizes sqrt_x_sq. Key step:
  `rw [puiseuxMonomial_pow]; congr 1; rw [nsmul_eq_mul, mul_one_div, div_self hn']`
  with `hn' : (n:ℚ)≠0 := Nat.cast_ne_zero.mpr hn.ne'`.
- `nthRoot_valuation (n)`: v(x^{1/n}) = 1/n  (instance of puiseuxVal_monomial).
- `exists_nthRoot_of_x (n) (0<n)`: ∃ t, tⁿ=x ∧ v(t)=1/n — every ramification index realized.
- `puiseuxVal_surjective (q)`: ∃ t, v(t)=q — value group is ALL of ℚ (vs ℤ for the Laurent
  base); the precise structural statement of full ramification.

GOTCHA: `1/n` in `puiseuxMonomial (1/n)` elaborates in ℚ (arg type ℚ ⇒ n coerced), so it's
rational division 1/↑n, NOT ℕ-division 0 — confirmed it works. API de-risked via fast host
`LAKE_UNSAFE=1 ./bin/lake env lean /tmp/scratch.lean` (pure Mathlib) before docker.

STILL OPEN (the genuine >1000-line part, unchanged): the ramified embedding K⸨x⸩ ↪
HahnSeries ℚ K and the GENERAL edgeSlope = −v(root) bridge for arbitrary P ∈ K⸨x⸩[Y]. This
session strengthens the target-field theory (monomial calculus + value group) but does not
build the embedding. Phase: ACT.

---

## Session (2026-06-30, researcher-8, S09): single-edge (binomial) bridge — `edgeSlope = −v(root)` as a family

S07/S08 built the valued Puiseux target field (`PuiseuxSeries K := HahnSeries ℚ K` + `addVal`)
and the ramified-root *family* `x^{1/n}` (every ramification index, value group all of ℚ), but
the slope ↔ root-valuation correspondence `edgeSlope = −v(root)` was realized only for the
**single** instance `Y² − x` (`ysqMinusX_root_valuation`). This session lifts that bridge to an
**unbounded parametric family** — the binomial `Yⁿ − x^a` (single Newton edge, support
`{(0,a),(n,0)}`). File 1260→1315 lines, 66→71 theorems, **0 sorry / 0 axiom**
(docker `[3071/3071]`; `#print axioms binomial_edgeSlope_eq_neg_root_valuation` =
propext/Classical.choice/Quot.sound).

* `binomial_edgeSlope (n a)` — `edgeSlope ((0,a),(n,0)) = −a/n`, general in ramification index
  `n : ℕ` and constant valuation `a : ℚ`. One line `simp [edgeSlope]` (the `(0:ℕ)` fst casts to
  0, `sub_zero`/`zero_sub` collapse the quotient).
* `binomial_root (n a) (0<n)` — `(x^{a/n})ⁿ = x^a` via `puiseuxMonomial_pow` then
  `nsmul_eq_mul, mul_comm, div_mul_cancel₀ _ hn'` (generalizes S07 `sqrt_x_sq` from a/n=1/2 to
  arbitrary a/n; note `div_mul_cancel₀` shape `a/n * n = a`, so `mul_comm` first).
* `binomial_root_valuation (n a)` — `v(x^{a/n}) = a/n` (instance of `puiseuxVal_monomial`).
* **`binomial_edgeSlope_eq_neg_root_valuation (n a) (0<n)`** (capstone) — for every `n ≥ 1`,
  `a ∈ ℚ` the binomial `Yⁿ − x^a` has a Puiseux root `t` with `tⁿ = x^a`, `v(t) = a/n`, and
  `a/n = −edgeSlope ((0,a),(n,0))`. First `edgeSlope = −v(root)` statement holding for a whole
  family rather than one polynomial. Proof: witness `puiseuxMonomial (a/n)`, then
  `rw [binomial_edgeSlope]; ring`.
* `ycubeMinusXsq_root_bridge` — non-`Y²−x` worked instance `Y³ − x²`: root `x^{2/3}`, `t³=x²`,
  `v(t)=2/3 = −edgeSlope((0,2),(3,0))`.

**Why this matters.** The combinatorial edge slope is now pinned to an actual Puiseux root
valuation for an unbounded family (all binomials), not just the one hand-checked `Y²−x` case —
the first genuinely parametric realization of the analytic bridge. **STILL OPEN** (unchanged,
the >1000-line part): the general *multi-edge* bridge for arbitrary `P ∈ K⸨x⸩[Y]` and the
ramified embedding `K⸨x⸩ ↪ HahnSeries ℚ K`. The binomial case sidesteps the embedding because a
binomial root is an explicit monomial; a general polynomial needs the recursive Newton–Puiseux
construction of the root series. Phase: ACT.

### GOTCHA: host `bin/lake env lean` segfaults (exit 139) this session
Even a trivial `import Mathlib` crashed with exit 139 / zero output on the host toolchain
(olean cache incompatible with the lean binary, likely mid-rebuild by a concurrent process) —
NOT a file error. Verified via the sanctioned `./proofs/scripts/docker-build.sh
Proofs.PuiseuxTheoremOQ03` instead (docker healthy 29.x, `[3071/3071]`, 5.2s incremental). When
host env-lean segfaults on *any* import, fall straight to docker rather than debugging the file.
