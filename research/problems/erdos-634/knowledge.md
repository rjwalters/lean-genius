# Erdős #634 — Triangle Dissection into Congruent Pieces

Status: gallery entry present (`Erdos634Problem.lean`), status `axiomatized`.
The general classification of (T, R, N) is OPEN ($25 prize).

## Session (researcher-1, 2026-07-12): eliminate the 5 positive-result `sorry`s (base entry now sorry-free)

**Mode:** REVISIT · **Outcome:** progress (soundness/honesty cleanup, Docker-verified)

`Erdos634Problem.lean` carried **5 `sorry`s** in its positive-results section
(`squares_dissectable`, `two_squares_dissectable`, `three_squares_dissectable`,
`six_squares_dissectable`, `sum_squares_dissectable`). These were **permanently
unprovable**: the tiling predicate `Tiles` is declared as an opaque
`axiom … : Prop` with no constructor, so `IsDissectable n` (which requires a
`Tiles` witness) can never be a *theorem* for any `n` without the missing
polygonal-tiling API. A `sorry` there falsely claimed the results were proved.

**Fix (symmetric to Beeson):** the negative known-results are honestly
axiomatized (`seven_not_dissectable`, `eleven_not_dissectable`); the positive
known-results (Snover–Waiveris–Williams / classical reptiling) now are too. Added

- `def IsKnownPositive n` — the families `k² | 2k² | 3k² | 6k² | k²+m²`;
- `axiom known_positive_dissectable : IsKnownPositive n → IsDissectable n` (one
  disclosed axiom);
- the 5 positive results are now **one-line theorems** applying it (0 sorries);
- `not_isKnownPositive_seven` / `not_isKnownPositive_eleven` — **machine-checked**
  (`interval_cases` + `norm_num`) proofs that 7 and 11 (both ≡ 3 mod 4) lie in no
  positive family, so the positive axiom never yields `IsDissectable 7/11`. This
  upgrades the "consistent with Beeson" claim from prose to a verified no-clash.

Net: `sorries 5 → 0`, `axiomCount 4 → 5`, `lineCount 412 → 503`. Docker build
`[7743/7743]` exit 0 (Mathlib 4.26). Sole residual blocker unchanged: no
polygonal-tiling API in Mathlib to *define* `Tiles` and promote the positive
axiom to a theorem; the general classification stays OPEN ($25 prize).

## Session (researcher-6, 2026-07-09): soundness repair of the base entry

The shipped entry `Erdos634Problem.lean` was **logically inconsistent** — it
could derive `False` two independent ways. Both fixed in PR #36318.

1. **Area-only `IsDissectable` contradicted Beeson.** Dissectability was defined
   by area balance alone (`∑ pieceᵢ.area = T.area`). The companion
   `Erdos634AreaCollapse.lean` (merged, PR #35219, 0-axiom) proves this holds for
   *every* `n ≥ 1` (n equilateral pieces of side `1/√n`). Hence `IsDissectable 7`
   is provable, contradicting the axiom `¬IsDissectable 7`.
   **Fix:** added an abstract `axiom Tiles (T) (n) (pieces) : Prop`
   (covering + interior-disjointness) and made
   `IsDissectable n := ∃ T D, IsCongruentDissection T n D ∧ Tiles T n D.pieces`.
   The `Tiles` conjunct blocks the trivial equal-area witness, so Beeson's
   negatives are now consistent. `Tiles` stays abstract because Mathlib has no
   polygonal-tiling API.

2. **`congruent_implies_similar` was a `sorry` on a FALSE statement.** `Congruent`
   is on the unordered side multiset, but `Similar` was order-pinned
   (`T₂.a = k·T₁.a ∧ …`), which congruence does not imply (`(3,4,5)` vs `(4,3,5)`).
   **Fix:** restated `Similar` on the unordered multiset (faithful, relabelling-
   invariant); the theorem is now a real 1-liner
   `⟨1, one_pos, by simpa only [Congruent, one_mul] using h.symm⟩`.

Counts after: axioms 3→4, sorries 6→5 (the 5 remaining are the genuine reptiling
constructions `squares/two/three/six/sum`, blocked only on a Mathlib tiling API).

### Verification note
File elaborated cleanly: a Docker build reached
`[7743/7743] Building Proofs.Erdos634Problem (2.5s)` with zero type errors.
A fully green olean write was not obtainable this session (host Docker containerd
I/O errors + intermittent Mathlib-cache corruption / SIGBUS-135 under fleet load —
pure infrastructure, never type/math errors).

### Remaining / next directions
- The real open frontier is a **non-abstract `Tiles`**: a Mathlib polygonal-tiling
  API (covering + interior-disjoint measurable pieces). The `-oq-02` covering line
  (`Erdos634MedialCoveringOQ02.lean`) is the concrete-covering seed.
- Mathematically #634 itself (classification of achievable N) is open; `n=19` is
  the smallest unknown; `4k+3` prime conjecture (excluding 3).

## Session (researcher-3, 2026-07-09): interior-disjointness of the medial subdivision (corner pieces)

New file `Erdos634MedialDisjointOQ02.lean` — VERIFIED, clean Docker build
`[7744/7744] Built Proofs.Erdos634MedialDisjointOQ02 (5.5s)`, 0 axioms / 0 sorries.

Supplies the *interior-disjointness* complement of the covering line
(`Erdos634MedialCoveringOQ02` proved the covering half of oq-02). Over a
**non-degenerate** triangle (`LinearIndependent ℝ ![B - A, C - A]`, the two edge
vectors at `A` independent), the three **corner** medial pieces meet pairwise in
exactly one point — the midpoint of their shared side — hence have disjoint
interiors:

- `bary_unique` — barycentric coordinates unique in a non-degenerate triangle.
  Derived directly from `LinearIndependent.pair_iff` (no `AffineIndependent`
  API): from `a•A+b•B+c•C = a'•A+b'•B+c'•C` with unit sums, substitute
  `a=1-b-c`, then `linear_combination (norm := module) h` yields
  `(b-b')•(B-A)+(c-c')•(C-A)=0`, and pair_iff pins the coefficients.
- `pieceA_inter_pieceB = {midpoint A B}`, `pieceB_inter_pieceC = {midpoint B C}`,
  `pieceA_inter_pieceC = {midpoint C A}`. Proof recipe: expand each point's two
  triHull representations into `A B C`-barycentric form via the same
  `simp only [midpoint_eq_smul_add, invOf_eq_inv]; module` idiom as the covering
  file's `piece*_subset`; apply `bary_unique`; the resulting linear system forces
  the two apex coordinates to `1/2` (all discharged by `linarith`), pinning the
  point to the shared midpoint.

Reuses `triHull` from `Erdos634MedialCoveringOQ02` (imported), so results compose
with the covering statements.

### Still open on the oq-02 tiling frontier
- Interior-disjointness of each corner piece against the **central** piece (they
  meet in a shared *edge*, a `triHull` of two midpoints — a segment, not a point).
- The measure/area accounting to upgrade covering + interior-disjointness to a
  fully quantitative tiling (needs a Mathlib area/measure-of-triangle input).

## Session 2026-07-09 (researcher-1) — link KnownNonDissectable set to Beeson's axioms

**Mode:** REVISIT (base file). **Outcome:** +1 theorem, 0 new axioms (still 4), 0 new sorries.

The set `KnownNonDissectable = {7, 11}` (line 222) was defined and used only by
`non_dissectable_form` (its 4k+3 shape), but was never tied back to the two Beeson
axioms — the name asserted non-dissectability that the file never actually derived.
Added:

- `knownNonDissectable_not_dissectable : ∀ n ∈ KnownNonDissectable, ¬ IsDissectable n`
  Proof mirrors the verified `non_dissectable_form` exactly: `simp [KnownNonDissectable]`
  turns membership into `n = 7 ∨ n = 11`, then `cases`/`subst` discharges each with
  `seven_not_dissectable` / `eleven_not_dissectable`. A single membership→¬dissectable
  entry point; validates the set's naming.

The 5 remaining sorries (squares/two/three/six/sum reptiling constructions) stay blocked
on a Mathlib polygonal-tiling API — not touched (unsafe without a build, not session-sized).

**Build: UNVERIFIED — docker infra down** (containerd meta.db I/O error; host has no
Mathlib cache). By-eye-checkable, mirrors the adjacent verified `non_dissectable_form`.
File 373→386; theoremCount 16→17; section/annotation line refs ≥231 shifted +13.

## Session (researcher-2, 2026-07-11): corner/central interior-disjointness closes oq-02 tiling frontier

New file `Erdos634MedialCentralDisjointOQ02.lean` — VERIFIED axiom-free
(`lake env lean`, `#print axioms` = [propext, Classical.choice, Quot.sound] on all
three theorems), 0 sorries / 0 axioms.

This closes the last qualitative gap flagged by prior oq-02 sessions:
`Erdos634MedialCoveringOQ02` gave covering; `Erdos634MedialDisjointOQ02` gave the
three **corner–corner** overlaps (each a single vertex/midpoint). The one remaining
overlap was **corner vs. central** — which, unlike two corners, is a full shared
*edge*, not a point. Proven exactly:

- `pieceA_inter_central` — `triHull A mAB mCA ∩ central = segment ℝ mAB mCA`
- `pieceB_inter_central` — `triHull mAB B mBC ∩ central = segment ℝ mAB mBC`
- `pieceC_inter_central` — `triHull mCA mBC C ∩ central = segment ℝ mCA mBC`

(central = `triHull mBC mCA mAB`, matching `piece4_subset`'s vertex order.)

**Recipe** (reuses `bary_unique` + `triHull` from the two companions): expand each
intersection point into `A B C`-barycentric form two ways (corner-piece coords vs.
central coords via `simp only [midpoint_eq_smul_add, invOf_eq_inv]; module`), apply
`bary_unique`, then `linarith` solves the linear system. The key cancellation: the
corner apex coordinate `a` and the central's opposite coordinate `a'` satisfy
`a = -a'` (from the two midpoint-edge equations + unit-sum), and both are `≥ 0`, so
`a = 0` — pinning the point onto the shared edge. Reverse inclusion: a segment point
`s•p + t•q` sits in the corner piece with apex coord `0` and in the central piece
with the opposite coord `0`; `module` discharges both witnesses.

**Upshot:** every overlap among the four medial pieces is now proven to lie on a
shared edge (segment, empty interior) or vertex (point) — i.e. the pieces are
genuinely **interior-disjoint**. Together with `medial_covering`, the medial
subdivision is a bona-fide (non-abstract) tiling of an arbitrary non-degenerate
triangle, completing the qualitative content of oq-02. What remains beyond oq-02 is
purely the measure/area accounting (needs a Mathlib triangle-area input) and, for
#634 proper, the still-open classification of achievable congruent-piece counts N.

## Session (researcher-5, 2026-07-12): concrete non-abstract tiling witness for n=4

New file `Erdos634MedialTilingOQ02.lean` — VERIFIED axiom-free (`lake env lean` +
`lake build`, `#print axioms` = [propext, Classical.choice, Quot.sound] on both main
theorems), 0 sorries / 0 problem axioms, 156 lines.

**The gap this closes.** The base entry `Erdos634Problem.lean` routes dissectability
through an **abstract** `axiom Tiles (T) (n) (pieces) : Prop` (PR #36318, added only to
make Beeson's `¬IsDissectable 7/11` consistent). Because `Tiles` is opaque there is no
introduction rule, so every *positive* dissection there (`squares_dissectable`,
`twenty_seven_dissectable`, …) is stuck at `sorry`: no concrete tiling can be witnessed.

This file supplies the missing concrete content at the base case `n = 4 = 2²`:

- `IsCongruentTiling A B C n pieces` — a **non-abstract** structure (3 fields): closed
  `triHull` pieces cover the triangle (`covers`, `⋃`-form), distinct pieces have disjoint
  relative interiors (`interior_disjoint`, via `triHullOpen`), and all pieces are
  mutually `TriCongruent` (isometry-congruent). No opaque axiom, no Lebesgue measure, no
  dimension hypothesis — the honest replacement for the base file's `Tiles`.
- `medialPieces A B C : Fin 4 → V×V×V` = `![T1,T2,T3,T4]` (corner-A, corner-B, corner-C,
  central), with `@[simp]`/`rfl` index lemmas.
- `medial_isCongruentTiling` (CAPSTONE) : over a non-degenerate triangle
  (`LinearIndependent ℝ ![B-A, C-A]`) the medial subdivision inhabits
  `IsCongruentTiling A B C 4 (medialPieces A B C)` — assembles the three previously
  separate results (`medial_four_congruent` from the congruence entry, `medial_covering`,
  `medial_interiors_pairwise_disjoint`) into ONE concrete tiling witness.
- `exists_congruentTiling_four` : `∃ pieces, IsCongruentTiling A B C 4 pieces` — the
  positive `n=4` dissection realised axiom-free, the concrete analogue of
  `Erdos634Problem.squares_dissectable 2` that the opaque `Tiles` axiom cannot exhibit.

Proof mechanics: `covers` via `medial_covering` + `⋃(Fin 4) = 4-union` by `fin_cases`;
`interior_disjoint` and `congruent` via `fin_cases i <;> fin_cases j <;> first | …` over
the 6 disjointness lemmas (with `Set.inter_comm` for reversed order) and the 6 congruence
witnesses (`.symm`/`TriCongruent.refl`). All piece-projection reductions are `rfl`-defeq
(the `medialPieces_*` `@[simp]` lemmas), so `exact` closes each case without simp.

**Honesty.** This does NOT dissolve the base file's `Tiles` axiom (that abstract
predicate still guards Beeson's negatives) and does NOT prove #634 itself (open $25
problem, classification of achievable N). It provides the first concrete, machine-checked
*positive* tiling witness for the reptiling base case — the k=2 square-reptiling cell —
that the abstract framework could only assert. Over an arbitrary real normed space.

### Next directions (unchanged frontier)
- Planar (V = ℝ²) Lebesgue/area accounting to upgrade to a measure-theoretic tiling.
- Iterate the medial subdivision (self-similarity) to realise `IsCongruentTiling` at
  `n = 4^j`, and generalise the concrete witness to the full k-subdivision of OQ-01.
