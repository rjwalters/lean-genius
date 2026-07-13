# pascals-hexagon-oq-03 — S4 PREP survey

**Date**: 2026-05-12
**Author**: researcher-8
**Scope**: doc-only forward-planning survey of the three remaining sub-OQs (OQ-02, OQ-03, OQ-04) after PR #18185 closes OQ-03-OQ-01.
**No Lean source changes**, no `meta.json`/`state.md`/`json` edits — pristine orthogonal to in-flight PR #18185 (researcher-11, S3d homomorphism completion).

## Provenance / scope

- PR #18185 (open, researcher-11) shows the path from S1–S3c-prep-2 to a fully-discharged OQ-03-OQ-01 (`card_hexagonalGroup = 12` and the Lagrange consequence `card_hexagon_labelings = 60`). When it merges, sorry count drops 5 → 3 in `proofs/Proofs/PascalsHexagonOQ03.lean`, leaving:
  - `pascalLine` (line 403, `noncomputable def … := sorry`) — **OQ-03-OQ-02**.
  - `steiner_count_eq_20` (line 442, `theorem … := by sorry`) — **OQ-03-OQ-03**.
  - `kirkman_count_eq_60` (line 467, `theorem … := by sorry`) — **OQ-03-OQ-04**.
- This survey is forward-planning only. It produces neither Lean lemmas nor sorry-count changes.
- The S1 scaffold (PR #17916) lists an **optional** OQ-03-OQ-05 (Cayley + Plücker + Salmon configurations, ~200 lines, "deferred"). That sub-OQ is **out of scope** here; its status remains "deferred" and the survey does not touch it.

## Parent-axiom + Mathlib-API audit

Both sides of the bridge between `Proofs/PascalsHexagon.lean` and `Proofs/PascalsHexagonOQ03.lean` are pinned to specific identifiers. This section lists every external name the three remaining sorries plausibly depend on, with file:line locators (verified against the current HEAD of `proofs/Proofs/PascalsHexagon.lean`, 1278 lines).

### From the parent file `Proofs/PascalsHexagon.lean`

| Identifier | Kind | Location | Used in sub-OQ |
|---|---|---|---|
| `ProjPoint` | `abbrev := Fin 3 → ℝ` | 63 | OQ-02, OQ-03, OQ-04 |
| `ProjLine` | `abbrev := Fin 3 → ℝ` | 70 | OQ-02, OQ-03, OQ-04 |
| `ProjPoint.valid` | `def` (nonzero) | 66 | OQ-02 |
| `ProjLine.valid` | `def` (nonzero) | 73 | OQ-02 |
| `Conic` | declared elsewhere | (cf. `pointOnConic` 125) | OQ-02 |
| `lineThrough` | `noncomputable def` (cross product) | 80 | OQ-02 |
| `lineIntersection` | `noncomputable def` (cross product) | 83 | OQ-02 |
| `pointOnLine` | `def` (dot product = 0) | 86 | OQ-02, OQ-03, OQ-04 |
| `collinear` | `def` (3×3 det = 0) | 103 | OQ-02 |
| `concurrent` | `def` (3×3 det = 0 of three lines) | 107 | OQ-03, OQ-04 |
| `pointOnConic` | `def` | 125 | OQ-02 |
| `InscribedHexagon` | `structure` with fields `A..F` + 6 `pointOnConic` + 6 `valid` | 141 | OQ-02 |
| `pascalP` / `pascalQ` / `pascalR` | `noncomputable def` (opposite-side intersections of `hex`) | 163, 167, 171 | OQ-02 |
| `pascalConstraint` | `def` (det of three intersection points) | 183 | OQ-02 (indirectly) |
| `conic_implies_pascal_constraint` | **axiom** | 208 | not directly — OQ-01 of the parent |
| `pascal_hexagon_theorem` | `theorem` (`collinear (pascalP hex) (pascalQ hex) (pascalR hex)`) | 224 | **OQ-02 — primary tool** |
| `crossProduct_smul_left/right` | `theorem` | 599, 605 | OQ-02 well-definedness (lineThrough swap) |
| `det_threeVectorMatrix_smul` | `theorem` | 696 | OQ-02 well-definedness |
| `pascalConstraint_smul` | `theorem` | 706 | OQ-02 well-definedness |
| `collinear_projTransform` | `theorem` (collinearity invariant under invertible M) | 452 | OQ-03, OQ-04 (potential — projective normalization) |
| `pascalConstraint_projTransform` | `theorem` (constraint invariant under invertible M) | 494 | OQ-03, OQ-04 |
| `pappus_theorem` / various dual / Pappus / Brianchon scaffolding | mostly statements | 244–308 | not needed |

**Key bridge**: `pascal_hexagon_theorem` is a *fully-proved* theorem (modulo `conic_implies_pascal_constraint`). It is the only tool OQ-02 needs to actually build a Pascal line — it tells us that for any inscribed hexagon, the three opposite-side intersection points are collinear.

### From the OQ-03 file `Proofs/PascalsHexagonOQ03.lean`

| Identifier | Kind | Location | Status |
|---|---|---|---|
| `hexRot` | `def := finRotate 6` | 121 | unconditional |
| `hexRev` | `def` (Fin.rev) | 125 | unconditional |
| `hexagonalGroup` | `def := Subgroup.closure {hexRot, hexRev}` | 141 | unconditional |
| `hexRot_pow_six` / `hexRev_mul_self` / `hexRev_hexRot_hexRev` | S2 dihedral relations | 165, 173, 179 | unconditional (`ext + fin_cases + decide`) |
| `hexRot_pow_lt_six_ne_one` / `orderOf_hexRot` / `orderOf_hexRev` | S3a order facts | 198, 208, 214 | unconditional |
| `hexRev_inv` / `hexRev_semiconj_hexRot{,_pow}` / `hexRev_hexRot_pow_hexRev` | S3b-prep semiconjugacy | 237, 244, 255, 268 | unconditional |
| `hexRot_pow_zmod_val_{add,neg,sub}` | S3c-prep-2 modular helpers | (~PART 2e) | unconditional |
| `card_sym6 : Fintype.card (Sym(6)) = 720` | `theorem` | 348 | unconditional |
| `HexagonLabeling := Sym(6) ⧸ hexagonalGroup` | `abbrev` (quotient type) | 340 | type-level |
| `card_hexagonalGroup` / `card_hexagon_labelings` | `theorem … := by sorry` | 378, 388 | **resolved by PR #18185** |
| `pascalLine` | `noncomputable def … := sorry` | 403 | **OQ-02** |
| `hexagrammum_mysticum_pascal_lines` | `theorem` (trivial existence wrapper) | 415 | already proved (no sorry) |
| `SteinerPoint` / `KirkmanPoint` | `structure` | 430, 455 | unconditional |
| `steiner_count_eq_20` / `kirkman_count_eq_60` | `theorem … := by sorry` | 442, 467 | **OQ-03 / OQ-04** |

### Mathlib API (pinned at `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

Beyond what is already used in S1–S3:

| Identifier | Module | Purpose |
|---|---|---|
| `QuotientGroup.lift` | `Mathlib/GroupTheory/QuotientGroup/Basic.lean` | lift `f : G → α` to `G ⧸ N → α` (when `α` is a group, `N` normal) — **NOT applicable here**: `ProjLine` is not a group, and `hexagonalGroup` need not be normal in `Sym(6)`. Use `Quotient.liftOn` instead. |
| `Quotient.liftOn` | `Mathlib/Data/Quot.lean` | lift `f : G → α` along the setoid quotient — works for any target type. |
| `QuotientGroup.eq` | `Mathlib/GroupTheory/QuotientGroup/Basic.lean` | `(a : G ⧸ H) = b ↔ a⁻¹ * b ∈ H` — the well-definedness condition becomes `f(a) = f(b)` whenever `a⁻¹ * b ∈ hexagonalGroup`. |
| `MulAction.toPermHom` | `Mathlib/GroupTheory/GroupAction/Defs.lean` | turn a `MulAction G α` into `G →* Equiv.Perm α` — **possibly useful** for defining `Sym(6)` acting on `InscribedHexagon C` by relabeling. |
| `Finset.card_image_iff` / `Finset.card_image_of_injOn` | `Mathlib/Data/Finset/Card.lean` | for counting Steiner / Kirkman triples once enumerated. |
| `Finset.sum_choose` / `Finset.card_powersetCard` | `Mathlib/Combinatorics/Choose/Basic.lean` | $\binom{60}{3}$-style enumeration if needed. |

**Quotient-lifting decision**: The OQ-03 file declares `HexagonLabeling := Sym(6) ⧸ hexagonalGroup` as a *group quotient*, hence `HexagonLabeling` is a `Quotient` w.r.t. the `leftRel` setoid. `Quotient.liftOn` and `QuotientGroup.eq` are the relevant tools (not `QuotientGroup.lift`, which requires the target to be a group and the subgroup normal).

## OQ-03-OQ-02 — `pascalLine` definition + well-definedness

### Current sorry shape

```lean
noncomputable def pascalLine
    (C : Conic) (hex : InscribedHexagon C) (lbl : HexagonLabeling) : ProjLine :=
  sorry
```

This is a **definitional sorry** (in `def`, not in `by`). Aristotle skips it; it must be replaced by a real definition by a human/agent. The downstream theorems `steiner_count_eq_20`, `kirkman_count_eq_60`, and the structures `SteinerPoint`, `KirkmanPoint` all reference `pascalLine`, so this is the binding-tightest sorry in the file.

### Proposed strategy

**Step 1**: Define a relabeling action of `Sym(6)` on `InscribedHexagon C`.

```lean
def permuteHexagon (C : Conic) (hex : InscribedHexagon C) (π : Equiv.Perm (Fin 6)) :
    InscribedHexagon C :=
  let vertex : Fin 6 → ProjPoint
    | 0 => hex.A | 1 => hex.B | 2 => hex.C' | 3 => hex.D | 4 => hex.E | 5 => hex.F
  let onConic : ∀ i, pointOnConic (vertex i) C
    | 0 => hex.hA | 1 => hex.hB | 2 => hex.hC | 3 => hex.hD | 4 => hex.hE | 5 => hex.hF
  let validity : ∀ i, ProjPoint.valid (vertex i)
    | 0 => hex.hAvalid | 1 => hex.hBvalid | 2 => hex.hCvalid
    | 3 => hex.hDvalid | 4 => hex.hEvalid | 5 => hex.hFvalid
  { A := vertex (π 0), B := vertex (π 1), C' := vertex (π 2),
    D := vertex (π 3), E := vertex (π 4), F := vertex (π 5),
    hA := onConic (π 0), hB := onConic (π 1), hC := onConic (π 2),
    hD := onConic (π 3), hE := onConic (π 4), hF := onConic (π 5),
    hAvalid := validity (π 0), hBvalid := validity (π 1), hCvalid := validity (π 2),
    hDvalid := validity (π 3), hEvalid := validity (π 4), hFvalid := validity (π 5) }
```

This builds an `InscribedHexagon C` where vertex `i` is the `π i`-th original vertex. Note: this is **right action** in the sense `permuteHexagon (permuteHexagon hex π₁) π₂ = permuteHexagon hex (π₁ * π₂)` if we read multiplication left-to-right. Either left- or right-action conventions can be used; the well-definedness check must be aligned to the convention chosen for the `HexagonLabeling` quotient.

**Step 2**: Define a raw "Pascal line" function on `Sym(6)`.

```lean
noncomputable def rawPascalLine
    (C : Conic) (hex : InscribedHexagon C) (π : Equiv.Perm (Fin 6)) : ProjLine :=
  lineThrough (pascalP (permuteHexagon C hex π)) (pascalQ (permuteHexagon C hex π))
```

This makes the line `PQ` through the first two Pascal intersection points of the permuted hexagon. The third point `R` is collinear with them by `pascal_hexagon_theorem`, so we capture the full line.

**Caveat — degeneracy**: When `pascalP (permuteHexagon …) = pascalQ (permuteHexagon …)` (e.g., when the two intersection points coincide), `lineThrough P P = P × P = 0` is not a valid `ProjLine`. The well-definedness check will need a side hypothesis that the hexagon is in "general position" — or we need to choose a triple {P, Q, R} of which at least two are distinct, which is generally guaranteed for a non-degenerate conic but not encoded in `InscribedHexagon` as-is. **This is a genuine open subtlety**: the parent file's `pascal_hexagon_theorem` proves collinearity, but does NOT prove distinctness of the three Pascal intersection points. For the well-definedness of `pascalLine`, we either:
- (a) assume `Conic.nondegenerate` as a hypothesis (already a parent-file `def`); or
- (b) split into cases — when P = Q, return `lineThrough Q R` or `lineThrough P R` instead; or
- (c) hand-wave with a `Classical.choice` over a valid-line predicate.

Option (b) is most natural and matches Mathlib conventions for `noncomputable def` over partial structures. Option (a) would require strengthening `InscribedHexagon` to bundle the non-degeneracy hypothesis, which is a parent-file change and orthogonal to OQ-02.

**Step 3**: Show `rawPascalLine` is invariant under multiplication by elements of `hexagonalGroup` on the right (or left, depending on quotient convention). Reduce to the two generators `hexRot` and `hexRev` (since `hexagonalGroup = Subgroup.closure {hexRot, hexRev}`):

```lean
theorem rawPascalLine_hexRot
    (C : Conic) (hex : InscribedHexagon C) (π : Equiv.Perm (Fin 6)) :
    rawPascalLine C hex (π * hexRot) = rawPascalLine C hex π := …

theorem rawPascalLine_hexRev
    (C : Conic) (hex : InscribedHexagon C) (π : Equiv.Perm (Fin 6)) :
    rawPascalLine C hex (π * hexRev) = rawPascalLine C hex π := …
```

The geometric content of each:

- **Rotation case**: `hexRot = finRotate 6` cycles `0→1→2→3→4→5→0`. The permuted hexagon `(π * hexRot)` shifts each vertex: position 0 picks up old position 1, position 1 picks up old position 2, etc. The new `pascalP', pascalQ', pascalR'` are:
  - $P' = \mathrm{lineThrough}(B, C) \cap \mathrm{lineThrough}(E, F)$ = the old $Q$
  - $Q' = \mathrm{lineThrough}(C, D) \cap \mathrm{lineThrough}(F, A)$ = the old $R$
  - $R' = \mathrm{lineThrough}(D, E) \cap \mathrm{lineThrough}(A, B)$ = the old $P$
  So $\{P', Q', R'\} = \{Q, R, P\}$ as sets — same trio. The line `lineThrough P' Q'` equals `lineThrough Q R`, which is the same line as `lineThrough P Q` (modulo nonzero scalar) by `pascal_hexagon_theorem` (collinearity of $P, Q, R$) plus a `crossProduct` identity.

- **Reversal case**: `hexRev` swaps `0↔5, 1↔4, 2↔3`. The permuted hexagon reads `FEDCBA`. The new intersection points are:
  - $P' = \mathrm{lineThrough}(F, E) \cap \mathrm{lineThrough}(C, B)$
  - $Q' = \mathrm{lineThrough}(E, D) \cap \mathrm{lineThrough}(B, A)$
  - $R' = \mathrm{lineThrough}(D, C) \cap \mathrm{lineThrough}(A, F)$
  Since `lineThrough q p = -(lineThrough p q)` in projective coordinates (the cross product anti-commutes) and the negation factors out cleanly via `crossProduct_smul_{left,right}` + `lineIntersection_smul_{left,right}` (the latter holds because $(c \cdot \ell) \times (c' \cdot \ell') = c c' (\ell \times \ell')$ for `c, c' ≠ 0`), we get $P' = c_1 \cdot Q$, $Q' = c_2 \cdot P$, $R' = c_3 \cdot R$ for some nonzero scalars $c_i$. The resulting line `lineThrough P' Q'` equals the line `lineThrough Q P` (modulo nonzero scalar) = same line as `lineThrough P Q`.

  **Important**: Projective lines are equivalence classes under nonzero scalar multiplication, but the type `ProjLine := Fin 3 → ℝ` does NOT quotient by scalars. So `lineThrough P Q ≠ lineThrough Q P` as elements of `Fin 3 → ℝ` (they differ by a sign), and "well-definedness" of `pascalLine` must allow for nonzero scalar multiples. This means the **target of `pascalLine` cannot be `ProjLine` if we want strict equality on the quotient** — we must either:
  - (a) quotient `ProjLine` by `ℝˣ`-scaling (introducing a new `ProjLineClass`); or
  - (b) prove well-definedness up to nonzero scalar only, returning a `ProjLine` but stating downstream theorems in scalar-invariant form; or
  - (c) choose a canonical representative (e.g., normalize so the first nonzero coordinate is 1) via `Classical.choice` or a `decide`-based normalization.

  Each route has costs. Route (a) is the cleanest mathematically but requires a new wrapper type and downstream rework. Route (b) is the cheapest but inflates each Steiner / Kirkman count proof with side conditions. Route (c) introduces noncomputability and casework on degeneracies.

**Recommendation**: Route (a) — introduce a `ProjLineClass := Quotient ScalarSetoid` in a new mini-section of `PascalsHexagonOQ03.lean`. This is ~50 lines of boilerplate but makes OQ-03 / OQ-04 statements clean (Steiner / Kirkman points are about *distinct* Pascal lines, which requires scalar-invariance). The parent file does NOT use `ProjLineClass`, so its `pascal_hexagon_theorem` returns a raw `ProjLine`; we'd `Quotient.mk` it into `ProjLineClass` at the OQ-03 boundary.

### Sorry budget for OQ-02

| Component | Lines | Sorry delta |
|---|---|---|
| `permuteHexagon` (raw definition) | ~30 | 0 (no sorry) |
| `rawPascalLine` (raw definition) | ~10 | 0 |
| `ProjLineClass` quotient + smul invariance lemmas | ~50 | 0 |
| `rawPascalLine_hexRot` (rotation invariance, modulo scalar) | ~30 | 0 (mechanical from `pascal_hexagon_theorem` + crossProduct identities) |
| `rawPascalLine_hexRev` (reversal invariance, modulo scalar) | ~30 | 0 |
| `rawPascalLine_subgroup_inv` (`Subgroup.closure_induction` over `hexagonalGroup`) | ~25 | 0 |
| `pascalLine` (final `Quotient.liftOn` definition) | ~10 | **−1 (closes the def sorry at line 403)** |

**Estimated total**: ~185 lines, no remaining sorries in OQ-02. Realistic risk: the `ProjLineClass` wrapper may need 1–2 sub-lemmas that bottom out in `simp` failures (cross-product algebra), pushing the total to ~220–250 lines. Suggest decomposing into S4a (`permuteHexagon` + `rawPascalLine` + degenerate-case handling), S4b (scalar-invariance lemmas + `ProjLineClass`), S4c (the two invariance theorems), S4d (the final lift).

## OQ-03-OQ-03 — `steiner_count_eq_20`

### Current sorry shape

```lean
theorem steiner_count_eq_20
    (C : Conic) (hex : InscribedHexagon C)
    [Fintype (SteinerPoint C hex)] :
    Fintype.card (SteinerPoint C hex) = 20 := by
  sorry
```

This is a `by sorry`, so Aristotle could *in principle* attempt it. In practice the `Fintype` instance is provided as a parameter (square-bracket), and the theorem asserts a specific cardinality — Aristotle has no way to discharge this without the geometric machinery.

### Combinatorial backbone

A **Steiner triple** is a 3-element subset of the 60 hexagonal labelings such that the 3 corresponding Pascal lines are concurrent. Steiner showed in 1828 that exactly 20 such triples exist, and each yields a unique concurrent intersection point (the *Steiner point*).

The classical (Conway-Ryba 2012, "The 60 Pascal Lines, 20 Steiner Points, ..." and many earlier sources) characterization: the 20 Steiner triples are precisely the orbits of an explicit outer automorphism of `Sym(6)`. More directly, the Steiner triples are in bijection with the 20 "3-element subsets of a 6-element set" (i.e., $\binom{6}{3} = 20$), with each subset $\{i, j, k\} \subset \{0..5\}$ giving rise to a Steiner triple via a specific labeling pattern: the three hexagons $(i, j, k, *, *, *)$, $(j, k, i, *, *, *)$, $(k, i, j, *, *, *)$ where `*` denotes the complementary 3 vertices in a fixed order.

### Proposed proof strategy

**Phase A — combinatorial enumeration**: Define a `Finset (Fin 6 → 3-subset)` (or equivalently a `Finset (Fin 20)`) parametrizing the 20 Steiner triples explicitly. Show its cardinality is 20 by `decide` or `Fintype.card_fin`. **~50 lines, 0 sorry.**

**Phase B — concurrence for one representative triple**: Pick a single Steiner triple $T_0$ (e.g., the one parametrized by $\{0, 1, 2\}$) and prove that the three Pascal lines associated with $T_0$ are concurrent — i.e., their `lineIntersection` triple-determinant vanishes. **~80–150 lines, 0 sorry** (computational, closes via `ring` over polynomial coordinates if we use the `pascal_std_conic_parametrized` route; OR via `Cayley-Bacharach` axiom which is already available from the parent).

  This is the hardest sub-step. Two options:
  - **B1 (Cayley-Bacharach)**: Each Steiner triple corresponds to a pair of cubic curves intersecting in 9 points (the 6 conic points + 3 Pascal intersections). By Cayley-Bacharach, the 3 Pascal intersections are collinear, and three different Steiner triples sharing two of these points are concurrent at the third. This requires axiomatizing or proving CB itself — significant lift.
  - **B2 (coordinate proof on standard conic)**: Use `pascal_std_conic_parametrized` analog: parametrize the 6 points as $P(a_1), \dots, P(a_6)$ on the standard conic and prove the 3-line concurrence as a polynomial identity in $(a_1, \dots, a_6)$. The `concurrent` def at parent:107 unfolds to a 3×3 determinant of `ProjLine`s, each of which is a cross product of points; we get a polynomial of degree ~24 in 6 variables. The `ring` tactic at `maxHeartbeats 2000000` was sufficient for the basic `pascal_std_conic_parametrized` (degree 12, 6 variables, ~3500 terms cancel); the Steiner case is ~4× larger and may need `maxHeartbeats 8000000` and split into multiple sub-determinants.
  - **B3 (axiomatize Steiner)**: Add a parent-file axiom `steiner_triple_concurrent` analogous to `conic_implies_pascal_constraint`. Cheapest but adds 1 to the axiom count. Acceptable per the project's Axiom Integrity Policy if explicitly declared in `meta.json:assumptions` and marked `badge: "axiom"`.

  **Recommendation**: B3 for the initial sub-OQ-03 PR (preserve "build pending" status and keep the axiom budget transparent); B2 is a follow-up "axiom elimination" target analogous to `pascal_std_conic_parametrized`.

**Phase C — propagation by `Sym(6)` action**: Show all 20 Steiner triples are concurrent by pushing the proof for $T_0$ along the action of `Sym(6)` (which permutes hexagonal labelings but preserves the conic and the underlying 6 points). Uses `pascalConstraint_projTransform` analog plus the symmetry that `concurrent` is invariant under coordinate relabeling. **~80 lines, 0 sorry** modulo Phase B.

**Phase D — `Fintype.card` closure**: Combine Phase A's 20-element enumeration with Phase B/C's concurrence to inhabit `SteinerPoint C hex` 20 times; show this is a bijection with the labeling enumeration via `Fintype.card_of_bijective`. **~40 lines.**

### Sorry budget for OQ-03

| Component | Lines | Sorry delta | Axiom delta |
|---|---|---|---|
| Phase A (Finset of 20 triples) | ~50 | 0 | 0 |
| Phase B (concurrence for $T_0$, B3 route) | ~30 | 0 | **+1** (`steiner_triple_concurrent`) |
| Phase C (propagation) | ~80 | 0 | 0 |
| Phase D (`Fintype.card` = 20) | ~40 | **−1 (closes 442)** | 0 |
| **Total (B3 route)** | **~200** | **−1** | **+1** |
| **Total (B2 route)** | **~350** | **−1** | **0** |

B3 is the "build pending" minimal-effort route; B2 is the axiom-free route requiring substantial computational tactic work and likely 2–3 PRs to land in pieces.

## OQ-03-OQ-04 — `kirkman_count_eq_60`

### Current sorry shape

```lean
theorem kirkman_count_eq_60
    (C : Conic) (hex : InscribedHexagon C)
    [Fintype (KirkmanPoint C hex)] :
    Fintype.card (KirkmanPoint C hex) = 60 := by
  sorry
```

Same shape as OQ-03 but with 60 (instead of 20) concurrent triples, indexed by a different combinatorial pattern.

### Combinatorial structure

A **Kirkman triple** is a 3-element subset of hexagonal labelings whose Pascal lines are concurrent at a Kirkman point. Kirkman triples are distinct from Steiner triples; their count is $60 = 3 \cdot 20$.

Combinatorial characterization (Kirkman 1849, refined Cayley 1849): each Kirkman triple is parametrized by a pair (Steiner triple, choice of one of its 3 elements). More directly: consider the 60 "Pascal-line classes" already enumerated; among the $\binom{60}{3} = 34{,}220$ triples, 20 are Steiner triples and 60 are Kirkman triples (and 15 Plücker quadruples form a fourth concurrence layer that is the OQ-03-OQ-05 deferred sub-OQ). The 60 + 20 + 15 incidence counts add up via the "$60 \cdot 3 = 180 = 20 \cdot 3 + 60 \cdot 2$" identity (each Pascal line passes through exactly 3 Steiner points and 2 Kirkman points... actually each Pascal line passes through 3 Kirkman points and the count 60×3 / 3 = 60 Kirkman points; see Cayley 1849 for the exact incidence pattern).

### Proposed proof strategy

Direct analog of OQ-03 Phases A–D:

**Phase A** — Finset of 60 Kirkman triples, parametrized by ordered pairs (Steiner triple, distinguished element) modulo a 1-element-orbit identification. **~80 lines**, 0 sorry.

**Phase B** — Concurrence for one representative Kirkman triple. **Same routes B1/B2/B3 as OQ-03**, with the same trade-offs. The B3 axiom would be `kirkman_triple_concurrent`. **~30 lines** (B3) or **~200+ lines** (B2 — polynomial identity in 6 vars).

**Phase C** — Propagation by `Sym(6)` action. **~80 lines**, 0 sorry.

**Phase D** — `Fintype.card = 60` closure. **~40 lines**.

### Sorry budget for OQ-04

| Component | Lines | Sorry delta | Axiom delta |
|---|---|---|---|
| Phase A (Finset of 60 triples) | ~80 | 0 | 0 |
| Phase B (concurrence, B3 route) | ~30 | 0 | **+1** (`kirkman_triple_concurrent`) |
| Phase C (propagation) | ~80 | 0 | 0 |
| Phase D (`Fintype.card` = 60) | ~40 | **−1 (closes 467)** | 0 |
| **Total (B3 route)** | **~230** | **−1** | **+1** |
| **Total (B2 route)** | **~400** | **−1** | **0** |

## Overall sorry / axiom delta projection

| Sub-OQ | Sorries closed | Axioms added (B3) | Lines added (B3) | Status after |
|---|---|---|---|---|
| OQ-03-OQ-01 (S3d, PR #18185) | 2 (cards) | 0 | +209 | merged → 3 sorries left |
| OQ-03-OQ-02 (this survey, route Q.liftOn + ProjLineClass) | 1 (`pascalLine` def) | 0 | +185 | 2 sorries left |
| OQ-03-OQ-03 (this survey, B3) | 1 (`steiner_count_eq_20`) | +1 (`steiner_triple_concurrent`) | +200 | 1 sorry left, +1 axiom |
| OQ-03-OQ-04 (this survey, B3) | 1 (`kirkman_count_eq_60`) | +1 (`kirkman_triple_concurrent`) | +230 | 0 sorry left, +2 axioms |
| **Totals (S3d + S4 plan, B3 route)** | **5** | **+2** | **+824** | **complete** |

Substituting B2 for either OQ-03 or OQ-04 trades each axiom for ~150 extra Lean lines of polynomial-identity tactic.

## Anti-targets (do not pick up these in S4)

- **OQ-03-OQ-05 (Cayley-Plücker-Salmon configurations)**: marked "deferred" in the S1 scaffold; out of scope here. The 15 Plücker lines and 15 Salmon points add a third concurrence layer; they require either a dedicated polynomial-identity tactic burst (≥500 lines) or 2 additional axioms.
- **Touching `PascalsHexagonOQ03.lean` while PR #18185 is open**: would create a merge conflict (PR #18185 touches `+209/-53` in the same file).
- **Touching `proofs/Proofs/PascalsHexagon.lean`**: parent file is broken on origin/main (~40 Mathlib drift errors at lines 360–1153, per state.md). Repair is a separate mechanic task; avoid edits that depend on the broken sections.
- **Editing `meta.json` / `state.md` / `pascals-hexagon-oq-03.json`**: PR #18185 touches all three; concurrent edits will conflict.
- **Adding `loom:review-requested` label**: math agents must not (CLAUDE.md axiom integrity policy).

## Honest scope guarantee

This file is a **forward-planning survey**. It does NOT discharge any sorry. It does NOT add any axiom. It does NOT change any Lean theorem statement. It does NOT modify `meta.json`, `state.md`, or any JSON. The only file added by this PR is `research/problems/pascals-hexagon-oq-03/sessions/2026-05-12-s4-prep-survey.md` (this document).

The estimates in this document are **upper bounds based on the current Mathlib pin and the current shape of `Proofs/PascalsHexagon.lean`**. Real implementation may diverge if:
- The parent file is repaired and `Conic.nondegenerate` becomes a precondition for `pascal_hexagon_theorem` (cleaner Pascal-line definition).
- Mathlib introduces a `ProjLineClass`-like quotient (currently absent).
- The Cayley-Bacharach theorem is formalized in Mathlib (would convert B3 axioms to derived theorems).

## Differentiation from PR #18185

PR #18185 (researcher-11, in-flight) closes OQ-03-OQ-01. This survey targets OQ-03-OQ-02, OQ-03-OQ-03, OQ-03-OQ-04 — three sub-OQs that are **independent of the group-theoretic content of S3d** (per PR #18185's own "Next steps" section). Once #18185 merges, the 3 remaining sorries can be picked up in parallel by future S4a/S4b/S4c PRs without re-entering the homomorphism construction.

This survey provides the concrete entry-point lemmas, Mathlib-API references, and sorry/axiom-budget projections so that the next researcher to claim `pascals-hexagon-oq-03` does not duplicate planning work.
