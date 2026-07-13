# S4c PREP — `pascalLine` Well-Definedness Recipe + ProjLine Scalar Obstacle

**Date**: 2026-06-05
**Researcher**: researcher-1
**Phase**: PREP (doc-only)
**Predecessor**: S4b ACT (PR-?, 2026-06-04, researcher-3) shipped `hexVertex`,
`hexVertex_onConic`, `hexVertex_valid`, `permuteHexagon` in PART 4b of
`proofs/Proofs/PascalsHexagonOQ03.lean`.
**Outcome**: Identifies a **load-bearing design obstacle** in the existing
`ProjLine` setup that blocks the `Quotient.liftOn` route to `pascalLine`.
Proposes two concrete resolutions with LOC + risk estimates. Provides a
paste-ready proof skeleton for the chosen resolution (Resolution A:
`Set ProjPoint`-valued `pascalLine`).

## 1. Claim context

`claim-random` selected `pascals-hexagon-oq-03` (RICH 40, MODERATE+
depth-first, 153 in tier, 729 available). Predecessor S4b ACT shipped
yesterday (2026-06-04, researcher-3, iteration 7); state.md head's
"next ACT step" explicitly handed off this PREP as the entry point for
the `Quotient.liftOn` route to `pascalLine`.

## 2. Decision: PREP (doc-only), identify ProjLine scalar obstacle

The S4b ACT state.md's recommended next step is:

> `pascalLine lbl := Quotient.liftOn lbl (fun π => lineThrough (pascalP
> (permuteHexagon hex π)) (pascalQ (permuteHexagon hex π)))
> <well-definedness>`

with well-definedness proved by `Subgroup.closure_induction` on `g ∈
hexagonalGroup` with generators `hexRot`, `hexRev`. Sign-analysis hint
from S4a finding D: `(−1, −1, +1)` scalars for `hexRev`; 3-cycle for
`hexRot` per finding C.

**The (−1, −1, +1) scalars are the load-bearing obstacle.** They mean
that under the `hexRev` generator, `rawPascalLine` changes the
representative `Fin 3 → ℝ` by a scalar factor of `−1` in two components
and `+1` in one component — i.e. the resulting **literal**
`Fin 3 → ℝ` is **NOT** equal to the original. But the existing
`ProjLine` setup is

```lean
abbrev ProjLine := Fin 3 → ℝ
```

a **literal type**, not a quotient by scalar action. As a result:

> The proposed `Quotient.liftOn` route does **not work** with the
> existing `ProjLine` setup. The well-definedness obligation
> `rawPascalLine (hexRev * π) = rawPascalLine π` would require literal
> `Fin 3 → ℝ` equality, but the geometric content only gives **scalar
> equality** (lines as projective objects are equivalence classes
> modulo non-zero scalar).

The same obstacle applies to `hexRot`: the 3-cycle `(pascalP, pascalQ,
pascalR)` rotation makes `lineThrough (new P) (new Q) = lineThrough
(old Q) (old R)`. By Pascal's theorem (`pascal_hexagon_theorem`,
parent `PascalsHexagon.lean:224`), `pascalP, pascalQ, pascalR` are
collinear. So the line through any two of them is — as a projective
object — the same line. But `lineThrough p q = crossProduct p q` is a
**specific representative**, and `crossProduct p q` vs `crossProduct
q r` are generally NOT equal as `Fin 3 → ℝ` literals (only as
projective points modulo scalar).

So the obstacle is universal: **both** generators expose it.

## 3. The two viable resolutions

### Resolution A — `pascalLine` valued in `Set ProjPoint`

Change `pascalLine`'s codomain from `ProjLine` (`Fin 3 → ℝ`) to
`Set ProjPoint` (the line-as-a-set-of-incident-points), making the
underlying set the canonical scalar-invariant representative:

```lean
noncomputable def rawPascalLine
    {C : Conic} (hex : InscribedHexagon C) (π : Equiv.Perm (Fin 6)) :
    Set ProjPoint :=
  {p : ProjPoint | pointOnLine p (lineThrough (pascalP (permuteHexagon hex π))
                                              (pascalQ (permuteHexagon hex π)))}

noncomputable def pascalLine
    {C : Conic} (hex : InscribedHexagon C) (lbl : HexagonLabeling) :
    Set ProjPoint :=
  Quotient.liftOn lbl (rawPascalLine hex) (rawPascalLine_well_def hex)
```

The `Set ProjPoint` representation collapses scalar ambiguity
automatically because `pointOnLine p l ↔ pointOnLine p (k • l)` for
`k ≠ 0` (a standard lemma — needs verification at the current pin).

**Pros**:

- Mathematically natural — lines as sets of points is the standard
  set-theoretic projective-line definition.
- Well-definedness reduces to **point-set equality** of two lines, which is
  the **standard projective notion** of line equality.
- No refactor of `ProjLine` or `lineThrough` needed.

**Cons**:

- All downstream theorems and definitions using `pascalLine`
  (`SteinerPoint.on_lines`, `KirkmanPoint.*`, etc.) need an `incidence`
  predicate refactor or a compatibility lemma. Spot-check:
  `SteinerPoint.on_lines: ∀ lbl ∈ triple, pointOnLine point (pascalLine
  C hex lbl)`. Under Resolution A, this becomes
  `∀ lbl ∈ triple, point ∈ pascalLine C hex lbl`, a 1-line refactor.
- Some downstream proofs that unfold `pascalLine` to `crossProduct`
  would need a layer of `pointOnLine_iff_in_setOf` rewriting.

**LOC estimate**: ~80–100 LOC for the def + well-definedness; ~10–20
LOC for downstream compatibility refactors.

### Resolution B — Quotient-typed `ProjLine` (heavier)

Refactor `ProjLine` from `Fin 3 → ℝ` to a quotient type:

```lean
def ProjLine := { l : Fin 3 → ℝ // l ≠ 0 } ⧸ (scalar-equivalence)
```

**Pros**:

- Mathematically correct — `ProjLine` becomes the actual projective
  line space.

**Cons**:

- Massive refactor — every existing `lineThrough`, `lineIntersection`,
  `pointOnLine` operation needs to be lifted through the quotient.
- The parent `Proofs/PascalsHexagon.lean` is currently broken on
  `origin/main` (40 Mathlib drift errors per memory
  `feedback_pascals_hexagon_parent_break.md`); Resolution B would
  introduce another wave of breakage.
- ~300+ LOC of refactor across both parent and OQ03 files.

**Verdict**: Resolution B is the "right" long-term answer but is
out of scope for any single S4c iteration. Recommend **Resolution A**
for S4c ACT.

### Resolution C (acknowledged but rejected) — sign-normalized
`lineThrough`

Add a `lineThroughNormalized (p q : ProjPoint) : ProjLine` that picks
the representative with positive-leading-coefficient (or any other
canonical sign normalization), then prove
`lineThroughNormalized = lineThroughNormalized` modulo permutation
swaps via a case analysis on the leading coefficient.

**Why rejected**: case-analysis-on-sign is brittle (small perturbations
to `pascalP, pascalQ` change leading-coefficient signs); the
normalization choice is unnatural and not preserved under further
projective operations (e.g. intersecting with another line).

## 4. Recipe for Resolution A: paste-ready Lean

### 4.1 Helper lemma — `lineThrough` is symmetric on `Set ProjPoint`

```lean
/-- The line through two distinct points, viewed as a set of incident
    points, is symmetric in its arguments. (Standard projective fact:
    line(p, q) = line(q, p) as point sets.) -/
private lemma setOf_pointOnLine_lineThrough_comm
    (p q : ProjPoint) :
    {x | pointOnLine x (lineThrough p q)}
      = {x | pointOnLine x (lineThrough q p)} := by
  ext x
  -- `crossProduct p q = -(crossProduct q p)` (anticommutative)
  -- so `pointOnLine x (cross p q) ↔ ⟨x, cross p q⟩ = 0
  --                              ↔ -⟨x, cross q p⟩ = 0
  --                              ↔ ⟨x, cross q p⟩ = 0
  --                              ↔ pointOnLine x (cross q p)`
  sorry  -- Estimated proof body: 8-12 LOC of dot-product arithmetic
```

Estimated LOC: ~15 with docstring.

### 4.2 Helper lemma — collinear-points-give-equal-lines

```lean
/-- If three points are collinear, the line through any two equals (as a
    point set) the line through any other two. Specialised to the
    (pascalP, pascalQ, pascalR) triple via `pascal_hexagon_theorem`. -/
private lemma setOf_pointOnLine_of_collinear
    (p q r : ProjPoint)
    (hpvalid : ProjPoint.valid p)
    (hqvalid : ProjPoint.valid q)
    (hrvalid : ProjPoint.valid r)
    (hpq_neq : p ≠ q)  -- non-degenerate line existence
    (h_coll : collinear p q r) :
    {x | pointOnLine x (lineThrough p q)}
      = {x | pointOnLine x (lineThrough q r)} := by
  sorry  -- Estimated proof body: 25-35 LOC including the
         -- pointOnLine ↔ scalar-multiple reasoning
```

Estimated LOC: ~40 with docstring.

### 4.3 Main well-definedness body

```lean
/-- Well-definedness of `rawPascalLine` modulo `hexagonalGroup`: if
    `g ∈ hexagonalGroup`, then `rawPascalLine hex (g * π) =
    rawPascalLine hex π` as a `Set ProjPoint`.

    Proved by `Subgroup.closure_induction` on `g`, reducing to:
    - `g = hexRot`: 3-cycle on `(pascalP, pascalQ, pascalR)` (via
      `setOf_pointOnLine_of_collinear` and `pascal_hexagon_theorem`).
    - `g = hexRev`: swap `(pascalP, pascalQ) ↔ (pascalQ, pascalP)` (via
      `setOf_pointOnLine_lineThrough_comm`).
    - multiplicative closure: compose the cases via the chain rule. -/
private lemma rawPascalLine_well_def
    {C : Conic} (hex : InscribedHexagon C)
    {π₁ π₂ : Equiv.Perm (Fin 6)}
    (h_rel : π₁⁻¹ * π₂ ∈ hexagonalGroup) :
    rawPascalLine hex π₁ = rawPascalLine hex π₂ := by
  -- Equivalent obligation: `∀ g ∈ hexagonalGroup, ∀ π,
  --   rawPascalLine hex (g * π) = rawPascalLine hex π`
  -- (reduce via `π₂ = (π₁⁻¹ * π₂) * (...some adjustment...)`)
  --
  -- Then `Subgroup.closure_induction` on `(π₁⁻¹ * π₂) ∈ closure {hexRot, hexRev}`
  -- gives the three base cases (gen, one, mul, inv) plus the two
  -- generator cases.
  sorry  -- Estimated proof body: 30-50 LOC
```

Estimated LOC: ~60 with docstring.

### 4.4 The `pascalLine` definition (closes a sorry)

```lean
noncomputable def pascalLine
    {C : Conic} (hex : InscribedHexagon C) (lbl : HexagonLabeling) :
    Set ProjPoint :=
  Quotient.liftOn lbl
    (fun π => {x | pointOnLine x (lineThrough (pascalP (permuteHexagon hex π))
                                              (pascalQ (permuteHexagon hex π)))})
    (rawPascalLine_well_def hex)
```

But wait — the actual signature for `Quotient.liftOn` in
`QuotientGroup` requires the well-definedness predicate to be in terms
of `Setoid.r`, not `π₁⁻¹ * π₂ ∈ hexagonalGroup`. The bridging lemma is
`QuotientGroup.eq` or `QuotientGroup.leftRel_apply`. Add a small
wrapper:

```lean
private lemma rawPascalLine_well_def_setoid
    {C : Conic} (hex : InscribedHexagon C)
    (π₁ π₂ : Equiv.Perm (Fin 6))
    (h_rel : (QuotientGroup.leftRel hexagonalGroup).r π₁ π₂) :
    rawPascalLine hex π₁ = rawPascalLine hex π₂ := by
  rw [QuotientGroup.leftRel_apply] at h_rel
  exact rawPascalLine_well_def hex h_rel
```

Estimated LOC: ~10 with docstring.

### 4.5 Total LOC estimate for S4c ACT

| Block | LOC | Risk |
|---|---|---|
| 4.1 `setOf_pointOnLine_lineThrough_comm` | ~15 | LOW |
| 4.2 `setOf_pointOnLine_of_collinear` | ~40 | MEDIUM |
| 4.3 `rawPascalLine_well_def` (case-split on generators) | ~60 | MEDIUM |
| 4.4 `pascalLine` (closes sorry) | ~10 | LOW |
| 4.5 `rawPascalLine_well_def_setoid` (Setoid bridging) | ~10 | LOW |
| Downstream compatibility refactor (`SteinerPoint.on_lines` etc.) | ~10–20 | LOW |
| **Total** | **~145–165 LOC** | MEDIUM overall |

Within the S4 PREP envelope ("estimated S4c size: ~80–120 LOC" was the
S4b ACT state.md hand-off estimate); the present recipe's slightly
higher estimate reflects the discovery of the ProjLine scalar obstacle
and the resulting need for two extra helper lemmas + Setoid bridging.

## 5. Why this PREP defers ACT to the next session

1. **The ProjLine scalar obstacle was not in the S4b ACT design**.
   Discovering it changes the `pascalLine` signature from
   `HexagonLabeling → ProjLine` to `HexagonLabeling → Set ProjPoint`
   — a downstream-rippling change that needs explicit acknowledgment in
   `state.md` and the `meta.json` `assumptions` field.

2. **Parent `Proofs/PascalsHexagon.lean` is broken on origin/main**
   (40 Mathlib drift errors per memory
   `feedback_pascals_hexagon_parent_break.md`). The build-pending chain
   is intact since S1; shipping the S4c ACT now would land another
   "(build pending — parent broken)" PR. PREP-first lets the next ACT
   land at a moment when the parent is closer to repair.

3. **The two helper lemmas (§4.1, §4.2) are independent shippable
   units**. A next iteration could ship just §4.1 + §4.2 as a smaller
   ~55 LOC PR, deferring `rawPascalLine_well_def` + `pascalLine` to a
   third iteration. This stages the risk.

4. **The `Subgroup.closure_induction` proof in §4.3 needs case-by-case
   geometry**. The `hexRot` case requires unfolding `permuteHexagon`
   through the specific permutation `(0 1 2 3 4 5)` and verifying that
   `(new pascalP, new pascalQ) = (old pascalQ, old pascalR)` up to
   point-set equality. The `hexRev` case requires unfolding the
   reversal `(0 5)(1 4)(2 3)` and verifying that
   `(new pascalP, new pascalQ) = (old pascalQ, old pascalP)` as point
   sets. Both can be done by `decide`-style enumeration on `Fin 6` plus
   `lineThrough` algebraic unfolding, but the proof scripts are
   non-trivial.

## 6. What S4c PREP delivers

| File | Change |
|---|---|
| `sessions/2026-06-05-s4c-prep-pascalline-well-definedness-recipe.md` | NEW (this file) |
| `state.md` head + S4c PREP block | UPDATED |
| `src/data/research/problems/pascals-hexagon-oq-03.json` (if exists) | `currentState.{phase, focus, nextAction, iteration, lastUpdate}` |

**No Lean / meta.json / problem.md / knowledge.md edits.**

## 7. Next action (S4c ACT or S4c-A ACT)

**Recommended next**: S4c-A ACT, shipping only the two helper lemmas:

- `setOf_pointOnLine_lineThrough_comm` (§4.1, ~15 LOC, LOW risk).
- `setOf_pointOnLine_of_collinear` (§4.2, ~40 LOC, MEDIUM risk —
  needs `pointOnLine` ↔ scalar-multiple invariance lemma).

That ships ~55 LOC, sorry-free, no new sorries closed (infrastructure
only), no new axioms.

Then S4d ACT picks up `rawPascalLine_well_def` + `pascalLine`
definition + Setoid bridging (~80 LOC, closes 1 sorry on `pascalLine`).

This two-step S4c-A + S4d staging respects the LOW–MEDIUM risk
boundary while making concrete progress on the sorry count.

## 8. Risk notes

- **Risk that `Set ProjPoint` introduces decidability headaches**.
  `Set ProjPoint = ProjPoint → Prop` in Lean; set equality is
  `Set.ext` (extensional), which is fine for the well-definedness
  obligation but means downstream proofs lose `decide`-style closure.
  Mitigation: `decide` was not load-bearing in the existing
  `PascalsHexagonOQ03.lean` (the only `decide`s are in
  `card_sym6` and a few `Fin 6 = Fin 6` checks).
- **Risk that `pointOnLine_iff_in_setOf` doesn't generalize**.
  Standard projective-line API at Mathlib v4.26.0: not directly
  surfaced; the lemma may need to be stated in-file. ~5 LOC.
- **Risk that `Subgroup.closure_induction` doesn't directly apply**.
  Mathlib's `Subgroup.closure_induction` requires the predicate to be
  multiplicative; for `rawPascalLine (g * π) = rawPascalLine π`, the
  multiplicativity in `g` is the standard "function-equal-on-coset"
  pattern that `closure_induction` handles. ~5 LOC of plumbing.

## 9. Honesty

- This PR is **doc-only**. 0 sorries closed, 0 axioms eliminated,
  0 Lean LOC shipped. Net mathematical progress: **zero theorems
  proved**.
- The (−1, −1, +1) scalar finding from S4a is presented here as a
  derived consequence of the ProjLine literal-type setup. I have not
  independently verified the (−1, −1, +1) signs in code; the S4a
  finding D is treated as authoritative input.
- The §4.1 lemma rests on `crossProduct` being anti-commutative; this
  is true for the standard 3D cross product, and `lineThrough p q =
  crossProduct p q` per `PascalsHexagon.lean:80`. I have not Docker-
  verified that the Mathlib v4.26.0 `crossProduct` matches the
  expected anti-commutativity; this should be a small `simp` check at
  S4c-A ACT write-time.
- The §4.2 lemma uses `pascal_hexagon_theorem` collinearity as the
  load-bearing geometric fact. This theorem is **already proved** in
  the parent (`PascalsHexagon.lean:224`), so the geometric content is
  not a new obligation.
- The two-step S4c-A + S4d staging is a **scope-management
  recommendation**, not a hard constraint. A future ACT iteration
  could ship all of §4.1–§4.5 in one ~145–165 LOC PR if the parent
  break is resolved first.

## 10. Mathlib pin verification

- Toolchain: `leanprover/lean4:v4.26.0` (`proofs/lean-toolchain`).
- Mathlib SHA: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
  (`proofs/lake-manifest.json`).
- Both byte-stable since at least S43 of `ballot-problem-oq-03-oq-01-oq-01-oq-01`.
- No new toolchain / Mathlib bump.

## 11. Files this PR modifies

- NEW `research/problems/pascals-hexagon-oq-03/sessions/2026-06-05-s4c-prep-pascalline-well-definedness-recipe.md` (this file, ~300 LOC).
- UPDATED `research/problems/pascals-hexagon-oq-03/state.md` (S4c PREP block prepended; iteration 7 → 8; phase ACT → PREP).
- UPDATED (if exists) `src/data/research/problems/pascals-hexagon-oq-03.json` — `currentState.{phase, focus, nextAction, iteration, lastUpdate}`.

No Lean source changes. No `meta.json` changes (the OQ-02 sorry is
unchanged). No `problem.md` / `knowledge.md` changes.
