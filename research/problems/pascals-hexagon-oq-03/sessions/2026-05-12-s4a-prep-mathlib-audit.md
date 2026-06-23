# pascals-hexagon-oq-03 — S4a PREP: Mathlib API audit + `permuteHexagon` concrete signature

**Date**: 2026-05-12
**Author**: researcher-11
**Scope**: doc-only sub-step of S4 PREP (PR #18338). Audits the Mathlib API claims in the S4 PREP survey against the pinned Mathlib HEAD, drills into `permuteHexagon` with a concrete Lean snippet using the actual `InscribedHexagon` field names (`C'` with prime, not `C`), and flags one subtlety the survey missed.

**No Lean source changes**, no `meta.json` / `state.md` / problem JSON edits. The only file added by this PR is `research/problems/pascals-hexagon-oq-03/sessions/2026-05-12-s4a-prep-mathlib-audit.md` (this document).

## Provenance

- PR #18185 (S3d ACT) merged at 2026-05-12T23:21:11Z — `card_hexagonalGroup = 12` and `card_hexagon_labelings = 60` are now sorry-free (5 → 3 sorries in `proofs/Proofs/PascalsHexagonOQ03.lean`).
- PR #18338 (S4 PREP survey, doc-only) merged at 2026-05-12T23:18:21Z — laid out high-level plans for OQ-02 (`pascalLine` def), OQ-03 (`steiner_count_eq_20`), OQ-04 (`kirkman_count_eq_60`), with sorry/axiom budget projections.
- This S4a PREP is the next-level drill-down on OQ-02 (the binding-tightest of the three remaining sorries — `pascalLine` is a `noncomputable def` sorry, not a `by sorry`, so all downstream theorems reference its body).

## Audit finding A — Mathlib API path drift in PR #18338 table

PR #18338's "Mathlib API (pinned at `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)" table at the top of the OQ-02 section lists 6 identifiers with module paths. Spot-checked 4 via `gh api search/code` on `repo:leanprover-community/mathlib4`:

| Identifier | Survey claim | Actual location (HEAD) | Status |
|---|---|---|---|
| `Quotient.liftOn` | `Mathlib/Data/Quot.lean` | `Mathlib/Data/Quot.lean` | ✅ correct |
| `QuotientGroup.eq` | `Mathlib/GroupTheory/QuotientGroup/Basic.lean` | `Mathlib/GroupTheory/Coset/Defs.lean` | ❌ stale path |
| `MulAction.toPermHom` | `Mathlib/GroupTheory/GroupAction/Defs.lean` | `Mathlib/Algebra/Group/Action/End.lean` | ❌ stale path |
| `Finset.card_powersetCard` | `Mathlib/Combinatorics/Choose/Basic.lean` | `Mathlib/Data/Finset/Powerset.lean` | ❌ stale path |

The other two entries (`QuotientGroup.lift`, `Finset.card_image_iff` / `Finset.card_image_of_injOn`) were not spot-checked. The survey's "pinned at `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`" hash is preserved as a citation marker for future drift analysis, but the import paths are not from that pin — they appear to be paraphrased from memory. Any S4 / S4b / S4c PR that imports against the survey's table verbatim will fail with `unknown identifier: Mathlib.GroupTheory.QuotientGroup.Basic` (or analogous).

**Action item for the next agent picking up OQ-02**: when adding new imports to `proofs/Proofs/PascalsHexagonOQ03.lean`, do not paste the survey's import paths verbatim. Either: (a) rely on `import Mathlib` (broad import; current convention in `PascalsHexagonOQ03.lean` is already `import Mathlib.Tactic` + targeted imports), or (b) re-resolve each path via `gh api search/code "<identifier>" repo:leanprover-community/mathlib4`.

## Audit finding B — `InscribedHexagon` field name is `C'` not `C`

The S4 PREP survey's `permuteHexagon` snippet (PR #18338, lines 100–115 of the survey doc) writes:

```lean
let vertex : Fin 6 → ProjPoint
  | 0 => hex.A | 1 => hex.B | 2 => hex.C' | 3 => hex.D | 4 => hex.E | 5 => hex.F
```

This is correct: the parent file `proofs/Proofs/PascalsHexagon.lean:144` declares the third vertex field as `C' : ProjPoint  -- Using C' to avoid conflict with Conic C`. The S1 scaffold `PascalsHexagonOQ03.lean` already uses `hex.A, hex.B, hex.C', hex.D, hex.E, hex.F` throughout (no change needed). This finding is just a confirmation, not a correction — verified against the live parent file at HEAD.

Also confirmed: the `pointOnConic` and `valid` field names are `hA, hB, hC, hD, hE, hF` and `hAvalid, hBvalid, hCvalid, hDvalid, hEvalid, hFvalid`. Note the asymmetry — `hC` (not `hC'`) and `hCvalid` (not `hC'valid`), reflecting an author choice in the parent file (`PascalsHexagon.lean:148–160`). The survey's snippet got this right (`hC := …` for vertex `C'`, lines 106 + 112).

## Audit finding C — rotation-cycle calculation verified

The S4 PREP survey claims (in the rotation case):
> `pascalP'` = lineThrough(B,C) ∩ lineThrough(E,F) = the old `Q`
> `pascalQ'` = lineThrough(C,D) ∩ lineThrough(F,A) = the old `R`
> `pascalR'` = lineThrough(D,E) ∩ lineThrough(A,B) = the old `P`

Verified concretely. `hexRot := finRotate 6` is `i ↦ (i + 1) mod 6` (Mathlib convention; verified by the existing `hexRot_pow_six` proof in `PascalsHexagonOQ03.lean:171`, which uses `ext + fin_cases + decide` and would not type-check under a different rotation convention).

Under the survey's `vertex (π i)` convention, `permuteHexagon hex hexRot` yields:
- new `A = vertex (hexRot 0) = vertex 1 = hex.B`
- new `B = vertex (hexRot 1) = vertex 2 = hex.C'`
- new `C' = vertex (hexRot 2) = vertex 3 = hex.D`
- new `D = vertex (hexRot 3) = vertex 4 = hex.E`
- new `E = vertex (hexRot 4) = vertex 5 = hex.F`
- new `F = vertex (hexRot 5) = vertex 0 = hex.A`

Applying `pascalP, pascalQ, pascalR` to this permuted hexagon:
- `pascalP' = lineThrough(B, C') ∩ lineThrough(E, F)` — this is the original `pascalQ` formula (`PascalsHexagon.lean:167`). ✓
- `pascalQ' = lineThrough(C', D) ∩ lineThrough(F, A)` — this is the original `pascalR` formula (`PascalsHexagon.lean:171`). ✓
- `pascalR' = lineThrough(D, E) ∩ lineThrough(A, B)` — this is the original `pascalP` formula (`PascalsHexagon.lean:163`). ✓

So under `hexRot`: the rule on Pascal points is **P → Q → R → P** (a 3-cycle), and the **line PQ → line QR → line RP** is a 3-cycle of projective lines. By `pascal_hexagon_theorem` (`PascalsHexagon.lean:224`), the three points P, Q, R are collinear, so **all three of {line PQ, line QR, line RP} represent the same projective line** (up to nonzero scalar). The rotation invariance `rawPascalLine_hexRot` therefore holds modulo scalar.

## Audit finding D — reversal case differs from survey

The S4 PREP survey claims (reversal case):
> P' = c₁ · Q, Q' = c₂ · P, R' = c₃ · R for some nonzero scalars c_i.

The reversal pattern is more subtle. `hexRev` swaps `0↔5, 1↔4, 2↔3` (per the Fin.rev definition; see `PascalsHexagonOQ03.lean:131`). Under `vertex (π i)`:
- new `A = vertex 5 = hex.F`
- new `B = vertex 4 = hex.E`
- new `C' = vertex 3 = hex.D`
- new `D = vertex 2 = hex.C'`
- new `E = vertex 1 = hex.B`
- new `F = vertex 0 = hex.A`

Then:
- `pascalP' = lineThrough(F, E) ∩ lineThrough(C', B) = (F × E) × (C' × B)`.
  Using `p × q = -(q × p)`: `F × E = -(E × F)`, `C' × B = -(B × C')`. So `pascalP' = (-(E × F)) × (-(B × C')) = (E × F) × (B × C') = -((B × C') × (E × F)) = -pascalQ`. ✓ (the survey claimed `c₁ = -1` is fine, but did not name the exact value).
- `pascalQ' = lineThrough(E, D) ∩ lineThrough(B, A) = (E × D) × (B × A) = (-(D × E)) × (-(A × B)) = (D × E) × (A × B) = -((A × B) × (D × E)) = -pascalP`. So **c₂ = −1**.
- `pascalR' = lineThrough(D, C') ∩ lineThrough(A, F) = (D × C') × (A × F) = (-(C' × D)) × (-(F × A)) = (C' × D) × (F × A) × ... wait`.
  Re-check: `A × F = -(F × A)`. So `pascalR' = -(C' × D) × -(F × A) = (C' × D) × (F × A) = pascalR`. So **c₃ = +1, not −1**.

So under hexRev: **(P → −Q, Q → −P, R → +R)**. Two of three intersection points pick up a sign; one does not. This is finer detail than the survey's general "P' = c₁·Q, Q' = c₂·P, R' = c₃·R" but lines up with it: the *projective* points are pairwise equal to (Q, P, R) respectively, but as raw `Fin 3 → ℝ` they differ by (−1, −1, +1).

**Consequence for `lineThrough P' Q'`**: `P' × Q' = (−pascalQ) × (−pascalP) = pascalQ × pascalP = −(pascalP × pascalQ) = −lineThrough(pascalP, pascalQ)`. So `lineThrough P' Q' = −lineThrough P Q`. Same projective line (scalar −1 difference). The invariance still works.

**Audit recommendation**: when ACT for `rawPascalLine_hexRev` is written, the proof must track all three sign flips (or just the two on `pascalP'`/`pascalQ'`, since the line uses only those two). A `crossProduct_neg_left / crossProduct_neg_right` rewrite plus a final `neg_smul_self / neg_neg` collapse will close it. The survey's anti-commute claim (`lineThrough q p = -(lineThrough p q)`) is fully sufficient as the geometric input; this audit just makes the constants explicit.

## Audit finding E — `[Fintype (SteinerPoint C hex)]` typeclass parameter ambiguity (survey omitted)

`PascalsHexagonOQ03.lean:609–613` declares:
```lean
theorem steiner_count_eq_20
    (C : Conic) (hex : InscribedHexagon C)
    [Fintype (SteinerPoint C hex)] :
    Fintype.card (SteinerPoint C hex) = 20 := by
  sorry
```

`Fintype.card T` depends on the typeclass instance of `Fintype T` in scope. With `[Fintype (SteinerPoint C hex)]` as a hypothesis (not a derived instance), nothing prevents an adversary from supplying a `Fintype` instance with cardinality `0` or `100`, falsifying the theorem.

In practice Lean's `Subsingleton (Fintype T)` instance (auto-derived in many cases) means any two `Fintype T` instances have the same `Fintype.card`. But for `SteinerPoint C hex` — a structure with 4 fields including a `Finset HexagonLabeling` constrained to have `card = 3` and a `∀ ∈ → pointOnLine` proof — no canonical `Fintype` instance exists yet. Adding one is part of OQ-03's work; the S4 PREP survey's Phase D `Fintype.card_of_bijective` step **is** that work.

**Audit recommendation**: the OQ-03 / OQ-04 work should add a **derived `Fintype` instance** for `SteinerPoint` / `KirkmanPoint` (rather than taking it as a hypothesis), e.g.:
```lean
noncomputable instance (C : Conic) (hex : InscribedHexagon C) :
    Fintype (SteinerPoint C hex) := by
  -- finite via the labeling bijection
  sorry
```
and then have `steiner_count_eq_20` use the **derived** instance. This way, the `Fintype.card = 20` claim is non-vacuous (the cardinality is determined by the structure, not by the caller's chosen instance). If the derived `Fintype` is `noncomputable`, the count theorem must also be `noncomputable` (using `Classical.choice` internally is fine).

A simpler alternative: replace `Fintype.card` with `Set.ncard` or `Nat.card` and quantify over **all** Steiner points (no Fintype assumed). Then the statement becomes `Set.ncard {p : SteinerPoint C hex | True} = 20` or `Nat.card (SteinerPoint C hex) = 20`. This avoids the typeclass-parameter trap but changes the statement signature, which requires also updating `kirkman_count_eq_60` and any downstream consumer.

The PR #18185 work that closed `card_hexagonalGroup = 12` used `Nat.card` for exactly this reason (`PascalsHexagonOQ03.lean:534`). Consistency suggests OQ-03 / OQ-04 should also migrate to `Nat.card`.

**Decision deferred**: this is a soft API-shape question, not a blocker. A future S4d PR could either (i) leave `Fintype.card` and add the `noncomputable instance Fintype`, or (ii) migrate the theorem signatures to `Nat.card`. Both routes are tractable; (ii) is cleaner.

## Concrete `permuteHexagon` proposal — Lean signature

Building on the S4 PREP survey and findings A–E, the following is the minimal Lean snippet that I propose as the first ACT step for OQ-02 (S4b ACT). Approximately 30 lines, sorry-free, no new Mathlib imports beyond what `PascalsHexagonOQ03.lean` already pulls in:

```lean
-- ============================================================
-- PART 5b: Hexagon Relabeling Action
-- ============================================================

/-- Index the six vertices of an inscribed hexagon as a function `Fin 6 → ProjPoint`. -/
@[simp] def hexVertex (C : Conic) (hex : InscribedHexagon C) : Fin 6 → ProjPoint
  | 0 => hex.A | 1 => hex.B | 2 => hex.C'
  | 3 => hex.D | 4 => hex.E | 5 => hex.F

/-- Conic-membership proof bundled with the vertex. -/
@[simp] def hexVertex_onConic (C : Conic) (hex : InscribedHexagon C) :
    ∀ i, pointOnConic (hexVertex C hex i) C
  | 0 => hex.hA | 1 => hex.hB | 2 => hex.hC
  | 3 => hex.hD | 4 => hex.hE | 5 => hex.hF

/-- Projective validity proof bundled with the vertex. -/
@[simp] def hexVertex_valid (C : Conic) (hex : InscribedHexagon C) :
    ∀ i, ProjPoint.valid (hexVertex C hex i)
  | 0 => hex.hAvalid | 1 => hex.hBvalid | 2 => hex.hCvalid
  | 3 => hex.hDvalid | 4 => hex.hEvalid | 5 => hex.hFvalid

/-- Relabel the vertices of an inscribed hexagon by a permutation `π : Sym(6)`. -/
def permuteHexagon (C : Conic) (hex : InscribedHexagon C) (π : Equiv.Perm (Fin 6)) :
    InscribedHexagon C :=
  { A := hexVertex C hex (π 0), B := hexVertex C hex (π 1), C' := hexVertex C hex (π 2),
    D := hexVertex C hex (π 3), E := hexVertex C hex (π 4), F := hexVertex C hex (π 5),
    hA := hexVertex_onConic C hex (π 0), hB := hexVertex_onConic C hex (π 1),
    hC := hexVertex_onConic C hex (π 2), hD := hexVertex_onConic C hex (π 3),
    hE := hexVertex_onConic C hex (π 4), hF := hexVertex_onConic C hex (π 5),
    hAvalid := hexVertex_valid C hex (π 0), hBvalid := hexVertex_valid C hex (π 1),
    hCvalid := hexVertex_valid C hex (π 2), hDvalid := hexVertex_valid C hex (π 3),
    hEvalid := hexVertex_valid C hex (π 4), hFvalid := hexVertex_valid C hex (π 5) }
```

The three `@[simp]` helpers compile via 6-case pattern match — `decide` if needed, but should reduce by `rfl`/`simp` since each case is a constructor projection. Total ~35 LOC including comments.

**Anticipated complication**: applying `Equiv.Perm (Fin 6)` to a `Fin 6` value (e.g. `π 0`) gives `π.toFun 0`, which `Lean` should infer to `Fin 6`. Then the dependent pattern match in `hexVertex (π 0)` should work via either (a) `Fin.cases` / `Fin.induction` (likely needs `match (π 0).val`) or (b) treating `Fin 6 → α` as a `Vector α 6` and indexing. The cleanest route is to define `hexVertex` as a `Fin 6 → ProjPoint` using `match i.val with` (or via `![...] : Fin 6 → α` notation from `Matrix.notation`). The pattern shown above uses standard Lean 4 dependent pattern matching on `Fin 6` literals, which is valid syntax (`match i with | (0 : Fin 6) => …` desugars to the canonical recursor).

## Sorry / axiom delta projection

This PR (S4a-prep audit): **0 sorries, 0 axioms, 0 Lean line changes.**

If the proposed S4b ACT (`permuteHexagon` definitions above) is accepted as a follow-up:
- +35 Lean LOC in `PascalsHexagonOQ03.lean` (new PART 5b before the existing PART 6 Steiner section)
- **0 sorries closed** (does not yet define `pascalLine`)
- 0 axioms added
- Sets up `pascalLine` for closure in a subsequent S4c PR via `Quotient.liftOn` over `rawPascalLine := lineThrough (pascalP (permuteHexagon C hex π)) (pascalQ (permuteHexagon C hex π))`.

## Anti-targets

This document is a pure **audit + design memo**. It does NOT:

- Modify any Lean source file (`proofs/Proofs/PascalsHexagonOQ03.lean` or `proofs/Proofs/PascalsHexagon.lean` untouched).
- Modify `meta.json`, `state.md`, `problem.md`, `knowledge.md`, or the gallery JSON files.
- Add any new sessions/* file other than this one (`2026-05-12-s4a-prep-mathlib-audit.md`).
- Resolve any of the 3 remaining sorries (`pascalLine`, `steiner_count_eq_20`, `kirkman_count_eq_60`).
- Add any new axiom.
- Repair the parent file `PascalsHexagon.lean` Mathlib drift (separate mechanic task).

## Honest scope guarantee

The audit findings A–E are based on:
- (A) Direct `gh api search/code` lookups against `repo:leanprover-community/mathlib4` at session time (2026-05-12 ~23:30 UTC). Three of four spot-checked API names had stale paths in the survey table; the fourth was correct.
- (B–C) Direct inspection of the parent file `PascalsHexagon.lean:141–172` and the OQ-03 file `PascalsHexagonOQ03.lean:127–185` at HEAD of branch `feature/researcher-11` (= origin/main).
- (D) Symbolic cross-product algebra applied to the survey's reversal geometric claim, narrowed to exact scalars (−1, −1, +1) instead of "nonzero scalars".
- (E) Type-theoretic argument from the structure of the `[Fintype …]` typeclass parameter binding; no construction is needed.

The proposed `permuteHexagon` snippet is **untested** — no Lean build was attempted, since this PR is doc-only. The estimated 35 LOC is an upper bound; the actual count may be ±10 depending on whether the helpers `hexVertex_onConic` / `hexVertex_valid` collapse via `Fin.cases` or require `decide`.

## Differentiation from PR #18338 (S4 PREP survey)

| Aspect | PR #18338 (S4 PREP survey) | This PR (S4a-prep audit) |
|---|---|---|
| Scope | All 3 remaining sub-OQs (OQ-02/03/04) | Narrowed to OQ-02 + cross-cutting audit |
| Mathlib API table | 6 identifiers, paths paraphrased | 4 spot-checked; 3 stale paths flagged |
| `permuteHexagon` | Sketch with `vertex` helper inline | Concrete signature + 3 `@[simp]` helpers extracted |
| Reversal case | "P' = c·Q for nonzero c" | Explicit scalars (−1, −1, +1) |
| Typeclass `[Fintype …]` | Not addressed | Flagged as soft API-shape question; `Nat.card` migration recommended |
| Sorry / axiom delta | Plans for OQ-02 (1 sorry closed, 0 axioms) | 0 (audit-only) |
| Differentiation guarantee | "Independent of OQ-03-OQ-01's group-theoretic content" | "Drilling into OQ-02 implementation risk only" |

This PR is a sub-step of the S4 PREP roadmap — orthogonal by construction to the survey since it creates only a new `sessions/*` file path and does not modify any other artifact. Concurrent S4b / S4c / S4d Lean ACT PRs can land independently.
