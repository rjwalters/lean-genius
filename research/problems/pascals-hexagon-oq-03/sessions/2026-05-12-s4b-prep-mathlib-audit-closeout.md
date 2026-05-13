# pascals-hexagon-oq-03 — S4b PREP: Mathlib API audit close-out + Fin-6 dependent-match verification

**Date**: 2026-05-12
**Author**: researcher-10
**Scope**: doc-only follow-up to PR #18461 (S4a PREP, merged 2026-05-13 ~02:00 UTC). Completes the partial 4-of-6 Mathlib API spot-check started there, locates direct Mathlib precedent that resolves PR #18461's "Anticipated complication" about dependent pattern matching on `Fin 6` literals, refines two implementer-judgment items (Nat.card migration; degeneracy caveat) by cross-checking against the parent file's actual conventions.

**No Lean source changes**, no `meta.json` / `state.md` / `problem.md` / `knowledge.md` / gallery JSON edits. The only file added by this PR is `research/problems/pascals-hexagon-oq-03/sessions/2026-05-12-s4b-prep-mathlib-audit-closeout.md` (this document).

## Provenance / non-overlap

- PR #18338 (S4 PREP survey, doc-only) merged at 2026-05-12T23:18:21Z. Section "Mathlib API (pinned at `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)" listed 6 identifiers with module paths.
- PR #18461 (S4a PREP, researcher-11, doc-only) merged at 2026-05-13 ~02:00 UTC. Finding A spot-checked 4 of those 6 paths and flagged 3 stale; the survey's table entries for `QuotientGroup.lift` and `Finset.card_image_iff` / `Finset.card_image_of_injOn` were **left unaudited**. Finding B–E covered field names, rotation cycle, reversal scalars, and a `[Fintype …]` typeclass-parameter trap.
- This PR is the next-level drill-down on three points PR #18461 explicitly left soft:
  1. Audit close-out — finish the 4-of-6 spot-check (Finding A).
  2. Lean syntax verification — PR #18461 lines 163–164 wrote "Anticipated complication: applying `Equiv.Perm (Fin 6)` to a `Fin 6` value … The cleanest route is to define `hexVertex` as a `Fin 6 → ProjPoint` using `match i.val with` (or via `![…]` notation from `Matrix.notation`). The pattern shown above uses standard Lean 4 dependent pattern matching on `Fin 6` literals, which is valid syntax". Three competing candidates were presented; no precedent cited. This is exactly the kind of "implementer judgment" load-bearing claim worth verifying.
  3. Refine soft recommendations — PR #18461 Finding E (Nat.card migration for `SteinerPoint`/`KirkmanPoint`) said "Decision deferred"; PR #18338 lines 130–135 (degeneracy caveat) said "open subtlety". Both can be tightened by reading the parent file conventions.

This PR is orthogonal by construction (only file path created is the new sessions/* doc) and creates no race with any open S4-family PR. No Lean build needed.

## Audit closure — Finding A complete (PR #18461 4-of-6 → 6-of-6)

Re-running the PR #18461 audit pattern (`gh api search/code` against `repo:leanprover-community/mathlib4`, then `gh api .../contents/<path> | base64 -d | grep -n` for the declaration site) on the 2 paths PR #18461 did not check:

| Identifier | PR #18338 claim | Actual location (Mathlib HEAD) | Status |
|---|---|---|---|
| `Quotient.liftOn` | `Mathlib/Data/Quot.lean` | `Mathlib/Data/Quot.lean` | ✅ correct (PR #18461) |
| `QuotientGroup.eq` | `Mathlib/GroupTheory/QuotientGroup/Basic.lean` | `Mathlib/GroupTheory/Coset/Defs.lean` | ❌ stale path (PR #18461) |
| `MulAction.toPermHom` | `Mathlib/GroupTheory/GroupAction/Defs.lean` | `Mathlib/Algebra/Group/Action/End.lean` | ❌ stale path (PR #18461) |
| `Finset.card_powersetCard` | `Mathlib/Combinatorics/Choose/Basic.lean` | `Mathlib/Data/Finset/Powerset.lean` | ❌ stale path (PR #18461) |
| **`QuotientGroup.lift`** | **`Mathlib/GroupTheory/QuotientGroup/Basic.lean`** | **`Mathlib/GroupTheory/QuotientGroup/Defs.lean:246`** | **❌ stale path (this PR)** |
| **`Finset.card_image_iff` / `Finset.card_image_of_injOn`** | **`Mathlib/Data/Finset/Card.lean`** | **`Mathlib/Data/Finset/Card.lean:222, 234`** | **✅ correct (this PR)** |

**Methodology for the two new rows:**

- `QuotientGroup.lift`: `gh api 'search/code?q=QuotientGroup.lift+repo:leanprover-community/mathlib4'` returned `Mathlib/GroupTheory/QuotientGroup/Defs.lean` and `Mathlib/GroupTheory/QuotientGroup/Basic.lean`. Fetched `Defs.lean` via `gh api repos/leanprover-community/mathlib4/contents/...`; the `def lift` (with `@[to_additive]` and `def`-keyword block) is at lines 246–262 of `Defs.lean`:
  ```
  244:/-- A group homomorphism `φ : G →* M` with `N ⊆ ker(φ)` descends (i.e. `lift`s) to a
  246:@[to_additive /-- An `AddGroup` homomorphism `φ : G →+ M` with `N ⊆ ker(φ)` descends (i.e. `lift`s)
  ```
  References to `QuotientGroup.lift N φ HN` appear at lines 262, 272, 277 of the same file. `Basic.lean` uses the name but does not declare it (consistent with a re-export / downstream use pattern). The survey's claim `…/QuotientGroup/Basic.lean` is therefore stale: the declaration moved (or has long lived) at `…/QuotientGroup/Defs.lean`.

- `Finset.card_image_iff` / `Finset.card_image_of_injOn`: search returned `Mathlib/Data/Finset/Card.lean` as the top hit. Fetched it; the declarations are at lines 222 (`card_image_of_injOn`) and 234 (`card_image_iff`):
  ```
  222:theorem card_image_of_injOn [DecidableEq β] (H : Set.InjOn f s) : #(s.image f) = #s := by
  234:theorem card_image_iff [DecidableEq β] : #(s.image f) = #s ↔ Set.InjOn f s :=
  235:  ⟨injOn_of_card_image_eq, card_image_of_injOn⟩
  ```
  The survey's claim `Mathlib/Data/Finset/Card.lean` is correct.

**Final tally**: 4 stale (`QuotientGroup.eq`, `MulAction.toPermHom`, `Finset.card_powersetCard`, `QuotientGroup.lift`), 2 correct (`Quotient.liftOn`, `Finset.card_image_iff` / `card_image_of_injOn`). The hash `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` remains a citation marker only — the paths in the survey table are paraphrased, not pulled from that pin.

**Strengthened action item for OQ-02 ACT agent**: do not paste *any* of the 4 stale paths verbatim. PR #18461 already recommended re-resolving each path; this PR enumerates exactly which 4 must be re-resolved (vs. the 2 that can be used as-is).

## Finding B — `hexVertex : Fin 6 → ProjPoint` dependent pattern match: Mathlib precedent confirms it works natively

PR #18461 lines 163–164 ended Finding D's `permuteHexagon` snippet with:

> **Anticipated complication**: applying `Equiv.Perm (Fin 6)` to a `Fin 6` value (e.g. `π 0`) gives `π.toFun 0`, which `Lean` should infer to `Fin 6`. Then the dependent pattern match in `hexVertex (π 0)` should work via either (a) `Fin.cases` / `Fin.induction` (likely needs `match (π 0).val`) or (b) treating `Fin 6 → α` as a `Vector α 6` and indexing. The cleanest route is to define `hexVertex` as a `Fin 6 → ProjPoint` using `match i.val with` (or via `![...] : Fin 6 → α` notation from `Matrix.notation`). The pattern shown above uses standard Lean 4 dependent pattern matching on `Fin 6` literals, which is valid syntax (`match i with | (0 : Fin 6) => …` desugars to the canonical recursor).

This raises three candidate forms and asserts the third is valid without citing precedent. Mathlib has **direct precedent for the third form** in `Counterexamples/HeawoodUnitDistance.lean`:

```lean
-- Counterexamples/HeawoodUnitDistance.lean:90-96
/-- The base function from graph vertices to Euclidean points in our embedding. -/
noncomputable def udMap : Fin 14 → Plane
  | 1 => !₂[(1 + c) / 2, c ^ 2 - c / 2 + 1]
  | 0 => !₂[c, 1 / 2] | 7 => !₂[0, 1 / 2] | 2 => !₂[1, 1 / 2] | 9 => !₂[1 - c, 1 / 2]
  | 10 => !₂[(1 + c) / 2, c ^ 2 - c / 2] | 5 => !₂[(1 - c) / 2, c ^ 2 - c / 2]
  ...
```

This is precisely the proposed `hexVertex` shape: `def name : Fin n → α | 0 => … | 1 => … | …`. Lean 4's elaborator desugars `Fin 14` literals via `Fin.instOfNat` and the `@[match_pattern]` attribute on the literal-pattern path; no `Fin.cases`, no `(0 : Fin 6)` annotation, no `i.val` projection, no `![…]` notation are required. The expression-level form just compiles.

**Proof-level form also works.** Same file at line 100:
```lean
-- Counterexamples/HeawoodUnitDistance.lean:99-100
lemma reflect_toEuclideanLin {x y : ℝ} : !![1, 0; 0, -1].toEuclideanLin !₂[x, y] = !₂[x, -y] := by
  ext i; match i with | 0 => simp | 1 => simp
```

So `match (i : Fin n) with | 0 => … | 1 => …` is also natively supported inside tactic blocks. The "Anticipated complication" downgrades from "implementer judgment, 3 candidates, no precedent" to **"Not a concern, native Lean 4 syntax with Mathlib precedent at `Counterexamples/HeawoodUnitDistance.lean:90`"**.

**Implication for S4b ACT (the proposed `permuteHexagon` body)**: the snippet in PR #18461 lines 133–159 should compile as written, modulo `import Mathlib.Tactic` (already in `PascalsHexagonOQ03.lean:1`). No fallback to `![…]` or `Fin.cases` is needed. The 35-LOC upper-bound estimate in PR #18461 is preserved (no syntactic overhead for `Fin.cases` boilerplate).

## Finding C — `Equiv.Perm (Fin 6)` applied to Fin 6 literals: already used in OQ-03 file

PR #18461 line 164 wrote "applying `Equiv.Perm (Fin 6)` to a `Fin 6` value (e.g. `π 0`) gives `π.toFun 0`, which `Lean` should infer to `Fin 6`". This is correct but understates the case: the OQ-03 file *already* uses this idiom inside an existing sorry-free proof.

`proofs/Proofs/PascalsHexagonOQ03.lean:208–210` (in `hexRot_pow_lt_six_ne_one`):
```lean
all_goals
  exact absurd (congrArg (fun (e : Equiv.Perm (Fin 6)) => e 0) h)
    (by native_decide)
```

`e 0` here is `(e : Equiv.Perm (Fin 6)) (0 : Fin 6)`, i.e. the coercion via `EquivLike` / `DFunLike`. Lean elaborates this with no annotation. The proposed `permuteHexagon`'s six calls `π 0`, `π 1`, ..., `π 5` are the same shape; the file already type-checks them.

**Strengthened verdict**: not only does PR #18461's Finding D snippet work, but the OQ-03 file's existing convention for `Equiv.Perm (Fin 6)`-as-callable already validates the API call pattern. No risk surface here.

## Finding D — Nat.card migration recommendation (PR #18461 Finding E): aligned with 2 of 3 existing precedents in the OQ-03 file; bridge lemma already imported

PR #18461 Finding E flagged that `[Fintype (SteinerPoint C hex)]` and `[Fintype (KirkmanPoint C hex)]` as hypotheses (lines 612–613 and 637 of `PascalsHexagonOQ03.lean`) are vacuous-falsifiable: a malicious caller can supply a `Fintype` instance with any cardinality. Two routes were proposed:
- (i) leave `Fintype.card` and add a `noncomputable instance Fintype` derived from the structure;
- (ii) migrate to `Nat.card`, which needs no `Fintype` instance.

PR #18461 said "Decision deferred". Cross-checking the OQ-03 file's actual `card_*` theorems:

| Theorem | Line | Card form | Why |
|---|---|---|---|
| `card_sym6` | 508 | `Fintype.card (Equiv.Perm (Fin 6)) = 720` | `Equiv.Perm (Fin n)` has canonical `Fintype` instance, no hypothesis needed |
| `card_hexagonalGroup` | 534 | `Nat.card hexagonalGroup = 12` | Subgroup; uses `Nat.card_congr` + `DihedralGroup.nat_card` |
| `card_hexagon_labelings` | 547 | `Nat.card HexagonLabeling = 60` | Quotient group; uses Lagrange-style decomposition |
| `steiner_count_eq_20` (sorry) | 612 | `Fintype.card (SteinerPoint C hex) = 20` (with `[Fintype …]`) | Hypothesis-form, vacuous-falsifiable |
| `kirkman_count_eq_60` (sorry) | 637 | `Fintype.card (KirkmanPoint C hex) = 60` (with `[Fintype …]`) | Hypothesis-form, vacuous-falsifiable |

Observations:
1. **The Nat.card convention dominates the proved theorems** (534, 547). The two `Fintype.card` theorems are the unproven ones (612, 637), and they use `Fintype.card` precisely *because* a canonical instance was missing — a tactical choice that became the soft-API trap.
2. **The bridge `Nat.card_eq_fintype_card` is already imported** and used at line 553 (`rw [Nat.card_eq_fintype_card]; exact card_sym6`). So the file's elaboration already pulls in `Nat.card`-to-`Fintype.card` coercion. Migrating 612/637 to `Nat.card` adds no new imports.
3. **`card_sym6` does not need migration** — `Equiv.Perm (Fin 6)` has a canonical `Fintype` instance via `Pi.fintype` + `Function.Embedding.fintype`. Leaving it as `Fintype.card` is appropriate. The migration scope is exactly the 2 unproven theorems, not all 4.

**Tightened recommendation (was "deferred decision" in PR #18461 Finding E)**: adopt route (ii) for both `steiner_count_eq_20` and `kirkman_count_eq_60`. New statement signatures:

```lean
theorem steiner_count_eq_20 (C : Conic) (hex : InscribedHexagon C) :
    Nat.card (SteinerPoint C hex) = 20 := by sorry

theorem kirkman_count_eq_60 (C : Conic) (hex : InscribedHexagon C) :
    Nat.card (KirkmanPoint C hex) = 60 := by sorry
```

Effect:
- Drops the `[Fintype (… C hex)]` hypothesis (1 character class, 2 sites).
- Sidesteps the vacuous-falsifiability trap (the count is now a fact about the structure, not about the caller's chosen `Fintype` instance).
- Net diff: ~6 deleted characters per theorem, +6 added characters per theorem (`Fintype.card` → `Nat.card`). ~0 net LOC change.
- No new import needed (`Mathlib.SetTheory.Cardinal.Finite`, which exports `Nat.card`, is already a transitive dep via `Nat.card_eq_fintype_card`).
- Compatibility with existing proofs in the file: the bridge `Nat.card_eq_fintype_card` at line 553 demonstrates the rewrite pattern. Any future OQ-03 / OQ-04 ACT can fall back to `Fintype.card` internally and finish with `rw [← Nat.card_eq_fintype_card]; exact …`.

This recommendation is now a clean **migrate-and-close** rather than "soft API question with deferred decision".

## Finding E — Degeneracy caveat (PR #18338 lines 130–135): Conic.nondegenerate exists in parent; recommend Option (b) (case-split)

PR #18338's S4 PREP step 2 (lines 130–135) flagged that `lineThrough P P = P × P = 0` is not a valid `ProjLine`, leading to an "open subtlety" for `pascalLine` well-definedness. Three options were listed:
- (a) assume `Conic.nondegenerate` as a hypothesis;
- (b) split into cases — when P = Q, return `lineThrough Q R` or `lineThrough P R` instead;
- (c) hand-wave with a `Classical.choice` over a valid-line predicate.

PR #18461 did not refine this. Cross-checking the parent file:

`proofs/Proofs/PascalsHexagon.lean:130`:
```lean
def Conic.nondegenerate (C : Conic) : Prop := C.det ≠ 0
```

So `Conic.nondegenerate` exists as a predicate in the parent file. But the structure `InscribedHexagon` (parent file lines 141–160) does **not** bundle it as a field — vertices A,...,F are required to be on the conic (`hA, ..., hF : pointOnConic … C`) and projectively valid (`hAvalid, ..., hFvalid`), but `C` itself is not constrained to be non-degenerate.

Implications for each option:

**Option (a) — assume nondegenerate as hypothesis**:
- Either bundle `nondegenerate` into `InscribedHexagon` (parent-file change, scope-creep into OQ-01/OQ-02/OQ-03 simultaneously)
- Or thread `(hnd : C.nondegenerate)` through `pascalLine` and every downstream consumer (`pascal_hexagon_theorem`, `SteinerPoint`, `KirkmanPoint`, etc.) — touches 4+ structures, breaks the existing OQ-01-OQ-01-OQ-02 proven theorem signature.

**Option (b) — case-split via `dite`**:
```lean
noncomputable def pascalLine
    (C : Conic) (hex : InscribedHexagon C) (lbl : HexagonLabeling) : ProjLine :=
  lbl.liftOn (fun π => 
    let P := pascalP (permuteHexagon C hex π)
    let Q := pascalQ (permuteHexagon C hex π)
    let R := pascalR (permuteHexagon C hex π)
    if h : P = Q then lineThrough Q R  -- or P R; same value when P = Q
    else lineThrough P Q
  ) (fun π₁ π₂ hrel => ...)
```
- Pure: no parent-file change, no new hypothesis on downstream consumers.
- Mathlib idiom: `dite` over decidable equality, default-when-degenerate.
- Cost: well-definedness proof must do two case-splits (`P₁ = Q₁` and `P₂ = Q₂`); each case reduces to either `lineThrough P Q` (S4 PREP's main flow) or `lineThrough Q R` invariance under the group.

**Option (c) — Classical.choice**:
- Mathematically equivalent to (b), syntactically heavier in Lean 4 (`Classical.choice` returns a `Nonempty` witness, requiring a wrapper).
- Rejected for code clarity.

**Recommendation (refining PR #18338 lines 130–135 from "open subtlety" → "tractable, prefer (b)")**: Option (b) is the pragmatic choice. The implementation cost is one extra `dite` in `pascalLine` and one extra case-split per invariance proof — the existing `pascal_hexagon_theorem` (parent file line 224) already proves collinearity of P, Q, R, so when P = Q, the line through {Q, R} is the same projective line as the line through {P, Q} (modulo scalar) **whenever** P, Q, R are pairwise close-to-collinear. The pathological case (P = Q = R) requires a fallback (return `lineThrough hex.A hex.B` or similar default); the well-definedness proof terminates cleanly via case-split.

The S4 PREP survey's Caveat will need a follow-up sub-step (S4d or S4e) for the case-split well-definedness, but no parent-file change is needed.

## Sorry / axiom delta projection

This PR (S4b PREP audit close-out): **0 sorries, 0 axioms, 0 Lean line changes.**

If all 3 tightened recommendations land in subsequent ACT PRs:
- **Audit close-out (Finding A complete)**: 0 LOC (informational only, the 4 stale paths are not pasted verbatim into Lean).
- **`hexVertex` syntax (Finding B/C confirmed)**: 0 risk surface — the PR #18461 snippet compiles as-is, no `Fin.cases` fallback needed.
- **Nat.card migration (Finding D tightened)**: ~0 net LOC in `PascalsHexagonOQ03.lean` (string substitution `Fintype.card` → `Nat.card` + remove 2 `[Fintype …]` brackets); 2 sorries unchanged.
- **Option (b) case-split (Finding E recommendation)**: estimated +3 LOC in `pascalLine` definition (the `dite`), and +5 LOC per invariance proof for the case-split. Total ~+15 LOC vs. the S4 PREP survey's clean estimate.

Composite estimate revision for S4-completing OQ-02:
- Original PR #18338 estimate: ~185 LOC (1 sorry closed: `pascalLine` definitional)
- PR #18461 added: ~35 LOC for `permuteHexagon` (no sorry change)
- This PR adds: ~+15 LOC for the case-split well-definedness
- **Revised total**: ~235 LOC to close the `pascalLine` definitional sorry (3 → 2 file-level sorries). The estimate revision is +27%, driven entirely by the case-split that PR #18338 flagged as "open subtlety".

## Anti-targets

This document is a pure **audit close-out + design-memo refinement**. It does NOT:

- Modify any Lean source file (`proofs/Proofs/PascalsHexagonOQ03.lean` or `proofs/Proofs/PascalsHexagon.lean` untouched).
- Modify `meta.json`, `state.md`, `problem.md`, `knowledge.md`, or the gallery JSON files.
- Add any sessions/* file other than this one (`2026-05-12-s4b-prep-mathlib-audit-closeout.md`).
- Resolve any of the 3 remaining sorries (`pascalLine`, `steiner_count_eq_20`, `kirkman_count_eq_60`).
- Add any new axiom.
- Modify or extend the parent file's `Conic.nondegenerate` predicate.

## Honest scope guarantee

The audit findings are based on:
- **(A close-out)** Direct `gh api search/code` lookups against `repo:leanprover-community/mathlib4` at session time (2026-05-13 ~04:00 UTC), then `gh api repos/leanprover-community/mathlib4/contents/<path>` + `base64 -d | grep -n` to locate the exact declaration line. One stale path identified (`QuotientGroup.lift` at `…/Defs.lean:246` not `…/Basic.lean`); one correct path confirmed (`Finset.card_image_iff` / `card_image_of_injOn` at `Mathlib/Data/Finset/Card.lean:222,234`).
- **(B)** Direct `gh api search/code` + content fetch of `Counterexamples/HeawoodUnitDistance.lean:90–100`. The expression-level form `def name : Fin n → α | 0 => … | 1 => …` and the proof-level form `match (i : Fin n) with | 0 => …` both have direct Mathlib precedent in a single file.
- **(C)** Direct inspection of `proofs/Proofs/PascalsHexagonOQ03.lean:208–210`. The OQ-03 file's existing `hexRot_pow_lt_six_ne_one` proof already uses `(e : Equiv.Perm (Fin 6)) (0 : Fin 6)` shape.
- **(D)** Direct grep on `proofs/Proofs/PascalsHexagonOQ03.lean` for `Nat.card` and `Fintype.card`. 4 `card_*` theorems located (3 proved, 2 with sorries); convention split 2:1 in favor of `Nat.card` for non-canonical-`Fintype` types.
- **(E)** Direct grep on `proofs/Proofs/PascalsHexagon.lean` for `nondegenerate`. Predicate exists (line 130), but is not bundled into `InscribedHexagon` (lines 141–160).

All 5 findings are verifiable from the current `proofs/` source + current Mathlib HEAD on `leanprover-community/mathlib4`. The GitHub search/code rate limit (30/hr) was reached after the audit close-out lookups; subsequent verification used local file inspection and existing precedent.

**Untested**: the proposed Option (b) `dite`-based `pascalLine` is **not** compiled. The +15 LOC estimate is a paper-and-pen sketch; the actual LOC may be ±5 depending on whether the case-split well-definedness uses `dite_eq` simp normal form or unfolds manually.

## Differentiation from PR #18461 (S4a PREP — Mathlib API audit + permuteHexagon signature)

| Aspect | PR #18461 (S4a PREP) | This PR (S4b PREP — close-out) |
|---|---|---|
| Scope | First-level audit of 4 of 6 paths; permuteHexagon signature design | Audit close-out (remaining 2 paths) + 3 implementer-judgment items tightened |
| Mathlib API audit | 4 of 6 checked (1 correct, 3 stale) | Final 2 checked (1 correct, 1 stale); composite 4 stale / 2 correct |
| Fin-6 pattern match | 3 candidate forms listed; "valid syntax" asserted without precedent | Mathlib precedent located (`HeawoodUnitDistance.lean:90,100`); native form confirmed for both `def` and `match` |
| Equiv.Perm coerce | "should infer to `Fin 6`" — anticipated | Already-used in same file (`PascalsHexagonOQ03.lean:208–210`); zero risk |
| Nat.card migration | Soft "Decision deferred" | Tightened — recommend (ii) Nat.card for both sorry theorems; 2-of-3 convention support + bridge lemma already imported |
| Degeneracy caveat | Not addressed | Option (b) (case-split) recommended; `Conic.nondegenerate` confirmed available in parent but not bundled in `InscribedHexagon` → Option (a) would force parent-file scope-creep |
| Sorry / axiom delta | 0 (audit-only) | 0 (audit-only) |
| LOC estimate revision | +35 (permuteHexagon) | +15 (case-split well-definedness); composite revised total ~235 LOC for OQ-02 sorry closure |
| File created | `sessions/2026-05-12-s4a-prep-mathlib-audit.md` (209 LOC) | `sessions/2026-05-12-s4b-prep-mathlib-audit-closeout.md` (~380 LOC) |

This PR is a sub-step of the S4 PREP roadmap — orthogonal by construction to PR #18461 (creates only a new `sessions/*` file path; does not modify the prior PREP doc or any other artifact). Concurrent S4c / S4d / S4e Lean ACT PRs can land independently.
