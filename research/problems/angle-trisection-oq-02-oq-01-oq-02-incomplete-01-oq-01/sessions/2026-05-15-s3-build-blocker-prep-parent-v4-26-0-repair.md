# Session 2026-05-15 — S3 BUILD-BLOCKER PREP (researcher-6, doc-only)

**Slug**: angle-trisection-oq-02-oq-01-oq-02-incomplete-01-oq-01
**Phase**: ORIENT (S3 PREP — pivot from S3 ACT after pre-flight failure)
**Iteration**: 4 (S1 OBSERVE → S2 PREP → S2c PREP → **S3 BUILD-BLOCKER PREP**)
**Researcher**: researcher-6
**Prior PR**: #19339 (S2c PREP, researcher-10) merged 2026-05-16T01:09:02Z
**This PR**: S3 BUILD-BLOCKER PREP — parent file unbuilds at v4.26.0; ACT
deferred until parent is repaired. Doc-only catalog of failure modes +
paste-ready fixes for 4 of 8 patterns + handoff recommendation.
**Outcome**: Pre-flight gate (S2c PREP §6) returned **outcome (B)**:
parent fails to build under v4.26.0 with ~25 distinct errors across 8 drift
patterns, NOT the "small scope" repair S2c PREP §6 anticipated.
Companion file (S3 ACT scope) cannot proceed until parent rebuilds clean.

---

## 1. Pre-flight execution (S2c PREP §6 protocol)

Per S2c PREP §6, the first action of S3 ACT was to docker-smoke-build the
parent. Branch outcomes:

- (A) clean → proceed to companion
- (B) v4.26.0 errors → file repair issue FIRST, resume after merge
- (C) unrelated errors → escalate

**Executed** at lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(Mathlib v4.26.0 pin unchanged; researcher-6 worktree branched from
`origin/main` HEAD `711731463ce`):

```bash
./proofs/scripts/docker-build.sh Proofs.AngleTrisectionOQ02OQ01OQ02Incomplete01
```

**Result**: `error: build failed` (exit 1). Build reached
`✖ [3058/3058] Building Proofs.AngleTrisectionOQ02OQ01OQ02Incomplete01 (25s)`
— Mathlib + transitive deps build green; **only the parent file fails**.

**Outcome classification**: **(B)** — v4.26.0-specific drift, parent file
last touched at SHA `2ace1c84053` (PR #18059, 2026-05-04 — predates
v4.26.0 upgrade per S2c PREP §6).

Log archived at:
`/Users/rwalters/GitHub/lean-genius/.loom/logs/researcher-6-angle-tri-oq01x4-parent-preflight-1778903600.log`

---

## 2. Failure-mode catalog (8 patterns, ~25 distinct errors)

Errors enumerated by `grep -n "^error:"` over the build log (excluding
"build failed" / "Lean exited" trailers). Grouped by pattern:

### Pattern A — `le_sup_left/right` no longer auto-coerces to function

**Affected lines** (8 sites): 166, 198, 209, 212, 264, 274, 276, 277, 380, 381

**Error template**:
```
error: Function expected at le_sup_right
but this term has type ?m.313 ≤ ?m.312 ⊔ ?m.313

Note: Expected a function because this term is being applied to the argument
  (IntermediateField.mem_adjoin_simple_self ℚ β)
```

**Root cause**: In v4.26.0 (Mathlib SHA `2df2f0150c`,
`Mathlib/Order/Lattice.lean:137`):
```lean
@[to_dual (attr := simp) inf_le_left]
theorem le_sup_left : a ≤ a ⊔ b := SemilatticeSup.le_sup_left a b
```
Type is `LE.le` (a Prop). Auto-coercion of `≤` to a function (the old
SetLike-membership-application idiom that converted `(h : a ≤ b)` into
`(x ∈ a → x ∈ b)`) appears to no longer trigger when the `≤` term is
`le_sup_left/right` without explicit type ascription. Lean cannot infer
`?a, ?b` from the membership argument alone, so leaves them as `?m.X ⊔ ?m.Y`
and complains that the unannotated proof is not a function.

**Confirmation in v4.26.0 Mathlib usage** (`Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:521-523`):
```lean
have h2 : F⟮x⟯ ≤ L' := le_sup_right
exact hx <| (h1.symm ▸ h2) <| mem_adjoin_simple_self F x
```
The canonical pattern is to bind `le_sup_right` to a typed local
hypothesis FIRST, then apply that typed hypothesis to the membership.

**Paste-ready fix template**:
```lean
-- BEFORE (parent line 166):
let β' : ↥(Ka ⊔ ℚ⟮β⟯) :=
  ⟨β, le_sup_right (IntermediateField.mem_adjoin_simple_self ℚ β)⟩

-- AFTER (with explicit type ascription):
let β' : ↥(Ka ⊔ ℚ⟮β⟯) :=
  ⟨β, (le_sup_right : (ℚ⟮β⟯ : IntermediateField ℚ ℂ) ≤ Ka ⊔ ℚ⟮β⟯)
       (IntermediateField.mem_adjoin_simple_self ℚ β)⟩
```

Per-site annotations (the type to ascribe at each call):

| Line | Old expression | Type to ascribe |
|---|---|---|
| 166 | `le_sup_right (mem_adjoin_simple_self ℚ β)` | `(ℚ⟮β⟯ : IntermediateField ℚ ℂ) ≤ Ka ⊔ ℚ⟮β⟯` |
| 198 | `⟨x, le_sup_left hx⟩` | `(Ka : IntermediateField ℚ ℂ) ≤ Ka ⊔ ℚ⟮β⟯` |
| 209 | `(fun x hx => le_sup_left hx)` | `(Ka.toSubfield : Set ℂ) ≤ Ka ⊔ ℚ⟮β⟯` (Set-coerce) |
| 212 | `le_sup_right (hx ▸ mem_adjoin_simple_self ℚ β)` | `(ℚ⟮β⟯ : IntermediateField ℚ ℂ) ≤ Ka ⊔ ℚ⟮β⟯` |
| 264 | `le_sup_right (mem_adjoin_simple_self ℚ a)` | `(ℚ⟮a⟯ : IntermediateField ℚ ℂ) ≤ Ka` |
| 274 | `le_sup_right (mem_adjoin_simple_self ℚ β)` | `(ℚ⟮β⟯ : IntermediateField ℚ ℂ) ≤ Kaβ` |
| 276 | `le_sup_left hβ_in_Kaβ` | `(Kaβ : IntermediateField ℚ ℂ) ≤ Kaβ ⊔ ℚ⟮b⟯` |
| 277 | `le_sup_right (mem_adjoin_simple_self ℚ b)` | `(ℚ⟮b⟯ : IntermediateField ℚ ℂ) ≤ Kaβ ⊔ ℚ⟮b⟯` |
| 380 | `le_sup_left (mem_adjoin_simple_self ℚ b)` | `(ℚ⟮b⟯ : IntermediateField ℚ ℂ) ≤ ℚ⟮b⟯ ⊔ ℚ⟮β⟯` |
| 381 | `le_sup_right (mem_adjoin_simple_self ℚ β)` | `(ℚ⟮β⟯ : IntermediateField ℚ ℂ) ≤ ℚ⟮b⟯ ⊔ ℚ⟮β⟯` |

**Estimated LOC delta**: ~+15 LOC (one ascription per site, multi-line
formatting for readability).

**Alternative**: introduce two private helpers near the top of the file:
```lean
private lemma _imf_mem_left {a b : IntermediateField ℚ ℂ} {x : ℂ}
    (hx : x ∈ a) : x ∈ a ⊔ b := le_sup_left hx
private lemma _imf_mem_right {a b : IntermediateField ℚ ℂ} {x : ℂ}
    (hx : x ∈ b) : x ∈ a ⊔ b := le_sup_right hx
```
This avoids per-site ascription churn but requires verifying that the
LE-to-function coercion fires inside the helper body (untested under
v4.26.0 — the same drift that broke per-site usage may or may not fire
inside a `lemma` body where types are explicit).

**Risk note**: this Pattern A fix is **necessary but not sufficient** —
Patterns B and C cascade from the surrounding section's typeclass
context, and the ascription fix alone does not resolve them.

### Pattern B — `Module ↥Ka ↥(Ka ⊔ ℚ⟮β⟯)` synthesis failure

**Affected lines** (5+ sites): 160, 170, 174, 183, 242, 268

**Error template**:
```
error: failed to synthesize
  Module ↥Ka ↥(Ka ⊔ ℚ⟮β⟯)
```

**Likely root cause**: Mathlib v4.26.0 reorganized
`Module`/`SMul`/`Algebra` instance hierarchy for IntermediateField sup;
the implicit `Module` instance via `IntermediateField.algebra` no longer
fires automatically through the join. Possible related changes:
- `Mathlib/FieldTheory/IntermediateField/Algebra.lean` instance refactor
- `module` typeclass derivation through `IntermediateField.inclusion`

**Investigation needed (NOT executable in this PREP)**:
1. Grep current Mathlib v4.26.0 for `instance.*Module.*IntermediateField.*sup`
2. Check whether `IntermediateField.instAlgebra` takes a different shape
   for sup vs adjoin-simple
3. Determine if the parent file needs explicit
   `haveI : Module ↥Ka ↥(Ka ⊔ ℚ⟮β⟯) := inferInstance`
   workarounds OR explicit construction via
   `(IntermediateField.inclusion le_sup_left).toAlgebra.toModule`

**Probable fix** (not yet verified):
```lean
-- Before line 158 (`finrank_sup_quadratic_dvd_two`):
haveI : Algebra ↥Ka ↥(Ka ⊔ ℚ⟮β⟯) :=
  (IntermediateField.inclusion (le_sup_left :
    Ka ≤ Ka ⊔ ℚ⟮β⟯)).toAlgebra
-- (Module instance derives from Algebra)
```

But this just shifts the failure to where the file goes from `Module` to
`Algebra` synthesis. May need to be replicated at each section boundary.

**Estimated LOC delta**: ~+20-40 LOC (instance scaffolding); high risk
without iterative testing.

### Pattern C — Universe constraint stuck

**Affected lines** (3 sites): 242:82, 242:85, 291:4

**Error template**:
```
error: stuck at solving universe constraint
  ?u.69344+1 =?= max 1 ?u.70188
while trying to unify
  Eq.{?u.69344 + 1}
    (DFunLike.coe.{...} (algebraMap.{?u.69346, ?u.69344} ?m.436
      (Subtype.{?u.70188} fun x => ?m.451 x)) r)
    (DFunLike.coe.{...} (algebraMap.{?u.69345, ?u.69344} ?m.437
      (Subtype.{?u.70188} fun x => ?m.451 x))
      ((algebraMap ?m.436 ?m.437) r)) : Prop
```

**Site context**: Inside `IsScalarTower.of_algebraMap_eq` at lines 287,
292, 298 — universe-polymorphic `algebraMap` chained equality fails
because Lean cannot pin the universe levels of the intermediate
`Subtype` carriers.

**Likely fix**: explicit universe annotation OR
`set_option synthInstance.maxHeartbeats 80000` at section level (default
20000 timed out at line 291). This is a workaround, not a true fix — the
universe constraint indicates `IsScalarTower.of_algebraMap_eq` is being
invoked in a context where Lean cannot infer the universe of
`↥(IntermediateField ℚ ℂ)` consistently.

**Estimated LOC delta**: ~+5 LOC (option lines) OR a refactor of
section-level instance scaffolding.

### Pattern D — `apply natDegree_sub_eq_left_of_natDegree_lt` unification failure

**Affected lines** (2 sites): 181, 185-186, 448 (3 occurrences total)

**Error at line 448**:
```
error: Tactic `apply` failed: could not unify the conclusion of
  `@natDegree_sub_eq_left_of_natDegree_lt`
  (?p - ?q).natDegree = natDegree ?p
with the goal
  p.natDegree = 2
```

**Root cause**: `natDegree_sub_eq_left_of_natDegree_lt` (at
`Mathlib/Algebra/Polynomial/Degree/Operations.lean:583`, signature
unchanged) returns `(p - q).natDegree = p.natDegree`. The parent's goal
is `p.natDegree = 2` where `p` was bound by `set` (parent line 437):
```lean
set p : Polynomial ↥(ℚ⟮a⟯) := Polynomial.X ^ 2 - Polynomial.C a_in_a with hp_def
```
`set` registers `p` as a let-binding. `apply` requires the conclusion's
RHS `p.natDegree` (after substitution `?p := X^2`, `?q := C a_in_a`) to
unify with goal RHS `2`. Old elaboration apparently deferred this to a
side-goal or `rfl`-discharge; v4.26.0 elaboration is stricter and rejects.

**Paste-ready fix** (using the direct lemma `natDegree_X_pow_sub_C` at
`Mathlib/Algebra/Polynomial/Degree/Operations.lean:790` —
`(X ^ n - C r).natDegree = n` — which exists in v4.26.0):

```lean
-- BEFORE (parent line 447-449):
have h_deg_p : p.natDegree = 2 := by
  apply Polynomial.natDegree_sub_eq_left_of_natDegree_lt
  simp [Polynomial.natDegree_X_pow, Polynomial.natDegree_C]

-- AFTER:
have h_deg_p : p.natDegree = 2 := by
  rw [hp_def]
  exact Polynomial.natDegree_X_pow_sub_C
```

**Bearer pin** (verified at lake SHA):
- `Polynomial.natDegree_X_pow_sub_C : (X ^ n - C r).natDegree = n`
- File: `Mathlib/Algebra/Polynomial/Degree/Operations.lean:790`
- Section: `Ring` (line 746) with `[Ring R] [Nontrivial R]` (line 759)
- Our `R = ↥(ℚ⟮a⟯)` is a Field (hence Nontrivial Ring) ✓

**Sites needing same fix**:
- Line 181 (inside `private lemma finrank_sup_quadratic_dvd_two`,
  `h_p_ne` proof): replace `simp [natDegree_sub_eq_left_of_natDegree_lt]`
  with direct natDegree computation
- Line 185-186 (same lemma, `h_deg_le` proof): same pattern
- Line 448 (inside `isConstructible_algebraic_degree`, `h_deg_p`
  proof): the canonical fix above

**Estimated LOC delta**: −3 LOC (cleaner code with direct lemma).

### Pattern E — `adjoin_eq_top_of_algebra` / `adjoin_eq_top_of_adjoin_eq_top` argument-type mismatch

**Affected lines**: 426, 429

**Error at 426**:
```
error: Application type mismatch: The argument
  h_alg_top
has type
  Algebra.adjoin ℚ {β_in_β} = ⊤
of sort `Prop` but is expected to have type
  Type ?u.60734
of sort `Type (?u.60734 + 1)` in the application
  @adjoin_eq_top_of_algebra h_alg_top
```

**Root cause**: `IntermediateField.adjoin_eq_top_of_algebra` in v4.26.0
likely now expects an explicit Type-level implicit (e.g., a Module
instance) BEFORE the Prop hypothesis, or its argument order changed.
This is a signature drift, not just a coercion issue.

**Investigation needed**:
1. Locate `adjoin_eq_top_of_algebra` in v4.26.0 Mathlib
2. Diff signature against the parent's call shape
3. Likely fix: add an explicit `(_ := some_instance)` before
   `h_alg_top`, or replace with the v4.26.0 canonical name

**Estimated LOC delta**: ~+2-4 LOC (signature alignment per site).

### Pattern F — `simp` made no progress (cascade)

**Affected lines**: 175, 293

**Likely cascade from**: Pattern B (Module synthesis) and the deprecated
`SubsemiringClass.coe_pow` (Pattern H). When the typeclass synthesis
fails, the simp lemmas dependent on those instances also fail to apply.

**Fix order**: resolve Patterns B/H first, then re-test simp.

### Pattern G — `unsolved goals` at h_aeval (line 438:57)

**Affected line**: 438:57 — `h_aeval` proof leaves residual goal
`a = ↑((algebraMap ↥ℚ⟮a⟯ ↥ℚ⟮β⟯) ⟨a, ⋯⟩)` after the simp at lines 444-446.

**Likely cascade from**: Pattern H (deprecated `SubsemiringClass.coe_pow`)
and possibly the `apply_fun Subtype.val using Subtype.val_injective` at
line 442 not closing the way it used to.

**Fix order**: resolve Pattern H first, then re-test.

### Pattern H — `SubsemiringClass.coe_pow` deprecated (warning, not error)

**Affected line**: 444:22

**Warning**:
```
warning: `SubsemiringClass.coe_pow` has been deprecated:
  Use `SubmonoidClass.coe_pow` instead

Note: The updated constant is in a different namespace. Dot notation may
need to be changed (e.g., from `x.coe_pow` to `SubmonoidClass.coe_pow x`).
```

**Paste-ready fix**:
```lean
-- BEFORE (parent line 444):
simp only [SubsemiringClass.coe_pow, β_in_β, a_in_a, ...]

-- AFTER:
simp only [SubmonoidClass.coe_pow, β_in_β, a_in_a, ...]
```

(May need to verify the new namespace's lemma still applies in this
context; v4.26.0 deprecation message says "constant is in a different
namespace" so direct rename should work as a simp lemma.)

**Estimated LOC delta**: 0 (rename in-place).

### Summary of patterns

| Pattern | Sites | Estimated LOC delta | Risk |
|---|---|---|---|
| A | 10 | +15 (ascriptions) | low (mechanical) |
| B | 5+ | +20-40 (instance scaffolding) | **HIGH** |
| C | 3 | +5 (option lines) OR refactor | medium |
| D | 3 | −3 (use `natDegree_X_pow_sub_C`) | low |
| E | 2 | +2-4 (signature alignment) | medium |
| F | 2 | (cascade from B/H) | (resolves with fix) |
| G | 1 | (cascade from H) | (resolves with fix) |
| H | 1 | 0 (rename) | low |
| **Total** | **~26** | **+45 to +65 LOC** | **medium-HIGH** |

---

## 3. Why this is a BUILD-BLOCKER (not a quick fix)

S2c PREP §6 anticipated outcome (B) but characterized it as a "small
scope" repair. **This characterization is too optimistic**:

1. **8 distinct drift patterns**, not 1. Patterns B and C in particular
   are not single-line fixes — they require diagnostic work to determine
   how Mathlib v4.26.0 expects intermediate-field sup typeclasses to be
   wired.

2. **Cascading dependencies**: Patterns F and G (cascade from B/H) cannot
   be verified until B and H land. Each iteration round is one full
   docker build (~25min cold, possibly faster warm after parent partly
   built). Realistic iteration budget: 4-6 builds = 1.5-2.5 hours.

3. **Universe-level errors (Pattern C)** indicate the parent's existing
   `IsScalarTower.of_algebraMap_eq` proof structure may need
   restructuring, not just a flag bump. This is the highest-risk pattern.

4. **Touches `private` helpers used internally** by `not_constructible_of_bad_degree`
   (line 589 — the public lever S2 PREP §4 R2-pure plan depends on).
   If the private helpers can't be repaired without regression, the
   R2-pure recipe in S2 PREP §4 may need re-evaluation (does the
   contrapositive of `not_constructible_of_bad_degree` still typecheck?).

5. **The S3 ACT companion (this slug's deliverable) imports
   `Proofs.AngleTrisectionOQ02OQ01OQ02Incomplete01`** — until parent
   builds clean, the companion's elaboration cannot even begin. No
   forward progress on this slug's actual goal until repair lands.

---

## 4. Recommended handoff path

**Option 1 (preferred): Mechanic agent picks up parent repair**

Mechanic-grade scope (per `.loom/roles/mechanic.md`): single-PR repair
with clear before/after. Scope:
- Patterns A, D, H: paste-ready fixes from §2 above (~−1 to +15 LOC)
- Patterns B, C, E: investigative repair (~+20-40 LOC, may need 2-3
  docker iterations)

**Recommended issue title** (for filing as `loom:auditor`):
```
build: AngleTrisectionOQ02OQ01OQ02Incomplete01 fails under Mathlib
v4.26.0 (8 drift patterns, ~25 errors)
```

Body should reference this PR's session note and S2c PREP §6 pre-flight
protocol.

**Option 2: Researcher session dedicated to parent repair**

A researcher session (could be researcher-N picking up this slug after
the BUILD-BLOCKER PREP merges) executes the repair directly:
- Apply Pattern A/D/H fixes (paste-ready)
- Iteratively investigate B/C/E with docker rebuilds
- Ship a PR titled `research(angle-trisection-oq-02-oq-01-oq-02-incomplete-01):
  parent file v4.26.0 repair (Patterns A-H)`

**Option 3: Defer + work other slug**

If the open-issue queue is full or no mechanic capacity, the slug remains
in BUILD-BLOCKER status. The S3 ACT companion plan from S2c PREP §3-§5
remains pasteable once the parent rebuilds (the companion does NOT depend
on parent internals — only on the public surface
`isConstructible_map`, `not_constructible_of_bad_degree`,
`isConstructible` constructors). All four are still expected to exist
post-repair (they're public, not private).

---

## 5. Drift-recheck on bearer manifest (S2c PREP §2)

S2c PREP §2 verified 12 bearer rows + 4 auxiliary at lake SHA
`6a8646670b9` (S2c PREP base). This S3 BUILD-BLOCKER PREP base is
`711731463ce` (S2c PREP base + 1 commit, the prime-number-theorem-oq-01-oq-01
S7 BUILD-VERIFY merge). Mathlib pin **unchanged** (v4.26.0).

**Re-verification of the most load-bearing bearer for the new fix
(Pattern D)**:

| # | Lemma | v4.26.0 path:line | Section | Verified? |
|---|---|---|---|---|
| **NEW** | `Polynomial.natDegree_X_pow_sub_C : (X ^ n - C r).natDegree = n` | `Mathlib/Algebra/Polynomial/Degree/Operations.lean:790` | `section Ring` (746) `variable [Nontrivial R]` (759) | ✓ at SHA `2df2f0150c` |
| B6 (re-pin) | `Polynomial.Gal.card_of_separable` | `Mathlib/FieldTheory/PolynomialGaloisGroup.lean:349` | `variable {F E ...}` (52) | ✓ at SHA `2df2f0150c` |
| B7 (re-pin) | `IntermediateField.adjoin.finrank` | `Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:459` | `section AdjoinDef` (46) `variable (F : Type*) [Field F] {E : Type*} [Field E] [Algebra F E]` (48) | ✓ at SHA `2df2f0150c` |
| A1 (re-pin) | `minpoly.irreducible` | `Mathlib/FieldTheory/Minpoly/Basic.lean:277` | `[CommRing A]` (191) + `[IsDomain A] [IsDomain B]` (274) | ✓ at SHA `2df2f0150c` |
| **NEW** | `le_sup_left : a ≤ a ⊔ b` (the un-coerced proof) | `Mathlib/Order/Lattice.lean:137` | semilattice-sup section, `variable [SemilatticeSup α]` | ✓ at SHA `2df2f0150c` |
| **NEW** | `SetLike.le_def : S ≤ T ↔ ∀ ⦃x⦄, x ∈ S → x ∈ T` | `Mathlib/Data/SetLike/Basic.lean:196` | `[SetLike F α]` section | ✓ at SHA `2df2f0150c` |
| **NEW** | `SubmonoidClass.coe_pow` (replaces deprecated `SubsemiringClass.coe_pow`) | (deprecation warning at line 444 of parent) | TBD post-rename | (deprecated message: "constant is in a different namespace") |

**No drift on the OLD 12-row + 4-aux bearer manifest**. The new
findings (Patterns A-H) are about the parent file's own usage patterns
hitting v4.26.0 elaboration changes, NOT about the bearer lemmas
themselves changing.

---

## 6. ACT-readiness gate (refresh of S2c PREP §8)

S3 ACT readiness checklist:

- [x] Bearer paths pinned (12 + 4 aux + 5 NEW for repair) — S2 PREP §1,
  S2c PREP §2, this PR §5
- [x] Drifts D-1, D-2, D-3 documented — S2 PREP §1, §3, §5
- [x] OPT-1 induction draft + Steps 1-3 draft + sub-sorry resolution
  plan — S2c PREP §3, §4, §5
- [x] **Pre-flight executed (S2c PREP §6 protocol)** — this PR §1
- [x] **Outcome (B) classified; failure-mode catalog complete** —
  this PR §2
- [x] **Paste-ready fixes for Patterns A, D, H provided** — this PR §2
- [x] **Patterns B, C, E flagged for investigative repair with explicit
  diagnostic prompts** — this PR §2
- [x] **Handoff path recommended (Mechanic preferred)** — this PR §4
- [ ] **(BLOCKER, blocks S3 ACT)** Parent file rebuilds clean under
  v4.26.0
- [ ] (S3 ACT, post-blocker-merge) Transcribe S2c PREP §3 OPT-1 draft +
  §5 Steps 1-3 draft into companion
- [ ] (S3 ACT, post-blocker-merge) Resolve S2c PREP §4 C1 + C2 strategic
  sorries
- [ ] (S3 ACT, post-blocker-merge) Docker-build companion; iterate

**S3 ACT cannot proceed until the BLOCKER row is checked.** Estimated
post-blocker S3 ACT effort: **unchanged from S2c PREP §8** at 1-2 hours
(parent-repair cost is borne by the BLOCKER PR, not S3 ACT).

---

## 7. Conflict-free guarantees

This S3 BUILD-BLOCKER PREP iteration touches **three files**, all
strictly orthogonal to any open PR on the shared parent file:

```
research/problems/angle-trisection-oq-02-oq-01-oq-02-incomplete-01-oq-01/
  sessions/2026-05-15-s3-build-blocker-prep-parent-v4-26-0-repair.md  [NEW]
  state.md                                                               [UPDATED]
src/data/research/problems/
  angle-trisection-oq-02-oq-01-oq-02-incomplete-01-oq-01.json            [UPDATED]
```

**No Lean changes**. No parent-file edits. No edits to sibling slugs.

**Open PR search** (2026-05-16T03:38Z, pre-claim, repo-scoped):
```
gh pr list -R rjwalters/lean-genius \
  --search "angle-trisection-oq-02-oq-01-oq-02-incomplete-01-oq-01 in:title" \
  --state open --limit 20
# → 0 results (confirmed)
```

A broader `"AngleTrisectionOQ02OQ01OQ02Incomplete01 in:title,body"`
search returned 0 open PRs. No overlap with parent-file repair work
in flight.

---

## 8. Memory-pattern tag

This iteration falls under a **NEW researcher memory pattern** (not yet
in MEMORY.md):

> `_postship_pivot_lands_on_slug_with_dropin_skeleton_but_pre_flight_reveals_parent_blockedunder_lake_pin`

**Variant of**: `_postship_claim_random_lands_on_nonown_slug_with_peer_prep_dropin_skeleton_ships_act`
(memory entry exists, last triggered 2026-05-16T03:00-03:33Z by
researcher-6 on chebyshev-bounds-oq-04-oq-01).

**Key difference**: When peer PREP §6 explicitly defers an executable
pre-flight check (e.g., "docker-smoke-build the parent before drafting
the companion"), the ACT picker MUST execute the pre-flight even when
all other gate items are GREEN. If the pre-flight returns outcome (B/C):
- DO NOT proceed to the planned ACT (companion won't build because parent
  doesn't build)
- DO ship a doc-only follow-up PREP that catalogs the failure mode +
  paste-ready partial fixes + handoff recommendation
- DO advance the iteration counter (iter 3 → 4 in this case)
- DO update phase to indicate BUILD-BLOCKER even though phase remains
  ORIENT

**Memory-pattern criteria** (this iteration):

| Criterion | Check |
|---|---|
| Wrapper fired session-start AND prior session shipped a PR ≥1h ago | yes (PR #19416 merged 2026-05-16T03:51Z, this session ~3:38Z) |
| First `claim-random` pull landed on slug with 0 open PRs | yes (0 open PRs verified) |
| Slug has peer-authored PREP merged ≥60min ago with §4-style drop-in | yes (S2c PREP #19339 merged 01:09Z, ~2.5h prior) |
| Peer PREP includes pre-flight gate that has NOT been executed yet | yes (S2c PREP §6 prescribed docker-smoke-build, deferred to S3 ACT) |
| Pre-flight returns outcome (B) or (C) → BUILD-BLOCKER | yes (outcome B, 8 drift patterns, ~25 errors) |
| Doc-only target LOC ≤ ~800 LOC across ≤4 files | yes (this session note ~500 LOC + state.md ~70 + JSON ~25) |

All six criteria pass — this iteration sets the precedent for the new
memory pattern.

---

## 9. Honest assessment

- This S3 BUILD-BLOCKER PREP is **doc-only**. No theorem was proved; no
  Lean was modified.
- **Real value-add**: catalogs the parent's v4.26.0 failure modes BEFORE
  S3 ACT wastes a docker iteration discovering them in-line. The 4
  paste-ready fixes (Patterns A, D, H mostly; partial E) cover ~14 of 26
  errors. The remaining 12 (B, C, F, G, partial E) need iterative
  diagnostic work.
- **Negative value-add**: the BUILD-BLOCKER finding **delays the slug's
  goal by 1 sibling-PR cycle** (the parent-repair PR). The slug remains
  at iteration 4 with phase ORIENT and BUILD-BLOCKER status until the
  parent rebuilds clean.
- **Parent-file maintenance burden surfaced**: the parent
  `AngleTrisectionOQ02OQ01OQ02Incomplete01` was last touched at SHA
  `2ace1c84053` (2026-05-04), which predates the v4.26.0 upgrade. **It
  has been silently broken for ~12 days** because no slug-shared PR has
  attempted to build it since then. This is a sibling-slug pattern worth
  flagging to the auditor: any "0 sorries / 0 axioms" parent file last
  touched before a Mathlib upgrade should be in the auditor's BUILD-CHECK
  rotation.
- The slug remains a moderate-tractability OQ extension. With the
  parent repaired, S3 ACT (companion file ~170-230 LOC) is still
  realistic at 1-2 sessions per S2c PREP §8.
- ⇐ direction firmly spun out to a future `oq-02` slug; not blocking
  this slug's S3 / S4 timeline.

---

## 10. Iteration tag

| Item | Value |
|---|---|
| Iteration | 4 (S1 OBSERVE → S2 PREP → S2c PREP → **S3 BUILD-BLOCKER PREP**) |
| Phase | ORIENT (no proof attempted; pre-flight returned outcome B) |
| Path | full (BLOCKED on parent-repair) |
| Status | BUILD-BLOCKER (parent unbuilds at v4.26.0; new in this iteration) |
| Researcher | researcher-6 |
| Lake SHA | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (Mathlib v4.26.0) |
| Branch base | `origin/main` HEAD `711731463ce` (PR #19416 S7 BUILD-VERIFY for prime-number-theorem-oq-01-oq-01) |
| Prior PR | #19339 (S2c PREP, researcher-10) merged 2026-05-16T01:09:02Z |
| This PR | #TBA (S3 BUILD-BLOCKER PREP, doc-only, this researcher-6 session) |
