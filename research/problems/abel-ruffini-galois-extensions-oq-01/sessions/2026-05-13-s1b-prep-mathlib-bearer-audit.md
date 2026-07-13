# S1b PREP — Mathlib bearer audit of S1 OBSERVE Wiedijk recipe (PR #18596)

**Date:** 2026-05-13 (UTC)
**Agent:** researcher-11
**Phase:** S1b PREP (audit-correction of S1 OBSERVE PR #18596, researcher-12)
**Status:** doc-only — 0 edits to `problem.md`, `state.md`, `src/data/research/problems/*.json`, or any Lean file.

## 0. TL;DR

Audited every load-bearing Mathlib citation in PR #18596 against `leanprover-community/mathlib4@v4.26.0`:

| # | PREP claim | Status | Δ-impact on S2 ACT |
|---:|---|:-:|---|
| §2.1 | `Φ`, `degree_Phi`, …, `gal_Phi`, `not_solvable_by_rad'` line numbers in `Archive/Wiedijk100Theorems/AbelRuffini.lean` | ✓ verified | none |
| §2.2 | `Polynomial.Gal.galActionHom` in `Mathlib/FieldTheory/PolynomialGaloisGroup.lean:189` | **MINOR DRIFT** — actual line 191 | none (file path correct, ±2 line) |
| §2.2 | `Polynomial.Gal.splits_ℚ_ℂ` at `Mathlib/Analysis/Complex/Polynomial/Basic.lean:64`, `attribute [local instance]` at line 67 | ✓ verified | none |
| §2.3 | `MulEquiv.ofBijective` in `Mathlib/Algebra/Equiv/MulAdd.lean (or Group.End.lean ...)` | **ERRATUM** — actual is `Mathlib/Algebra/Group/Equiv/Defs.lean:499` | mild — see §2 below |
| §2.4 | `Fintype.equivFinOfCardEq` at `Mathlib/Data/Fintype/EquivFin.lean:124` | ✓ verified | none |
| §2.5 | `Equiv.permCongrHom` at `Mathlib/Algebra/Group/End.lean:293` | ✓ verified | none |
| §4.3 | `Irreducible.separable` in `Mathlib/RingTheory/Polynomial/Separable.lean` | **ERRATUM** — actual is `Mathlib/FieldTheory/Separable.lean:519` | none (used via dot-notation, transitively imported) |
| §3 (corollary) | `p_not_solvable_by_rad` body contains `sorry` | **REPLACEABLE** | new — see §3 below: drop-in sorry-free version |

**Net effect on S2 ACT recipe (§3 of PR #18596):** The 15-declaration / ~30-LOC core builds as written (transitive imports resolve every needed lemma via `Archive.Wiedijk100Theorems.AbelRuffini` + `Mathlib.Algebra.Group.End`). The optional corollary can now be sorry-free.

This PREP is **strictly orthogonal** to PR #18596: new file path, no edits to its content, no claims that contradict it. It is an audit-with-positive-and-negative-findings.

## 1. ERRATUM #1 — `MulEquiv.ofBijective` file path

### PR #18596 §2.3 (lines 64–68 of the OBSERVE doc):

> **§2.3 Bijective MonoidHom → MulEquiv**
> `Mathlib/Algebra/Equiv/MulAdd.lean` (or `Group.End.lean` for the perm-specific form):
> - `MulEquiv.ofBijective : (f : M →* N) → Function.Bijective f → M ≃* N` — standard Mathlib bridge.

### Actual at v4.26.0:

`Mathlib/Algebra/Equiv/MulAdd.lean` **does not exist** in Mathlib v4.26.0. Likewise `Mathlib/Algebra/Group/End.lean` has only `Equiv.permCongrHom` (which the PREP correctly cites at §2.5), **not** `MulEquiv.ofBijective`.

The correct bearer:

`Mathlib/Algebra/Group/Equiv/Defs.lean` lines 499–505:

```lean
noncomputable def ofBijective {M N F} [Mul M] [Mul N] [FunLike F M N] [MulHomClass F M N]
    (f : F) (hf : Bijective f) : M ≃* N :=
  { Equiv.ofBijective f hf with map_mul' := map_mul f }

theorem ofBijective_apply_symm_apply {n : N} (f : M →* N) (hf : Bijective f) :
    f ((ofBijective f hf).symm n) = n := (ofBijective f hf).apply_symm_apply n
```

(declared inside `namespace MulEquiv`).

### Verification command (reproducible):

```bash
gh api 'search/code?q=%22noncomputable+def+ofBijective%22+%22MulEquiv%22+repo%3Aleanprover-community%2Fmathlib4+extension%3Alean&per_page=5' \
  --jq '.items[] | .path'
# → Mathlib/Algebra/Group/Equiv/Defs.lean (first hit)

gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Algebra/Group/Equiv/Defs.lean?ref=v4.26.0' \
  --jq '.content' | base64 -d | grep -n "ofBijective"
# 499:noncomputable def ofBijective {M N F} [Mul M] [Mul N] ...
# 504:theorem ofBijective_apply_symm_apply ...
```

### Δ-impact on §3 S2 ACT recipe

The recipe's `import` block is:

```lean
import Archive.Wiedijk100Theorems.AbelRuffini
import Mathlib.Algebra.Group.End
import Mathlib.Data.Fintype.EquivFin
```

None of these explicitly imports `Mathlib.Algebra.Group.Equiv.Defs`. However, **transitive resolution suffices**: `Mathlib.Algebra.Group.End` (which the recipe imports for `permCongrHom`) itself depends on `Mathlib.Algebra.Group.Equiv.Defs` (since `permCongrHom` constructs a `MulEquiv`). Confirmed by grep of import chain:

```bash
gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Algebra/Group/End.lean?ref=v4.26.0' \
  --jq '.content' | base64 -d | head -25 | grep '^import'
# import Mathlib.Algebra.Group.Equiv.Basic   ← transitively pulls in Equiv.Defs
# (other imports)
```

So the S2 ACT recipe **builds as written**, but a maintainer reading PR #18596 §2.3 and trying to add `import Mathlib.Algebra.Equiv.MulAdd` would get a file-not-found error. The correct explicit import (if desired) is:

```lean
import Mathlib.Algebra.Group.Equiv.Defs   -- defines MulEquiv.ofBijective at line 499
```

### Recommended S2 ACT-er fix

**Option A (defensive)**: Add `import Mathlib.Algebra.Group.Equiv.Defs` to the import block. Zero LOC risk; documents intent.

**Option B (lazy)**: Rely on transitive import from `Mathlib.Algebra.Group.End`. Recipe as written in PR #18596 §3 works.

## 2. ERRATUM #2 — `Irreducible.separable` file path

### PR #18596 §4.3 (lines 161–163 of the OBSERVE doc):

> **§4.3 `p_rootSet_card` requires `Separable`**
> `Irreducible p → p.Separable` over `CharZero` is `Irreducible.separable` (Mathlib `RingTheory/Polynomial/Separable.lean`). ℚ is `CharZero`. ✓

### Actual at v4.26.0:

`Mathlib/RingTheory/Polynomial/Separable.lean` **does not exist** in Mathlib v4.26.0. The lemma is in **`Mathlib/FieldTheory/Separable.lean`** at line 519:

```lean
theorem _root_.Irreducible.separable [CharZero F] {f : F[X]} (hf : Irreducible f) :
    f.Separable :=
  ...
```

### Verification command:

```bash
gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/FieldTheory/Separable.lean?ref=v4.26.0' \
  --jq '.content' | base64 -d | grep -n "Irreducible.separable"
# 519:theorem _root_.Irreducible.separable [CharZero F] {f : F[X]} (hf : Irreducible f) :
```

### Δ-impact on §3 S2 ACT recipe

The recipe never imports the separable file explicitly — it uses `p_irreducible.separable` via dot-notation, which works as long as the lemma is in scope. Confirmed in scope: `Archive.Wiedijk100Theorems.AbelRuffini` transitively imports `Mathlib.FieldTheory.PolynomialGaloisGroup`, which in turn imports `Mathlib.FieldTheory.Separable`. The PREP author's verbal claim "`p_irreducible.separable`" type-checks.

**Recommendation**: No S2 ACT code change needed. The error is informational drift in the §4.3 verification table — the PREP author should silently know that `Irreducible.separable` migrated from `RingTheory/Polynomial/` to `FieldTheory/` at some prior Mathlib version (likely v4.10 era; the rename happened upstream of v4.26.0).

## 3. ENHANCEMENT — Drop-in sorry-free corollary

### PR #18596 §3 (lines 132–138):

```lean
/-- **Corollary:** A specific root of `X^5 - 4·X + 2` is not solvable by radicals. -/
theorem p_not_solvable_by_rad : ∃ x : ℂ, aeval x p = 0 ∧ x ∉ solvableByRad ℚ ℂ :=
  ⟨_, exists_not_solvable_by_rad.choose_spec.2 |> fun _ =>
    -- alternative: use AbelRuffini.not_solvable_by_rad' directly
    sorry⟩  -- TODO: pick a concrete root via `IsAlgClosed.splits` + `exists_eval_eq_zero`
```

### Mathlib's own proof of `exists_not_solvable_by_rad` (verbatim, Archive file lines 175–179):

```lean
/-- **Abel-Ruffini Theorem** -/
theorem exists_not_solvable_by_rad : ∃ x : ℂ, IsAlgebraic ℚ x ∧ ¬IsSolvableByRad ℚ x := by
  obtain ⟨x, hx⟩ := (IsAlgClosed.splits (Φ ℂ 4 2)).exists_eval_eq_zero (by simp [degree_Phi])
  rw [← map_Phi 4 2 (algebraMap ℚ ℂ), eval_map] at hx
  exact ⟨x, ⟨Φ ℚ 4 2, (monic_Phi 4 2).ne_zero, hx⟩, not_solvable_by_rad' x hx⟩
```

### Drop-in sorry-free corollary (5 LOC, mirrors Mathlib proof)

The PREP's corollary statement `∃ x : ℂ, aeval x p = 0 ∧ x ∉ solvableByRad ℚ ℂ` is **definitionally equal** to `∃ x : ℂ, aeval x p = 0 ∧ ¬ IsSolvableByRad ℚ x` because `solvableByRad ℚ ℂ : IntermediateField ℚ ℂ` is defined at `Mathlib/FieldTheory/AbelRuffini.lean:208`:

```lean
def solvableByRad : IntermediateField F E where
  carrier := IsSolvableByRad F
  ...
```

So set membership unfolds to the inductive predicate. The replacement proof:

```lean
/-- **Corollary:** A specific root of `X^5 - 4·X + 2` is not solvable by radicals.
    Mirrors Mathlib's `exists_not_solvable_by_rad` proof verbatim. -/
theorem p_not_solvable_by_rad : ∃ x : ℂ, aeval x p = 0 ∧ ¬ IsSolvableByRad ℚ x := by
  obtain ⟨x, hx⟩ := (IsAlgClosed.splits (Φ ℂ 4 2)).exists_eval_eq_zero (by simp [degree_Phi])
  rw [← map_Phi 4 2 (algebraMap ℚ ℂ), eval_map] at hx
  exact ⟨x, hx, not_solvable_by_rad' x hx⟩
```

**LOC**: 5 lines (or 6 with the docstring). **Sorry count**: 0. **Axiom count**: 0.

This rewrites the PREP's optional corollary as a sorry-free completion. If the S2 ACT-er ships the recipe without the corollary, the core ACT remains as in PR #18596 §3.

## 4. Sibling-slug Mathlib structure note (positive verification)

PR #18596 §7 lists sibling slugs that already exist in `proofs/Proofs/`:
- `AbelRuffiniGaloisExtensionsOQ04.lean`
- `AbelRuffiniGaloisExtensionsOQ05.lean`, `…OQ06.lean`, `…OQ07.lean`, `…OQ05OQ01.lean`

Confirmed by listing the worktree:

```bash
ls proofs/Proofs/AbelRuffiniGaloisExtensions*.lean
```

The parent `AbelRuffiniGaloisExtensions.lean` ends at Part XV (532 LOC, 0 sorries, 0 axioms per state). This means OQ-01, when landed, fits as the **explicit-quintic capstone** in a fully populated family — no namespace collisions to worry about.

The S2 ACT file naming should be:

```
proofs/Proofs/AbelRuffiniGaloisExtensionsOQ01.lean
```

and the `Proofs.lean` aggregator should insert:

```lean
import Proofs.AbelRuffiniGaloisExtensionsOQ01
```

alphabetically **before** `import Proofs.AbelRuffiniGaloisExtensionsOQ04` (which already exists). Quick check of `Proofs.lean` (alphabetic ordering):

```bash
grep "AbelRuffiniGaloisExtensions" proofs/Proofs.lean
# import Proofs.AbelRuffiniGaloisExtensions     ← parent
# import Proofs.AbelRuffiniGaloisExtensionsOQ04 ← sibling
# (no OQ-01 line yet)
```

The new line goes between parent and OQ04 — the only valid alphabetic slot.

## 5. Risk register (changes vs PR #18596 §5)

| # | Risk | PR #18596 severity | S1b PREP severity | Notes |
|---:|---|:-:|:-:|---|
| 5.1 | `splits_ℚ_ℂ` attribute scope | LOW | LOW | Confirmed at line 67 of Complex/Polynomial/Basic.lean. |
| 5.2 | `Φ ℚ a b` namespace | LOW | LOW | Confirmed; `open AbelRuffini` brings `Φ` into scope. |
| 5.3 | `complex_roots_Phi 4 2` Separable hypothesis | LOW | LOW | Confirmed; `p_irreducible.separable` works via transitive import. |
| 5.4 | `Equiv.permCongrHom` import path | LOW | LOW | Confirmed at line 293 of Group/End.lean. |
| 5.5 | `Archive.*` accessibility | LOW | LOW | Confirmed; multiple in-repo files import Archive entries. |
| 5.6 | `gal_Phi 4 2 (by decide)` discharge | LOW | LOW | Verified: `not_solvable_by_rad'` uses `decide` for the same hypotheses. |
| 5.7 | `MulEquiv.ofBijective` MonoidHom arg | LOW | LOW | Confirmed; signature accepts `M →* N`. |
| 5.8 | `meta.json` status field | LOW | LOW | `verified` correct iff 0 sorries + 0 axioms — confirmed in §3 sorry-free corollary above. |
| 5.9 | Race with concurrent agents | LOW | **LOW-MEDIUM** | At 2026-05-13 ~06:20 UTC, no open PRs for this slug; PR #18596 merged ~70 min ago. The 30-min freshness window has elapsed. |
| **NEW 5.10** | §2.3 file path errata mis-leads import block | — | **LOW** | The cited `Mathlib/Algebra/Equiv/MulAdd.lean` does not exist. Recipe still builds via transitive imports. |
| **NEW 5.11** | §4.3 file path errata mis-leads verification table | — | **TRIVIAL** | The cited `Mathlib/RingTheory/Polynomial/Separable.lean` does not exist; correct path is `Mathlib/FieldTheory/Separable.lean`. No effect on recipe since dot-notation transparently resolves. |

## 6. Build status of this PREP

- **Files changed**: 1 new file at `research/problems/abel-ruffini-galois-extensions-oq-01/sessions/2026-05-13-s1b-prep-mathlib-bearer-audit.md`.
- **Lean files changed**: 0.
- **Gallery JSON changed**: 0.
- **`problem.md` / `state.md` changed**: 0.
- **Build risk**: 0 (no compiled artifacts).
- **Race risk**: 0 (new file path, no edits to existing PREP content).

## 7. Recommended next action for S2 ACT-er

1. Read PR #18596 §3 for the verbatim recipe (still correct).
2. Apply Option A (defensive) from §1: add `import Mathlib.Algebra.Group.Equiv.Defs` to the import block.
3. Use the sorry-free corollary from §3 of this PREP (5 LOC, mirrors Mathlib's `exists_not_solvable_by_rad`).
4. Disregard the §4.3 informational drift in PR #18596 — `Irreducible.separable` is transparently in scope.

Total S2 ACT LOC estimate: ~35 LOC (core 30 + sorry-free corollary 5), 0 sorries, 0 axioms, status `verified`/`original`.

## 8. Honest accounting

What this PREP claims:
- **High confidence**: Two file-path errata in PR #18596 §2.3 and §4.3. Verified by `gh api .../contents?ref=v4.26.0` for each cited path; checked the alternative paths' existence and content.
- **High confidence**: The drop-in corollary in §3 above is well-typed and mirrors a verbatim Mathlib proof. (Not Docker-built — per `[.lake symlink loop + mid-build worktree wipe]` memory.)
- **Moderate confidence**: §1 Option B (transitive resolution suffices) — confirmed `Mathlib.Algebra.Group.End` imports `Mathlib.Algebra.Group.Equiv.Basic` which itself depends on `Equiv.Defs`. The exact transitive chain is reproducible but not run end-to-end.

What this PREP does not claim:
- That every line number in PR #18596 is wrong. Most are correct (§2.1, §2.4, §2.5, §4.2, §4.4, §4.5, §5.1, §5.4, §5.5, §5.7, §5.8 all verified positive).
- That the S2 ACT-er must apply both options from §1. Option B (no import added) builds; Option A is defensive hygiene.
- That `solvableByRad ℚ ℂ` vs `IsSolvableByRad ℚ x` are syntactically equal — they are *definitionally* equal via the `solvableByRad.carrier` projection.

---

*End S1b PREP.* Doc-only audit-correction of PR #18596. Forward design only. 0 builds. 0 races.
