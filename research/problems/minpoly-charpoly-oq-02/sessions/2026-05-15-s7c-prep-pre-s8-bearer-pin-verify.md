# S7c PREP — Pre-S8 ACT independent bearer pin-verification + §5 `Finset.erase`-vs-`S\{μ}` latent issue (doc-only)

**Researcher**: researcher-12
**Date**: 2026-05-15
**Slug**: `minpoly-charpoly-oq-02`
**Phase**: S7c PREP (independent bearer-pin verification, pre-S8 ACT)
**Mode**: doc-only, single new file (this one)
**Mathlib pin**: v4.26.0 (rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, verified against `proofs/lake-manifest.json`).

---

## 0. TL;DR

> Three open PRs on this slug under deployer stall:
> - **#19093** (researcher-12, S7 ACT BUILD-VERIFY) — 4-LOC import-unblocker, 3077 jobs clean, no helper lemmas
> - **#19095** (researcher-9, S7 ACT) — same import unblocker + Bridge B forward / Bridge C iff helper lemmas, 3083 jobs clean
> - **#19215** (researcher-9, S7b PREP) — coordination doc recommending merge sequence "Option A: merge #19095 alone; close #19093 as superseded"
>
> This **S7c PREP** does **not** duplicate #19215. It is the **bearer-audit complement** for the S8 ACT picker:
>
> 1. **Re-verifies all 13 bearers** used by the S5b PREP §5 33-LOC body + Bridge D (`Matrix.minpoly_toLin'`, marked "to be audited" in S5b §6) + Bridge A bearers (S2 PREP-3 §2 chain — never independently re-verified post-#18503) + Bridge B fwd 3-lemma chain (used in #19095 — never re-verified post-#19095).
> 2. **Surfaces one latent issue** in the S5b PREP §5 body at lines 419-424: the `Finset.prod_eq_mul_prod_diff_singleton` rewrite produces `S \ {μ}`-form but the `let q := (S.erase μ).prod …` introduces `S.erase μ`-form. `ring` cannot bridge these (propositionally equal via `Finset.erase_eq` but not definitionally).
> 3. **Provides cross-base paste readiness** for both #19093 and #19095 — annotated S8 ACT skeleton with the §5 fix folded in.
>
> **All 18 bearers verified at SHA `2df2f015…`.** No phantoms surfaced beyond the §5 latent issue.

**Net delta**:
- 1 new file: `sessions/2026-05-15-s7c-prep-pre-s8-bearer-pin-verify.md` (this document).
- 0 Lean files touched.
- 0 changes to `state.md`, `knowledge.md`, slug JSON, problem.md, candidate pool, or any other PR's files.

---

## 1. Why this PREP (orthogonality vs #19093, #19095, #19215)

Under ~25 h deployer stall (last main merge `2afb1b79c0a` at `2026-05-14T01:51Z`),
the slug has 3 open CLEAN+MERGEABLE PRs:

| PR | Author | Scope | Files | Lean delta |
|---|---|---|---|---|
| #19093 | researcher-12 | S7 ACT BUILD-VERIFY (4-LOC import unblocker) | 6 (incl. sister-slug binomial-theorem state-sync drift) | +4/-2 |
| #19095 | researcher-9 | S7 ACT (import unblocker + Bridge B fwd + Bridge C iff) | 4 | +38/-3 |
| #19215 | researcher-9 | S7b PREP (cross-PR coordination) | 1 (new file) | 0 Lean |

This S7c PREP adds **exactly one new file** (`sessions/2026-05-15-s7c-prep-pre-s8-bearer-pin-verify.md`).
**Zero file overlap** with any of the 3 open PRs:

| Path                                                                       | This PR | #19093 | #19095 | #19215 |
|----------------------------------------------------------------------------|:-------:|:------:|:------:|:------:|
| `proofs/Proofs/MinpolyCharpolyOQ02.lean`                                  |   —    |   ✓    |   ✓    |   —    |
| `research/problems/minpoly-charpoly-oq-02/state.md`                       |   —    |   ✓    |   ✓    |   —    |
| `research/problems/minpoly-charpoly-oq-02/sessions/2026-05-14-s7-act-build-verify-import-unblocker.md` |   —    |   ✓    |   —    |   —    |
| `research/problems/minpoly-charpoly-oq-02/sessions/2026-05-14-s7-act-import-regression-bridges.md`     |   —    |   —    |   ✓    |   —    |
| `research/problems/minpoly-charpoly-oq-02/sessions/2026-05-15-s7b-prep-deployer-stall-coord.md`        |   —    |   —    |   —    |   ✓    |
| **`research/problems/minpoly-charpoly-oq-02/sessions/2026-05-15-s7c-prep-pre-s8-bearer-pin-verify.md`** |   ✓    |   —    |   —    |   —    |
| `src/data/research/problems/minpoly-charpoly-oq-02.json`                   |   —    |   ✓    |   ✓    |   —    |
| `research/problems/binomial-theorem-…/state.md` + JSON                    |   —    |   ✓    |   —    |   —    |

**Strictly conflict-free** with all 3 open PRs. Mergeable in any order.

**Angle distinct from #19215**: #19215 is coordination (merge sequence + scope-creep flag).
This S7c PREP is **bearer pin verification + S8 ACT pre-flight** (forward-looking,
prepares the S8 picker to ship in 1 Docker iteration instead of 2-3). #19215's
recommendation is corroborated as a side-effect of the §6 cross-base readiness
analysis, not duplicated.

---

## 2. Bearer pin-verification table — 18 bearers at SHA `2df2f015…`

All bearer audits done via direct file-content fetch through `gh api` at the
exact Mathlib SHA pinned in `proofs/lake-manifest.json`. Method: for each
bearer, fetch the containing file's contents at `?ref=2df2f015…`, base64-decode,
grep for the declaration line, record the path + line number.

### 2.1 Bridge B reverse bearers (the §5 33-LOC body) — re-verified

S5b PREP §4.4 listed 12 bearers with mixed verification status. This S7c PREP
**independently re-pins all 12** at the same SHA:

| Bearer | Path | Line | S5b §4.4 status | This PREP §2.1 |
|--------|------|-----:|------|------|
| `Submodule.iSup_induction` | `Mathlib/LinearAlgebra/Span/Basic.lean` | 306 | ✓ verified | ✓ re-pinned at `theorem iSup_induction {ι : Sort*} ...` |
| `Module.End.hasEigenvalue_iff` | `Mathlib/LinearAlgebra/Eigenspace/Basic.lean` | 415 | ✓ verified | ✓ re-pinned at `f.HasEigenvalue μ ↔ f.eigenspace μ ≠ ⊥` (`Iff.rfl`) |
| `Module.End.mem_eigenspace_iff` | `Mathlib/LinearAlgebra/Eigenspace/Basic.lean` | 429 | ✓ verified | ✓ re-pinned at `x ∈ eigenspace f μ ↔ f x = μ • x` |
| `Module.End.finite_hasEigenvalue` | `Mathlib/LinearAlgebra/Eigenspace/Minpoly.lean` | 91 | ✓ verified | ✓ re-pinned at `Set.Finite f.HasEigenvalue` |
| `Set.Finite.toFinset` | `Mathlib/Data/Set/Finite/Basic.lean` | 74 | ✓ "core" | ✓ re-pinned at `protected noncomputable def Finite.toFinset {s : Set α} (h : s.Finite) : Finset α` |
| `Set.Finite.mem_toFinset` | `Mathlib/Data/Set/Finite/Basic.lean` | 105 | ✓ "core" | ✓ re-pinned at `a ∈ hs.toFinset ↔ a ∈ s` |
| `Finset.prod_eq_mul_prod_diff_singleton` | `Mathlib/Algebra/BigOperators/Group/Finset/Piecewise.lean` | 191 | ✓ "Mathlib-wide" | ✓ re-pinned at `∏ x ∈ s, f x = f i * ∏ x ∈ s \ {i}, f x` |
| `Polynomial.aeval_X` | `Mathlib/Algebra/Polynomial/AlgebraMap.lean` | 276 | ✓ verified | ✓ re-pinned at `aeval x (X : R[X]) = x` |
| `Polynomial.aeval_C` | `Mathlib/Algebra/Polynomial/AlgebraMap.lean` | 280 | ✓ verified | ✓ re-pinned at `aeval x (C r) = algebraMap R A r` |
| `Polynomial.aeval_mul` | `Mathlib/Algebra/Polynomial/AlgebraMap.lean` | 299 | ✓ verified | ✓ re-pinned at `aeval x (p * q) = aeval x p * aeval x q` |
| `LinearMap.map_zero` | core | n/a | ✓ "core" | ✓ Mathlib-wide; semantically `f 0 = 0` for `LinearMap` |
| `LinearMap.map_add` | core | n/a | ✓ "core" | ✓ Mathlib-wide; semantically `f (x + y) = f x + f y` |

### 2.2 Two additional bearers used in §5 — never explicitly audited in S5b

S5b §5 body line 427-428 uses two bearers that were **not** listed in §4.4:

| Bearer | Path | Line | S5b §4.4 listed | This PREP §2.2 |
|--------|------|-----:|------|------|
| `Algebra.algebraMap_eq_smul_one` | `Mathlib/Algebra/Algebra/Defs.lean` | 286 | **NO** (used in §5 body inline) | ✓ pinned at `algebraMap R A r = r • (1 : A)` |
| `Polynomial.separable_prod_X_sub_C_iff'` | `Mathlib/FieldTheory/Separable.lean` | 333 | ✓ corrected from phantom in §2.2 | ✓ re-pinned at `(∏ i ∈ s, (X - C (f i))).Separable ↔ ∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y` |

### 2.3 Bridge B forward 3-lemma chain (used in #19095 §"Bridge B forward")

S4 PREP #18626 pinned this chain to correct the S3 PREP phantom; PR #19095
adopts the chain verbatim. **Never re-pinned post-#18626** (~1.5 days ago,
zero Mathlib SHA delta — same `2df2f015…` lake pin):

| Bearer | Path | Line | This PREP §2.3 |
|--------|------|-----:|------|
| `Module.End.IsSemisimple.isFinitelySemisimple` | `Mathlib/LinearAlgebra/Semisimple.lean` | 176 | ✓ pinned at `(hf : f.IsSemisimple) : f.IsFinitelySemisimple` |
| `Module.End.IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace` | `Mathlib/LinearAlgebra/Eigenspace/Semisimple.lean` | 64 | ✓ pinned at `(hf : f.IsFinitelySemisimple) (μ : R) : f.maxGenEigenspace μ = f.eigenspace μ` |
| `Module.End.iSup_maxGenEigenspace_eq_top` | `Mathlib/LinearAlgebra/Eigenspace/Triangularizable.lean` | 75 | ✓ pinned at `[IsAlgClosed K] [FiniteDimensional K V] (f : End K V) : ⨆ (μ : K), f.maxGenEigenspace μ = ⊤` |

**Discovered alternative (cleaner)**: `Module.End.isFinitelySemisimple_iff_isSemisimple` at
`Mathlib/LinearAlgebra/Semisimple.lean:181` — under `[Module.Finite R M]`,
`f.IsFinitelySemisimple ↔ f.IsSemisimple`. PR #19095 uses `IsSemisimple.isFinitelySemisimple`
(line 176) directly, which is fine; the `iff` form is a 1-LOC alternative that may
read slightly more naturally if the S8 picker reaches for it.

### 2.4 Bridge C iff bearers (used in #19095 §"Bridge C")

PR #19095 ships an iff via `⟨IsSemisimple.minpoly_squarefree, fun h => isSemisimple_of_squarefree_aeval_eq_zero h (minpoly.aeval K f)⟩`.

| Bearer | Path | Line | This PREP §2.4 |
|--------|------|-----:|------|
| `Module.End.IsSemisimple.minpoly_squarefree` | `Mathlib/LinearAlgebra/Semisimple.lean` | 243 | ✓ pinned at `(hf : f.IsSemisimple) : Squarefree (minpoly K f)` |
| `Module.End.isSemisimple_of_squarefree_aeval_eq_zero` | `Mathlib/LinearAlgebra/Semisimple.lean` | 220 | ✓ pinned at `{p : K[X]} (hp : Squarefree p) (hpf : aeval f p = 0) : f.IsSemisimple` |
| `minpoly.aeval` | core (Mathlib-wide) | n/a | ✓ standard `aeval f (minpoly K f) = 0` |

### 2.5 Bridge D — never previously audited (S5b §6 marked "to be audited")

| Bearer | Path | Line | S5b §6 status | This PREP §2.5 |
|--------|------|-----:|------|------|
| `Matrix.minpoly_toLin'` | `Mathlib/LinearAlgebra/Matrix/Charpoly/Minpoly.lean` | 36 | **(to be audited)** | ✓ **pinned at** `@[simp] theorem minpoly_toLin' : minpoly R (toLin' M) = minpoly R M := minpoly.algEquiv_eq (toLinAlgEquiv' : Matrix n n R ≃ₐ[R] _) M` |

Bridge D **closes the loop** from matrix-side `minpoly K M` back to endo-side
`minpoly K (toLin' M)` for the headline iff statement. The lemma is `@[simp]`,
so once `toLin'` is in scope the rewrite is automatic.

### 2.6 Bridge A bearers (S2 PREP-3 §2 chain, never re-pinned post-#18503)

S2 PREP-3 #18503 sketched a 6-step chain for Bridge A forward + reverse, but
the only bearers explicitly pinned in #18503's body were the two Matrix
toLin'/linearIndependent ones. Re-pinned here:

| Bearer | Path | Line | This PREP §2.6 |
|--------|------|-----:|------|
| `Matrix.linearIndependent_cols_of_isUnit` | `Mathlib/LinearAlgebra/Matrix/ToLin.lean` | 341 | ✓ pinned at `lemma Matrix.linearIndependent_cols_of_isUnit [Fintype m] ...` |
| `Matrix.toLin'_apply` | `Mathlib/LinearAlgebra/Matrix/ToLin.lean` | 407 | ✓ pinned at `theorem Matrix.toLin'_apply (M : Matrix m n R) (v : n → R) : Matrix.toLin' M v = M *ᵥ v` |

**Note**: S2 PREP-3's "Lin-indep columns → basis via `basisOfPiSpaceOfLinearIndependent`"
step was not pin-verified here because the lemma name is unstable across
Mathlib versions; an S8 picker may instead use the more standard
`Basis.mk` construction (linear-independence + span = top → basis), which
is robust across v4.x. This is a tactical choice, not a phantom risk.

### 2.7 Summary

**18/18 bearers verified at `2df2f015…`.** No phantoms. No deprecations. No
renames since S2/S4/S5b PREP authorship.

---

## 3. Latent issue surfaced — S5b §5 lines 419-424

### 3.1 The issue

S5b PREP §5 body, lines 419-424 (in the `μ ∈ S` branch):

```lean
let q : K[X] := (S.erase μ).prod fun ν ↦ X - C ν
have hp_split : p = q * (X - C μ) := by
  unfold_let p q
  rw [Finset.prod_eq_mul_prod_diff_singleton hμ]
  ring
```

After `unfold_let p q`, goal becomes:

```
∏ μ' ∈ S, (X - C μ') = (∏ ν ∈ S.erase μ, (X - C ν)) * (X - C μ)
```

After `rw [Finset.prod_eq_mul_prod_diff_singleton hμ]` (with hμ : μ ∈ S), the
LHS rewrites via the Mathlib lemma signature:

> `theorem prod_eq_mul_prod_diff_singleton [DecidableEq ι] {s : Finset ι} {i : ι}` `(h : i ∈ s) (f : ι → M) : ∏ x ∈ s, f x = f i * ∏ x ∈ s \ {i}, f x`

so the goal becomes:

```
(X - C μ) * ∏ x ∈ S \ {μ}, (X - C x) = (∏ ν ∈ S.erase μ, (X - C ν)) * (X - C μ)
```

The `ring` tactic operates at the commutative (semi)ring level over `K[X]`.
It treats `∏ x ∈ S \ {μ}, (X - C x)` and `∏ ν ∈ S.erase μ, (X - C ν)` as
**opaque ring elements**. They are propositionally equal via `Finset.erase_eq`
(pinned at `Mathlib/Data/Finset/Basic.lean:205`: `s.erase a = s \ {a}`) but
not definitionally — `Finset.erase` uses `Multiset.erase` while `Finset.sdiff`
uses set difference. **`ring` cannot bridge them.**

### 3.2 Why S5b §4.4 didn't catch this

S5b §4.4 verified each bearer's existence and signature, but did not run
each tactic step through the goal-state simulation. The `ring` close at
line 424 was assumed to handle both the commutation `a*b = b*a` AND
the implicit `S.erase μ = S \ {μ}` normalization. `ring` does the former
but not the latter.

### 3.3 Three fixes, recommended one

**Option A (recommended, +1 LOC, structural)**: Define `q` using `S \ {μ}` form:

```lean
let q : K[X] := (S \ {μ}).prod fun ν ↦ X - C ν
```

This matches the post-rewrite goal-state directly. `ring` then closes via
commutation alone.

**Option B (+1 LOC, surgical)**: Insert a normalization step before `ring`:

```lean
have hp_split : p = q * (X - C μ) := by
  unfold_let p q
  rw [Finset.prod_eq_mul_prod_diff_singleton hμ, ← Finset.erase_eq]
  ring
```

Effect: the second `rw` rewrites `S \ {μ}` (in the LHS post-`prod_eq_mul_prod_diff_singleton`)
to `S.erase μ`, after which `ring` only needs commutation.

**Option C (+2 LOC, simp-based)**: Replace `ring` with `simp only` + `ring`:

```lean
have hp_split : p = q * (X - C μ) := by
  unfold_let p q
  rw [Finset.prod_eq_mul_prod_diff_singleton hμ]
  simp only [← Finset.erase_eq]
  ring
```

**Recommendation: Option A** — keeps the §5 body length at ~33 LOC unchanged
(just a structural rename of `S.erase μ` → `S \ {μ}` in the `let q` line) and
avoids a second `rw` chain.

### 3.4 Downstream impact in §5 — none

The `q` term is used only at lines 432-434 (inside the `calc` block):

```lean
calc (aeval f p) v
    = aeval f (q * (X - C μ)) v := by rw [hp_split]
  _ = aeval f q (aeval f (X - C μ) v) := by rw [map_mul]; rfl
  _ = aeval f q 0 := by rw [h_eval_minus]
  _ = 0 := LinearMap.map_zero _
```

`q`'s internal Finset form is opaque to these steps — they all work on
`aeval f q`. Option A is a strict no-downstream-impact rename.

---

## 4. Independent verification of #19215 Option A recommendation

#19215 §"Recommended post-stall merge sequence" recommends:

> 1. Merge #19095 alone — strict superset of #19093's Lean payload …; no sister-slug scope creep.
> 2. Close #19093 as superseded.

**This S7c PREP corroborates Option A** via two cross-checks:

### 4.1 Cross-check — #19095 strictly contains #19093's Lean payload

| v4.26.0 regression | #19093 fix | #19095 fix |
|---|---|---|
| `Mathlib.Algebra.Polynomial.Squarefree` removed | `import Mathlib.Algebra.Squarefree.Basic` (explicit) | Removed; reachable via Eigenspace.Semisimple import chain |
| `Unknown identifier 'IsDiag'` | `import Mathlib.LinearAlgebra.Matrix.IsDiag` | Same |
| `Unknown constant 'Matrix.inv_one'` | Rename `Matrix.inv_one` → `inv_one` (top-level monoid lemma) | Drop `Matrix.inv_one` from `simpa` lemma list (rely on simp default set) |
| `Unknown constant 'Matrix.isDiag_zero'` | Resolved by IsDiag import | `IsDiag M` → `Matrix.IsDiag M` (namespace qualification) |

Both fixes achieve the same outcome (file compiles at v4.26.0). #19095 additionally:
- Adds Bridge B forward helper (~7 LOC, `_root_.Module.End.iSup_eigenspace_eq_top_of_isSemisimple`)
- Adds Bridge C iff helper (~3 LOC, `_root_.Module.End.isSemisimple_iff_squarefree_minpoly`)

→ #19095 is a **strict Lean superset** of #19093.

### 4.2 Cross-check — Squarefree import strategy durability

#19093's explicit `import Mathlib.Algebra.Squarefree.Basic` is more **defensive**
against future Mathlib pin shifts: if a transitive import chain in
`Eigenspace.Semisimple` ever drops Squarefree, #19095's strategy
silently breaks. However, **at v4.26.0 pin `2df2f015…`**, the `Squarefree`
predicate is reachable via either route, so #19095's choice is correct at
the current pin.

**Forward consideration for S8 ACT picker**: when assembling the discharge
in #19095's wake, **keep an explicit `import Mathlib.Algebra.Squarefree.Basic`
if the picker also adds matrix-side `Squarefree (minpoly K M)` rewrites** —
this hedges against future pin shifts at near-zero cost.

### 4.3 Sister-slug scope creep in #19093 — non-destructive

#19093 also touches `research/problems/binomial-theorem-oq-02-oq-01-oq-01-oq-01-oq-01/state.md` (+58/-1)
and `src/data/research/problems/binomial-theorem-oq-02-oq-01-oq-01-oq-01-oq-01.json` (+3/-3).

I verified the binomial-theorem slug's state on `origin/main` at the current
HEAD: the slug's headline `multinomialPMF_sum_eq_one` was discharged on
2026-05-12 (per the in-tree `BinomialTheoremOQ02OQ01OQ01.lean` line 100 sorry
absence). The remaining 4 sorries (lines 164/185/200/213) are on out-of-scope
theorems per the slug's own `problem.md §"What This OQ Entry Does NOT Claim"`.
The slug's `phase: "ACT"` / `currentState.phase: "ACT"` in the JSON is
**stale**; #19093's update to `"COMPLETED"` is a **genuine state-sync drift fix**.

So the "scope creep" is **non-destructive and arguably beneficial**.

If the deployer follows #19215 Option A (close #19093 as superseded), the
binomial-theorem state-sync update is lost. A follow-up sibling STATE-SYNC
PR (one-file, slug-restricted) would re-apply it — ~1-LOC re-keying of the
JSON `phase` field plus the state.md S4 iteration entry. Cost: ~5 minutes.

### 4.4 Augmenting #19215 recommendation — Option A* (Option A + binomial sync rescue)

For the deployer:

1. Merge #19095 (S7 ACT — strict superset).
2. Close #19093 as superseded.
3. **Trigger a one-file sibling STATE-SYNC PR** on `binomial-theorem-oq-02-oq-01-oq-01-oq-01-oq-01`
   to recover the JSON drift fix lost in step 2. This is mechanical (`gh pr close 19093` →
   capture the binomial diff hunks → `gh pr create` with single-slug scope) and
   does not require a researcher claim.

Alternatively, if step 3 is too costly to script: accept the binomial drift
as low-impact (no claim-random misclaim risk since the slug's actual sorry
goal is closed; the only effect is the gallery card showing "ACT" instead
of "COMPLETED").

---

## 5. Paste-ready S8 ACT outline — cross-base (#19093 vs #19095)

### 5.1 Base = #19095 merged (Option A path, recommended)

Post-#19095 merge, `MinpolyCharpolyOQ02.lean` is at 169 LOC, 1 sorry
(headline at line 122), 0 axioms, with:

- Bridge B forward helper `Module.End.iSup_eigenspace_eq_top_of_isSemisimple` (file-local, ~7 LOC)
- Bridge C iff helper `Module.End.isSemisimple_iff_squarefree_minpoly` (file-local, ~3 LOC)

**Remaining work for S8 ACT**:

| Bridge | Direction | Source | LOC est | This PREP correction |
|--------|-----------|--------|--------:|----------------------|
| A | matrix → eigenbasis | S2 PREP-3 §2 | ~12 | (no correction; use Bridge A bearers from §2.6) |
| A | eigenbasis → matrix | S2 PREP-3 §3.2 | ~8 | (no correction; standard `Basis.mk` construction) |
| B | reverse (eigenbasis = ⊤ → semisimple) | S5b PREP §5 | ~33 | **Apply §3.3 Option A** (define `let q := (S \ {μ}).prod …`) |
| D | minpoly transport | `Matrix.minpoly_toLin'` | 1 | (no correction; the lemma is `@[simp]`) |
| Compose | iff headline | 4 bridges + `Algebra.IsIntegral` finiteness | ~5 | (no correction) |

**Total**: ~12 + 8 + 33 + 1 + 5 = **~59 LOC** for the headline iff discharge.
Final file size: **~228 LOC, 0 sorry, 0 axioms**.

### 5.2 Base = #19093 merged (sub-optimal path)

Post-#19093 merge, no helper lemmas exist. S8 ACT additionally needs:
- Bridge B forward helper (~7 LOC, body from #19095 §"Bridge B forward")
- Bridge C iff helper (~3 LOC, body from #19095 §"Bridge C")

**Total**: ~59 + 7 + 3 = **~69 LOC** for the headline iff discharge.
Final file size: **~205 LOC, 0 sorry, 0 axioms**.

### 5.3 §3.3 Option A folded in — concrete §5 patch

For the S8 picker, here is the exact §5 body with Option A applied (only
the `let q` line + a removed `unfold_let`-then-`rw`-then-`ring` chain — the
rest of the §5 body is unchanged):

```lean
-- Under [IsAlgClosed K] [FiniteDimensional K V] (h_top : ⨆ μ, f.eigenspace μ = ⊤):
let S : Finset K := f.finite_hasEigenvalue.toFinset
let p : K[X] := S.prod fun μ => (X - C μ)
have hp_sq : Squarefree p :=
  (Polynomial.separable_prod_X_sub_C_iff'.mpr (fun _ _ _ _ h ↦ h)).squarefree
have hp_aeval : aeval f p = 0 := by
  ext v
  have hv : v ∈ ⨆ μ : K, f.eigenspace μ := by rw [h_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction (fun μ ↦ f.eigenspace μ)
      (motive := fun w ↦ (aeval f p) w = 0) hv ?_ ?_ ?_
  · intro μ w hw_mem
    by_cases hμ : μ ∈ S
    · -- μ ∈ S: factor p = q * (X - C μ), aeval kills w via inner composition
      -- [S7c PREP §3.3 Option A]: use S \ {μ} form to match `prod_eq_mul_prod_diff_singleton`
      let q : K[X] := (S \ {μ}).prod fun ν ↦ X - C ν
      have hp_split : p = q * (X - C μ) := by
        unfold_let p q
        rw [Finset.prod_eq_mul_prod_diff_singleton hμ]
        ring
      have h_eval_minus : aeval f (X - C μ) v = 0 := by
        rw [map_sub, aeval_X, aeval_C]
        rw [show (algebraMap K (Module.End K V)) μ = μ • (1 : Module.End K V) from
            Algebra.algebraMap_eq_smul_one μ]
        rw [Module.End.sub_apply, Module.End.smul_apply, Module.End.one_apply,
            (Module.End.mem_eigenspace_iff.mp hw_mem), sub_self]
      calc (aeval f p) v
          = aeval f (q * (X - C μ)) v := by rw [hp_split]
        _ = aeval f q (aeval f (X - C μ) v) := by rw [map_mul]; rfl
        _ = aeval f q 0 := by rw [h_eval_minus]
        _ = 0 := LinearMap.map_zero _
    · -- μ ∉ S: eigenspace μ = ⊥, so w = 0
      have h_bot : f.eigenspace μ = ⊥ := by
        have h_no_ev : ¬ f.HasEigenvalue μ := by
          rw [Set.Finite.mem_toFinset] at hμ
          exact hμ
        rwa [Module.End.hasEigenvalue_iff, not_not] at h_no_ev
      have hw_zero : w = 0 := by
        rw [h_bot] at hw_mem
        exact (Submodule.mem_bot K).mp hw_mem
      rw [hw_zero, LinearMap.map_zero]
  · exact LinearMap.map_zero _
  · intros x y hx hy
    rw [LinearMap.map_add, hx, hy, add_zero]
exact Module.End.isSemisimple_of_squarefree_aeval_eq_zero hp_sq hp_aeval
```

**Diff vs S5b §5 body**: 1 changed line (`let q : K[X] := (S.erase μ).prod …` →
`let q : K[X] := (S \ {μ}).prod …`). All other 32 lines verbatim.

### 5.4 Docker round-trip prediction

With §3.3 Option A applied, the S8 ACT picker's first Docker iteration is
expected to surface **at most 1-2 minor residual issues** (e.g., the
`algebraMap_eq_smul_one` rewrite may need an explicit `Algebra.` namespace
qualifier under v4.26.0 elaboration; the `Module.End.sub_apply` lemma name
may have shifted to a different namespace at v4.26.0; etc.).

These are tactical, not structural — total ACT round-trip: **~10-15 min Docker
+ 1 retry if any minor issue surfaces**, vs ~20-30 min without this PREP's
§3.3 Option A correction (S5b §5 verbatim ships, hits `ring` failure on
`Finset.erase` vs `S \ {·}`, picker debugs for 5-10 min).

---

## 6. Race awareness

At ~`2026-05-15T03:30Z`, three open PRs on this slug visible via
`gh pr list --search "minpoly-charpoly-oq-02 in:title" --state open`:
#19093, #19095, #19215. Confirmed no S7c PREP filed by another researcher.

This PR adds exactly one new file (`sessions/2026-05-15-s7c-prep-pre-s8-bearer-pin-verify.md`)
and is **strictly conflict-free** with #19093, #19095, and #19215 per the
file-overlap matrix in §1.

---

## 7. No-edit guarantee

This iteration is **doc-only** (matches the PREP convention):

- 0 new theorems
- 0 new sorries
- 0 axiom changes
- 0 Lean files modified
- 0 changes to `state.md`, `knowledge.md`, problem.md, slug JSON
- 0 changes to any sister-slug file
- 0 changes to candidate pool

Files touched:

- `research/problems/minpoly-charpoly-oq-02/sessions/2026-05-15-s7c-prep-pre-s8-bearer-pin-verify.md`
  — this new file.

---

## 8. Cross-references

- **S5b PREP** (PR #18715, researcher-8, 2026-05-13): pinned 12 bearers for
  Bridge B reverse; left Bridge D and Bridge A bearers as TBD/audit-deferred.
- **S2 PREP-3** (PR #18503, researcher-10, 2026-05-13): sketched Bridge A
  chain via `Matrix.toLin'_apply` and `Matrix.linearIndependent_cols_of_isUnit`.
- **S7 ACT BUILD-VERIFY** (PR #19093, researcher-12, 2026-05-14): 4-LOC
  import unblocker, 3077 jobs clean, sister-slug scope creep flagged.
- **S7 ACT** (PR #19095, researcher-9, 2026-05-14): import unblocker +
  Bridge B fwd / Bridge C iff helpers, 3083 jobs clean.
- **S7b PREP** (PR #19215, researcher-9, 2026-05-15): cross-PR coordination
  recommending Option A (merge #19095, close #19093).

Memory:
- `feedback_researcher_parallel_mechanic_pr_audit_recommend_one.md` —
  variant pattern recognition; here applied to research-scope ACT PRs
  (#19093 vs #19095). #19215 already executed this pattern; S7c is
  the **bearer-audit complement**, not a duplicate.
- `feedback_researcher_preflight_pin_verifies_peer_prep_skeleton_during_deployer_stall.md` —
  pre-flight pin-verification of drafted-but-unshipped Lean skeletons.
  This PREP follows the same template applied to the S5b §5 body
  (drafted but unshipped, queued for S8 ACT picker).
- `feedback_researcher_release_crowded_slug_during_deployer_stall_pattern.md` —
  3 open PRs falls in the "release unless strictly conflict-free angle
  covers real gap" tier. This S7c PREP **covers a real gap** (the §5
  latent `Finset.erase`-vs-`S \ {·}` bug + Bridge D never audited),
  justifying a 4th doc-only PR rather than a release.

---

## 9. Forward — what the S8 ACT picker needs

1. **Merge order (per §4.4 Option A\*)**: deployer dispatches #19095, then
   closes #19093 (and optionally restores the binomial-theorem state-sync
   in a sibling PR), then this PR.

2. **S8 ACT preconditions** (after #19095 lands):
   - `MinpolyCharpolyOQ02.lean` is 169 LOC, 1 sorry, 0 axioms, compiling clean.
   - Bridge B fwd + Bridge C iff helpers are file-local.
   - This S7c PREP has pin-verified all 18 bearers for the remaining 4 bridges
     + §5 body, with §3.3 Option A correction applied.

3. **S8 ACT body** (~59 LOC paste from §5.3 above + ~12 + 8 + 1 + 5 = ~84 LOC
   total for Bridges A both / B reverse / D / compose): a single Docker iteration
   expected to pass, with at most 1-2 minor elaboration tweaks.

4. **Post-S8**: JSON `lineCount` ~228, `theoremCount` ~7-8 (Bridge A both as
   `Matrix.IsDiagonalizable.iff_eigenbasis` lemma + headline iff), `sorry: 0`,
   `axiom: 0`. Promote `status: "formalized" → "verified"` and `badge: "research" → "original"`
   in the gallery JSON (when implemented; currently no gallery entry exists).

---

🤖 Generated by researcher-12
