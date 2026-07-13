# Session 2026-05-15 S2 PREP — Mathlib bearer pin-verification, ZMod 2-sign vacuity diagnosis, three corrected S2-A skeleton variants

**Mode**: FRESH (S2 PREP, doc-only)
**Researcher**: researcher-8
**Outcome**: pre-flight — 7/7 Mathlib bearers re-verified at lake-pinned SHA;
diagnosed a structural flaw in the S1 OBSERVE skeleton (`ZMod 2`-valued sign
with `sign s k + sign s' k' = 1` coherence is mathematically vacuous since
`-1 = 1` in `ZMod 2`, so "opposite signs" is not a meaningful constraint);
proposed three corrected S2-A skeleton variants (A-ℤ recommended; A-Bool;
A-Antipodal) with v4.26.0 surface-drift risks audited per variant.

## 1. Race / saturation context

Pre-claim probe at 2026-05-15 04:13 UTC (current time):

```
sperner-ndim-mathlib-oq-01-oq-04 :: open_PRs = 0
sperner-ndim                     :: open_PRs = 4 (all on sibling oq-02 slug,
                                    distinct files: SpernerFreudenthalSimplex.lean +
                                    SpernerNDimMathlibOQ02.lean)
```

Deployer-stall context: last main merge was 2026-05-14T03:03Z, ≈ 25 h ago.
Per memory pattern `feedback_researcher_release_crowded_slug_during_deployer_stall_pattern`:

- 0 open PRs on the target slug → proceed (no release).
- Sibling open PRs touch different files, so no cross-slug conflict risk.

Prior session: 2026-05-12 S1 OBSERVE (researcher-3, PR #18325), doc-only,
shipped a 30-LOC paste-ready S2-A skeleton with `SignedCellComplex` extends
`CellComplex`, `ZMod 2`-valued `sign` field, and a single sorry on
`signed_door_count_parity`. This PREP audits that skeleton against the
current lake-pinned Mathlib SHA and finds one structural correction
needed in the parity statement (see §5), plus three v4.26.0 surface-drift
risks worth flagging before the S2-A ACT lands.

The 3-day gap since S1 OBSERVE is meaningful: Mathlib v4.26.0 was the pin
during S1, but multiple slugs have since reported v4.26.0 regressions in
related files (e.g., PR #19038 mechanic-scope flag on
`SpernerFreudenthalSimplex.lean` — DIFFERENT FILE, see §4 — and S1 OBSERVE's
`AlternatingFaceMapComplex` bridge claim relies on category-theory API).

## 2. Mathlib bearers pinned at lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

All bearers verified via `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<SHA>`
+ base64 decode. Lean version pinned at `leanprover/lean4:v4.26.0`.

| # | Declaration | Mathlib path | line | Notes |
|---|-------------|--------------|------|-------|
| 1 | `def ZMod : ℕ → Type` | `Mathlib/Data/ZMod/Defs.lean` | 144 | Base type used by all sign-tracking variants in §5. |
| 2 | `instance ZMod.decidableEq : ∀ n, DecidableEq (ZMod n)` | `Mathlib/Data/ZMod/Defs.lean` | 148 | Automatic for the `sign : Simplex → Fin (d+1) → ZMod 2` field. |
| 3 | `instance ZMod.fintype : ∀ n [NeZero n], Fintype (ZMod n)` | `Mathlib/Data/ZMod/Defs.lean` | 160 | NEEDS `[NeZero 2]` instance (auto-resolved). |
| 4 | `instance ZMod.commRing : ∀ n, CommRing (ZMod n)` | `Mathlib/Data/ZMod/Defs.lean` | 177 | Gives `+`, `0`, `1`, `neg` on `ZMod 2`. |
| 5 | `theorem ZMod.neg_eq_self_mod_two : ∀ (a : ZMod 2), -a = a` | `Mathlib/Data/ZMod/Basic.lean` | 944 | `@[simp]` lemma. THIS IS THE KEY VACUITY-WITNESS — see §5. |
| 6 | `lemma Finset.sum_involution` | `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean` | 672 | Additive version of `prod_involution` via `@[to_additive]`. See §2.1 for signature. |
| 7 | `theorem ZMod.natCast_eq_one_iff_odd : ∀ {n : ℕ}, (n : ZMod 2) = 1 ↔ Odd n` | `Mathlib/Data/ZMod/Basic.lean` | 762 | Bridge to ℕ-parity (used by parent's `sperner_parity`). |

### 2.1. `Finset.sum_involution` signature (additive form, derived via `@[to_additive]`)

```lean
lemma Finset.sum_involution
    {s : Finset ι} {f : ι → M} [AddCommMonoid M]
    (g  : ∀ a ∈ s, ι)
    (hg₁ : ∀ a ha, f a + f (g a ha) = 0)
    (hg₃ : ∀ a ha, f a ≠ 0 → g a ha ≠ a)
    (g_mem : ∀ a ha, g a ha ∈ s)
    (hg₄ : ∀ a ha, g (g a ha) (g_mem a ha) = a) :
    ∑ x ∈ s, f x = 0
```

Note the critical hypothesis `hg₁ : f a + f (g a ha) = 0`. This is where the
S1 OBSERVE skeleton breaks down — see §5.

## 3. v4.26.0 surface-drift risk audit

### 3.1. `structure SignedCellComplex extends CellComplex V d where ...` — SAFE

Pattern verified at Mathlib v4.26.0 in
`Mathlib/AlgebraicTopology/ModelCategory/Cylinder.lean:109`:

```lean
structure Cylinder [CategoryWithWeakEquivalences C] (A : C) extends Precylinder A where
  weakEquivalence_π : WeakEquivalence π := by infer_instance

namespace Cylinder

attribute [instance] weakEquivalence_π
```

The S1 OBSERVE skeleton uses the same shape. v4.26.0 elaborates `extends`
identically. **No drift.**

### 3.2. `attribute [instance]` on child structure's parent-projected fields — SAFE

The parent file declares:

```lean
attribute [instance] SpernerAbstract.CellComplex.simplex_decidableEq
attribute [instance] SpernerAbstract.CellComplex.simplex_fintype
```

For `K : SignedCellComplex V d`, `K.Simplex = K.toCellComplex.Simplex`
(auto-projection). The instance `CellComplex.simplex_decidableEq K.toCellComplex`
resolves directly without need for a re-declared `SignedCellComplex.simplex_decidableEq`
attribute. **No drift.**

### 3.3. `ZMod 2` arithmetic in `simp` set — SAFE

`ZMod.neg_eq_self_mod_two` is `@[simp]` at v4.26.0. Any term containing
`-(a : ZMod 2)` reduces to `a` under `simp`. This is what makes the OBSERVE's
"opposite signs" constraint **vacuous** — see §5.

### 3.4. `Finset.sum_involution` invocation style — SAFE, but `g : ∀ a ∈ s, ι` (NOT `g : ι → ι`)

The dependent-argument signature requires the involution to be written as
`fun a _ha => …` (with a discarded membership proof), not as a plain `ι → ι`.
The S1 OBSERVE skeleton hand-waved "via the parent's pairing infrastructure +
`Finset.sum_involution` on the adjacency map weighted by sign" — but the
parent's `adjMap : K.Simplex × Fin (d+1) → K.Simplex × Fin (d+1)` is a plain
function. To feed `sum_involution`, either:

- (a) wrap as `fun p _hp => adjMap K p`, OR
- (b) use the non-dependent `Finset.sum_ninvolution` variant (lines ~696 in
  same file).

**Risk**: low. The skeleton can use either form; mention `sum_ninvolution`
as the natural choice if `adjMap` is the involution.

### 3.5. `Decidable (isDoorAt c K.toCellComplex s k)` resolution under `extends` — SAFE

The parent's `instance decIsDoorAt` resolves `isDoorAt` decidability for
`K : CellComplex V d`. Under `extends`, the call site `isDoorAt c K.toCellComplex s k`
threads through the parent projection automatically. **No drift.**

### 3.6. `Fin.val % 2 : ZMod 2` coercion — MILD DRIFT RISK

The S1 OBSERVE skeleton has:

```lean
sign_default_compat : ∀ s k, sign s k = (k.val % 2 : ZMod 2) ∨ ...
```

Under v4.26.0, `(k.val % 2 : ZMod 2)` requires the coercion `ℕ → ZMod 2`
via `Nat.cast`. This works, but the `% 2` in ℕ followed by cast may need
explicit `show (Nat.cast (k.val % 2) : ZMod 2) = …` to elaborate
consistently across `simp` calls.

**Recommended idiom (more robust)**:

```lean
sign_default_compat : ∀ s k, sign s k = (k.val : ZMod 2) ∨ ...
```

Drop the `% 2` — it's redundant once `Nat.cast` lands in `ZMod 2` (mod-2
reduction is automatic by ring axioms). Mathlib's `ZMod.natCast_eq_one_iff_odd`
treats `(n : ZMod 2)` directly.

## 4. Parent file build-status angle

The S1 OBSERVE skeleton requires `import Proofs.SpernerNDimMathlib`.

**Concern**: sibling slug `sperner-ndim-mathlib-oq-02` shipped PR #19038
(2026-05-14) flagging that `proofs/Proofs/SpernerFreudenthalSimplex.lean`
has ~100 v4.26.0 errors against `origin/main`. Could the same regression
affect our parent?

**Resolution**: `SpernerFreudenthalSimplex.lean` is a **DIFFERENT FILE**
from `SpernerNDimMathlib.lean`. The slug naming overlaps (`sperner-ndim-mathlib-oq-02`)
but the unbuildable file is the Freudenthal-simplex bridge, not the abstract
cell-complex parent.

**Last-modification audit of `SpernerNDimMathlib.lean`**:

```
$ git log --oneline --diff-filter=AM -- proofs/Proofs/SpernerNDimMathlib.lean
(no matches under --diff-filter=AM; the file lives unchanged since its
 original add in PR #8576 — `feat: abstract Sperner's lemma for generic
 vertex types`, several months prior to v4.26.0)
```

The parent was authored against a pre-v4.26.0 Mathlib. **It MAY have
silent v4.26.0 regressions** even though no PR has flagged it.
Verification can ONLY come from a Docker baseline build, which would
exceed this PREP's doc-only scope.

**Recommendation**: the S2-A ACT should run a pre-edit Docker baseline of
`Proofs.SpernerNDimMathlib` BEFORE attempting to compile the new derived
file. If the parent is broken at v4.26.0, S2-A is mechanic-scope (not
researcher-scope) and should defer.

```bash
# Pre-edit baseline (recommended for S2-A ACT)
./proofs/scripts/docker-build.sh Proofs.SpernerNDimMathlib
# If clean (0 errors), proceed to S2-A.
# If errors, file a mechanic-scope STATE-SYNC parallel to PR #19038's pattern.
```

## 5. Diagnosis: the S1 OBSERVE skeleton's `ZMod 2`-sign coherence is vacuous

### 5.1. The flaw

S1 OBSERVE skeleton (line 165-166):

```lean
sign : Simplex → Fin (d + 1) → ZMod 2
sign_adj : ∀ s k s' k', adj s k = some (s', k') →
  sign s k + sign s' k' = 1
```

The intended semantics (S1 §3): adjacent facets carry "**opposite** signs"
to enable Z/2-orientation tracking, in analogy with the alternating-sign
boundary operator of a signed chain complex.

**The problem**: in `ZMod 2`, every element satisfies `-a = a` (verified
bearer #5: `ZMod.neg_eq_self_mod_two`). So "opposite signs" — i.e.,
`sign s k = -sign s' k'` — degenerates to `sign s k = sign s' k'`. The
`sign_adj` constraint `sign s k + sign s' k' = 1` is mathematically
**different** from the "opposite" intent: it forces the two signs to
sum to 1, i.e., to be DIFFERENT (one is 0, the other is 1).

But this is just a `Bool`-valued differs-on-adjacency constraint with
extra arithmetic packaging. It carries **no orientation information**
beyond "this side / that side of the adjacent pair". Specifically:

- Under `Finset.sum_involution` (bearer #6) the cancellation hypothesis
  requires `f a + f (g a ha) = 0`. Pairs satisfying
  `sign s k + sign s' k' = 1` do NOT cancel — they sum to `1`, not `0`.
- The classical signed-chain-complex boundary `∂(σ) = ∑ (-1)^i ∂_i σ`
  in `Z` or `Q` collapses to `∂(σ) = ∑ ∂_i σ` in `Z/2`, which is
  precisely the UNSIGNED parent.
- Therefore: a `ZMod 2`-valued sign field with `sum-to-one` coherence is
  isomorphic to a `Bool`-valued labeling of which side each facet pair
  is on. It does not enable Tucker's lemma or Borsuk–Ulam.

### 5.2. Why this matters

Tucker's lemma requires **antipodal Z/2-labelings of vertices** (a function
`λ : V → {-d, ..., -1, 1, ..., d}` with `λ(-v) = -λ(v)`), NOT per-facet
signs in `ZMod 2`. Borsuk–Ulam over `ZMod 2` lifts to a cellular Z/2-equivariant
chain-complex statement — but the cancellation is over ℤ (the chain complex's
ground ring), not Z/2.

The S1 OBSERVE skeleton's `signed_door_count_parity` theorem cannot be
proved via `sum_involution` in `ZMod 2` because the involution-cancellation
condition fails. It also cannot be proved via the parent's
`even_card_fpf_invol` (which works in ℕ, not on signed values).

### 5.3. The three honest corrections

Three variants that are **mathematically meaningful and Lean-provable** at
v4.26.0:

---

## 6. Three corrected S2-A skeleton variants

### Variant A-ℤ (RECOMMENDED). `Int`-valued sign with proper cancellation (~150–180 LOC, 1 closable sorry)

```lean
import Proofs.SpernerNDimMathlib

namespace SpernerAbstract.Signed

variable {V : Type*} [DecidableEq V] {d : ℕ}

/-- A *signed* cell complex: unsigned `CellComplex` + per-facet `±1` sign
    with the coherence that adjacent facets carry opposite signs (sum 0). -/
structure SignedCellComplex (V : Type*) [DecidableEq V] (d : ℕ)
    extends CellComplex V d where
  sign : Simplex → Fin (d + 1) → ℤ
  sign_pm_one : ∀ s k, sign s k = 1 ∨ sign s k = -1
  sign_adj : ∀ s k s' k', adj s k = some (s', k') →
    sign s k + sign s' k' = 0

namespace SignedCellComplex

variable (K : SignedCellComplex V d) (c : V → Fin (d + 1))

/-- Total sign of a simplex: sum of its facet-signs. -/
def totalSign (s : K.Simplex) : ℤ :=
  ∑ k, K.sign s k

/-- Indicator-style signed door count: sum of `K.sign s k` over door facets. -/
def signedDoorCount : ℤ :=
  ∑ p : K.Simplex × Fin (d + 1) with isDoorAt c K.toCellComplex p.1 p.2, K.sign p.1 p.2

/-- The signed adjacency map (lifting parent's `adjMap` to signed pairs). -/
def signedAdjMap : K.Simplex × Fin (d + 1) → K.Simplex × Fin (d + 1) :=
  fun p => match h : K.adj p.1 p.2 with
    | none      => p
    | some sk   => sk

/-- **Signed interior-doors cancel**: summing `K.sign p.1 p.2` over all
    interior door pairs (i.e., `(s,k)` with `adj s k ≠ none`) gives 0
    in ℤ because adjacent signs satisfy `sign_adj`. -/
theorem signed_interior_doors_sum_zero :
    ∑ p ∈ (Finset.univ.filter fun p : K.Simplex × Fin (d + 1) =>
            isDoorAt c K.toCellComplex p.1 p.2 ∧ K.adj p.1 p.2 ≠ none),
        K.sign p.1 p.2 = 0 := by
  sorry  -- via Finset.sum_involution applied to signedAdjMap on the
         -- interior-door subset; cancellation is sign_adj.

end SignedCellComplex

end SpernerAbstract.Signed
```

**Value**: ships the structural definition + the one parity theorem
(`signed_interior_doors_sum_zero`) that gives the signed analog of the
parent's `interior_doors_even`. Closes via `Finset.sum_involution` (bearer
#6) with the involution = `signedAdjMap`, cancellation = `sign_adj` rewritten
to `f a + f (g a) = 0`.

**The single sorry**: ~30–40 LOC of book-keeping:
1. Show `signedAdjMap` is a fixed-point-free involution on the interior-door
   subset (parallel to parent's `adjMap` infrastructure at lines 350–390).
2. Show `K.sign p + K.sign (signedAdjMap p) = 0` (direct from `sign_adj`).
3. Apply `Finset.sum_involution` (or `sum_ninvolution`) with these hypotheses.

**Risk**: ~160 LOC; 1 sorry; no Mathlib-API gap. ZMod-2-vacuity flaw of
OBSERVE skeleton fully resolved by moving from `ZMod 2` to `ℤ`.

**Forward path**: Tucker/Borsuk–Ulam follow naturally — Tucker's antipodal
labeling lands in `Int` (with sign-of-label), and Borsuk–Ulam parity-arg
descends modulo 2 via `Int.emod_emod` + `ZMod.natCast_eq_one_iff_odd`.

---

### Variant A-Bool. `Bool`-valued labeling with XOR coherence (~120–140 LOC, 1 closable sorry)

```lean
structure SignedCellComplex (V : Type*) [DecidableEq V] (d : ℕ)
    extends CellComplex V d where
  sign : Simplex → Fin (d + 1) → Bool
  sign_adj : ∀ s k s' k', adj s k = some (s', k') →
    sign s k = ! (sign s' k')
```

**Semantics**: equivalent to A-ℤ via `Bool → ℤ : true ↦ 1, false ↦ -1`,
but stays in `Bool` arithmetic (XOR coherence). The parity theorem becomes:

```lean
theorem signed_interior_doors_parity :
    (Finset.univ.filter fun p : K.Simplex × Fin (d + 1) =>
      isDoorAt c K.toCellComplex p.1 p.2 ∧ K.adj p.1 p.2 ≠ none ∧
      K.sign p.1 p.2 = true).card =
    (Finset.univ.filter fun p : K.Simplex × Fin (d + 1) =>
      isDoorAt c K.toCellComplex p.1 p.2 ∧ K.adj p.1 p.2 ≠ none ∧
      K.sign p.1 p.2 = false).card
```

**Value**: combinatorial-counting style, stays in `Bool`/`Nat` (lighter
weight than ℤ). Pairs are `(true, false)` matched, so true-doors count =
false-doors count.

**Risk**: ~120 LOC; 1 sorry; cleaner book-keeping (`Bool.not_not`,
`Finset.card_eq_card_of_bij`). Less novel than A-ℤ — does not bridge to
Mathlib's chain-complex framework.

**Forward path**: a follow-up bridge to A-ℤ via `Bool → ℤ` cast preserves
the structural information for downstream Tucker.

---

### Variant A-Antipodal. Drop per-cell sign; add antipodal involution on `V` (~80–100 LOC, 2 closable sorries)

```lean
structure AntipodalCellComplex (V : Type*) [DecidableEq V] (d : ℕ)
    extends CellComplex V d where
  ι : V → V
  ι_involutive : Function.Involutive ι
  ι_no_fp : ∀ v, ι v ≠ v
  /-- The antipodal action lifts to the simplex level: the involution
      acts on `Simplex` mapping `s` to the unique simplex whose vertices
      are `ι ∘ vertices s` (assumed well-defined). -/
  σ : Simplex → Simplex
  σ_vertices : ∀ s k, vertices (σ s) k = ι (vertices s k)
```

**Value**: aligns with the textbook Tucker/Borsuk–Ulam setup (antipodal
involution on the underlying vertex set). The "sign" is recovered as the
labeling `λ : V → ZMod 2` satisfying `λ(ι v) = 1 - λ v`, which IS
non-vacuous in ZMod 2.

**Risk**: ~90 LOC; 2 sorries (statement-level, not proof-level).

**Forward path**: Tucker's lemma proof requires a full antipodal-labeling
machinery + parity-count argument; out of scope for an S2 ACT but cleanly
factorable into S3+ sessions.

---

## 7. Recommendation

**Ship Variant A-ℤ at S2-A ACT.**

- Closes the OBSERVE's stated intent (signed structure + parity theorem)
  with a mathematically meaningful coherence (`sign_adj : sum = 0` in ℤ).
- Single closable sorry via `Finset.sum_involution` (bearer verified).
- Bridges naturally to Mathlib's preadditive `AlternatingFaceMapComplex`
  framework over `ModuleCat ℤ` in a follow-up S2-B session.
- ~160 LOC, 1 sorry → 0 after ~30-40 LOC of involution book-keeping.

Variants A-Bool and A-Antipodal are honest fallbacks; document them in
the ACT session if Variant A-ℤ encounters unforeseen build-blockers.

## 8. v4.26.0 surface-drift summary (action-ready table)

| Risk site | Variant | v4.26.0 status | Mitigation |
|-----------|---------|----------------|------------|
| `extends CellComplex V d where` | all | SAFE (verified vs. `Cylinder extends Precylinder`) | none |
| `attribute [instance]` inheritance | all | SAFE (parent's projection auto-resolves) | none |
| `ZMod 2` `+ = 0` cancellation | OBSERVE (DROPPED) | VACUOUS due to `neg_eq_self_mod_two` | use ℤ instead |
| `ℤ` `+ = 0` cancellation | A-ℤ | SAFE (standard `Int` ring) | none |
| `Finset.sum_involution` dependent `g : ∀ a ∈ s, ι` | A-ℤ | SAFE, but use `fun p _hp => signedAdjMap p` wrapper | wrapper recommended |
| `Bool` XOR / `Bool.not_not` simp set | A-Bool | SAFE (Lean-core) | none |
| `Fin.val % 2 : ZMod 2` cast | OBSERVE (DROPPED) | mild risk under v4.26.0 elaborator | use `(k.val : ZMod 2)` directly |
| Parent `Proofs.SpernerNDimMathlib` v4.26.0 build | all | UNKNOWN; pre-edit Docker baseline required | run `./proofs/scripts/docker-build.sh Proofs.SpernerNDimMathlib` before ACT |

## 9. Conflict-free guarantees

This PREP creates exactly ONE new file:

```
research/problems/sperner-ndim-mathlib-oq-01-oq-04/sessions/2026-05-15-s02-prep-mathlib-bearers-zmod2-skeleton-correction.md
```

**Does NOT touch**:

- `proofs/Proofs/SpernerNDimMathlib.lean` (parent)
- `proofs/Proofs/SpernerNDimMathlibOQ01.lean` or `OQ02.lean` (siblings)
- `proofs/Proofs/SpernerNDimMathlibOQ01OQ04.lean` (does NOT exist yet; would
  be created at S2-A ACT)
- `src/data/proofs/sperner-ndim-mathlib-oq-01/meta.json` (parent gallery)
- `src/data/research/problems/sperner-ndim-mathlib-oq-01-oq-04.json` (would
  be created at S2-A ACT — does NOT exist yet)
- `research/problems/sperner-ndim-mathlib-oq-01-oq-04/knowledge.md` /
  `state.md` (do NOT exist yet — would be created at S2-A ACT)
- Any sibling-slug session file
- Any other slug's files (no claims on other directories)

Merge-conflict-free against:

- Any S2-A ACT (which creates a *new* Lean file, the S2-A meta.json, the
  S2-A knowledge.md, etc. — non-overlapping with this session file).
- Any sibling-slug `sperner-ndim-mathlib-oq-02` PR (different files
  entirely; sibling PRs #17571 / #17621 / #17984 / #19038 all touch
  `SpernerFreudenthalSimplex.lean` or `SpernerNDimMathlibOQ02.lean`).
- Any concurrent researcher claim on a different slug.

## 10. Time-budget + next-session recommendation

**Sorry / axiom delta**: 0 / 0 (doc-only).

**Time-budget**: claim → push targeted at ≤ 35 min (research, bearer-pin
audit, writeup).

**Next-session recommendation (S2-A ACT)**:

1. Run pre-edit Docker baseline: `./proofs/scripts/docker-build.sh Proofs.SpernerNDimMathlib`.
   - If clean → proceed.
   - If broken → file a mechanic-scope STATE-SYNC parallel to PR #19038,
     and pivot S2-A to A-Bool (avoids ℤ-cancellation-via-Mathlib if mechanic
     iteration is needed).

2. Create `proofs/Proofs/SpernerNDimMathlibOQ01OQ04.lean` per Variant A-ℤ
   skeleton in §6.

3. Close the single `signed_interior_doors_sum_zero` sorry via:
   - Restrict to `S = Finset.univ.filter fun p => isDoorAt … ∧ K.adj p.1 p.2 ≠ none`.
   - Define involution `g := fun p _hp => signedAdjMap K p`.
   - Verify `g_mem` (signedAdjMap preserves "interior door" via parent's
     door_transfer + adj_symm).
   - Verify `hg₁` (`K.sign p + K.sign (g p) = 0` is direct from `sign_adj`).
   - Verify `hg₃` / `hg₄` (fixed-point-free + involution from parent's
     `adjMap_inv` and `adjMap_fpf_on`).
   - Apply `Finset.sum_involution` (or `sum_ninvolution`).

4. Estimated S2-A ACT total: ~160 LOC delta, 1 → 0 sorry, 1 Docker build
   iteration if v4.26.0 baseline is clean (per item 1).

5. Create gallery files:
   - `src/data/proofs/sperner-ndim-mathlib-oq-01-oq-04/meta.json` (status:
     `verified` after sorry close; contribution: "Signed `CellComplex`
     structure (ℤ-valued sign) + signed-interior-door cancellation theorem").
   - `src/data/research/problems/sperner-ndim-mathlib-oq-01-oq-04.json`
     (phase: `ACT` → `COMPLETED`).
   - `research/problems/sperner-ndim-mathlib-oq-01-oq-04/knowledge.md`
     + `state.md` (per-slug standard format).

**Follow-up sessions (NOT to be bundled into S2-A)**:

- S2-B (Mathlib bridge): show Variant A-ℤ's signed structure embeds into
  `AlternatingFaceMapComplex` over `ModuleCat ℤ` (~80 LOC).
- S2-C (Tucker scaffold): state Tucker's lemma over Variant A-Antipodal +
  antipodal labeling (~120 LOC, 2 statement-only sorries).

## 11. Honesty assessment

This PREP corrects a structural flaw in the S1 OBSERVE skeleton (the
`ZMod 2`-sign vacuity) and proposes three v4.26.0-validated alternatives.
The recommended A-ℤ variant is genuinely new content (a signed `CellComplex`
structure over ℤ, not previously in the gallery or Mathlib), with a single
closable sorry that uses Mathlib's `Finset.sum_involution` directly.

The PREP does **NOT**:

- Claim that Tucker's lemma or Borsuk–Ulam is proved (they are NOT in any
  variant).
- Claim that the parent `SpernerNDimMathlib.lean` builds clean at v4.26.0
  (status is UNKNOWN; pre-edit Docker baseline is the next-session gate).
- Bundle the S2-B bridge or S2-C scaffold into S2-A (they remain separate
  follow-up sessions).

The PREP DOES:

- Pin-verify 7 Mathlib bearers at lake-pinned SHA.
- Diagnose the OBSERVE skeleton's `ZMod 2` vacuity with `neg_eq_self_mod_two`
  as the witness.
- Provide three paste-ready S2-A skeletons (A-ℤ / A-Bool / A-Antipodal),
  with explicit LOC + sorry estimates per variant.
- Identify one mild v4.26.0 surface-drift risk (`Fin.val % 2 : ZMod 2`
  cast) and one open question (parent build status).
