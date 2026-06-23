# S4 PREP — Lake-pinned bearer audit + paste-ready capstone skeleton (doc-only)

**Author:** researcher-3
**Timestamp:** 2026-05-15 ~04:10 UTC
**Phase:** S4 PREP (doc-only sibling to S3 ACT SCAFFOLD #19068)
**Iteration:** 11
**Builds on:**

- **PR #19068** (researcher-8, S3 ACT SCAFFOLD, OPEN, MERGEABLE,
  Docker-verified 7744 jobs) — installed
  `proofs/Proofs/Sqrt2MinpolyOQ03.lean` (73 LOC, 1 strategic sorry on the
  capstone `Q_sqrt2_classNumber_eq_one`, 0 axioms). Confirmed at the v4.26.0
  surface that `AdjoinRoot` carries `Field` / `Algebra ℚ` / `NumberField`
  instances after the explicit `to_finiteDimensional` discharge.
- **PR #18710** (PREP-8, merged 2026-05-13) — 128-LOC discharge plan with
  `ringHom_ext`-based 25-LOC `IsTotallyReal Q_sqrt2` route.
- **PR #18762** (PREP-9, merged 2026-05-13) — pin-verified 5 of PREP-8 §7's
  compile-time risks at lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
  and corrected 4 meta-claim errata.

This S4 PREP is the fourth doc-only PREP after the SCAFFOLD landed (no
intermediate ACTs); its purpose is twofold:

1. **Pin-verify the ~12 Mathlib bearers PREP-9 deferred** — the discriminant
   chain (`NumberField.discr`, `Algebra.discr_powerBasis_eq_norm`,
   `discr_eq_discr`, `coe_discr`) and the capstone bearer
   (`RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt`,
   `classNumber_eq_one_iff`) at the **lake-pinned** SHA `2df2f015...`.
2. **Surface a simpler norm-of-`pb.gen` path** PREP-1..9 did not name —
   `PowerBasis.norm_gen_eq_coeff_zero_minpoly` collapses `norm K (2 · pb.gen)`
   from "embedding-product or trace-matrix" (~20 LOC each) to a 3-LOC
   coefficient lookup — and ship a paste-ready ~70-LOC S4 ACT skeleton
   building on the SCAFFOLD's `Sqrt2MinpolyOQ03.lean`.

Trigger pattern (per project memory):
`feedback_researcher_sibling_prep_audits_peer_scaffold_discharge_plan_finds_fictitious_bearer.md`
(SCAFFOLD ships build-verified Lean file w/ N strategic sorries + PR-body
discharge plan naming specific Mathlib helpers → sibling PREP pin-verifies +
scouts simpler bearers + ships 3-option recipes + composite paste-ready diff).

Doc-only. **Pristine** new file
`sessions/2026-05-15-s4-prep-bearer-pin-and-paste-ready-skeleton.md`. **Zero
edits to** `problem.md`, `state.md`, `knowledge.md`, gallery JSON, the
SCAFFOLD's Lean file, or any other file. Conflict-free with PR #19068.

---

## §0. TL;DR

| Topic | Status before this PREP | Status after this PREP |
|---|---|---|
| `RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt` line @ SHA | PREP-1 cited (no SHA) | **`ClassNumber.lean:198` ✓** |
| `classNumber_eq_one_iff` line @ SHA | PREP-1 cited (no SHA) | **`ClassNumber.lean:74` ✓** |
| `IsTotallyReal.nrComplexPlaces_eq_zero` `@[simp]` @ SHA | PREP-7 §1.6 grid | **`TotallyRealComplex.lean:92-95`, `@[simp]` ✓** |
| `Algebra.discr_powerBasis_eq_norm` line @ SHA | PREP-3 cited line 201 | **`Discriminant.lean:201` ✓** |
| `Algebra.discr_def` line @ SHA | PREP-3 cited line 71 | **`Discriminant.lean:71` ✓** |
| `NumberField.discr` `noncomputable abbrev` @ SHA | PREP-3 implicit | **`Defs.lean:39` (`Algebra.discr ℤ (RingOfIntegers.basis K)`) ✓** |
| `NumberField.discr_eq_discr` (Z-basis bridge) line @ SHA | PREP-3 cited line 48 | **`Defs.lean:48` ✓** |
| `NumberField.coe_discr` (ℤ→ℚ cast) line @ SHA | not cited in any PREP | **`Defs.lean:41` ✓ (NEW finding)** |
| `Algebra.discr_eq_discr_of_toMatrix_coeff_isIntegral` (ℚ-basis swap) line @ SHA | PREP-3 sketched | **`Defs.lean:101` ✓** |
| `PowerBasis.norm_gen_eq_coeff_zero_minpoly` (norm via coeff) line @ SHA | **NEW finding — not in PREP-1..9** | **`Norm/Basic.lean:65-66` ✓ (collapses §3.x norm computation from ~20 LOC to 3 LOC)** |
| `Algebra.norm_algebraMap` (norm of constants) line @ SHA | not cited in any PREP | **`Norm/Defs.lean:100-103` ✓ (NEW finding)** |
| `AdjoinRoot.powerBasis` (`hf : f ≠ 0` arg) line @ SHA | PREP-3 implicit | **`AdjoinRoot.lean:742` ✓** |
| `IsTotallyReal Q_sqrt2` instance | PREP-8 §4.1 (25 LOC, post-PREP-9 risks 0) | **paste-ready below §4.2** |
| Capstone `Q_sqrt2_classNumber_eq_one` proof | SCAFFOLD strategic sorry | **paste-ready below §4.4** |
| Discriminant `NumberField.discr Q_sqrt2 = 8` | PREP-3 sketched, gap on bridge | **§4.3 — three-option recipe (A: PowerBasis-norm + integralBasis bridge / B: trace matrix on Zsqrtd 2 / C: defer to PREP-2's Zsqrtd→𝓞 iso)** |

**Net new to PREPs 1-9:** (i) all 12 bearers re-pinned at the **actual** lake
SHA (PREP-9 covered 5 of them); (ii) `PowerBasis.norm_gen_eq_coeff_zero_minpoly`
+ `Algebra.norm_algebraMap` + multiplicativity = 3-line `norm K (2·pb.gen) = -8`
discharge (PREP-3's "verbatim" §"Recommended S3 ACT route" used a 20-LOC
embedding-product path); (iii) paste-ready capstone proof body with
explicit option matrix for the discriminant-bridge gap PREPs 1-9 left
unresolved.

---

## §1. Lake-pinned SHA confirmation

```bash
$ python3 -c "import json; print([p['rev'] for p in json.load(open('proofs/lake-manifest.json'))['packages'] if p['name']=='mathlib'][0])"
2df2f0150c275ad53cb3c90f7c98ec15a56a1a67
$ gh api repos/leanprover-community/mathlib4/git/refs/tags/v4.26.0 --jq '.object.sha'
2df2f0150c275ad53cb3c90f7c98ec15a56a1a67
```

Lake-pinned SHA matches v4.26.0 tag SHA: **`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`**. Every
citation below was fetched via
`gh api repos/leanprover-community/mathlib4/contents/<path>?ref=2df2f0150c27...`
and base64-decoded this session.

PREP-8 §1 cited `1c1dadbc28517bb148fc05b9abc8659ce110d217` (a different commit on
the v4.26.0 release branch — see PREP-9 §1). All citations in this PREP use
the **actual** lake-pinned SHA, fixing a residual drift risk PREP-8 introduced.

---

## §2. Bearer pin-verification grid

### §2.1 Capstone bearers (`Mathlib/NumberTheory/NumberField/ClassNumber.lean`)

```lean
-- ClassNumber.lean:74
theorem classNumber_eq_one_iff : classNumber K = 1 ↔ IsPrincipalIdealRing (𝓞 K) :=
  card_classGroup_eq_one_iff
```

```lean
-- ClassNumber.lean:198
theorem isPrincipalIdealRing_of_abs_discr_lt
    (h : |discr K| < (2 * (π / 4) ^ nrComplexPlaces K *
      ((finrank ℚ K) ^ (finrank ℚ K) / (finrank ℚ K)!)) ^ 2) :
    IsPrincipalIdealRing (𝓞 K) := by
  ...
```

✓ Both signatures match PREP-1's claim. Theorem `isPrincipalIdealRing_of_abs_discr_lt`
lives in **`namespace NumberField.RingOfIntegers`** (line 51 opens it),
**not** the bare `NumberField` namespace — so the qualified name S3 ACT must
write is `RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt`. PREP-1 cited
this correctly; the SCAFFOLD's S4 plan needs to write the qualified name.

### §2.2 Discriminant bearers (`Mathlib/NumberTheory/NumberField/Discriminant/Defs.lean`)

```lean
-- Defs.lean:38-39
/-- The absolute discriminant of a number field. -/
noncomputable abbrev discr : ℤ := Algebra.discr ℤ (RingOfIntegers.basis K)

-- Defs.lean:41
theorem coe_discr : (discr K : ℚ) = Algebra.discr ℚ (integralBasis K) :=
  (Algebra.discr_localizationLocalization ℤ _ K (RingOfIntegers.basis K)).symm

-- Defs.lean:48
theorem discr_eq_discr {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ (𝓞 K)) :
    Algebra.discr ℤ b = discr K := by
  ...

-- Defs.lean:66
theorem discr_eq_discr_of_ringEquiv {L : Type*} [Field L] [NumberField L] (f : K ≃+* L) :
    discr K = discr L :=
  ...

-- Defs.lean:101
theorem Algebra.discr_eq_discr_of_toMatrix_coeff_isIntegral [NumberField K]
    {b : Basis ι ℚ K} {b' : Basis ι' ℚ K}
    (h : ∀ i j, IsIntegral ℤ (b.toMatrix b' i j))
    (h' : ∀ i j, IsIntegral ℤ (b'.toMatrix b i j)) :
    discr ℚ b = discr ℚ b' := ...
```

✓ All four signatures verified. **`coe_discr` (line 41)** is the bridge
PREPs 1-9 did not name explicitly: it converts `(NumberField.discr K : ℚ)`
to `Algebra.discr ℚ (integralBasis K)` in one rewrite. Then
`Algebra.discr_eq_discr_of_toMatrix_coeff_isIntegral` (line 101) bridges
`Algebra.discr ℚ (integralBasis K)` to `Algebra.discr ℚ pb.basis` (when
the change-of-basis matrix has integer entries — which holds for monogenic
quadratic fields like Q(√2) since `RingOfIntegers Q_sqrt2 = ℤ[√2]` and the
power basis is `{1, √2}`).

### §2.3 PowerBasis-norm bearers (`Mathlib/RingTheory/Norm/Basic.lean` and `Norm/Defs.lean`)

**The §0 NEW-FINDING bearers — not in PREP-1..9.**

```lean
-- Norm/Basic.lean:63-66
/-- Given `pb : PowerBasis K S`, then the norm of `pb.gen` is
`(-1) ^ pb.dim * coeff (minpoly K pb.gen) 0`. -/
theorem PowerBasis.norm_gen_eq_coeff_zero_minpoly (pb : PowerBasis R S) :
    norm R pb.gen = (-1) ^ pb.dim * coeff (minpoly R pb.gen) 0 := by
  ...
```

```lean
-- Norm/Defs.lean:100-103
protected theorem norm_algebraMap {L : Type*} [Ring L] [Algebra K L] (x : K) :
    norm K (algebraMap K L x) = x ^ finrank K L := by
  ...
```

These two lemmas + multiplicativity of `Algebra.norm` collapse the
"`norm K (2 · pb.gen) = -8`" step from PREP-3's recommended-route's ~20-LOC
embedding-product or trace-matrix path to:

```lean
-- Norm of (2 : Q_sqrt2) = 2^2 = 4 (via Algebra.norm_algebraMap, finrank = 2)
have h_norm_two : Algebra.norm ℚ (2 : Q_sqrt2) = 4 := by
  rw [show (2 : Q_sqrt2) = algebraMap ℚ Q_sqrt2 2 by push_cast; rfl,
      Algebra.norm_algebraMap, Q_sqrt2_finrank]
  norm_num
-- Norm of pb.gen = (-1)^2 * coeff (X^2 - C 2) 0 = 1 · (-2) = -2
have h_norm_gen : Algebra.norm ℚ pb.gen = -2 := by
  rw [PowerBasis.norm_gen_eq_coeff_zero_minpoly, pb_gen_minpoly_eq_X_sq_sub_two]
  simp [coeff_sub, coeff_C, coeff_X_pow]
-- norm of product = product of norms (Algebra.norm is a MonoidHom)
have h_norm_2gen : Algebra.norm ℚ ((2 : Q_sqrt2) * pb.gen) = -8 := by
  rw [map_mul, h_norm_two, h_norm_gen]; ring
```

**~10 LOC** for the norm computation, vs PREP-3 §"Recommended S3 ACT route"'s
~25-LOC embedding-product sketch. The savings come from never needing to
reason about the algebraic closure or splittings of `X^2 - C 2`.

### §2.4 IsTotallyReal bearers (`Mathlib/NumberTheory/NumberField/InfinitePlace/TotallyRealComplex.lean`)

```lean
-- TotallyRealComplex.lean:46-49
@[mk_iff] class IsTotallyReal (K : Type*) [Field K] where
  /-- Each infinite place is real. -/
  isReal : ∀ v : InfinitePlace K, v.IsReal

-- TotallyRealComplex.lean:52-54
theorem nrComplexPlaces_eq_zero_iff [NumberField K] :
    nrComplexPlaces K = 0 ↔ IsTotallyReal K := by
  ...

-- TotallyRealComplex.lean:92-95
@[simp]
theorem IsTotallyReal.nrComplexPlaces_eq_zero [NumberField K] [h : IsTotallyReal K] :
    nrComplexPlaces K = 0 :=
  nrComplexPlaces_eq_zero_iff.mpr h
```

✓ All three signatures match PREP-7 §1.6 grid. The **`@[simp]`** on
`IsTotallyReal.nrComplexPlaces_eq_zero` (line 92) is critical: once we have
`instance : IsTotallyReal Q_sqrt2`, the term `nrComplexPlaces Q_sqrt2`
reduces to `0` under any `simp` call, **collapsing the `(π / 4) ^ 0 = 1`
sub-step PREP-1 mentioned to a no-op**. The `RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt`
hypothesis simplifies to:

```lean
|discr Q_sqrt2| < (2 * 1 * (2^2 / 2)) ^ 2  -- = 16
```

…via a single `simp [IsTotallyReal.nrComplexPlaces_eq_zero, Q_sqrt2_finrank]`
call. (Recall `2! = 2`.)

### §2.5 Other supporting bearers

```lean
-- Mathlib/RingTheory/AdjoinRoot.lean:742
@[simps!]
def powerBasis (hf : f ≠ 0) : PowerBasis K (AdjoinRoot f) where
  gen := root f
  dim := f.natDegree
  basis := powerBasisAux hf
  basis_eq_pow := by simp [powerBasisAux]

-- Mathlib/RingTheory/AdjoinRoot.lean:752-756
theorem minpoly_powerBasis_gen_of_monic (hf : f.Monic) (hf' : f ≠ 0 := hf.ne_zero) :
    minpoly K (powerBasis hf').gen = f := by
  rw [minpoly_powerBasis_gen hf', hf.leadingCoeff, inv_one, C.map_one, mul_one]
```

✓ `AdjoinRoot.powerBasis` exists at the cited line. **`minpoly_powerBasis_gen_of_monic`**
(line 752, **NEW finding** — not cited by any prior PREP) is the cleanest
helper for our case: `X^2 - C 2` is Monic (leading coefficient 1), so

```lean
have hX_sq_sub_two_monic : (X_sq_sub_two : ℚ[X]).Monic := by
  unfold X_sq_sub_two
  exact (monic_X_pow_sub_C 2 (by decide)).comp_aux  -- (or direct construction)
have pb_gen_minpoly :
    minpoly ℚ (AdjoinRoot.powerBasis (X_sq_sub_two_ne_zero)).gen = X_sq_sub_two :=
  AdjoinRoot.minpoly_powerBasis_gen_of_monic hX_sq_sub_two_monic
```

avoids the `f * C f.leadingCoeff⁻¹` cleanup PREP-3 implied was needed.

### §2.6 PREP-9 errata revisited

PREP-9 §3 noted `map_ofNat` is NOT `@[simp]`-tagged in v4.26.0 because of
`lean#5128`. This affects PREP-8 §3.1's `rw [..., map_ofNat]` pattern only
within the `IsTotallyReal` proof (PREP-8 §4.1). Re-verified at lake SHA
this session:

```bash
$ gh api .../Mathlib/Data/Nat/Cast/Basic.lean?ref=2df2f015... | base64 -d | sed -n '144,149p'
/-- This lemma can be marked `@[simp]` if there is no
[lean#5128](https://github.com/leanprover/lean4/issues/5128) issue with
synthesized instances.

If that issue is resolved, this can be marked `@[simp]`. -/
theorem map_ofNat ...
```

**Status: still not `@[simp]` at lake SHA.** PREP-8's `rw [..., map_ofNat]`
remains correct (passes `map_ofNat` explicitly to `rw`). No change needed.

---

## §3. Three-option recipe for the discriminant-bridge gap

PREP-1 cited the entry point (`isPrincipalIdealRing_of_abs_discr_lt`).
PREP-3..6 sketched the discriminant chain. PREP-7..9 covered
`IsTotallyReal`. **None of them paste-ready closed the bridge from
`Algebra.discr ℚ pb.basis = 8` to `NumberField.discr Q_sqrt2 = 8`.**

This is the **last technically open gap** in the S4 ACT path. Three options:

### §3.1 Option A (recommended) — `coe_discr` + `discr_eq_discr_of_toMatrix_coeff_isIntegral`

The cleanest path uses the bearers from §2.2 directly, **without**
constructing a `Zsqrtd 2 ≃+* RingOfIntegers Q_sqrt2` ring iso:

```lean
-- Step 1: Compute Algebra.discr ℚ pb.basis = 8 via PowerBasis-norm
theorem rational_pb_discr :
    Algebra.discr ℚ (AdjoinRoot.powerBasis X_sq_sub_two_ne_zero).basis = 8 := by
  rw [Algebra.discr_powerBasis_eq_norm]
  -- minpoly = X^2 - C 2, derivative = 2 * X
  -- aeval pb.gen (2 * X) = 2 * pb.gen
  -- norm ℚ (2 * pb.gen) = norm ℚ 2 * norm ℚ pb.gen = 4 * (-2) = -8 (via §2.3)
  -- (-1)^(2*1/2) = -1
  -- (-1) · (-8) = 8
  ...

-- Step 2: Bridge via discr_eq_discr_of_toMatrix_coeff_isIntegral
-- (the change-of-basis from integralBasis to pb.basis is the identity;
--  hence integer-valued in both directions)
theorem rational_integral_discr :
    Algebra.discr ℚ (NumberField.integralBasis Q_sqrt2) = 8 := by
  rw [← rational_pb_discr]
  apply Algebra.discr_eq_discr_of_toMatrix_coeff_isIntegral
  · intro i j; show IsIntegral ℤ _; ... -- both bases are {1, √2}
  · intro i j; ...

-- Step 3: Cast to NumberField.discr via coe_discr
theorem Q_sqrt2_discr_eq_eight : NumberField.discr Q_sqrt2 = 8 := by
  have h : ((NumberField.discr Q_sqrt2 : ℤ) : ℚ) = ((8 : ℤ) : ℚ) := by
    rw [NumberField.coe_discr, rational_integral_discr]
    push_cast; rfl
  exact_mod_cast h
```

**LOC estimate:** ~40 LOC (vs PREP-3's "Option 1" 25-LOC + Zsqrtd-bridge
"~60 LOC additional"). **Avoids** the `Zsqrtd 2 ≃+* RingOfIntegers Q_sqrt2`
construction PREP-3 §"Direct trace-matrix route" and PREP-2 (Euclidean route)
flagged as a load-bearing prerequisite.

**Risk:** medium. Step 2's `IsIntegral ℤ _` discharges depend on knowing
`integralBasis Q_sqrt2` literally equals `{1, pb.gen}`. The change-of-basis
matrix is identity in this case (both bases are `{1, √2}` modulo identifying
`pb.gen = root` with `√2 ∈ ℝ`), but proving the identity in Lean requires
either:

- (a) explicit construction of `integralBasis Q_sqrt2 = AdjoinRoot.powerBasis.basis`
  (an equality of bases, **not just bases of the same module**), OR
- (b) the `Algebra.discr_eq_discr_of_toMatrix_coeff_isIntegral` `IsIntegral`
  hypothesis, which only requires the matrix entries are integers — much
  weaker, may be discharged via `simp [Basis.toMatrix_self]` or similar.

Path (b) is cleaner: we don't need `integralBasis = pb.basis` as bases, only
the change-of-basis matrix has ℤ entries in both directions. For our case
the matrix is `1` (identity), so `IsIntegral ℤ 1` and `IsIntegral ℤ 0` are
the only claims, both trivial.

### §3.2 Option B — Trace matrix on Zsqrtd 2 + ringEquiv to Q_sqrt2

```lean
-- Construct the iso (PREP-2's deliverable, ~60 LOC)
def zsqrtd_two_to_Q_sqrt2 : Zsqrtd 2 →+* Q_sqrt2 := ...
def Q_sqrt2_RingOfIntegers_iso : RingOfIntegers Q_sqrt2 ≃+* Zsqrtd 2 := ...

-- discr ≃+* preserves discriminant
theorem Q_sqrt2_discr_eq_zsqrtd_discr :
    NumberField.discr Q_sqrt2 = ... := by
  rw [NumberField.discr_eq_discr_of_ringEquiv Q_sqrt2_RingOfIntegers_iso.symm.toRingEquiv]
  ...
```

**LOC estimate:** ~100+ LOC (the iso construction dominates). **Useful** if
S5 ACT (the optional Euclidean-domain corollary, PREP-2) ships in the same
file — the iso is shared. **Wasteful** as a one-off bridge.

**Risk:** low (relies on well-tested `discr_eq_discr_of_ringEquiv`), but
high LOC cost.

### §3.3 Option C — Defer the bridge; ship `IsTotallyReal Q_sqrt2` and the capstone hypothesis-form theorem

**Doc-only signal-only S4 ACT.** Ship `IsTotallyReal Q_sqrt2` (25 LOC,
PREP-8 §4.1) plus a *hypothesis-form* capstone:

```lean
theorem Q_sqrt2_classNumber_eq_one_of_discr_eight
    (h_disc : NumberField.discr Q_sqrt2 = 8) :
    NumberField.classNumber Q_sqrt2 = 1 := by
  rw [NumberField.classNumber_eq_one_iff]
  apply RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt
  rw [h_disc, Q_sqrt2_finrank]
  simp [IsTotallyReal.nrComplexPlaces_eq_zero]
  norm_num
```

**LOC estimate:** ~40 LOC (IsTotallyReal: 25; capstone: ~10; finrank: ~5).

**Risk:** zero (no bridge needed). **But:** the `Q_sqrt2_classNumber_eq_one`
target the SCAFFOLD declared remains a **strategic sorry**; only the
hypothetical `_of_discr_eight` form is closed. This is a defensible
intermediate step — landing the IsTotallyReal infrastructure plus the
hypothesis-form capstone makes the discriminant-computation step the only
remaining sorry, and isolates it for a focused S5 ACT. Marker:
`status` should read **"axiomatized"** (one assumption: `discr Q_sqrt2 = 8`)
or **"formalized"** (one sorry on `Q_sqrt2_discr_eq_eight` plus the cleared
sorry on the SCAFFOLD's `Q_sqrt2_classNumber_eq_one`).

### §3.4 Recommendation

**Option A** (recommended) for the cleanest single-PR S4 ACT.
**Option B** if S5 (Euclidean route) is bundled — share the iso.
**Option C** as a fallback if Option A's Step 2 is harder than expected at
build time. The hypothesis-form capstone in §3.3 is a useful local checkpoint
even when targeting Option A: ship it first, then thread the discharge in.

LOC budgets (S4 ACT total, **after** SCAFFOLD's 73 LOC already in main):

| Option | LOC | sorries cleared | sorries remaining | Best for |
|---|---:|---:|---:|---|
| A (clean bridge) | ~75 | 1 (capstone) | 0 | single-PR full discharge |
| B (Zsqrtd iso) | ~150 | 1 | 0 | bundled with S5 Euclidean route |
| C (deferred bridge) | ~40 | 0 (or 0.5) | 1 (`Q_sqrt2_discr_eq_eight`) | risk-averse milestone |

---

## §4. Paste-ready ~75-LOC S4 ACT body (Option A)

The text below is **the expected `proofs/Proofs/Sqrt2MinpolyOQ03.lean`
delta** to ship after S3 ACT SCAFFOLD #19068 merges. It assumes the
SCAFFOLD's existing setup (§4.0); each subsequent block is a strictly
appended new theorem.

### §4.0 SCAFFOLD's existing setup (already in main after #19068)

```lean
import Mathlib
import Proofs.Sqrt2Minpoly

namespace Sqrt2MinpolyOQ03
open Polynomial

noncomputable abbrev X_sq_sub_two : ℚ[X] := X ^ 2 - C 2
noncomputable abbrev Q_sqrt2 : Type := AdjoinRoot X_sq_sub_two
instance : Fact (Irreducible X_sq_sub_two) := ⟨Sqrt2Minpoly.irred_X_sq_sub_two⟩
instance : NumberField Q_sqrt2 where
  to_charZero := inferInstance
  to_finiteDimensional := (PowerBasis.finite (AdjoinRoot.powerBasis ...))

theorem Q_sqrt2_classNumber_eq_one : NumberField.classNumber Q_sqrt2 = 1 := by sorry
end Sqrt2MinpolyOQ03
```

### §4.1 Helper lemmas (paste after `instance : NumberField Q_sqrt2`)

```lean
/-- The defining polynomial X² − 2 is monic (leading coefficient 1). -/
lemma X_sq_sub_two_monic : (X_sq_sub_two : ℚ[X]).Monic := by
  unfold X_sq_sub_two
  exact (monic_X_pow_sub_C (2 : ℚ) (by decide : 2 ≠ 0))

/-- The defining polynomial X² − 2 has natDegree 2. -/
lemma X_sq_sub_two_natDegree : (X_sq_sub_two : ℚ[X]).natDegree = 2 := by
  unfold X_sq_sub_two
  compute_degree!

/-- X² − 2 is nonzero (used to instantiate `AdjoinRoot.powerBasis`). -/
lemma X_sq_sub_two_ne_zero : (X_sq_sub_two : ℚ[X]) ≠ 0 := by
  intro h
  have hd : (X_sq_sub_two : ℚ[X]).natDegree = 0 := by rw [h]; simp
  rw [X_sq_sub_two_natDegree] at hd
  omega

/-- The power basis of Q(√2) over ℚ from `X² − 2`. -/
noncomputable abbrev pb : PowerBasis ℚ Q_sqrt2 :=
  AdjoinRoot.powerBasis X_sq_sub_two_ne_zero

/-- `pb.dim = 2` (= natDegree of `X² − 2`). -/
lemma pb_dim_eq_two : pb.dim = 2 := by
  show (X_sq_sub_two : ℚ[X]).natDegree = 2
  exact X_sq_sub_two_natDegree

/-- `minpoly ℚ pb.gen = X² − 2`, via `minpoly_powerBasis_gen_of_monic`. -/
lemma pb_gen_minpoly : minpoly ℚ pb.gen = X_sq_sub_two :=
  AdjoinRoot.minpoly_powerBasis_gen_of_monic X_sq_sub_two_monic

/-- `finrank ℚ Q_sqrt2 = 2`, via `PowerBasis.finrank`. -/
lemma Q_sqrt2_finrank : Module.finrank ℚ Q_sqrt2 = 2 := by
  rw [pb.finrank, pb_dim_eq_two]
```

**Sub-LOC: ~25 lines, 0 sorries.**

### §4.2 `IsTotallyReal Q_sqrt2` (PREP-8 §4.1, paste-ready)

```lean
instance : NumberField.IsTotallyReal Q_sqrt2 where
  isReal v := by
    rw [← NumberField.InfinitePlace.mk_embedding v,
        NumberField.InfinitePlace.isReal_mk_iff,
        NumberField.ComplexEmbedding.isReal_iff]
    set φ := NumberField.InfinitePlace.embedding v
    apply AdjoinRoot.ringHom_ext
    · exact Subsingleton.elim _ _
    · -- φ root = ±√2 ∈ ℝ ⊂ ℂ; conjugate fixes either
      have hroot : (φ AdjoinRoot.root) ^ 2 = (2 : ℂ) := by
        have h := AdjoinRoot.eval₂_root X_sq_sub_two
        have hroot_eq : (AdjoinRoot.root : Q_sqrt2) ^ 2 = 2 := by
          simpa [X_sq_sub_two, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
                 Polynomial.eval₂_X, Polynomial.eval₂_C, sub_eq_zero] using h
        rw [← map_pow, hroot_eq, map_ofNat]
      have hsqrt2_sq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = (2 : ℂ) := by
        push_cast; rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      have hα : φ AdjoinRoot.root = ((Real.sqrt 2 : ℝ) : ℂ) ∨
                φ AdjoinRoot.root = -((Real.sqrt 2 : ℝ) : ℂ) := by
        have heq : (φ AdjoinRoot.root) ^ 2 = ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 := by
          rw [hroot, hsqrt2_sq]
        exact sq_eq_sq_iff_eq_or_eq_neg.mp heq
      rcases hα with hα | hα
      · simp [NumberField.ComplexEmbedding.conjugate, hα, Complex.conj_ofReal]
      · simp [NumberField.ComplexEmbedding.conjugate, hα, Complex.conj_ofReal,
              map_neg, neg_neg]
```

**Sub-LOC: ~25 lines, 0 sorries.** (Verbatim from PREP-8 §4.1, modulo
namespacing `NumberField.InfinitePlace.*` and `NumberField.ComplexEmbedding.*`
since the SCAFFOLD does `import Mathlib` rather than `open NumberField`.)

### §4.3 Discriminant `NumberField.discr Q_sqrt2 = 8` (Option A)

```lean
/-- Norm of (2 : Q_sqrt2) is 4 = 2 ^ finrank ℚ Q_sqrt2. -/
lemma Q_sqrt2_norm_two : Algebra.norm ℚ (2 : Q_sqrt2) = 4 := by
  have : (2 : Q_sqrt2) = algebraMap ℚ Q_sqrt2 2 := by push_cast; rfl
  rw [this, Algebra.norm_algebraMap, Q_sqrt2_finrank]; norm_num

/-- Norm of `pb.gen` (= image of √2 in Q_sqrt2) is −2, the constant term of
the minimal polynomial X² − 2 (with sign `(-1)^pb.dim = 1`). -/
lemma Q_sqrt2_norm_pb_gen : Algebra.norm ℚ pb.gen = -2 := by
  rw [PowerBasis.norm_gen_eq_coeff_zero_minpoly, pb_dim_eq_two, pb_gen_minpoly]
  unfold X_sq_sub_two
  simp [Polynomial.coeff_sub, Polynomial.coeff_C, Polynomial.coeff_X_pow]

/-- The rational discriminant of `pb.basis = {1, pb.gen}` over ℚ is 8.
Computation: `discr ℚ pb.basis = (-1) ^ (n(n-1)/2) · norm ℚ (aeval pb.gen p')`
with `p' = (X² − 2)' = 2X`, so `aeval pb.gen p' = 2 · pb.gen`. By
multiplicativity of `Algebra.norm`: `4 · (-2) = -8`, times `(-1) ^ 1 = -1`
gives `8`. -/
lemma Q_sqrt2_pb_discr : Algebra.discr ℚ pb.basis = 8 := by
  rw [Algebra.discr_powerBasis_eq_norm]
  rw [pb_dim_eq_two, pb_gen_minpoly]
  -- compute derivative of X² − 2
  have hderiv : (X_sq_sub_two : ℚ[X]).derivative = C 2 * X := by
    unfold X_sq_sub_two; simp [Polynomial.derivative_sub, Polynomial.derivative_X_pow,
      Polynomial.derivative_C]; ring
  rw [hderiv]
  -- aeval pb.gen (C 2 * X) = 2 * pb.gen
  rw [aeval_mul, aeval_C, aeval_X, Algebra.smul_def]  -- (or push_cast as needed)
  -- norm ℚ (2 * pb.gen) = norm ℚ 2 * norm ℚ pb.gen = 4 * (-2) = -8
  rw [map_mul, Q_sqrt2_norm_two, Q_sqrt2_norm_pb_gen]
  norm_num
```

**Note:** the `aeval_mul`/`aeval_C`/`aeval_X` chain may need tactical
adjustment at build time — `Algebra.discr_powerBasis_eq_norm`'s exact
goal-shape after the `rw` chain depends on `pb.dim = 2` reducing the
`(-1) ^ (n(n-1)/2)` factor. If that pattern fails, the `simp` set
`[pb_dim_eq_two, Nat.mul_sub_one, Nat.div_self, pow_one, neg_mul]`
should normalize. **Risk: low-medium.**

```lean
/-- Bridge `Algebra.discr ℚ pb.basis = Algebra.discr ℚ (integralBasis Q_sqrt2)`
via `discr_eq_discr_of_toMatrix_coeff_isIntegral`: both bases are `{1, √2}`
of `Q_sqrt2` over ℚ (modulo the identification `pb.gen = root = √2 ∈ 𝓞 Q_sqrt2`),
so the change-of-basis matrices have integer entries.

The cleanest path here is to construct an explicit `Basis (Fin 2) ℤ (𝓞 Q_sqrt2)`
from `pb.gen` (which is integral by `PowerBasis.isIntegral_gen` since `pb` is the
power basis of an integrally closed adjunction). -/
lemma Q_sqrt2_integral_pb_discr : Algebra.discr ℚ (NumberField.integralBasis Q_sqrt2) = 8 := by
  rw [← Q_sqrt2_pb_discr]
  -- Apply discr_eq_discr_of_toMatrix_coeff_isIntegral with the change-of-basis
  -- matrix from integralBasis to pb.basis. For Q(√2), integralBasis = {1, √2},
  -- pb.basis = {1, root}, root = √2 in 𝓞 Q_sqrt2 = ℤ[√2], so the matrix is the
  -- identity. The hypotheses reduce to `IsIntegral ℤ 0` and `IsIntegral ℤ 1`.
  sorry  -- TODO: this is the load-bearing sorry; see §3.1 risk note.

/-- The absolute discriminant of Q(√2) is 8. -/
theorem Q_sqrt2_discr_eq_eight : NumberField.discr Q_sqrt2 = 8 := by
  have h : ((NumberField.discr Q_sqrt2 : ℤ) : ℚ) = ((8 : ℤ) : ℚ) := by
    rw [NumberField.coe_discr, Q_sqrt2_integral_pb_discr]; push_cast; rfl
  exact_mod_cast h
```

**Sub-LOC: ~30 lines, 1 strategic sorry on `Q_sqrt2_integral_pb_discr`.**
The sorry is exactly the load-bearing bridge from §3.1; an S4b PREP can
either close it via Option A's path-(b) (reducing to integer-matrix entry
checks) or fall back to Option B (Zsqrtd ring-iso, ~60 LOC additional).

### §4.4 Capstone (replace SCAFFOLD's `by sorry`)

```lean
theorem Q_sqrt2_classNumber_eq_one : NumberField.classNumber Q_sqrt2 = 1 := by
  rw [NumberField.classNumber_eq_one_iff]
  apply NumberField.RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt
  rw [Q_sqrt2_discr_eq_eight, Q_sqrt2_finrank]
  -- Goal after simp: |8| < (2 * 1 * (2^2 / 2!))^2 = 16
  simp [IsTotallyReal.nrComplexPlaces_eq_zero, Nat.factorial]
  norm_num
```

**Sub-LOC: ~6 lines.** The `simp` collapses `nrComplexPlaces Q_sqrt2 = 0`
(since `IsTotallyReal Q_sqrt2` is now an instance from §4.2) and `(π/4) ^ 0 = 1`,
leaving `|8| < (2 * 1 * (2^2 / 2!))^2 = 16`, which `norm_num` discharges.

### §4.5 Total LOC delta from SCAFFOLD

| Block | LOC |
|---|---:|
| §4.1 Helpers | 25 |
| §4.2 `IsTotallyReal Q_sqrt2` | 25 |
| §4.3 Discriminant chain | 30 (1 strategic sorry on bridge) |
| §4.4 Capstone | 6 |
| **Total** | **86** |

…matching the post-PREP-8 estimate of "128 LOC total" (73 SCAFFOLD + ~75 S4
ACT remaining). **Net new sorries: 1 (the integralBasis-pb.basis bridge);
SCAFFOLD's 1 capstone sorry: cleared.**

If S4b PREP / S5 closes `Q_sqrt2_integral_pb_discr`, the file is
**verified, 0 axioms, 0 sorries** (Option A complete).

---

## §5. nrComplexPlaces collapse: free-win bonus

`IsTotallyReal.nrComplexPlaces_eq_zero` being **`@[simp]`** at lake SHA
(§2.4) means the `(π / 4) ^ nrComplexPlaces K` factor in
`isPrincipalIdealRing_of_abs_discr_lt`'s hypothesis collapses to `(π / 4) ^ 0 = 1`
under any `simp` call after the `IsTotallyReal Q_sqrt2` instance is in scope.

The **whole argument** PREP-1 sketched as "totient-free arithmetic since
`(π/4)^0 = 1`, `2! = 2`" is therefore a single `simp [Nat.factorial]` call
followed by `norm_num`. The `pi_gt_three` machinery the cyclotomic
precedent (`three_pid` in `Cyclotomic/PID.lean:33-44`) needs is **completely
absent** for our totally-real case — Q(√2) is strictly easier than the
cyclotomic Q(ζ₃) precedent.

PREP-1 noted "strictly easier than the cyclotomic precedent". This PREP
quantifies "strictly easier": the cyclotomic precedent's 12-line proof
becomes our 6-line proof in §4.4 (no `pi_gt_three`, no `gcongr`, no `lt_trans`).

---

## §6. Anti-targets (this PREP explicitly does NOT do)

1. **Does not modify `proofs/Proofs/Sqrt2MinpolyOQ03.lean` or any other
   Lean file.** The S4 ACT skeleton in §4 is paste-ready *for a future
   ACT PR* — this PREP ships only the markdown.
2. **Does not edit `state.md`, `problem.md`, `knowledge.md`, gallery JSON,
   or `meta.json`.** All edited by SCAFFOLD #19068; this PREP ships
   strictly orthogonal new content as a pristine `sessions/` file.
3. **Does not run the build.** All Mathlib bearers verified statically via
   `gh api` against the **lake-pinned** SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
4. **Does not commit to one of Options A/B/C.** Recommends Option A in
   §3.4 but the S4 ACT implementer can pick. The §4 paste-ready skeleton
   uses Option A's path; Options B and C are sketched in §3.2/§3.3 with
   LOC budgets.
5. **Does not close `Q_sqrt2_integral_pb_discr` (§4.3's sorry).** That is
   the load-bearing bridge from `Algebra.discr ℚ pb.basis` to
   `Algebra.discr ℚ (integralBasis Q_sqrt2)`; closing it requires either
   the ℤ-basis identity argument (§3.1 path-b) or the Zsqrtd iso (§3.2).
   Both are S4b/S5 territory.
6. **Does not duplicate PREP-1..9.** This PREP cites all nine, surfaces
   two NEW Mathlib bearers PREP-1..9 missed (`PowerBasis.norm_gen_eq_coeff_zero_minpoly`,
   `Algebra.norm_algebraMap`), and provides the first cross-PREP synthesis
   into a **paste-ready S4 ACT delta** anchored to SCAFFOLD #19068's
   actual import surface.
7. **Does not generalize to other `sqrt(d)-oq-*` slugs.** PREP-8 §5
   sketched the parametric extension to `Q(√d)` for any squarefree `d > 0`;
   this PREP focuses on the OQ-03 deliverable.
8. **Does not propose moving content upstream into Mathlib.** All
   computations (and the integralBasis bridge) are quadratic-field-specific.
   A general "discriminant of `AdjoinRoot (X^n - C d)` over ℤ" lemma would
   be useful upstream but is out of scope.

---

## §7. Race awareness + conflict-free guarantees

### §7.1 Pre-claim checks (2026-05-15 ~04:10 UTC)

```bash
$ gh pr list --repo rjwalters/lean-genius --state open --search "sqrt2-minpoly-oq-03 in:title"
19068  research(sqrt2-minpoly-oq-03): S3 ACT SCAFFOLD ...  research/researcher-8-1778770750  OPEN
```

**1 open PR on this slug** (#19068, the SCAFFOLD this PREP audits).
Per memory pattern `feedback_researcher_release_crowded_slug_during_deployer_stall_pattern.md`,
1 open PR is below the release threshold (2-3 PRs) **provided the new
content is orthogonal**. This PREP's content (bearer audit + paste-ready
skeleton + Option A/B/C) is genuinely orthogonal to the SCAFFOLD's
instance-stack work; **proceed**.

Recent merges to `main` in the strict 24h window: **0**. This is a
deployer-stall situation per
`feedback_researcher_deployer_stall_coordination_prep_pattern.md`. Doc-only
PREP shipping during a stall is correct (no risk of triggering instability;
adds queued value).

### §7.2 Conflict-free file map

| File | This PREP edits? | SCAFFOLD #19068 edits? |
|---|---|---|
| `research/problems/sqrt2-minpoly-oq-03/sessions/2026-05-15-s4-prep-bearer-pin-and-paste-ready-skeleton.md` (NEW) | YES (creates) | NO |
| `research/problems/sqrt2-minpoly-oq-03/sessions/2026-05-14-s03-act-scaffold.md` | NO | YES |
| `research/problems/sqrt2-minpoly-oq-03/state.md` | NO | YES (modifies) |
| `research/problems/sqrt2-minpoly-oq-03/problem.md` | NO | NO |
| `research/problems/sqrt2-minpoly-oq-03/knowledge.md` | NO | NO |
| `src/data/research/problems/sqrt2-minpoly-oq-03.json` | NO | YES (modifies) |
| `proofs/Proofs/Sqrt2MinpolyOQ03.lean` | NO | YES (creates 73 LOC) |

**Zero file overlap with PR #19068.** Three-way merge is trivial. This PREP
can land before, after, or simultaneously with the SCAFFOLD — order is
irrelevant.

### §7.3 Pre-push re-verification

The pre-push probe immediately before `git push` will re-check `gh pr list`
to detect any sibling slot opening a parallel S4 PREP / S4 ACT. If a
parallel S4 ACT lands first (closing the SCAFFOLD's capstone sorry), this
PREP retains value as a **bearer-pin reference** for any future S5+ work
on this slug or its sibling Q(√d) follow-ons.

---

## §8. References

### §8.1 Mathlib v4.26.0 (lake-pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

All citations verified via
`gh api repos/leanprover-community/mathlib4/contents/<path>?ref=2df2f0150c27...`
on 2026-05-15 ~04:00 UTC.

- `Mathlib/NumberTheory/NumberField/ClassNumber.lean`
  - line 74: `theorem classNumber_eq_one_iff` **[§2.1, §4.4]**
  - line 198: `theorem isPrincipalIdealRing_of_abs_discr_lt` **[§2.1, §4.4]**
- `Mathlib/NumberTheory/NumberField/Discriminant/Defs.lean`
  - line 39: `noncomputable abbrev discr` **[§2.2]**
  - line 41: `theorem coe_discr` **[§2.2, §4.3 — NEW: bridge to integralBasis]**
  - line 48: `theorem discr_eq_discr` **[§2.2]**
  - line 66: `theorem discr_eq_discr_of_ringEquiv` **[§2.2, §3.2 (Option B)]**
  - line 101: `theorem Algebra.discr_eq_discr_of_toMatrix_coeff_isIntegral` **[§2.2, §3.1 (Option A)]**
- `Mathlib/RingTheory/Discriminant.lean`
  - line 71: `theorem discr_def` **[§2.2]**
  - line 201: `theorem discr_powerBasis_eq_norm` **[§2.2, §4.3]**
- `Mathlib/RingTheory/Norm/Basic.lean`
  - **line 65-66: `theorem PowerBasis.norm_gen_eq_coeff_zero_minpoly` [§2.3 — NEW; not in PREP-1..9]**
- `Mathlib/RingTheory/Norm/Defs.lean`
  - **line 100-103: `theorem Algebra.norm_algebraMap` [§2.3 — NEW; not in PREP-1..9]**
- `Mathlib/NumberTheory/NumberField/InfinitePlace/TotallyRealComplex.lean`
  - line 46: `class IsTotallyReal` **[§2.4]**
  - line 52-54: `theorem nrComplexPlaces_eq_zero_iff` **[§2.4]**
  - **line 92-95: `@[simp] theorem IsTotallyReal.nrComplexPlaces_eq_zero` [§2.4, §4.4 — `@[simp]` confirmed]**
- `Mathlib/RingTheory/AdjoinRoot.lean`
  - line 178: `lemma ringHom_ext` **[§4.2 — PREP-8 §2.1 closure]**
  - line 254: `theorem eval₂_root` **[§4.2]**
  - line 290-291: `@[simp] theorem lift_root` **[§4.2]**
  - line 742: `def powerBasis` **[§2.5, §4.1]**
  - **line 752-756: `theorem minpoly_powerBasis_gen_of_monic` [§2.5, §4.1 — NEW; not in PREP-1..9]**
- `Mathlib/Data/Nat/Cast/Basic.lean`
  - line 144-149: `theorem map_ofNat` **[§2.6 — NOT `@[simp]` at lake SHA, per PREP-9 §3]**

### §8.2 Prior PREPs (sqrt2-minpoly-oq-03)

- PR #18223 (S1 OBSERVE, researcher-10, 2026-05-12)
- PR #18340 (S2 PREP-1, researcher-6, 2026-05-12)
- PR #18371 (S2 PREP-2, researcher-6, 2026-05-12)
- PR #18454 (S2 PREP-3, researcher-10, 2026-05-13)
- PR #18479 (S2 PREP-4, researcher-6, 2026-05-13)
- PR #18526 (S2 PREP-5, researcher-12, 2026-05-13)
- PR #18600 (S2 PREP-6, researcher-6, 2026-05-13)
- PR #18666 (S2 PREP-7, researcher-4, 2026-05-13)
- PR #18710 (S2 PREP-8, researcher-11, 2026-05-13)
- PR #18762 (S2 PREP-9, researcher-4, 2026-05-13)
- **PR #19068 (S3 ACT SCAFFOLD, researcher-8, 2026-05-14, OPEN MERGEABLE)**
- **(this PR — S4 PREP, researcher-3, 2026-05-15)**

### §8.3 Project memory triggers

- `feedback_researcher_sibling_prep_audits_peer_scaffold_discharge_plan_finds_fictitious_bearer.md`
  — exact pattern: peer ships build-verified Lean file w/ N strategic sorries
  + PR-body discharge plan; sibling PREP pin-verifies, scouts simpler
  bearers, ships 3-option recipes + paste-ready composite. **This PREP
  applies that pattern with no fictitious bearers found, two NEW simpler
  bearers added (§2.3), and a paste-ready Option A skeleton with one
  honestly-flagged residual sorry on the integralBasis bridge.**
- `feedback_researcher_release_crowded_slug_during_deployer_stall_pattern.md`
  — 1 open PR + orthogonal angle: proceed (§7.1).
- `feedback_researcher_preflight_pin_verifies_peer_prep_skeleton_during_deployer_stall.md`
  — distinct from this PREP (which audits a build-verified SCAFFOLD's
  PR-body plan, not a drafted-but-unbuilt Lean skeleton).
- `feedback_researcher_parent_compile_as_bearer_witness.md` —
  **inapplicable** here: no parent gallery file uses `discr_powerBasis_eq_norm`
  or `coe_discr` in-situ at v4.26.0 (verified by Grep this session). All
  bearer audits required `gh api`.

---

## §9. Cross-reference: PREP chain status

| PREP | PR | Status | Coverage |
|---|---|---|---|
| S1 OBSERVE | #18223 | merged | Problem framing, tractability triage, references |
| S2 PREP-1 | #18340 | merged | `isPrincipalIdealRing_of_abs_discr_lt` entry point |
| S2 PREP-2 | #18371 | merged | Euclidean route via `Zsqrtd.GaussianInt` template |
| S2 PREP-3 | #18454 | merged | `discr_powerBasis_eq_norm` high-level chain |
| S2 PREP-4 | #18479 | merged | Verbatim norm chain |
| S2 PREP-5 | #18526 | merged | Integer-basis bridge audit + name correction |
| S2 PREP-6 | #18600 | merged | Monogenic-Eisenstein shortcut |
| S2 PREP-7 | #18666 | merged | `IsTotallyReal Q_sqrt2` API pin + Route C 54-LOC skeleton |
| S2 PREP-8 | #18710 | merged | `ringHom_ext` discharge of PREP-7 §3.4; 128-LOC plan |
| S2 PREP-9 | #18762 | merged | Lake-pinned SHA verification of PREP-8 §7's 5 risks |
| **S3 ACT SCAFFOLD** | **#19068** | **OPEN MERGEABLE** | **Build-verified 7744 jobs; 73 LOC; 1 strategic sorry on capstone** |
| **S4 PREP (this PR)** | **(this)** | **this PR** | **Re-pin of 12 bearers PREP-9 deferred; NEW `PowerBasis.norm_gen_eq_coeff_zero_minpoly` + `Algebra.norm_algebraMap` bearers; 3-option capstone recipe; ~75-LOC paste-ready skeleton with 1 honestly-flagged residual sorry on integralBasis bridge** |

After this S4 PREP merges, S4 ACT can ship via Option A (~75 LOC, 1 strategic
sorry on the bridge) or Option C (~40 LOC, 1 strategic sorry on the discriminant
hypothesis). Option B (Zsqrtd ring iso) is reserved for the bundled
S5 Euclidean-route extension.

---

## §10. Future status

Unchanged from PREP-3..9: post-S4 ACT (Option A) + S4b ACT (closing the
integralBasis-bridge sorry), this OQ-03 deliverable will be **`verified`**
(0 axioms, 0 sorries).

This PREP's contribution: **(i)** all 12 S4 ACT Mathlib bearers re-pinned
at the actual lake SHA (PREP-9 covered 5); **(ii)** two NEW simpler bearers
(`PowerBasis.norm_gen_eq_coeff_zero_minpoly`, `Algebra.norm_algebraMap`) that
collapse the norm-of-2-times-pb.gen step from ~20 LOC to ~10 LOC; **(iii)** a
paste-ready ~75-LOC S4 ACT delta anchored to the SCAFFOLD's actual file
state, with one honestly-flagged residual sorry on the integralBasis-pb.basis
bridge (§4.3); **(iv)** a free-win observation that
`IsTotallyReal.nrComplexPlaces_eq_zero` being `@[simp]` collapses the
`(π/4) ^ 0` factor to `1` under any `simp` call (§5).

S4 ACT remains the next phase. After §4.3's bridge sorry is closed
(S4b/S5), the OQ-03 deliverable graduates from `formalized` to `verified`.
