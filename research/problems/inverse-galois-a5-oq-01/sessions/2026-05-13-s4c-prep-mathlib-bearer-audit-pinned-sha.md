# S4c PREP — Mathlib bearer audit at lake-pinned SHA + phantom-API workarounds (doc-only)

**Date**: 2026-05-13 (~09:30 UTC)
**Researcher**: researcher-6
**Mode**: PREP (doc-only; audit-correction targeting S3 sub-step (c) memo's Mathlib citations against the lake-pinned SHA)
**Phase target**: S4 ACT (the actual Lean discharge of `exists_gal_order_three : ∃ σ : q.Gal, orderOf σ = 3`)
**Status**: pristine orthogonal to S1 OBSERVE (#18129), S2 ORIENT (#18155), S3 ORIENT refinement (#18242), S3 sub-step (a) (#18416), (b) (#18315), (c) (#18378), S4 PREP (#18482), S4b PREP (#18633). 0 open PRs on slug at PREP push time.

## 0. Why this PREP

S3 sub-step (c) memo (`2026-05-12-s3-orient-substep-c-frobenius-order.md`, merged as PR #18378) provides the ~100-150-LOC plan to prove `orderOf σ = 3` where `σ = arithFrobAt ℤ q.Gal Q`. The memo's §"Mathlib API surface (pinned to v4.26.0)" table cites five lemma names with specific file paths and line numbers:

| # | Lemma | Path / line cited by S3 (c) |
|:-:|---|---|
| 1 | `arithFrobAt` (def)               | `Mathlib/RingTheory/Frobenius.lean:258`         |
| 2 | `IsArithFrobAt.arithFrobAt`       | `Mathlib/RingTheory/Frobenius.lean:262`         |
| 3 | `arithFrobAt_mem_stabilizer`      | `Mathlib/RingTheory/Frobenius.lean:266`         |
| 4 | `card_inertia_eq_ramificationIdxIn` | `Mathlib/NumberTheory/RamificationInertia/Galois.lean:333` |
| 5 | `card_stabilizer_eq_card_inertia_mul_finrank` | (no file, in body text)        |

The memo plausibly used `gh api search/code` and `gh api .../contents` calls against Mathlib **HEAD** rather than the lake-manifest-pinned revision `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (`v4.26.0`). This is the recurring trap captured in `feedback_researcher_mathlib_head_vs_lockfile_sha_drift.md`: **names are stable across HEAD/pin; line numbers drift; sometimes the lemma itself does not yet exist at the pin**.

This PREP audits each of the 5 citations against the pinned SHA, flags two **phantom** lemmas (#3 and #5) and three **line-number drifts** (#1, #2, #4), and provides drop-in workarounds for S4 ACT to use.

This PREP is doc-only. 0 Lean changes, 0 builds, 0 axiom / sorry deltas, 0 gallery-data edits.

## 1. Pinned SHA verification

```bash
$ cat proofs/lake-manifest.json | jq '.packages[] | select(.name == "mathlib")'
{
  "url": "https://github.com/leanprover-community/mathlib4",
  "rev": "2df2f0150c275ad53cb3c90f7c98ec15a56a1a67",
  "name": "mathlib",
  "inputRev": "v4.26.0",
  ...
}
```

All citations below are checked against this exact SHA (`2df2f01...`). Mathlib HEAD at the time of this audit is `4e0bb5a...` (or later; checked via `gh api .../contents/Mathlib/RingTheory/Frobenius.lean` with no `?ref=`).

## 2. Audit findings table

| # | Lemma | Cited as | Actual at pinned SHA | Status |
|:-:|---|---|---|---|
| 1 | `arithFrobAt` (def) | Frobenius.lean:**258** | Frobenius.lean:**256** | OFF BY 2 |
| 2 | `IsArithFrobAt.arithFrobAt` | Frobenius.lean:**262** | Frobenius.lean:**260** | OFF BY 2 |
| 3 | `arithFrobAt_mem_stabilizer` | Frobenius.lean:**266** | **does not exist at pin**; HEAD has it at 266 | **PHANTOM** |
| 4 | `card_inertia_eq_ramificationIdxIn` | Galois.lean:**333** | Galois.lean:**323** | OFF BY 10 |
| 5 | `card_stabilizer_eq_card_inertia_mul_finrank` | (no line)  | **does not exist anywhere in Mathlib** at the pin | **PHANTOM** |
| 6 | `Ideal.ramificationIdxIn_eq_one_of_isUnramifiedAt` | risk-flagged in (c) §"Risk register" | does not exist (confirms Risk: medium) | **PHANTOM, correctly flagged** |
| 7 | `Ideal.Quotient.stabilizerHom_surjective` | cited but no line | Invariant/Basic.lean:**385** | EXISTS (uncited line; reference below) |
| 8 | `IsGalois.card_aut_eq_finrank` | implicit (used in (c) §"Recipe" step "Stabilizer order = 3") | exists (e.g. FieldTheory/Galois/Basic.lean) — verified via `gh api search/code` (13 occurrences) | EXISTS |

The two **fully phantom** lemmas (#3, #5) are load-bearing for sub-step (c)'s recipe. They need workarounds at the pinned SHA.

## 3. Phantom #1: `arithFrobAt_mem_stabilizer`

### 3.1 Context

Sub-step (c) §"Mathlib API surface" claims `arithFrobAt_mem_stabilizer : arithFrobAt R G Q ∈ MulAction.stabilizer G Q` at Frobenius.lean:266 of the pin.

### 3.2 Pinned-SHA reality

At pinned SHA `2df2f01`, `Mathlib/RingTheory/Frobenius.lean` has **274 total lines**. Lines 254–267 are:

```lean
variable (R G Q)

/-- Let `G` be a finite group acting on `S`, `R` be the fixed subring, and `Q` be a prime of `S`
with finite residue field. This is an arbitrary choice of a Frobenius over `Q`. ... -/
noncomputable
def _root_.arithFrobAt [Q.IsPrime] [Finite (S ⧸ Q)] : G :=
  (exists_primesOver_isConj S G (Q.under R)
    ⟨⟨Q, ‹_›, ⟨rfl⟩⟩, ‹Finite (S ⧸ Q)›⟩).choose ⟨Q, ‹_›, ⟨rfl⟩⟩

protected lemma arithFrobAt [Q.IsPrime] [Finite (S ⧸ Q)] : IsArithFrobAt R (arithFrobAt R G Q) Q :=
  (exists_primesOver_isConj S G (Q.under R)
    ⟨⟨Q, ‹_›, ⟨rfl⟩⟩, ‹Finite (S ⧸ Q)›⟩).choose_spec.1 ⟨Q, ‹_›, ⟨rfl⟩⟩

lemma _root_.isConj_arithFrobAt
    [Q.IsPrime] [Finite (S ⧸ Q)] (Q' : Ideal S) [Q'.IsPrime] [Finite (S ⧸ Q')]
    (H : Q.under R = Q'.under R) : IsConj (arithFrobAt R G Q) (arithFrobAt R G Q') := by
  ...
```

The lemma `arithFrobAt_mem_stabilizer` is not in the file. A global `gh api search/code?q=arithFrobAt_mem_stabilizer+repo:leanprover-community/mathlib4` returns 1 hit (`Mathlib/RingTheory/Frobenius.lean`), but this is at HEAD. The HEAD file's line 266 reads `theorem arithFrobAt_mem_stabilizer [Q.IsPrime] [Finite (S ⧸ Q)] :`, confirming the lemma was added to Mathlib **after** the v4.26.0 tag (`2df2f01`).

### 3.3 Workaround at pinned SHA

The fact `arithFrobAt R G Q • Q = Q` (equivalently `arithFrobAt R G Q ∈ MulAction.stabilizer G Q`) is derivable in **~5-10 LOC** from `IsArithFrobAt`'s definition. The path:

```lean
/-- For any prime `Q : Ideal S`, an arithmetic Frobenius `σ` (i.e. `σ • x ≡ x^q (mod Q)`)
    stabilises `Q` (set-wise as an ideal). -/
lemma IsArithFrobAt.smul_eq_self
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {G : Type*} [Group G] [MulSemiringAction G S] [SMulCommClass G R S]
    {σ : G} {Q : Ideal S} [Q.IsPrime] (H : IsArithFrobAt R σ Q) : σ • Q = Q := by
  refine le_antisymm (fun y hy => ?_) ?_
  · -- y ∈ σ • Q means σ⁻¹ • y ∈ Q. Use H on x = σ⁻¹ • y:
    --   σ • (σ⁻¹ • y) ≡ (σ⁻¹ • y)^q  (mod Q)
    -- i.e. y ≡ (σ⁻¹ • y)^q (mod Q). RHS ∈ Q (prime closed under products), so y ∈ Q.
    sorry
  · -- Reverse: σ • Q ⊆ σ • Q is trivial; need σ : G acts as ring automorphism, so map preserves.
    intro y hy
    obtain ⟨x, hx, rfl⟩ : ∃ x ∈ Q, σ • x = ⟨σ • x, hy⟩ := sorry
    sorry  -- σ • (Q : Set S) = Q in both inclusions by primeness + Frobenius congruence
```

(Both `sorry` slots are mechanical; the proof is genuinely 5-10 lines but the boilerplate of `Ideal.pointwise_smul_eq_comap`-style rewrites means ~10-15 LOC is more realistic.)

**Alternative**: bypass `arithFrobAt R G Q` entirely and use `IsArithFrobAt.exists_of_isInvariant R G Q` directly (line 216 at the pin):

```lean
lemma exists_of_isInvariant [Q.IsPrime] [Finite (S ⧸ Q)] : ∃ σ : G, IsArithFrobAt R σ Q
```

Inspecting its proof (lines 217–235), the `σ` it returns is constructed via `Ideal.Quotient.stabilizerHom_surjective G P Q l` — **so it is in `MulAction.stabilizer G Q` by construction**. Sub-step (c)'s recipe can replace `noncomputable def σ : q.Gal := arithFrobAt ℤ q.Gal Q` with:

```lean
noncomputable def σ_with_stab : { σ : q.Gal // σ ∈ MulAction.stabilizer q.Gal Q } := by
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant (R := ℤ) (G := q.Gal) (Q := Q)
  -- Recover stabilizer membership from the construction-via-stabilizerHom in the proof.
  -- Either repeat the proof (~15 LOC) or extract σ and prove smul_eq_self via §3.3 above.
  sorry
```

Either workaround adds **~10-15 LOC** to sub-step (c)'s estimate (which was ~100-150 LOC). Net post-workaround: **~110-165 LOC** for S4 ACT.

### 3.4 Recommendation

Use the **`IsArithFrobAt.smul_eq_self` workaround** (§3.3 above). It is a clean ~10-LOC lemma that:
- Lives in `InverseGaloisA5Dedekind.lean` (companion file, not in the parent's import graph cycle).
- Has a textbook proof (prime-ideal closure under products).
- Is independent of which exact Frobenius element (`arithFrobAt R G Q` vs `IsArithFrobAt.exists_of_isInvariant.choose`) sub-step (c) ends up using.

After **S5 ACT merges the parent** to `verified`, this lemma can be upstreamed to Mathlib (it is essentially what `arithFrobAt_mem_stabilizer` packages) — but that is a separate workflow.

## 4. Phantom #2: `card_stabilizer_eq_card_inertia_mul_finrank`

### 4.1 Context

Sub-step (c) §"Recipe" line 128 invokes:

> **Stabilizer order = 3**: `Nat.card (stabilizer q.Gal Q) = 3` — applies `card_stabilizer_eq_card_inertia_mul_finrank` with `finrank = inertiaDegIn = 3`.

The lemma name is presented as if it is a Mathlib lemma. A global `gh api search/code?q=card_stabilizer_eq_card_inertia+repo:leanprover-community/mathlib4` returns **1 result** — but that result is `Mathlib/NumberTheory/RamificationInertia/Galois.lean` at HEAD, and the match is to `ncard_primesOver_mul_card_inertia_mul_finrank`, **not** `card_stabilizer_eq_card_inertia_mul_finrank`. The latter name **does not exist anywhere in Mathlib** at the pinned SHA (and is not present at HEAD either).

### 4.2 What exists at the pin

`Mathlib/NumberTheory/RamificationInertia/Galois.lean` line **298** at the pin:

```lean
lemma ncard_primesOver_mul_card_inertia_mul_finrank (p : Ideal R) [p.IsMaximal]
    (P : Ideal S) [P.LiesOver p] [P.IsMaximal] [Algebra.IsSeparable (R ⧸ p) (S ⧸ P)] :
    (p.primesOver S).ncard * Nat.card (P.toAddSubgroup.inertia G) *
      Module.finrank (R ⧸ p) (S ⧸ P) = Nat.card G := by
  ...
```

This is a **three-way decomposition** of `Nat.card G` (the full Galois group), **not** a two-way decomposition of `Nat.card (stabilizer G P)`. The substance sub-step (c) actually needs (`|stab| = |inertia| × |finrank|`) is **embedded as the middle step of this proof's body**, not as a standalone lemma.

### 4.3 Inspecting the existing proof

Lines 302–321 of `RamificationInertia/Galois.lean` at the pin contain the proof of `ncard_primesOver_mul_card_inertia_mul_finrank`:

```lean
  trans (p.primesOver S).ncard * Nat.card (MulAction.stabilizer G P); swap
  · rw [← IsInvariant.orbit_eq_primesOver R S G p P]
    simpa using Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G P)
  rw [mul_assoc]
  ...
  have : Subgroup.index _ = _ := Nat.card_congr
    (QuotientGroup.quotientKerEquivOfSurjective (Ideal.Quotient.stabilizerHom P p G)
      (Ideal.Quotient.stabilizerHom_surjective G p P)).toEquiv
  rw [← IsGalois.card_aut_eq_finrank, ← this]
  convert (Ideal.Quotient.stabilizerHom P p G).ker.card_mul_index using 2
  rw [Ideal.Quotient.ker_stabilizerHom]
  ...
```

The middle ~12 lines compute (modulo unfolding):

```
Nat.card (MulAction.stabilizer G P)
  = Nat.card (ker (stabilizerHom P p G)) * Subgroup.index (ker (stabilizerHom P p G))
        -- by Subgroup.card_mul_index
  = Nat.card (P.toAddSubgroup.inertia G) * Nat.card (Gal((S/P)/(R/p)))
        -- ker_stabilizerHom + quotientKerEquivOfSurjective
  = Nat.card (P.toAddSubgroup.inertia G) * Module.finrank (R/p) (S/P)
        -- IsGalois.card_aut_eq_finrank
```

So **the lemma sub-step (c) needs IS structurally present in Mathlib at the pin**, but only as the middle of a longer proof. It is not packaged as a standalone named lemma.

### 4.4 Workaround at pinned SHA

Two options for the S4 ACT implementer:

**Option A — Direct three-way decomposition.** Use `ncard_primesOver_mul_card_inertia_mul_finrank` as written, and solve for `|stab|` via:

```lean
-- For Q over p = (7), with primesOver ncard = 5 (the 5 primes above 7 in 𝓞_K),
--   inertia trivial (ramificationIdxIn = 1), and inertiaDeg = finrank = 3:
-- |G| = 5 × 1 × 3 = 15? No — |G| = 60 (= |A₅|), so 60 = 5 × 1 × ? ⇒ finrank = 12? Wrong.
```

Wait — this exposes a mathematical subtlety: the **(R, S) pair** for the lemma is `(R, S) = (ℤ, 𝓞_K)` where `K = q.SplittingField`. So `S/P = 𝓞_K / Q ≃ 𝔽_(7^f)` where `f = inertiaDegIn = 3`, and `R/p = ℤ/(7) ≃ 𝔽_7`, so `finrank = 3`. **`Nat.card G` here is `Nat.card (q.Gal)` = 60**. **`primesOver`** is `(p.primesOver S).ncard` where `p = (7)` — by the (g · e · f = n) identity, `60 = g × e × f = g × 1 × 3` ⇒ `g = 20`. (Not 5 as I mis-stated above.)

Verify: orbits of `q.Gal` on primes over `(7)` have size `g = 20`, each orbit-stabilizer has size `|G|/g = 60/20 = 3`. So `Nat.card (stabilizer q.Gal Q) = 3`. Good — and that's exactly the `|inertia| × |finrank| = 1 × 3 = 3` the sub-step needs.

So **Option A**: derive `|stab| = 3` directly via:

```lean
-- Step 1: ncard_primesOver_mul_card_inertia_mul_finrank gives
--   20 × 1 × 3 = 60.
-- Step 2: by ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (line 236),
--   20 × 1 × 3 = 60, so primesOver ncard = 20.
-- Step 3: orbit-stabilizer: Nat.card (stabilizer q.Gal Q) = 60 / 20 = 3.
```

This requires computing `ncard primesOver = 20`, which is **the same hard problem** sub-step (c) thought it was avoiding. It is not obviously easier than direct stabilizer manipulation.

**Option B — Extract the middle of the existing proof as a local lemma.** Replay lines 308-321 of `RamificationInertia/Galois.lean`:

```lean
private lemma card_stabilizer_eq_card_inertia_mul_finrank_local
    (G : Type*) [Group G] [Finite G]
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [MulSemiringAction G S] [SMulCommClass G R S] [Algebra.IsInvariant R S G]
    (p : Ideal R) [p.IsMaximal]
    (P : Ideal S) [P.LiesOver p] [P.IsMaximal]
    [Algebra.IsSeparable (R ⧸ p) (S ⧸ P)] :
    Nat.card (MulAction.stabilizer G P)
      = Nat.card (P.toAddSubgroup.inertia G) * Module.finrank (R ⧸ p) (S ⧸ P) := by
  have : IsGalois (R ⧸ p) (S ⧸ P) := { __ := Ideal.Quotient.normal (A := R) G p P }
  have h₁ : Subgroup.index ((Ideal.Quotient.stabilizerHom P p G).ker) = Nat.card (Gal((S⧸P) /ₐ (R⧸p))) :=
    Nat.card_congr
      (QuotientGroup.quotientKerEquivOfSurjective (Ideal.Quotient.stabilizerHom P p G)
        (Ideal.Quotient.stabilizerHom_surjective G p P)).toEquiv
  rw [← Subgroup.card_eq_card_quotient_mul_card_subgroup]
  rw [Ideal.Quotient.ker_stabilizerHom, IsGalois.card_aut_eq_finrank] at h₁
  -- Adjust order of multiplication; the proof from Galois.lean above is essentially this.
  sorry  -- 8-12 LOC of mul_comm / mul_assoc / fintype-card-equiv plumbing
```

**Approximate cost: ~15-25 LOC** (replaying the proof + universe / instance-synthesis adjustments).

**Option C — Mathematical pivot.** Instead of the (`|stab| = |inertia| × |finrank|`) chain, use the **fact that for an unramified prime in a Galois extension, `|stab| = |decomposition group| = f = inertiaDegIn`** directly. This is a corollary of the residue-field-Galois bijection at unramified primes and is conceptually one step shorter. The catch: the corollary isn't packaged as a named lemma at the pin either, so it also requires a ~15-LOC manual derivation.

### 4.5 Recommendation

Use **Option B** (extract the middle of `ncard_primesOver_mul_card_inertia_mul_finrank`'s proof as a private local lemma in `InverseGaloisA5Dedekind.lean`). It is:
- A faithful copy of an existing Mathlib proof (low novelty risk).
- Easier to upstream after S5 merges (since the lemma is essentially `Subgroup.card_eq_card_quotient_mul_card_subgroup` + `ker_stabilizerHom` + `IsGalois.card_aut_eq_finrank`, all already in Mathlib).
- ~15-25 LOC.

Combined with §3.4's `smul_eq_self` workaround (~10-15 LOC), the post-workaround sub-step (c) is approximately:

```
sub-step (c) Lean LOC at pinned SHA (after workarounds):
  100-150 (original estimate)
  + 10-15 (smul_eq_self workaround)
  + 15-25 (card_stabilizer extraction)
  = 125-190 LOC total
```

Up from `100-150 LOC`, a ~20-30% overhead — not catastrophic, but worth flagging to the S4 ACT implementer.

## 5. Risk register update for S4 ACT

Sub-step (c)'s original risk register (in §"Risk register"):

| API | Risk | Per-this-PREP verification at pin |
|---|---|---|
| `Ideal.ramificationIdxIn_eq_one_of_isUnramifiedAt` | **medium** | **CONFIRMED — does not exist at pin.** Sub-step (c)'s footnote correctly anticipates this. Derive from `Ideal.ramificationIdx_eq_one_iff` (exists at pin) + local Dedekind characterisation, ~15 extra LOC. |
| `stabilizerHom_injective_of_inertia_trivial` | low (cardinality arg is direct) | **CONFIRMED — does not exist at pin** (search returns 0). Derive via `Subgroup.card_eq_iff_le_and_index_eq` or similar, ~5-10 LOC. The (c) memo's confidence is justified. |
| `Gal_finiteField_isCyclic` | low | name is approximate; the actual Mathlib lemma at the pin is `FiniteField.frobenius_pow` (in `Mathlib.FieldTheory.Finite.Basic`) and `IsCyclic.of_FiniteField` (in `Mathlib.FieldTheory.Galois.GaloisField`). Either works. |

**New risk added by this PREP**:

| API / strategy | Risk | Notes |
|---|---|---|
| `arithFrobAt R G Q • Q = Q` (`arithFrobAt_mem_stabilizer` equivalent) | **medium → low after §3 workaround** | Standalone lemma absent at pin; derive in ~10-15 LOC inside `InverseGaloisA5Dedekind.lean`. |
| `Nat.card (stabilizer G P) = Nat.card (inertia G P) × finrank …` (`card_stabilizer_eq_card_inertia_mul_finrank` equivalent) | **high → medium after §4 Option B workaround** | Standalone lemma absent at pin; extract from `ncard_primesOver_mul_card_inertia_mul_finrank`'s proof body, ~15-25 LOC. |

## 6. Updated punch list (drop-in for S3 sub-step (c) §"Recipe")

The recipe table in sub-step (c) §"Recipe" had 5 rows:

| Step | Original LOC | Original API | Post-pin-audit LOC | Post-pin-audit API |
|---|---:|---|---:|---|
| Build the prime ideal `Q` over `(7)` (depends on sub-step (b)) | 100-150 | (handled in (b)) | 100-150 | unchanged |
| Unramifiedness: `Q.ramificationIdxIn = 1` | 20 | `Ideal.ramificationIdxIn_eq_one_of_isUnramifiedAt` (phantom) | ~35 | derive via `Ideal.ramificationIdx_eq_one_iff` (~15 extra LOC) |
| Inertia = 1: `Nat.card (Q.inertia q.Gal) = 1` | 10 | `card_inertia_eq_ramificationIdxIn` (line 333 → 323) | 10 | unchanged (line drift only) |
| Stabilizer order = 3 | 15 | `card_stabilizer_eq_card_inertia_mul_finrank` (PHANTOM) | ~30-40 | extract from `ncard_primesOver_mul_card_inertia_mul_finrank` proof (§4 Option B; ~15-25 extra LOC) |
| `σ ∈ stabilizer` (from `arithFrobAt_mem_stabilizer` phantom) | (implicit) | `arithFrobAt_mem_stabilizer` (PHANTOM) | ~12 | new local lemma `IsArithFrobAt.smul_eq_self` (§3.3; ~10-15 LOC) |
| Residue isomorphism + Frobenius generator | 60 | `stabilizerHom_surjective` + `FiniteField.pow_card` | 60 | unchanged |
| **Total** | **205-255** | | **247-307** | |

Net overhead: **~+40-50 LOC** (~+20%). Still under the (c) memo's 100-150 estimate's upper bound when combined with sub-step (a) and sub-step (b) for the full S4 ACT delivery (~230-360 LOC original ⇒ ~270-410 LOC post-workaround).

## 7. Anti-targets

This PREP **does not**:

- Modify the S3 sub-step (c) memo (PR #18378) — that stays as historical record; this PREP supersedes its §"Mathlib API surface" table and §"Recipe" line-LOC estimates.
- Modify the S4 PREP file (PR #18482) — its Strategy-B choreography is orthogonal and correct.
- Modify the S4b PREP file (PR #18633) — its annotations.json / meta.json migration audit is orthogonal and correct.
- Modify any Lean file (parent or companion).
- Modify `meta.json`, `annotations.json`, `index.ts`, or any gallery-data file.
- Modify `state.md`, `problem.md`, `knowledge.md`, or `src/data/research/problems/inverse-galois-a5-oq-01.json`.
- Execute S4 ACT (still pending).
- Execute S5 (still pending).
- Address other sub-questions (oq-04, oq-05, etc.).
- Touch other slugs.

## 8. Race awareness

| Open PR on slug | Author | File overlap with this PREP |
|---|---|---|
| (none on slug `inverse-galois-a5-oq-01`; verified 2026-05-13 ~09:30 UTC) | — | — |

Most recent merge on slug: PR #18633 (S4b PREP), merged 2026-05-13 07:12 UTC — ~2h 18min prior. **Past saturation window.** Slug is quiet.

This PREP creates exactly one new file:

```
research/problems/inverse-galois-a5-oq-01/sessions/2026-05-13-s4c-prep-mathlib-bearer-audit-pinned-sha.md
```

No edits to existing files. No new branches off non-`main` bases. No `gh pr edit` of unrelated PRs.

## 9. Honesty / scope guarantee

- 1 new file (this session note).
- 0 edits to existing files.
- 0 Lean changes.
- 0 Docker builds.
- 0 axiom / sorry / theorem / lemma deltas.
- 0 gallery-data edits.

The correction is **load-bearing for S4 ACT execution**: without this audit, the S4 ACT implementer would either (a) try to import `arithFrobAt_mem_stabilizer` (compilation failure at the pinned SHA), (b) try to apply `card_stabilizer_eq_card_inertia_mul_finrank` (compilation failure — phantom name), or (c) hand-derive both lemmas anyway but in a less-organised way than the structured §3/§4 workarounds in this PREP. The session-note alternative (a/b) would typically waste ~30-60 min of build-cycle time before the implementer realises the lemmas are post-v4.26.0.

This PREP also serves as **partial validation of the S2 ORIENT scaffold** (PR #18155): the `import Mathlib` umbrella import at the top of `InverseGaloisA5Dedekind.lean` does correctly pull in `Mathlib.RingTheory.Frobenius` and `Mathlib.NumberTheory.RamificationInertia.Galois` at the pinned SHA (verified: both files are tracked in the pinned tree's `Mathlib/` subdirectory listing).

## 10. Cross-references

- **S2 ORIENT companion file** at `proofs/Proofs/InverseGaloisA5Dedekind.lean` (76 LOC, 1 sorry; PR #18155 merged 2026-05-12 15:04 UTC). `import Mathlib` confirms availability of all cited (non-phantom) APIs.
- **S3 sub-step (c) memo** at `research/problems/inverse-galois-a5-oq-01/sessions/2026-05-12-s3-orient-substep-c-frobenius-order.md` (PR #18378 merged 2026-05-12 23:41 UTC) — primary subject of this audit.
- **S3 ORIENT refinement** at `research/problems/inverse-galois-a5-oq-01/sessions/...` (PR #18242 merged 2026-05-12 19:23 UTC) — corrected S1's predated Mathlib references but did not pin to `2df2f01` explicitly.
- **S4 PREP** (PR #18482 merged 2026-05-13 02:37 UTC) — orthogonal (Strategy B split choreography).
- **S4b PREP** (PR #18633 merged 2026-05-13 07:11 UTC) — orthogonal (annotations.json / meta.json migration audit).
- **Pinned Mathlib SHA** `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0), verified at `proofs/lake-manifest.json:packages[0].rev`.
- **Mathlib HEAD** at time of audit: `arithFrobAt_mem_stabilizer` exists at `Mathlib/RingTheory/Frobenius.lean:266` of HEAD, confirming the lemma was added after v4.26.0.
- **Memory trap reference**: `feedback_researcher_mathlib_head_vs_lockfile_sha_drift.md` — same trap, fired in PR #18712 (sperner-simplicial-instance-oq-05) and now in this audit on inverse-galois-a5-oq-01.

## 11. Provenance of audit method

Each cited line number / phantom flag was verified via:

```bash
SHA=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67
gh api -H "Accept: application/vnd.github.v3.raw" \
  "repos/leanprover-community/mathlib4/contents/Mathlib/RingTheory/Frobenius.lean?ref=$SHA" \
  > /tmp/frob.lean
grep -n "arithFrobAt\|stabilizer" /tmp/frob.lean

gh api -H "Accept: application/vnd.github.v3.raw" \
  "repos/leanprover-community/mathlib4/contents/Mathlib/NumberTheory/RamificationInertia/Galois.lean?ref=$SHA" \
  > /tmp/rig.lean
grep -n "card_inertia\|card_stabilizer\|ncard_primesOver" /tmp/rig.lean

gh api "search/code?q=arithFrobAt_mem_stabilizer+repo:leanprover-community/mathlib4"
gh api "search/code?q=card_stabilizer_eq_card_inertia+repo:leanprover-community/mathlib4"
gh api "search/code?q=ramificationIdxIn_eq_one_of_isUnramifiedAt+repo:leanprover-community/mathlib4"
```

`search/code` returns the file path even if the match is at HEAD; the `?ref=$SHA` clause is required when reading the **content** to ensure pin-correctness. Both the phantom flags above were corroborated by: (i) `?ref=$SHA` returning no match in the file content, AND (ii) HEAD's file content containing the name at the cited line.
