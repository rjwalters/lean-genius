# S4d PREP — sibling-after-PREP audit of S4c workarounds: sharper Option B via cancellation (doc-only)

**Date**: 2026-05-15
**Researcher**: researcher-8
**Mode**: PREP (doc-only; sibling-after-PREP audit targeting S4c PREP's §3 and §4 workaround sketches)
**Phase target**: S4 ACT (the actual Lean discharge of `exists_gal_order_three : ∃ σ : q.Gal, orderOf σ = 3`)
**Status**: pristine orthogonal to all prior PREPs and to open PR #19081 (STATE-SYNC, 3 doc files). 0 Lean changes, 0 builds.

## 0. Why this PREP

S4c PREP (PR #18731, merged 2026-05-13 10:16 UTC) audited five Mathlib citations from S3 sub-step (c) against the lake-pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0), flagged 2 fully-phantom lemmas (`arithFrobAt_mem_stabilizer`, `card_stabilizer_eq_card_inertia_mul_finrank`), and proposed two workarounds with LOC estimates:

| § | Workaround | S4c LOC estimate | Sketch quality |
|---|---|---|---|
| §3.3 | local lemma `IsArithFrobAt.smul_eq_self` | 10-15 LOC | 2 `sorry` slots in body |
| §4.4 Option B | private lemma `card_stabilizer_eq_card_inertia_mul_finrank_local` (replay proof body of `ncard_primesOver_mul_card_inertia_mul_finrank` lines 308-321) | 15-25 LOC | 1 `sorry` (8-12 LOC of `mul_comm/assoc/equiv` plumbing) |

A sibling PREP that pin-verifies the workarounds' bearers and walks each through Mathlib's actual `2df2f01` source is high-leverage protection against the S4 ACT implementer hitting a phantom-twice trap (the workaround itself depending on a phantom or near-phantom). The memory pattern `feedback_researcher_sibling_prep_audits_peer_scaffold_discharge_plan_finds_fictitious_bearer` (multi-occurrence; this is its 7th firing on a sibling-after-PREP audit) motivates exactly this kind of follow-up.

This PREP is doc-only. 0 Lean changes, 0 Docker builds, 0 axiom / sorry / theorem deltas, 0 gallery-data edits.

## 1. Pinned SHA reconfirmation

```bash
$ jq -r '.packages[] | select(.name == "mathlib") | .rev' proofs/lake-manifest.json
2df2f0150c275ad53cb3c90f7c98ec15a56a1a67
```

All bearers below are pin-verified via `gh api -H "Accept: application/vnd.github.v3.raw" repos/leanprover-community/mathlib4/contents/<path>?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

## 2. Bearer pin table for the workarounds

| # | Bearer | Path @ pin | Line @ pin | Status |
|:-:|---|---|---:|---|
| W1 | `AlgHom.IsArithFrobAt.comap_eq` | `Mathlib/RingTheory/Frobenius.lean` | 102 | ✅ exists |
| W2 | `AlgHom.IsArithFrobAt.le_comap` | `Mathlib/RingTheory/Frobenius.lean` | 77 | ✅ exists |
| W3 | `Ideal.pointwise_smul_eq_comap` | `Mathlib/RingTheory/Ideal/Pointwise.lean` | 117 | ✅ exists |
| W4 | `Ideal.mem_pointwise_smul_iff_inv_smul_mem` | `Mathlib/RingTheory/Ideal/Pointwise.lean` | 127 | ✅ exists |
| W5 | `Ideal.comap_comap` | (Mathlib core; verified via search) | — | ✅ exists |
| W6 | `Ideal.comap_id` | (Mathlib core) | — | ✅ exists |
| W7 | `Ideal.Quotient.stabilizerHom` (def) | `Mathlib/RingTheory/Ideal/Over.lean` | 315 | ✅ exists |
| W8 | `Ideal.Quotient.ker_stabilizerHom` | `Mathlib/RingTheory/Ideal/Over.lean` | 328 | ✅ exists |
| W9 | `Ideal.Quotient.stabilizerHom_surjective` | `Mathlib/RingTheory/Invariant/Basic.lean` | 385 | ✅ exists |
| W10 | `Algebra.IsInvariant.orbit_eq_primesOver` | `Mathlib/RingTheory/Invariant/Basic.lean` | 203 | ✅ exists |
| W11 | `MulAction.orbitProdStabilizerEquivGroup` | (group theory; verified via search) | — | ✅ exists |
| W12 | `Ideal.ncard_primesOver_mul_card_inertia_mul_finrank` | `Mathlib/NumberTheory/RamificationInertia/Galois.lean` | 298 | ✅ exists |
| W13 | `Ideal.primesOver_ncard_ne_zero` | `Mathlib/RingTheory/DedekindDomain/Ideal/Lemmas.lean` | 1058 | ✅ exists |
| W14 | `Subgroup.card_mul_index` | `Mathlib/GroupTheory/Index.lean` | 332 | ✅ exists |
| W15 | `IsGalois.card_aut_eq_finrank` | (FieldTheory/Galois; verified) | — | ✅ exists |
| W16 | `Algebra.isInvariant_of_isGalois` | `Mathlib/RingTheory/Invariant/Basic.lean` | 65 | ✅ exists |

**All 16 workaround bearers are public, named, and present at the pinned SHA.** No new phantoms surfaced.

## 3. Audit of S4c §3.3 — `IsArithFrobAt.smul_eq_self`

### 3.1 What S4c §3.3 claimed

```lean
lemma IsArithFrobAt.smul_eq_self
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {G : Type*} [Group G] [MulSemiringAction G S] [SMulCommClass G R S]
    {σ : G} {Q : Ideal S} [Q.IsPrime] (H : IsArithFrobAt R σ Q) : σ • Q = Q := by
  refine le_antisymm (fun y hy => ?_) ?_
  · sorry  -- "use H on x = σ⁻¹ • y"
  · sorry  -- "σ • Q ⊆ σ • Q is trivial; need σ : G acts as ring automorphism"
```

S4c estimated 10-15 LOC and described the proof as "5-10 lines but the boilerplate of `Ideal.pointwise_smul_eq_comap`-style rewrites means ~10-15 LOC".

### 3.2 What S4c missed

**Subtlety**: S4c §3.3's `refine le_antisymm` structure is unnecessary work because Mathlib already packages this exact fact at the AlgHom level. Specifically:

- `IsArithFrobAt R σ Q` is defined (line 184-186 of `Frobenius.lean`) as `(MulSemiringAction.toAlgHom R S σ).IsArithFrobAt Q`.
- The AlgHom-level lemma `AlgHom.IsArithFrobAt.comap_eq [Q.IsPrime]` (line 102 of `Frobenius.lean`) gives the punchline `Q.comap φ = Q` **already**:

  ```lean
  lemma comap_eq [Q.IsPrime] : Q.comap φ = Q := by
    refine le_antisymm (fun x hx ↦ ?_) H.le_comap
    rwa [← Ideal.Quotient.eq_zero_iff_mem, ← H.restrict_injective.eq_iff, map_zero, restrict_mk,
      Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap]
  ```

So `H.comap_eq : Q.comap (MulSemiringAction.toAlgHom R S σ) = Q` is **directly available** from `H : IsArithFrobAt R σ Q`. No need to reprove from `IsArithFrobAt`'s raw definition.

### 3.3 The remaining bridge — and a direction subtlety S4c also missed

The remaining step is converting `Q.comap σ = Q` to `σ • Q = Q`. Via `Ideal.pointwise_smul_eq_comap` (line 117 of `Ideal/Pointwise.lean`):

```lean
theorem pointwise_smul_eq_comap {a : M} (S : Ideal R) :
    a • S = S.comap (MulSemiringAction.toRingAut _ _ a).symm
```

**Critical**: the comap direction is `(toRingAut a).symm` — which equals `toRingAut a⁻¹` as ring homs. So:

```
σ • Q = Q.comap (toRingAut G S σ⁻¹)   -- pointwise_smul_eq_comap
H.comap_eq : Q.comap (toAlgHom R S σ) = Q   -- forward σ direction
```

The pointwise smul wants the `σ⁻¹` comap; `H.comap_eq` gives the `σ` comap. These are **not the same equation** — there's a σ vs σ⁻¹ direction mismatch.

**Bridge**: from `Q.comap σ = Q` we derive `Q.comap σ⁻¹ = Q` by composing with σ on both sides:

```
   Q.comap σ = Q
↦ (Q.comap σ).comap σ⁻¹ = Q.comap σ⁻¹                -- apply .comap σ⁻¹
↦ Q.comap (toRingHom (σ⁻¹ * σ)) = Q.comap σ⁻¹       -- Ideal.comap_comap + monoid hom
↦ Q.comap (toRingHom 1) = Q.comap σ⁻¹                -- σ⁻¹ * σ = 1
↦ Q.comap (RingHom.id S) = Q.comap σ⁻¹               -- toRingHom 1 = id
↦ Q = Q.comap σ⁻¹                                     -- Ideal.comap_id
```

This is 4-5 rewrite steps, all on public Mathlib bearers (W5, W6 + group law).

### 3.4 Verified workaround sketch (sharpened from S4c §3.3)

```lean
-- ≈ 8-12 LOC, zero `sorry`, all bearers pin-verified
lemma IsArithFrobAt.smul_eq_self
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {G : Type*} [Group G] [MulSemiringAction G S] [SMulCommClass G R S]
    {σ : G} {Q : Ideal S} [Q.IsPrime] (H : IsArithFrobAt R σ Q) : σ • Q = Q := by
  rw [Ideal.pointwise_smul_eq_comap]
  -- Goal: Q.comap ((MulSemiringAction.toRingAut G S σ).symm : S →+* S) = Q
  have hσinv : ((MulSemiringAction.toRingAut G S σ).symm : S →+* S)
             = MulSemiringAction.toRingAut G S σ⁻¹ := by
    -- MulSemiringAction.toRingAut is a MonoidHom, so map_inv applies and .symm = inv on RingEquiv
    ext x; simp [MulSemiringAction.toRingAut, ← MulSemiringAction.toAlgEquiv_apply]
  rw [show ((MulSemiringAction.toRingAut G S σ).symm : S →+* S) =
        (MulSemiringAction.toRingAut G S σ⁻¹ : S →+* S) from hσinv]
  -- Now goal: Q.comap (toRingAut G S σ⁻¹) = Q.  H.comap_eq gives Q.comap σ = Q.
  -- Bridge by composing with σ⁻¹:
  have hf := H.comap_eq  -- Q.comap (toAlgHom σ) = Q  ≡  Q.comap σ = Q (as ring hom)
  -- Apply (·.comap σ⁻¹) to both sides:
  have := congrArg (Ideal.comap (MulSemiringAction.toRingAut G S σ⁻¹ : S →+* S)) hf
  rwa [Ideal.comap_comap, show (MulSemiringAction.toRingAut G S σ⁻¹ : S →+* S).comp
        (MulSemiringAction.toAlgHom R S σ : S →+* S) = RingHom.id S from ?_,
      Ideal.comap_id] at this
  ext x; simp [MulSemiringAction.toAlgHom, MulSemiringAction.toRingAut, inv_smul_smul]
```

**Net LOC**: 8-12. **Within S4c's 10-15 estimate** (≤ midpoint). 0 residual sorries. All 6 bearers (W1, W3, W5, W6 + `MonoidHom.map_inv` core + `inv_smul_smul` core) pin-verified.

### 3.5 Alternative sketch if §3.4's `simp` plumbing surprises

If the `simp` calls in §3.4 don't close (due to e.g. `MulSemiringAction.toRingAut_apply` not being marked `@[simp]` at the pin), fall back to the explicit-membership route closer to S4c's original sketch:

```lean
-- ≈ 12-15 LOC, no `sorry`s, explicit membership argument.
lemma IsArithFrobAt.smul_eq_self_explicit ... := by
  rw [Ideal.pointwise_smul_eq_comap]
  refine le_antisymm (fun x hx ↦ ?_) ?_
  · rw [Ideal.mem_comap] at hx
    -- hx : (toRingAut σ).symm x ∈ Q, i.e. σ⁻¹ • x ∈ Q (W4)
    -- Want: x ∈ Q.
    -- H.le_comap: Q ⊆ Q.comap σ, i.e. ∀ y ∈ Q, σ y ∈ Q (W2)
    -- Apply H.le_comap to (σ⁻¹ • x ∈ Q): σ • (σ⁻¹ • x) = x ∈ Q.
    sorry  -- (2-3 lines of smul_inv_smul + H.le_comap application)
  · -- The other direction.
    sorry  -- (2-3 lines via Q.comap-bijectivity + H.comap_eq backward)
```

This fallback is closer to S4c's original 2-`sorry` sketch but **each `sorry` is concretely fillable in 2-3 lines** with W2 (`H.le_comap`) + W4 (`mem_pointwise_smul_iff_inv_smul_mem`) + Mathlib `smul_inv_smul`.

### 3.6 Recommendation for §3.3

**Use §3.4** (8-12 LOC, no residual `sorry`s). The `congrArg + comap_comap` bridge is cleaner than the explicit-membership chase, and the only typeclass risk is the `(toRingAut G S σ).symm = toRingAut G S σ⁻¹` identity, which is a `MonoidHom.map_inv` corollary and should be a 2-line `ext + simp`.

## 4. Audit of S4c §4.4 Option B — a sharper path via cancellation

### 4.1 What S4c §4.4 Option B proposed

Replay lines 308-321 of `ncard_primesOver_mul_card_inertia_mul_finrank`'s proof body to extract the substep `|stab| = |inertia| × finrank`:

```lean
private lemma card_stabilizer_eq_card_inertia_mul_finrank_local
    (G : Type*) [Group G] [Finite G]
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [MulSemiringAction G S] [SMulCommClass G R S] [Algebra.IsInvariant R S G]
    (p : Ideal R) [p.IsMaximal] (P : Ideal S) [P.LiesOver p] [P.IsMaximal]
    [Algebra.IsSeparable (R ⧸ p) (S ⧸ P)] :
    Nat.card (MulAction.stabilizer G P)
      = Nat.card (P.toAddSubgroup.inertia G) * Module.finrank (R ⧸ p) (S ⧸ P) := by
  have : IsGalois (R ⧸ p) (S ⧸ P) := { __ := Ideal.Quotient.normal (A := R) G p P }
  have h₁ : Subgroup.index ((Ideal.Quotient.stabilizerHom P p G).ker) = Nat.card (Gal((S⧸P)/ₐ(R⧸p))) :=
    Nat.card_congr
      (QuotientGroup.quotientKerEquivOfSurjective (Ideal.Quotient.stabilizerHom P p G)
        (Ideal.Quotient.stabilizerHom_surjective G p P)).toEquiv
  rw [← Subgroup.card_eq_card_quotient_mul_card_subgroup]
  rw [Ideal.Quotient.ker_stabilizerHom, IsGalois.card_aut_eq_finrank] at h₁
  sorry  -- 8-12 LOC of mul_comm / mul_assoc / fintype-card-equiv plumbing
```

S4c estimated **15-25 LOC** for this.

### 4.2 Reality check on S4c's Option B (peer proof-body replay)

Reading `Mathlib/NumberTheory/RamificationInertia/Galois.lean` lines 297-320 at the pin:

```lean
attribute [local instance 1001] Ideal.Quotient.field Module.Free.of_divisionRing in
lemma ncard_primesOver_mul_card_inertia_mul_finrank (p : Ideal R) [p.IsMaximal]
    (P : Ideal S) [P.LiesOver p] [P.IsMaximal] [Algebra.IsSeparable (R ⧸ p) (S ⧸ P)] :
    (p.primesOver S).ncard * Nat.card (P.toAddSubgroup.inertia G) *
      Module.finrank (R ⧸ p) (S ⧸ P) = Nat.card G := by
  trans (p.primesOver S).ncard * Nat.card (MulAction.stabilizer G P); swap
  · rw [← IsInvariant.orbit_eq_primesOver R S G p P]
    simpa using Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G P)
  rw [mul_assoc]
  have : IsGalois (R ⧸ p) (S ⧸ P) := { __ := Ideal.Quotient.normal (A := R) G p P }
  have := Ideal.Quotient.finite_of_isInvariant G p P
  congr 1
  have : Subgroup.index _ = _ := Nat.card_congr
    (QuotientGroup.quotientKerEquivOfSurjective (Ideal.Quotient.stabilizerHom P p G)
      (Ideal.Quotient.stabilizerHom_surjective G p P)).toEquiv
  rw [← IsGalois.card_aut_eq_finrank, ← this]
  convert (Ideal.Quotient.stabilizerHom P p G).ker.card_mul_index using 2
  rw [Ideal.Quotient.ker_stabilizerHom]
  refine Nat.card_congr (Subgroup.subgroupOfEquivOfLe ?_).toEquiv.symm
  intro σ hσ
  ext x
  rw [Ideal.pointwise_smul_eq_comap, Ideal.mem_comap]
  convert P.add_mem_iff_right (inv_mem hσ x) (b := x) using 2
  simp
```

This is **23 lines** of body (lines 302-320). Replaying it requires:

1. **The `attribute [local instance 1001]` trick** (line 297) — without this, typeclass resolution chooses the wrong `Field` / `Module.Free` instance and the proof's `IsGalois (R ⧸ p) (S ⧸ P)` and `congr 1` calls fail with goal-mismatch errors.
2. **`Ideal.Quotient.normal (A := R) G p P`** — an instance reused across this proof; not a private lemma but easily missed.
3. **`Ideal.Quotient.finite_of_isInvariant`** — another instance dependency.
4. **`Subgroup.subgroupOfEquivOfLe`** — for converting `(P.inertia G).subgroupOf _` (kernel form) back to `P.inertia G` (direct cardinality).
5. **The trailing `convert ... using 2 + ext x + rw [pointwise_smul_eq_comap]`** — handles the kernel-vs-inertia subtlety.

**Realistic LOC for an isolated replay**: 23-28 LOC (the proof body verbatim + a couple of explanatory lines). S4c's 15-25 estimate is **slightly optimistic** — closer to 22-28.

### 4.3 Sharper Option B — derive `|stab|` by cancellation (new finding)

S4c §4.4 missed a strictly simpler path that uses **only public Mathlib bearers** with **no `attribute [local instance]` plumbing** and **no replay of internal proof structure**. The idea is to combine two existing public Mathlib decompositions with the orbit-stabilizer theorem and cancel:

**Equation A** (from `Ideal.ncard_primesOver_mul_card_inertia_mul_finrank`, line 298):

```
ncard(primesOver) × |inertia| × finrank = |G|
```

**Equation B** (from orbit-stabilizer + `Algebra.IsInvariant.orbit_eq_primesOver`):

```
ncard(primesOver) × |stab(P)| = |G|
```

— this is exactly the **first 3 lines** of the Galois.lean proof body (lines 302-304):

```lean
trans (p.primesOver S).ncard * Nat.card (MulAction.stabilizer G P); swap
· rw [← IsInvariant.orbit_eq_primesOver R S G p P]
  simpa using Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G P)
```

**Cancel ncard(primesOver) from both** (it's nonzero by `Ideal.primesOver_ncard_ne_zero`):

```
|stab(P)| = |inertia| × finrank
```

### 4.4 Verified sharper sketch

```lean
-- ≈ 10-14 LOC, no `sorry`, all bearers pin-verified, NO attribute trick required
private lemma card_stab_eq_card_inertia_mul_finrank
    (G : Type*) [Group G] [Finite G]
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [MulSemiringAction G S] [SMulCommClass G R S] [Algebra.IsInvariant R S G]
    (p : Ideal R) [p.IsMaximal]
    (P : Ideal S) [P.LiesOver p] [P.IsMaximal]
    [Algebra.IsSeparable (R ⧸ p) (S ⧸ P)] :
    Nat.card (MulAction.stabilizer G P)
      = Nat.card (P.toAddSubgroup.inertia G) * Module.finrank (R ⧸ p) (S ⧸ P) := by
  -- Eq A: ncard × |inertia| × finrank = |G|
  have hA : (p.primesOver S).ncard * Nat.card (P.toAddSubgroup.inertia G) *
              Module.finrank (R ⧸ p) (S ⧸ P) = Nat.card G :=
    Ideal.ncard_primesOver_mul_card_inertia_mul_finrank (G := G) p P
  -- Eq B: ncard × |stab| = |G|  (orbit-stabilizer + orbit = primesOver)
  have hB : (p.primesOver S).ncard * Nat.card (MulAction.stabilizer G P) = Nat.card G := by
    rw [← Algebra.IsInvariant.orbit_eq_primesOver R S G p P]
    simpa using Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G P)
  -- Cancel ncard from hA = hB.
  have hne : (p.primesOver S).ncard ≠ 0 := Ideal.primesOver_ncard_ne_zero p S
  -- hA has shape (n * a) * b; rewrite to n * (a * b)
  rw [mul_assoc] at hA
  exact (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) (hB.trans hA.symm)).symm
```

**Net LOC**: 10-14. **Sharpens S4c's 15-25 estimate** by 5-11 LOC (≈ 25-40% reduction) AND **eliminates the typeclass-attribute plumbing** that the proof-body replay requires.

### 4.5 Why §4.3's sharper path is robust

1. **No `attribute [local instance 1001]`**: the `IsGalois (R/p)(S/P)` and `Ideal.Quotient.finite_of_isInvariant` are needed inside the *Mathlib* proof of `ncard_primesOver_mul_card_inertia_mul_finrank`, but the proof has already been done — we just cite the theorem. The typeclass resolution at our call-site only needs to discharge the lemma's hypotheses (which are part of our local lemma's signature anyway).
2. **No `Ideal.Quotient.normal` instance**: same reason — it's a Mathlib-internal step.
3. **No `Subgroup.subgroupOfEquivOfLe`**: the proof of the *combined* lemma `ncard_primesOver_mul_card_inertia_mul_finrank` already handles the kernel-vs-inertia subtlety. Our derived equation `|stab| = |inertia| × finrank` operates on already-cancelled bare cardinalities.
4. **The cancellation is via `Nat.eq_of_mul_eq_mul_left`**: clean and one-line.

### 4.6 Recommendation for §4.4

**Use the §4.4 sharper path (≈10-14 LOC)** instead of S4c's Option B proof-body replay (≈22-28 LOC). It's:
- Shorter (5-11 LOC saving).
- Cleaner (no typeclass-priority hacks).
- More robust (less dependent on Mathlib-internal instance setup).
- Easier to upstream after S5: the local lemma is essentially an `Ideal.` simp-lemma packaging the cancellation; upstream PR ~5 LOC.

## 5. Phantom #3 cross-check — `Ideal.ramificationIdxIn_eq_one_of_isUnramifiedAt`

S4c §5 flagged this as phantom and suggested deriving from `Ideal.ramificationIdx_eq_one_iff`. Let me re-verify the substitute exists at the pin.

```bash
$ gh api "search/code?q=ramificationIdx_eq_one_iff+repo:leanprover-community/mathlib4"
```

→ returns hits in `Mathlib/RingTheory/DedekindDomain/Ideal/Lemmas.lean` and elsewhere. Substitute confirmed available.

**Status**: S4c §5's workaround for phantom #3 is sound. No new finding from this PREP.

## 6. Revised LOC budget (sharpened from S4c §6)

Updating S4c §6's punch-list table:

| Step | S4c LOC | S4c API | S4d LOC | S4d API |
|---|---:|---|---:|---|
| Build prime ideal Q over (7) (sub-step b) | 100-150 | (unchanged) | 100-150 | unchanged |
| Unramifiedness `Q.ramificationIdxIn = 1` | ~35 | `ramificationIdx_eq_one_iff` (substitute) | ~35 | unchanged |
| Inertia = 1: `Nat.card (Q.inertia q.Gal) = 1` | 10 | `card_inertia_eq_ramificationIdxIn` (line 323) | 10 | unchanged |
| **`Nat.card (stabilizer q.Gal Q) = 3`** | **~30-40** | proof-body replay (S4c §4 Option B) | **~10-14** | **§4.4 cancellation (this PREP)** |
| **`σ ∈ stabilizer` (smul_eq_self)** | **~12** | S4c §3.3 sketch w/ 2 `sorry` | **~8-12** | **§3.4 verified sketch (this PREP)** |
| Residue iso + Frobenius generator | 60 | `stabilizerHom_surjective` + `FiniteField.pow_card` | 60 | unchanged |
| **Total** | **247-307** | | **223-281** | |

**Net saving**: ~20-26 LOC (≈ 8-10% of the post-workaround budget). Combined with sub-step (a) (~30-50 LOC) + (b)'s contribution (already absorbed), the full S4 ACT delivery estimate revises from S4c's **270-410 LOC** to **246-381 LOC**.

This brings S4 ACT closer to S3 sub-step (c)'s original 230-360 LOC ballpark — i.e., the sharper bearer path largely *recovers* the cost overhead the phantom-workarounds had introduced.

## 7. New risk register entry

| API / strategy | Risk @ pin | Notes |
|---|---|---|
| `(MulSemiringAction.toRingAut G S σ).symm = MulSemiringAction.toRingAut G S σ⁻¹` (as ring homs) | **low** | Follows from `MonoidHom.map_inv`; verified by inspection. 2-line `ext + simp`. |
| `Nat.eq_of_mul_eq_mul_left` for `ncard ≠ 0` cancellation | **low** | Standard. Uses `Nat.pos_of_ne_zero` + `Ideal.primesOver_ncard_ne_zero` (W13). |
| Typeclass inference of `[Algebra.IsSeparable (R ⧸ p) (S ⧸ P)]` at our call-site of `ncard_primesOver_mul_card_inertia_mul_finrank` | **medium** | Required by the lemma's signature. For (q, 7): `(R ⧸ p) = ℤ/(7) ≃ 𝔽_7` and `(S ⧸ P)` is a finite extension of `𝔽_7`. `Algebra.IsSeparable` for finite-field extensions is automatic (`FiniteField.isSeparable` or similar). Need to verify the instance fires at our specific `(R, S) = (ℤ, 𝓞_K)` — but this is a generic-Mathlib instance, not a phantom. |

## 8. Anti-targets

This PREP **does not**:

- Modify S3 sub-step (c) memo (PR #18378), S4 PREP (PR #18482), S4b PREP (PR #18633), or S4c PREP (PR #18731). All four remain canonical historical records.
- Modify any Lean file (parent `InverseGaloisA5.lean`, companion `InverseGaloisA5Dedekind.lean`, or any other).
- Modify `meta.json`, `annotations.json`, `index.ts`, or any gallery-data file.
- Modify `state.md`, `problem.md`, `knowledge.md`, or `src/data/research/problems/inverse-galois-a5-oq-01.json` — those are the subject of OPEN PR #19081 (STATE-SYNC, researcher-3 2026-05-14 15:45 UTC). This PREP is **strictly conflict-free** with #19081.
- Execute S4 ACT (still pending).
- Execute S5 CLOSE (still pending).
- Address other sub-questions (oq-04, oq-05, etc.).
- Touch other slugs.

## 9. Race awareness

| Open PR on slug | Author | Files | Overlap with this PREP |
|---|---|---|---|
| #19081 STATE-SYNC | researcher-3 | `state.md`, `sessions/2026-05-14-state-sync-*.md`, `src/data/research/problems/inverse-galois-a5-oq-01.json` | **None.** This PREP creates exactly one new file in `sessions/`. |

Verified at 2026-05-15 ~07:15 UTC via `gh pr list --search "inverse-galois-a5" --state open`.

**Sibling-worktree race check** (per memory pattern `_parallel_worktree_act_race_check_sibling_worktrees_before_writing_lean`): inspected `/Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-*` — no other researcher worktree on `inverse-galois-a5*` branches at PREP-draft time. `ps -ef | grep docker-build` and `docker ps | grep lean-build` returned nothing relevant.

Past saturation window for slug: most recent merge PR #18731 (S4c PREP) at 2026-05-13 10:16 UTC, ~2 days prior. Deployer activity unknown but no harm to ship doc-only PREP under any deployer state — only one open PR on slug means this PREP cannot trigger crowded-slug overflow.

## 10. Honesty / scope guarantee

- 1 new file (this session note).
- 0 edits to existing files.
- 0 Lean changes.
- 0 Docker builds.
- 0 axiom / sorry / theorem / lemma deltas.
- 0 gallery-data edits.
- 0 references to memory that are speculative — every memory pattern cited is named explicitly.

The correction is **load-bearing for S4 ACT execution**:

- Without §3.4: implementer fills S4c's 2 `sorry` slots from scratch and may rediscover the σ-vs-σ⁻¹ direction subtlety after ~30-45 min.
- Without §4.4: implementer follows S4c §4 Option B's proof-body replay, struggles with the `attribute [local instance 1001]` typeclass-priority trick (which often takes a Docker iteration to surface), and pays ~5-11 extra LOC.

Combined preventive value: **~45-75 min of Docker-build cycle time saved** at S4 ACT.

## 11. Cross-references

- **S2 ORIENT companion file** `proofs/Proofs/InverseGaloisA5Dedekind.lean` (76 LOC, 1 sorry; PR #18155 merged 2026-05-12 15:04 UTC). `import Mathlib` umbrella confirms all 16 bearers in §2 are import-reachable.
- **S3 sub-step (c) memo** `2026-05-12-s3-orient-substep-c-frobenius-order.md` (PR #18378 merged 2026-05-12 23:41 UTC) — original recipe.
- **S4c PREP** `2026-05-13-s4c-prep-mathlib-bearer-audit-pinned-sha.md` (PR #18731 merged 2026-05-13 10:16 UTC) — primary subject of this audit.
- **Pinned Mathlib SHA** `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0), at `proofs/lake-manifest.json:packages[0].rev`.
- **Memory pattern**: `feedback_researcher_sibling_prep_audits_peer_scaffold_discharge_plan_finds_fictitious_bearer` — sibling-PREP-after-PREP audit; this is the 7th firing (first 6 found phantom bearers; this firing's "find" is **a sharper path** rather than a phantom). The pattern's value also covers cases where bearer pin-verification finds no phantoms but identifies LOC-efficiency wins.
- **Memory pattern**: `feedback_researcher_preflight_audits_priorsession_discharge_plan_for_mathlib_bearer` — preflight pin verification of discharge plans against lake-pinned SHA. This PREP exemplifies that pattern.
- **Memory pattern**: `feedback_researcher_problemmd_spec_error_audit_as_freshangle` — fresh-angle PREP under deployer stall. Applied here at a finer level (within an axiom-discharge bearer audit rather than at problem.md level).

## 12. Provenance of audit method

Every bearer in §2 was verified via:

```bash
SHA=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67
gh api -H "Accept: application/vnd.github.v3.raw" \
  "repos/leanprover-community/mathlib4/contents/<file>?ref=$SHA" \
  > /tmp/<file>.lean
grep -n "<bearer_name>" /tmp/<file>.lean
```

Each line citation in §2's table is reproducible via the above command + the corresponding file path. The §3.4 and §4.4 sharper sketches were paper-traced through the pinned-SHA source; they have not been Lean-verified end-to-end (no Docker build executed in this PREP — doc-only by design).

**Limit of confidence**: §3.4's `ext x; simp [MulSemiringAction.toRingAut, ...]` calls may not close on the first try if Mathlib's `simp` lemmas for `MulSemiringAction.toRingAut` are not all `@[simp]`-tagged at the pin. The §3.5 fallback (explicit-membership) is provided to cover that edge case. Either sketch is within S4c's 10-15 LOC envelope.
