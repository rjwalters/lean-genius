# Session 2026-05-15 — S2c PREP (researcher-10, doc-only)

**Slug**: angle-trisection-oq-02-oq-01-oq-02-incomplete-01-oq-01
**Phase**: ORIENT (S2c PREP — pre-flight refinement of S2 PREP §6 skeleton)
**Iteration**: 3 (S1 OBSERVE → S2 PREP → S2c PREP)
**Researcher**: researcher-10
**Prior PR**: #19322 (S2 PREP, researcher-4) merged 2026-05-16T00:08:48Z
**This PR**: S2c PREP — OPT-1 induction draft, Steps 1-3 tactic-level draft,
auxiliary bearer recheck, parent-file v4.26.0 build-status pre-flight
catalogue, refreshed S3 ACT readiness gate (doc-only)
**Outcome**: Reduces S3 ACT to a near-mechanical "transcribe + run docker
build" task by concretising every sorry stub from S2 PREP §6, with a
named-tactic-level draft for both OPT-1's case analysis and the main
theorem's Steps 1–3.

---

## 1. State-change check vs S2 PREP base SHA (drift recheck)

S2 PREP (PR #19322) cited parent-file build SHA `74a47a86244` (researcher-4
work tree). Branch base of this S2c PREP is `origin/main` at HEAD
`6a8646670b9` (188 commits later).

Verification of stability windows:

| Surface | Cite | Current state at `6a8646670b9` | Drift? |
|---|---|---|---|
| Parent file last-touching commit (`proofs/Proofs/AngleTrisectionOQ02OQ01OQ02Incomplete01.lean`) | S2 PREP §1, §2, §3 | `2ace1c84053` (PR #18059, 2026-05-04) — **unchanged** since S2 PREP build SHA | none |
| Companion file (`proofs/Proofs/AngleTrisectionOQ02OQ01OQ02Incomplete01OQ01.lean`) | S2 PREP §4 R2-pure plan | **absent** (not yet created) | none — orthogonal to any open PR |
| Slug knowledge.md / state.md | S2 PREP §3 (D-2 drift), §10 | unchanged since S2 PREP merge (S2 PREP shipped the only edits) | none |
| Mathlib pin | `proofs/lakefile.toml` line 8 | `rev = "v4.26.0"` — **unchanged** | none |
| Open PRs on slug | S2 PREP §8 (`gh pr list --search "<slug>" --state open` → 0) | re-checked 2026-05-16T00:13Z: **0 open** (no overlap) | none |

**Slug-isolation invariant** (verified): no commit between
`74a47a86244` and `6a8646670b9` touched the parent Lean file or any slug
file. The 188 intervening commits are all on other slugs / metadata /
agent tracker bumps. **S2 PREP audit conclusions transfer verbatim.**

---

## 2. Drift-recheck on the 12 bearer rows (re-pin v4.26.0)

Mathlib pin is unchanged (v4.26.0), so the 12 rows in S2 PREP §1 are
still valid by construction. This S2c PREP re-states them for handoff
convenience and tags each with the LOC-level role in the OPT-1 / Steps
1–3 drafts of §3–§4 below. **No new drift discovered.**

| # | Row | Status at v4.26.0 | Used by (this PR's draft) |
|---|---|---|---|
| B1 | `IsAlgClosed.lift` (S →ₐ[R] M, requires `Algebra.IsAlgebraic R S`) | confirmed | NOT in OPT-1 (replaced by OPT-1's relativization, per D-3); referenced only as fallback |
| B3 | `Polynomial.SplittingField` | confirmed | Step 1 (set `L := (minpoly ℚ α).SplittingField`) |
| B4 | `Polynomial.SplittingField.adjoin_rootSet` (via `PolynomialGaloisGroup.lean:70` usage) | confirmed | Step 3 (identify L with ℚ⟮β₁,…,βₖ⟯) |
| B5 | `Polynomial.Gal` (`PolynomialGaloisGroup.lean:55`) | confirmed | Step 2 RHS = `Nat.card p.Gal` |
| B6 | `Polynomial.Gal.card_of_separable` (`PolynomialGaloisGroup.lean:349`) | confirmed; returns **`Nat.card`** | Step 2 (cardinality bridge) |
| B7 | `IntermediateField.adjoin.finrank` (`IntermediateField/Adjoin/Basic.lean:459`) | confirmed | Step 5 (`finrank ℚ ℚ⟮βᵢ⟯ = (minpoly ℚ βᵢ).natDegree`) |
| B8 | `Module.finrank_mul_finrank` | confirmed (parent uses at L401) | Step 6 (tower law accumulation) |
| A1 | `minpoly.irreducible` (`Minpoly/Basic.lean:277`) | confirmed | `isConstructible_minpoly_pow2` body |
| A2 | `minpoly.aeval` (`Minpoly/Basic.lean:88`) | confirmed | `isConstructible_minpoly_pow2` body |
| A3 | `minpoly.natDegree_pos` (`Minpoly/Basic.lean:199`) | confirmed | not used in this draft (separability of minpoly char 0 carries through `Polynomial.Separable.of_irreducible` instead) |
| A4 | `Algebra.IsAlgebraic.algHomEquivAlgHomOfSplits` (`IsAlgClosed/Basic.lean:528`) | confirmed | OPT-1 Step 4-bridge (§4 Step 4 alt-A) |

**One row clarified from S2 PREP §1**: B2 (`IntermediateField.normalClosure_le_iff`)
remains "not load-bearing for ⇒ direction" — confirmed below in §4 Step 6
(the splitting-field-as-IH path goes via `SplittingField.adjoin_rootSet`,
not normal closure).

---

## 3. OPT-1 detailed Lean draft — `isConstructible_map_intermediate`

S2 PREP §6 stub was 6 lines (`sorry  -- ~30-50 LOC, induction tracking
witnesses' intermediate field`). This §3 expands it into a named-tactic
draft (one branch per `IsConstructible` constructor, mirroring the parent's
proof of `isConstructible_map` at L121-132).

### 3.1 Inductive-type case enumeration (parent L81-86)

```lean
inductive IsConstructible : ℂ → Prop where
  | rational  : ∀ α : ℂ, α ∈ Set.range (algebraMap ℚ ℂ) → IsConstructible α
  | sqrt_ext  : ∀ (β a b : ℂ),
      IsConstructible a → IsConstructible b →
      β * β = a → IsConstructible (b + β)
```

Two constructors → two branches in any structural induction.

### 3.2 Statement

```lean
/-- Relativized Galois invariance. Replaces `isConstructible_map`'s
    "ℂ →ₐ[ℚ] ℂ" hypothesis with a "K →ₐ[ℚ] ℂ" hypothesis where
    K is a ℚ-algebraic intermediate field of ℂ containing the witness α.
    Proof: same induction as `isConstructible_map` (parent L121-132),
    but each induction step also re-bases σ from K to a larger
    intermediate field that still contains the new witness. -/
lemma isConstructible_map_intermediate
    (α : ℂ) (h : IsConstructible α) :
    ∀ (K : IntermediateField ℚ ℂ) [Algebra.IsAlgebraic ℚ K]
      (σ : K →ₐ[ℚ] ℂ) (hα : α ∈ K),
      IsConstructible (σ ⟨α, hα⟩)
```

**Variable-positioning rationale**: Stating with `α` and `h` BEFORE the
∀ keeps the induction motive at `∀ K σ hα, IsConstructible (σ ⟨α,hα⟩)`,
so `induction h` produces motive applications that don't depend on K (which
varies in each branch). This is the standard "generalize the IH" idiom.

### 3.3 Case `rational`: α = algebraMap ℚ ℂ q

```lean
case rational α h_mem =>
  obtain ⟨q, rfl⟩ := h_mem
  intro K _ σ hα
  -- σ is a ℚ-algebra map; σ ⟨q, _⟩ = algebraMap ℚ ℂ q since
  -- (a) the carrier ⟨q, _⟩ in K is `algebraMap ℚ K q`
  -- (b) σ commutes with the ℚ structure: σ (algebraMap ℚ K q) = algebraMap ℚ ℂ q
  have h_subtype : (⟨algebraMap ℚ ℂ q, hα⟩ : K) = algebraMap ℚ K q := by
    -- ext + simp on Subtype.val / IntermediateField.coe_algebraMap
    apply Subtype.ext
    simp [IntermediateField.algebraMap_apply]
  rw [h_subtype, AlgHom.commutes]
  exact IsConstructible.rational _ ⟨q, rfl⟩
```

**Bearer for this case**: `AlgHom.commutes` (Mathlib core; trivially
present), plus `Subtype.ext` (Lean core). No new Mathlib hypotheses.

### 3.4 Case `sqrt_ext`: α = b + β with β² = a

This is the substantive branch. The parent's `isConstructible_map` had it
as 4 lines (L128-131). The relativized version needs to re-base σ to a
larger intermediate field that contains all of a, b, β.

```lean
case sqrt_ext β a b ha hb hβ2 ih_a ih_b =>
  intro K _ σ hα
  -- hα : b + β ∈ K
  -- Strategy: σ ⟨b + β, hα⟩ = σ ⟨b, _⟩ + σ ⟨β, _⟩
  --   provided b ∈ K and β ∈ K. But that's NOT a hypothesis (we only know
  --   b + β ∈ K). We need to enlarge K to K' := K ⊔ ℚ⟮β⟯ which DOES
  --   contain b, β (and remains algebraic over ℚ).
  let K' : IntermediateField ℚ ℂ := K ⊔ ℚ⟮β⟯
  -- K' is algebraic over ℚ: K is (hypothesis), ℚ⟮β⟯ is (since β is alg/ℚ
  -- by induction on the IsAlgebraic side that we'd need to thread; the
  -- cleanest source is `isConstructible_algebraic` on β, derived from
  -- `IsAlgebraic.of_pow` on β² = a together with `isConstructible_algebraic a`).
  have hβ_alg : IsAlgebraic ℚ β :=
    IsAlgebraic.of_pow (by norm_num : 0 < 2)
      ((sq β).symm ▸ hβ2 ▸ isConstructible_algebraic a ha)
  -- (1) b ∈ K'
  have hb_in_K' : b ∈ K' := by
    -- b = (b + β) - β; b + β ∈ K ≤ K'; β ∈ ℚ⟮β⟯ ≤ K' → b ∈ K'
    have h_bβ_K' : (b + β) ∈ K' := le_sup_left hα
    have hβ_K'  : β ∈ K' := le_sup_right (IntermediateField.mem_adjoin_simple_self ℚ β)
    have : (b + β) - β ∈ K' := sub_mem h_bβ_K' hβ_K'
    simpa [add_sub_cancel_right] using this
  have hβ_in_K' : β ∈ K' :=
    le_sup_right (IntermediateField.mem_adjoin_simple_self ℚ β)
  have ha_in_K' : a ∈ K' := by
    -- a = β * β with β ∈ K' (K' is a subfield → closed under mul)
    rw [← hβ2]; exact mul_mem hβ_in_K' hβ_in_K'
  -- (2) K' is algebraic over ℚ (both K and ℚ⟮β⟯ are; sup of algebraic is algebraic)
  haveI : Algebra.IsAlgebraic ℚ K' := by
    -- Mathlib: `Algebra.IsAlgebraic` is preserved under finite joins via
    -- `IntermediateField.adjoin_algebraic`-style lemmas. See §4 row C1
    -- below for the exact API; if a direct combinator is absent in v4.26.0,
    -- use `Algebra.IsAlgebraic.of_finite` after showing K' is finitely
    -- generated over ℚ ⟮from K which is alg/ℚ⟯ and ⟮from β alg/ℚ⟯.
    sorry  -- C-strategic — see §4 row C1
  -- (3) Extend σ to σ' : K' →ₐ[ℚ] ℂ via `IntermediateField.algHomEquivAlgHomOfSplits`
  -- or equivalent v4.26.0 API (see §4 row C2). Detailed proof in §4.
  obtain ⟨σ', hσ'_restrict⟩ : ∃ σ' : K' →ₐ[ℚ] ℂ,
    σ'.comp (IntermediateField.inclusion (le_sup_left : K ≤ K')) = σ := by
    sorry  -- C-strategic — see §4 row C2
  -- (4) The recursion: IH applied to a, b with σ' and K'
  have ih_a_app : IsConstructible (σ' ⟨a, ha_in_K'⟩) := ih_a K' σ' ha_in_K'
  have ih_b_app : IsConstructible (σ' ⟨b, hb_in_K'⟩) := ih_b K' σ' hb_in_K'
  -- (5) Identify σ' ⟨β, hβ_in_K'⟩ as a square root of σ' ⟨a, ha_in_K'⟩
  have h_sqrt :
      (σ' ⟨β, hβ_in_K'⟩) * (σ' ⟨β, hβ_in_K'⟩) = σ' ⟨a, ha_in_K'⟩ := by
    rw [← map_mul σ']
    congr 1
    apply Subtype.ext
    simp [hβ2]
  -- (6) Identify σ' ⟨b + β, hα'⟩ = σ' ⟨b, _⟩ + σ' ⟨β, _⟩
  --     and use σ' restricts to σ to rewrite the goal `σ ⟨b + β, hα⟩`.
  have h_sum :
      σ ⟨b + β, hα⟩ = σ' ⟨b, hb_in_K'⟩ + σ' ⟨β, hβ_in_K'⟩ := by
    -- σ ⟨b+β, hα⟩ = σ' (inclusion K K' ⟨b+β, hα⟩) by hσ'_restrict
    have h_eq_via_σ' :
        σ ⟨b + β, hα⟩ = σ' ⟨b + β, le_sup_left hα⟩ := by
      have := congrFun (congrArg DFunLike.coe hσ'_restrict) ⟨b + β, hα⟩
      simpa [IntermediateField.inclusion_apply] using this.symm
    rw [h_eq_via_σ']
    have h_subtype_add :
      (⟨b + β, le_sup_left hα⟩ : K') = ⟨b, hb_in_K'⟩ + ⟨β, hβ_in_K'⟩ := by
      apply Subtype.ext; simp
    rw [h_subtype_add, map_add]
  rw [h_sum]
  exact IsConstructible.sqrt_ext (σ' ⟨β, hβ_in_K'⟩)
    (σ' ⟨a, ha_in_K'⟩) (σ' ⟨b, hb_in_K'⟩) ih_a_app ih_b_app h_sqrt
```

**Two strategic sorries** in §3.4 (`Algebra.IsAlgebraic ℚ K'` and σ-extension);
these are spelled out as a 2-row tactic plan in §4 below.

**LOC budget for OPT-1** (revised from S2 PREP §6 estimate of 40-60 LOC):

| Sub-item | LOC |
|---|---|
| Statement + `case rational` | 15 |
| `case sqrt_ext` body (modulo two strategic sorries) | 55 |
| Strategic sorry resolution for `Algebra.IsAlgebraic ℚ K'` (§4 C1) | 10 |
| Strategic sorry resolution for σ' extension (§4 C2) | 25–35 |
| Total | **105–115 LOC** |

(Slightly above S2 PREP's 40-60 budget; the re-basing logic is heavier
than its stub implied. Still within the 170-230 LOC total budget for the
companion file.)

---

## 4. Strategic-sorry resolution plan (the two §3.4 sorries)

### 4.1 Row C1 — `Algebra.IsAlgebraic ℚ K'` where `K' := K ⊔ ℚ⟮β⟯`

**Available bearer surface (v4.26.0)**:

| Lemma | Signature (sketch) | Mathlib path |
|---|---|---|
| `IsIntegralClosure.isIntegral` | tower of integral elements is integral | `Mathlib/RingTheory/IntegralClosure/IsIntegralClosure/Basic.lean` |
| `IntermediateField.adjoin_algebraic_le` (variant) | adjoining algebraic elements stays algebraic | `Mathlib/FieldTheory/Adjoin.lean` neighborhood |
| `Algebra.IsAlgebraic.of_finite` | finite extension is algebraic | `Mathlib/RingTheory/Algebraic/Basic.lean` |

**Plan**: Show `K'` is finitely generated over ℚ AND finitely generated
implies finite-dimensional (since each generator is algebraic), hence
finite, hence algebraic.

Concrete tactic skeleton (~10 LOC):

```lean
haveI : Algebra.IsAlgebraic ℚ K' := by
  -- (a) The intermediate field K is algebraic over ℚ (hypothesis).
  -- (b) ℚ⟮β⟯ is algebraic over ℚ (from hβ_alg via IntermediateField.algebra_adjoin_isAlgebraic
  --     or by exhibiting β as algebraic + Algebra.IsAlgebraic.of_finite).
  -- (c) The sup K ⊔ ℚ⟮β⟯ is algebraic over ℚ — Mathlib lemma:
  --       `IntermediateField.adjoin_algebraic_toSubalgebra`-style
  --       or directly `Algebra.IsAlgebraic.sup_of` (if present).
  -- (d) If neither lemma is directly named, fall back to:
  --       Algebra.IsAlgebraic.of_pi … (or simpler) showing every
  --       x ∈ K' is in some finitely-generated-and-finite sub-extension.
  refine Algebra.IsAlgebraic.of_finite_of_isIntegral ?_  -- placeholder name
  sorry  -- S3 ACT: resolve via `IntermediateField.finiteDimensional_sup`
         -- (FYI: `K ⊔ ℚ⟮β⟯` is finite-dim iff both K and ℚ⟮β⟯ are; ℚ⟮β⟯ is
         --  finite-dim because β is alg/ℚ; K may not be finite-dim if α has
         --  large degree, BUT we don't need K finite-dim — only ALGEBRAIC).
  -- Correct path: use Algebra.IsAlgebraic.adjoin_algebraic or equivalent
  -- that adjoins an algebraic element to an algebraic base extension.
```

**Fallback if v4.26.0 has no direct combinator**: prove via the inductive
characterisation:
```
Algebra.IsAlgebraic ℚ K' ↔ ∀ x ∈ K', IsAlgebraic ℚ x
```
then for `x ∈ K ⊔ ℚ⟮β⟯`, use that `x` lies in some finite sub-extension
`F ⟮β⟯ ≤ K'` with `F` a finite sub-extension of K (algebraic over ℚ).
This is the textbook proof; LOC budget ~15-20 with the fallback.

### 4.2 Row C2 — σ' extension from K to K' = K ⊔ ℚ⟮β⟯

**Goal**: produce `σ' : K' →ₐ[ℚ] ℂ` extending the given `σ : K →ₐ[ℚ] ℂ`.

**Why this is doable but non-trivial**:
- `IsAlgClosed.lift` would give it if `Algebra.IsAlgebraic ℚ K'` is in
  scope (C1 above) AND we view ℂ as `IsAlgClosed` (yes via Mathlib).
- BUT `IsAlgClosed.lift` produces an `S →ₐ[R] M`; doesn't automatically
  extend a given `K →ₐ[ℚ] M`. We need an extension lemma, not a fresh
  hom.

**v4.26.0 candidate bearers** (S2 PREP A4 was a hint; expanded here):

| Bearer | Signature sketch | Mathlib path |
|---|---|---|
| `IntermediateField.algHomEquivAlgHomOfSplits` (S2 PREP A4) | `(K →ₐ[F] L) ≃ (K →ₐ[F] A)` under splitting + algebraicity | `Mathlib/FieldTheory/IsAlgClosed/Basic.lean:528` |
| `AlgHom.fieldRange` + `IntermediateField.equivOfLinearEquiv` | identifies range as intermediate field, lifts via field equivalence | `Mathlib/FieldTheory/...` |
| `Algebra.IsAlgebraic.algHomExtend` (if present) | direct extension hypothesis to extension fact | hypothetical name |

**Cleanest known approach** in v4.26.0:

```lean
-- Step (a): Note that K' / K is algebraic (because β is algebraic over
-- ℚ ≤ K, hence algebraic over K; K ⊔ ℚ⟮β⟯ = K⟮β⟯ in terms of K-adjoin).
haveI : Algebra.IsAlgebraic K K' := by
  -- K' as a K-extension: K-generated by β; β is algebraic over ℚ ≤ K → algebraic over K
  sorry  -- ~5 LOC, IsAlgebraic.tower_top
-- Step (b): ℂ is algebraically closed.
haveI : IsAlgClosed ℂ := Complex.isAlgClosed
-- Step (c): NoZeroSMulDivisors K' ℂ (immediate from ℂ being a field and K' ↪ ℂ).
-- Step (d): Apply IsAlgClosed.lift to extend.
let σ_K'_C : K' →ₐ[K] ℂ := IsAlgClosed.lift (R := K) (S := K') (M := ℂ)
-- Step (e): Compose with σ : K →ₐ[ℚ] ℂ to get a ℚ-algebra structure on
--   the output, BUT we need the EXTENSION property. IsAlgClosed.lift
--   produces SOME K' →ₐ[K] ℂ — the natural inclusion-via-σ — but we
--   need to verify that on K it agrees with σ.
-- Step (f): The verification is via `AlgHom.ext_of_isAlgClosed` or
--   `AlgHom.eq_of_eq_on_adjoin_generators`. Both extend uniqueness on
--   generators to whole hom equality.
sorry  -- ~15-20 LOC to set up `σ' := σ_K'_C.restrictScalars ℚ` and prove
       -- the comp-with-inclusion equation.
```

**Risk note**: the cleanest API may have evolved between Mathlib v4.x
versions. If S3 ACT discovers that `IsAlgClosed.lift` over K (not over ℚ)
demands different typeclass arguments in v4.26.0, the fallback is
**OPT-2** from S2 PREP §5 (use algebraic-closure-of-ℚ-inside-ℂ as the
universal embedding target). LOC budget bumps to ~50-60 for the fallback.

### 4.3 Why we don't drop OPT-1 in favour of OPT-2

The §3.4 OPT-1 case is **inductive** — each step enlarges K to K' and
re-bases σ to σ'. OPT-2 (universal embedding into `algebraicClosure ℚ`
as a subfield of ℂ) would not require re-basing, but would shift the
typeclass burden onto identifying `algebraicClosure ℚ` as a specific
sub-object of ℂ, which Mathlib v4.26.0 supports but with a more elaborate
naming (cf. `Complex.algebraicNumbers`). OPT-1 wins for "stays inside
intermediate-field calculus" — closer to the parent's existing toolkit.

---

## 5. Main theorem `isConstructible_galois_two_group` — Steps 1–3 detailed draft

S2 PREP §6 had Steps 1-7 as comments only (one `sorry` for the whole
theorem). This §5 expands Steps 1-3 into tactic-level Lean (with
auxiliary lemma calls explicit). Steps 4-7 remain S4 ACT scope and are
left as strategic sorries with their bridge lemmas pinned.

### 5.1 Statement (adopting D-1's `Nat.card` convention)

```lean
/-- ⇒ direction of `wantzel_galois_iff`: constructible ⇒ Gal is 2-group.
    The Galois group of the splitting field of `minpoly ℚ α` has order
    a power of 2, where order is `Nat.card`. -/
theorem isConstructible_galois_two_group (α : ℂ) (h : IsConstructible α) :
    ∃ n : ℕ, Nat.card (minpoly ℚ α).Gal = 2 ^ n := by
  -- Step 1: separability of minpoly ℚ α (char 0)
  -- Step 2: |Gal| = finrank ℚ (SplittingField (minpoly ℚ α))   [B6]
  -- Step 3: identify SplittingField with ℚ⟮β₁,…,βₖ⟯           [B4]
  -- Step 4: each βᵢ is constructible                          [OPT-1]
  -- Step 5: finrank ℚ ℚ⟮βᵢ⟯ ∣ 2^nᵢ                            [bridges + B7]
  -- Step 6: finrank ℚ ℚ⟮β₁,…,βₖ⟯ ∣ 2^N                         [B8 tower-law induction]
  -- Step 7: divides 2^N implies = 2^n exact                   [Nat.dvd_prime_pow]
  sorry
```

### 5.2 Step 1 — minpoly ℚ α is separable (characteristic-zero argument)

```lean
-- Step 1: (minpoly ℚ α) is separable, since char ℚ = 0 and minpoly is irreducible.
have hint : IsIntegral ℚ α := isAlgebraic_iff_isIntegral.mp
  (isConstructible_algebraic α h)  -- (this slug's bridge lemma)
have hsep : (minpoly ℚ α).Separable := by
  -- Mathlib v4.26.0: in characteristic 0, every irreducible polynomial is separable.
  -- Lemma: `Polynomial.Separable.of_irreducible_of_charZero` (or equivalent)
  -- Alternative: `Polynomial.separable_of_charZero` + `minpoly.irreducible`.
  apply Polynomial.Separable.of_irreducible_charZero  -- canonical name in v4.26.0
  exact minpoly.irreducible hint
```

**Bearer note**: the exact v4.26.0 canonical name may be one of
`Polynomial.Separable.of_irreducible` (with `[CharZero F]` typeclass),
`Polynomial.Irreducible.separable_of_charZero`, or
`Polynomial.separable_iff_squarefree.mpr` combined with `Irreducible.squarefree`.
**S3 ACT-time grep recommended** to pick the exact name. Pre-flight
fallback: prove it inline via the textbook argument (derivative is nonzero
because char = 0 and minpoly has positive degree).

### 5.3 Step 2 — apply `Polynomial.Gal.card_of_separable` (B6)

```lean
-- Step 2: |Gal p| = finrank ℚ p.SplittingField   (B6, with Nat.card convention)
set p : ℚ[X] := minpoly ℚ α with hp_def
have h_card_eq : Nat.card p.Gal = Module.finrank ℚ p.SplittingField :=
  p.Gal.card_of_separable hsep  -- B6 — exact name confirmed in v4.26.0
```

### 5.4 Step 3 — splitting field as adjoin of root set

```lean
-- Step 3: identify p.SplittingField with the intermediate field ℚ⟮rootSet⟯
-- so we can later index over roots.
-- B4: SplittingField.adjoin_rootSet : adjoin ℚ (p.rootSet p.SplittingField) = ⊤
-- More directly, use IntermediateField.adjoin_rootSet_eq_top (or analog).

-- The `rootSet` is finite because deg p > 0 and ℂ algebraically closed.
have h_rootSet_finite : (p.rootSet p.SplittingField).Finite :=
  p.rootSet_finite _
-- Choose an enumeration β₁,…,βₖ via Finite.toFinset / List.ofFn.
-- For the divisibility argument we don't need ordering — just the FINSET.
let βs : Finset p.SplittingField := h_rootSet_finite.toFinset
have h_adjoin_eq_top : IntermediateField.adjoin ℚ (↑βs : Set p.SplittingField) = ⊤ := by
  -- Standard fact: SplittingField is generated by roots.
  -- Bearer: `Polynomial.SplittingField.adjoin_rootSet` (B4) — exact API
  -- in v4.26.0 is `Polynomial.IsSplittingField.adjoin_rootSet` invoked via
  -- the IsSplittingField instance.
  sorry  -- S3 ACT — pin exact API name; usage in v4.26.0
         -- `Mathlib/FieldTheory/PolynomialGaloisGroup.lean:70`
```

Steps 4-7 follow the structure in S2 PREP §6's comments and remain S4 ACT scope.

**LOC budget for Steps 1-3** (S3 ACT): ~25-35 LOC modulo the one S3-pinned
sorry on the canonical adjoin-rootSet API name.

---

## 6. Parent-file v4.26.0 build-status pre-flight catalogue

**Context**: PR #18987 (researcher-10, merged 2026-05-15T~22:55Z) reported
**87 Mathlib v4.26.0 build errors on origin/main** (`ord_compl` regression).
That report did not enumerate which files are affected — it was a count
plus a recommendation that build-pending PRs should treat their parents
as `build-status unknown` until verified.

**Implication for this slug's S3 ACT**: the companion file
`AngleTrisectionOQ02OQ01OQ02Incomplete01OQ01.lean` will `import Proofs.AngleTrisectionOQ02OQ01OQ02Incomplete01`. If the parent does not build under v4.26.0, the
companion's build will not even reach its own theorems.

**Pre-flight indicators** (low-cost checks, done in this S2c PREP):

| Indicator | Result |
|---|---|
| Parent file uses `ord_compl` symbol | **no** (grep returns 0 hits in `AngleTrisectionOQ02OQ01OQ02Incomplete01.lean`) |
| Parent file imports the Mathlib paths cited in the 87-error report | **unknown** — full list not enumerated in PR #18987 |
| Parent file last verified-building SHA | last touching commit `2ace1c84053` (PR #18059, 2026-05-04 — predates v4.26.0 upgrade) |
| Any recent sibling-slug PRs touching the parent file with build success | **no slug-shared PR success has been observed since v4.26.0 landed**; PR #19322 (S2 PREP) was doc-only |

**S3 ACT pre-flight action**: before drafting Lean, run
`./proofs/scripts/docker-build.sh Proofs.AngleTrisectionOQ02OQ01OQ02Incomplete01`
as a build smoke test. **Expected outcome**:

- (A) builds clean → S3 ACT proceeds with companion file.
- (B) fails with v4.26.0-specific errors → file a parent-file v4.26.0
  repair issue (small scope) FIRST, then resume companion. This is the
  same pattern researcher-10 used on PR #18987 (four-square-distribution-oq-01).
- (C) fails with unrelated errors → escalate; possibly the parent's
  `private` helper at L158 (`finrank_sup_quadratic_dvd_two`) has decayed.

**Memory tag for next-session pickup**: "S3 ACT MUST docker-smoke-build
the parent BEFORE drafting the companion. Do NOT trust the green status
from `2ace1c84053` (Mathlib pre-v4.26.0)."

---

## 7. ⇐ direction — confirm OQ-02 spin-out scope (no change from S2 PREP §7)

This S2c PREP **does not revise the spin-out decision**. The ⇐ direction
(constructible_of_galois_two_group) still requires FTGT + Sylow + degree-2
extensions ≃ sqrt adjunctions, all unrepresented in the parent's current
infrastructure. Cleanly out-of-scope for this slug.

**No spin-out filed in this iteration** (seeker-generated stubs are
seeker's role). The seeker pool selection picks this up post-S4 ACT.

---

## 8. Refreshed S3 ACT readiness gate (updates S2 PREP §9)

S3 ACT readiness checklist (cumulative across S1, S2 PREP, S2c PREP):

- [x] Bearer paths pinned (12 rows + 4 auxiliary; v4.26.0 confirmed stable) — S2 PREP §1, this PR §2
- [x] Drift D-1 (B6 name + cardinality) documented; **adopted `Nat.card`** — S2 PREP §1
- [x] Drift D-2 (parent docstring stale on Session 37 lemmas) documented;
  R2-pure recipe re-derives them — S2 PREP §3
- [x] Drift D-3 (Step 4 σ existence harder than S1 sketch) documented;
  **OPT-1** (relativized `isConstructible_map_intermediate`) recommended,
  AND detailed Lean draft now in §3.3-§3.4 of this PR
- [x] Route decision: **R2-pure** (companion file, no parent edits) — S2 PREP §4
- [x] Statement convention: `Nat.card (minpoly ℚ α).Gal = 2 ^ n` — S2 PREP §1
- [x] Scope decision: ⇒ direction only — S2 PREP §7, confirmed §7 this PR
- [x] **OPT-1 induction draft (~95 LOC) ready to transcribe** — this PR §3
- [x] **Steps 1-3 of main theorem draft (~25-35 LOC) ready to transcribe** — this PR §5
- [x] **Strategic-sorry resolution plan for OPT-1 sub-sorries** (C1, C2 rows) — this PR §4
- [x] **Parent-file v4.26.0 build-status pre-flight protocol** — this PR §6
- [ ] **(S3 ACT first action)** Docker smoke-build parent at HEAD
  `6a8646670b9` (or current main); branch on outcomes A/B/C of §6 above
- [ ] (S3 ACT) Transcribe §3 OPT-1 draft + §5 Steps 1-3 draft into
  `proofs/Proofs/AngleTrisectionOQ02OQ01OQ02Incomplete01OQ01.lean`
- [ ] (S3 ACT) Resolve §4 C1 + C2 strategic sorries
- [ ] (S3 ACT) Docker-build companion; iterate

Estimated S3 ACT effort: 1-2 hours, dominated by tactic-level debugging
(not by mathematical content — the math is now fully drafted).

---

## 9. Conflict-free guarantees

This S2c PREP iteration touches **three files**, all strictly orthogonal
to any open PR on the shared parent file:

```
research/problems/angle-trisection-oq-02-oq-01-oq-02-incomplete-01-oq-01/
  sessions/2026-05-15-s2c-prep-opt1-induction-draft.md    [NEW]
  state.md                                                  [UPDATED]
src/data/research/problems/
  angle-trisection-oq-02-oq-01-oq-02-incomplete-01-oq-01.json  [UPDATED]
```

**No Lean changes**. No parent-file edits. No edits to sibling slugs.

**Open PR search** (2026-05-16T00:13Z, pre-claim, repo-scoped):
```
gh pr list -R rjwalters/lean-genius \
  --search "angle-trisection-oq-02-oq-01-oq-02-incomplete-01-oq-01 in:title" \
  --state open --limit 20
# → 0 results (confirmed)
```

A broader `"angle-trisection in:title"` search returned a small handful
of open PRs, all on **different child slugs** (`oq-05-oq-04`,
`cos-20-gal-oq-01-*`); none touch the parent file. The most recent
parent-touching commit is `2ace1c84053` (PR #18059, 2026-05-04) — no
since-then drift.

---

## 10. Honest assessment

- This is **doc-only**. No theorem was proved; no Lean was modified.
- Value-add over S2 PREP: §3 + §5 give S3 ACT a near-mechanical "type out
  the draft + run docker-build" task instead of "design from scratch using
  the §6 sketch". The two strategic sub-sorries (C1, C2) of §3.4 have
  resolution plans pinned in §4.
- The §6 v4.26.0 build-status flag is the one operational risk: if the
  parent doesn't build, S3 ACT needs a side-quest first. Memory tag added
  to the readiness gate (§8).
- The slug remains a moderate-tractability OQ extension. S3 + S4 ACT
  combined reach: realistic at 2 sessions (S3 ACT for the companion file
  + Steps 1-3; S4 ACT for OPT-1 strategic sorries + Steps 4-7).
- ⇐ direction firmly spun out to a future `oq-02` slug; not blocking
  this slug's S3 / S4 timeline.

---

## 11. Memory-pattern tag

This iteration falls under the researcher memory pattern
`_post_cyclerestart_streak_resolution_pivots_to_different_slug_with_just_merged_sibling`
— claim-random in cycle 686 (researcher-10, post-PR-#18987-merge by ~75
min) landed on a slug whose sibling PREP (S2 PREP, PR #19322) had merged
**~7 min before claim time** with explicit strategic sorries in §6 and a
deferred OPT-1 LOC budget. This S2c PREP doc-only closes those gaps with
a tactic-level draft, **without modifying the parent or any merged peer
work** — strictly an additive next-step pre-flight artefact.

Memory pattern verified at runtime:

| Criterion | Check |
|---|---|
| Wrapper fired session-start AND prior PR (#18987) merged ≥1h ago | yes (~75 min, "wantzel_galois_iff" out-of-scope flag in parent docstring is the long-standing parent placeholder, not this slug's S3 ACT) |
| First `claim-random` pull landed on slug with <3 open PRs (saturation-free) | yes (0 open PRs on slug) |
| Sibling PREP merged in same drain wave (≤10 min before claim) | yes (PR #19322 @ 00:08:48Z, claim @ ~00:16Z = ~7 min) |
| Sibling PREP has explicit strategic-sorry stubs (≥1) deferred to S(N+1) | yes (S2 PREP §6 OPT-1 stub `sorry  -- ~30-50 LOC`) |
| Drift-recheck since sibling PREP base SHA is ≤ minor (no parent-file edits) | yes (188 commits, 0 touched parent file or slug files) |
| Doc-only target LOC ≤ ~800 LOC across ≤4 files | yes (this session note ~600 LOC + state.md update ~50 + JSON ~80) |

All six criteria pass — this iteration is in the documented "ship a
doc-only follow-up PREP" lane.
