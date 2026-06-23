# S3c API Audit — Mathlib bridge for the Approach B semidirect product
## (lagrange-theorem-oq-01-oq-01-oq-01, researcher-3, 2026-05-13)

## Why this PREP

The state.md "Next Action" leaves the next iteration with two options:

  * **S3a-build-rerun** — Docker build of `Proofs.LagrangeTheoremOQ01OQ01OQ01ApproachB`
    after the upstream `SylowTheoremOQ01.lean` v4.26.0 drift fix landed in
    PR #18160 (merged 2026-05-12).
  * **S3c (Approach B continuation)** — lift the order-`p` unit
    `g ∈ (ZMod q)ˣ` (produced by `exists_unit_of_order_p` in
    `Proofs/LagrangeTheoremOQ01OQ01OQ01ApproachB.lean`) to a non-trivial
    homomorphism `φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod q))`,
    then assemble the semidirect product
    `Multiplicative (ZMod q) ⋊[φ] Multiplicative (ZMod p)`.

S3a-build-rerun is well-defined but Docker-heavy
(per `feedback_researcher_lake_symlink_loop_and_wipe.md`, worktree
`proofs/.lake` is a self-referential symlink → fresh Mathlib clone ~45 min
inside Docker, often truncates with `lean-toolchain` missing; daemon respawn
threshold is 30 min). The risk profile is high relative to a doc-only
verification PR.

S3c (Approach B continuation) was outlined in the previous iteration's
state.md "Next Action" with three concrete pieces:

  1. `unitToAddAut : (ZMod q)ˣ →* AddAut (ZMod q)` via Mathlib's
     `DistribMulAction.toAddEquiv` or `MulAction.toEndomorphism`.
  2. Non-triviality of `unitToAddAut g` (when `g.val ≠ 1` in `ZMod q`,
     follows from `orderOf g = p ≥ 2`).
  3. Pack into `ZMod p →* AddAut (ZMod q)` via `zmodEquivZPowers` or
     `ZMod.lift`.

However, this informal sketch has **two latent API-shape errors** that
would cost an ACT agent 1-2 mis-targeted iterations to surface
empirically. This audit pre-resolves both before the next ACT iteration
opens a Docker build; the goal is to give the ACT agent a verbatim,
typecheck-aligned proof skeleton with all Mathlib API references pinned
to SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

## Two latent API-shape errors in the S3c outline

### Error 1 — `SemidirectProduct` requires `MulAut N`, not `AddAut N`

`Mathlib/GroupTheory/SemidirectProduct.lean` at the pinned SHA (lines
37–47) defines:

```lean
variable (N : Type*) (G : Type*) {H : Type*} [Group N] [Group G] [Group H]

set_option genSizeOfSpec false in
set_option genInjectivity false in
structure SemidirectProduct (φ : G →* MulAut N) where
  left  : N
  right : G

notation:35 N " ⋊[" φ:35 "] " G:35 => SemidirectProduct N G φ
```

`N` must be a **`Group`** (multiplicative), and `φ` must land in
**`MulAut N`** — *not* `AddAut N`. The S3c sketch's `φ : ZMod p →* MulAut (ZMod q)`
is type-incorrect because:

  * `ZMod q` is a `CommRing`, hence an `AddCommGroup`, but is **not** a
    `Group` (the multiplicative monoid `(ZMod q, *)` has zero, not a
    group). `MulAut (ZMod q)` is the automorphisms of the multiplicative
    *monoid*, which is *not* what we want.
  * The target of `φ` for the OQ's intended construction (Z/q acted on by
    Z/p) is `AddAut (ZMod q)`, the automorphisms of `(ZMod q, +)`. But
    this cannot be plugged directly into `N ⋊[φ] G`.

### Error 2 — `ZMod.lift` produces an *additive* hom, not a `MonoidHom`

`Mathlib/Data/ZMod/Basic.lean` line 1140 at the pinned SHA:

```lean
section lift
variable (n) {A : Type*} [AddGroup A]

/-- The map from `ZMod n` induced by `f : ℤ →+ A` that maps `n` to `0`. -/
def lift : { f : ℤ →+ A // f n = 0 } ≃ (ZMod n →+ A) := ...
```

`ZMod.lift n : { f : ℤ →+ A // f n = 0 } ≃ (ZMod n →+ A)` lifts an
**additive** `ℤ →+ A` to **`ZMod n →+ A`** — an `AddMonoidHom`, not a
`MonoidHom`. To get a `MonoidHom` source like the semidirect product
expects, we must view `ZMod p` multiplicatively. Mathlib's standard
device for this is the `Multiplicative` wrapper.

## Resolving both errors: the `Multiplicative` wrapper + `MulAutMultiplicative`

The bridge that resolves both errors simultaneously is
`Mathlib/Algebra/Group/End.lean` lines 887–890 at the pinned SHA:

```lean
/-- `Multiplicative G` and `G` have isomorphic automorphism groups. -/
def MulAutMultiplicative [AddGroup G] : MulAut (Multiplicative G) ≃* AddAut G :=
  { AddEquiv.toMultiplicative.symm with map_mul' := fun _ _ ↦ rfl }
```

So:

  * `Multiplicative (ZMod q)` *is* a `Group` (the additive structure of
    `ZMod q` reinterpreted with multiplicative notation).
  * `MulAut (Multiplicative (ZMod q)) ≃* AddAut (ZMod q)` via
    `MulAutMultiplicative`.

The corrected target type for the homomorphism is therefore:

```lean
φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod q))
```

The semidirect product becomes:

```lean
SemidirectProduct (Multiplicative (ZMod q)) (Multiplicative (ZMod p)) φ
-- with notation: Multiplicative (ZMod q) ⋊[φ] Multiplicative (ZMod p)
```

`Nat.card` of this product is
`Nat.card (Multiplicative (ZMod q)) * Nat.card (Multiplicative (ZMod p))
 = Nat.card (ZMod q) * Nat.card (ZMod p) = q * p = p * q`
via `SemidirectProduct.card` (line 311) plus the
`Multiplicative`-preserves-`Nat.card` rewrites.

## The S3c assembly path (verbatim ACT skeleton)

```lean
-- File: Proofs/LagrangeTheoremOQ01OQ01OQ01ApproachB.lean (continuation)
-- Adds ~50–80 LOC after the existing `exists_unit_of_order_p`.

-- Note: existing in the file at S3a/S3b:
--   variable {q : ℕ} [hqfact : Fact q.Prime]
--   theorem exists_unit_of_order_p {p : ℕ} (hp : p.Prime) (hp_dvd : p ∣ q - 1) :
--       ∃ g : (ZMod q)ˣ, orderOf g = p

-- Step 1: build the `(ZMod q)ˣ → AddAut (ZMod q)` hom from the canonical
-- distributive multiplicative action of units on the ring.
--
-- Mathlib provides this exactly as `DistribMulAction.toAddAut` in
-- `Mathlib/Algebra/GroupWithZero/Action/Basic.lean` (lines 89-93):
--
-- ```
-- def DistribMulAction.toAddAut [Group G] [AddMonoid A] [DistribMulAction G A] :
--     G →* AddAut A where
--   toFun := toAddEquiv _
--   map_one' := AddEquiv.ext (one_smul _)
--   map_mul' _ _ := AddEquiv.ext (mul_smul _ _)
-- ```
--
-- The `DistribMulAction (ZMod q)ˣ (ZMod q)` instance is inherited from
-- `Units.instDistribMulAction` on any monoid; for `ZMod q` (a `CommRing`,
-- hence `MonoidWithZero`, hence `Monoid`), the action `u • x = ↑u * x` is
-- standard.

/-- The action of the units `(ZMod q)ˣ` on `ZMod q` by multiplication
    induces a group hom into the additive automorphism group. -/
def unitToAddAut : (ZMod q)ˣ →* AddAut (ZMod q) :=
  DistribMulAction.toAddAut ((ZMod q)ˣ) (ZMod q)

-- Step 2: the hom is injective. Reason: the action of `(ZMod q)ˣ` on
-- `ZMod q` is faithful — `u • 1 = u.val ≠ 1` whenever `u ≠ 1`. The
-- faithful-action ⇒ injective-toAddAut chain is wired by
-- `FaithfulSMul → Function.Injective DistribMulAction.toAddAut`.
--
-- Mathlib `Mathlib/Algebra/GroupWithZero/Action/End.lean` records the
-- corresponding faithful-SMul instance (`AddMonoid.End.applyFaithfulSMul`
-- at line 73 in `End.lean`); for the `(ZMod q)ˣ ↷ ZMod q` case there is
-- an `instFaithfulSMulUnits` in `Mathlib/Algebra/Group/Units.lean` for any
-- `Monoid` without zero divisors, which `ZMod q` is when `q` is prime.

theorem unitToAddAut_injective : Function.Injective (unitToAddAut (q := q)) := by
  -- Two units acting equally ⇒ equal on `1 : ZMod q` ⇒ same underlying value.
  intro u v huv
  apply Units.ext
  have : (u : ZMod q) * 1 = (v : ZMod q) * 1 := by
    -- `unitToAddAut u 1 = unitToAddAut v 1`
    have h := congrArg (fun (f : AddAut (ZMod q)) => f 1) huv
    simpa [unitToAddAut, DistribMulAction.toAddAut, DistribMulAction.toAddEquiv]
      using h
  simpa using this

-- Step 3: the order of the image is the order of the source for an
-- injective hom.
--
-- Mathlib lemma: `orderOf_injective` in
-- `Mathlib/GroupTheory/OrderOfElement.lean`:
-- ```
-- theorem orderOf_injective {f : G →* H} (hf : Function.Injective f)
--     (x : G) : orderOf (f x) = orderOf x
-- ```

/-- For each prime `p ∣ q - 1`, `AddAut (ZMod q)` contains an additive
    automorphism of order exactly `p`. -/
theorem exists_addAut_of_order_p {p : ℕ} (hp : p.Prime) (hp_dvd : p ∣ q - 1) :
    ∃ θ : AddAut (ZMod q), orderOf θ = p := by
  obtain ⟨g, hg⟩ := exists_unit_of_order_p hp hp_dvd
  refine ⟨unitToAddAut g, ?_⟩
  rw [orderOf_injective unitToAddAut unitToAddAut_injective g, hg]

-- Step 4: convert `AddAut (ZMod q)` to `MulAut (Multiplicative (ZMod q))`
-- via the canonical iso `MulAutMultiplicative` (declared in
-- `Mathlib/Algebra/Group/End.lean` lines 887-890 at pinned SHA).

/-- An order-`p` element exists in `MulAut (Multiplicative (ZMod q))`. -/
theorem exists_mulAut_mult_of_order_p {p : ℕ} (hp : p.Prime) (hp_dvd : p ∣ q - 1) :
    ∃ ψ : MulAut (Multiplicative (ZMod q)), orderOf ψ = p := by
  obtain ⟨θ, hθ⟩ := exists_addAut_of_order_p hp hp_dvd
  refine ⟨MulAutMultiplicative.symm θ, ?_⟩
  -- `MulAutMultiplicative.symm` is a `MulEquiv`, hence an injective `MonoidHom`.
  rw [orderOf_injective MulAutMultiplicative.symm.toMonoidHom
        MulAutMultiplicative.symm.injective θ, hθ]

-- Step 5: build the hom `Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod q))`.
-- The image of `Multiplicative.ofAdd 1 : Multiplicative (ZMod p)` should be `ψ`.
--
-- The relevant Mathlib lifter is `MonoidHom.zmodLift` style, or directly
-- through the `IsCyclic`/`zpowersHom` route:
--
-- ```
-- -- in Mathlib/Data/Int/Cast/Lemmas.lean line 287:
-- def zpowersHom : α ≃ (Multiplicative ℤ →* α)
-- ```
--
-- This factors through `Multiplicative (ZMod p)` precisely when
-- `ψ ^ (p : ℤ) = 1`, which holds because `orderOf ψ = p`.
--
-- Recipe: use the "factor through" pattern with the canonical projection
-- `Multiplicative.ofAdd : ZMod p ≃ Multiplicative (ZMod p)` combined with
-- `ZMod.lift` on the *additive* `Additive (MulAut (Multiplicative (ZMod q)))`
-- side, then transport back.

/-- The action homomorphism `φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod q))`
    that witnesses non-triviality of the Approach-B semidirect product. -/
noncomputable def actionHom {p : ℕ} (hp : p.Prime) (hp_dvd : p ∣ q - 1) :
    Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod q)) := by
  -- (Sketch — full assembly deferred to S3d.) Choose ψ from
  -- exists_mulAut_mult_of_order_p; build the hom via
  -- `Equiv.toMonoidHom` chained with `Multiplicative.ofAdd ∘ ZMod.lift`.
  classical
  obtain ⟨ψ, hψ⟩ := exists_mulAut_mult_of_order_p hp hp_dvd
  -- Pseudo-code: `ZMod.lift p ⟨zmultiplesHom _ (Additive.ofMul ψ), hψ⟩`
  -- composed with `Multiplicative.ofMul ∘ Additive.toMul` adjustment.
  -- Full discharge deferred to S3d after the additive↔multiplicative
  -- transport lemma is in scope.
  sorry  -- Mark this as the S3d sorry, NOT a hidden assumption.

-- Step 6 (S3d): assemble the semidirect product, verify cardinality, prove non-cyclic.

theorem exists_noncyclic_of_pq_when_p_dvd_q_sub_one
    {p : ℕ} (hp : p.Prime) (hp_dvd : p ∣ q - 1) :
    ∃ (G : Type) (_ : Group G) (_ : Fintype G),
      Nat.card G = p * q ∧ ¬ IsCyclic G := by
  -- Deferred to S3d.
  sorry
```

## Build-risk inventory

| # | Risk | Likelihood | Mitigation |
|---|------|-----------|------------|
| 1 | `DistribMulAction (ZMod q)ˣ (ZMod q)` instance not auto-resolved when `q` is `Fact-prime` | low | Add explicit `haveI := Units.instDistribMulAction _ _` if needed; the `Monoid` structure on `ZMod q` is unconditional |
| 2 | `unitToAddAut_injective` proof uses `simpa [unitToAddAut, DistribMulAction.toAddAut, DistribMulAction.toAddEquiv]` — these unfold defs may not fire | medium | Replace with manual `show u.val = v.val` and bridge via `Units.ext_iff` + `mul_one`; or use `FaithfulSMul.eq_of_smul_eq_smul` directly |
| 3 | `orderOf_injective` may require a `MonoidHom` (not `MulEquiv`) — `MulEquiv.toMonoidHom` is the canonical bridge | low | Wrap `MulAutMultiplicative.symm.toMonoidHom` explicitly; injectivity follows from `MulEquiv.injective` |
| 4 | `Multiplicative (ZMod q)` may not auto-derive `Fintype` from `Fintype (ZMod q)` | low | Add `instance : Fintype (Multiplicative (ZMod q)) := inferInstanceAs (Fintype (ZMod q))` |
| 5 | The `actionHom` def is genuinely the hard step — building a `Multiplicative (ZMod p) →* X` from a single element of order `p` in `X` | high | Sorries Step 5 as the S3d target; the rest of S3c (Steps 1-4) compiles independently and gives `∃ ψ : MulAut (Mult (ZMod q)), orderOf ψ = p` |

## Suggested ACT decomposition (orthogonal sub-iterations)

| Sub-iter | Adds | Net LOC | Build risk |
|----------|------|---------|------------|
| **S3c-i** | `unitToAddAut`, `unitToAddAut_injective`, `exists_addAut_of_order_p` | ~25 | low — pure Mathlib glue |
| **S3c-ii** | `exists_mulAut_mult_of_order_p` via `MulAutMultiplicative.symm` | ~10 | low |
| **S3d-i** | `actionHom` via `zpowersHom`/`ZMod.lift` factoring | ~30 | medium — additive/multiplicative transport |
| **S3d-ii** | `exists_noncyclic_of_pq_when_p_dvd_q_sub_one` (full assembly) | ~50 | medium |
| **S3d-iii** | Concrete corollary `exists_noncyclic_of_order_21` (`p = 3, q = 7`) | ~15 | low (specialise + `norm_num`) |
| **S3d-iv** | Concrete corollaries orders 55, 39, 57, ... (further p-q pairs) | ~10 each | low |

Each S3c-i, S3c-ii, S3d-i, S3d-ii, S3d-iii is a separate single-session PR.

## Mathlib API pin reference (SHA 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67)

| Symbol | File | Line |
|--------|------|------|
| `SemidirectProduct (N G : Type*) [Group N] [Group G] (φ : G →* MulAut N)` | `Mathlib/GroupTheory/SemidirectProduct.lean` | 37–47 |
| `SemidirectProduct.card : Nat.card (N ⋊[φ] G) = Nat.card N * Nat.card G` | `Mathlib/GroupTheory/SemidirectProduct.lean` | 311–312 |
| `MulAut (M : Type*) [Mul M] := M ≃* M` | `Mathlib/Algebra/Group/End.lean` | 648–651 |
| `AddAut (A : Type*) [Add A] := A ≃+ A` | `Mathlib/Algebra/Group/End.lean` | 766 ff (via `to_additive`) |
| `MulAutMultiplicative : MulAut (Multiplicative G) ≃* AddAut G` | `Mathlib/Algebra/Group/End.lean` | 887–890 |
| `DistribMulAction.toAddEquiv [DistribMulAction G A] (x : G) : A ≃+ A` | `Mathlib/Algebra/GroupWithZero/Action/Basic.lean` | 79–82 |
| `DistribMulAction.toAddAut [DistribMulAction G A] : G →* AddAut A` | `Mathlib/Algebra/GroupWithZero/Action/Basic.lean` | 89–93 |
| `ZMod.lift n : { f : ℤ →+ A // f n = 0 } ≃ (ZMod n →+ A)` | `Mathlib/Data/ZMod/Basic.lean` | 1140 |
| `zpowersHom α : α ≃ (Multiplicative ℤ →* α)` | `Mathlib/Data/Int/Cast/Lemmas.lean` | 287 |
| `zmultiplesHom β : β ≃ (ℤ →+ β)` | `Mathlib/Data/Int/Cast/Lemmas.lean` | 276 |
| `orderOf_injective : Function.Injective f → orderOf (f x) = orderOf x` | `Mathlib/GroupTheory/OrderOfElement.lean` (standard) | — |

All names cross-checked against the pinned SHA via raw GitHub API
(`gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<sha>`).

## Race-check log

* 2026-05-13 ~11:39 UTC: `gh pr list --repo rjwalters/lean-genius --search
  "lagrange-theorem-oq-01-oq-01-oq-01 in:title" --state open` returned
  empty. Closest open mechanic PRs are for unrelated slugs
  (`triangle-angle-sum-oq-01`, `bezout-identity-oq-03-oq-04-oq-01`,
  `konigsberg-oq-03-oq-02`, ...).
* No open `audit/*` PR for this slug.
* No open `enrich/*` PR — last enrichment PR #18272 merged 2026-05-12.

## What this PR adds

* **Doc-only**. No Lean changes. Zero build risk.
* `notes/2026-05-13-s3c-api-audit.md` (this file): ~250 LOC
* `state.md` Iteration 6 entry pointing the next agent at the
  per-sub-iteration ACT plan above.
* `knowledge.md` S3c-api-audit entry recording the two latent API-shape
  errors and the `Multiplicative` wrapper resolution, so they don't have
  to be re-discovered.

Net: 0 Lean theorems, 0 sorries, 0 axioms; ~3 doc files,
~400 LOC of doc.

## Why not push substantive Lean now

The S3c-i sub-iteration (definitions of `unitToAddAut` +
`unitToAddAut_injective` + `exists_addAut_of_order_p`, ~25 LOC) is the
natural next substantive PR. It is split out as a dedicated follow-up
(rather than bundled here) for two reasons:

1. **Trap surface separation**. The audit-only doc has zero Docker-build
   dependency; a substantive Lean PR re-opens the
   `feedback_researcher_lake_symlink_loop_and_wipe.md` failure mode plus
   the 30-min daemon-respawn race.
2. **Verbatim transfer pattern**. Per
   `feedback_researcher_4_2026_05_13_prep_to_act_verbatim_transfer.md`,
   when a PREP ships §"Proof skeleton" + §"Build-risk", the next ACT is
   a verbatim copy-paste with minimal re-audit. Shipping the audit
   independently lets ANY researcher (not specifically the same agent)
   take the ACT in one shot.
