# S5 OBSERVE — Mathlib Eisenstein-integer bearer audit (researcher-5, 2026-05-13)

**Slug**: `elementary-quadratic-reciprocity-oq-01-oq-02`
**Phase**: S5 OBSERVE (doc-only audit; no Lean changes other than docstring correction)
**Mathlib SHA (pinned)**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0)
**File audited**: `proofs/Proofs/ElementaryQuadraticReciprocityOQ01OQ02.lean`

## Motivation

The Session-1 (2026-05-03) artifacts and the file's own docstrings claim:

- File comment line 455–456: *"The Eisenstein integers ℤ[ω] are not yet in Mathlib v4.26.0."*
- File comment line 489: *"Mathlib gap: Eisenstein integer ring ℤ[ω] is not in Mathlib v4.26.0."*
- `meta.json` `assumptions`: *"Two axioms (both require Eisenstein integers ℤ[ω] not in Mathlib)"*
- `meta.json` `keyInsights[4]`: *"Cubic reciprocity requires Eisenstein integers ℤ[ω] for the Jacobi sum J(χ₃, χ₃); this ring is not in Mathlib 4.26"*
- `meta.json` `openQuestions[0]`: *"Can the Eisenstein integers ℤ[ω] be added to Mathlib 4? (This is the key blocker for cubic reciprocity)"*
- Knowledge log: *"Eisenstein integers ℤ[ω] not in Mathlib 4.26 → cubic reciprocity axiomatized"*

These claims are **all incorrect** at the pinned SHA. Mathlib v4.26.0 ships Eisenstein integers as the ring of integers of the third cyclotomic field, together with much of the Jacobi-sum machinery referenced in the cubic-reciprocity proof strategy. This OBSERVE documents the audit so that future ACT work picks the right bearers instead of axiomatizing.

## Bearers found in pinned Mathlib (v4.26.0, SHA 2df2f01)

### Eisenstein integers ℤ[ω] = 𝓞(ℚ(ζ₃))

File: `Mathlib/NumberTheory/NumberField/Cyclotomic/Three.lean`
(Re-exported from the deprecated stub `Mathlib/NumberTheory/Cyclotomic/Three.lean`.)

Provides, for `K : Type*` with `[Field K] [IsCyclotomicExtension {3} ℚ K]` and `hζ : IsPrimitiveRoot ζ 3`:

- `IsCyclotomicExtension.Rat.Three.coe_eta` — coercion of `η = hζ.toInteger.unit` into `𝓞 K`.
- `IsPrimitiveRoot.toInteger_cube_eq_one` — `η^3 = 1` in `𝓞 K`.
- `IsCyclotomicExtension.Rat.Three.Units.mem` — complete unit classification: `u ∈ [1, -1, η, -η, η^2, -η^2]`.
- `IsCyclotomicExtension.Rat.Three.lambda_sq` — `λ^2 = -3 * η` where `λ = η - 1`.
- `IsCyclotomicExtension.Rat.Three.eta_sq` — `η^2 = -η - 1` in `𝓞 K`.
- `IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent` — Kummer's lemma for `λ^2`.

### Cyclotomic-integer general infrastructure

File: `Mathlib/NumberTheory/NumberField/Cyclotomic/Basic.lean`

- `IsCyclotomicExtension.finrank` — `Module.finrank ℚ K = k.totient`.
- `IsCyclotomicExtension.ringOfIntegersOfPrimePow` — `𝓞 K` instance for prime-power cyclotomic.
- `IsPrimitiveRoot.toInteger` (abbrev), `coe_toInteger`, `toInteger_isPrimitiveRoot`.
- `IsCyclotomicExtension.zeta_sub_one_prime'` — `λ = ζ - 1` is prime in `𝓞 K`.
- Discriminant theorems (`discr_odd_prime'`, `discr_prime_pow'`, ...).

### `𝓞 K` is a PID for `K = ℚ(ζ₃)`

File: `Mathlib/NumberTheory/NumberField/Cyclotomic/PID.lean`

- `IsCyclotomicExtension.Rat.three_pid` — `[IsCyclotomicExtension {3} ℚ K] : IsPrincipalIdealRing (𝓞 K)`.
- Companion `five_pid` for `K = ℚ(ζ₅)`.

This is the structural fact that underwrites unique factorization of Eisenstein primes — a prerequisite for the cubic-residue symbol definition.

### Jacobi sums (Ireland–Rosen §8.3)

File: `Mathlib/NumberTheory/JacobiSum/Basic.lean`

- `jacobiSum χ ψ = ∑ x : R, χ x * ψ (1 - x)` — the canonical definition.
- `jacobiSum_comm`, `jacobiSum_ringHomComp` — symmetry + naturality.
- `jacobiSum_one_one : jacobiSum (1 : MulChar F R) 1 = #F - 2`.
- `jacobiSum_one_nontrivial : χ ≠ 1 → jacobiSum 1 χ = -1`.
- `jacobiSum_nontrivial_inv : χ ≠ 1 → jacobiSum χ χ⁻¹ = -χ (-1)`.
- `jacobiSum_mul_nontrivial` — main relation `χ φ ≠ 1 → ⋯`.
- `jacobiSum_eq_gaussSum_mul_gaussSum_div_gaussSum` — relates `J(χ,φ)` to Gauss sums.
- `jacobiSum_mul_jacobiSum_inv` — magnitude identity `J(χ,φ) · J(χ,φ)⁻¹ = q`-style.
- `gaussSum_pow_eq_prod_jacobiSum` — `g(χ,ψ)^n = q · ∏ⱼ J(χ, χʲ)` (the structural identity at the heart of Eisenstein's proof).
- `jacobiSum_mem_algebraAdjoin_of_pow_eq_one` — Jacobi sum lies in the algebra adjoined to a root of unity (i.e., `J(χ₃, χ₃) ∈ ℤ[ω]`).

### Multiplicative-character / Gauss-sum surrounding API

- `Mathlib.NumberTheory.MulChar.Lemmas` — `MulChar` API used throughout the cubic-char file.
- `Mathlib.NumberTheory.GaussSum` — Gauss-sum definition and `|g(χ)|^2 = q` for non-trivial χ.
- `Mathlib.RingTheory.RootsOfUnity.Lemmas` — root-of-unity lemmas used by Jacobi-sum membership statements.

## Implication for the two axioms

The two `axiom` declarations in the slug's Lean file are:

1. `cubicResidueSymbol (π : EisensteinPrime) (a : ℤ) : ZMod 3` (line 470)
2. `cubic_reciprocity (π ρ : EisensteinPrime) (h_distinct) (hπ) (hρ) : ⋯ ` (line 491)

Both are predicated on the file's local `structure EisensteinPrime` (line 459). The structure is a placeholder for `IsCyclotomicExtension {3} ℚ K`'s ring of integers — but the actual Mathlib formalization is *richer* (carries the field `K`, the primitive root `ζ`, full PID/unit/norm API). Because the local structure is decoupled from Mathlib's, the axioms are not *strictly* impossible to discharge from Mathlib bearers — but doing so requires first replacing the local `EisensteinPrime` with the Mathlib formulation. This is a non-trivial S6/S7 refactor, *not* a Mathlib upstreaming task.

**The two axioms are therefore "axiomatized pending refactor + formalization", not "axiomatized pending upstream Mathlib feature".** This distinction matters because:

- Future researchers attempting the cubic-reciprocity ACT should *not* wait for a Mathlib PR — the prerequisites are already merged.
- The blocker is engineering effort (rebase local `EisensteinPrime` onto `𝓞 K`, then port Ireland–Rosen §9 proof using the existing `jacobiSum` and `gaussSum` API), not external bearer development.

## Suggested next ACT (S6) — refactor plan

1. **Delete local `structure EisensteinPrime`**; replace with a context `[hKζ : IsCyclotomicExtension {3} ℚ K] (hζ : IsPrimitiveRoot ζ 3)` and use `𝓞 K`.
2. **Define the cubic residue symbol concretely**: for a prime `π : 𝓞 K` (in the sense of `IsCyclotomicExtension.Rat.Three`-style), and `a : ℤ` coprime to `π`,
   `cubicResidueSymbol π a := IsPrimitiveRoot.cubicCharLift (a^((Ideal.absNorm (Ideal.span {π}) - 1) / 3) mod π)`.
   The image lies in `μ₃ ⊆ 𝓞 K`, which `IsPrimitiveRoot.toInteger_cube_eq_one` shows is `{1, η, η^2}`.
3. **Define χ_π : MulChar (𝓞 K ⧸ Ideal.span {π}) (𝓞 K)** as the lift of the cubic residue symbol; check it is a non-trivial `MulChar` of order 3.
4. **Apply `jacobiSum_mem_algebraAdjoin_of_pow_eq_one`** to conclude `J(χ_π, χ_π) ∈ ℤ[ω]`.
5. **Compute `|J|^2 = N(π)`** via `jacobiSum_mul_jacobiSum_inv` and `gaussSum_pow_eq_prod_jacobiSum`.
6. **Derive cubic reciprocity** by comparing `J(χ_π, χ_π)^((N(ρ)-1)/3) mod ρ` against `χ_ρ(N(π))`, following Ireland–Rosen Theorem 1 of Chapter 9 verbatim.

Estimated LOC: ~250 lines of Lean. No new Mathlib bearer needed.

## Files touched by this OBSERVE

- `research/problems/elementary-quadratic-reciprocity-oq-01-oq-02/s5-observe-eisenstein-bearer.md` — this note (NEW).
- `research/problems/elementary-quadratic-reciprocity-oq-01-oq-02/knowledge.md` — sync Phase + 0-sorries; append Session-5.
- `src/data/proofs/elementary-quadratic-reciprocity-oq-01-oq-02/meta.json` — correct `assumptions`, `description`, `keyInsights[4]`, `openQuestions[0]`.
- `proofs/Proofs/ElementaryQuadraticReciprocityOQ01OQ02.lean` — correct docstring comments at lines 455–456 and 489 (text-only; no code change).

Diff is text-only / no proof tactic changes / no `import` changes → 0 build risk. Sorries unchanged (0). Axiom count unchanged (2).

## Audit trail

- Knowledge.md previously asserted "1 sorry" remained (Phase: ACT). The file in fact has 0 sorries since merge of #15356 (2026-05-03) which discharged `cubicChar_kernel_card`. This is an independent drift, also corrected by this PR.
- Memory trap notes (`feedback_researcher_mathlib_head_vs_lockfile_sha_drift.md`) followed: all Mathlib API references in this note were resolved against the **lake-pinned SHA** `2df2f01...`, not Mathlib HEAD.
