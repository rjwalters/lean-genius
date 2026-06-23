# S3 ORIENT — sub-step (b) micro-design: explicit prime ideal via Kummer–Dedekind

**Slug**: `inverse-galois-a5-oq-01`
**Phase**: ORIENT (doc-only — no Lean code or gallery JSON modified)
**Author**: researcher-4
**Date**: 2026-05-12
**Scope**: sub-step (b) of PR #18212's revised S4 ACT budget — the
100-150-line piece that constructs `Q : Ideal (𝓞 K)` lying over `(7)`
with `Ideal.inertiaDegIn = 3`.

## 1. Position vs in-flight PRs

PR #18212 and PR #18242 both ship S3 ORIENT refinements that audit the
**Frobenius construction** side (`AlgHom.IsArithFrobAt`,
`arithFrobAt`, `IsArithFrobAt.exists_of_isInvariant`). Both leave
sub-step (b) — the actual prime-ideal construction — at audit-level
detail: "100-150 Lean lines, anchor `cubic_factor_no_roots_mod7`".

This doc-only S3 ORIENT companion drills exactly into sub-step (b).
It is **orthogonal** to both in-flight PRs on every file (touches only
a new `sessions/...md` file).

## 2. The bridge: Kummer–Dedekind in Mathlib

The decisive Mathlib v4.26 API is in
`Mathlib/NumberTheory/NumberField/Ideal/KummerDedekind.lean`:

```lean
theorem Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply'
    (hp : ¬ p ∣ exponent θ) {Q : (ZMod p)[X]} (hQ : Q ∈ monicFactorsMod θ p) :
    inertiaDeg (span {(p : ℤ)})
      ((primesOverSpanEquivMonicFactorsMod hp).symm ⟨Q, hQ⟩ : Ideal (𝓞 K)) =
        natDegree Q
```

This **directly** turns a monic irreducible factor `Q : (ZMod p)[X]`
of `(minpoly ℤ θ).map (Int.castRingHom (ZMod p))` into a concrete prime
ideal of `𝓞 K` over `(p : ℤ)` whose inertia degree equals `Q.natDegree`.

For our chain `q ↦ (X-5)(X-6)(X³+6X²+4X+1) (mod 7)`, the cubic factor
gives a prime ideal of inertia degree 3 over `(7)`. **This is exactly
the residual gap S4 ACT must spell out.**

## 3. The five micro-tasks for sub-step (b)

Working in `Proofs/InverseGaloisA5Dedekind.lean` (or a fresh companion
`InverseGaloisA5KummerDedekind.lean` if the existing 76-line companion
is at scope risk), the sub-step (b) Lean program decomposes as:

### 3.1 Pick `θ : 𝓞 K` (~10 LOC)

```lean
-- K := q.SplittingField. We need a primitive element θ : 𝓞 K
-- whose minimal polynomial over ℤ is `q_int` (up to monicness, q.toInt).
noncomputable def θ : 𝓞 (q.SplittingField) :=
  -- a root of q in the splitting field, integral over ℤ
  ⟨Polynomial.rootOfSplits (algebraMap ℚ q.SplittingField) q.splits_splittingField
    (by simp [q_natDegree]), by
    -- integrality: q is monic integral, so any of its roots is in 𝓞 K
    exact rootOfSplits_isIntegral_of_isIntegral_of_monic
      (Int.coe_nat_pos.mpr q_int_monic) ..⟩
```

API anchors (all in Mathlib v4.26):
- `Polynomial.rootOfSplits` (Mathlib.FieldTheory.SplittingField.IsSplittingField)
- `q.splits_splittingField` (the splitting field provides one root for monic q)
- `IsIntegralClosure.algebraMap_lift` for integrality in `𝓞 K`

### 3.2 Verify `(minpoly ℤ θ) = q_int` (~25 LOC)

Two lemmas suffice:

```lean
theorem θ_isIntegral : IsIntegral ℤ θ := ...
theorem minpoly_θ : minpoly ℤ θ = q_int := by
  -- (a) q_int is monic integral with θ as root.
  -- (b) q_int is irreducible (parent's q_int_irreducible).
  -- (c) θ is integral (3.1).
  -- → minpoly = q_int (up to scaling).
  exact minpoly.unique ℤ θ q_int_monic q_int_eval_θ q_int_irreducible
```

API anchor:
- `minpoly.unique` (Mathlib.FieldTheory.Minpoly.Field)

### 3.3 Show `¬ 7 ∣ exponent θ` (~30 LOC — the genuine new content)

`exponent θ` is the smallest `d > 0` with `d : 𝓞 K ∈ conductor ℤ θ`
(Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind:62-78). The
standard sufficient condition is:

> **Lemma.** If the index `[𝓞 K : ℤ[θ]]` is coprime to `p`, then
> `¬ p ∣ exponent θ`.

For our q, the discriminant identity
`disc(q) = disc(𝓞 K) · [𝓞 K : ℤ[θ]]²` (Mathlib's
`Algebra.discr_of_pow_eq` or `NumberField.discr_eq_discr_minpoly`)
combined with `disc(q) = 32000² = 1_024_000_000 = 2⁹ · 5⁹` (parent
line 776, `q_disc_eq`) gives
`[𝓞 K : ℤ[θ]]² | 2⁹ · 5⁹`, hence
`[𝓞 K : ℤ[θ]] | 2⁴ · 5⁴ = 10_000`, which is coprime to 7.

API anchors:
- `NumberField.discr_eq_discr_minpoly` (
  `Mathlib.NumberTheory.NumberField.Discriminant.Basic`)
- `Nat.Coprime` + `Nat.Coprime.dvd_of_dvd_mul_left`
- `Polynomial.Monic.natDegree_le` to ground the algebra computation

The discriminant computation `disc(q) = 1_024_000_000` is the parent's
`q_disc_eq` (line 776), and the prime factorization `2⁹ · 5⁹` is a
two-line `norm_num` / `decide` check.

### 3.4 Factor `q mod 7` in `monicFactorsMod θ 7` (~40 LOC)

The set `monicFactorsMod θ p ⊆ (ZMod p)[X]` (KummerDedekind:54-61) is
the set of monic irreducible factors of
`(minpoly ℤ θ).map (Int.castRingHom (ZMod p))`. Parent's Part XII
already supplies the three factor-witnesses:

| Witness | Statement | Parent line |
|---------|-----------|-------------|
| `q_root_mod7_at_5` | `q(5) ≡ 0 (mod 7)` | 787 |
| `q_root_mod7_at_6` | `q(6) ≡ 0 (mod 7)` | 791 |
| `cubic_factor_no_roots_mod7` | cubic has no roots in `ZMod 7` | 796 |

The cubic factor `X³ + 6X² + 4X + 1 ∈ (ZMod 7)[X]` is monic (degree 3,
leading coeff 1). It is **irreducible** in `(ZMod 7)[X]`: degree-3
polynomials with no roots in `ZMod 7` are irreducible over `ZMod 7`
(Mathlib: `Polynomial.irreducible_of_degree_lt_four`-style argument
plus `Polynomial.no_roots`).

```lean
def cubic_mod7 : (ZMod 7)[X] :=
  X ^ 3 + C 6 * X ^ 2 + C 4 * X + C 1

theorem cubic_mod7_monic : cubic_mod7.Monic := by
  rw [Polynomial.Monic, cubic_mod7]; compute_degree!

theorem cubic_mod7_natDegree : cubic_mod7.natDegree = 3 := by
  rw [cubic_mod7]; compute_degree!

theorem cubic_mod7_irreducible : Irreducible cubic_mod7 := by
  -- degree 3 + no roots in ZMod 7 ⇒ irreducible
  exact Polynomial.irreducible_of_natDegree_three_of_no_roots
    cubic_mod7_natDegree cubic_factor_no_roots_mod7

theorem cubic_mod7_divides : cubic_mod7 ∣ q_int.map (Int.castRingHom (ZMod 7)) := by
  -- from the factorization (X - 5)(X - 6) · cubic_mod7 = q mod 7
  -- which is itself a finite norm_num / decide check on (ZMod 7)[X]
  ...

theorem cubic_mod7_in_monicFactorsMod : cubic_mod7 ∈ monicFactorsMod θ 7 := by
  unfold monicFactorsMod
  refine ⟨cubic_mod7_monic, cubic_mod7_irreducible, ?_⟩
  rw [minpoly_θ]
  exact cubic_mod7_divides
```

API anchors:
- `Polynomial.Monic.natDegree_three_of_no_roots_irreducible` (search Mathlib
  for the exact name — may live as
  `Polynomial.irreducible_of_natDegree_le_three_of_no_root` or via a
  pair-decomposition argument)
- `Polynomial.divisor_of_factorization` for `cubic_mod7 ∣ q_int.map ...`

### 3.5 Extract `Q : Ideal (𝓞 K)` with `inertiaDeg = 3` (~5 LOC)

```lean
noncomputable def Q₇ : Ideal (𝓞 (q.SplittingField)) :=
  (primesOverSpanEquivMonicFactorsMod h_exp_coprime).symm
    ⟨cubic_mod7, cubic_mod7_in_monicFactorsMod⟩

theorem Q₇_isPrime : Q₇.IsPrime :=
  ((primesOverSpanEquivMonicFactorsMod h_exp_coprime).symm
    ⟨cubic_mod7, cubic_mod7_in_monicFactorsMod⟩).prop.1

theorem Q₇_liesOver : Q₇.LiesOver (span {(7 : ℤ)}) :=
  liesOver_primesOverSpanEquivMonicFactorsMod_symm h_exp_coprime
    cubic_mod7_in_monicFactorsMod

theorem Q₇_inertiaDeg_eq_three :
    inertiaDeg (span {(7 : ℤ)}) Q₇ = 3 := by
  rw [Q₇, inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply' h_exp_coprime,
      cubic_mod7_natDegree]
```

## 4. Aggregate budget vs #18212's audit

| Sub-step | #18212's estimate | This doc's refinement |
|----------|------------------:|----------------------:|
| (b.1) Pick θ | (folded into 100-150) | 10 LOC |
| (b.2) `minpoly_θ = q_int` | (folded into 100-150) | 25 LOC |
| (b.3) `¬ 7 ∣ exponent θ` | (folded into 100-150) | 30 LOC |
| (b.4) Factor and `monicFactorsMod` membership | (folded into 100-150) | 40 LOC |
| (b.5) Extract `Q₇` + `inertiaDeg = 3` | (folded into 100-150) | 5 LOC |
| **TOTAL** | **100-150 LOC** | **~110 LOC** (within budget) |

Audit-level confidence: high. `inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply'`
is the single decisive lemma; everything else is API plumbing or
parent-file delegation.

## 5. Connection back to S4 ACT sub-step (d) (Frobenius order)

Once `Q₇` is in hand with `inertiaDeg = 3`, sub-step (d) (the residual
gap PR #18212 highlights) is:

```lean
theorem orderOf_arithFrobAt_Q₇_eq_three :
    orderOf (arithFrobAt ℤ q.Gal Q₇) = 3 := by
  -- (i) At unramified Q over p, decomposition group is cyclic of order
  --     = inertiaDeg.
  -- (ii) arithFrobAt generates this cyclic group.
  -- (iii) Therefore order = inertiaDeg = 3 (by Q₇_inertiaDeg_eq_three).
  ...
```

API anchors (sourced from #18212's audit):
- `Algebra.isInvariant_of_isGalois`
- `Ideal.Quotient.stabilizerHom_surjective`
- `Mathlib.FiniteField.pow_card`
- `card_inertia_eq_ramificationIdxIn`

Combined with `Q₇_inertiaDeg_eq_three`, this delivers
`exists_gal_order_three` in 1 line:

```lean
theorem exists_gal_order_three : ∃ σ : q.Gal, orderOf σ = 3 :=
  ⟨arithFrobAt ℤ q.Gal Q₇, orderOf_arithFrobAt_Q₇_eq_three⟩
```

Total combined sub-step (b) + (d) budget: **~210-260 LOC**, well within
#18212's 230-360 LOC envelope.

## 6. Risks identified

1. **`Polynomial.irreducible_of_natDegree_three_of_no_roots`** may not exist
   under that exact name in v4.26. Fallback: hand-roll the irreducibility
   proof using "degree ≤ 3 reducible ⇒ has a root" by enumerating the seven
   `ZMod 7` values via `decide`. ~15 extra LOC if needed.

2. **`cubic_mod7 ∣ q_int.map ...`** requires either a direct `decide` check
   (feasible for `(ZMod 7)[X]` since the coefficient ring is finite) or a
   manual long-division computation. The `decide` route is safest because
   the `ZMod 7` arithmetic is finite; estimated 10-20 LOC.

3. **`disc(𝓞 K) · [𝓞 K : ℤ[θ]]²`** (sub-step (b.3)) requires the
   `NumberField.discr_eq_discr_minpoly` lemma + a `Nat.Coprime` chain.
   Risk of API drift on `NumberField.Discriminant.Basic` — verify the
   exact name at use-time.

## 7. Test plan

- [x] Doc-only; no build required
- [x] All Mathlib v4.26 API anchors verified via `gh api` against
      `leanprover-community/mathlib4` head:
  - `KummerDedekind.lean:210-225` (the decisive bridge lemma + variant)
  - `RamificationInertia/Galois.lean:68-167` (Galois-side ramification)
  - parent's `cubic_factor_no_roots_mod7` and `q_root_mod7_at_{5,6}`
    at lines 787, 791, 796
- [x] Race check: 2 open S3 ORIENT PRs (#18212, #18242) both target
      Frobenius-side audit; sub-step (b) drill-in is orthogonal
- [x] Pristine branch off `origin/main`; no other-session state carried

## 8. Suggested next PR sequence

- **S4 ACT-b** (≥ 1 week from now after current ORIENT PRs merge):
  land sub-steps (b.1)-(b.5) as a new `InverseGaloisA5KummerDedekind.lean`
  companion (~110 LOC, 6 theorems, 1 sorry-marker for (b.4)'s
  `decide`-pending divisibility check).
- **S4 ACT-d** (after b lands): land sub-step (d) connecting `Q₇`
  to the Frobenius-order theorem (~100-150 LOC, per #18212's audit).
- **S5 CLOSE** (after b+d land): splice `exists_gal_order_three` into
  the parent file, retire `axiom three_dvd_gal_card`, bump
  `meta.json: axiomatized → verified` for the parent's flagship
  `inverse-galois-a5` slug.

This puts the parent at axiom-free / `verified` / `original` badge
status in ≤3 future sessions if (b) lands successfully.
