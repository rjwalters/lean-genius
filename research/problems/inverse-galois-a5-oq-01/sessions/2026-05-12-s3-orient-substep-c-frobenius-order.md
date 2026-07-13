# S3 ORIENT — sub-step (c) micro-design: `orderOf σ = 3` via stabilizer-inertia bridge

**Slug**: `inverse-galois-a5-oq-01`
**Phase**: ORIENT (doc-only — no Lean code or gallery JSON modified)
**Author**: researcher-12
**Date**: 2026-05-12
**Scope**: sub-step (c) of S4 ACT — the ~100-150 LOC piece that, given a prime ideal `Q : Ideal (𝓞 K)` over `(7)` with `inertiaDegIn = 3` (constructed in sub-step (b) per PR #18315), proves `orderOf (arithFrobAt ℤ q.Gal Q) = 3`.

## 1. Position vs in-flight PRs

| PR | Sub-step | Status | Files touched |
|---|---|---|---|
| #18129 | S1 OBSERVE | merged | problem.md, knowledge.md, state.md, JSON |
| #18155 | S2 ACT scaffold | merged | Proofs/InverseGaloisA5Dedekind.lean (new), Proofs.lean |
| #18242 | S3 sub-step (a) audit | merged | knowledge.md, state.md, JSON |
| #18212 | S3 sub-step (a) audit | OPEN, stale | knowledge.md, state.md, JSON (superseded by #18242) |
| #18315 | S3 sub-step (b) micro-design | merged | sessions/2026-05-12-s3-orient-substep-b-prime-ideal-via-kummer-dedekind.md (only) |
| **this PR** | **S3 sub-step (c) micro-design** | **doc-only** | sessions/2026-05-12-s3-orient-substep-c-frobenius-order.md (only) |

Sub-step (c) is **orthogonal** to all in-flight PRs (touches only a single new `sessions/...md` file). PR #18212's still-open meta-edit set does not collide.

## 2. The goal

Given the S2 scaffold (`InverseGaloisA5Dedekind.lean`, 76 LOC) and sub-step (b)'s output:

```lean
-- output of sub-step (b), per PR #18315:
noncomputable def Q : Ideal (𝓞 q.SplittingField) := ...
instance : Q.IsPrime := ...
instance : Finite (𝓞 q.SplittingField ⧸ Q) := ...
theorem Q_inertiaDegIn : (Q.under ℤ).inertiaDegIn (𝓞 q.SplittingField) = 3 := ...
theorem Q_lies_over_seven : Q.under ℤ = Ideal.span {(7 : ℤ)} := ...
```

The sub-step (c) deliverable is:

```lean
noncomputable def σ : q.Gal := arithFrobAt ℤ q.Gal Q
theorem σ_orderOf : orderOf σ = 3
theorem exists_gal_order_three : ∃ σ : q.Gal, orderOf σ = 3 := ⟨σ, σ_orderOf⟩
```

The last line discharges the **sole remaining sorry** in `InverseGaloisA5Dedekind.lean` (line 67 of state.md). With S5 then splicing this into the parent's `axiom three_dvd_gal_card`, the parent `inverse-galois-a5` proof upgrades from `axiomatized` (1 axiom) to **`verified`** (0 axioms) — a status change for the gallery's first non-solvable inverse-Galois realisation.

## 3. The decisive Mathlib v4.26.0 lemmas

Probed `Mathlib/RingTheory/Frobenius.lean` and `Mathlib/NumberTheory/RamificationInertia/Galois.lean` at the pinned commit. The four load-bearing lemmas:

| Lemma | File:Line | Signature |
|---|---|---|
| `arithFrobAt` (def) | Frobenius.lean:258 | `(R G Q) [Q.IsPrime] [Finite (S ⧸ Q)] : G` |
| `IsArithFrobAt.arithFrobAt` | Frobenius.lean:262 | `(R G Q) → IsArithFrobAt R (arithFrobAt R G Q) Q` |
| `arithFrobAt_mem_stabilizer` | Frobenius.lean:266 | `arithFrobAt R G Q ∈ MulAction.stabilizer G Q` |
| `card_stabilizer_eq_card_inertia_mul_finrank` | Galois.lean:310 | `Nat.card (MulAction.stabilizer G P) = Nat.card (inertia G P) * Module.finrank (R⧸p) (S⧸P)` |
| `card_inertia_eq_ramificationIdxIn` | Galois.lean:333 | `Nat.card (inertia G P) = Ideal.ramificationIdxIn p S` (under Dedekind + torsion-free) |

The chain `arithFrobAt` ⇒ `stabilizer` ⇒ `inertia × finrank` ⇒ `ramIdx × inertiaDeg` is the structural backbone of sub-step (c).

## 4. The proof structure

### 4.1 Upper bound: `orderOf σ ∣ 3` (~30 LOC)

From `IsArithFrobAt.arithFrobAt`, we have the Frobenius congruence:

```
∀ x : 𝓞 K, σ • x ≡ x ^ 7 (mod Q)
```

Therefore `σ^3 • x ≡ x ^ (7³) ≡ x ^ (7³) (mod Q)`. Reducing modulo Q gives an action on `𝓞 K / Q`, which is a finite field `𝔽_q` with `q = 7^3 = 343` (because `inertiaDegIn = 3`). The induced action is Frobenius cubed: `x ↦ x^(7³)`. By `FiniteField.pow_card`, this is the identity on `𝔽_(7³)` (the absolute Frobenius has order = finrank = 3 in `Gal(𝔽_(7³) / 𝔽_7)`).

Together with **unramifiedness** (sub-step (b) shows `ramificationIdxIn = 1` since `7 ∤ disc(q) = 32000² · k` for some `k` — proved in S2 scaffold line 62 already, via `seven_nondiv_disc`), the inertia group of `Q` is trivial. By `card_stabilizer_eq_card_inertia_mul_finrank`:

```
Nat.card (stabilizer q.Gal Q) = Nat.card (inertia q.Gal Q) * finrank (ℤ ⧸ 7ℤ) (𝓞 K ⧸ Q)
                              = 1 * 3 = 3
```

Since `σ` stabilizes `Q` (`arithFrobAt_mem_stabilizer`), `σ ∈ stabilizer q.Gal Q`, so `orderOf σ ∣ Nat.card (stabilizer q.Gal Q) = 3` by `orderOf_dvd_card`.

### 4.2 Lower bound: `3 ∣ orderOf σ` (~50 LOC)

This is the harder direction and where most of the LOC budget lives.

Strategy: show that `σ` is not the identity (so `orderOf σ ≥ 2`), and that `σ` is not order-2 (so `orderOf σ ≥ 3`). Since `orderOf σ ∣ 3` from §4.1 and `orderOf σ > 1, ≠ 2`, the only divisor of 3 left is 3 itself.

But there is a cleaner route via the **residue-field Galois action**:

```lean
-- The action of `stabilizer q.Gal Q` on `𝓞 K / Q` factors through Gal(𝔽_(7³) / 𝔽_7).
-- This quotient map is surjective at unramified primes (since inertia = 1).
-- σ maps to absolute Frobenius (the canonical generator of Gal(𝔽_(7³) / 𝔽_7)).
-- Absolute Frobenius has order 3 in this Galois group.
-- Therefore σ has order ≥ 3 in q.Gal.
```

Mathlib v4.26 packages this as `Ideal.Quotient.stabilizerHom`:

```lean
theorem Ideal.Quotient.stabilizerHom_surjective :
    Function.Surjective (Ideal.Quotient.stabilizerHom G p P)
-- (from Mathlib/RingTheory/Invariant/Basic.lean, audited in PR #18242)
```

The surjective map sends `σ` to its action on `𝓞 K / Q`. At unramified primes, this map is also **injective** (by `card_stabilizer_eq_card_inertia_mul_finrank` with inertia = 1), hence an **isomorphism** `stabilizer q.Gal Q ≃* Gal(𝔽_(7³) / 𝔽_7)`. The right-hand side is cyclic of order 3 (`FiniteField.galois_field_finrank_eq_card`-style result, or directly `Gal(𝔽_(p^n) / 𝔽_p) ≃ ZMod n`).

Under this isomorphism, `arithFrobAt ℤ q.Gal Q` maps to the **canonical Frobenius generator** of `Gal(𝔽_(7³) / 𝔽_7)`, which has order exactly 3.

**Total**: `orderOf σ = orderOf (canonical Frobenius in Gal(𝔽_(7³) / 𝔽_7)) = 3`.

### 4.3 Combining (~10 LOC)

```lean
theorem σ_orderOf : orderOf σ = 3 := by
  -- σ ∈ stabilizer (from arithFrobAt_mem_stabilizer)
  -- stabilizer ≃* Gal(𝔽_(7³) / 𝔽_7) (cyclic of order 3)
  -- σ maps to absolute Frobenius (order 3)
  -- hence orderOf σ = 3 in stabilizer, hence in q.Gal
  exact ...
```

## 5. LOC budget (refined)

| Piece | Mechanical lines | Justification |
|---|---|---|
| Set up the action of `q.Gal` on `𝓞 q.SplittingField` (already in S2 scaffold or sub-step (b)) | 0 | inherited |
| Unramifiedness: `Q.ramificationIdxIn = 1` | 20 | uses `seven_nondiv_disc` + `Ideal.ramificationIdxIn_eq_one_of_isUnramifiedAt` (or `ne_bot` + `discr_dvd`) |
| Inertia = 1: `Nat.card (Q.inertia q.Gal) = 1` | 10 | applies `card_inertia_eq_ramificationIdxIn` |
| Stabilizer order = 3: `Nat.card (stabilizer q.Gal Q) = 3` | 15 | applies `card_stabilizer_eq_card_inertia_mul_finrank` with `finrank = inertiaDegIn = 3` |
| Upper bound: `orderOf σ ∣ 3` | 10 | `arithFrobAt_mem_stabilizer` + `orderOf_dvd_card` |
| Residue-field isomorphism + Frobenius generator | 60 | `stabilizerHom_surjective` + injectivity at unramified primes + `FiniteField.pow_card`-style |
| Lower bound + final equality | 15 | `orderOf σ ≥ 3` from residue-field image |
| Glue to `exists_gal_order_three` | 5 | already in S2 scaffold line 67-73 (replace the sorry) |
| **Total** | **~135 LOC** | midpoint of S3 audit estimate (100-150) |

## 6. Three tentative API names to verify pre-flight

Three lemma names whose existence/signature at Mathlib v4.26.0 was not verified by direct fetch:

1. **`Ideal.ramificationIdxIn_eq_one_of_isUnramifiedAt`** — converts a discriminant-non-divisibility into ramification-index-1. **Risk: medium.** Mathlib may name this `Ideal.IsUnramified.ramificationIdx_eq_one` or factor through `Algebra.IsUnramifiedAt`. If absent, derive from `Ideal.ramificationIdx_eq_one_iff` + the local Dedekind characterization (~15 extra LOC).

2. **`Ideal.Quotient.stabilizerHom`** + **`stabilizerHom_injective_of_inertia_trivial`** — Mathlib has `stabilizerHom_surjective` in `Mathlib/RingTheory/Invariant/Basic.lean` (audited in #18242). The injectivity counterpart at unramified primes is likely named differently or follows from `MulEquiv.ofBijective` after exhibiting both surjectivity and equal cardinality. **Risk: low** (cardinality argument is direct).

3. **`Gal_finiteField_isCyclic`** (canonical Frobenius generator of `Gal(𝔽_(p^n) / 𝔽_p)` has order `n`) — Mathlib has `FiniteField.galoisGroup_isCyclic` and `FiniteField.frobenius_pow` style lemmas. **Risk: low.** If the exact named generator differs, the `FiniteField.pow_card` + cardinality argument is structurally robust.

## 7. Risks and anti-targets

### 7.1 Load-bearing risks

- **Universe handling.** `q.Gal = q.SplittingField ≃ₐ[ℚ] q.SplittingField` is `Type 0`-pinned in the parent. `arithFrobAt` is universe-polymorphic; instances should unify but may require explicit type ascription.
- **`MulSemiringAction` instance synthesis.** The parent file does not currently expose a `MulSemiringAction q.Gal (𝓞 q.SplittingField)` instance. Sub-step (b) should produce this (via `Algebra.isInvariant_of_isGalois` + `IsIntegralClosure.MulSemiringAction`); this PR assumes (b) has done so.
- **Finiteness of the residue field.** `Finite (𝓞 q.SplittingField ⧸ Q)` is required for `arithFrobAt`. Follows from `[𝓞/Q : ℤ/7] = 3 < ∞` + `Finite (ZMod 7)`, but may need explicit `IsNoetherian` + `Module.Finite` chain. ~5 LOC ETA.

### 7.2 Anti-targets

1. **Do not edit `proofs/Proofs/InverseGaloisA5Dedekind.lean`.** That is the S4 ACT artifact; this is a design doc only.
2. **Do not edit the parent `proofs/Proofs/InverseGaloisA5.lean`.** Axiom replacement is S5 CLOSE, not S4.
3. **Do not touch `proofs/Proofs.lean`** (master import list — touched by #18155 already).
4. **Do not run `lake build` or any Docker build.** Doc-only session.
5. **Do not edit `state.md`, `knowledge.md`, `problem.md`, or the gallery JSON.** Those are touched by stale PR #18212 (a meta-edit conflict zone). The session-note pattern (analogous to PR #18315) is conflict-free.
6. **Do not attempt sub-step (b) work** (prime ideal construction). That is PR #18315's scope.

## 8. S4 ACT execution checklist (for the next researcher)

When S4 ACT is unblocked (sub-steps (a), (b), (c) all designed), the build sequence is:

1. **Branch off origin/main** (no need to wait for #18212 — it's stale and may be closed).
2. **Verify three tentative API names** via `gh api .../contents/Mathlib/...` (~5 min).
3. **Write sub-step (a) typeclass plumbing** (~30-50 LOC, per state.md:116-120).
4. **Write sub-step (b) prime ideal** per PR #18315's micro-design (~100-150 LOC).
5. **Write sub-step (c) Frobenius order** per this micro-design (~135 LOC).
6. **Glue to `exists_gal_order_three`** (~5 LOC, replacing the sorry).
7. **Build**: `./proofs/scripts/docker-build.sh Proofs.InverseGaloisA5Dedekind` (~45 min wall-clock).
8. **PR with `(build pending)` label** if build doesn't finish in session window; deployer/auditor will validate.

**Total S4 ACT budget**: ~230-340 LOC across one Lean file + one import line, 1 sorry eliminated, 0 axioms added. After S5 CLOSE: parent axiom count 1 → 0, status `axiomatized` → `verified`.

## 9. Honesty

- This is **doc-only S3 ORIENT sub-step (c)**. No Lean edits. No build. No proof of `σ_orderOf` is included.
- The 135 LOC estimate is a **forecast** based on Mathlib v4.26.0 API audits at the structural level (lemma signatures verified; tactic chains sketched but not type-checked).
- The session-note pattern matches PR #18315's precedent: pristine new `sessions/...md` file, orthogonal to all in-flight PRs.
- **Originality framing**: sub-step (c) is **not a contribution**; it is the Mathlib-side mechanical bridge from `arithFrobAt` to a concrete integer order. The genuine non-Mathlib content lives in S5 (parent axiom replacement) and in S4's sub-step (b) (the explicit prime ideal exhibition, which #18315 already designed).

## 10. References

- PR #18129 (S1 OBSERVE): three-route survey for axiom three_dvd_gal_card elimination
- PR #18155 (S2 ACT): InverseGaloisA5Dedekind.lean scaffold (1 sorry)
- PR #18242 (S3 sub-step (a)): Mathlib AlgHom.IsArithFrobAt API audit
- PR #18315 (S3 sub-step (b)): Kummer–Dedekind prime ideal construction micro-design
- PR #18212 (open, stale): superseded sub-step (a) audit — meta-edit
- Mathlib refs:
  - `Mathlib/RingTheory/Frobenius.lean:54-280` (arithFrobAt + IsArithFrobAt API)
  - `Mathlib/NumberTheory/RamificationInertia/Galois.lean:310-340` (card_stabilizer + card_inertia identities)
  - `Mathlib/RingTheory/Invariant/Basic.lean` (`stabilizerHom_surjective`)
- Number theory refs:
  - Neukirch (1999), §I.9: Frobenius element at unramified primes is a canonical generator of the decomposition group
  - Lang (1994), §I.7: decomposition / inertia exact sequence
  - Dummit & Foote (2004), §14.8: Dedekind's theorem on splitting behaviour
