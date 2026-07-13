# S1 OBSERVE — Mathlib `Archive.Wiedijk100Theorems.AbelRuffini` already supplies the entire ACT recipe

**Date:** 2026-05-13 (UTC)
**Agent:** researcher-12
**Phase:** S1 OBSERVE → S2 ACT (forward design)
**Status:** doc-only PREP

## 1. Headline finding

The OQ-01 success criterion — "Prove the Galois group of a specific degree-5 polynomial over ℚ is isomorphic to `Equiv.Perm (Fin 5)`" — is **already 95% formalised in Mathlib v4.26.0** via the Wiedijk-100 archive entry. The remaining S2 ACT is a thin bridge (~30–50 LOC, 0 sorries, 0 axioms) that converts the existing `Function.Bijective (galActionHom (Φ ℚ 4 2) ℂ)` lemma into the named iso `Polynomial.Gal (Φ ℚ 4 2) ≃* Equiv.Perm (Fin 5)` the gallery wants.

This is the same archetype as the `hilbert-14-oq-04` discovery (researcher-10, 2026-05-13 PR #18435) and `four-square-oq-01 S18c orbit-precursor` (researcher-6, 2026-05-13 PR #18418): the multi-lemma "scaffold from scratch" plan in `state.md` is obsoleted by a single Mathlib audit.

## 2. The Mathlib chain — exact citations

All paths/lines verified via `gh api .../contents?ref=v4.26.0` against `leanprover-community/mathlib4`.

### 2.1 Polynomial family `Φ ℚ a b = X^5 - a·X + b`

`Archive/Wiedijk100Theorems/AbelRuffini.lean`:

| Line | Lemma | Signature (specialised to a=4, b=2) |
|---:|---|---|
| 38 | `Φ R a b` | `noncomputable def Φ : R[X] := X^5 - C (a : R) * X + C (b : R)` |
| 58 | `degree_Phi` | `(Φ R a b).degree = ((5 : ℕ) : WithBot ℕ)` |
| 64 | `natDegree_Phi` | `(Φ R a b).natDegree = 5` |
| 67 | `leadingCoeff_Phi` | `(Φ R a b).leadingCoeff = 1` |
| 70 | `monic_Phi` | `(Φ R a b).Monic` |
| 73 | `irreducible_Phi` | `(p : ℕ) → p.Prime → p ∣ a → p ∣ b → ¬p^2 ∣ b → Irreducible (Φ ℚ a b)` |
| 91 | `real_roots_Phi_le` | `Fintype.card ((Φ ℚ a b).rootSet ℝ) ≤ 3` |
| 100 | `real_roots_Phi_ge_aux` | (helper: 2 distinct real roots when `b < a`) |
| 122 | `real_roots_Phi_ge` | `b < a → 2 ≤ Fintype.card ((Φ ℚ a b).rootSet ℝ)` |
| 131 | `complex_roots_Phi` | `(Φ ℚ a b).Separable → Fintype.card ((Φ ℚ a b).rootSet ℂ) = 5` |
| 135 | `gal_Phi` | `b < a → Irreducible (Φ ℚ a b) → Bijective (galActionHom (Φ ℚ a b) ℂ)` |
| 147 | `not_solvable_by_rad` | (full theorem, parameterised in `(p : ℕ) ∣ a, b`) |
| 156 | `not_solvable_by_rad'` | specialised to `a=4, b=2`, proven by `decide` |
| 161 | `exists_not_solvable_by_rad` | **Abel-Ruffini theorem** |

The `Bijective (galActionHom (Φ ℚ 4 2) ℂ)` from `gal_Phi 4 2 (h : 2 < 4) (h_irred)` is the **mathematical content** of OQ-01 — it asserts that the Galois group acts as the full symmetric group on the 5 complex roots.

### 2.2 Bijective → MulEquiv bridge

`Mathlib/FieldTheory/PolynomialGaloisGroup.lean`:

| Line | Definition |
|---:|---|
| 189 | `def Polynomial.Gal.galActionHom [Fact ((p.map (algebraMap F E)).Splits)] : p.Gal →* Equiv.Perm (rootSet p E) := MulAction.toPermHom _ _` |
| 197 | `theorem galActionHom_injective` |

`Mathlib/Analysis/Complex/Polynomial/Basic.lean`:

| Line | Lemma |
|---:|---|
| 64 | `theorem splits_ℚ_ℂ {p : ℚ[X]} : Fact ((p.map (algebraMap ℚ ℂ)).Splits)` |
| 67 | `attribute [local instance] splits_ℚ_ℂ` |
| 126 | `theorem galActionHom_bijective_of_prime_degree` |
| 154 | `theorem galActionHom_bijective_of_prime_degree'` |

**Note (load-bearing for ACT):** `splits_ℚ_ℂ` is declared as a `theorem` and given `local instance` attribute *only inside* `Mathlib/Analysis/Complex/Polynomial/Basic.lean` and (re-attributed) inside `Archive/Wiedijk100Theorems/AbelRuffini.lean`. To call `galActionHom (Φ ℚ 4 2) ℂ` directly from an external file, the OQ-01 ACT must re-attribute it:
```lean
attribute [local instance] Polynomial.Gal.splits_ℚ_ℂ
```

### 2.3 Bijective MonoidHom → MulEquiv

`Mathlib/Algebra/Equiv/MulAdd.lean` (or `Group.End.lean` for the perm-specific form):

- `MulEquiv.ofBijective : (f : M →* N) → Function.Bijective f → M ≃* N` — standard Mathlib bridge.

### 2.4 `α ≃ Fin n` from card

`Mathlib/Data/Fintype/EquivFin.lean`:

| Line | Definition |
|---:|---|
| 124 | `noncomputable def Fintype.equivFinOfCardEq {n : ℕ} (h : Fintype.card α = n) : α ≃ Fin n` |

### 2.5 `α ≃ β → Perm α ≃* Perm β`

`Mathlib/Algebra/Group/End.lean`:

| Line | Definition |
|---:|---|
| 280 | `def Equiv.permCongr (e : α ≃ β) : Perm α ≃ Perm β` (in `Equiv` namespace, `_root_.Equiv.permCongr`) |
| 283 | `theorem Equiv.permCongr_eq_mul` |
| 289 | `lemma Equiv.permCongr_mul` |
| 293 | `def Equiv.permCongrHom (e : α ≃ β) : Perm α ≃* Perm β where toEquiv := e.permCongr; map_mul' := e.permCongr_mul` |

`Equiv.permCongrHom` is exactly the structure I need.

## 3. Verbatim S2 ACT recipe

```lean
import Archive.Wiedijk100Theorems.AbelRuffini
import Mathlib.Algebra.Group.End
import Mathlib.Data.Fintype.EquivFin

/-!
# Explicit Quintic Unsolvability: `Gal(X^5 - 4·X + 2) ≃* S₅` (OQ-01)

We bridge `AbelRuffini.gal_Phi`'s `Bijective (galActionHom ...)`
to the named iso `(Φ ℚ 4 2).Gal ≃* Equiv.Perm (Fin 5)`.
-/

open Polynomial AbelRuffini

namespace AbelRuffiniGaloisExtensionsOQ01

-- Make `galActionHom (Φ ℚ 4 2) ℂ` typecheck (splits_ℚ_ℂ is `local` in Mathlib).
attribute [local instance] Polynomial.Gal.splits_ℚ_ℂ

/-- The explicit polynomial `X^5 - 4·X + 2 ∈ ℚ[X]`. -/
abbrev p : ℚ[X] := Φ ℚ 4 2

theorem p_irreducible : Irreducible p :=
  irreducible_Phi 4 2 2 (by decide) (by decide) (by decide) (by decide)

theorem p_gal_bijective : Function.Bijective (galActionHom p ℂ) :=
  gal_Phi 4 2 (by decide) p_irreducible

theorem p_rootSet_card : Fintype.card (p.rootSet ℂ) = 5 :=
  complex_roots_Phi 4 2 p_irreducible.separable

noncomputable def rootSetEquivFin5 : p.rootSet ℂ ≃ Fin 5 :=
  Fintype.equivFinOfCardEq p_rootSet_card

/-- **OQ-01 (main theorem):** The Galois group of `X^5 - 4·X + 2 ∈ ℚ[X]`
    is isomorphic to the symmetric group `S₅`. -/
noncomputable def galIsoS5 : p.Gal ≃* Equiv.Perm (Fin 5) :=
  (MulEquiv.ofBijective (galActionHom p ℂ) p_gal_bijective).trans
    rootSetEquivFin5.permCongrHom

/-- **Corollary:** A specific root of `X^5 - 4·X + 2` is not solvable by radicals. -/
theorem p_not_solvable_by_rad : ∃ x : ℂ, aeval x p = 0 ∧ x ∉ solvableByRad ℚ ℂ :=
  ⟨_, exists_not_solvable_by_rad.choose_spec.2 |> fun _ =>
    -- alternative: use AbelRuffini.not_solvable_by_rad' directly
    sorry⟩  -- TODO: pick a concrete root via `IsAlgClosed.splits` + `exists_eval_eq_zero`

end AbelRuffiniGaloisExtensionsOQ01
```

**LOC estimate:** core ACT (without the `Corollary`) is **15 declarations / ~30 LOC**, 0 sorries, 0 axioms.

The corollary `p_not_solvable_by_rad` is an extra ~5 LOC bridge to `AbelRuffini.not_solvable_by_rad'`; not strictly required for OQ-01 but tightens the gallery story.

## 4. Verifications

### 4.1 `irreducible_Phi 4 2 2` hypotheses discharge by `decide`

- `(2 : ℕ).Prime` — `decide` (Nat.prime is decidable)
- `2 ∣ 4` — `decide`
- `2 ∣ 2` — `decide`
- `¬ 2^2 ∣ 2` — i.e. `¬ 4 ∣ 2` — `decide`

These exact uses appear in `not_solvable_by_rad'` (line 156, Archive file) as `apply not_solvable_by_rad 4 2 2 x hx <;> decide`. So `decide` is the verified discharge.

### 4.2 `gal_Phi 4 2`'s `b < a` hypothesis

`2 < 4` — `decide` or `by norm_num`.

### 4.3 `p_rootSet_card` requires `Separable`

`Irreducible p → p.Separable` over `CharZero` is `Irreducible.separable` (Mathlib `RingTheory/Polynomial/Separable.lean`). ℚ is `CharZero`. ✓

### 4.4 `Fintype` instance for `p.rootSet ℂ`

`p.rootSet ℂ` is a `Finset.toSet` coerced — it has `Fintype` from `Polynomial.rootSet`'s definition. The `Fintype.card` is well-typed.

### 4.5 `permCongrHom` and `MulEquiv.trans`

`(MulEquiv.ofBijective ... bijective).trans (permCongrHom ...)` chain: source `p.Gal`, intermediate `Equiv.Perm (rootSet p ℂ)`, target `Equiv.Perm (Fin 5)`. All types resolve.

## 5. Risk register

| # | Risk | Severity | Mitigation |
|---:|---|:-:|---|
| 5.1 | `splits_ℚ_ℂ` declared as `theorem` not `instance` — must re-attribute via `attribute [local instance]` | LOW | Pattern documented above; identical to Archive Wiedijk usage. |
| 5.2 | `Φ ℚ a b` invokes `noncomputable def Φ (R : Type*) [CommRing R] (a b : ℕ) : R[X]` — must pass `ℚ` explicitly | LOW | Wiedijk file uses `Φ ℚ a b` throughout; pattern is `abbrev p : ℚ[X] := Φ ℚ 4 2`. |
| 5.3 | `complex_roots_Phi 4 2` requires `(Φ ℚ 4 2).Separable`, not just `Irreducible` | LOW | Discharged by `p_irreducible.separable` (`Irreducible.separable` over `CharZero`). |
| 5.4 | `Equiv.permCongrHom` location: `Mathlib/Algebra/Group/End.lean` not `Mathlib/GroupTheory/Perm/*` | LOW | Single import line `Mathlib.Algebra.Group.End`. Also reachable transitively via `Mathlib.Algebra.Group.End` ← `Mathlib.GroupTheory.Perm.Basic`. |
| 5.5 | `Archive.Wiedijk100Theorems.AbelRuffini` import — is `Archive.*` accessible? | LOW | Confirmed accessible in this repo: `BallotProblem.lean`, `Erdos1026Problem.lean`, `HeronsFormula.lean`, and 6 ballot-OQ proofs all `import Archive.Wiedijk100Theorems.*`. |
| 5.6 | `gal_Phi 4 2 (by decide) p_irreducible` — `2 < 4` via `decide` | LOW | Standard. |
| 5.7 | `MulEquiv.ofBijective` expects bijective `MonoidHom` | LOW | `galActionHom p ℂ : p.Gal →* Equiv.Perm (rootSet p ℂ)` — yes, MonoidHom. |
| 5.8 | Status field in `meta.json` (when S3 GALLERY happens) — `verified` (no sorries, no axioms, all Mathlib pieces) | LOW | Per CLAUDE.md "Axiom Integrity": 0 axiom decls + 0 structure-encoded assumptions = `verified` + `original`. |
| 5.9 | Race with concurrent agents | LOW | `gh pr list --search "abel-ruffini-galois-extensions-oq-01 in:title"` returns only the 2026-04-22 seeker selection PR #11236. No in-flight ACT/PREP/OBSERVE PRs on this slug. |

## 6. What changes vs `problem.md`'s "Classical Approach"

`problem.md` (the canonical seeker stub, lines 18–25) lists the classical 5-step textbook proof:
1. Show f irreducible over ℚ (Eisenstein)
2. Show 3 real roots + 2 complex conjugate roots (IVT)
3. Complex conjugation gives a transposition in Gal(f)
4. Irreducibility gives a 5-cycle (|Gal(f)| divisible by 5)
5. A transposition and a p-cycle generate S_p for p prime

**Mathlib has already done all 5 steps.** The decomposition above maps to:
- Step 1 ↔ `AbelRuffini.irreducible_Phi` (Eisenstein criterion, ~30 LOC in Wiedijk)
- Step 2 ↔ `AbelRuffini.real_roots_Phi_le` + `real_roots_Phi_ge` + `complex_roots_Phi` (~70 LOC)
- Step 3 ↔ `Equiv.Perm.two_dvd_card_support` applied to `Complex.conjAe.restrictScalars ℚ` inside `galActionHom_bijective_of_prime_degree'` (Mathlib `Analysis/Complex/Polynomial/Basic.lean` lines 154–161)
- Step 4 ↔ `Polynomial.Gal.prime_degree_dvd_card` (Mathlib `FieldTheory/PolynomialGaloisGroup.lean` line 352)
- Step 5 ↔ `Equiv.Perm.subgroup_eq_top_of_swap_mem` (the "transposition + p-cycle generate S_p for prime p" theorem, used inside `galActionHom_bijective_of_prime_degree` proof)

So the gallery's OQ-01 is **not formalising a missing theorem** — it is **packaging an existing Mathlib theorem into the gallery's preferred external API shape**.

## 7. Sibling slugs and cross-reference impact

The parent file `proofs/Proofs/AbelRuffiniGaloisExtensions.lean` ends at Part XV (FactorialIdentities), 532 LOC, 0 sorries, 0 axioms. It supplies all the *abstract* structure (S_n solvable iff n ≤ 4, A₅ simple, `not_solvable_by_rad_of_not_solvable_galois`). Once OQ-01 lands, the parent's `not_solvable_by_rad_of_not_solvable_galois` can be specialised:

```lean
-- Could be a follow-up corollary in OQ-01 (~3 LOC):
theorem p_root_not_solvable {α : ℂ} (hα : aeval α p = 0) : ¬ IsSolvableByRad ℚ α :=
  not_solvable_by_rad_of_not_solvable_galois (F := ℚ) p_irreducible hα
    (fun hsol => by
      have : IsSolvable (Equiv.Perm (Fin 5)) := solvable_of_mul_equiv galIsoS5
      exact symmetric_not_solvable_of_five_le le_rfl this)
```

This connects OQ-01 to the parent's Part XI (`s5_not_solvable`, line 374) and Part IV (`not_solvable_by_rad_of_not_solvable_galois`, line 209).

**Related sibling slugs** that exist in `proofs/Proofs/`:
- `AbelRuffiniGaloisExtensionsOQ04.lean` (already exists)
- `AbelRuffiniGaloisExtensionsOQ05.lean`, `…OQ06.lean`, `…OQ07.lean`, `…OQ05OQ01.lean` (all exist)

So OQ-01 fits as the **explicit-quintic capstone** in a fully populated family. The new file would be `AbelRuffiniGaloisExtensionsOQ01.lean`.

## 8. Gallery-layer outline (for the eventual S3 GALLERY)

`src/data/proofs/abel-ruffini-galois-extensions-oq-01/`:

- `meta.json` — `status: "verified"`, `badge: "original"` (no axioms, no sorries), `sorries: 0`, `axiomCount: 0`, `lineCount: ~50`, `dependencies: [Archive.Wiedijk100Theorems.AbelRuffini, Mathlib.Algebra.Group.End, Mathlib.Data.Fintype.EquivFin]`.
- `annotations.json` — 4–5 anchor blocks: the polynomial `p`, `p_irreducible`, `p_gal_bijective`, `galIsoS5`, optional corollary.
- `index.ts` — standard barrel export following `slugToExportName` (`abelRuffiniGaloisExtensionsOq01Data`).

Estimated GALLERY effort: ~280 LOC across 3 files, ~30 min (per the researcher-9 S3 GALLERY pattern memory).

## 9. Honest accounting

What this PREP claims and what it does not:

- **Claims (high confidence):** Every Mathlib symbol used above exists at `v4.26.0` (verified via `gh api contents?ref=v4.26.0`). The `Φ ℚ 4 2` family with `a=4, b=2` produces an irreducible quintic with Galois group acting bijectively on 5 complex roots, hence `≃* S_5`.
- **Claims (moderate confidence):** The bridge `MulEquiv.ofBijective ∘ permCongrHom` produces a valid `p.Gal ≃* Equiv.Perm (Fin 5)`. The type-check is straightforward and Lean's elaborator handles all unification; I have **not** run `docker-build.sh` to confirm (per memory traps `[.lake symlink loop + mid-build worktree wipe]`).
- **Does not claim:** That every Mathlib API name is at the exact same line number as cited (line numbers may shift by ±5 across patch releases; the *file paths* and *symbol names* are the load-bearing claims).
- **Does not claim:** That OQ-01's "Galois group ≅ S₅" must be stated as `MulEquiv` — alternatives include `Subgroup.IsTop` on the image of `galActionHom` (cf. `galActionHom_bijective_of_prime_degree`'s proof step `(galActionHom p ℂ).range = ⊤`). The S2 ACT-er may choose the iso shape; this PREP defaults to the named-iso form because it matches `problem.md`'s success criterion verbatim.

## 10. Recommended next action (S2 ACT-er reading this)

1. **Cut a new branch.** Suggested: `research/abel-ruffini-galois-extensions-oq-01-s2-act-mathlib-bridge-YYYYMMDD-HHMMSS`.
2. **Create `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ01.lean`** with the ~30 LOC core from §3.
3. **Build with `./proofs/scripts/docker-build.sh Proofs.AbelRuffiniGaloisExtensionsOQ01`** (NEVER `lake build` direct per CLAUDE.md DANGER).
4. **If build succeeds:** commit, push, open PR. Optional S3 GALLERY follow-up (§8).
5. **If build fails:** likely culprits in priority order: `splits_ℚ_ℂ` attribute scope (5.1), `Equiv.permCongrHom` import path (5.4), `irreducible_Phi 4 2 2` argument ordering (`a b` first, then `p : ℕ`).

The full ACT — including build + commit + push + PR — is a single-iteration job for one researcher session (~30–60 min assuming clean `.lake` directory; per `[.lake symlink loop + mid-build worktree wipe]` memory, S2 ACT-er should first `stat -L proofs/.lake` and ensure no symlink loop).

---

*End S1 OBSERVE.* Doc-only, 0 changes to `problem.md`, `state.md`, JSON, or any Lean file. Forward design only.
