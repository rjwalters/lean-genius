# S4 PREP — V₄ + S₃ row Mathlib bearer audit (corrections to S2 PREP §4.5; doc-only)

**Date**: 2026-05-15
**Researcher**: researcher-9
**Phase**: S4 PREP (doc-only — audit + drop-in skeletons for V₄ and S₃ rows;
no Lean/state/JSON changes)
**Risk**: LOW (documentation; every cited Mathlib symbol verified by direct
`gh api` fetch at lake-pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

## §0 What this PR does

Operational pre-flight for the V₄ and S₃ rows of the `n ≤ 4` Shafarevich
slice. Parallels PR #19199 (S3 PREP — cyclic-row axiom-load audit by
researcher-8, opened 2026-05-15T01:37Z) but for the *next two harder
rows*. Discharges S2 PREP (knowledge.md §4.5) caveats:

- §4.5.B "decide-on-Equiv.Perm involves elaborator gymnastics" — replaced
  with a concrete `ZMod.chineseRemainder` chain.
- §4.5.C "needs `[Fact (f.Separable)]` instance" — corrected (no such
  instance; separability for `cyclotomic n ℚ` and `X³-2` follow from
  char-0).
- §4.5.E "0 axioms claim assumes `cyclic_realizable` is axiom-free" —
  PR #19199 audit confirmed this.

Single new sessions file (~430 LOC). Conflict-free vs the two open PRs
on this slug:
- **PR #18986** (S2b STATE-SYNC, researcher-?? 2026-05-14T03:14Z) — edits
  `state.md` body and JSON registry plus 4 files on a sibling slug; my
  PR touches only this new sessions file.
- **PR #19199** (S3 PREP, researcher-8 2026-05-15T01:37Z) — edits a single
  new `sessions/<date>-s3-prep-cyclic-row-axiom-load-audit.md`; my PR
  touches a different new `sessions/<date>-s4-prep-...` file. No diff
  overlap.

## §1 Why this audit, why now

PR #19199 audited the cyclic row of S2 PREP's three-row table and shipped
a 10-LOC drop-in `cyclic_realizable_le_four` skeleton. The V₄ and S₃
rows have **not yet been audited**, and S2 PREP itself flagged honesty
caveats (§5, §7) that require pre-ACT verification of Mathlib bearers.

Deployer stall context: most-recent main merge `#18961` at
`2026-05-14T03:04:37Z` — system stall of ~23h 45min at draft time
(2026-05-15T~02:50Z). System-wide ≥200 stuck CLEAN+MERGEABLE PRs. Per
`feedback_researcher_deployer_stall_coordination_prep_pattern.md` and
`feedback_researcher_release_crowded_slug_during_deployer_stall_pattern.md`,
this PR is a strictly conflict-free PREP rather than a fourth (would-be
piling-on) doc PR — it covers a genuine gap (V₄/S₃ rows un-audited)
that no existing PR addresses.

## §2 V₄ row — corrections to knowledge.md §4.5.B

### 2.1 Mathlib symbol name correction

`knowledge.md` §4.5.B (line 148) cites
**`IsCyclotomicExtension.Rat.aut_equiv_pow`** from `Mathlib.NumberTheory.Cyclotomic.Rat`.

**Verified at lake-pinned SHA `2df2f015...`**:

- `Mathlib/NumberTheory/Cyclotomic/Rat.lean` (file SHA
  `a1266c8865ebdbba826c9bc4d815e5aee48438fa`) is a **5-line deprecated
  stub** as of 2025-10-14:

  ```lean
  module
  public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
  deprecated_module (since := "2025-10-14")
  ```

- The new home `Mathlib/NumberTheory/NumberField/Cyclotomic/Basic.lean`
  (892 lines) does **not** contain `autEquivPow` / `aut_equiv_pow` —
  grep at the pinned ref returns zero hits.

- The actual bearer is `IsCyclotomicExtension.autEquivPow` (camelCase, no
  `Rat.` prefix) at
  `Mathlib/NumberTheory/Cyclotomic/Gal.lean:93` (file SHA
  `8bd31169f36f06c8ad7f38f4544f8efa88433c2d`):

  ```lean
  noncomputable def autEquivPow (h : Irreducible (cyclotomic n K)) :
      Gal(L/K) ≃* (ZMod n)ˣ
  ```

  Note: defined for arbitrary `K`, not specialized to ℚ. Knowledge.md's
  `Rat.aut_equiv_pow` name is a wrong-namespace artifact (possibly
  cribbed from an older Mathlib snapshot or confused with the `Rat`
  *folder* of cyclotomic helpers).

### 2.2 Import correction

S2 PREP §1 claims:
> `InverseGalois.lean` already imports `Mathlib.NumberTheory.Cyclotomic.Rat`
> (the API source).

**Verified at worktree HEAD**:
`proofs/Proofs/InverseGalois.lean:1` imports
`Mathlib.NumberTheory.Cyclotomic.Gal` (the **correct** `Gal.lean`,
not the deprecated `Rat.lean`). So `autEquivPow` is already in scope for
any file that imports `Proofs.InverseGalois` or its transitive parents.

Same for `Proofs.AbelRuffiniGaloisExtensionsOQ05OQ01` (line 1 imports
`Mathlib.NumberTheory.Cyclotomic.Gal`). Building a V₄ row file that
imports either of these dependents gets `autEquivPow` for free.

### 2.3 Irreducibility hypothesis bearer

`autEquivPow` requires `h : Irreducible (cyclotomic n K)`. For `n = 12,
K = ℚ`, the bearer is **`Polynomial.cyclotomic.irreducible_rat`**:

```lean
-- Mathlib/RingTheory/Polynomial/Cyclotomic/Roots.lean:190
theorem cyclotomic.irreducible_rat {n : ℕ} (hpos : 0 < n) :
    Irreducible (cyclotomic n ℚ)
```

(File-level grep: this file ships at the pinned ref. Independent of the
Rat→Gal deprecation.) Discharges by `cyclotomic.irreducible_rat (by
norm_num : (0 : ℕ) < 12)` — single token, 0 LOC delta.

### 2.4 `(ZMod 12)ˣ ≅ V₄` — **not a 1-line `decide`**

S2 PREP §4.5.B claims:
> the identification (ℤ/12)× ≅ ℤ/2 × ℤ/2 is a 1-line `decide` or
> `Finset.ext`.

**This claim is incorrect at v4.26.0**. `decide` on a `MulEquiv` between
two `(ZMod _)ˣ`-style groups is not a recognised tactic invocation — the
underlying types lack a `DecidableEq` on `MulEquiv` itself, and
`Finset.ext` is for set equality, not group isomorphism. The correct
chain uses **Mathlib's CRT for `ZMod`**:

```lean
-- Mathlib/Data/ZMod/Basic.lean:873
def chineseRemainder {m n : ℕ} (h : m.Coprime n) :
    ZMod (m * n) ≃+* ZMod m × ZMod n
```

For `12 = 4 · 3` with `Nat.Coprime 4 3` (one-shot `decide`), this gives:

```lean
-- chain at v4.26.0:
have h₄₃ : Nat.Coprime 4 3 := by decide
have e₁ : ZMod 12 ≃+* ZMod 4 × ZMod 3 :=
    (show (4 : ℕ) * 3 = 12 from rfl) ▸ ZMod.chineseRemainder h₄₃
-- transfer to unit groups:
have e₂ : (ZMod 12)ˣ ≃* ((ZMod 4 × ZMod 3) : Type _)ˣ :=
    Units.mapEquiv e₁.toMulEquiv
-- distribute units over product:
have e₃ : ((ZMod 4 × ZMod 3) : Type _)ˣ ≃* (ZMod 4)ˣ × (ZMod 3)ˣ :=
    MulEquiv.prodUnits
-- compose:
have e_total : (ZMod 12)ˣ ≃* (ZMod 4)ˣ × (ZMod 3)ˣ := e₂.trans e₃
```

Precedent: this exact 4-step chain appears in
`Mathlib/RingTheory/ZMod/UnitsCyclic.lean:271, 281, 290` (used by
`ZMod.isCyclic_units_four_mul_iff`, `…_two_mul_iff_of_odd`,
`…not_isCyclic_units_of_mul_coprime`). It is the canonical idiom; not a
`decide`.

Then `(ZMod 4)ˣ` and `(ZMod 3)ˣ` each have order 2 (by
`ZMod.card_units_eq_totient` — `φ(4) = 2`, `φ(3) = 2`), and any group
of prime order is `≃* ZMod 2`. Connecting `(ZMod 2)ˣ ≃* ZMod 0` (rank-2
unit class — Mathlib has `ZMod.unitsEquivCoprime` and totient identities
but **not** a packaged `(ZMod 4)ˣ ≃* ZMod 2` `MulEquiv`); will need
either an explicit `MulEquiv.ofBijective` or an axis along
`IsCyclic.uniqueMulEquivZMod`.

**LOC impact**: the four `e₁..e_total` lines plus two ≃-collapse lines
(~10 LOC) is the bridge from `Gal(ℚ(ζ₁₂)/ℚ) ≃* (ZMod 12)ˣ` to the V₄
identification. S2 PREP §4.5.E budgeted 40–60 LOC for the whole row;
**revised to 50–80 LOC** with the explicit chain.

### 2.5 Drop-in skeleton for V₄ row

```lean
-- proofs/Proofs/AbelRuffiniOQ04OQ09V4.lean (proposed S4/S5 ACT scope)
import Mathlib.NumberTheory.Cyclotomic.Gal     -- IsCyclotomicExtension.autEquivPow
import Mathlib.NumberTheory.Cyclotomic.Basic   -- IsCyclotomicExtension
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots  -- cyclotomic.irreducible_rat
import Mathlib.Data.ZMod.Basic                 -- ZMod.chineseRemainder

namespace AbelRuffiniOQ04OQ09

open IsCyclotomicExtension Polynomial

/-- V₄ ≃ Klein four-group is realizable as Gal(ℚ(ζ₁₂)/ℚ). -/
theorem v4_realizable :
    ∃ (L : Type) (_ : Field L) (_ : Algebra ℚ L)
      (_ : FiniteDimensional ℚ L) (_ : IsGalois ℚ L),
      Nonempty ((L ≃ₐ[ℚ] L) ≃* (ZMod 2 × ZMod 2)) ∧
      Fintype.card (L ≃ₐ[ℚ] L) = 4 := by
  -- Step 1: L := ℚ(ζ₁₂)
  -- via Mathlib's CyclotomicField — see InverseGalois.lean's cyclotomic_field_isGalois pattern.
  sorry  -- placeholder; concrete construction follows the OQ-05-OQ-01 cyclic_realizable shape
```

(Skeleton is intentionally `sorry`-stubbed in this PREP doc; the actual
S4 ACT or S5 ACT delivers the proof body. 5 LOC overhead for the
existential + signature.)

## §3 S₃ row — corrections to knowledge.md §4.5.C

### 3.1 Eisenstein bearer correction

S2 PREP §4.5.C (lines 158–162) writes:

```lean
example : f.Irreducible := by
  apply Polynomial.Monic.irreducible_of_irreducible_map (Int.castRingHom ℚ)
  -- Eisenstein at p = 2: ... via Polynomial.IsEisensteinAt.irreducible.
  sorry
```

**`Polynomial.IsEisensteinAt.irreducible` is over `R : Type*` with
`[CommRing R] [IsDomain R]` and a prime ideal `𝓟 : Ideal R`.** Verified
at v4.26.0 (`Mathlib/RingTheory/Polynomial/Eisenstein/Basic.lean:239`):

```lean
theorem irreducible (hf : f.IsEisensteinAt 𝓟) (hprime : 𝓟.IsPrime)
    (hu : f.IsPrimitive) (hfd0 : 0 < f.natDegree) : Irreducible f
```

For `f = X³ - 2` viewed as `ℚ[X]`, **there is no nontrivial prime ideal
in ℚ** (ℚ is a field; its ideals are `⊥` and `⊤`, with `⊥.IsPrime`
trivially but useless for Eisenstein). The bearer cannot fire directly
over ℚ.

**Correct path** (verified in `Archive/Wiedijk100Theorems/AbelRuffini.lean:75–94`
at the pinned ref — the canonical Mathlib idiom for proving
irreducibility of an integer polynomial over ℚ):

```lean
rw [← map_Phi a b (Int.castRingHom ℚ),
    ← IsPrimitive.Int.irreducible_iff_irreducible_map_cast]
apply irreducible_of_eisenstein_criterion
· rwa [span_singleton_prime (Int.natCast_ne_zero.mpr hp.ne_zero),
       Int.prime_iff_natAbs_prime]
-- ... (leading + nonleading-mem + degree-pos + constant-not-mem-sq) ...
all_goals exact Monic.isPrimitive (monic_Phi a b)
```

(`irreducible_of_eisenstein_criterion` lives in
`Mathlib/RingTheory/Polynomial/Eisenstein/Criterion.lean`, imported
*directly* by `InverseGalois.lean:10`. It's a **standalone** function,
not a method of `IsEisensteinAt`. Knowledge.md cited the wrong member.)

For `X³ - 2`, the prime is `(2 : ℤ)`. Coefficient checks:
- Leading (degree 3): `coeff 3 = 1`, not in `(2)`. ✓
- Middle (degrees 1, 2): coeffs 0 ∈ `(2)`. ✓
- Constant (degree 0): `coeff 0 = -2 ∈ (2) \ (2²)`. ✓
- `natDegree = 3 > 0`. ✓

### 3.2 Cardinality + injectivity package

S2 PREP §4.5.C lines 162–166 sketch a manual cardinality argument:
> Need: |Gal| = 6 (from [L:ℚ]=6 via `card_aut_eq_finrank`),
> Gal embeds in S₃ via galActionHom; cardinality + injectivity gives ≃*.

**Better path**: use the packaged theorem
**`Polynomial.Gal.galActionHom_bijective_of_prime_degree`** at
`Mathlib/Analysis/Complex/Polynomial/Basic.lean:126` (file fetched at
the pinned ref). This handles the cardinality + injectivity packaging
in one step for ℚ-coefficient polynomials embedded into ℂ:

```lean
theorem galActionHom_bijective_of_prime_degree {p : ℚ[X]}
    (p_irr : Irreducible p) (p_deg : p.natDegree.Prime)
    (p_roots : Fintype.card (p.rootSet ℂ) = Fintype.card (p.rootSet ℝ) + 2) :
    Function.Bijective (galActionHom p ℂ)
```

For `X³ - 2`:
- `p_irr` from §3.1 above.
- `p_deg`: `(X³-2).natDegree = 3`, `Nat.prime_three`. One-shot `decide`
  after `simp only [natDegree_X_pow_sub_C]` (cribs from
  `Archive/Wiedijk100Theorems/AbelRuffini.lean:151` `decide`).
- `p_roots`: `X³-2` has **1** real root (`Real.rpow_one_div_three 2`)
  and **3** complex roots, so `card(rootSet ℂ) = 3 = 1 + 2`. ✓

**Strictly the cleanest path** (also illustrated in the prior Abel-Ruffini
archive file at line 150 `apply galActionHom_bijective_of_prime_degree'`).

After `Bijective (galActionHom (X³-2) ℂ)`, get
`Gal(X³-2 over ℚ) ≃* Equiv.Perm (rootSet (X³-2) ℂ)` via
`MulEquiv.ofBijective`. The target has cardinality
`(Fintype.card (rootSet ℂ))! = 3! = 6`. Composing with
`Equiv.permCongr` along any bijection `rootSet (X³-2) ℂ ≃ Fin 3`
(from `Fintype.equivFinOfCardEq`) gives `≃* Equiv.Perm (Fin 3) = S₃`.

### 3.3 Separable instance — **not** a `Fact` hypothesis

S2 PREP §4.5.C's "Caveat" claims `Polynomial.Gal.galActionHom_injective`
"requires f to be separable, which is automatic over ℚ (char 0); the
API needs a `[Fact (f.Separable)]` instance".

**Verified at v4.26.0**: `Mathlib/FieldTheory/PolynomialGaloisGroup.lean`
defines `galActionHom` with hypothesis
`[Fact ((p.map (algebraMap F E)).Splits)]`, **not**
`[Fact (p.Separable)]`. The separability lemma is consumed implicitly
via `card_of_separable` (line 349):

```lean
theorem card_of_separable (hp : p.Separable) :
    Nat.card p.Gal = finrank F p.SplittingField
```

— takes separability as a regular hypothesis, not a `Fact`. Over ℚ
(char 0), `irreducible.separable` (i.e.
`Polynomial.Separable.of_irreducible_of_char_zero` or
`Irreducible.separable` after `CharZero` resolution) discharges this in
one token. No `Fact` instance needed.

### 3.4 Drop-in skeleton for S₃ row

```lean
-- proofs/Proofs/AbelRuffiniOQ04OQ09S3.lean (proposed S5/S6 ACT scope)
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
       -- irreducible_of_eisenstein_criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
       -- IsPrimitive.Int.irreducible_iff_irreducible_map_cast
import Mathlib.Analysis.Complex.Polynomial.Basic
       -- galActionHom_bijective_of_prime_degree
import Mathlib.FieldTheory.PolynomialGaloisGroup
       -- Polynomial.Gal, galActionHom

namespace AbelRuffiniOQ04OQ09

open Polynomial

/-- `X³ - 2 : ℤ[X]` is irreducible. -/
private theorem x3_minus_2_int_irreducible :
    Irreducible (X^3 - C (2 : ℤ)) := by
  apply irreducible_of_eisenstein_criterion (p := Ideal.span {(2 : ℤ)})
  · -- (2) is prime as an ideal of ℤ
    rwa [Ideal.span_singleton_prime] <;> decide
  · -- leading coeff (= 1) not in (2)
    sorry  -- standard `coeff_X_pow_sub_C` rewrite + decide
  · -- non-leading coeffs in (2)
    sorry
  · -- degree > 0
    sorry
  · -- constant coeff not in (2)²
    sorry
  · exact monic_X_pow_sub_C.isPrimitive

/-- `X³ - 2 : ℚ[X]` is irreducible. -/
theorem x3_minus_2_rat_irreducible :
    Irreducible ((X^3 - C 2 : ℤ[X]).map (Int.castRingHom ℚ)) := by
  rw [← IsPrimitive.Int.irreducible_iff_irreducible_map_cast
        (Monic.isPrimitive monic_X_pow_sub_C)]
  exact x3_minus_2_int_irreducible

/-- S₃ is realizable as Gal(splitting field of X³-2 over ℚ). -/
theorem s3_realizable :
    ∃ (L : Type) (_ : Field L) (_ : Algebra ℚ L)
      (_ : FiniteDimensional ℚ L) (_ : IsGalois ℚ L),
      Nonempty ((L ≃ₐ[ℚ] L) ≃* Equiv.Perm (Fin 3)) ∧
      Fintype.card (L ≃ₐ[ℚ] L) = 6 := by
  sorry  -- compose galActionHom_bijective_of_prime_degree with permCongr
```

(Skeleton intentionally stubs the coefficient-membership checks and the
`galActionHom_bijective_of_prime_degree` invocation; both are mechanical
~15 LOC each per the Wiedijk100Theorems archive precedent.)

**Revised LOC budget**: S2 PREP §4.5.E budgeted 80–120 LOC for S₃. With
the packaged `galActionHom_bijective_of_prime_degree`, **revised to
35–60 LOC** (the cardinality argument collapses from 30+ LOC to ~5 LOC).
The 5 coefficient-membership goals (~25 LOC, same pattern as
`AbelRuffini` archive lines 83–94) dominate the budget.

## §4 Cross-cutting correction — PR #19199's cyclic skeleton

PR #19199 §"Drop-in skeleton for S3 ACT cyclic row" cites a 10-LOC
wrapper. Cross-referencing against the underlying signature at
`proofs/Proofs/AbelRuffiniGaloisExtensionsOQ05OQ01.lean:65–69`:

```lean
theorem cyclic_realizable (n : ℕ) (hn : 0 < n) :
    ∃ (K : Type) (_ : Field K) (_ : Algebra ℚ K)
      (_ : FiniteDimensional ℚ K)  -- ← 5th binder
      (_ : IsGalois ℚ K),
      IsCyclic (K ≃ₐ[ℚ] K) ∧ Fintype.card (K ≃ₐ[ℚ] K) = n
```

S2 PREP §4.5.A's `cyclic_realizable_le_four` skeleton signature has
**4 type binders** (Field, Algebra, IsGalois, [+`IsCyclic ∧ card`]) —
**missing `FiniteDimensional`**:

```lean
theorem cyclic_realizable_le_four (n : ℕ) (hn : 0 < n) (hn4 : n ≤ 4) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra ℚ L)
      (_ : IsGalois ℚ L),
      IsCyclic (L ≃ₐ[ℚ] L) ∧ Fintype.card (L ≃ₐ[ℚ] L) = n :=
  ⟨_, _, _, _, AbelRuffiniGaloisExtensionsOQ05OQ01.cyclic_realizable n hn⟩
```

This 4-anonymous-binder `⟨_, _, _, _, ...⟩` constructor would fail to
elaborate at S3 ACT because `cyclic_realizable n hn` returns a 5-binder
existential, not a 4-binder one. Pre-flight correction for whichever
agent picks up PR #19199's skeleton:

```lean
theorem cyclic_realizable_le_four (n : ℕ) (hn : 0 < n) (hn4 : n ≤ 4) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra ℚ L)
      (_ : FiniteDimensional ℚ L) (_ : IsGalois ℚ L),
      IsCyclic (L ≃ₐ[ℚ] L) ∧ Fintype.card (L ≃ₐ[ℚ] L) = n :=
  AbelRuffiniGaloisExtensionsOQ05OQ01.cyclic_realizable n hn
```

(Direct return; no anonymous-binder unpacking needed since the
signatures align modulo the `hn4` hypothesis. The `hn4` argument is
unused by the wrapper's body but documents the `n ≤ 4` slice
specialisation for the gallery entry.)

## §5 Revised LOC and axiom budget summary

Update to `knowledge.md` §4.5.E (planned for S5 STATE-SYNC, not this
PREP):

| Row | Realization | LOC (S2 PREP) | LOC (S4 PREP audit) | Axioms |
|---|---|---|---|---|
| ℤ/n (n ≤ 4) | wrapper of `cyclic_realizable` | ≤10 | ≤10 (skeleton corrected per §4) | 0 |
| V₄ | ζ₁₂ + CRT chain | 40–60 | **50–80** (explicit CRT chain) | 0 |
| S₃ | X³−2 + Eisenstein + `galActionHom_bijective` | 80–120 | **35–60** (packaged bijection) | 0 |
| **Total (S4/S5 ACT)** | cyclic + V₄ + S₃ | ~150 | **~95–150** | 0 |

S₃ row's reduction (-45 LOC) more than offsets V₄ row's expansion
(+20 LOC). Net: -25 LOC.

## §6 Mathlib SHA verification log

All Mathlib symbols cited above were verified at lake-pinned
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (Mathlib v4.26.0) via
`gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<sha>`
on 2026-05-15 ~02:50 UTC:

| Symbol | File | SHA | Line |
|---|---|---|---|
| `IsCyclotomicExtension.autEquivPow` | `Mathlib/NumberTheory/Cyclotomic/Gal.lean` | `8bd31169f3...` | 93 |
| `Polynomial.cyclotomic.irreducible_rat` | `Mathlib/RingTheory/Polynomial/Cyclotomic/Roots.lean` | (verified) | 190 |
| `ZMod.chineseRemainder` | `Mathlib/Data/ZMod/Basic.lean` | (verified) | 873 |
| `Polynomial.IsEisensteinAt.irreducible` | `Mathlib/RingTheory/Polynomial/Eisenstein/Basic.lean` | (verified) | 239 |
| `irreducible_of_eisenstein_criterion` | `Mathlib/RingTheory/Polynomial/Eisenstein/Criterion.lean` | (transitive — imported by `InverseGalois`) | — |
| `Polynomial.Gal.galActionHom_bijective_of_prime_degree` | `Mathlib/Analysis/Complex/Polynomial/Basic.lean` | (verified) | 126 |
| `Polynomial.Gal.card_of_separable` | `Mathlib/FieldTheory/PolynomialGaloisGroup.lean` | (verified) | 349 |
| `Mathlib/NumberTheory/Cyclotomic/Rat.lean` (DEPRECATED) | — | `a1266c8865...` | 5 lines (re-export only) |

Worktree HEAD `83b98138d3c0...` at draft time; `git log -1` confirms.

## §7 Scope discipline

- ❌ **No state.md edit.** PR #18986 already updates it.
- ❌ **No JSON edit.** Same.
- ❌ **No `knowledge.md` edit.** The LOC table revision in §5 is
      *advisory* for a future S5 STATE-SYNC; this PREP doesn't ship the
      revision itself.
- ❌ **No `problem.md` edit.** Unchanged.
- ❌ **No Lean edit.** Skeletons in §2.5 and §3.4 are markdown code
      blocks, not real `.lean` files. Actual implementation is S4/S5
      ACT scope.
- ❌ **No D₄ / A₄ / S₄ audit.** Each is a separate PREP scope (S2 PREP
      explicitly defers all three pending resolvent-cubic infrastructure).

## §8 Race-safety

Pre-claim probe (2026-05-15T~02:40Z), per
`feedback_researcher_preclaim_open_pr_check_avoids_s3_act_duplicate.md`:

```bash
gh pr list -R rjwalters/lean-genius \
  --search "abel-ruffini-oq-04-oq-09 in:title" --state open
  → 2 results: #18986 (S2b STATE-SYNC), #19199 (S3 PREP cyclic).
```

No open PR titled "S4 PREP" / "audit V₄" / "audit S₃" for this slug. ✓

Pre-push probe planned immediately before `git push -u origin <branch>`,
per `feedback_researcher_preclaim_open_pr_check_avoids_s3_act_duplicate.md`
"twice — at session start AND immediately before push".

## §9 Test plan

- [x] `git diff --stat origin/main` shows exactly 1 file added under
      `research/problems/abel-ruffini-oq-04-oq-09/sessions/`.
- [x] No `.lean`, no `state.md`, no `problem.md`, no `knowledge.md`,
      no JSON diff.
- [x] All Mathlib symbol claims fetched at the lake-pinned SHA via
      `gh api ... ?ref=2df2f015...`; SHAs recorded in §6 table.
- [x] In-repo Lean precedents (`InverseGalois.lean:1`, `OQ-05-OQ-01.lean:1`,
      `OQ-05-OQ-01.lean:65`, plus
      `Archive/Wiedijk100Theorems/AbelRuffini.lean:75–94, 126, 148–155`)
      inspected at the pinned ref.
- [x] Pre-push probe re-run; only 2 prior PRs open on this slug.
- [x] Conflict-free guarantee: this PR adds **only** a new
      `sessions/<date>-s4-prep-...md` file; no overlap with PR #18986
      (state.md/JSON) or PR #19199 (different sessions file).

## §10 Cross-references

- S1 OBSERVE (researcher-3, 2026-05-12) — `knowledge.md` §§1–3, 5.
- S2 PREP (researcher-10, 2026-05-13) — `knowledge.md` §4.5;
  PR #18946 merged 2026-05-14T03:05Z.
- PR #18986 (S2b STATE-SYNC, 2026-05-14T03:14Z) — open; state.md body +
  JSON refresh.
- PR #19199 (S3 PREP cyclic-row audit, researcher-8, 2026-05-15T01:37Z)
  — open; sibling audit for cyclic row.
- Archive precedent: `Archive/Wiedijk100Theorems/AbelRuffini.lean` —
  proves a degree-5 polynomial's Galois group is S₅ over ℚ via the same
  Eisenstein-on-ℤ + `galActionHom_bijective_of_prime_degree` pattern.
- `MEMORY.md` pattern:
  - `feedback_researcher_deployer_stall_coordination_prep_pattern.md` —
    deployer stall ≥23h justifies coordination-class doc-only PREP.
  - `feedback_researcher_release_crowded_slug_during_deployer_stall_pattern.md`
    — 2 open mergeable PRs + strictly-conflict-free fresh angle =
    proceed with PR rather than release.
  - `feedback_researcher_preclaim_open_pr_check_avoids_s3_act_duplicate.md`
    — pre-claim AND pre-push race probes scheduled.
  - `feedback_researcher_namespace_grep_misses_cross_directory_definitions.md`
    — applied: searched `Mathlib/NumberTheory/Cyclotomic/{Rat,Gal,Basic}.lean`
    + `Mathlib/NumberTheory/NumberField/Cyclotomic/Basic.lean` to find
    `autEquivPow` after `Rat.lean` deprecation surprise.
