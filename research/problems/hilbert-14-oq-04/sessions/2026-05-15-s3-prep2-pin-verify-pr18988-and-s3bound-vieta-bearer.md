# hilbert-14-oq-04 — S3 PREP-2: pin-verify PR #18988 Lean bearers + close S2g §2.4 open Vieta gap (doc-only)

**Date**: 2026-05-15
**Phase**: S3 PREP-2 (doc-only — sibling-PREP audit of pending PR #18988 + close S2g §2.4 §"NOT searched in this PREP" gap)
**Researcher**: researcher-8
**Branch**: `research/hilbert-14-oq-04-s3-prep2-pin-verify-pr18988-and-s3bound-vieta-1778836500`
**Mathlib pin**: v4.26.0 (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)
**Status**: Pre-ACT design memo — no Lean changes, no edits to
`problem.md` / `knowledge.md` / `state.md` / gallery JSON / any sibling
`.lean` / any existing PREP doc.

## §0 Why this PREP-2

Three observable facts in the slug's open-PR landscape made a sibling
PREP-2 audit the highest-leverage doc-only action available without
conflicting:

1. **PR #18988** (S2-finite ACT — `hilbert_finiteness verified`, 102 LOC,
   build verified Docker 7743 jobs) is **OPEN, MERGEABLE, CLEAN** on
   `topic/hilbert-14-oq-04-1778727768`. Per state.md (last touched at
   S1) the listed "Next Action: S2 ACT" is **stale**: the ACT has in
   fact shipped, awaiting deployer merge.

2. **PR #19188** (S3 PREP — coordination note for pending PR #18988,
   doc-only 108 LOC) is **OPEN, MERGEABLE** on
   `research/hilbert-14-oq-04-s3-prep-coordination-pr18988-pending-1778807582`.
   This is a pure coordination note — it surfaces the staleness of
   state.md and the deployer-stall blocker, but does no further
   technical audit work.

3. **S2g PREP** (PR #18750 merged) closed 3 of 4 caveats from S2f §8 but
   explicitly flagged its §2.4 charpoly↔esymm Vieta link as
   *"NOT searched in this PREP (rate-limited)"*:

   > **Caveat**: `mul_esymm_eq_sum` and friends are stated for `MvPolynomial σ R`
   > where `esymm σ R k` and `psum σ R k` are the **elementary symmetric / power-sum
   > polynomials in `MvPolynomial σ R`** (indexed by `σ`-tuples). For the Noether
   > degree bound, we use this with `σ = G` (or `Fin (Fintype.card G)`), `R = k[V]`,
   > and **apply the polynomial identity at the orbit `(g • v)_{g ∈ G}`** of a
   > distinguished `v ∈ R = k[V]`. The relationship to `MulSemiringAction.charpoly G v`
   > is:
   > - `charpoly G v = ∏_g (X - C (g•v))` is the polynomial in `B[X]` whose roots are
   >   the orbit elements.
   > - Vieta's formulas give `coeff (charpoly G v) (|G| - k) = (-1)^k * esymm_G k` evaluated at the orbit.
   > - Newton's identities then relate `psum_G k = ∑_g (g•v)^k` to the `coeff`s.
   >
   > The exact Mathlib bearer linking `charpoly` coefficients to `esymm` over the
   > orbit set is **NOT searched in this PREP** (rate-limited).

   This **PREP-2** closes that open Vieta-bearer search (§3 below).

**Net deliverable**: (a) reaffirm every S2g claim and every PR #18988
Lean-file bearer at the lake-pinned SHA; (b) close S2g §2.4's
charpoly↔esymm Vieta gap with concrete Mathlib bearers at SHA; (c) pre-stage
a reference S3-bound bearer skeleton for the next ACT iteration.

**Anti-targets**: doc-only, single new file under `sessions/`. No edits
to `problem.md` / `state.md` / `knowledge.md` / gallery JSON / `.lean` /
any prior PREP. **Strict conflict-free** with PR #18988 (different
files), PR #19188 (different filename in the same `sessions/`
directory), and the 7 already-merged PREPs.

## §1 PR #18988 Lean file: line-by-line pin-verify at lake SHA

### §1.1 The 5 ACT bearers — each pin-verified at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

PR #18988 ships `proofs/Proofs/Hilbert14OQ04.lean` (NEW, 102 LOC,
`docker-build.sh Proofs.Hilbert14OQ04` → 7743 jobs green, third Docker
attempt). The proof chain rests on 5 Mathlib bearers + 1 anonymous
constructor pack. Each line in the table below was fetched via:

```
gh api 'repos/leanprover-community/mathlib4/contents/<File>?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67'
  --jq '.content' | base64 -d
```

| # | Bearer | Path & line | Signature at SHA | PR call site | Audit verdict |
|:--|:-------|:------------|:-----------------|:-------------|:--------------|
| B1 | `Algebra.IsInvariant.isIntegral` | `Mathlib/RingTheory/Invariant/Basic.lean:174` | `theorem isIntegral [Finite G] : Algebra.IsIntegral A B` (in namespace `Algebra.IsInvariant`, `variable [IsInvariant A B G]` block) | `Algebra.IsInvariant.isIntegral _ _ G` | ✅ Match — `[Finite G]` automatic from `[Fintype G]`; `IsInvariant` synthesized from B2's instance |
| B2 | `Algebra.IsInvariant` (typeclass) | `Mathlib/RingTheory/Invariant/Defs.lean:30-31` | `@[mk_iff] class IsInvariant : Prop where isInvariant : ∀ b : B, (∀ g : G, g • b = b) → ∃ a : A, algebraMap A B a = b` | `instance isInvariant_fixedPoints ... where isInvariant b hb := ⟨⟨b, hb⟩, rfl⟩` | ✅ Match — field name `isInvariant`; `⟨b, hb⟩` is the FixedPoints-subalgebra element whose `algebraMap` is `Subtype.val = b`, hence `rfl` |
| B3 | `Algebra.FiniteType.of_restrictScalars_finiteType` | `Mathlib/RingTheory/FiniteType.lean:77` | `theorem of_restrictScalars_finiteType [Algebra S A] [IsScalarTower R S A] [hA : FiniteType R A] : FiniteType S A` | `Algebra.FiniteType.of_restrictScalars_finiteType k B R` | ✅ Match — `R, S, A` are *explicit* args via `variable (R : Type uR) (S : Type uS) (A : Type uA) ...` block at L35; 3 explicit positional args correct |
| B4 | `Algebra.IsIntegral.finite` | `Mathlib/RingTheory/IntegralClosure/IsIntegralClosure/Basic.lean:93` | `theorem Algebra.IsIntegral.finite [Algebra.IsIntegral R A] [h' : Algebra.FiniteType R A] : Module.Finite R A` | `haveI hMF_BR : Module.Finite B R := Algebra.IsIntegral.finite` | ✅ Match — both typeclass args from instances above |
| B5 | `fg_of_fg_of_fg` (Artin–Tate) | `Mathlib/RingTheory/Adjoin/Tower.lean:150` | `theorem fg_of_fg_of_fg [IsNoetherianRing A] (hAC : (⊤ : Subalgebra A C).FG) (hBC : (⊤ : Submodule B C).FG) (hBCi : Function.Injective (algebraMap B C)) : (⊤ : Subalgebra A B).FG` (`variable [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]`) | `fg_of_fg_of_fg k B R h_kR_fg h_BR_fg h_BR_inj` | ✅ Match — 3 explicit (A, B, C) + 3 positional hypothesis args |
| B6 | `Module.Finite.fg_top` | `Mathlib/RingTheory/Finiteness/Defs.lean:123` (field of `Module.Finite`) | `class Module.Finite ... where fg_top : (⊤ : Submodule R M).FG` | `have h_BR_fg : (⊤ : Submodule B R).FG := Module.Finite.fg_top` | ✅ Match — invoked as `[Module.Finite B R].fg_top` via typeclass synth |
| B7 | `Algebra.FiniteType` (anonymous constructor pack) | `Mathlib/RingTheory/FiniteType.lean:39` (field name `out`) | `class Algebra.FiniteType : Prop where out : (⊤ : Subalgebra R A).FG` | `exact ⟨h_kB_fg⟩` | ✅ Match — `⟨_⟩` packs `(⊤ : Subalgebra k B).FG` into `Algebra.FiniteType k B` |
| B8 | `FixedPoints.subalgebra` (definition) | `Mathlib/Algebra/Algebra/Subalgebra/Operations.lean:91` | `def FixedPoints.subalgebra : Subalgebra A B where __ := FixedPoints.addSubgroup G B; __ := FixedPoints.submonoid G B; algebraMap_mem' r := by simp` (`variable (A B : Type*) [CommSemiring A] [Ring B] [Algebra A B] (G : Type*) [Monoid G] [MulSemiringAction G B] [SMulCommClass G A B]`) | `FixedPoints.subalgebra k (MvPolynomial (Fin n) k) G` | ✅ Match — `[Monoid G]` synthesized from `[Group G]` in the PR's variable block; membership predicate `∀ g : G, g • b = b` matches the `isInvariant_fixedPoints` instance proof body `⟨⟨b, hb⟩, rfl⟩` |

**`Subtype.val_injective`** — used for `h_BR_inj : Function.Injective (algebraMap B R)`. The `algebraMap (FixedPoints.subalgebra k R G) R` is implemented as `Subtype.val` (via `Subalgebra`'s `Algebra` instance). ✅ Match.

### §1.2 No mismatches found

Every typeclass argument, every explicit/implicit-positional convention,
and every field-name reference in the PR file checks out against
Mathlib at the lake-pinned SHA. The chain compiles **as written**;
the build trace (Docker iterations #1, #2 surfaced specific gotchas;
#3 green) is consistent with the bearer signatures listed above.

### §1.3 What the PR file gets right (reaffirmation)

The PR's `instance isInvariant_fixedPoints` proof body is `⟨⟨b, hb⟩, rfl⟩`,
not a longer assembly via `FixedPoints.mem_subalgebra_iff`. This works because:

(a) The `FixedPoints.subalgebra` definition (see B8) inherits the
    membership predicate `∀ g : G, g • b = b` from `FixedPoints.submonoid G B`.
    So `b ∈ FixedPoints.subalgebra k R G ↔ ∀ g : G, g • b = b`, which is
    exactly `hb` in the proof body.

(b) The `algebraMap (FixedPoints.subalgebra k R G) R` is `Subtype.val`,
    so `algebraMap _ _ ⟨b, hb⟩ = b` is `rfl`.

These two definitional facts pack the entire `IsInvariant` field
discharge into a single anonymous constructor — there is **no shorter
form**.

### §1.4 Hypotheses are the minimal `MulSemiringAction` setup

The PR's 5 typeclass hypotheses are:

```lean
variable {k : Type*} [Field k] {n : ℕ}
variable {G : Type*} [Group G] [Fintype G]
variable [MulSemiringAction G (MvPolynomial (Fin n) k)]
variable [SMulCommClass G k (MvPolynomial (Fin n) k)]
```

Each is required by the bearer chain:

- `[Field k]` — required for `IsNoetherianRing k` (Artin–Tate B5's `[IsNoetherianRing A]`).
  Mathlib synthesizes `Field → CommRing → IsNoetherianRing` automatically.
- `[Fintype G]` — required for `[Finite G]` (B1).
- `[Group G]` (not just `[Monoid G]`) — `MulSemiringAction G B` is a `Monoid`-level
  typeclass, so `Group` is stronger than necessary, but the typical statement
  for Noether-invariant theory carries `Group G`. No conflict.
- `[MulSemiringAction G (MvPolynomial (Fin n) k)]` — load-bearing for `FixedPoints.subalgebra`,
  `Algebra.IsInvariant`, and `MulSemiringAction.charpoly` (§3).
- `[SMulCommClass G k (MvPolynomial (Fin n) k)]` — required by `FixedPoints.subalgebra` (B8)'s
  `variable` block.

**No assumption is structure-encoded or hidden**; the OQ-04 axiom
integrity policy is respected (cf. project CLAUDE.md "Axiom Integrity
Policy" — invariant ring finite generation here is a *theorem*, not an
axiom).

## §2 S2g PREP §2.4 line-number re-pin at lake SHA

S2g §2.4 cited three Newton-identity bearers at file
`Mathlib/RingTheory/MvPolynomial/Symmetric/NewtonIdentities.lean`. All
three line numbers re-pinned at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

| # | Bearer | S2g §2.4 claim | Re-pin at SHA | Verdict |
|:--|:-------|:---------------|:--------------|:--------|
| N1 | `MvPolynomial.mul_esymm_eq_sum` | L223 | L223 (`theorem mul_esymm_eq_sum (k : ℕ) : k * esymm σ R k = (-1) ^ (k + 1) * ∑ a ∈ antidiagonal k with a.1 < k, (-1) ^ a.1 * esymm σ R a.1 * psum σ R a.2`) | ✅ |
| N2 | `MvPolynomial.sum_antidiagonal_card_esymm_psum_eq_zero` | L236 | L236 | ✅ |
| N3 | `MvPolynomial.psum_eq_mul_esymm_sub_sum` | L247 | L247 | ✅ |

Namespace verification: line 217 closes `namespace NewtonIdentities`,
line 219 declares `variable (σ : Type*) [Fintype σ] (R : Type*) [CommRing R]`,
line 221 begins the docstring, line 223 begins the public theorem. So
the fully-qualified name is **`MvPolynomial.mul_esymm_eq_sum`** (NOT
`MvPolynomial.NewtonIdentities.mul_esymm_eq_sum` — the inner namespace
is closed before the public theorem starts). S2g §2.4 was correct on
this point. ✅

## §3 S2g §2.4 open Vieta gap — closed at SHA

S2g §2.4 explicitly flagged the charpoly↔esymm link as
*"NOT searched in this PREP (rate-limited)"*. This PREP-2 closes that gap.

### §3.1 Mathlib bearers for the charpoly↔esymm link

All bearers at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

| # | Bearer | Path & line | Signature (abbreviated) | Role for S3-bound ACT |
|:--|:-------|:------------|:------------------------|:----------------------|
| V1 | `MulSemiringAction.charpoly` | `Mathlib/RingTheory/Invariant/Basic.lean:138` | `noncomputable def charpoly (b : B) : B[X] := ∏ g : G, (X - C (g • b))` | Mathlib's **orbit polynomial**: replaces the hand-built `orbitPolynomial v` from state.md `Next Action §2`. **Already in Mathlib at SHA** — no need to redefine. |
| V2 | `MulSemiringAction.smul_coeff_charpoly` | `Mathlib/RingTheory/Invariant/Basic.lean:158` | `theorem smul_coeff_charpoly (b : B) (n : ℕ) (g : G) : g • (charpoly G b).coeff n = (charpoly G b).coeff n` | Each coefficient of `charpoly G b` is `G`-fixed (the **`orbit_polynomial_invariant`** lemma the state.md §3 sketched). |
| V3 | `MulSemiringAction.monic_charpoly` | `Mathlib/RingTheory/Invariant/Basic.lean:145` | `theorem monic_charpoly (b : B) : (charpoly G b).Monic` | Monicity (needed for `natDegree = |G|` and integrality). |
| V4 | `MulSemiringAction.eval_charpoly` | `Mathlib/RingTheory/Invariant/Basic.lean:148` | `theorem eval_charpoly (b : B) : (charpoly G b).eval b = 0` | The **`vanishes_at_v`** lemma the state.md §3 sketched; `b` is a root of its own charpoly. |
| V5 | `Multiset.prod_X_sub_C_coeff` | `Mathlib/RingTheory/Polynomial/Vieta.lean:101` | `theorem prod_X_sub_C_coeff (s : Multiset R) {k : ℕ} (h : k ≤ Multiset.card s) : (s.map fun r => X - C r).prod.coeff k = (-1) ^ (Multiset.card s - k) * s.esymm (Multiset.card s - k)` | **Vieta's formula** for `∏(X - C aᵢ)`: directly applicable to `charpoly G b` via `Finset.prod_eq_multiset_prod`. |
| V6 | `Polynomial.coeff_eq_esymm_roots_of_card` | `Mathlib/RingTheory/Polynomial/Vieta.lean:118-124` | `[IsDomain R] {p : R[X]} (hroots : p.roots.card = p.natDegree) {k : ℕ} (h : k ≤ p.natDegree) : p.coeff k = p.leadingCoeff * (-1) ^ (p.natDegree - k) * p.roots.esymm (p.natDegree - k)` | Alternative Vieta-via-roots form (requires `[IsDomain R]`; `MvPolynomial (Fin n) k` over a field is an integral domain, so this is applicable). |
| V7 | `Finset.prod_X_add_C_coeff` | `Mathlib/RingTheory/Polynomial/Vieta.lean:67` | `theorem _root_.Finset.prod_X_add_C_coeff {σ} (s : Finset σ) (r : σ → R) {k : ℕ} (h : k ≤ #s) : ...` | **Finset variant** of the same Vieta link — more directly applicable to `charpoly G b = ∏ g : G, (X - C (g • b)) = ∏ g ∈ (Finset.univ : Finset G), (X - C (g • b))`. (Note: this is the `X + C` variant, the `X - C` version is `prod_X_sub_C_coeff` via `r := -(g • b)`.) |

### §3.2 Resulting S3-bound bearer skeleton (recommended)

With V1–V7 above, the S3-bound ACT (Noether degree bound:
*every minimal generator of `R^G` has total degree ≤ |G|*) admits the
following 3-stage skeleton (Lean sketch, NOT compiled — just bearer
references):

```lean
-- Stage 1: orbit polynomial coefficients are invariants.
example (b : R) (k : ℕ) :
    MulAction.toFun G R ((MulSemiringAction.charpoly G b).coeff k) =
      fun _ => (MulSemiringAction.charpoly G b).coeff k := by
  funext g
  exact (MulSemiringAction.smul_coeff_charpoly b k g).symm
  -- Bearer: V2 (smul_coeff_charpoly)

-- Stage 2: orbit polynomial is monic of degree |G|.
example (b : R) : (MulSemiringAction.charpoly G b).natDegree = Fintype.card G := by
  -- charpoly = ∏ g : G, (X - C (g • b))
  -- natDegree of finite product of monic linear factors = card of index set
  rw [MulSemiringAction.charpoly_eq]
  -- + Polynomial.prod_natDegree_X_sub_C-style or natDegree_finset_prod
  sorry
  -- Bearer: V1 + Mathlib `natDegree_prod` (Mathlib/Algebra/Polynomial/Monic.lean — not pinned here)

-- Stage 3: coefficients ⊆ k[V]^G, each of total degree ≤ |G|.
example (b : R) (k : ℕ) (hk : k ≤ Fintype.card G) :
    MvPolynomial.totalDegree ((MulSemiringAction.charpoly G b).coeff k) ≤
      Fintype.card G := by
  -- Via V5 + V3 + Polynomial.totalDegree_esymm bound (Symmetric.lean —
  -- not pinned here; bearer 4-step search for S3-bound ACT writer).
  sorry
```

**Net LOC estimate** for S3-bound ACT: ~150-250 LOC (close to the
estimate in PR #19188's §3 sequencing recommendation; not changed by
this PREP-2). The main S3-bound bearer that **still requires audit by
the next ACT writer** is the `totalDegree` bound on `esymm`-style
coefficient polynomials — this PREP-2 narrows the search to two
Mathlib files (`Mathlib/Algebra/Polynomial/Monic.lean`,
`Mathlib/RingTheory/MvPolynomial/Symmetric/Basic.lean`) but does not
pin the exact theorem name.

### §3.3 Negative finding — no need to reinvent `orbitPolynomial`

The current state.md `Next Action` §2 sketches a hand-built definition:

```lean
noncomputable def orbitPolynomial (v : MvPolynomial (Fin n) k) :
    Polynomial (MvPolynomial (Fin n) k) :=
  ∏ g : G, (Polynomial.X - Polynomial.C (g • v))
```

This is **definitionally identical** to `MulSemiringAction.charpoly G v`
(bearer V1 above). **The S3-bound ACT should use `charpoly G v`
directly** — no hand-built `orbitPolynomial` is needed. This:

(a) saves ~3-5 LOC + 2 supporting lemmas;
(b) inherits 4 supporting Mathlib lemmas (V2, V3, V4, and
    `MulSemiringAction.charpoly_eq` at L140) for free;
(c) is consistent with PR #18988's actual code path — PR #18988 does
    **not** introduce `orbitPolynomial`; it goes through `Algebra.IsInvariant.isIntegral`
    which uses `charpoly` internally.

This is a **soft correction to state.md `Next Action` §2** — but per the
strict-conflict-free rule of this PREP-2, no state.md edits are made
here. The next ACT writer should treat state.md §2's hand-built
`orbitPolynomial` as a sketch superseded by V1 + V2 + V3 + V4 from
this audit.

## §4 Reaffirm what S2g PREP got right (per-claim audit)

S2g PREP shipped 4 sections of audit findings (S2g §2.1–§2.4). Each is
re-verified at SHA below:

| S2g § | Bearer | S2g claim | Re-pin verdict |
|:------|:-------|:----------|:---------------|
| §2.1  | `fg_of_fg_of_fg`                                    | CONFIRMED real, `Adjoin/Tower.lean:150` | ✅ Line 150 exact; signature exact (3 hypotheses + `[IsNoetherianRing A]`). |
| §2.2  | `Algebra.FiniteType.of_restrictScalars_finiteType`  | CONFIRMED real, `FiniteType.lean:77`     | ✅ Line 77 exact; explicit R/S/A confirmed. |
| §2.3  | `Algebra.FiniteType.of_finite_of_finiteType_top`    | PHANTOM (does NOT exist)                 | ✅ PR #18988's Lean file does NOT invoke this phantom (it routes through `Subalgebra.fg_iff_finiteType.mp h_kB_fg` via the `⟨h_kB_fg⟩` pack on the `out` field — equivalent shortcut). |
| §2.4  | `MvPolynomial.mul_esymm_eq_sum` (and bonuses N2, N3) | location + namespace                     | ✅ L223 / L236 / L247 exact; namespace `MvPolynomial` (NOT inner `NewtonIdentities`) confirmed. |
| §3.1  | `Algebra.FiniteType.mvPolynomial` deprecated         | deprecation valid since 2025-07-12       | ✅ PR #18988's Lean file does NOT invoke the deprecated alias — it relies on `inferInstance` for `Algebra.FiniteType k R` (per §1.3 above). |
| §3.2  | `Algebra.finite_iff_isIntegral_and_finiteType`       | bidirectional bridge at L99              | ✅ Confirmed at SHA, file `IntegralClosure/IsIntegralClosure/Basic.lean:99`. |
| §3.3  | `Algebra.IsIntegral.finite` line drift               | line 93 (not 96)                         | ✅ Confirmed at SHA — line 93 exact. |

**Net**: S2g PREP's 7 audit findings all hold at the lake-pinned SHA.
The S3-bound ACT writer can trust S2g §2 + §3 as a **complete bearer
reference** when paired with this PREP-2's §3 charpoly↔esymm bearer
table.

## §5 Sequencing recommendation (post-merge of PR #18988 and PR #19188)

Once the deployer-stall clears and PR #18988 + PR #19188 both merge:

1. **State.md will need refresh** — current text "Phase: OBSERVE,
   Iter 1, **Next Action: S2 ACT**" is stale; correct text should
   be "Phase: ACT, Iter 2+, **Next Action: S3-bound ACT — Noether degree
   bound**". PR #19188 flags this; this PREP-2 reaffirms it.

2. **S3-bound ACT writer's bearer reference** is now complete:
   - PR #18750 §2.1–§3.3 (Hilbert-finiteness bearer chain) — verified by §1, §4 of this PREP-2.
   - This PREP-2 §3 (charpoly↔esymm Vieta bearer table) — for the S3-bound iteration.
   - Together: 7 Mathlib files, 14 bearers, all pinned at lake SHA `2df2f0150...`.

3. **Estimated S3-bound ACT LOC**: 150-250 LOC (per PR #19188 §3;
   this PREP-2 does not change the estimate but supplies the bearer
   skeleton in §3.2).

4. **No additional PREP audit needed** for S3-bound ACT entry — this
   PREP-2 closes the last "NOT searched" caveat from S2g §2.4. The next
   writer can proceed directly from PREP-2 to ACT, **with one residual
   bearer search** (the `MvPolynomial.totalDegree`-bound on
   `esymm`-style coefficients per §3.2 Stage 3 sketch).

## §6 Conflict footprint

**Zero**. This PREP-2 adds **one new file**:

```
research/problems/hilbert-14-oq-04/sessions/2026-05-15-s3-prep2-pin-verify-pr18988-and-s3bound-vieta-bearer.md
```

No edits to:

- `state.md`
- `problem.md`
- `knowledge.md`
- `src/data/research/problems/hilbert-14-oq-04.json`
- any `.lean` file (most importantly: NO touch of
  `proofs/Proofs/Hilbert14OQ04.lean`, the file being audited)
- any prior session/PREP file in `sessions/`
- the parent gallery entry `src/data/proofs/hilbert-14/meta.json`

**Safe-mergeable** alongside:

- PR #18988 (`topic/hilbert-14-oq-04-1778727768`, S2-finite ACT — adds different files).
- PR #19188 (`research/hilbert-14-oq-04-s3-prep-coordination-pr18988-pending-1778807582`, S3 PREP coord — adds different filename in same `sessions/` directory).
- All 7 merged PREP docs (S2/S2b/S2c/S2d/S2e/S2f/S2g — adds different filename).

## §7 Test plan

- [x] Branch created off `origin/main`: `research/hilbert-14-oq-04-s3-prep2-pin-verify-pr18988-and-s3bound-vieta-1778836500`.
- [x] Lake-pinned Mathlib SHA verified: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` per `proofs/lake-manifest.json`.
- [x] Each of B1-B8 fetched via `gh api repos/leanprover-community/mathlib4/contents/<file>?ref=<sha>` and signature confirmed.
- [x] Each of V1-V7 fetched same way.
- [x] Each of N1-N3 fetched same way; line numbers L223 / L236 / L247 reconfirmed.
- [x] PR #18988 Lean file fetched from remote (`pr18988-head`) and line-by-line cross-checked against bearer signatures.
- [x] PR #19188 body read in full; no claim contradicted by this PREP-2.
- [x] No Docker build performed (doc-only).
- [x] No edits to existing files; only one new file added.

## §8 References

- **PR #18988** — `topic/hilbert-14-oq-04-1778727768`. S2-finite ACT,
  `hilbert_finiteness verified (build verified)`, OPEN, MERGEABLE, CLEAN at audit time.
- **PR #19188** — `research/hilbert-14-oq-04-s3-prep-coordination-pr18988-pending-1778807582`.
  S3 PREP coordination note, OPEN, MERGEABLE at audit time.
- **PR #18750** — merged. S2g PREP — Mathlib bearer re-pin (this PREP-2 audits and reaffirms).
- **PR #18714** — merged. S2f PREP — scope clarification + §8 caveat list (closed by PR #18750 except §2.4 Vieta gap, closed here).
- **PR #18667** — merged. S2e PREP — `Algebra.IsInvariant.isIntegral` discovery (B1 above).
- **PR #18589** — merged. S2d PREP — sibling-slug OQ-01 typeclass bridge.
- **PR #18562** — merged. S2c PREP — `IsScalarTower` / `IsNoetherianRing` trap resolution.
- **PR #18501** — merged. S2b PREP — Artin–Tate canonical bearer (B5 above).
- **PR #18435** — merged. S2 PREP — original orbit-polynomial API audit.
- **PR #18248** — merged. S1 OBSERVE — algorithmic landscape + Noether bound plan.

Mathlib pin: v4.26.0, commit `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`,
verified via `proofs/lake-manifest.json`.
